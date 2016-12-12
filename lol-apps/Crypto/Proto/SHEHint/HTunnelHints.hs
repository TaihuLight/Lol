{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveGeneric, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC  -fno-warn-unused-imports #-}
module Crypto.Proto.SHEHint.HTunnelHints (HTunnelHints(..)) where
import Prelude ((+), (/))
import qualified Prelude as Prelude'
import qualified Data.Typeable as Prelude'
import qualified GHC.Generics as Prelude'
import qualified Data.Data as Prelude'
import qualified Text.ProtocolBuffers.Header as P'
import qualified Crypto.Proto.RLWE.LinearRq as RLWE (LinearRq)
import qualified Crypto.Proto.SHEHint.KSLinearHint as SHEHint (KSLinearHint)

data HTunnelHints = HTunnelHints{func :: !(RLWE.LinearRq), hint :: !(P'.Seq SHEHint.KSLinearHint), p :: !(P'.Word64),
                                 gad :: !(P'.Utf8)}
                  deriving (Prelude'.Show, Prelude'.Eq, Prelude'.Ord, Prelude'.Typeable, Prelude'.Data, Prelude'.Generic)

instance P'.Mergeable HTunnelHints where
  mergeAppend (HTunnelHints x'1 x'2 x'3 x'4) (HTunnelHints y'1 y'2 y'3 y'4)
   = HTunnelHints (P'.mergeAppend x'1 y'1) (P'.mergeAppend x'2 y'2) (P'.mergeAppend x'3 y'3) (P'.mergeAppend x'4 y'4)

instance P'.Default HTunnelHints where
  defaultValue = HTunnelHints P'.defaultValue P'.defaultValue P'.defaultValue P'.defaultValue

instance P'.Wire HTunnelHints where
  wireSize ft' self'@(HTunnelHints x'1 x'2 x'3 x'4)
   = case ft' of
       10 -> calc'Size
       11 -> P'.prependMessageSize calc'Size
       _ -> P'.wireSizeErr ft' self'
    where
        calc'Size = (P'.wireSizeReq 1 11 x'1 + P'.wireSizeRep 1 11 x'2 + P'.wireSizeReq 1 4 x'3 + P'.wireSizeReq 1 9 x'4)
  wirePut ft' self'@(HTunnelHints x'1 x'2 x'3 x'4)
   = case ft' of
       10 -> put'Fields
       11 -> do
               P'.putSize (P'.wireSize 10 self')
               put'Fields
       _ -> P'.wirePutErr ft' self'
    where
        put'Fields
         = do
             P'.wirePutReq 10 11 x'1
             P'.wirePutRep 18 11 x'2
             P'.wirePutReq 24 4 x'3
             P'.wirePutReq 34 9 x'4
  wireGet ft'
   = case ft' of
       10 -> P'.getBareMessageWith update'Self
       11 -> P'.getMessageWith update'Self
       _ -> P'.wireGetErr ft'
    where
        update'Self wire'Tag old'Self
         = case wire'Tag of
             10 -> Prelude'.fmap (\ !new'Field -> old'Self{func = P'.mergeAppend (func old'Self) (new'Field)}) (P'.wireGet 11)
             18 -> Prelude'.fmap (\ !new'Field -> old'Self{hint = P'.append (hint old'Self) new'Field}) (P'.wireGet 11)
             24 -> Prelude'.fmap (\ !new'Field -> old'Self{p = new'Field}) (P'.wireGet 4)
             34 -> Prelude'.fmap (\ !new'Field -> old'Self{gad = new'Field}) (P'.wireGet 9)
             _ -> let (field'Number, wire'Type) = P'.splitWireTag wire'Tag in P'.unknown field'Number wire'Type old'Self

instance P'.MessageAPI msg' (msg' -> HTunnelHints) HTunnelHints where
  getVal m' f' = f' m'

instance P'.GPB HTunnelHints

instance P'.ReflectDescriptor HTunnelHints where
  getMessageInfo _ = P'.GetMessageInfo (P'.fromDistinctAscList [10, 24, 34]) (P'.fromDistinctAscList [10, 18, 24, 34])
  reflectDescriptorInfo _
   = Prelude'.read
      "DescriptorInfo {descName = ProtoName {protobufName = FIName \".SHEHint.HTunnelHints\", haskellPrefix = [MName \"Crypto\",MName \"Proto\"], parentModule = [MName \"SHEHint\"], baseName = MName \"HTunnelHints\"}, descFilePath = [\"Crypto\",\"Proto\",\"SHEHint\",\"HTunnelHints.hs\"], isGroup = False, fields = fromList [FieldInfo {fieldName = ProtoFName {protobufName' = FIName \".SHEHint.HTunnelHints.func\", haskellPrefix' = [MName \"Crypto\",MName \"Proto\"], parentModule' = [MName \"SHEHint\",MName \"HTunnelHints\"], baseName' = FName \"func\", baseNamePrefix' = \"\"}, fieldNumber = FieldId {getFieldId = 1}, wireTag = WireTag {getWireTag = 10}, packedTag = Nothing, wireTagLength = 1, isPacked = False, isRequired = True, canRepeat = False, mightPack = False, typeCode = FieldType {getFieldType = 11}, typeName = Just (ProtoName {protobufName = FIName \".RLWE.LinearRq\", haskellPrefix = [MName \"Crypto\",MName \"Proto\"], parentModule = [MName \"RLWE\"], baseName = MName \"LinearRq\"}), hsRawDefault = Nothing, hsDefault = Nothing},FieldInfo {fieldName = ProtoFName {protobufName' = FIName \".SHEHint.HTunnelHints.hint\", haskellPrefix' = [MName \"Crypto\",MName \"Proto\"], parentModule' = [MName \"SHEHint\",MName \"HTunnelHints\"], baseName' = FName \"hint\", baseNamePrefix' = \"\"}, fieldNumber = FieldId {getFieldId = 2}, wireTag = WireTag {getWireTag = 18}, packedTag = Nothing, wireTagLength = 1, isPacked = False, isRequired = False, canRepeat = True, mightPack = False, typeCode = FieldType {getFieldType = 11}, typeName = Just (ProtoName {protobufName = FIName \".SHEHint.KSLinearHint\", haskellPrefix = [MName \"Crypto\",MName \"Proto\"], parentModule = [MName \"SHEHint\"], baseName = MName \"KSLinearHint\"}), hsRawDefault = Nothing, hsDefault = Nothing},FieldInfo {fieldName = ProtoFName {protobufName' = FIName \".SHEHint.HTunnelHints.p\", haskellPrefix' = [MName \"Crypto\",MName \"Proto\"], parentModule' = [MName \"SHEHint\",MName \"HTunnelHints\"], baseName' = FName \"p\", baseNamePrefix' = \"\"}, fieldNumber = FieldId {getFieldId = 3}, wireTag = WireTag {getWireTag = 24}, packedTag = Nothing, wireTagLength = 1, isPacked = False, isRequired = True, canRepeat = False, mightPack = False, typeCode = FieldType {getFieldType = 4}, typeName = Nothing, hsRawDefault = Nothing, hsDefault = Nothing},FieldInfo {fieldName = ProtoFName {protobufName' = FIName \".SHEHint.HTunnelHints.gad\", haskellPrefix' = [MName \"Crypto\",MName \"Proto\"], parentModule' = [MName \"SHEHint\",MName \"HTunnelHints\"], baseName' = FName \"gad\", baseNamePrefix' = \"\"}, fieldNumber = FieldId {getFieldId = 4}, wireTag = WireTag {getWireTag = 34}, packedTag = Nothing, wireTagLength = 1, isPacked = False, isRequired = True, canRepeat = False, mightPack = False, typeCode = FieldType {getFieldType = 9}, typeName = Nothing, hsRawDefault = Nothing, hsDefault = Nothing}], descOneofs = fromList [], keys = fromList [], extRanges = [], knownKeys = fromList [], storeUnknown = False, lazyFields = False, makeLenses = False}"

instance P'.TextType HTunnelHints where
  tellT = P'.tellSubMessage
  getT = P'.getSubMessage

instance P'.TextMsg HTunnelHints where
  textPut msg
   = do
       P'.tellT "func" (func msg)
       P'.tellT "hint" (hint msg)
       P'.tellT "p" (p msg)
       P'.tellT "gad" (gad msg)
  textGet
   = do
       mods <- P'.sepEndBy (P'.choice [parse'func, parse'hint, parse'p, parse'gad]) P'.spaces
       Prelude'.return (Prelude'.foldl (\ v f -> f v) P'.defaultValue mods)
    where
        parse'func
         = P'.try
            (do
               v <- P'.getT "func"
               Prelude'.return (\ o -> o{func = v}))
        parse'hint
         = P'.try
            (do
               v <- P'.getT "hint"
               Prelude'.return (\ o -> o{hint = P'.append (hint o) v}))
        parse'p
         = P'.try
            (do
               v <- P'.getT "p"
               Prelude'.return (\ o -> o{p = v}))
        parse'gad
         = P'.try
            (do
               v <- P'.getT "gad"
               Prelude'.return (\ o -> o{gad = v}))