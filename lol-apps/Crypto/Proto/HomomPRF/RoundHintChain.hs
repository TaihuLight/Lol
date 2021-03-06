{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveGeneric, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC  -fno-warn-unused-imports #-}
module Crypto.Proto.HomomPRF.RoundHintChain (RoundHintChain(..)) where
import Prelude ((+), (/))
import qualified Prelude as Prelude'
import qualified Data.Typeable as Prelude'
import qualified GHC.Generics as Prelude'
import qualified Data.Data as Prelude'
import qualified Text.ProtocolBuffers.Header as P'
import qualified Crypto.Proto.SHE.KSHint as Crypto.Proto.SHE (KSHint)

data RoundHintChain = RoundHintChain{hints :: !(P'.Seq Crypto.Proto.SHE.KSHint)}
                    deriving (Prelude'.Show, Prelude'.Eq, Prelude'.Ord, Prelude'.Typeable, Prelude'.Data, Prelude'.Generic)

instance P'.Mergeable RoundHintChain where
  mergeAppend (RoundHintChain x'1) (RoundHintChain y'1) = RoundHintChain (P'.mergeAppend x'1 y'1)

instance P'.Default RoundHintChain where
  defaultValue = RoundHintChain P'.defaultValue

instance P'.Wire RoundHintChain where
  wireSize ft' self'@(RoundHintChain x'1)
   = case ft' of
       10 -> calc'Size
       11 -> P'.prependMessageSize calc'Size
       _ -> P'.wireSizeErr ft' self'
    where
        calc'Size = (P'.wireSizeRep 1 11 x'1)
  wirePut ft' self'@(RoundHintChain x'1)
   = case ft' of
       10 -> put'Fields
       11 -> do
               P'.putSize (P'.wireSize 10 self')
               put'Fields
       _ -> P'.wirePutErr ft' self'
    where
        put'Fields
         = do
             P'.wirePutRep 10 11 x'1
  wireGet ft'
   = case ft' of
       10 -> P'.getBareMessageWith update'Self
       11 -> P'.getMessageWith update'Self
       _ -> P'.wireGetErr ft'
    where
        update'Self wire'Tag old'Self
         = case wire'Tag of
             10 -> Prelude'.fmap (\ !new'Field -> old'Self{hints = P'.append (hints old'Self) new'Field}) (P'.wireGet 11)
             _ -> let (field'Number, wire'Type) = P'.splitWireTag wire'Tag in P'.unknown field'Number wire'Type old'Self

instance P'.MessageAPI msg' (msg' -> RoundHintChain) RoundHintChain where
  getVal m' f' = f' m'

instance P'.GPB RoundHintChain

instance P'.ReflectDescriptor RoundHintChain where
  getMessageInfo _ = P'.GetMessageInfo (P'.fromDistinctAscList []) (P'.fromDistinctAscList [10])
  reflectDescriptorInfo _
   = Prelude'.read
      "DescriptorInfo {descName = ProtoName {protobufName = FIName \".crypto.proto.HomomPRF.RoundHintChain\", haskellPrefix = [], parentModule = [MName \"Crypto\",MName \"Proto\",MName \"HomomPRF\"], baseName = MName \"RoundHintChain\"}, descFilePath = [\"Crypto\",\"Proto\",\"HomomPRF\",\"RoundHintChain.hs\"], isGroup = False, fields = fromList [FieldInfo {fieldName = ProtoFName {protobufName' = FIName \".crypto.proto.HomomPRF.RoundHintChain.hints\", haskellPrefix' = [], parentModule' = [MName \"Crypto\",MName \"Proto\",MName \"HomomPRF\",MName \"RoundHintChain\"], baseName' = FName \"hints\", baseNamePrefix' = \"\"}, fieldNumber = FieldId {getFieldId = 1}, wireTag = WireTag {getWireTag = 10}, packedTag = Nothing, wireTagLength = 1, isPacked = False, isRequired = False, canRepeat = True, mightPack = False, typeCode = FieldType {getFieldType = 11}, typeName = Just (ProtoName {protobufName = FIName \".crypto.proto.SHE.KSHint\", haskellPrefix = [], parentModule = [MName \"Crypto\",MName \"Proto\",MName \"SHE\"], baseName = MName \"KSHint\"}), hsRawDefault = Nothing, hsDefault = Nothing}], descOneofs = fromList [], keys = fromList [], extRanges = [], knownKeys = fromList [], storeUnknown = False, lazyFields = False, makeLenses = False}"

instance P'.TextType RoundHintChain where
  tellT = P'.tellSubMessage
  getT = P'.getSubMessage

instance P'.TextMsg RoundHintChain where
  textPut msg
   = do
       P'.tellT "hints" (hints msg)
  textGet
   = do
       mods <- P'.sepEndBy (P'.choice [parse'hints]) P'.spaces
       Prelude'.return (Prelude'.foldl (\ v f -> f v) P'.defaultValue mods)
    where
        parse'hints
         = P'.try
            (do
               v <- P'.getT "hints"
               Prelude'.return (\ o -> o{hints = P'.append (hints o) v}))