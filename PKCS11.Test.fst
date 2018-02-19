module PKCS11.Test

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.UInt32
open FStar.Option

open FStar.Buffer

open PKCS11.TypeDeclaration
open PKCS11.Parse
open PKCS11.Exception

open PKCS11.Attribute
open PKCS11.Mechanism
open PKCS11.Objects

open FStar.List

type _CK_RV = FStar.UInt32.t
type _CK_BBOOL = bool
type _CK_OBJECT_CLASS = buffer FStar.UInt32.t

type int = FStar.UInt32.t

(*CK_RV createKeyObject(CK_SESSION_HANDLE hSession, CK_BYTE_PTR key, CK_ULONG keyLength) {
  CK_RV rc;

  CK_OBJECT_HANDLE hKey;
  CK_BBOOL true = TRUE;
  CK_BBOOL false = FALSE;

  CK_OBJECT_CLASS keyClass = CKO_SECRET_KEY;
  CK_KEY_TYPE keyType = CKK_AES;
  CK_ATTRIBUTE keyTempl[] = {
    {CKA_CLASS (* ulong *), &keyClass, sizeof(keyClass)},
    {CKA_KEY_TYPE, &keyType, sizeof(keyType)},
    {CKA_ENCRYPT, &true, sizeof(true)},
    {CKA_DECRYPT, &true, sizeof(true)},
    {CKA_SIGN, &true, sizeof(true)},
    {CKA_VERIFY, &true, sizeof(true)},
    {CKA_TOKEN, &true, sizeof(true)},     /* token object  */
    {CKA_PRIVATE, &false, sizeof(false)}, /* public object */
    {CKA_VALUE, keyValue, keyLength}, /* AES key       */
    {CKA_LABEL, "My_AES_Key", sizeof("My_AES_Key")}
  };
  rc = C_CreateObject(hSession, keyTempl, sizeof (keyTempl)/sizeof (CK_ATTRIBUTE), &hKey);
  if (rc != CKR_OK) {
  printf("Error creating key object: 0x%X\n", rc); return rc;
  }
  printf("AES Key object creation successful.\n");
}
 *)

(* type ex_result = 
  |Ex : #a:Type -> r:result a -> ex_result

let is_exception = function Ex (Inr _) -> true | _ -> false 
 *)

val checkAttributes: attr: buffer attribute_t -> m: mechanism -> Tot (result bool)

let checkAttributes attr m = Inl true (*)
   // let check1 = atrributesAllValid attr in 
    let check2 = attributesForAllNotReadOnly attr in 
    let check3 = attributesSufficient attr m in 
    (* +  two inconsistencies *) 
    if ( check2 && check3) then 
      (Inl true) else (Inr TestExc)  *)


assume val getMemory: unit -> StackInline (sBuffer _CK_ULONG)
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))


val _CK_C_GenerateKey: hsession: _CK_SESSION_HANDLE -> 
    pMechanism: _CK_MECHANISM -> 
    pTemplate: buffer _CK_ATTRIBUTE -> usCount: FStar.UInt32.t -> 
    phKey: _CK_OBJECT_HANDLE -> 
    Stack _CK_RV
      (requires (fun h -> True))
      (ensures (fun h0 _ h1 -> True))


let _CK_C_GenerateKey hSession pMechanism pTemplate usCount phKey  = 
    let reference = getTheReference phKey in 
    let memory = getMemory() in 
    let b =  getSBufferB memory in 
    let l = getSBufferLength memory in 
      (* version 1 *)
    let parsedMechanism = parseMechanism pMechanism b l  in 
    if not (resultIsOk parsedMechanism) then 
      castExpectionToRV(Inl true) else
    let unpackedMechanism = resultLeft parsedMechanism in 
      if not (isMechanismGeneration unpackedMechanism) then
        castExpectionToRV(Inl true) else

    let unpackedReference = resultLeft reference in 
    let f = mechanismGetFunctionGeneration unpackedMechanism in 
    f unpackedReference 100ul; 
      (* version 1*)

    //let parseAttributes = parseAttributes pTemplate in 
      castExpectionToRV(Inl true) (*)
    let parsedAttributes = parseAttributes pTemplate in 
    let parsedMechanism = parseMechanism pMechanism in 
     (* TODO: check session *)
    let result = resultIsOk parsedAttributes && resultIsOk parsedMechanism
        && resultIsOk reference in

    if result then begin
      let unpackedMechanism = resultLeft parsedMechanism in 
      let unpackedAttributes = resultLeft parsedAttributes in 
      let unpackedReference = resultLeft reference in 
      let attributes_correct = checkAttributes unpackedAttributes unpackedMechanism in 
      if not (resultIsOk attributes_correct) then 
        let exc =  Inr #bool (resultRight attributes_correct) in 
        castExpectionToRV exc
      else    
        (*Check is completed *)
        (*let keyLengthAttributeUnpacked = attrubuteSearchKeyLength unpackedAttributes in *)
        (*(mechanismGetFunctionGeneration unpackedMechanism) unpackedReference 100ul;*)
      castExpectionToRV(Inl true)
    end  
    else 
      begin 
        castExpectionToRV(Inr #bool (expectionChoose parsedAttributes parsedMechanism))
      end
  
  *)

let main()  = 
  let hSession = 10ul in 
  let pMechanism = MechanismRaw 01ul () 1ul in 
  let testAttribute = AttributeRaw 1ul () 0ul in 
  let pTemplate = createL [testAttribute] in 
  let usCount = 0ul in 
  let phKey = 0ul in 
  let r = _CK_C_GenerateKey hSession pMechanism pTemplate usCount phKey in 
  0x1ul