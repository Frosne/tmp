module PKCS11.TypeDeclaration 

open PKCS11.DateTime

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All
open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

type _CK_ULONG = FStar.UInt32.t

type _CK_ATTRIBUTE_TYPE = _CK_ULONG 
type _CK_MECHANISM_TYPE = _CK_ULONG 
type _CK_SESSION_HANDLE = _CK_ULONG
type _CK_OBJECT_HANDLE = _CK_ULONG

type _CK_RV = _CK_ULONG


type bytes = buffer FStar.UInt8.t
type int = FStar.UInt64.t

(* Pointer Section  *)

(*assume type _CK_VOID_PTR*)  (*well, I am magic *)
type _CK_VOID_PTR = unit

assume val ptrCastToBool: _CK_VOID_PTR -> buffer bool

(*https://stackoverflow.com/questions/3559656/casting-void-pointers *)

(*Note that pValue is a “void” pointer, facilitating the passing of
arbitrary values. Both the application and Cryptoki library MUST
ensure that the pointer can be safely cast to the expected type (i.e.,
without word-alignment errors) *)
val castableToBool: length : _CK_ULONG -> Tot bool

let castableToBool length = 
	let open FStar.UInt32 in 
	if (gt length 0ul) && (eq (rem length 4ul) 0ul) then 
		true
	else false	

(*/Pointer Section  *)
type attributeClass = 
	|CL:  typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x0ul} -> pValue: buffer _CK_ULONG -> 
		ulValueLength: _CK_ULONG -> isReadOnly: bool-> attributeClass 

noeq type attribute_t  = 
	| CKA_CLASS: params: attributeClass ->  attribute_t
	| CKA_TOKEN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x1ul}->  pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_PRIVATE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x2ul} ->  pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_LABEL: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x3ul} ->  pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_APPLICATION:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x10ul} ->pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_VALUE:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x11ul} ->pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_OBJECT_ID:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x12ul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_CERTIFICATE_TYPE:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x80ul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_ISSUER:typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x81ul} ->pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_SERIAL_NUMBER: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x82ul}-> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_KEY_TYPE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x100ul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_ID: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x102ul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_SENSITIVE: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x103ul} ->pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_ENCRYPT: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x104ul} ->pValue: buffer bool -> ulValueLength: _CK_ULONG-> isReadOnly: bool -> a: attribute_t
	| CKA_DECRYPT: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x105ul}->pValue: buffer bool -> ulValueLength: _CK_ULONG-> isReadOnly: bool -> a: attribute_t
	| CKA_WRAP: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x106ul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_UNWRAP: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x107ul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_SIGN: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x108ul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t
	| CKA_VERIFY: typeId: _CK_ATTRIBUTE_TYPE{typeId= 0x10Aul} -> pValue: _CK_VOID_PTR -> ulValueLength: _CK_ULONG{castableToBool ulValueLength}-> isReadOnly: bool -> a: attribute_t

type flags_t = fl: buffer bool

type mechGen = | Ge: mechanismID: _CK_MECHANISM_TYPE -> 
			m : (buffer FStar.UInt8.t -> 
				FStar.UInt32.t -> Stack unit 
				(requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))) ->
			pParameters: _CK_VOID_PTR -> 
			ulParameterLen : _CK_ULONG -> 
			attrs: (buffer attribute_t) ->
			attributesLen: _CK_ULONG -> 
			attributesRequired: (buffer _CK_ATTRIBUTE_TYPE) -> 
			attributesRequiredList: _CK_ULONG ->  mechGen

type mechanism = 
		| Generation: a: mechGen -> mechanism
		| Test: mechanismID: _CK_MECHANISM_TYPE -> mechanism	
		| NotFoundMechanism:  mechanism	

noeq (* TODO - to check *)
type _CK_ATTRIBUTE =  |AttributeRaw: _type: _CK_ATTRIBUTE_TYPE -> 
	pValue : _CK_VOID_PTR ->  ulValueLen : _CK_ULONG  -> _CK_ATTRIBUTE

type _CK_MECHANISM =  |MechanismRaw: _type: _CK_MECHANISM_TYPE-> 
	pParameter: _CK_VOID_PTR ->ulParameterLen : _CK_ULONG->  _CK_MECHANISM

(*let cryptoKiAttributesIsReadOnly = (function | 4uL -> true | _ -> false)*)

type sBuffer 'a = 
	| SBuffer: b: buffer 'a  -> l: FStar.UInt32.t{length b == UInt32.v l} -> sBuffer 'a

val getSBufferB: sBuffer 'a -> buffer 'a

let getSBufferB a = 
	match a with
	| SBuffer b _ -> b

val getSBufferLength: sBuffer 'a -> FStar.UInt32.t

let getSBufferLength a = 
	match a with
	| SBuffer _ l -> l