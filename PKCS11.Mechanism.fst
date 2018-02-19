module PKCS11.Mechanism

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.HyperStack
open FStar.Ghost

open FStar.Seq
open FStar.Buffer

open PKCS11.DateTime
open PKCS11.TypeDeclaration
open FStar.Option

(* Getters *)

assume val isMechanismGeneration: m: mechanism -> Tot bool
(*)
let isMechanismGeneration m = 
	match m with
	| Generation _ _ _ _ _ _ _ _  -> true
	| _ -> false
*)
val isMechanismFound: m: mechanism -> Tot bool

let isMechanismFound m = 
	match m with
	| NotFoundMechanism -> true
	| _ -> false	

assume val mechanismGetType: m: mechanism -> Tot _CK_MECHANISM_TYPE
(*)
let mechanismGetType m = 
	match m with 
	| Generation identifier _ _ _ _ _ _ _   -> identifier
	| _ -> 0ul
*)

assume val mechanismGetFunctionGeneration: m: mechanism{isMechanismGeneration m} -> 
	Tot (buffer FStar.UInt8.t -> 
		FStar.UInt32.t -> Stack unit 
			(requires (fun h -> True)) 
			(ensures (fun h0 _ h1 -> True))
		)
(*)
let mechanismGetFunctionGeneration m = 
	match m with 
	| Generation _ f _ _ _ _ _ _  -> f 
*)
val mechanismRawGetTypeID: m: _CK_MECHANISM -> Tot _CK_MECHANISM_TYPE	

let mechanismRawGetTypeID m = 
	match m with 
	|MechanismRaw t _ _ -> t

val getMechanismRawParameters: m: _CK_MECHANISM -> Tot _CK_VOID_PTR 

let getMechanismRawParameters m = 
	match m with 
	|MechanismRaw _ par _ -> par


val getMechanismRawParametersLen: m: _CK_MECHANISM -> Tot _CK_ULONG

let getMechanismRawParametersLen m = 
	match m with 
	|MechanismRaw _ _ len -> len
(* /Getters *)

(*
If the attribute values in the supplied template, together with any
default attribute values and any attribute values contributed to the
object by the object-creation function itself, are insufficient to
fully specify the object to create, then the attempt should fail with
the error code CKR_TEMPLATE_INCOMPLETE. 
*)

(*2.33.3 Blowfish key generation

The Blowfish key generation mechanism, denoted CKM_BLOWFISH_KEY_GEN,
is a key generation mechanism Blowfish.

It does not have a parameter.

The mechanism generates Blowfish keys with a particular length, as
specified in the CKA_VALUE_LEN attribute of the template for the key.

The mechanism contributes the CKA_CLASS, CKA_KEY_TYPE, and CKA_VALUE
attributes to the new key. Other attributes supported by the key type
(specifically, the flags indicating which functions the key supports)
may be specified in the template for the key, or else are assigned
default initial values.

For this mechanism, the ulMinKeySize and ulMaxKeySize fields of the
CK_MECHANISM_INFO structure specify the supported range of key sizes
in byte *)

val getMemoryIndexForMechanism: m: _CK_MECHANISM_TYPE ->  b: buffer 'a-> 
	len: FStar.UInt32.t{length b == UInt32.v len} -> 
	start: FStar.UInt32.t -> 
	finish: FStar.UInt32.t -> 
	Stack (buffer 'a) 
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let getMemoryIndexForMechanism m b len start finish= 
	sub b start finish

assume val getAddressOfMechanismAttributes: m: mechanism -> 
	Tot (buffer attribute_t)
(*)
let getAddressOfMechanismAttributes m = 
	match m with 
	| Generation _ _ _ _ attrs _ _ _  -> attrs
*)
assume val getAddressOfMechanismRequiredAttributes: m: mechanism -> 
	Tot (buffer _CK_ATTRIBUTE_TYPE)

(* let getAddressOfMechanismRequiredAttributes m = 
	match m with 
	| Generation _ _ _ _ _ _ attrs _  -> attrs
*)
val mechanismAttributesProvidedList: m: mechanism -> StackInline (buffer attribute_t)
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let mechanismAttributesProvidedList m  = 
	getAddressOfMechanismAttributes m 
(*)
val mechanismRequiredAttributes: m: mechanism -> Stack (sBuffer _CK_ATTRIBUTE_TYPE)
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let mechanismRequiredAttributes m = 
	let id = mechanismGetType m in 
	mechanismAttributesRequiredList id

val getAttributesProvidedByMechanism: m: mechanism -> Stack (buffer attribute_t)
	(requires (fun h -> True))
	(ensures (fun h0 _ h1 -> True))

let getAttributesProvidedByMechanism m = 
	mechanismAttributesProvidedList (mechanismGetType m)
