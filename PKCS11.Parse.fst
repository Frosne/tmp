module PKCS11.Parse


module ST = FStar.HyperStack.ST

open FStar.HyperStack.All


open FStar.Mul
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer

open PKCS11.TypeDeclaration
open PKCS11.Attribute
open PKCS11.Mechanism
open PKCS11.Exception
open PKCS11.DateTime
open PKCS11.Cast

open FStar.Option

(*)
assume val parseAttributeDerive: attr_r: _CK_ATTRIBUTE -> 
	Tot (result (attr: attribute_t{attributeGetTypeID attr = attributeRawGetTypeID attr_r /\ 
		(let f = (function| Derive _ _ _ _ -> True | _ -> False) in f attr)
		}
	)
)
*)




val parseAttribute: attr_r: _CK_ATTRIBUTE -> 
	Stack (result (attr: attribute_t(*{attributeGetTypeID attr = attributeRawGetTypeID attr_r})*)))
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let parseAttribute attr_r = 
	let typ = attributeRawGetTypeID attr_r in 
	let data = attributeRawGetData attr_r in 
	let length = attributeRawGetLength attr_r in 
	let isReadOnly = (*cryptoKiAttributesIsReadOnly typ *) false in 
	if (UInt32.v typ) = 0 then 
			let pointer = castToUlong data in 
			let length = changeSizeOfBuffer length in 
			let attr = CL typ pointer length (attributesIsReadOnly typ) in 
			let attr = CKA_CLASS attr in 
			Inl (attr) 
		else
			(*(CKA_CLASS typ pointer length (attributesIsReadOnly typ)) *)
	(*| 1 -> let data = (if length = 0 then None else Some data) in 
			let attribute = ID typ data length isReadOnly in
				Inl attribute
	| 2 -> let data = Some Seq.createEmpty(*(if length = 0 then None else Some (parseDate data))*) in 
				let attribute = CKA_PRIVATE typ data length isReadOnly in
					Inl attribute
	| 4 -> let data = (if length = 0 then None else Some (bytesToBoolean data length)) in 
				let attribute = Derive typ data length isReadOnly in 
					Inl attribute *) 
	 Inr (TestExc) (*In *)


val _buffer_map: #a: Type -> #b: Type -> b1: buffer a -> b2: buffer b -> 
	f: (a -> Stack (result b)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))) -> 
	len: FStar.UInt32.t -> 
	counter: FStar.UInt32.t -> 
	StackInline (result unit)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let rec _buffer_map #a #b b1 b2 f len counter  = 
	if UInt32.eq counter len then Inl ()
	else 
		let element = (f b1.(counter)) in 
		if resultIsOk element then 
	begin
		let toChange = index b1 counter in 
		let changed = f toChange in 
		if not (resultIsOk changed) then 
			Inr (TestExc)
		else 
			let unpackedChanged = resultLeft changed in 	
		upd b2 counter unpackedChanged;
		_buffer_map #a #b b1 b2 f len counter
	end
		else
			Inr (TestExc)

val buffer_map: #a: Type -> #b: Type -> b1: buffer a -> b2: buffer b -> f: (a -> Stack(result b)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))) -> 
	len: FStar.UInt32.t -> 
	StackInline (result unit)
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let buffer_map #a #b b1 b2 f len = 
	_buffer_map #a #b b1 b2 f len 0ul

(*the first attribute worked twice *)
val parseAttributes: attr_r: buffer _CK_ATTRIBUTE{length attr_r > 0}-> 
	len: UInt32.t -> StackInline (result (buffer attribute_t))
		(requires (fun h -> True))
		(ensures (fun h0 _ h1 -> True))

let parseAttributes attr_r len = 
		assume(length attr_r > UInt32.v 0ul);
	let e1 = parseAttribute attr_r.(0ul) in
		if not (resultIsOk e1) then
			Inr TestExc
		else	
	let e1 = resultLeft e1 in 	 
	let buff = create e1 len in 
	let r = buffer_map attr_r buff parseAttribute len in 
	if resultIsOk r then 
		Inl buff 
	else 
		Inr TestExc	

val rng_algorithm: input: buffer FStar.UInt8.t ->  length: FStar.UInt32.t -> 
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))

let rng_algorithm input length = 
	let zero = 0x1uy in 
	upd input 0ul zero    

assume val rng_algorithm2: input: buffer FStar.UInt8.t ->  length: FStar.UInt32.t -> 
  Stack unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))    

(* memory distribution  *)
(* mechanism1 : values for attributes - usually there are just three of them, where the third one is
value - no need to store*)
(*the list of required attributes *)

val memoryMap: index: FStar.UInt32.t -> Tot(indexInBuffer: FStar.UInt32.t)
let memoryMap index = 
	if (FStar.UInt32.v index = 0) then 0ul
	else 0ul

val parseMechanism: m: _CK_MECHANISM-> b: buffer _CK_ULONG-> 
	len: FStar.UInt32.t{length b == UInt32.v len} -> Stack(result mechanism)
		(requires (fun h -> True))
	    (ensures (fun h0 _ h1 -> True)) 

let parseMechanism m b len = 
	let id = mechanismRawGetTypeID m in 
	let params = getMechanismRawParameters m in 
	let paramLen = getMechanismRawParametersLen m in 
	if (UInt32.v id) = 1 then (*Generation mechanisms *)
		
		let startIndex = memoryMap id in 

		let lengthProvidedAttr = 2ul in 
		let lengthRequiredAttr = 0ul in 

		let indForProvidedAttributes = startIndex in 
		let indForRequiredAttributes = FStar.UInt32.add lengthProvidedAttr indForProvidedAttributes in 

		let providedAttrs = getMemoryIndexForMechanism id b len indForProvidedAttributes lengthProvidedAttr in 
		let requiredAttrs = getMemoryIndexForMechanism id b len indForRequiredAttributes lengthRequiredAttr in 

		let providedAttr0 = sub providedAttrs 0ul 1ul in 
		let providedAttr1 = sub providedAttrs 1ul 1ul in 

		let attr0 = CKA_CLASS (CL 0ul providedAttr0 1ul false) in 
		let attr1 = CKA_CLASS (CL 0ul providedAttr1 1ul false) in 

		let bufferForProvidedAttributes = createL [attr0; attr1] in 
 
		let m = Generation (Ge id rng_algorithm params paramLen bufferForProvidedAttributes lengthProvidedAttr
		 requiredAttrs lengthRequiredAttr) in 
		Inl m
	else
		Inr (TestExc)		
	
