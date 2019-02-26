open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let deriver = "tupleable"
let raise_errorf = Ppx_deriving.raise_errorf

(* zip2 : ('a list * 'b list) -> ('a * 'b * 'c * 'd) list *)
let zip2 xs ys = List.map2 (fun x y -> (x, y)) xs ys

(* unzip3 : ('a * 'b * 'c) list -> ('a list * 'b list * 'c list) *)
let unzip3 l =
  List.fold_right (fun (v1,v2,v3) (a1,a2,a3) -> (v1::a1, v2::a2, v3::a3)) l ([],[],[])

(* ------------------------------------------------
   --- useful helpers from ppx_deriving_yojson  --- *)
(* calls `f` on the contents of a structure *)
let structure f ~options ~path type_ =
  let (pre, vals, post) = f ~options ~path type_ in
  match vals with
  | [] -> pre @ post
  | _  -> pre @ [Str.value ?loc:None Recursive vals] @ post

(* calls `f` on each type declaration in a structure *)
let on_str_decls f ~options ~path type_decls =
  let (pre, vals, post) = unzip3 (List.map (f ~options ~path) type_decls) in
  (List.concat pre, List.concat vals, List.concat post)

(* calls `f` on each type declaration in a signature *)
let on_sig_decls f ~options ~path type_decls =
  List.concat (List.map (f ~options ~path) type_decls)
(* ------------------------------------------------ *)

(* str_to_lid : string loc -> longident loc
   str_to_lid : Ast_helper.str -> Ast_helper.lid *)
let str_to_lid { txt; loc } = { txt = Lident txt; loc = loc }

(* generate_temporaries : string -> 'a list -> string list *)
(* Generates a list of strings based on `base` with different numbers added to the end *)
let generate_temporaries base vs = List.mapi (fun i _ -> base ^ string_of_int i) vs

(* A "bidirectional case" is a tuple of four values:
    * a `pattern` that matches the record type
    * a `pattern` that matches the tuple
    * an `expression` that reconstructs record type
    * an `expression` that reconstructs tuple
 *)
type bidirectional_case = (pattern * pattern * expression * expression)

(* case_data_to_tuple : bidirectional_case -> Parsetree.case *)
(* Generates a Parsetree match case for converting from data to a tuple *)
let case_data_to_tuple (data_pat, _, _, tup_exp) = Exp.case data_pat tup_exp

(* case_tuple_to_data : bidirectional_case -> Parsetree.case *)
(* Generates a Parsetree match case for converting from a tuple to data *)
let case_tuple_to_data (_, tup_pat, data_exp, _) = Exp.case tup_pat data_exp

(* ctor_tup_args : (pat list -> pat) -> pat list -> pat option
   ctor_tup_args : (exp list -> exp) -> exp list -> exp option *)
let ctor_tup_args tuple args =
  match args with
  | []    -> None
  | [arg] -> Some arg
  | args  -> Some (tuple args)

(* ------------------------------------------------ *)

type 'a tua_ops = { to_tuple: 'a;
                    of_tuple: 'a }

let tua_ops_to_list { to_tuple; of_tuple }
  =
  [ to_tuple; of_tuple ]

let tua_op_map f { to_tuple; of_tuple }
  =
  { to_tuple = f to_tuple;
    of_tuple = f of_tuple }

let tua_op_map2 f a b =
  { to_tuple = f a.to_tuple b.to_tuple;
    of_tuple = f a.of_tuple b.of_tuple }

let tua_op_names = { to_tuple = "to_tuple";
                     of_tuple = "of_tuple" }

let tua_op_types data_t tup_t =
  { to_tuple = Typ.arrow Nolabel data_t tup_t;
    of_tuple = Typ.arrow Nolabel tup_t data_t }

(* ------------------------------------------------ *)

(* ppx_deriving_tupleable always uses suffixes. Never prefixes, and never both. *)
let mangle_type_decl_suffix s = Ppx_deriving.mangle_type_decl (`Suffix s)

let core_type_to_case ty tmp : bidirectional_case =
  match ty.ptyp_desc with
  | Ptyp_tuple _ -> (pvar tmp, pvar tmp, evar tmp, evar tmp) (* already a tuple *)
  | _            -> (pvar tmp, pvar tmp, evar tmp, evar tmp)

let record_fields_to_case flds tmp =
  let tmps = generate_temporaries tmp flds
  and lids = List.map (fun fld -> str_to_lid fld.pld_name) flds in
  let pats = List.map pvar tmps
  and exps = List.map evar tmps
  in (Pat.record (zip2 lids pats) Closed,
      ctor_tup_args Pat.tuple pats,
      Exp.record (zip2 lids exps) None,
      ctor_tup_args Exp.tuple exps)

let constructor_arguments_to_case pcd_args tmp =
  match pcd_args with
  | Pcstr_tuple tys ->
    let tmps = generate_temporaries tmp tys in
    let pats = List.map pvar tmps
    and exps = List.map evar tmps
    in (ctor_tup_args Pat.tuple pats,
        ctor_tup_args Pat.tuple pats,
        ctor_tup_args Exp.tuple exps,
        ctor_tup_args Exp.tuple exps)
  | Pcstr_record flds ->
    let (data_pat, tup_pat, data_exp, tup_exp) = record_fields_to_case flds tmp
    in (Some data_pat, tup_pat, Some data_exp, tup_exp)

let type_decl_record_to_case (fields : label_declaration list) tmp =
  let (data_pat, tup_pat, data_exp, tup_exp) = record_fields_to_case fields tmp
  in (data_pat,
      (match tup_pat with Some v -> v | None -> punit ()),
      data_exp,
      (match tup_exp with Some v -> v | None -> unit ()))

let type_decl_variant_to_case { pcd_name; pcd_args; pcd_res; pcd_loc; pcd_attributes } tmp =
  ignore pcd_loc; ignore pcd_attributes;
  (* pcd_res is used for GADTs, but we don't support those yet, so if its there, raise an error *)
  (match pcd_res with | None -> () | _ -> raise_errorf "ppx_deriving_tupleable: GADTs are not yet supported");
  let name_lid = str_to_lid pcd_name
  and (data_pat, tup_pat, data_exp, tup_exp) = constructor_arguments_to_case pcd_args tmp
  in (Pat.construct name_lid data_pat,
      (match tup_pat with Some v -> v | None -> punit ()),
      Exp.construct name_lid data_exp,
      (match tup_exp with Some v -> v | None -> unit ()))

let type_decl_variants_to_cases (variants : constructor_declaration list) tmp =
  match variants with
  | [variant] -> [type_decl_variant_to_case variant tmp]
  | _         -> raise_errorf "ppx_deriving_tupleable: multiple-variant ADTs are not yet supported"

(* Produces a tuple of the "to" function and the "of" function *)
let type_decl_record_to_funs fields =
  let (data_pat, tup_pat, data_exp, tup_exp) = type_decl_record_to_case fields "tmp" in
  ((lam data_pat tup_exp),
   (lam tup_pat data_exp))

(* Produces a tuple of the "to" function and the "of" function *)
let type_decl_variants_to_funs variants =
  let bidi_cases = type_decl_variants_to_cases variants "tmp" in
  ((lam (pvar "x")
     (Exp.match_
       (evar "x")
       (List.map case_data_to_tuple bidi_cases))),
   (lam (pvar "x")
     (Exp.match_
       (evar "x")
       (List.map case_tuple_to_data bidi_cases))))

(* Produces a tuple of the "to" function and the "of" function *)
let type_decl_manifest_to_funs manifest =
  match manifest with
  | None    -> raise_errorf "ppx_deriving_tupleable: cannot find definition for abstract type"
  | Some ty ->
    let (data_pat, tup_pat, data_exp, tup_exp) = core_type_to_case ty "tmp" in
    ((lam data_pat tup_exp),
     (lam tup_pat data_exp))

(* Produces a tuple of the "to" function and the "of" function
  The rhs_typ_kind contains either the variants or the record fields
  for an Algebraic Data Type (ADT), such as:
    - `type foo = A of int | B of bool`
      the rhs_typ_kind is Ptype_variant with constructor declarations
      `A of int` and `B of bool`
    - `type foo = { s : string; v : int }`
      the rhs_typ_kind is Ptype_record with fields `s : string` and
      `v : int`
  The manifest is the thing on the right hand side of the `=` sign
   for a type alias such as:
     - `type foo = int`
       the manifest is Some with `int` *)
let type_decl_rhs_to_funs rhs_typ_kind manifest =
  match rhs_typ_kind with
  | Ptype_abstract    -> type_decl_manifest_to_funs manifest
  | Ptype_variant vs  -> type_decl_variants_to_funs vs
  | Ptype_record flds -> type_decl_record_to_funs flds
  | Ptype_open        -> raise_errorf "ppx_deriving_tupleable: open types are not yet supported"

(* returns a tuple of three values:
    * pre : listof structure_item
    * vals : listof value_binding
    * post : listof structure_item
  *)
let tupleable_str_of_type ~options ~path type_decl =
  ignore options;
  ignore path;
  let name = tua_op_map (fun s -> mangle_type_decl_suffix s type_decl) tua_op_names in
  let (to_fun, of_fun) = type_decl_rhs_to_funs type_decl.ptype_kind type_decl.ptype_manifest in
  let tua_op_exps = {
    to_tuple = to_fun;
    of_tuple = of_fun;
  }
  in

  let make_op_binding name exp =
    Vb.mk (pvar name) exp
  in
  let val_bindings = tua_op_map2 make_op_binding name tua_op_exps
  in
  ([], (tua_ops_to_list val_bindings), [])

(* --------------------------------- *)

let core_type_as_tuple ty = ty

let type_decl_manifest_as_tuple manifest =
  match manifest with
  | None    -> raise_errorf "ppx_deriving_tupleable: cannot find definition for abstract type"
  | Some ty -> core_type_as_tuple ty

let record_fields_as_tuple (flds : label_declaration list) =
  let tys = List.map (fun fld -> fld.pld_type) flds in
  match ctor_tup_args Typ.tuple tys with
  | Some t -> t
  | None -> tconstr "unit" []

let constructor_arguments_as_tuple pcd_args =
  match pcd_args with
  | Pcstr_tuple tys ->
    (match ctor_tup_args Typ.tuple tys with
     | Some t -> t
     | None -> tconstr "unit" [])
  | Pcstr_record flds ->
    record_fields_as_tuple flds

let type_decl_variant_as_tuple { pcd_name; pcd_args; pcd_res; pcd_loc; pcd_attributes } =
  ignore pcd_name; ignore pcd_loc; ignore pcd_attributes;
  (* pcd_res is used for GADTs, but we don't support those yet, so if its there, raise an error *)
  (match pcd_res with | None -> () | _ -> raise_errorf "ppx_deriving_tupleable: GADTs are not yet supported");
  constructor_arguments_as_tuple pcd_args

let type_decl_variants_as_tuple (variants : constructor_declaration list) =
  match variants with
  | [variant] -> type_decl_variant_as_tuple variant
  | _         -> raise_errorf "ppx_deriving_tupleable: multiple-variant ADTs are not yet supported"

let type_decl_record_as_tuple record =
  record_fields_as_tuple record

(* Produces a tuple type that it will be converted to.
  The rhs_typ_kind contains either the variants or the record fields
  for an Algebraic Data Type (ADT), such as:
    - `type foo = A of int | B of bool`
      the rhs_typ_kind is Ptype_variant with constructor declarations
      `A of int` and `B of bool`
    - `type foo = { s : string; v : int }`
      the rhs_typ_kind is Ptype_record with fields `s : string` and
      `v : int`
  The manifest is the thing on the right hand side of the `=` sign
   for a type alias such as:
     - `type foo = int`
       the manifest is Some with `int` *)
let type_decl_rhs_as_tuple rhs_typ_kind manifest =
  match rhs_typ_kind with
  | Ptype_abstract    -> type_decl_manifest_as_tuple manifest
  | Ptype_variant vs  -> type_decl_variants_as_tuple vs
  | Ptype_record flds -> type_decl_record_as_tuple flds
  | Ptype_open        -> raise_errorf "ppx_deriving_tupleable: open types are not yet supported"

let tupleable_sig_of_type ~options ~path type_decl =
  ignore options;
  ignore path;
  let name = tua_op_map (fun s -> mangle_type_decl_suffix s type_decl) tua_op_names
  in

  let param_types = List.map (fun (t,_) -> t) type_decl.ptype_params in
  let type_defined = Typ.constr (str_to_lid type_decl.ptype_name) param_types
  and tuple_type = type_decl_rhs_as_tuple type_decl.ptype_kind type_decl.ptype_manifest in
  let op_type = tua_op_types type_defined tuple_type
  in

  let make_op_decl name op_type =
    Sig.value (Val.mk (mknoloc name) op_type)
  in
  let op_decls = tua_op_map2 make_op_decl name op_type
  in

  (tua_ops_to_list op_decls)

(* --------------------------------- *)

let () =
  Ppx_deriving.register
    (Ppx_deriving.create
      deriver
      (* ~core_type:tupleable_expr_of_typ *)
      ~type_decl_str:(structure (on_str_decls tupleable_str_of_type))
      (* ~type_ext_str:tupleable_str_of_type_ext *)
      ~type_decl_sig:(on_sig_decls tupleable_sig_of_type)
      (* ~type_ext_sig:tupleable_sig_of_type_ext *)
      ())

