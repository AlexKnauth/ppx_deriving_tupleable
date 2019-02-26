# ppx_deriving_tupleable

Converting OCaml record types to tuples and back.

Example:
```ocaml
type full_name = { first_name: string; middle_name: string; last_name: string }
[@@deriving tupleable]
```

Generates:
 - `full_name_to_tuple` : `full_name -> (string * string * string)`
 - `full_name_of_tuple` : `(string * string * string) -> full_name`
