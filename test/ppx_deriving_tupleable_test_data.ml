
type full_name = { first_name: string; middle_name: string; last_name: string }
[@@deriving tupleable]

type 'a located = { location: string; value: 'a }
[@@deriving tupleable]
