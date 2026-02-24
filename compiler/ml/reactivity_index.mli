type value_summary = {
  is_scope_creator : bool;
  is_primitive_creator : bool;
  is_accessor : bool;
  is_proxy : bool;
  is_setter : bool;
  reads_reactive : bool;
  escapes_reactive : bool;
  escape_ok : bool;
}

val empty_value_summary : value_summary

val merge_value_summary : value_summary -> value_summary -> value_summary

val has_reactivity : value_summary -> bool

val index_dir_from_outputprefix : string -> string option

val index_dir_from_sourcefile : string -> string option

val index_dir_from_package_root : string -> string

val write_module_summary_in_index_dir :
  index_dir:string ->
  module_name:string ->
  values:(string * value_summary) list ->
  stamps:(int * value_summary) list ->
  unit

val write_module_summary :
  outputprefix:string ->
  module_name:string ->
  values:(string * value_summary) list ->
  stamps:(int * value_summary) list ->
  unit

val read_module_summary :
  index_dir:string -> module_name:string -> (string * value_summary) list option

val read_value_summary :
  index_dir:string -> module_name:string -> value_name:string -> value_summary option

val read_stamp_summary :
  index_dir:string -> module_name:string -> stamp:int -> value_summary option

val module_and_value_of_path : Path.t -> (string * string) option

val read_value_summary_for_path :
  index_dir:string -> path:Path.t -> value_summary option
