type value_summary = {
  is_scope_creator : bool;
  is_primitive_creator : bool;
  is_accessor : bool;
  is_proxy : bool;
}

let empty_value_summary =
  {
    is_scope_creator = false;
    is_primitive_creator = false;
    is_accessor = false;
    is_proxy = false;
  }

let merge_value_summary left right =
  {
    is_scope_creator = left.is_scope_creator || right.is_scope_creator;
    is_primitive_creator =
      left.is_primitive_creator || right.is_primitive_creator;
    is_accessor = left.is_accessor || right.is_accessor;
    is_proxy = left.is_proxy || right.is_proxy;
  }

let has_reactivity summary =
  summary.is_scope_creator || summary.is_primitive_creator || summary.is_accessor
  || summary.is_proxy

type serialized_module_summary = {
  format_version : int;
  values : (string * value_summary) list;
}

let serialized_format_version = 1

let is_safe_filename_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '-' | '.' -> true
  | _ -> false

let safe_module_component module_name =
  let bytes = Bytes.of_string module_name in
  for index = 0 to Bytes.length bytes - 1 do
    let char = Bytes.get bytes index in
    if not (is_safe_filename_char char) then Bytes.set bytes index '_'
  done;
  Bytes.unsafe_to_string bytes

let summary_filename module_name =
  safe_module_component module_name ^ ".reactivity"

let summary_path ~index_dir ~module_name =
  Filename.concat index_dir (summary_filename module_name)

let rec ensure_directory path =
  if path = "" || path = "." || path = Filename.dir_sep then ()
  else if Sys.file_exists path then ()
  else
    let parent = Filename.dirname path in
    if parent <> path then ensure_directory parent;
    try Unix.mkdir path 0o755
    with Unix.Unix_error (Unix.EEXIST, _, _) -> ()

let write_marshaled_file ~path value =
  let tmp_path = path ^ ".tmp-" ^ string_of_int (Unix.getpid ()) in
  try
    Ext_pervasives.finally (open_out_bin tmp_path) ~clean:close_out
      (fun channel ->
        Marshal.to_channel channel value [];
        flush channel);
    Sys.rename tmp_path path
  with error ->
    (try Sys.remove tmp_path with _ -> ());
    raise error

let read_marshaled_file ~path =
  Ext_pervasives.finally (open_in_bin path) ~clean:close_in (fun channel ->
      Marshal.from_channel channel)

let rec find_bs_root directory =
  let parent = Filename.dirname directory in
  if parent = directory then None
  else
    let base = Filename.basename directory in
    let parent_base = Filename.basename parent in
    if base = "bs" && parent_base = "lib" then Some directory
    else find_bs_root parent

let index_dir_from_outputprefix outputprefix =
  let containing_directory = Filename.dirname outputprefix in
  match find_bs_root containing_directory with
  | None -> None
  | Some bs_root -> Some (Filename.concat bs_root ".reactivity-index")

let rec find_package_root directory =
  let candidate = Filename.concat directory "rescript.json" in
  if Sys.file_exists candidate then Some directory
  else
    let parent = Filename.dirname directory in
    if parent = directory then None else find_package_root parent

let index_dir_from_sourcefile sourcefile =
  let containing_directory = Filename.dirname sourcefile in
  match find_package_root containing_directory with
  | None -> None
  | Some package_root ->
    Some (Filename.concat package_root "lib/bs/.reactivity-index")

let index_dir_from_package_root root =
  Filename.concat root "lib/bs/.reactivity-index"

let write_module_summary_in_index_dir ~index_dir ~module_name ~values =
  try
    ensure_directory index_dir;
    write_marshaled_file
      ~path:(summary_path ~index_dir ~module_name)
      {format_version = serialized_format_version; values}
  with _ -> ()

let write_module_summary ~outputprefix ~module_name ~values =
  match index_dir_from_outputprefix outputprefix with
  | None -> ()
  | Some index_dir ->
    write_module_summary_in_index_dir ~index_dir ~module_name ~values

let read_module_summary ~index_dir ~module_name =
  let path = summary_path ~index_dir ~module_name in
  if not (Sys.file_exists path) then None
  else
    try
      let payload : serialized_module_summary = read_marshaled_file ~path in
      if payload.format_version <> serialized_format_version then None
      else Some payload.values
    with _ -> None

let read_value_summary ~index_dir ~module_name ~value_name =
  match read_module_summary ~index_dir ~module_name with
  | None -> None
  | Some values -> (
    match List.find_opt (fun (name, _) -> name = value_name) values with
    | None -> None
    | Some (_, summary) -> Some summary)

let module_and_value_of_path (path : Path.t) =
  match Path.flatten path with
  | `Contains_apply -> None
  | `Ok (head_ident, segments) -> (
    match List.rev segments with
    | [] -> None
    | value_name :: rev_module_segments ->
      let module_segments = Ident.name head_ident :: List.rev rev_module_segments in
      match module_segments with
      | [module_name] -> Some (module_name, value_name)
      | _ -> None)

let read_value_summary_for_path ~index_dir ~path =
  match module_and_value_of_path path with
  | None -> None
  | Some (module_name, value_name) ->
    read_value_summary ~index_dir ~module_name ~value_name
