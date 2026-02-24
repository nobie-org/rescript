open Typedtree

module IntSet = Set.Make (struct
  type t = int

  let compare = compare
end)

module StringSet = Set.Make (String)

type bound_ident = {
  stamp : int;
  name : string;
  loc : Location.t;
}

type callee_kind = {
  is_scope_creator : bool;
  is_primitive_creator : bool;
  is_accessor : bool;
  is_proxy : bool;
  is_setter : bool;
  reads_reactive : bool;
  escapes_reactive : bool;
  escape_ok : bool;
  primitive_name : string option;
}

let empty_callee_kind =
  {
    is_scope_creator = false;
    is_primitive_creator = false;
    is_accessor = false;
    is_proxy = false;
    is_setter = false;
    reads_reactive = false;
    escapes_reactive = false;
    escape_ok = false;
    primitive_name = None;
  }

let scope_attribute_names =
  [ "reactive.scope"; "reactiveScope"; "nobie.reactive.scope" ]

let primitive_attribute_names =
  [ "reactive.primitive"; "reactivePrimitive"; "nobie.reactive.primitive" ]

let accessor_attribute_names =
  [ "reactive.accessor"; "reactiveAccessor"; "nobie.reactive.accessor" ]

let proxy_attribute_names =
  [ "reactive.proxy"; "reactiveProxy"; "nobie.reactive.proxy" ]

let setter_attribute_names =
  [ "reactive.setter"; "reactiveSetter"; "nobie.reactive.setter" ]

let reads_attribute_names =
  [ "reactive.reads"; "reactiveReads"; "nobie.reactive.reads" ]

let escape_ok_attribute_names =
  [ "reactive.escapeOk"; "reactiveEscapeOk"; "nobie.reactive.escapeOk" ]

let scope_primitive_names =
  StringSet.of_list
    [ "createEffect"; "createComputed"; "createRenderEffect"; "createMemo" ]

let primitive_creator_names =
  StringSet.of_list
    [
      "createSignal";
      "createStore";
      "createResource";
      "createMemo";
      "createSelector";
      "createDeferred";
      "createReaction";
    ]

let is_one_of names value = List.exists (fun candidate -> candidate = value) names

let has_any_attribute attributes names =
  List.exists
    (fun (attribute : Parsetree.attribute) ->
      let name_loc, _payload = attribute in
      is_one_of names name_loc.txt)
    attributes

let value_binding_has_any_attribute (value_binding : value_binding) names =
  has_any_attribute value_binding.vb_attributes names

let primitive_name_of_value_description (description : Types.value_description)
    =
  match description.val_kind with
  | Types.Val_prim primitive -> Some primitive.Primitive.prim_name
  | Types.Val_reg -> None

let normalize_ident_name name =
  if name = "" then ""
  else
    try
      let slash_index = String.index name '/' in
      if slash_index <= 0 then name else String.sub name 0 slash_index
    with Not_found -> name

let path_last_name path =
  let name = Path.last path |> normalize_ident_name in
  if name = "" then None else Some name

let callee_kind_of_value_description (description : Types.value_description) =
  let primitive_name = primitive_name_of_value_description description in
  let by_accessor_attribute =
    has_any_attribute description.val_attributes accessor_attribute_names
  in
  let by_proxy_attribute =
    has_any_attribute description.val_attributes proxy_attribute_names
  in
  let by_setter_attribute =
    has_any_attribute description.val_attributes setter_attribute_names
  in
  let by_reads_attribute =
    has_any_attribute description.val_attributes reads_attribute_names
  in
  let by_escape_ok_attribute =
    has_any_attribute description.val_attributes escape_ok_attribute_names
  in
  let by_scope_attribute =
    has_any_attribute description.val_attributes scope_attribute_names
  in
  let by_primitive_attribute =
    has_any_attribute description.val_attributes primitive_attribute_names
  in
  let by_scope_primitive_name =
    match primitive_name with
    | Some name -> StringSet.mem name scope_primitive_names
    | None -> false
  in
  let by_creator_primitive_name =
    match primitive_name with
    | Some name -> StringSet.mem name primitive_creator_names
    | None -> false
  in
  {
    is_scope_creator = by_scope_attribute || by_scope_primitive_name;
    is_primitive_creator = by_primitive_attribute || by_creator_primitive_name;
    is_accessor = by_accessor_attribute;
    is_proxy = by_proxy_attribute;
    is_setter = by_setter_attribute;
    reads_reactive = by_reads_attribute;
    escapes_reactive = false;
    escape_ok = by_escape_ok_attribute;
    primitive_name;
  }

let callee_kind_of_ident ~path ~value_description =
  let by_value_description = callee_kind_of_value_description value_description in
  let path_name = path_last_name path in
  let by_scope_name =
    match path_name with
    | Some name -> StringSet.mem name scope_primitive_names
    | None -> false
  in
  let by_primitive_name =
    match path_name with
    | Some name -> StringSet.mem name primitive_creator_names
    | None -> false
  in
  {
    is_scope_creator = by_value_description.is_scope_creator || by_scope_name;
    is_primitive_creator =
      by_value_description.is_primitive_creator || by_primitive_name;
    is_accessor = by_value_description.is_accessor;
    is_proxy = by_value_description.is_proxy;
    is_setter = by_value_description.is_setter;
    reads_reactive = by_value_description.reads_reactive;
    escapes_reactive = by_value_description.escapes_reactive;
    escape_ok = by_value_description.escape_ok;
    primitive_name =
      (match by_value_description.primitive_name with
      | Some _ as name -> name
      | None -> path_name);
  }

let callee_kind_of_reactivity_summary (summary : Reactivity_index.value_summary) =
  {
    is_scope_creator = summary.is_scope_creator;
    is_primitive_creator = summary.is_primitive_creator;
    is_accessor = summary.is_accessor;
    is_proxy = summary.is_proxy;
    is_setter = summary.is_setter;
    reads_reactive = summary.reads_reactive;
    escapes_reactive = summary.escapes_reactive;
    escape_ok = summary.escape_ok;
    primitive_name = None;
  }

let merge_callee_kind left right =
  {
    is_scope_creator = left.is_scope_creator || right.is_scope_creator;
    is_primitive_creator =
      left.is_primitive_creator || right.is_primitive_creator;
    is_accessor = left.is_accessor || right.is_accessor;
    is_proxy = left.is_proxy || right.is_proxy;
    is_setter = left.is_setter || right.is_setter;
    reads_reactive = left.reads_reactive || right.reads_reactive;
    escapes_reactive = left.escapes_reactive || right.escapes_reactive;
    escape_ok = left.escape_ok || right.escape_ok;
    primitive_name =
      (match left.primitive_name with
      | Some _ as name -> name
      | None -> right.primitive_name);
  }

let string_of_callee_name ~fallback_name = function
  | Some name when name <> "" -> name
  | _ -> fallback_name

let stamp_of_ident ident = Ident.binding_time ident

let rec collect_value_pattern_bound_idents (pattern : pattern) =
  match pattern.pat_desc with
  | Tpat_var (ident, name_loc) ->
    [ {stamp = stamp_of_ident ident; name = name_loc.txt; loc = pattern.pat_loc} ]
  | Tpat_alias (_, ident, name_loc) ->
    [ {stamp = stamp_of_ident ident; name = name_loc.txt; loc = pattern.pat_loc} ]
  | Tpat_tuple patterns | Tpat_array patterns ->
    Ext_list.flat_map patterns collect_value_pattern_bound_idents
  | Tpat_record (rows, _) ->
    rows
    |> List.map (fun (_, _, nested_pattern, _) ->
           collect_value_pattern_bound_idents nested_pattern)
    |> List.concat
  | Tpat_construct (_, _, patterns) ->
    Ext_list.flat_map patterns collect_value_pattern_bound_idents
  | Tpat_variant (_, Some nested_pattern, _) ->
    collect_value_pattern_bound_idents nested_pattern
  | Tpat_or (left, right, _) ->
    collect_value_pattern_bound_idents left
    @ collect_value_pattern_bound_idents right
  | Tpat_any | Tpat_constant _ | Tpat_variant (_, None, _) -> []

let single_bound_ident_of_pattern pattern =
  match collect_value_pattern_bound_idents pattern with
  | [ bound_ident ] -> Some bound_ident
  | _ -> None

let rec first_two_tuple_patterns pattern =
  match pattern.pat_desc with
  | Tpat_tuple (first :: second :: _) -> Some (first, second)
  | Tpat_alias (nested_pattern, _, _) -> first_two_tuple_patterns nested_pattern
  | _ -> None

let rec pattern_is_simple_binding pattern =
  match pattern.pat_desc with
  | Tpat_var _ -> true
  | Tpat_alias (nested_pattern, _, _) ->
    pattern_is_simple_binding nested_pattern
  | Tpat_any
  | Tpat_constant _
  | Tpat_tuple _
  | Tpat_record _
  | Tpat_construct _
  | Tpat_variant _
  | Tpat_array _
  | Tpat_or _ -> false

let rec pattern_is_destructuring pattern =
  match pattern.pat_desc with
  | Tpat_tuple _ | Tpat_record _ | Tpat_construct _ | Tpat_array _ | Tpat_or _
    ->
    true
  | Tpat_variant (_, Some _, _) -> true
  | Tpat_alias (nested_pattern, _, _) ->
    pattern_is_destructuring nested_pattern
  | Tpat_any | Tpat_var _ | Tpat_constant _ | Tpat_variant (_, None, _) -> false

let function_body_expressions_of_expression expression =
  match expression.exp_desc with
  | Texp_function {case; _} -> [ case.c_rhs ]
  | _ -> []

let expression_is_function expression =
  match expression.exp_desc with
  | Texp_function _ -> true
  | _ -> false

let callee_kind_of_expression_identifier expression =
  match expression.exp_desc with
  | Texp_ident (path, _, value_description) ->
    callee_kind_of_ident ~path ~value_description
  | _ -> empty_callee_kind

let call_expression_kind expression =
  match expression.exp_desc with
  | Texp_apply {funct = callee; _} ->
    callee_kind_of_expression_identifier callee
  | _ -> empty_callee_kind

let expression_contains_target_call ~target_stamps ~target_predicate
    ~callee_kind_for_path expression =
  let found = ref false in
  let iterator =
    {
      Tast_iterator.default_iterator with
      expr =
        (fun self current_expression ->
          if !found then ()
          else
            (match current_expression.exp_desc with
            | Texp_apply {funct = callee; _} -> (
              match callee.exp_desc with
              | Texp_ident (path, _, value_description) ->
                let by_stamp =
                  match path with
                  | Path.Pident ident ->
                    IntSet.mem (stamp_of_ident ident) target_stamps
                  | _ -> false
                in
                if by_stamp then found := true
                else
                  let kind =
                    callee_kind_for_path ~path ~value_description
                  in
                  if target_predicate kind then found := true
                  else Tast_iterator.default_iterator.expr self current_expression
              | _ -> Tast_iterator.default_iterator.expr self current_expression)
            | _ -> Tast_iterator.default_iterator.expr self current_expression));
    }
  in
  iterator.expr iterator expression;
  !found

let collect_value_bindings structure =
  let value_bindings = ref [] in
  let iterator =
    {
      Tast_iterator.default_iterator with
      value_binding =
        (fun self value_binding ->
          value_bindings := value_binding :: !value_bindings;
          Tast_iterator.default_iterator.value_binding self value_binding);
    }
  in
  iterator.structure iterator structure;
  List.rev !value_bindings

let compute_callable_sets ~callee_kind_for_path value_bindings =
  let scope_callable_stamps = ref IntSet.empty in
  let primitive_callable_stamps = ref IntSet.empty in
  let changed = ref true in

  let add_to_set set_reference stamp =
    if IntSet.mem stamp !set_reference then false
    else (
      set_reference := IntSet.add stamp !set_reference;
      true)
  in

  while !changed do
    changed := false;
    List.iter
      (fun (value_binding : value_binding) ->
        match single_bound_ident_of_pattern value_binding.vb_pat with
        | None -> ()
        | Some bound_ident ->
          let maybe_add_scope should_add =
            if should_add then changed := add_to_set scope_callable_stamps bound_ident.stamp || !changed
          in
          let maybe_add_primitive should_add =
            if should_add then
              changed :=
                add_to_set primitive_callable_stamps bound_ident.stamp || !changed
          in

          maybe_add_scope
            (value_binding_has_any_attribute value_binding
               scope_attribute_names);
          maybe_add_primitive
            (value_binding_has_any_attribute value_binding
               primitive_attribute_names);

          (match value_binding.vb_expr.exp_desc with
          | Texp_ident (Path.Pident source_ident, _, value_description) ->
            let source_stamp = stamp_of_ident source_ident in
            maybe_add_scope (IntSet.mem source_stamp !scope_callable_stamps);
            maybe_add_primitive
              (IntSet.mem source_stamp !primitive_callable_stamps);
            let direct_kind =
              callee_kind_for_path
                ~path:(Path.Pident source_ident)
                ~value_description
            in
            maybe_add_scope direct_kind.is_scope_creator;
            maybe_add_primitive direct_kind.is_primitive_creator
          | Texp_ident (path, _, value_description) ->
            let direct_kind = callee_kind_for_path ~path ~value_description in
            maybe_add_scope direct_kind.is_scope_creator;
            maybe_add_primitive direct_kind.is_primitive_creator
          | _ -> ());

          let function_bodies =
            function_body_expressions_of_expression value_binding.vb_expr
          in
          if function_bodies <> [] then (
            let body_mentions_scope =
              List.exists
                (expression_contains_target_call
                   ~target_stamps:!scope_callable_stamps
                   ~target_predicate:(fun kind -> kind.is_scope_creator)
                   ~callee_kind_for_path)
                function_bodies
            in
            let body_mentions_primitive =
              List.exists
                (expression_contains_target_call
                   ~target_stamps:!primitive_callable_stamps
                   ~target_predicate:(fun kind -> kind.is_primitive_creator)
                   ~callee_kind_for_path)
                function_bodies
            in
            maybe_add_scope body_mentions_scope;
            maybe_add_primitive body_mentions_primitive))
      value_bindings
  done;

  (!scope_callable_stamps, !primitive_callable_stamps)

let add_stamp_if_absent set_reference stamp =
  if IntSet.mem stamp !set_reference then false
  else (
    set_reference := IntSet.add stamp !set_reference;
    true)

let collect_attribute_bound_stamps value_bindings attribute_names =
  List.fold_left
    (fun acc (value_binding : value_binding) ->
      if value_binding_has_any_attribute value_binding attribute_names then
        List.fold_left
          (fun nested_acc (bound_ident : bound_ident) ->
            IntSet.add bound_ident.stamp nested_acc)
          acc
          (collect_value_pattern_bound_idents value_binding.vb_pat)
      else acc)
    IntSet.empty value_bindings

let collect_carrier_sets ~lookup_reactivity_summary_for_path value_bindings =
  let accessor_stamps =
    ref (collect_attribute_bound_stamps value_bindings accessor_attribute_names)
  in
  let proxy_stamps =
    ref (collect_attribute_bound_stamps value_bindings proxy_attribute_names)
  in
  let setter_stamps =
    ref (collect_attribute_bound_stamps value_bindings setter_attribute_names)
  in

  let add_accessor bound_ident =
    accessor_stamps := IntSet.add bound_ident.stamp !accessor_stamps
  in
  let add_proxy bound_ident = proxy_stamps := IntSet.add bound_ident.stamp !proxy_stamps in
  let add_setter bound_ident =
    setter_stamps := IntSet.add bound_ident.stamp !setter_stamps
  in

  List.iter
    (fun (value_binding : value_binding) ->
      let call_kind = call_expression_kind value_binding.vb_expr in
      match call_kind.primitive_name with
      | Some "createSignal" | Some "createResource" -> (
        match first_two_tuple_patterns value_binding.vb_pat with
        | Some (first_pattern, second_pattern) ->
          (match single_bound_ident_of_pattern first_pattern with
          | Some accessor_bound_ident -> add_accessor accessor_bound_ident
          | None -> ());
          (match single_bound_ident_of_pattern second_pattern with
          | Some setter_bound_ident -> add_setter setter_bound_ident
          | None -> ())
        | None -> ())
      | Some "createStore" -> (
        match first_two_tuple_patterns value_binding.vb_pat with
        | Some (first_pattern, second_pattern) ->
          (match single_bound_ident_of_pattern first_pattern with
          | Some proxy_bound_ident -> add_proxy proxy_bound_ident
          | None -> ());
          (match single_bound_ident_of_pattern second_pattern with
          | Some setter_bound_ident -> add_setter setter_bound_ident
          | None -> ())
        | None -> ())
      | Some "createMemo" | Some "createSelector" | Some "createDeferred" -> (
        match single_bound_ident_of_pattern value_binding.vb_pat with
        | Some accessor_bound_ident -> add_accessor accessor_bound_ident
        | None -> ())
      | _ -> ())
    value_bindings;

  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun (value_binding : value_binding) ->
        match single_bound_ident_of_pattern value_binding.vb_pat with
        | None -> ()
        | Some bound_ident -> (
          let add_accessor_if condition =
            if condition then
              changed :=
                add_stamp_if_absent accessor_stamps bound_ident.stamp || !changed
          in
          let add_proxy_if condition =
            if condition then
              changed := add_stamp_if_absent proxy_stamps bound_ident.stamp || !changed
          in
          let add_setter_if condition =
            if condition then
              changed :=
                add_stamp_if_absent setter_stamps bound_ident.stamp || !changed
          in

          match value_binding.vb_expr.exp_desc with
          | Texp_ident (path, _, _) ->
            let source_stamp =
              match path with
              | Path.Pident source_ident -> Some (stamp_of_ident source_ident)
              | _ -> None
            in
            let summary =
              lookup_reactivity_summary_for_path path
            in
            add_accessor_if
              ((match source_stamp with
              | Some stamp -> IntSet.mem stamp !accessor_stamps
              | None -> false)
              ||
              match summary with
              | Some value_summary -> value_summary.Reactivity_index.is_accessor
              | None -> false);
            add_proxy_if
              ((match source_stamp with
              | Some stamp -> IntSet.mem stamp !proxy_stamps
              | None -> false)
              ||
              match summary with
              | Some value_summary -> value_summary.Reactivity_index.is_proxy
              | None -> false);
            add_setter_if
              ((match source_stamp with
              | Some stamp -> IntSet.mem stamp !setter_stamps
              | None -> false)
              ||
              match summary with
              | Some value_summary -> value_summary.Reactivity_index.is_setter
              | None -> false)
          | _ -> ()))
      value_bindings
  done;

  (!accessor_stamps, !proxy_stamps, !setter_stamps)

let expression_contains_reactive_read_call ~reads_reactive_stamps
    ~accessor_stamps ~proxy_stamps ~callee_kind_for_path expression =
  expression_contains_target_call ~target_stamps:reads_reactive_stamps
    ~target_predicate:(fun kind ->
      kind.reads_reactive || kind.is_accessor || kind.is_proxy)
    ~callee_kind_for_path expression
  ||
  expression_contains_target_call ~target_stamps:accessor_stamps
    ~target_predicate:(fun kind -> kind.is_accessor)
    ~callee_kind_for_path expression
  ||
  expression_contains_target_call ~target_stamps:proxy_stamps
    ~target_predicate:(fun kind -> kind.is_proxy)
    ~callee_kind_for_path expression

let compute_reads_reactive_set ~callee_kind_for_path
    ~lookup_reactivity_summary_for_path ~accessor_stamps ~proxy_stamps
    value_bindings =
  let reads_reactive_stamps =
    ref (collect_attribute_bound_stamps value_bindings reads_attribute_names)
  in
  let changed = ref true in

  while !changed do
    changed := false;
    List.iter
      (fun (value_binding : value_binding) ->
        match single_bound_ident_of_pattern value_binding.vb_pat with
        | None -> ()
        | Some bound_ident ->
          let maybe_add_reads should_add =
            if should_add then
              changed :=
                add_stamp_if_absent reads_reactive_stamps bound_ident.stamp
                || !changed
          in

          (match value_binding.vb_expr.exp_desc with
          | Texp_ident (path, _, _) ->
            let source_stamp =
              match path with
              | Path.Pident source_ident -> Some (stamp_of_ident source_ident)
              | _ -> None
            in
            maybe_add_reads
              ((match source_stamp with
              | Some stamp -> IntSet.mem stamp !reads_reactive_stamps
              | None -> false)
              ||
              match lookup_reactivity_summary_for_path path with
              | Some summary -> summary.Reactivity_index.reads_reactive
              | None -> false)
          | _ -> ());

          maybe_add_reads
            (expression_contains_reactive_read_call
               ~reads_reactive_stamps:!reads_reactive_stamps ~accessor_stamps
               ~proxy_stamps ~callee_kind_for_path value_binding.vb_expr))
      value_bindings
  done;

  !reads_reactive_stamps

let expression_contains_reactive_value ~accessor_stamps ~proxy_stamps
    ~setter_stamps ~lookup_reactivity_summary_for_path expression =
  let found = ref false in
  let iterator =
    {
      Tast_iterator.default_iterator with
      expr =
        (fun self current_expression ->
          if !found then ()
          else
            match current_expression.exp_desc with
            | Texp_ident (path, _, _) ->
              let source_stamp =
                match path with
                | Path.Pident source_ident -> Some (stamp_of_ident source_ident)
                | _ -> None
              in
              let summary =
                lookup_reactivity_summary_for_path path
              in
              if
                (match source_stamp with
                | Some stamp ->
                  IntSet.mem stamp accessor_stamps
                  || IntSet.mem stamp proxy_stamps
                  || IntSet.mem stamp setter_stamps
                | None -> false)
                ||
                match summary with
                | Some value_summary ->
                  value_summary.Reactivity_index.is_accessor
                  || value_summary.Reactivity_index.is_proxy
                  || value_summary.Reactivity_index.is_setter
                | None -> false
              then found := true
              else Tast_iterator.default_iterator.expr self current_expression
            | Texp_apply {args; _} ->
              List.iter
                (fun (_, argument_expression_opt) ->
                  Option.iter (self.expr self) argument_expression_opt)
                args
            | _ -> Tast_iterator.default_iterator.expr self current_expression);
    }
  in
  iterator.expr iterator expression;
  !found

let callee_is_known_reactive (kind : callee_kind) =
  kind.is_scope_creator || kind.is_primitive_creator || kind.is_accessor
  || kind.is_proxy || kind.is_setter || kind.reads_reactive || kind.escape_ok

let expression_contains_reactive_escape_call ~escape_stamps
    ~accessor_stamps ~proxy_stamps ~setter_stamps
    ~callee_kind_for_path ~lookup_reactivity_summary_for_path expression =
  let found = ref false in
  let iterator =
    {
      Tast_iterator.default_iterator with
      expr =
        (fun self current_expression ->
          if !found then ()
          else
            match current_expression.exp_desc with
            | Texp_apply {funct = callee; args; _} -> (
              match callee.exp_desc with
              | Texp_ident (path, _, value_description) ->
                let callee_stamp =
                  match path with
                  | Path.Pident ident -> Some (stamp_of_ident ident)
                  | _ -> None
                in
                if
                  match callee_stamp with
                  | Some stamp -> IntSet.mem stamp escape_stamps
                  | None -> false
                then found := true
                else
                  let callee_kind =
                    callee_kind_for_path ~path ~value_description
                  in
                  if not (callee_is_known_reactive callee_kind) then
                    let has_reactive_arg =
                      List.exists
                        (fun (_, argument_expression_opt) ->
                          match argument_expression_opt with
                          | None -> false
                          | Some argument_expression ->
                            expression_contains_reactive_value
                              ~accessor_stamps ~proxy_stamps ~setter_stamps
                              ~lookup_reactivity_summary_for_path
                              argument_expression)
                        args
                    in
                    if has_reactive_arg then found := true
                    else Tast_iterator.default_iterator.expr self current_expression
                  else Tast_iterator.default_iterator.expr self current_expression
              | _ -> Tast_iterator.default_iterator.expr self current_expression)
            | _ -> Tast_iterator.default_iterator.expr self current_expression);
    }
  in
  iterator.expr iterator expression;
  !found

let compute_escape_set ~callee_kind_for_path ~lookup_reactivity_summary_for_path
    ~accessor_stamps ~proxy_stamps ~setter_stamps value_bindings =
  let escape_stamps = ref IntSet.empty in
  let changed = ref true in

  while !changed do
    changed := false;
    List.iter
      (fun (value_binding : value_binding) ->
        match single_bound_ident_of_pattern value_binding.vb_pat with
        | None -> ()
        | Some bound_ident ->
          let maybe_add_escape should_add =
            if should_add then
              changed := add_stamp_if_absent escape_stamps bound_ident.stamp || !changed
          in

          (match value_binding.vb_expr.exp_desc with
          | Texp_ident (path, _, _) ->
            let source_stamp =
              match path with
              | Path.Pident source_ident -> Some (stamp_of_ident source_ident)
              | _ -> None
            in
            maybe_add_escape
              ((match source_stamp with
              | Some stamp -> IntSet.mem stamp !escape_stamps
              | None -> false)
              ||
              match lookup_reactivity_summary_for_path path with
              | Some summary -> summary.Reactivity_index.escapes_reactive
              | None -> false)
          | _ -> ());

          maybe_add_escape
            (expression_contains_reactive_escape_call
               ~escape_stamps:!escape_stamps
               ~accessor_stamps ~proxy_stamps ~setter_stamps
               ~callee_kind_for_path ~lookup_reactivity_summary_for_path
               value_binding.vb_expr))
      value_bindings
  done;

  !escape_stamps

let emit_warning location warning =
  if not location.Location.loc_ghost then Location.prerr_warning location warning

let first_non_simple_pattern_name pattern =
  match pattern.pat_desc with
  | Tpat_var (_, name_loc) -> Some name_loc.txt
  | Tpat_alias (_, _, name_loc) -> Some name_loc.txt
  | _ -> None

let collect_top_level_bound_idents structure =
  let add_binding_bound_idents acc (value_binding : value_binding) =
    collect_value_pattern_bound_idents value_binding.vb_pat @ acc
  in
  structure.str_items
  |> List.fold_left
       (fun acc structure_item ->
         match structure_item.str_desc with
         | Tstr_value (_, value_bindings) ->
           List.fold_left add_binding_bound_idents acc value_bindings
         | _ -> acc)
       []
  |> List.rev

let collect_all_bound_idents value_bindings =
  value_bindings
  |> List.fold_left
       (fun acc (value_binding : value_binding) ->
         collect_value_pattern_bound_idents value_binding.vb_pat @ acc)
       []
  |> List.rev

let unsafe_cast_name_of_path (path : Path.t) =
  match Path.flatten path with
  | `Contains_apply -> None
  | `Ok (head_ident, segments) -> (
    match Ident.name head_ident :: segments with
    | [ "Obj"; "magic" ] -> Some "Obj.magic"
    | [ "Js"; "Unsafe"; "coerce" ] -> Some "Js.Unsafe.coerce"
    | _ -> None)

let emit_warnings ~outputprefix structure =
  let module_name = Env.get_unit_name () in
  let reactivity_index_dir =
    match Reactivity_index.index_dir_from_outputprefix outputprefix with
    | Some _ as index_dir -> index_dir
    | None ->
      Reactivity_index.index_dir_from_sourcefile !Location.input_name
  in

  let lookup_reactivity_summary_for_path path =
    match reactivity_index_dir with
    | None -> None
    | Some index_dir ->
      Reactivity_index.read_value_summary_for_path ~index_dir ~path
  in

  let callee_kind_for_path ~path ~value_description =
    let from_value_description = callee_kind_of_ident ~path ~value_description in
    let from_summary =
      match lookup_reactivity_summary_for_path path with
      | None -> empty_callee_kind
      | Some summary -> callee_kind_of_reactivity_summary summary
    in
    let merged = merge_callee_kind from_value_description from_summary in
    let path_name = path_last_name path in
    {
      merged with
      primitive_name =
        (match merged.primitive_name with
        | Some _ as name -> name
        | None -> path_name);
    }
  in

  let value_bindings = collect_value_bindings structure in
  let scope_callable_stamps, primitive_callable_stamps =
    compute_callable_sets ~callee_kind_for_path value_bindings
  in
  let accessor_stamps, proxy_stamps, setter_stamps =
    collect_carrier_sets ~lookup_reactivity_summary_for_path
      value_bindings
  in
  let reads_reactive_stamps =
    compute_reads_reactive_set ~callee_kind_for_path
      ~lookup_reactivity_summary_for_path ~accessor_stamps ~proxy_stamps
      value_bindings
  in
  let escape_stamps =
    compute_escape_set ~callee_kind_for_path ~lookup_reactivity_summary_for_path
      ~accessor_stamps ~proxy_stamps ~setter_stamps value_bindings
  in
  let escape_ok_stamps =
    collect_attribute_bound_stamps value_bindings escape_ok_attribute_names
  in

  let top_level_bound_idents = collect_top_level_bound_idents structure in
  let all_bound_idents = collect_all_bound_idents value_bindings in

  let summary_for_bound_ident (bound_ident : bound_ident) :
      Reactivity_index.value_summary =
    {
      is_scope_creator =
        IntSet.mem bound_ident.stamp scope_callable_stamps;
      is_primitive_creator =
        IntSet.mem bound_ident.stamp primitive_callable_stamps;
      is_accessor = IntSet.mem bound_ident.stamp accessor_stamps;
      is_proxy = IntSet.mem bound_ident.stamp proxy_stamps;
      is_setter = IntSet.mem bound_ident.stamp setter_stamps;
      reads_reactive = IntSet.mem bound_ident.stamp reads_reactive_stamps;
      escapes_reactive = IntSet.mem bound_ident.stamp escape_stamps;
      escape_ok = IntSet.mem bound_ident.stamp escape_ok_stamps;
    }
  in

  let summary_by_name = Hashtbl.create 16 in
  List.iter
    (fun (bound_ident : bound_ident) ->
      let summary = summary_for_bound_ident bound_ident in
      if Reactivity_index.has_reactivity summary then
        let merged =
          match Hashtbl.find_opt summary_by_name bound_ident.name with
          | None -> summary
          | Some existing ->
            Reactivity_index.merge_value_summary existing summary
        in
        Hashtbl.replace summary_by_name bound_ident.name merged)
    top_level_bound_idents;
  let module_summary_values =
    Hashtbl.to_seq summary_by_name |> List.of_seq
    |> List.sort (fun (left_name, _) (right_name, _) ->
           String.compare left_name right_name)
  in
  let summary_by_stamp = Hashtbl.create 16 in
  List.iter
    (fun (bound_ident : bound_ident) ->
      let summary = summary_for_bound_ident bound_ident in
      if Reactivity_index.has_reactivity summary then
        let merged =
          match Hashtbl.find_opt summary_by_stamp bound_ident.stamp with
          | None -> summary
          | Some existing ->
            Reactivity_index.merge_value_summary existing summary
        in
        Hashtbl.replace summary_by_stamp bound_ident.stamp merged)
    all_bound_idents;
  let module_summary_stamps =
    Hashtbl.to_seq summary_by_stamp |> List.of_seq
    |> List.sort (fun (left_stamp, _) (right_stamp, _) ->
           Int.compare left_stamp right_stamp)
  in
  (match reactivity_index_dir with
  | None -> ()
  | Some index_dir ->
    Reactivity_index.write_module_summary_in_index_dir ~index_dir ~module_name
      ~values:module_summary_values ~stamps:module_summary_stamps);

  let reactive_scope_depth = ref 0 in
  let with_reactive_scope visit =
    reactive_scope_depth := !reactive_scope_depth + 1;
    try
      let result = visit () in
      reactive_scope_depth := !reactive_scope_depth - 1;
      result
    with error ->
      reactive_scope_depth := !reactive_scope_depth - 1;
      raise error
  in

  let callee_kind_for_expression callee =
    match callee.exp_desc with
    | Texp_ident (Path.Pident ident, _, value_description) ->
      let from_value_description =
        callee_kind_for_path ~path:(Path.Pident ident) ~value_description
      in
      {
        is_scope_creator =
          from_value_description.is_scope_creator
          || IntSet.mem (stamp_of_ident ident) scope_callable_stamps;
        is_primitive_creator =
          from_value_description.is_primitive_creator
          || IntSet.mem (stamp_of_ident ident) primitive_callable_stamps;
        is_accessor =
          from_value_description.is_accessor
          || IntSet.mem (stamp_of_ident ident) accessor_stamps;
        is_proxy =
          from_value_description.is_proxy
          || IntSet.mem (stamp_of_ident ident) proxy_stamps;
        is_setter =
          from_value_description.is_setter
          || IntSet.mem (stamp_of_ident ident) setter_stamps;
        reads_reactive =
          from_value_description.reads_reactive
          || IntSet.mem (stamp_of_ident ident) reads_reactive_stamps;
        escapes_reactive =
          from_value_description.escapes_reactive
          || IntSet.mem (stamp_of_ident ident) escape_stamps;
        escape_ok =
          from_value_description.escape_ok
          || IntSet.mem (stamp_of_ident ident) escape_ok_stamps;
        primitive_name =
          (match from_value_description.primitive_name with
          | Some _ as name -> name
              | None -> Some (Ident.name ident));
      }
    | Texp_ident (path, _, value_description) ->
      callee_kind_for_path ~path ~value_description
    | _ -> empty_callee_kind
  in

  let iterator =
    {
      Tast_iterator.default_iterator with
      value_binding =
        (fun self (value_binding : value_binding) ->
          let call_kind = call_expression_kind value_binding.vb_expr in
          (match
             ( call_kind.primitive_name,
               first_two_tuple_patterns value_binding.vb_pat )
           with
          | Some "createStore", Some (first_pattern, _) ->
            if not (pattern_is_simple_binding first_pattern) then
              let proxy_name =
                match first_non_simple_pattern_name first_pattern with
                | Some name -> name
                | None -> "store proxy"
              in
              emit_warning value_binding.vb_pat.pat_loc
                (Warnings.Bs_reactivity_proxy_destructure proxy_name)
          | _ -> ());

          (if pattern_is_destructuring value_binding.vb_pat then
             match value_binding.vb_expr.exp_desc with
             | Texp_ident (path, _, value_description) ->
               let source_kind =
                 callee_kind_for_path ~path ~value_description
               in
               if source_kind.is_proxy then
                 let proxy_name =
                   string_of_callee_name ~fallback_name:"store proxy"
                     (path_last_name path)
                 in
                 emit_warning value_binding.vb_pat.pat_loc
                   (Warnings.Bs_reactivity_proxy_destructure proxy_name)
             | _ -> ());

          if !reactive_scope_depth = 0 then (
            match
              ( single_bound_ident_of_pattern value_binding.vb_pat,
                value_binding.vb_expr.exp_desc )
            with
            | Some _, Texp_apply {funct = callee; _} ->
              let callee_kind = callee_kind_for_expression callee in
              if callee_kind.is_accessor || callee_kind.reads_reactive then
                let accessor_name =
                  string_of_callee_name
                    ~fallback_name:"reactive accessor/read function"
                    callee_kind.primitive_name
                in
                  emit_warning value_binding.vb_expr.exp_loc
                    (Warnings.Bs_reactivity_stale_snapshot
                       accessor_name)
            | _ -> ());
          Tast_iterator.default_iterator.value_binding self value_binding);
      expr =
        (fun self expression ->
          match expression.exp_desc with
          | Texp_apply {funct = callee; args; _} ->
            (match callee.exp_desc with
            | Texp_ident (path, _, _) -> (
              match unsafe_cast_name_of_path path with
              | Some cast_name ->
                emit_warning expression.exp_loc
                  (Warnings.Bs_unsafe_cast cast_name)
              | None -> ())
            | _ -> ());
            let callee_kind = callee_kind_for_expression callee in
            if !reactive_scope_depth > 0 && callee_kind.is_primitive_creator
            then (
              let primitive_name =
                string_of_callee_name ~fallback_name:"reactive primitive"
                  callee_kind.primitive_name
              in
              emit_warning expression.exp_loc
                (Warnings.Bs_reactivity_primitive_in_scope primitive_name));
            if
              (not (callee_is_known_reactive callee_kind))
              || callee_kind.escapes_reactive
            then
              let has_reactive_arg =
                List.exists
                  (fun (_, argument_expression_opt) ->
                    match argument_expression_opt with
                    | None -> false
                    | Some argument_expression ->
                      expression_contains_reactive_value
                        ~accessor_stamps ~proxy_stamps ~setter_stamps
                        ~lookup_reactivity_summary_for_path argument_expression)
                  args
              in
              if has_reactive_arg then
                let callee_name =
                  match callee.exp_desc with
                  | Texp_ident (path, _, _) ->
                    string_of_callee_name ~fallback_name:"unknown API"
                      (path_last_name path)
                  | _ ->
                    string_of_callee_name ~fallback_name:"unknown API"
                      callee_kind.primitive_name
                in
                emit_warning expression.exp_loc
                  (Warnings.Bs_reactivity_escape callee_name);
            let visit_apply_subexpressions () =
              self.expr self callee;
              List.iter
                (fun (_, argument_expression_opt) ->
                  Option.iter (self.expr self) argument_expression_opt)
                args
            in
            if callee_kind.is_scope_creator then
              with_reactive_scope visit_apply_subexpressions
            else visit_apply_subexpressions ()
          | _ -> Tast_iterator.default_iterator.expr self expression);
    }
  in
  iterator.structure iterator structure
