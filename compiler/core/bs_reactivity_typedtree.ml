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
  primitive_name : string option;
}

let empty_callee_kind =
  {
    is_scope_creator = false;
    is_primitive_creator = false;
    primitive_name = None;
  }

let scope_attribute_names =
  [ "reactive.scope"; "reactiveScope"; "nobie.reactive.scope" ]

let primitive_attribute_names =
  [ "reactive.primitive"; "reactivePrimitive"; "nobie.reactive.primitive" ]

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
    primitive_name =
      (match by_value_description.primitive_name with
      | Some _ as name -> name
      | None -> path_name);
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

let expression_contains_target_call ~target_stamps ~direct_target_predicate
    expression =
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
              | Texp_ident (Path.Pident ident, _, value_description) ->
                if
                  IntSet.mem (stamp_of_ident ident) target_stamps
                  || direct_target_predicate value_description
                then found := true
                else Tast_iterator.default_iterator.expr self current_expression
              | Texp_ident (_, _, value_description) ->
                if direct_target_predicate value_description then found := true
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

let compute_callable_sets value_bindings =
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

          (match value_binding.vb_expr.exp_desc with
          | Texp_ident (Path.Pident source_ident, _, value_description) ->
            let source_stamp = stamp_of_ident source_ident in
            maybe_add_scope (IntSet.mem source_stamp !scope_callable_stamps);
            maybe_add_primitive
              (IntSet.mem source_stamp !primitive_callable_stamps);
            let direct_kind =
              callee_kind_of_ident
                ~path:(Path.Pident source_ident)
                ~value_description
            in
            maybe_add_scope direct_kind.is_scope_creator;
            maybe_add_primitive direct_kind.is_primitive_creator
          | Texp_ident (path, _, value_description) ->
            let direct_kind = callee_kind_of_ident ~path ~value_description in
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
                   ~direct_target_predicate:(fun value_description ->
                     (callee_kind_of_value_description value_description)
                       .is_scope_creator))
                function_bodies
            in
            let body_mentions_primitive =
              List.exists
                (expression_contains_target_call
                   ~target_stamps:!primitive_callable_stamps
                   ~direct_target_predicate:(fun value_description ->
                     (callee_kind_of_value_description value_description)
                       .is_primitive_creator))
                function_bodies
            in
            maybe_add_scope body_mentions_scope;
            maybe_add_primitive body_mentions_primitive))
      value_bindings
  done;

  (!scope_callable_stamps, !primitive_callable_stamps)

let collect_accessor_and_proxy_sets value_bindings =
  let accessor_stamps = ref IntSet.empty in
  let proxy_stamps = ref IntSet.empty in

  let add_accessor bound_ident =
    accessor_stamps := IntSet.add bound_ident.stamp !accessor_stamps
  in
  let add_proxy bound_ident = proxy_stamps := IntSet.add bound_ident.stamp !proxy_stamps in

  List.iter
    (fun (value_binding : value_binding) ->
      let call_kind = call_expression_kind value_binding.vb_expr in
      match call_kind.primitive_name with
      | Some "createSignal" | Some "createResource" -> (
        match first_two_tuple_patterns value_binding.vb_pat with
        | Some (first_pattern, _) -> (
          match single_bound_ident_of_pattern first_pattern with
          | Some accessor_bound_ident -> add_accessor accessor_bound_ident
          | None -> ())
        | None -> ())
      | Some "createStore" -> (
        match first_two_tuple_patterns value_binding.vb_pat with
        | Some (first_pattern, _) -> (
          match single_bound_ident_of_pattern first_pattern with
          | Some proxy_bound_ident -> add_proxy proxy_bound_ident
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
        match (single_bound_ident_of_pattern value_binding.vb_pat, value_binding.vb_expr.exp_desc) with
        | Some bound_ident, Texp_ident (Path.Pident source_ident, _, _) ->
          let source_stamp = stamp_of_ident source_ident in
          if
            IntSet.mem source_stamp !accessor_stamps
            && not (IntSet.mem bound_ident.stamp !accessor_stamps)
          then (
            accessor_stamps := IntSet.add bound_ident.stamp !accessor_stamps;
            changed := true);
          if
            IntSet.mem source_stamp !proxy_stamps
            && not (IntSet.mem bound_ident.stamp !proxy_stamps)
          then (
            proxy_stamps := IntSet.add bound_ident.stamp !proxy_stamps;
            changed := true)
        | _ -> ())
      value_bindings
  done;

  (!accessor_stamps, !proxy_stamps)

let emit_warning location warning =
  if not location.Location.loc_ghost then Location.prerr_warning location warning

let first_non_simple_pattern_name pattern =
  match pattern.pat_desc with
  | Tpat_var (_, name_loc) -> Some name_loc.txt
  | Tpat_alias (_, _, name_loc) -> Some name_loc.txt
  | _ -> None

let emit_warnings structure =
  let value_bindings = collect_value_bindings structure in
  let scope_callable_stamps, primitive_callable_stamps =
    compute_callable_sets value_bindings
  in
  let accessor_stamps, proxy_stamps = collect_accessor_and_proxy_sets value_bindings in

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
        callee_kind_of_ident
          ~path:(Path.Pident ident)
          ~value_description
      in
      {
        is_scope_creator =
          from_value_description.is_scope_creator
          || IntSet.mem (stamp_of_ident ident) scope_callable_stamps;
        is_primitive_creator =
          from_value_description.is_primitive_creator
          || IntSet.mem (stamp_of_ident ident) primitive_callable_stamps;
        primitive_name =
          (match from_value_description.primitive_name with
          | Some _ as name -> name
              | None -> Some (Ident.name ident));
      }
    | Texp_ident (path, _, value_description) ->
      callee_kind_of_ident ~path ~value_description
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
             | Texp_ident (Path.Pident source_ident, _, _) ->
               let source_stamp = stamp_of_ident source_ident in
               if IntSet.mem source_stamp proxy_stamps then
                 emit_warning value_binding.vb_pat.pat_loc
                   (Warnings.Bs_reactivity_proxy_destructure
                      (Ident.name source_ident))
             | _ -> ());

          if !reactive_scope_depth = 0 then (
            match
              ( single_bound_ident_of_pattern value_binding.vb_pat,
                value_binding.vb_expr.exp_desc )
            with
            | Some _, Texp_apply {funct = callee; _} -> (
              match callee.exp_desc with
              | Texp_ident (Path.Pident source_ident, _, _) ->
                if IntSet.mem (stamp_of_ident source_ident) accessor_stamps then
                  emit_warning value_binding.vb_expr.exp_loc
                    (Warnings.Bs_reactivity_stale_snapshot
                       (Ident.name source_ident))
              | _ -> ())
            | _ -> ());
          Tast_iterator.default_iterator.value_binding self value_binding);
      expr =
        (fun self expression ->
          match expression.exp_desc with
          | Texp_apply {funct = callee; args; _} ->
            let callee_kind = callee_kind_for_expression callee in
            if !reactive_scope_depth > 0 && callee_kind.is_primitive_creator
            then (
              let primitive_name =
                string_of_callee_name ~fallback_name:"reactive primitive"
                  callee_kind.primitive_name
              in
              emit_warning expression.exp_loc
                (Warnings.Bs_reactivity_primitive_in_scope primitive_name));
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
