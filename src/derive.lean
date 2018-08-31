
import serial
import tactic.serial
import tactic.norm_num
import tactic.basic
import category.basic

section tactic

open tactic

meta def mk_up (u : level) (e : expr) : tactic expr :=
do t  ← infer_type e,
   u' ← mk_meta_univ,
   (t,e)  ← mcond (succeeds $ infer_type t >>= unify (expr.sort (level.succ u')))
     (pure (t,e))
     (prod.mk <$> mk_app ``plift [t] <*> mk_app ``plift.up [e]),
   let up : expr := expr.const ``ulift.up [u,u'],
   pure $ up t e

meta def mk_down (u : level) (e t : expr) : tactic expr :=
do u' ← mk_meta_univ,
   e ← mk_app ``ulift.down [e],
   mcond (succeeds $ infer_type t >>= unify (expr.sort (level.succ u')))
     (pure (e))
     (mk_app ``plift.down [e])

meta def mk_ulift (u : level) (t : expr) : tactic expr :=
do u' ← mk_meta_univ,
   t  ← mcond (succeeds $ infer_type t >>= unify (expr.sort (level.succ u')))
     (pure t)
     (mk_app ``plift [t] <|> do { t ← pp t, fail format!"plift {t}" }),
   let ulift_t : expr := expr.const ``ulift [u,u'],
   pure $ ulift_t t

meta def mk_encode (u : level) : tactic (list (name × list (expr × expr))) :=
do x ← intro1,
   vs ← cases_core x,
   gs ← get_goals,
   mzip_with (λ (g : ℕ × expr) (c : name × list expr × list (name × expr)),
     do let ⟨i,g⟩ := g,
        set_goals [g],
        when (gs.length ≠ 1) $ refine ``(write_word (fin.of_nat %%(reflect i)) >> _),
        let ⟨c,vs,_⟩ := c,
        vs' ← vs.mmap infer_type,
        vs.mmap' (λ v,
          do v ← mk_up u v,
             refine ``(encode %%v >> _)),
        refine ``(pure punit.star),
        (c,vs.zip vs') <$ done) gs.enum vs

meta def mk_parser (u : level) : expr → list (expr × expr) → list (name × expr) → tactic unit
| e [] _ := refine ``(pure %%e)
| e ((v,t) :: vs) σ :=
do let t := t.instantiate_locals σ,
   ulift_t ← mk_ulift u t,
   refine ``(decode %%ulift_t >>= _),
   v' ← intro1,
   v' ← mk_down u v' t,
   mk_parser (e v') vs ( (v.local_uniq_name,v') :: σ )

meta def mk_decode (u : level) (n : name) (pat : list (name × list (expr × expr))) : tactic unit :=
do t ← target,
   e ← get_env,
   if pat.length = 1 then do
       let ⟨c,vs⟩ := pat.head,
       c ← mk_const c,
       mk_parser u c vs []
   else do
     refine ``(select_tag _),
     pat.enum.mmap' $ λ ⟨i,c,vs⟩, do {
       v₀ ← mk_mvar, v₁ ← mk_mvar,
       refine ``((fin.of_nat %%(reflect i),%%v₀) :: %%v₁),
       set_goals [v₀],
       c ← mk_const c,
       mk_parser u c vs [], done,
       set_goals [v₁] },
     refine ``([])

-- set_option trace.app_builder true
open tactic.interactive (unfold norm_num trivial)
open interactive

meta def reduce_select_tag (tag : expr) : expr → tactic unit
| `( list.cons (fin.of_nat %%n, %%br) %%brs ) :=
  if n =ₐ tag then do
    v ← mk_mvar,
    to_expr ``(read_write_tag_hit %%v) >>= rewrite_target,
    gs ← get_goals,
    set_goals [v], tactic.interactive.norm_num [] (loc.ns [none]), done,
    set_goals gs
  else do
    v ← mk_mvar,
    to_expr ``(read_write_tag_miss %%v) >>= rewrite_target,
    gs ← get_goals,
    set_goals [v],
    do { applyc ``fin.ne_of_vne,
         let rs := list.map simp_arg_type.expr
             [``(fin.of_nat),``(fin.val),``(nat.succ_eq_add_one)],
         tactic.interactive.norm_num rs (loc.ns [none]), done },
    set_goals gs,
    reduce_select_tag brs
| e := failed

meta def match_sum_branch : tactic unit :=
do brs ← mk_mvar, tag ← mk_mvar,
   tgt ← target,
   to_expr ``(select_tag %%brs -<< (write_word (fin.of_nat %%tag) >>= _) = _) >>= unify tgt,
   brs ← instantiate_mvars brs,
   tag ← instantiate_mvars tag,
   reduce_select_tag tag brs

meta def mk_serial_correctness (encode_n decode_n : name) : tactic unit :=
do w ← intro1, cases w,
   all_goals $ do {
     dunfold_target [decode_n,encode_n],
     match_sum_branch <|> skip,
     `[simp [(>>),encode_decode_bind,encode_decode_bind',encode_decode_pure]],
     done }

meta def mk_serial_instance : tactic unit :=
do tgt ← target,
   let t := tgt.app_arg,
   (expr.sort (level.succ u)) ← infer_type t,
   let n := t.get_app_fn.const_name,
   d ← get_decl n,
   let t := d.is_trusted,
   enc ← mk_mvar,
   dec ← mk_mvar,
   correct ← mk_mvar,
   refine ``( { encode := %%enc,
                decode := %%dec,
                correctness := %%correct } ),
   let decode_n := n <.> "decode",
   let encode_n := n <.> "encode",
   set_goals [enc],
   vs ← extract_def' encode_n t (mk_encode u),
   set_goals [dec],
   extract_def' decode_n t (mk_decode u n vs),
   set_goals [correct],
   mk_serial_correctness encode_n decode_n

@[derive_handler] meta def serial_derive_handler :=
instance_derive_handler ``serial mk_serial_instance

end tactic

@[derive serial]
inductive my_sum
| first : my_sum
| second : ℕ → my_sum
| third (n : ℕ) (xs : list ℕ) : n ≤ xs.length → my_sum

@[derive serial]
structure my_struct :=
(x : ℕ)
(xs : list ℕ)
(bounded : xs.length ≤ x)
