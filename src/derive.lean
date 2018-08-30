
import serial
import tactic.serial
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
   mzip_with (λ g (c : name × list expr × list (name × expr)),
     do set_goals [g],
        let ⟨c,vs,_⟩ := c,
        vs' ← vs.mmap infer_type,
        vs.mmap' (λ v,
          do v ← mk_up u v,
             refine ``(encode %%v >> _)),
        refine ``(pure punit.star),
        (c,vs.zip vs') <$ done) gs vs

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
   let ⟨c,vs⟩ := pat.head,
   c ← mk_const c,
   mk_parser u c vs []

-- set_option trace.app_builder true
open tactic.interactive (unfold)
open interactive

meta def mk_serial_correctness (encode_n decode_n : name) : tactic unit :=
do w ← intro1, cases w,
   all_goals $ do {
     dunfold_target [decode_n,encode_n],
     -- unfold_projs_target,
     `[simp [(>>),encode_decode_bind,encode_decode_bind',encode_decode_pure]] }

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
   extract_def decode_n t (mk_decode u n vs),
   set_goals [correct],
   mk_serial_correctness encode_n decode_n

@[derive_handler] meta def serial_derive_handler :=
instance_derive_handler ``serial mk_serial_instance

end tactic

@[derive serial]
structure my_struct :=
(x : ℕ)
(xs : list ℕ)
(bounded : xs.length ≤ x)
