
import tactic.basic

namespace tactic

meta def extract_def' {α} (n : name) (trusted : bool) (elab_def : tactic α) : tactic α :=
do cxt ← list.map to_implicit <$> local_context,
   t ← target,
   (r,d) ← solve_aux t elab_def,
   d ← instantiate_mvars d,
   t' ← pis cxt t,
   d' ← lambdas cxt d,
   let univ := t'.collect_univ_params,
   add_decl $ declaration.defn n univ t' d' (reducibility_hints.regular 1 tt) trusted,
   r <$ applyc n

end tactic
