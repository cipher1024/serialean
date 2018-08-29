
import tactic

@[simp]
lemma bind_pure_star {m} [monad m] [is_lawful_monad m] (x : m punit) :
  x >>= (λ (_x : punit), pure punit.star : punit → m punit) = x :=
by { transitivity,
     { apply congr_arg, ext z, cases z, refl },
     { simp } }
