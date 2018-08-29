
import category.basic tactic
import category.liftable
import lawful

universes u v

namespace monad

variables {α β γ : Type u}
variables {m : Type u → Type v} [monad m]

@[reducible]
def pipe (a : α → m β) (b : β → m γ) : α → m γ :=
λ x, a x >>= b

infixr ` >=> `:55 := pipe

end monad

@[functor_norm]
lemma map_bind_eq_bind_comp {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → β) (cmd : m α) (g : β → m γ) :
  (f <$> cmd) >>= g = cmd >>= g ∘ f :=
by rw [← bind_pure_comp_eq_map,bind_assoc,(∘)]; simp

@[functor_norm]
lemma bind_map {α β γ} {m} [monad m] [is_lawful_monad m]
  (f : α → γ → β) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <$> g x) = do { x ← cmd, y ← g x, pure $ f x y }  :=
sorry

@[functor_norm]
lemma bind_seq {α β γ : Type u} {m} [monad m] [is_lawful_monad m]
  (f : α → m (γ → β)) (cmd : m α) (g : α → m γ) :
  cmd >>= (λ x, f x <*> g x) = do { x ← cmd, h ← f x, y ← g x, pure $ h y }  :=
sorry
-- by rw [← bind_pure_comp_eq_map,bind_assoc,(∘)]; simp

@[simp]
lemma prod_map_comp {α₀ α₁ β₀ β₁ γ₀ γ₁}
  {f₀ : α₀ → β₀} {g₀ : β₀ → γ₀}
  {f₁ : α₁ → β₁} {g₁ : β₁ → γ₁} :
  prod.map g₀ g₁ ∘ prod.map f₀ f₁ = prod.map (g₀ ∘ f₀) (g₁ ∘ f₁) :=
by ext x ; cases x; refl

def state_t.exec {α σ : Type u} {m} [monad m] (cmd : state_t σ m α) : σ → m σ :=
λ (s : σ), prod.snd <$> cmd.run s

def state_t.eval {α σ : Type u} {m} [monad m] (cmd : state_t σ m α) (s : σ) : m α :=
prod.fst <$> cmd.run s

-- @[reducible]
def state.exec {α σ : Type u} (cmd : state σ α) (s : σ) : σ :=
state_t.exec cmd s

def state.eval {α σ : Type u} (cmd : state σ α) (s : σ) : σ :=
state_t.exec cmd s

variables {m : Type u → Type v} [monad m] [is_lawful_monad m]
variables {α β σ γ : Type u}

@[simp]
lemma state.run_map
  (f : α → β) (x : state_t σ m α) (s : σ) :
  (pure f <*> x).run s = prod.map f id <$> x.run s :=
by { cases x; simp [has_seq.seq,pure,state_t.pure,state_t.bind,pure_bind],
     rw ← bind_pure_comp_eq_map, congr, ext, cases x_1, refl, }

-- @[simp]
-- lemma state.exec_seq {α β : Type u} {σ}
--   (f : state_t σ m $ α → β) (x : state_t σ m α) (s : σ) :
--   (f <*> x).exec s = f.exec s >>= x.exec :=
-- by { cases x; cases f; simp [has_seq.seq,pure,state_t.pure,state_t.bind,pure_bind,state_t.exec,map_bind] with functor_norm,
--      congr, ext s, cases s, simp [state_t.bind._match_1,map_bind,state_t.exec] with functor_norm,
--      rw ← bind_pure_comp_eq_map, congr, ext z, cases z, simp [state_t.bind._match_1,state_t.pure] }

-- @[simp]
-- lemma state.exec_bind {α β : Type u} {σ}
--   (f : state_t σ m α) (x : state_t σ m β) :
--   (f >> x).exec = f.exec >=> x.exec :=
-- by cases x; cases f; simp [has_seq.seq,pure,state_t.pure,state_t.bind,pure_bind,state_t.exec,map_bind,(>>)] with functor_norm; congr

@[simp]
lemma state.run_seq {α β : Type u} {σ}
  (f : state_t σ m $ α → β) (x : state_t σ m α) (s : σ) :
  (f <*> x).run s = f.run s >>= λ r:(α → β)×σ, x.run r.2 >>= λ r', pure (r.1 r'.1,r'.2) :=
by { cases x; cases f; simp [has_seq.seq,pure,state_t.pure,state_t.bind,pure_bind,state_t.exec,map_bind] with functor_norm,
     congr, ext s, cases s, simp [state_t.bind._match_1,map_bind,state_t.exec] with functor_norm,
     congr, ext s', cases s', refl }

lemma id_bind_def (x : id α) (f : α → id β) :
  x >>= f = f x := by simp [(>>=),id_bind]

lemma id_map_def (x : id α) (f : α → β) :
  f <$> x = f x := by simp [(<$>),id_bind]

variables [is_lawful_monad m]

-- @[simp]
-- lemma monad_state_lift_bind {σ α β} [monad_state σ m] (x : state σ α) (y : α → state σ β) :
--   (monad_state.lift $ x >>= y : m β) = monad_state.lift x >>= monad_state.lift ∘ y :=
-- by { cases x, simp [monad_state.lift,(>>=),state_t.bind,id_bind],
--      ext z, cases x z, refl }

-- @[simp]
-- lemma monad_state_lift_bind' {σ α β} [monad_state σ m] (x : state σ α) (y : state σ β) :
--   (monad_state.lift $ x >> y : m β) = monad_state.lift x >> monad_state.lift y :=
-- by simp [(>>)]

lemma bind_eq_of_eq_pure (x : m α) (f : α → m β) (y : α) (x' : m β)
  (h : x = pure y)
  (h' : f y = x') :
  x >>= f = x' :=
by simp *

attribute [functor_norm] bind_assoc has_bind.and_then map_bind

-- lemma monad_state_lift_liftable_up (α') {σ' m'}
--   [functor m'] [is_lawful_functor m'] [liftable1 m' m]
--   [liftable σ' σ]
--   (cmd : state σ' α')
--   (Hα : α' ≃ α) :
--   (monad_state.lift $ liftable1.up Hα cmd : state_t σ m α) =
--   (liftable1.up Hα (monad_state.lift (cmd : state σ' α') : state_t σ' m' α')) :=
-- sorry
