
import tactic
import logic.basic
import category.serial
import category.liftable
import category.liftable.serial

universes u v

inductive put_m' (α : Type u)
| pure : α → put_m'
| write : unsigned → (unit → put_m') → put_m'

def put_m'.bind {α β} : put_m' α → (α → put_m' β) → put_m' β
| (put_m'.pure x)   f := f x
| (put_m'.write w f) g := put_m'.write w $ λ u, put_m'.bind (f u) g

instance : monad put_m' :=
{ pure := λ α, put_m'.pure
, bind := @put_m'.bind }

instance : is_lawful_monad put_m' :=
by { refine { .. }; intros;
       try { refl };
       induction x;
       try { refl };
     { dsimp [put_m'.bind] at *, congr, simp * } }

@[reducible]
def put_m := put_m' punit

def put_m.eval : put_m → list unsigned
| (put_m'.pure x) := []
| (put_m'.write w f) := w :: put_m.eval (f punit.star)

inductive get_m : Type u → Type (u+1)
| fail {α} : get_m α
| pure {α} : α → get_m α
| read {α} : (unsigned → get_m α) → get_m α
| loop {α β γ : Type u} : (β → unsigned → get_m (α ⊕ β)) → (α → get_m γ) → β → get_m γ

def get_m.bind : Π {α β}, get_m α → (α → get_m β) → get_m β
| _ _ (get_m.fail) _ := get_m.fail
| _ _ (get_m.pure x)   f := f x
| _ _ (get_m.read f) g := get_m.read $ λ w, get_m.bind (f w) g
| _ _ (get_m.loop f g x₀) h := get_m.loop f (λ r, get_m.bind (g r) h) x₀

def get_m.map : Π {α β : Type u}, (α → β) → get_m α → get_m β
| _ _ _ (get_m.fail) := get_m.fail
| _ _ f (get_m.pure x) := get_m.pure $ f x
| _ _ f (get_m.read g) := get_m.read $ λ w, get_m.map f (g w)
| _ _ h (get_m.loop f g x₀) := get_m.loop f (λ r, get_m.map h (g r)) x₀

instance : functor get_m.{u} :=
{ map := @get_m.map }

def get_m.seq {α β : Type u} : Π (f : get_m (α → β)) (x : get_m α), get_m β :=
λ (f : get_m (α → β)) (x : get_m α), get_m.bind f (λ f, f <$> x)

-- instance : applicative get_m :=
-- { to_functor := get_m.functor
-- , pure := λ α, get_m.pure
-- , seq := @get_m.seq }
open function

instance : is_lawful_functor.{u} get_m :=
by { constructor; intros;
     dsimp [(<$>),get_m.seq];
     induction x;
     try { refl };
     simp [get_m.map,*]; ext }

instance : monad get_m :=
{ to_functor := get_m.functor
, pure := @get_m.pure
, bind := @get_m.bind }

instance : is_lawful_monad get_m.{u} :=
{ to_is_lawful_functor := get_m.is_lawful_functor,
  bind_assoc := by { intros, dsimp [(>>=)],
                     induction x; try { refl }; simp [get_m.bind,*], },
  bind_pure_comp_eq_map := by { intros, dsimp [(>>=),(<$>)],
                                induction x; try {refl}; simp [get_m.bind,get_m.map,*], },
  map_pure := by intros; refl,
  pure_seq_eq_map := by { intros, dsimp [(>>=),(<$>)],
                          induction x; try {refl}; simp [get_m.bind,get_m.map,*], },
  pure_bind := by intros; refl }

def get_m.eval {α} : list unsigned → get_m α → option α
| [] (get_m.pure x) := pure x
| [] _  := none
| (w :: ws) (get_m.read f) := get_m.eval ws (f w)
| (w :: ws) (get_m.loop f g x₀) :=
  get_m.eval ws $
  f x₀ w >>= @sum.rec _ _ (λ _, get_m α) g (get_m.loop f g)
| (w :: ws) _ := none


def read_write : Π {α}, get_m.{u} α → put_m.{u} → option α
| ._ (get_m.pure x) (put_m'.pure _) := some x
| _ _ (put_m'.pure _) := none
| ._ (get_m.read f) (put_m'.write w g) := read_write (f w) (g punit.star)
| α (@get_m.loop α' β γ f g x₀) (put_m'.write w h) :=
  read_write
    (f x₀ w >>= @sum.rec α' β (λ _, get_m α) g (get_m.loop f g))
    (h punit.star)
| _ _ (put_m'.write w g) := none

def read_write' : Π {α}, get_m α → put_m → option (α × put_m)
| _ (get_m.read f) (put_m'.write w g) := read_write' (f w) (g punit.star)
| α (@get_m.loop α' β γ f g x₀) (put_m'.write w h) :=
  read_write'
    (f x₀ w >>= @sum.rec α' β (λ _, get_m α) g (get_m.loop f g))
    (h punit.star)
-- | _ (get_m.pure x) m@(put_m'.write w g) := some (x,m)
| _ (get_m.pure x) m := some (x,m)
| _ _ (put_m'.pure _) := none
| _ (get_m.fail) (put_m'.write _ _) := none
-- | _ _ m := none

lemma read_read_write_write {α} (x : get_m α) (m : put_m) (i : α) :
  read_write x m = some i ↔ read_write' x m = some (i,pure punit.star) :=
begin
  induction m generalizing x;
  cases x; casesm* punit; simp [read_write,read_write',prod.ext_iff,pure,*],
end

def pipeline {α} (x : get_m α) (y : α → put_m) (i : α) : option α :=
read_write x (y i)

infix ` -<< `:60  := read_write
infix ` -<<< `:60  := read_write'
infix ` <-< `:60  := pipeline

lemma eq_star (x : punit) : x = punit.star :=
by cases x; refl

-- inductive agree : Π {α} (x : α), get_m α → put_m → put_m → Prop
-- | pure {α} (x : α) (m : put_m) : agree x (get_m.pure x) m m
-- | read_write {α} (x : α) (w : unsigned)
--   (f : unsigned → get_m α) (g : punit → put_m) (m : put_m) :
--   agree x (f w) (g punit.star) m →
--   agree x (get_m.read f) (put_m'.write w g) m
-- | loop_write {α} (x : α) {β γ} (σ₀ σ₁ : β) (w : unsigned)
--   (f : β → unsigned → get_m (γ ⊕ β)) (f' : γ → get_m α)
--   (g : punit → put_m) (m m' : put_m) :
--   agree (sum.inr σ₁) (f σ₀ w) (g punit.star) m' →
--   agree x (get_m.loop σ₁ f f') m' m →
--   agree x (get_m.loop σ₀ f f') (put_m'.write w g) m
-- | loop_exit_write {α} (x : α) {β γ} (σ₀ : β) (r : γ) (w : unsigned)
--   (f : β → unsigned → get_m (γ ⊕ β)) (f' : γ → get_m α)
--   (g : punit → put_m) (m m' : put_m) :
--   agree (sum.inl r) (f σ₀ w) (g punit.star) m' →
--   agree x (f' r) m' m →
--   agree x (get_m.loop σ₀ f f') (put_m'.write w g) m

-- lemma agree_spec {α} (g : get_m α) (m : put_m) (x : α) :
--   agree x g m (put_m'.pure punit.star) ↔ g -<< m = some x :=
-- begin
--   split; intro h,
--   { cases h,
--     refl, simp [read_write], }
-- end

-- lemma loop_bind {α β γ} (i : β)
--       (body : β → unsigned → get_m (α ⊕ β)) (f₀ : α → get_m γ) :
--   get_m.loop i body f₀ = get_m.read (body i) >>= _ := _

lemma read_write_loop_bind {α β γ φ : Type u} (i : α)
      (body : α → unsigned → get_m (φ ⊕ α))
      (f₀ : φ → get_m β) (f₁ : β → get_m γ)
      (m : punit → put_m) (w : unsigned) :
  (get_m.loop body f₀ i >>= f₁) -<<< put_m'.write w m =
  (body i w >>= @sum.rec φ α (λ _, get_m β) f₀ (get_m.loop body f₀) >>= f₁) -<<< m punit.star :=
begin
  rw bind_assoc,
  simp [(>>=),get_m.bind,read_write'],
  congr, ext, cases x; simp; refl,
end

-- lemma read_write_left_overs_bind {α} (i : α)
--       (x₀ : get_m α)
--       (x₁ x₂ : put_m) :
-- x₀ -<<< x₁ = some (i,x₂) →

lemma fail_read_write {α} (x₁ : put_m) :
  get_m.fail -<<< x₁ = @none (α × put_m) :=
by cases x₁; refl

lemma pure_read_write {α} (x₁ : put_m) (i : α) :
  get_m.pure i -<<< x₁ = some (i, x₁) :=
by cases x₁; refl

lemma read_write_left_overs_bind {α} (f : punit → put_m) (i : α)
      (x₀ : get_m α)
      (x₁ x₂ : put_m) :
  x₀ -<<< x₁ = some (i,x₂) → x₀ -<<< (x₁ >>= f) = some (i,x₂ >>= f) :=
begin
  induction x₁ generalizing x₀ x₂,
  cases x₀; simp [(>>=),put_m'.bind,read_write',pure_read_write],
  { intros, subst x₂, tauto },
  cases x₀; simp [(>>=),put_m'.bind,read_write'],
  { intros, substs x₂ i, split; refl },
  { apply x₁_ih, },
  { apply x₁_ih, },
end

lemma option_eq_forall_some {α} (x y : option α) :
  x = y ↔ ∀ z, x = some z ↔ y = some z :=
begin
  split; intro h, { rw h; intro, refl },
  { cases y, cases x, refl,
    symmetry, rw ← h, rw h, },
end

lemma read_write_weakening {α}
  (x₀ x₁ : put_m) (y₀ y₁ : get_m α)
  (h : y₀ -<<< x₀ = y₁ -<<< x₁) :
  y₀ -<< x₀ = y₁ -<< x₁ :=
begin
  rw option_eq_forall_some,
  intro, simp [read_read_write_write,h],
end

lemma read_write_mono' {α β} (i : α)
      (x₀ : get_m α) (f₀ : α → get_m β)
      (x₁ x₂ : put_m)
      (h : x₀ -<<< x₁ = some (i,x₂)) :
  (x₀ >>= f₀) -<<< x₁ = f₀ i -<<< x₂ :=
begin
  -- simp [(>>=)],
  induction x₁ generalizing x₀ f₀;
    try { cases x₀; cases h },
  { simp [(>>=),read_write',get_m.bind] },
  { cases x₀; try { cases h },
    simp [(>>=),read_write',get_m.bind] at h ⊢,
    simp [(>>=),read_write',get_m.bind] at h ⊢,
    { apply x₁_ih, assumption },
    simp [read_write_loop_bind,x₁_ih],
    rw [x₁_ih _ _ _ h], }
end

lemma read_write_mono {α β} {i : α}
      {x₀ : get_m α} {f₀ : α → get_m β}
      {x₁ : put_m} {f₁ : punit → put_m}
      (h : x₀ -<< x₁ = some i) :
  (x₀ >>= f₀) -<< (x₁ >>= f₁) = f₀ i -<< f₁ punit.star :=
begin
  apply read_write_weakening,
  apply read_write_mono',
  rw [read_read_write_write] at h,
  replace h := read_write_left_overs_bind f₁ _ _ _ _ h,
  simp [h],
end

lemma read_write_mono_left {α β} {i : α}
      {x₀ : get_m α} {f₀ : α → get_m β}
      {x₁ : put_m}
      (h : x₀ -<< x₁ = some i) :
  (x₀ >>= f₀) -<< x₁ = f₀ i -<< pure punit.star :=
by rw ← read_write_mono h; simp

lemma read_write_eq_eval_eval {α}
      (x₀ : get_m α) (x₁ : put_m)  :
  x₀ -<< x₁ = x₀.eval x₁.eval :=
begin
  induction x₁ generalizing x₀; cases x₀; try { refl },
  simp! [*,read_write],
  simp! [*,read_write],
end
open ulift

lemma get_m.fold_bind {α β} (x : get_m α) (f : α → get_m β) :
  get_m.bind x f = x >>= f := rfl

lemma map_read_write {α β} (f : α → β) (x : get_m α) (y : put_m) :
  (f <$> x) -<< y = f <$> (x -<< y) :=
begin
  rw [← bind_pure_comp_eq_map,← bind_pure_comp_eq_map],
  symmetry,
  simp [(>>=)],
  induction y generalizing x,
  { cases x; refl },
  { cases x; simp [read_write]; try { refl };
    simp [get_m.bind,read_write,y_ih],
    congr' 1, cases h : x_a x_a_2 y_a, refl,
    cases a; refl,
    dsimp [(>>=),get_m.bind],
    congr, ext, simp [get_m.fold_bind],
    rw bind_assoc, congr, ext z, cases z; refl,
    simp [get_m.fold_bind], rw bind_assoc, congr, ext x,
    cases x; refl, }
end

def sum_ulift (α β : Type u) : (α ⊕ β) ≃ (ulift.{v} α ⊕ ulift.{v} β) :=
(equiv.sum_congr equiv.ulift.symm equiv.ulift.symm)

-- def get_m.up : Π {α : Type u} {β : Type.{max u v}} (Heq : α ≃ β), get_m α → get_m β
-- | _ _ Heq (get_m.pure x) := get_m.pure $ Heq x
-- | _ _ Heq (get_m.fail) := get_m.fail
-- | _ _ Heq (get_m.read f) := get_m.read (λ w, get_m.up Heq (f w))
-- | _ β' Heq (@get_m.loop α β γ f g x) :=
--   get_m.loop
--     (λ a b, get_m.up (sum_ulift α β) (f (down.{v} a) b))
--     (λ w, get_m.up Heq (g $ down w))
--     (up.{v} x)

def get_m.up : Π {α : Type u} {β : Type.{max u v}} (Heq : α → β), get_m α → get_m β :=
λ α β f x, (@get_m.rec_on (λ α _, Π β, (α → β) → get_m β) α x
(λ α β f, get_m.fail)
(λ α x β f, get_m.pure $ f x)
(λ α next get_m_up β f, get_m.read $ λ w, get_m_up w _ f)
(λ α β γ body rest x₀ get_m_up₀ get_m_up₁ β' f,
  get_m.loop
    (λ a b, get_m_up₀ (down a) b (ulift.{v} α ⊕ ulift.{v} β)
                     (sum_ulift α β))
    (λ r, get_m_up₁ (down r) _ f)
    (up x₀)) β f)

section eqns

variables {α β' γ : Type u} {β : Type.{max u v}} (Heq : α → β) (x : get_m α)

variables {i : α} {f : unsigned → get_m α}
variables {f' : β' → unsigned → get_m (γ ⊕ β')}
variables {g' : γ → get_m α} {j : β'}

@[simp] lemma get_m.up.eqn_1 : get_m.up Heq (get_m.pure i) = get_m.pure (Heq i) := rfl
@[simp] lemma get_m.up.eqn_2 : get_m.up Heq (get_m.fail) = get_m.fail := rfl
@[simp] lemma get_m.up.eqn_3 : get_m.up Heq (get_m.read f) = get_m.read (λ w, get_m.up Heq (f w)) := rfl
@[simp] lemma get_m.up.eqn_4 :
  get_m.up Heq (get_m.loop f' g' j) =
  get_m.loop
    (λ a b, get_m.up (sum_ulift γ β') (f' (down.{v} a) b))
    (λ w, get_m.up Heq (g' $ down w))
    (up.{v} j) := rfl

end eqns

def put_m.up {α : Type u} {β : Type v} (Heq : α → β) : put_m' α → put_m' β
| (put_m'.pure x) := put_m'.pure $ Heq x
| (put_m'.write w f) := put_m'.write w $ λ u, put_m.up $ f u

instance : liftable1 put_m'.{u} put_m'.{v} :=
{ up := λ α β (eq : α ≃ β) x, put_m.up eq x
, down := λ α β (eq : α ≃ β) x, put_m.up eq.symm x
, down_up := by intros; induction x; simp [put_m.up,*]
, up_down := by intros; induction x; simp [put_m.up,*]  }

open pliftable (up')

lemma up_bind {α β : Type u} {β' : Type (max u v)} (x : get_m α) (g : α → get_m β) (f : β → β') :
  (x >>= g).up f = x.up up.{v} >>= (λ i : ulift α, (g $ down i).up f) :=
begin
  dsimp [(>>=)],
  induction x generalizing f g; try { refl };
    simp [get_m.bind,*]
end

lemma equiv_bind {m} [monad m] [is_lawful_monad m] {α α' β}
  (Heq : α ≃ α') (x : m α) (f : α → m β) :
  x >>= f = (Heq <$> x) >>= f ∘ Heq.symm :=
by simp [(∘)] with functor_norm

def sum.map {α α' β β'} (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β'
| (sum.inr x) := sum.inr $ g x
| (sum.inl x) := sum.inl $ f x

def equiv.ulift_sum {α β} : (ulift $ α ⊕ β) ≃ (ulift α ⊕ ulift β) :=
{ to_fun := λ x, sum.map up up (down x),
  inv_fun := λ x, up $ sum.map down down x,
  right_inv := by intro; casesm* [_ ⊕ _,ulift _]; refl,
  left_inv := by intro; casesm* [_ ⊕ _,ulift _]; refl }

lemma map_get_m_up {α : Type u} {β γ} (x : get_m α) (f : α → β) (g : β → γ) :
  g <$> get_m.up f x = get_m.up (g ∘ f) x :=
begin
  dsimp [(<$>)],
  induction x; simp [get_m.map,*]; refl,
end

lemma up_read_write {α : Type u} {α' : Type (max u v)} (x : get_m α) (y : put_m) (f : α ≃ α') :
  x.up f -<< up' y = liftable1.up f (x -<< y) :=
begin
  dsimp [up',liftable1.up],
  induction y generalizing x f,
  cases x; simp; refl,
  cases x; simp [up',liftable.up',liftable1.up,read_write,put_m.up,*], refl, refl, refl,
  rw [read_write,← y_ih,up_bind],
    apply congr,
    { apply congr_arg, rw equiv_bind (@equiv.ulift_sum.{u u v v v} x_α x_β) ,
      congr,
      { rw map_get_m_up, congr, ext, cases x; refl },
      simp [(∘)], ext, cases x;
      dsimp [equiv.ulift_sum,sum.map], refl,
      cases x, refl, apply_instance },
    congr,
end

lemma up_read_write' {α : Type u} {α' : Type (max u v)}
  {x : get_m α} {y : put_m} (f : α → α') (f' : α ≃ α')
  (h : ∀ i, f i = f' i) :
  x.up f -<< up' y = liftable1.up f' (x -<< y) :=
begin
  rw ← up_read_write, congr, ext, apply h
end
