
import tactic
import logic.basic

universes u

inductive put_m_intl (α : Type u)
| pure : α → put_m_intl
| write : unsigned → (unit → put_m_intl) → put_m_intl

def put_m_intl.bind {α β} : put_m_intl α → (α → put_m_intl β) → put_m_intl β
| (put_m_intl.pure x)   f := f x
| (put_m_intl.write w f) g := put_m_intl.write w $ λ u, put_m_intl.bind (f u) g

instance : monad put_m_intl :=
{ pure := λ α, put_m_intl.pure
, bind := @put_m_intl.bind }

instance : is_lawful_monad put_m_intl :=
sorry

def put_m := put_m_intl punit

def put_m.eval : put_m → list unsigned
| (put_m_intl.pure x) := []
| (put_m_intl.write w f) := w :: put_m.eval (f punit.star)

inductive get_m : Type u → Type (u+1)
| fail {α} : get_m α
| pure {α} : α → get_m α
| read {α} : (unsigned → get_m α) → get_m α
| loop {α β γ : Type u} : β → (β → unsigned → get_m (α ⊕ β)) → (α → get_m γ) → get_m γ

def get_m.bind : Π {α β}, get_m α → (α → get_m β) → get_m β
| _ _ (get_m.fail) _ := get_m.fail
| _ _ (get_m.pure x)   f := f x
| _ _ (get_m.read f) g := get_m.read $ λ w, get_m.bind (f w) g
| _ _ (get_m.loop x₀ f g) h := get_m.loop x₀ f (λ r, get_m.bind (g r) h)

instance : monad get_m :=
{ pure := λ α, get_m.pure
, bind := @get_m.bind }

instance : is_lawful_monad get_m :=
sorry

def get_m.eval {α} : list unsigned → get_m α → option α
| [] (get_m.pure x) := pure x
| [] _  := none
| (w :: ws) (get_m.read f) := get_m.eval ws (f w)
| (w :: ws) (get_m.loop x₀ f g) :=
  get_m.eval ws $
  do { r ← f x₀ w,
       match r with
       | (sum.inr x₁) := get_m.loop x₁ f g
       | (sum.inl r) := g r
       end }
| (w :: ws) _ := none


def read_write : Π {α}, get_m α → put_m → option α
| ._ (get_m.pure x) (put_m_intl.pure _) := some x
| _ _ (put_m_intl.pure _) := none
| ._ (get_m.read f) (put_m_intl.write w g) := read_write (f w) (g punit.star)
| _ (@get_m.loop α β γ x₀ f g) (put_m_intl.write w h) :=
  read_write
    (do r ← f x₀ w,
       match r with
       | (sum.inr x₁) := get_m.loop x₁ f g
       | (sum.inl r) := g r
       end )
    (h punit.star)
| _ _ (put_m_intl.write w g) := none

def read_write' : Π {α}, get_m α → put_m → option (α × put_m)
| _ (get_m.read f) (put_m_intl.write w g) := read_write' (f w) (g punit.star)
| _ (@get_m.loop α β γ x₀ f g) (put_m_intl.write w h) :=
  read_write'
    (do r ← f x₀ w,
       match r with
       | (sum.inr x₁) := get_m.loop x₁ f g
       | (sum.inl r) := g r
       end )
    (h punit.star)
-- | _ (get_m.pure x) m@(put_m_intl.write w g) := some (x,m)
| _ (get_m.pure x) m := some (x,m)
| _ _ (put_m_intl.pure _) := none
| _ (get_m.fail) (put_m_intl.write _ _) := none
-- | _ _ m := none

lemma read_read_write_write {α} (x : get_m α) (m : put_m) (i : α) :
  read_write x m = some i ↔ read_write' x m = some (i,pure punit.star) :=
begin
  induction m generalizing x;
  cases x; casesm* punit; simp [read_write,read_write',prod.ext_iff,pure,*],
  apply iff_of_eq, congr,
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
--   agree x (get_m.read f) (put_m_intl.write w g) m
-- | loop_write {α} (x : α) {β γ} (σ₀ σ₁ : β) (w : unsigned)
--   (f : β → unsigned → get_m (γ ⊕ β)) (f' : γ → get_m α)
--   (g : punit → put_m) (m m' : put_m) :
--   agree (sum.inr σ₁) (f σ₀ w) (g punit.star) m' →
--   agree x (get_m.loop σ₁ f f') m' m →
--   agree x (get_m.loop σ₀ f f') (put_m_intl.write w g) m
-- | loop_exit_write {α} (x : α) {β γ} (σ₀ : β) (r : γ) (w : unsigned)
--   (f : β → unsigned → get_m (γ ⊕ β)) (f' : γ → get_m α)
--   (g : punit → put_m) (m m' : put_m) :
--   agree (sum.inl r) (f σ₀ w) (g punit.star) m' →
--   agree x (f' r) m' m →
--   agree x (get_m.loop σ₀ f f') (put_m_intl.write w g) m

-- lemma agree_spec {α} (g : get_m α) (m : put_m) (x : α) :
--   agree x g m (put_m_intl.pure punit.star) ↔ g -<< m = some x :=
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
  (get_m.loop i body f₀ >>= f₁) -<<< put_m_intl.write w m =
  (body i w >>= read_write'._match_1 _ _ _ body f₀ >>= f₁) -<<< m punit.star :=
begin
  rw bind_assoc,
  simp [(>>=),get_m.bind,read_write'],
  congr, ext, cases x; simp [read_write'._match_1]; refl,
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
  cases x₀; simp [(>>=),put_m_intl.bind,read_write',pure_read_write],
  { intros, subst x₂, tauto },
  cases x₀; simp [(>>=),put_m_intl.bind,read_write'],
  { intros, substs x₂ i, split; refl },
  { apply x₁_ih, },
  { apply x₁_ih, },
end

lemma read_write_weakening {α}
  (x₀ x₁ : put_m) (y₀ y₁ : get_m α)
  (h : y₀ -<<< x₀ = y₁ -<<< x₁) :
  y₀ -<< x₀ = y₁ -<< x₁ :=
begin
  suffices : ∀ z, y₀ -<< x₀ = some z ↔ y₁ -<< x₁ = some z,
  { cases y₁ -<< x₁, cases y₀ -<< x₀, refl,
    symmetry, rw ← this, rw this, },
  intro, simp [read_read_write_write,h],
end

lemma read_write_mono' {α β} (i : α)
      (x₀ : get_m α) (f₀ : α → get_m β)
      (x₁ x₂ : put_m)
      (h : x₀ -<<< x₁ = some (i,x₂)) :
  (x₀ >>= f₀) -<<< x₁ = f₀ i -<<< x₂ :=
begin
  induction x₁ generalizing x₀;
    try { cases x₀; cases h },
  { simp [(>>=),read_write',get_m.bind] },
  { cases x₀; try { cases h },
    simp [(>>=),read_write',get_m.bind] at h ⊢,
    simp [(>>=),read_write',get_m.bind] at h ⊢,
    { apply x₁_ih, assumption },
    simp [read_write'] at h,
    rw [read_write_loop_bind,x₁_ih _ _ h], }
end

lemma read_write_mono {α β} (i : α)
      (x₀ : get_m α) (f₀ : α → get_m β)
      (x₁ : put_m) (f₁ : punit → put_m)
      (h : x₀ -<< x₁ = some i) :
  (x₀ >>= f₀) -<< (x₁ >>= f₁) = f₀ i -<< f₁ punit.star :=
begin
  apply read_write_weakening,
  apply read_write_mono',
  rw [read_read_write_write] at h,
  replace h := read_write_left_overs_bind f₁ _ _ _ _ h,
  simp [h],
end

lemma read_write_eq_eval_eval {α}
      (x₀ : get_m α) (x₁ : put_m)  :
  x₀ -<< x₁ = x₀.eval x₁.eval :=
begin
  induction x₁ generalizing x₀; cases x₀; try { refl },
  simp! [*,read_write],
  simp! [*,read_write], refl,
end
