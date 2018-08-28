
import tactic state
import category.liftable
import liftable

universes u v

@[reducible]
def put_m' (β : Type) (α : Type u) := α → state (ulift.{u} β) punit
@[reducible]
def get_m' (β : Type) := λ (α : Type u), state_t (ulift β) option α

def serial_inverse {α} {β : Type u} (encode : put_m' α β) (decode : get_m' α β) : Prop :=
∀ w, monad_state.lift (encode w) >> decode = pure w

structure medium :=
  (rep : Type)
  (encode_word : put_m' rep unsigned)
  (decode_word : get_m' rep unsigned)
  (inverse : serial_inverse encode_word decode_word)

def medium.state (m : medium) := ulift m.rep

@[reducible]
def put_m (m : medium) := put_m' m.rep
@[reducible]
def get_m (m : medium) := get_m' m.rep

instance (m : medium) : monad (get_m m) :=
by apply_instance

instance (m : medium) : is_lawful_monad (get_m m) :=
by apply_instance

instance (m : medium) : liftable1 (get_m.{u} m) (get_m.{v} m) :=
by apply_instance

class serial (α : Type u) :=
  (encode : Π m : medium, put_m m α)
  (decode : Π m : medium, get_m m α)
  (correctness : ∀ m : medium, serial_inverse (encode m) (decode m))

export serial (encode decode)

structure serializer (α β : Type u) :=
intl ::
(encoder : Π m : medium, put_m m α)
(decoder : Π m : medium, get_m m β)

def valid_serializer {α} (x : serializer α α) :=
∀ m : medium, serial_inverse
      (serializer.encoder x m)
      (serializer.decoder x m)

def apply {α β} : α → (α → β) → β :=
λ x (f : α → β), f x

namespace serializer.seq

variables {α i j : Type u}
variables (x : serializer α (i → j))
variables (y : serializer α i)

def encoder (m : medium) := λ (k : α), x.encoder m k >> y.encoder m k
def decoder (m : medium) := apply <$> y.decoder m <*> x.decoder m

end serializer.seq

instance {α : Type u} : applicative (serializer α) :=
{ pure := λ i x, { encoder := λ _ _, return punit.star, decoder := λ k, pure x }
, seq := λ i j x y,
  { encoder := serializer.seq.encoder x y
  , decoder := serializer.seq.decoder x y } }

instance {α} : is_lawful_applicative (serializer α) :=
begin
  refine { .. }; dsimp; intros; casesm* serializer _ _;
    simp [serializer.seq.encoder,serializer.seq.decoder];
    split; ext,
  all_goals
  { simp [serializer.seq.encoder,serializer.seq.decoder,return,(>>),pure_bind,bind_pure,bind_assoc,pure_star,apply] with functor_norm },
end

def of_serializer {α} (s : serializer α α) (h : valid_serializer s) : serial α :=
{ encode := s.encoder
, decode := s.decoder
, correctness := @h }

def ser_field {α β} [serial β] (f : α → β) : serializer α β :=
{ encoder := λ inst x, @encode _ _ inst (f x)
, decoder := @decode _ _ }

-- @[simp]
-- lemma encoder_seq {γ α β : Type*} {ω} [medium ω]
--   (x : serializer γ (α → β)) (y : serializer γ α) (w : γ) :
--   (x <*> y).encoder ω w = (x.encoder ω w >> y.encoder ω w : state _ _) :=
-- rfl

-- @[simp]
-- lemma encoder_map {γ α β : Type*} {ω} [medium ω]
--   (x : α → β) (y : serializer γ α) (w : γ) :
--   (x <$> y).encoder ω w = (y.encoder ω w : state _ _) :=
-- by cases y; simp [functor.map,serializer.seq.encoder,(>>),pure_bind]

-- @[simp]
-- lemma encoder_field {α β : Type*} [serial β] {ω} [medium ω]
--   (x : α → β) (w : α) :
--   (ser_field x).encoder ω w = encode _ _ (x w) :=
-- rfl

open function

variables {α β σ γ : Type u} {ω : Type}

def there_and_back_again (m : medium)
  (y : serializer γ α) (w : γ) : get_m m α :=
monad_state.lift (y.encoder m w) >> y.decoder m

@[simp]
lemma decoder_pure (m : medium)
  (x : α) :
  (pure x : serializer γ α).decoder m = pure x := rfl

@[simp]
lemma decoder_seq (m : medium)
  (f : serializer σ (α → β)) (x : serializer σ α) :
  (f <*> x).decoder m = apply <$> x.decoder m <*> f.decoder m := rfl

@[simp]
lemma encoder_seq (m : medium)
  (f : serializer σ $ α → β) (x : serializer σ α) (w : σ) :
  (f <*> x).encoder m w = f.encoder m w >> x.encoder m w := rfl

@[simp]
lemma decoder_map (m : medium)
  (f : α → β) (x : serializer σ α) :
  (f <$> x).decoder m = f <$> x.decoder m :=
by rw [← pure_seq_eq_map]; simp; simp [(∘),apply] with functor_norm

@[simp]
lemma encoder_map (m : medium)
  (f : α → β) (x : serializer σ α) :
  (f <$> x).encoder m = x.encoder m :=
by { cases x, ext, simp! [functor.map,serializer.seq.encoder,(>>)] }

@[simp]
lemma encoder_field [serial β] (m : medium)
  (f : α → β) :
  (ser_field f).encoder m = λ w, encode _ m (f w) := rfl

@[simp]
lemma decoder_field [serial β] (m : medium)
  (f : α → β) :
  (ser_field f).decoder m = decode β m := rfl

@[simp]
lemma encode_decode_cancel [serial α] (m : medium)
  (x : α) (f : α → get_m m β) :
do { monad_state.lift (encode α m x),
     decode α m >>= f } = f x :=
by rw [← bind_assoc];
     apply bind_eq_of_eq_pure;
     [ apply serial.correctness,
       refl ]

@[simp]
lemma lift_encoder_bind {β} (m : medium)
  (encoder : put_m m α) (rest : state m.state β) (x : α) :
  (monad_state.lift $ do { encoder x, rest } : get_m m _) =
  do { monad_state.lift (encoder x), monad_state.lift rest }  :=
is_lawful_monad_state.lift_bind _ _

@[simp]
lemma encode_decode_seq [serial α] (m : medium)
  (x : serializer γ (α → β)) (y : γ → α) (w : γ) :
  there_and_back_again m (x <*> ser_field y) w =
  there_and_back_again m x w <*> pure (y w) :=
by simp [there_and_back_again,apply] with functor_norm

@[simp]
lemma encode_decode_pure (m : medium) (x : β) (w : γ) :
  there_and_back_again m (pure x) w =
  pure x := rfl

@[simp]
lemma encode_decode_map [serial α] (m : medium)
  (f : α → β) (y : γ → α) (w : γ) :
  there_and_back_again m (f <$> ser_field y) w =
  pure (f $ y w) :=
by rw [← pure_seq_eq_map]; simp

-- @[simp]
-- lemma encode_decode_map {γ α β : Type*} {ω} (m : medium ω) (σ₀ : ω)
--   (x : α → β) (y : serializer γ α) (w : γ) :
--   there_and_back_again m (x <$> y) w (σ₀ : ω) =
--   prod.map x id <$> there_and_back_again m y w σ₀ :=
-- begin
--   simp [there_and_back_again,serializer.seq.decoder,serializer.seq.encoder,(>>)] with functor_norm,
--   congr' 1, ext z; cases z; simp [prod.map,const],
-- end

lemma valid_serializer_of_there_and_back_again
      {α : Type*} (y : serializer α α) :
  valid_serializer y ↔
  ∀ (m : medium) (w : α), there_and_back_again m y w = pure w :=
by { simp [valid_serializer,serial_inverse],
     repeat { rw forall_congr, intro }, refl }

-- lemma valid_serializer_seq {γ α β : Type*} {ω} (m : medium ω) (σ₀ : ω)
--   (x : serializer γ (α → β)) (y : serializer γ α) (w : γ) :
--   valid_serializer (x <*> y) := _
open ulift

def ulift.encode [serial α] (m : medium) (w : ulift.{v} α) : state (ulift $ medium.rep m) punit :=
liftable1.up equiv.punit_equiv_punit (encode _ m (down w))

def ulift.decode [serial α] (m : medium) : get_m m (ulift α) :=
liftable1.down equiv.ulift (decode α m)

instance [serial α] : serial (ulift α) :=
{ encode := ulift.encode
, decode := ulift.decode
, correctness := by { introv _, simp [ulift.encode], rw monad_state_lift_liftable_up, simp [serial_inverse,monad_state_lift_liftable_up], rw monad_state_lift_liftable_up, apply medium.inverse } }

instance : serial unsigned :=
{ encode := λ γ inst w, @medium.encode_word γ inst ⟨w⟩
, decode := λ γ inst, ulift.down <$> @medium.decode_word γ inst
, correctness := by { introv w, simp, rw medium.inverse, refl } }

structure point :=
(x y : unsigned)

section
open tactic interactive interactive.types tactic.interactive (casesm trivial)

meta def mk_serializer (s : parse texpr) : tactic unit :=
do `(serial %%t) ← tactic.target,
   refine ``(of_serializer %%s _),
   `[simp [valid_serializer_of_there_and_back_again,serial_inverse], intros],
   casesm none [to_pexpr t],
   reflexivity <|> trivial

run_cmd add_interactive [`mk_serializer]

end

instance : serial point :=
by mk_serializer (point.mk <$> ser_field point.x <*> ser_field point.y)
open ulift

def prod.mk' {β : Type v} : ulift α → ulift β → (α × β) := _

instance {β : Type v} [serial α] [serial β] : serial (α × β) :=
by mk_serializer (prod.mk' <$> ser_field (up prod.fst) <*> ser_field (up prod.snd))

#check bind_pure
attribute [simp] serial.correctness

variables {m : Type* → Type*} [monad m]

variables {α β γ φ : Type u}

def compose (x : serial β γ) (y : serial α β) : serial α γ :=
{ encode := λ i z, x.encode (y.encode i _) z
, decode := _ -- y.decode <=< x.decode
, correctness := by intros; simp [monad.pipe] }

local infixr ` ∘ ` := compose

variables (x : serial α β) (y : serial β γ) (z : serial γ φ)

lemma compose_assoc :
  z ∘ (y ∘ x) = (z ∘ y) ∘ x :=
begin
  casesm* serial _ _, dsimp [compose], congr' 1,
  ext, simp [(<=<),bind_assoc],
end

def serial_unsigned : serial unsigned (list unsigned) :=
{ encode := list.ret
, decode := λ xs, list.nth xs 0
, correctness := by intros; simp!; refl }

def serial_pair (x : serial α (list unsigned)) (y : serial β (list unsigned)) :
  serial (α × β) (list unsigned) :=
{ encode := λ i, x.encode i.1 ++ y.encode i.2
, decode := _
, correctness := _}

def serial_sum (x : serial α (list unsigned)) (y : serial β (list unsigned)) :
  serial (α ⊕ β) (list unsigned) :=
sorry -- implementation please!

#eval serial_unsigned.encode 3
#eval (serial_pair serial_unsigned serial_unsigned).encode (31,17)
#eval (serial_sum serial_unsigned serial_unsigned).encode (sum.inl 31)
