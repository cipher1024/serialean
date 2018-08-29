
import tactic
import category.liftable
import category.basic
import category.serial
import liftable
import medium

universes u v

-- @[reducible]
-- def put_m' (β : Type) (α : Type u) := α → state (ulift.{u} β) punit
-- @[reducible]
-- def get_m' (β : Type) := λ (α : Type u), state_t (ulift β) option α

def serial_inverse {α : Type u} (encode : α → put_m) (decode : get_m α) : Prop :=
∀ w, decode -<< encode w = pure w

-- structure medium :=
--   (rep : Type)
--   (encode_word : put_m' rep unsigned)
--   (decode_word : get_m' rep unsigned)
--   (inverse : serial_inverse encode_word decode_word)

-- def medium.state (m : medium) := ulift m.rep

-- @[reducible]
-- def put_m (m : medium) := put_m' m.rep
-- @[reducible]
-- def get_m (m : medium) := get_m' m.rep

-- instance (m : medium) : monad (get_m m) :=
-- by apply_instance

-- instance (m : medium) : is_lawful_monad (get_m m) :=
-- by apply_instance

-- instance (m : medium) : liftable1 (get_m.{u} m) (get_m.{v} m) :=
-- by apply_instance

class serial (α : Type u) :=
  (encode : α → put_m.{u})
  (decode : get_m α)
  (correctness : serial_inverse encode decode)

export serial (encode decode)

structure serializer (α : Type u) (β : Type u) :=
intl ::
(encoder : α → put_m.{u})
(decoder : get_m β)

def valid_serializer {α} (x : serializer α α) :=
serial_inverse
      (serializer.encoder x)
      (serializer.decoder x)

def apply {α β} : α → (α → β) → β :=
λ x (f : α → β), f x

lemma serializer.eq {α β} (x y : serializer α β)
  (h : x.encoder = y.encoder)
  (h' : x.decoder = y.decoder) :
  x = y :=
by cases x; cases y; congr; assumption

namespace serializer.seq

variables {α : Type u} {i j : Type u}
variables (x : serializer α (i → j))
variables (y : serializer α i)

def encoder := λ (k : α), x.encoder k >> y.encoder k
def decoder := x.decoder <*> y.decoder

end serializer.seq

instance {α : Type u} : applicative (serializer.{u} α) :=
{ pure := λ i x, { encoder := λ _, return punit.star, decoder := pure x }
, seq := λ i j x y,
  { encoder := serializer.seq.encoder x y
  , decoder := serializer.seq.decoder x y } }

section lawful_applicative

variables {α β : Type u} {σ : Type u}

@[simp]
lemma decoder_pure (x : β) :
  (pure x : serializer σ β).decoder = pure x := rfl

@[simp]
lemma decoder_map (f : α → β) (x : serializer σ α) :
  (f <$> x).decoder = f <$> x.decoder := rfl

@[simp]
lemma decoder_seq (f : serializer σ (α → β)) (x : serializer σ α) :
  (f <*> x).decoder = f.decoder <*> x.decoder := rfl

@[simp]
lemma encoder_pure (x : β) (w : σ) :
  (pure x : serializer σ β).encoder w = pure punit.star := rfl

@[simp]
lemma encoder_map (f : α → β) (w : σ) (x : serializer σ α) :
  (f <$> x : serializer σ β).encoder w = x.encoder w := rfl

@[simp]
lemma encoder_seq (f : serializer σ (α → β)) (x : serializer σ α) (w : σ) :
  (f <*> x : serializer σ β).encoder w = f.encoder w >> x.encoder w := rfl

end lawful_applicative

instance {α} : is_lawful_functor (serializer.{u} α) :=
by refine { .. }; intros; apply serializer.eq; try { ext }; simp [map_map]

instance {α} : is_lawful_applicative (serializer.{u} α) :=
by{  constructor; intros; apply serializer.eq; try { ext };
     simp [(>>),pure_seq_eq_map,seq_assoc,bind_assoc],  }

def ser_field {α β} [serial β] (f : α → β) : serializer α β :=
{ encoder := λ x, encode (f x)
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

def there_and_back_again
  (y : serializer γ α) (w : γ) : option α :=
y.decoder -<< y.encoder w

-- @[simp]
-- lemma decoder_pure (m : medium)
--   (x : α) :
--   (pure x : serializer γ α).decoder m = pure x := rfl

-- @[simp]
-- lemma decoder_seq (m : medium)
--   (f : serializer σ (α → β)) (x : serializer σ α) :
--   (f <*> x).decoder m = apply <$> x.decoder m <*> f.decoder m := rfl

-- @[simp]
-- lemma encoder_seq (m : medium)
--   (f : serializer σ $ α → β) (x : serializer σ α) (w : σ) :
--   (f <*> x).encoder m w = f.encoder m w >> x.encoder m w := rfl

-- @[simp]
-- lemma decoder_map (m : medium)
--   (f : α → β) (x : serializer σ α) :
--   (f <$> x).decoder m = f <$> x.decoder m :=
-- by rw [← pure_seq_eq_map]; simp; simp [(∘),apply] with functor_norm

-- @[simp]
-- lemma encoder_map (m : medium)
--   (f : α → β) (x : serializer σ α) :
--   (f <$> x).encoder m = x.encoder m :=
-- by { cases x, ext, simp! [functor.map,serializer.seq.encoder,(>>)] }

-- @[simp]
-- lemma encoder_field [serial β] (m : medium)
--   (f : α → β) :
--   (ser_field f).encoder m = λ w, encode _ m (f w) := rfl

-- @[simp]
-- lemma decoder_field [serial β] (m : medium)
--   (f : α → β) :
--   (ser_field f).decoder m = decode β m := rfl

-- @[simp]
-- lemma encode_decode_cancel [serial α] (m : medium)
--   (x : α) (f : α → get_m m β) :
-- do { monad_state.lift (encode α m x),
--      decode α m >>= f } = f x :=
-- by rw [← bind_assoc];
--      apply bind_eq_of_eq_pure;
--      [ apply serial.correctness,
--        refl ]

-- @[simp]
-- lemma lift_encoder_bind {β}
--   (encoder : put_m α) (rest : state m.state β) (x : α) :
--   (monad_state.lift $ do { encoder x, rest } : get_m m _) =
--   do { monad_state.lift (encoder x), monad_state.lift rest }  :=
-- is_lawful_monad_state.lift_bind _ _

lemma encode_decode_seq [serial α]
  (x : serializer γ (α → β)) (f : α → β) (y : γ → α) (w : γ) (w' : β)
  (h' : there_and_back_again x w = pure f)
  (h  : w' = f (y w)) :
  there_and_back_again (x <*> ser_field y) w = pure w' :=
by { simp [there_and_back_again,(>>),seq_eq_bind_map] at *,
     rw [read_write_mono _ _ _ _ _ h',map_read_write],
     rw [ser_field,serial.correctness], subst w', refl }

@[simp]
lemma encode_decode_map [serial α]
  (f : α → β) (y : γ → α) (w : γ) :
  there_and_back_again (f <$> ser_field y) w = pure (f $ y w) :=
by rw [← pure_seq_eq_map,encode_decode_seq]; refl

@[simp]
lemma encode_decode_pure (x : β) (w : γ) :
  there_and_back_again (pure x) w =
  pure x := rfl

-- @[simp]
-- lemma encode_decode_map [serial α] (m : medium)
--   (f : α → β) (y : γ → α) (w : γ) :
--   there_and_back_again m (f <$> ser_field y) w =
--   pure (f $ y w) :=
-- by rw [← pure_seq_eq_map]; simp

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
  ∀ (w : α), there_and_back_again y w = pure w :=
by { simp [valid_serializer,serial_inverse],
     repeat { rw forall_congr, intro }, refl }

-- lemma valid_serializer_seq {γ α β : Type*} {ω} (m : medium ω) (σ₀ : ω)
--   (x : serializer γ (α → β)) (y : serializer γ α) (w : γ) :
--   valid_serializer (x <*> y) := _
open ulift

def ulift.encode [serial α] (w : ulift.{v} α) : put_m :=
liftable1.up equiv.punit_equiv_punit (encode (down w))

def ulift.decode [serial α] : get_m (ulift α) :=
get_m.up ulift.up (decode α)

instance [serial α] : serial (ulift.{v u} α) :=
{ encode := ulift.encode
, decode := ulift.decode
, correctness :=
  by { introv _, simp [ulift.encode,ulift.decode],
       rw up_read_write' _ equiv.ulift.symm,
       rw [serial.correctness], cases w, refl,
       intro, refl } }

def ser_field' {α β} [serial β] (f : α → β) : serializer.{max u v} α (ulift.{v} β) :=
ser_field (up ∘ f)

instance : serial unsigned :=
{ encode := λ w, put_m'.write w put_m'.pure
, decode := get_m.read get_m.pure
, correctness := by introv w; refl }

def of_serializer {α} (s : serializer α α) (h : ∀ w, there_and_back_again s w = pure w) : serial α :=
{ encode := s.encoder
, decode := s.decoder
, correctness := @h }

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
of_serializer (point.mk <$> ser_field point.x <*> ser_field point.y)
begin
  intro,
  apply encode_decode_seq,
  apply encode_decode_map,
  cases w, refl
end

open ulift

def prod.mk' {β : Type v} : ulift α → ulift β → (α × β)
| ⟨ x ⟩ ⟨ y ⟩ := (x,y)

instance {β : Type v} [serial α] [serial β] : serial (α × β) :=
of_serializer (prod.mk' <$> ser_field' prod.fst <*> ser_field'.{v u} prod.snd)
begin
  intro,
  apply encode_decode_seq,
  apply encode_decode_map,
  cases w, refl
end

attribute [simp] serial.correctness

/- Todo:
* sum
* list
* nat
-/
