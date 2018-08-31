
import tactic state
import tactic.monotonicity
import tactic.norm_num
import category.liftable
import category.basic
import category.serial
import liftable
import medium

universes u v w

def serial_inverse {α : Type u} (encode : α → put_m) (decode : get_m α) : Prop :=
∀ w, decode -<< encode w = pure w

class serial (α : Type u) :=
  (encode : α → put_m.{u})
  (decode : get_m α)
  (correctness : ∀ w, decode -<< encode w = pure w)

class serial1 (f : Type u → Type v) :=
  (encode : Π {α} [serial α], f α → put_m.{v})
  (decode : Π {α} [serial α], get_m (f α))
  (correctness : ∀ {α} [serial α] (w : f α), decode -<< encode w = pure w)

instance serial.serial1 {f α} [serial1 f] [serial α] : serial (f α) :=
{ encode := λ x, serial1.encode x,
  decode := serial1.decode f,
  correctness := serial1.correctness }

class serial2 (f : Type u → Type v → Type w) :=
  (encode : Π {α β} [serial α] [serial β], f α β → put_m.{w})
  (decode : Π {α β} [serial α] [serial β], get_m (f α β))
  (correctness : ∀ {α β} [serial α] [serial β] (w : f α β), decode -<< encode w = pure w)

instance serial.serial2 {f α β} [serial2 f] [serial α] [serial β] : serial (f α β) :=
{ encode := λ x, serial2.encode x,
  decode := serial2.decode f,
  correctness := serial2.correctness }

instance serial1.serial2 {f α} [serial2 f] [serial α] : serial1 (f α) :=
{ encode := λ β inst x, @serial2.encode _ _ α β _ inst x,
  decode := λ β inst, @serial2.decode f _ α β _ inst,
  correctness := λ β inst, @serial2.correctness _ _ α β _ inst }

export serial (encode decode)

structure serializer (α : Type u) (β : Type u) :=
intl ::
(encoder : α → put_m.{u})
(decoder : get_m β)

def valid_serializer {α} (x : serializer α α) :=
serial_inverse
      (serializer.encoder x)
      (serializer.decoder x)

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

open function

variables {α β σ γ : Type u} {ω : Type}

def there_and_back_again
  (y : serializer γ α) (w : γ) : option α :=
y.decoder -<< y.encoder w

lemma there_and_back_again_seq [serial α]
  (x : serializer γ (α → β)) (f : α → β) (y : γ → α) (w : γ) (w' : β)
  (h' : there_and_back_again x w = pure f)
  (h  : w' = f (y w)) :
  there_and_back_again (x <*> ser_field y) w = pure w' :=
by { simp [there_and_back_again,(>>),seq_eq_bind_map] at *,
     rw [read_write_mono h',map_read_write],
     rw [ser_field,serial.correctness], subst w', refl }

lemma encode_decode_bind [serial α]
  (f : α → get_m β) (f' : punit → put_m) (w : α) :
  (decode α >>= f) -<< (encode w >>= f') = f w -<< f' punit.star :=
by { rw [read_write_mono]; rw serial.correctness; refl }

lemma encode_decode_bind' [serial α]
  (f : α → get_m β) (w : α) :
  (decode α >>= f) -<< (encode w) = f w -<< pure punit.star :=
by { rw [read_write_mono_left]; rw serial.correctness; refl }

lemma encode_decode_pure
  (w w' : α) (u : punit) :
  (pure w) -<< (pure u) = pure w' ↔ w = w' :=
by split; intro h; cases h; refl

@[simp]
lemma there_and_back_again_map [serial α]
  (f : α → β) (y : γ → α) (w : γ) :
  there_and_back_again (f <$> ser_field y) w = pure (f $ y w) :=
by rw [← pure_seq_eq_map,there_and_back_again_seq]; refl

@[simp]
lemma there_and_back_again_pure (x : β) (w : γ) :
  there_and_back_again (pure x) w =
  pure x := rfl

lemma valid_serializer_of_there_and_back_again
      {α : Type*} (y : serializer α α) :
  valid_serializer y ↔
  ∀ (w : α), there_and_back_again y w = pure w :=
by { simp [valid_serializer,serial_inverse],
     repeat { rw forall_congr, intro }, refl }

open ulift

protected def ulift.encode [serial α] (w : ulift.{v} α) : put_m :=
liftable1.up equiv.punit_equiv_punit (encode (down w))

protected def ulift.decode [serial α] : get_m (ulift α) :=
get_m.up ulift.up (decode α)

instance [serial α] : serial (ulift.{v u} α) :=
{ encode := ulift.encode
, decode := ulift.decode
, correctness :=
  by { introv, simp [ulift.encode,ulift.decode],
       rw up_read_write' _ equiv.ulift.symm,
       rw [serial.correctness], cases w, refl,
       intro, refl } }

def ser_field' {α β} [serial β] (f : α → β) : serializer.{max u v} α (ulift.{v} β) :=
ser_field (up ∘ f)

instance : serial unsigned :=
{ encode := λ w, put_m'.write w put_m'.pure
, decode := get_m.read get_m.pure
, correctness := by introv; refl }

def of_serializer {α} (s : serializer α α) (h : ∀ w, there_and_back_again s w = pure w) : serial α :=
{ encode := s.encoder
, decode := s.decoder
, correctness := @h }

def of_serializer₁ {f : Type u → Type v}
  (s : Π α [serial α], serializer (f α) (f α))
  (h : ∀ α [serial α] w, there_and_back_again (s α) w = pure w) : serial1 f :=
{ encode := λ α inst, (@s α inst).encoder
, decode := λ α inst, (@s α inst).decoder
, correctness := @h }

def of_serializer₂ {f : Type u → Type v → Type w}
  (s : Π α β [serial α] [serial β], serializer (f α β) (f α β))
  (h : ∀ α β [serial α] [serial β] w, there_and_back_again (s α β) w = pure w) : serial2 f :=
{ encode := λ α β inst inst', (@s α β inst inst').encoder
, decode := λ α β inst inst', (@s α β inst inst').decoder
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
  apply there_and_back_again_seq,
  apply there_and_back_again_map,
  cases w, refl
end

open ulift

def prod.mk' {β : Type v} : ulift α → ulift β → (α × β)
| ⟨ x ⟩ ⟨ y ⟩ := (x,y)

instance : serial2 prod.{u v} :=
of_serializer₂ (λ α β, by introsI; exact prod.mk' <$> ser_field' prod.fst <*> ser_field'.{v u} prod.snd)
begin
  intros,
  apply there_and_back_again_seq,
  apply there_and_back_again_map,
  cases w, refl
end

def write_word (w : unsigned) : put_m.{u} :=
encode (up.{u} w)

@[simp] lemma loop_read_write_word {α β γ : Type u}
  (w : unsigned) (x : α) (f : α → unsigned → get_m (β ⊕ α)) (g : β → get_m γ)
  (rest : punit → put_m) :
  get_m.loop f g x -<< (write_word w >>= rest) =
  (f x w >>= @sum.rec _ _ (λ _, get_m γ) g (get_m.loop f g)) -<< rest punit.star := rfl

@[simp] lemma loop_read_write_word' {α β γ : Type u}
  (w : unsigned) (x : α) (f : α → unsigned → get_m (β ⊕ α)) (g : β → get_m γ)  :
  get_m.loop f g x -<< (write_word w) =
  (f x w >>= @sum.rec _ _ (λ _, get_m γ) g (get_m.loop f g)) -<< pure punit.star := rfl

def read_word : get_m.{u} (ulift unsigned) :=
decode _

def select_tag' (tag : unsigned) : list (unsigned × get_m α) → get_m α
| [] := get_m.fail
| ((w,x) :: xs) := if w = tag then x else select_tag' xs

def select_tag (xs : list (unsigned × get_m α)) : get_m α :=
do w ← read_word,
   select_tag' (down w) xs

@[simp]
lemma read_write_tag_hit {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)} {y : put_m}
  (h : w = w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w' >> y) = x -<< y :=
by subst w'; simp [select_tag,(>>),read_word,write_word,encode_decode_bind,select_tag']

lemma read_write_tag_hit' {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)}
  (h : w = w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w') = x -<< pure punit.star :=
by subst w'; simp [select_tag,(>>),read_word,write_word,encode_decode_bind',select_tag']

@[simp]
lemma read_write_tag_miss {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)} {y : put_m}
  (h : w ≠ w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w' >> y) = select_tag xs -<< (write_word w' >> y) :=
by simp [select_tag,(>>),read_word,write_word,encode_decode_bind,select_tag',*]

def recursive_parser {α} : ℕ → (get_m α → get_m α) → get_m α
| 0 _ := get_m.fail
| (nat.succ n) rec_fn := rec_fn $ recursive_parser n rec_fn

lemma recursive_parser_unfold {α} (n : ℕ) (f : get_m α → get_m α) (h : 1 ≤ n) :
  recursive_parser n f = f (recursive_parser (n-1) f) :=
by cases n; [ cases h, refl ]

def sum.inl' {β : Type v} : ulift.{v} α → (α ⊕ β)
| ⟨ x ⟩ := sum.inl x

def sum.inr' {β : Type v} : ulift.{u} β → (α ⊕ β)
| ⟨ x ⟩ := sum.inr x

attribute [simp] serial.correctness

def sum.encode {α β} [serial.{u} α] [serial.{v} β] : α ⊕ β → put_m.{max u v}
| (sum.inl x) := write_word 1 >> encode (up.{v} x)
| (sum.inr x) := write_word 2 >> encode (up.{u} x)

def sum.decode {α β} [serial.{u} α] [serial.{v} β] : get_m (α ⊕ β) :=
select_tag
  [ (1,sum.inl' <$> decode _),
    (2,sum.inr' <$> decode _) ]

instance {β} [serial.{u} α] [serial.{v} β] : serial (α ⊕ β) :=
{ encode := sum.encode,
  decode := sum.decode,
  correctness :=
  by { rintro ⟨w⟩; simp [sum.encode,sum.decode,map_read_write,*], refl,
       rw read_write_tag_miss, simp [map_read_write], refl, intro h, cases h, } }

def word_sz : ℕ := unsigned_sz / 2

def nat.encode : ℕ → put_m
| n :=
let r := n / word_sz,
    w := n % word_sz in
have h : 2 * w + 1 < unsigned_sz,
  by { apply @lt_of_lt_of_le _ _ _ (2 * (w + 1)), simp [mul_add], norm_num,
       transitivity 2 * word_sz,
       { apply mul_le_mul, refl,
         { apply nat.succ_le_of_lt, apply nat.mod_lt,
           norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one] },
         apply nat.zero_le, apply nat.zero_le, },
       { rw mul_comm, apply nat.div_mul_le_self } },
if Hr : 1 ≤ r then
  have h : 2 * w < unsigned_sz,
    by { transitivity; [skip, assumption], apply nat.lt_succ_self } ,
  have h'' : word_sz > 0,
    by norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one],
  have h' : r < n,
    by { apply nat.div_lt_self, rw [nat.le_div_iff_mul_le,one_mul] at Hr,
         apply lt_of_lt_of_le h'' Hr, assumption,
         norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one] },
  do write_word ⟨2 * w, h⟩,
     nat.encode r
else
  write_word ⟨2 * w + 1, h⟩

def nat.decode_aux (coef : ℕ × ℕ) (w : unsigned) : get_m (ℕ ⊕ (ℕ × ℕ)) :=
let b := w.val % 2,
    w' := w.val / 2,
    c := coef.1,
    coef' := (c * word_sz, c * w' + coef.2) in
if b = 0 then pure (sum.inr coef')
         else pure (sum.inl coef'.2)

def nat.decode : get_m ℕ :=
get_m.loop nat.decode_aux pure (1,0)

instance : serial ℕ :=
{ encode := nat.encode,
  decode := nat.decode,
  correctness :=
begin
  intro, dsimp [nat.decode],
  suffices : get_m.loop nat.decode_aux pure (1, 0) -<< nat.encode w = pure (1 * w + 0),
  { simp * },
  generalize : 0 = k,
  generalize : 1 = x,
  induction w using nat.strong_induction_on generalizing x k,
  rw [nat.encode], dsimp, split_ifs,
  { simp [nat.decode_aux], rw w_a,
    simp, congr,
    rw [nat.mul_div_right,mul_assoc,← nat.left_distrib x,add_comm,nat.mod_add_div],
    norm_num, apply nat.div_lt_self,
    { by_contradiction, revert h,
      apply not_lt_of_le, replace a := le_antisymm (le_of_not_lt a) (nat.zero_le _),
      subst w_n, norm_num [word_sz], },
    norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one], },
  { simp [nat.decode_aux], rw if_neg,
    simp, simp [pure,read_write], congr, rw nat.add_mul_div_left,
    norm_num, replace h := le_antisymm (le_of_not_lt h) (nat.zero_le _),
    have := nat.mod_add_div w_n word_sz,
    simp [h] at this, exact this,
    { norm_num }, { norm_num } }
end }

def list.encode {α : Type u} [serial α] (xs : list α) : put_m.{u} :=
encode (up.{u} xs.length) >> xs.mmap encode >> pure punit.star

def list.decode {α : Type u} [serial α] : get_m.{u} (list α) :=
do n ← decode _,
   (list.iota $ down.{u} n).mmap $ λ _, decode α

instance : serial1 list.{u} :=
{ encode := @list.encode,
  decode := @list.decode,
  correctness :=
begin
  introsI,
  simp [list.encode,list.decode,seq_left_eq,(>>)],
  simp [bind_assoc,encode_decode_bind],
  induction w,
  { simp [nat.add_one,list.iota,mmap], refl },
  { simp [nat.add_one,list.iota,mmap,encode_decode_bind] with functor_norm,
    rw read_write_mono_left w_ih, refl, }
end }

instance {p : Prop} [decidable p] : serial (plift p) :=
{ encode := λ w, pure punit.star,
  decode := if h : p then pure ⟨ h ⟩ else get_m.fail,
  correctness := by { rintros ⟨ h ⟩, rw dif_pos h, refl } }

/- Todo:
* instances
   * [x] sum
   * [x] nat
   * [x] list
   * [ ] tree
* automate
-/
