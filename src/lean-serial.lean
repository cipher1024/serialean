
universes u v

structure serial (α : Type u) (β : Type v) :=
  (encode : α → β)
  (decode : β → option α)
  (correctness : true) -- fill me up

variables {α β γ φ : Type*}

def compose : serial β γ → serial α β → serial α γ :=
sorry -- fill me up

local infixr ` ∘ ` := compose

variables (x : serial α β) (y : serial β γ) (z : serial γ φ)

lemma compose_assoc :
  z ∘ (y ∘ x) = (z ∘ y) ∘ x :=
sorry -- prove me!

def serial_unsigned : serial unsigned (list unsigned) :=
sorry -- implementation please!

def serial_pair (x : serial α (list unsigned)) (y : serial β (list unsigned)) :
  serial (α × β) (list unsigned) :=
sorry -- implementation please!

def serial_sum (x : serial α (list unsigned)) (y : serial β (list unsigned)) :
  serial (α ⊕ β) (list unsigned) :=
sorry -- implementation please!

#eval serial_unsigned.encode 3
#eval (serial_pair serial_unsigned serial_unsigned).encode (31,17)
#eval (serial_sum serial_unsigned serial_unsigned).encode (sum.inl 31)
