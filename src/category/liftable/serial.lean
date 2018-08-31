
import category.liftable

universes u v w
universes u₀ u₁ v₀ v₁

instance : liftable1 option.{u} option.{v} :=
{ up := λ α β eq, @option.rec _ (λ _, option β) (@none β) (λ x, some $ eq x)
, down := λ α β eq, @option.rec _ (λ _, option α) (@none α) (λ x, some $ eq.symm x)
, up_down := by intros; cases x; simp
, down_up := by intros; cases x; simp }

namespace pliftable

@[reducible]
def up' {f : Type v₀ → Type v₁} {g : Type u₀ → Type u₁} [liftable1 f g] :
  f punit → g punit :=
liftable1.up equiv.punit_equiv_punit

@[reducible]
def down' {f : Type u₀ → Type u₁} {g : Type v₀ → Type v₁} [liftable1 f g] :
  g punit → f punit :=
liftable1.down equiv.punit_equiv_punit

end pliftable
