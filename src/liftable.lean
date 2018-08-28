
import category.liftable

universes u v

instance : liftable1 option.{u} option.{v} :=
{ up := λ α β eq, @option.rec _ (λ _, option β) (@none β) (λ x, some $ eq x)
, down := λ α β eq, @option.rec _ (λ _, option α) (@none α) (λ x, some $ eq.symm x)
, up_down := by intros; cases x; simp
, down_up := by intros; cases x; simp }
