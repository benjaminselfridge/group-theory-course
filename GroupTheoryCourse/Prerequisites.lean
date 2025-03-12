import GroupTheoryCourse.Utils

def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

def Bijective (f : α → β) :=
  Injective f ∧ Surjective f

instance : Neg (Fin n) where
  neg _ := sorry
