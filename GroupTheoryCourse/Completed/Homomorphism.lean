import GroupTheoryCourse.Completed.Group
import GroupTheoryCourse.Completed.Subgroup
import GroupTheoryCourse.Completed.Coset

variable {G H} [Group G] [Group H]

structure Hom (G H : Type*) [Group G] [Group H] where
  map : G → H
  map_mul' (a b : G) : map (a * b) = map a * map b

infixr:34 " →* "  => Hom

namespace Hom

-- Notation
instance instFunLike : FunLike (G →* H) G H where
  coe φ := φ.map
  coe_injective' := by
    intro φ₁ φ₂ h
    simp at h
    calc  φ₁  = Hom.mk φ₁.map φ₁.map_mul' := by definition
          _   = Hom.mk φ₂.map φ₂.map_mul' := by simp [h]
          _   = φ₂                        := by definition

------------------------------------------------------------
-- (Definitional lemma)
                /- φ (a * b) = φ a * φ b -/
                lemma map_mul
                  (φ : G →* H)
                  (a b : G)
                :------------------------
                  φ (a * b) = φ a * φ b
  :=
  φ.map_mul' a b
------------------------------------------------------------
-- Simplification lemmas
                lemma map_one
                  (φ : G →* H)
                :---------------
                  φ 1 = 1
  := by
  have h' : φ 1 * φ 1 = φ 1 * 1 := by group; rw [←map_mul]; group
  apply Group.mul_left_cancel (φ 1)
  exact h'
------------------------------------------------------------
                lemma map_inv
                  (φ : G →* H) (g : G)
                :-----------------------
                  φ g⁻¹ = (φ g)⁻¹
  := by
  have h' : φ g * φ g⁻¹ = φ g * (φ g)⁻¹ := by
    group; rw [←map_mul]; group; rw [map_one]
  apply Group.mul_left_cancel (φ g)
  exact h'
------------------------------------------------------------

end Hom
------------------------------------------------------------

-- Simplifying expressions with homomorphisms
---------------------------------------------
macro "hom" : tactic =>
  `(tactic| simp [Hom.map_mul,
                  Hom.map_inv,
                  Hom.map_one])
