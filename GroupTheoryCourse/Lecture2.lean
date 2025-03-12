-- Group Theory Lecture 2. Subgroups
--
-- Definition of a subgroup. Examples of subgroups. A few basic group lemmas. Multiplication/
-- inversion of subsets/subgroups.
---------------------------------

import GroupTheoryCourse.Lecture1

import Mathlib.Data.Set.Basic

-- Throughout this chapter, let G be a group.
variable {G} [Group G]

-- DEFINITION.
/- A *subgroup* is -/
structure Subgroup (G : Type u) [Group G] where
  /- a set of elements from a group (its "underlying set" or "uset")-/
    uset : Set G

  -- satisfying:

  /- The set is closed under multiplication -/
    mul_mem' (a b : G) (ha : a ∈ uset) (hb : b ∈ uset) : a * b ∈ uset
  /- The set contains 1                     -/
    one_mem'                                           : 1 ∈ uset
  /- 3. The set is closed under inversion   -/
    inv_mem' (a : G) (ha : a ∈ uset)                   : a⁻¹ ∈ uset

-- Throughout the remainder of this lecture, let H be a subgroup of G.
variable {H : Subgroup G}

namespace Subgroup

---->>Notation<<----
-- This "makes H into a type". (whatever that means)
instance instCoe : CoeOut (Subgroup G) (Type u) where
  coe H := Subtype H.uset
---->>--------<<----

---->>Notation<<----
-- This allows the notation "a ∈ H", "∀ x ∈ H", and "∃ x ∈ H".
instance instMembership : Membership G (Subgroup G) where
  mem H x := x ∈ H.uset
---->>--------<<----

---->>Notation<<----
-- For `H : Subgroup G`, notation for `1 : H`, `x⁻¹ : H`, and `x * y ∈ H` is inherited from G.
instance instOne: One H where
  one := Subtype.mk (1 : G) (Subgroup.one_mem' H)
instance instInv: Inv H where
  inv x := Subtype.mk (x⁻¹ : G) (Subgroup.inv_mem' H x.val x.property)
instance instMul: Mul H where
  mul x y := Subtype.mk (x * y : G) (Subgroup.mul_mem' H x.val y.val x.property y.property)
---->>--------<<----

-- Subgroup laws
------------------------------------------------------------
                /- A subgroup is closed under multiplication -/
                lemma mul_mem
                  (a b : G)
                  (ha : a ∈ H)
                  (hb : b ∈ H)
                :---------------
                  a * b ∈ H
  :=
  H.mul_mem' a b ha hb
------------------------------------------------------------
                /- A subgroup contains the identity -/
                lemma one_mem
                :--------
                  1 ∈ H
  := H.one_mem'
------------------------------------------------------------
                /- A subgroup is closed under inversion -/
                lemma inv_mem
                  (a : G)
                  (ha : a ∈ H)
                :---------------
                  a⁻¹ ∈ H
  :=
  H.inv_mem' a ha
------------------------------------------------------------

-- Finally, we are now able to prove that if `H` is a subgroup of `G`, then it is also a group. This
-- fact follows directly from the group axioms.

instance instGroup {H : Subgroup G} : Group H where
  mul_assoc' x y z  := Subtype.eq_iff.mpr (Group.mul_assoc x.val y.val z.val)
  one_mul' x        := Subtype.eq_iff.mpr (Group.one_mul x.val)
  inv_mul' x        := Subtype.eq_iff.mpr (Group.inv_mul x.val)
end Subgroup

-- Generalizing group operations to subsets and subgroups
---------------------------------------------------------

-- Next, we define multiplication and inversion for subsets and subgroups of G.
/-
  DEFINITION. For any A, B ⊆ G and any g ∈ G, define
      g * A = { g * a | a ∈ A }
      A * g = { a * g | a ∈ A }
      A * B = { a * b | a ∈ A, b ∈ B }
      A⁻¹   = { a⁻¹   | a ∈ A }

    For any subgroup H of G, define
      g * H = g * H.uset
-/
instance : HMul G (Set G) (Set G) where
  hMul g A := {h : G | ∃ a ∈ A, h = g * a}
instance : HMul (Set G) G (Set G) where
  hMul A g := {h : G | ∃ a ∈ A, h = a * g}
instance : Mul (Set G) where
  mul A B := {h : G | ∃ a ∈ A, ∃ b ∈ B, h = a * b}
instance : Inv (Set G) where
  inv H := {a : G | a⁻¹ ∈ H}
instance : HMul G (Subgroup G) (Set G) where
  hMul g H := { gh : G | ∃ h ∈ H, gh = g * h }
instance : HMul (Subgroup G) G (Set G) where
  hMul H g := { hg : G | ∃ h ∈ H, hg = h * g }

-- Lemmas about set and subgroup multiplication
------------------------------------------------------------
                lemma set_one_mul
                  (A : Set G)
                :------------------
                  (1 : G) * A = A
:= by
  calc  (1 : G) * A = { a' | ∃ a ∈ A, a' = 1 * a } := by definition
        _           = { a | a ∈ A } := by group
        _           = A := by definition
------------------------------------------------------------
                lemma set_mul_assoc
                  (A B C : Set G)
                :--------------------------
                  A * B * C = A * (B * C)
:= by
  ext x; constructor <;> intro h
  . have ⟨w, ⟨a, ha, b, hb, hw⟩, c, hc, hx⟩ := h
    use a; constructor
    . exact ha
    . use b * c; constructor
      . use b; constructor
        . exact hb
        . use c
      . rw [hx, hw]; group
  . have _ := h
    sorry
------------------------------------------------------------
                lemma subgroup_one_mul
                  (H : Subgroup G)
                :--------------------------
                  (1 : G) * H = H.uset
:= by
  calc  (1 : G) * H = { a' | ∃ a ∈ H, a' = 1 * a } := by definition
        _           = { a | a ∈ H } := by group
        _           = H.uset := by definition
------------------------------------------------------------
