------------------------------------------------------------
-- Subgroups
------------------------------------------------------------
import GroupTheoryCourse.Completed.Group
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.SymmDiff
------------------------------------------------------------
-- Throughout this chapter, let G be a group.
------------------------------------------------------------
variable {G} [Group G]

/- DEFINITION. A *subgroup* is -/
structure Subgroup (G : Type u) [Group G] where
  /- a set of elements from a group (its "underlying set" or "uset") -/
    uset : Set G

  -- satisfying:

  /- The set is closed under multiplication -/
    mul_mem' (a b : G) (ha : a ∈ uset) (hb : b ∈ uset) : a * b ∈ uset
  /- The set contains 1                     -/
    one_mem'                                           : 1 ∈ uset
  /- 3. The set is closed under inversion   -/
    inv_mem' (a : G) (ha : a ∈ uset)                   : a⁻¹ ∈ uset
------------------------------------------------------------
-- Throughout the remainder of this chapter, let H be a subgroup of G.
------------------------------------------------------------
variable {H : Subgroup G}

namespace Subgroup

instance instCoe : CoeOut (Subgroup G) (Type u) where
  coe H := Subtype H.uset
instance instOne: One H where
  one := Subtype.mk (1 : G) (Subgroup.one_mem' H)
instance instInv: Inv H where
  inv x := Subtype.mk (x⁻¹ : G) (Subgroup.inv_mem' H x.val x.property)
instance instMul: Mul H where
  mul x y := Subtype.mk (x * y : G) (Subgroup.mul_mem' H x.val y.val x.property y.property)
------------------------------------------------------------
-- Subgroup laws
------------------------------------------------------------
                /- A subgroup is closed under multiplication -/
                lemma mul_mem
                  (a b : G)
                  (ha : a ∈ H.uset)
                  (hb : b ∈ H.uset)
                :---------------
                  a * b ∈ H.uset
  :=
  H.mul_mem' a b ha hb
------------------------------------------------------------
                /- A subgroup contains the identity -/
                lemma one_mem
                :--------
                  1 ∈ H.uset
  := H.one_mem'
------------------------------------------------------------
                /- A subgroup is closed under inversion -/
                lemma inv_mem
                  (a : G)
                  (ha : a ∈ H.uset)
                :---------------
                  a⁻¹ ∈ H.uset
  :=
  H.inv_mem' a ha
------------------------------------------------------------
-- Finally, we are now able to prove that if `H` is a subgroup of `G`, then it is also a group. This
-- fact follows directly from the group axioms.
------------------------------------------------------------
instance instGroup {H : Subgroup G} : Group H where
  mul_assoc' x y z  := Subtype.eq_iff.mpr (Group.mul_assoc x.val y.val z.val)
  one_mul' x        := Subtype.eq_iff.mpr (Group.one_mul x.val)
  inv_mul' x        := Subtype.eq_iff.mpr (Group.inv_mul x.val)
------------------------------------------------------------
end Subgroup
