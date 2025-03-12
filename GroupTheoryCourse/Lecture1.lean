-- Group Theory Lecture 1. Groups
--
-- Definition of a group. Examples of groups. A few basic group lemmas.
---------------------------------

import GroupTheoryCourse.Utils
import GroupTheoryCourse.Prerequisites

-- DEFINITION.
--------------
/- A *Group* is a type G equipped with: -/
class Group (G : Type u) extends
  /- a binary operation,     * : G × G → G -/
    Mul G,
  /- an element,             1 : G         -/
    One G,
  /- an inverse,         [·]⁻¹ : G → G     -/
    Inv G
  where
  /- 1. Multiplication is associative: -/
    protected mul_assoc' (a b c : G) :  (a * b) * c  =  a * (b * c)
  /- 2. 1 is a left identity:          -/
    protected one_mul' (a : G) :              1 * a  =  a
  /- 3. a⁻¹ is a left inverse of a.    -/
    protected inv_mul' (a : G) :            a⁻¹ * a  =  1

/- An *AddGroup* is just a group with additive symbols rather than multiplicative ones, i.e it is a
   type G equipped with: -/
class AddGroup (G : Type u) extends
  /- a binary operation,     + : G × G → G -/
    Add G,
  /- an element,             0 : G         -/
    Zero G,
  /- an additive inverse, -[·] : G → G     -/
    Neg G
  where
  /- 1. Addition is associative:   -/
    protected add_assoc' (a b c : G) :  (a + b) + c  =  a + (b + c)
  /- 2. 0 is a left identity:      -/
    protected zero_add' (a : G) :              0 + a  =  a
  /- 3. -a is a left inverse of a. -/
    protected neg_add' (a : G) :              -a + a  =  0

---->>Notation<<----
-- * The `mul` operation `* : G × G → G` is left-associative, so when we write `a * b * c`, we mean
--   `(a * b) * c`.
-- * Same as above, but for `+`.
---->>--------<<----

---------------------
-- Examples of groups
namespace Examples
/- Example 1: Integers -/
namespace Int
instance instAdd' : AddGroup Int where
  add_assoc' := Int.add_assoc
  zero_add' := Int.zero_add
  neg_add' := Int.add_left_neg
end Int

/- Example 2: Permutations -/
structure Perm (α : Type u) where
  map : α → α
  inv : α → α

  inv_map : inv ∘ map = id
  map_inv : map ∘ inv = id

namespace Perm

-- [TODO] replace with Mathlib.
instance instMul {α} : Mul (Perm α) where
  mul σ τ := Perm.mk (σ.map ∘ τ.map) (τ.inv ∘ σ.inv)
    (by calc  ((τ.inv ∘ σ.inv) ∘ σ.map ∘ τ.map) = τ.inv ∘ (σ.inv ∘ σ.map) ∘ τ.map := by definition
              _                                 = τ.inv ∘ id ∘ τ.map := by rw [σ.inv_map]
              _                                 = τ.inv ∘ τ.map := by definition
              _                                 = id := by rw [τ.inv_map])
    (by sorry)

instance instOne {α} : One (Perm α) where
  one := Perm.mk id id
    (by definition)
    (by definition)

instance instInv {α} : Inv (Perm α) where
  inv σ := Perm.mk σ.inv σ.map
    (by sorry)
    (by sorry)

instance instGroup {α} : Group (Perm α) where
  mul_assoc' σ τ ρ := by
    sorry
  one_mul' σ := by
    sorry
  inv_mul' := by
    sorry

end Perm

/- Example 3: ℤ mod n -/
-- [TODO]

end Examples

namespace Group

-- Throughout this chapter, let G and H be arbitrary groups:
variable {G H} [Group G] [Group H]

-- Group lemmas
---------------
-- Style of lemma presentation:
-- ```
------------------------------------------------------------
--              /- Description of lemma. -/
--              lemma lemma_name
--                (A₁ : T₁)
--                ...
--                (Aₙ : Tₙ)
--              :----------
--                C
-- := <proof>
------------------------------------------------------------
-- ```

-- Group laws
------------------------------------------------------------
/- multiplication is associative. -/
lemma mul_assoc
                  (a b c : G)
                :--------------------------
                  a * b * c = a * (b * c)
  := Group.mul_assoc' a b c
------------------------------------------------------------
                /-- 1 is a left identity. -/
                lemma one_mul
                  (a : G)
                :------------
                  1 * a = a
:= Group.one_mul' a
------------------------------------------------------------
                /- Inverse left-cancellation. -/
                lemma inv_mul
                  (a : G)
                :--------------
                  a⁻¹ * a = 1
  := Group.inv_mul' a
------------------------------------------------------------

-- Basic derived laws
------------------------------------------------------------
                /- Inverse right-cancellation. -/
                lemma mul_inv
                  (a : G)
                :--------------
                  a * a⁻¹ = 1
  := by sorry
------------------------------------------------------------
                /- 1 is a right identity. -/
                lemma mul_one
                  (a : G)
                :------------
                  a * 1 = a
  := by sorry
------------------------------------------------------------
                /- 1⁻¹ = 1 -/
                lemma inv_one
                :----------------
                  (1 : G)⁻¹ = 1
  := by sorry
------------------------------------------------------------
                /- a⁻¹⁻¹ = a -/
                lemma inv_inv
                  (a : G)
                :------------
                  a⁻¹⁻¹ = a
  := by sorry
------------------------------------------------------------
                /- (a * b)⁻¹ = b⁻¹ * a⁻¹ -/
                lemma mul_inv_rev
                  (a b : G)
                :------------------------
                  (a * b)⁻¹ = b⁻¹ * a⁻¹
  := by sorry
------------------------------------------------------------

-- The "group tactic"
---------------------
-- To make our lives easier, we'll define the `group` tactic to automate proofs that only require
-- the repeated use of the above lemmas.

lemma reassoc_right_inv_mul (a b : G) : b⁻¹ * (b * a) = a := by
  simp [←mul_assoc, inv_mul, one_mul]
lemma reassoc_right_mul_inv (a b : G) : b * (b⁻¹ * a) = a := by
  simp [←mul_assoc, mul_inv, one_mul]

macro "group" : tactic =>
  `(tactic| simp [mul_assoc, one_mul, mul_one, inv_one,
                  reassoc_right_inv_mul, reassoc_right_mul_inv,
                  inv_mul, mul_inv, mul_inv_rev, inv_inv
                  ])

-- We can use our new tactic to blast away simple equalities:
example (a b c d: G) : a * (b * b⁻¹) * c * (d * 1) * d⁻¹ * c⁻¹ * a⁻¹ = 1 :=
  by group

-- More lemmas
--------------
-- These occasionally come in handy.
------------------------------------------------------------
                /- The identity is unique. -/
                lemma id_unique
                  (a b : G)
                  (h : a * b = b)
                :---------------------------
                  a = 1
:= by sorry
------------------------------------------------------------
                /- Inverses are unique. -/
                lemma inv_unique
                  (a b : G)
                  (h : a * b = 1)
                :------------------
                  b = a⁻¹
:= by sorry
------------------------------------------------------------
                /- Left cancellation. -/
                lemma mul_left_cancel
                  (a b c : G)
                  (h : a * b = a * c)
                :----------------------
                  b = c
:= by sorry
------------------------------------------------------------
                /- Right cancellation. -/
                lemma mul_right_cancel
                  (a b c : G)
                  (h : a * c = b * c)
                :---------------------
                  a = b
:= by sorry
------------------------------------------------------------

                theorem eq_inv_iff_inv_eq
                  (a b : G)
                :--------------------
                  a⁻¹ = b ↔ a = b⁻¹
:= by sorry
------------------------------------------------------------

end Group
