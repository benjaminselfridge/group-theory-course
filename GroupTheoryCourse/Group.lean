------------------------------------------------------------
-- Groups
------------------------------------------------------------
import GroupTheoryCourse.Utils
import GroupTheoryCourse.Prerequisites

/- DEFINITION. A *Group* is a type G equipped with: -/
class Group (G : Type u) extends
  /- a binary operation,     * : G × G → G -/
    Mul G,
  /- an element,             1 : G         -/
    One G,
  /- an inverse,         [·]⁻¹ : G → G     -/
    Inv G
  where
  /- 1. Multiplication is associative: -/
    mul_assoc' (a b c : G) :  (a * b) * c  =  a * (b * c)
  /- 2. 1 is a left identity:          -/
    one_mul' (a : G) :              1 * a  =  a
  /- 3. a⁻¹ is a left inverse of a.    -/
    inv_mul' (a : G) :            a⁻¹ * a  =  1
------------------------------------------------------------
-- Notation:
-- * The `mul` operation `* : G × G → G` is left-associative, so when we write `a * b * c`, we mean
--   `(a * b) * c`.
-- * Same as above, but for `+`.
------------------------------------------------------------
namespace Group
------------------------------------------------------------
-- Throughout this chapter, let G and H be arbitrary groups:
------------------------------------------------------------
variable {G H} [Group G] [Group H]
------------------------------------------------------------
-- Group lemmas
---------------
-- Mathematically important lemmas and theorems are presented in the following style:
------------------------------------------------------------
--              lemma lemma_name
--                (A₁ : T₁)    -- assumption 1
--                ...
--                (Aₙ : Tₙ)    -- assumption n
--              :------------
--                C            -- conclusion
-- := <proof>
------------------------------------------------------------
-- The A₁, ..., Aₙ are just local variable names representing each assumption T₁. We usually read
-- each assumption `A : T` as either
--
--             `a : G` <=====> "a is an element of type G"
--
-- or
--
--         `h : x = y` <=====> "h is a proof that x = y"
------------------------------------------------------------
-- Group laws
------------------------------------------------------------
                lemma mul_assoc
                  (a b c : G)
                :--------------------------
                  a * b * c = a * (b * c)
  := Group.mul_assoc' a b c
------------------------------------------------------------
                lemma one_mul
                  (a : G)
                :------------
                  1 * a = a
:= Group.one_mul' a
------------------------------------------------------------
                lemma inv_mul
                  (a : G)
                :--------------
                  a⁻¹ * a = 1
  := Group.inv_mul' a
------------------------------------------------------------
-- Basic derived laws
------------------------------------------------------------
                lemma mul_inv
                  (a : G)
                :--------------
                  a * a⁻¹ = 1
  := by sorry
------------------------------------------------------------
                lemma mul_one
                  (a : G)
                :------------
                  a * 1 = a
  := by sorry
------------------------------------------------------------
                lemma inv_one
                :----------------
                  (1 : G)⁻¹ = 1
  := by sorry
------------------------------------------------------------
                lemma inv_inv
                  (a : G)
                :------------
                  a⁻¹⁻¹ = a
  := by sorry
------------------------------------------------------------
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
------------------------------------------------------------
lemma reassoc_right_inv_mul (a b : G) : b⁻¹ * (b * a) = a := by
  simp [←mul_assoc, inv_mul, one_mul]
lemma reassoc_right_mul_inv (a b : G) : b * (b⁻¹ * a) = a := by
  simp [←mul_assoc, mul_inv, one_mul]
------------------------------------------------------------
macro "group" : tactic =>
  `(tactic| simp [mul_assoc, one_mul, mul_one, inv_one,
                  reassoc_right_inv_mul, reassoc_right_mul_inv,
                  inv_mul, mul_inv, mul_inv_rev, inv_inv])
------------------------------------------------------------
-- We can use our new tactic to blast away simple equalities:
------------------------------------------------------------
example (a b c d: G) : a * (b * b⁻¹) * c * (d * 1) * d⁻¹ * c⁻¹ * a⁻¹ = 1 :=
  by group
------------------------------------------------------------
-- More lemmas
--------------
-- These occasionally come in handy.
------------------------------------------------------------
                lemma id_unique
                  (a b : G)
                  (h : a * b = b)
                :---------------------------
                  a = 1
:= by sorry
------------------------------------------------------------
                lemma inv_unique
                  (a b : G)
                  (h : a * b = 1)
                :------------------
                  b = a⁻¹
:= by sorry
------------------------------------------------------------
                lemma mul_left_cancel
                  (a b c : G)
                  (h : a * b = a * c)
                :----------------------
                  b = c
:= by sorry
------------------------------------------------------------
                lemma mul_right_cancel
                  (a b c : G)
                  (h : a * c = b * c)
                :---------------------
                  a = b
:= by sorry
------------------------------------------------------------
namespace Exercises

-- Exercise 1.
-- Fill in all of the `sorry`s in this file.

end Exercises
end Group
