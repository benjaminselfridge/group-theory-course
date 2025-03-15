-- Group Theory Lecture 3. Multiplication of subsets; Quotient groups
--
-- Motivation. Informal discussion. Definition of normal subgroup. Definition of quotient group.
---------------------------------

import GroupTheoryCourse.Group
import GroupTheoryCourse.Subgroup

-- Throughout this lecture, let G be a group.
variable {G} [Group G]

-- Generalizing group operations to subsets and subgroups
---------------------------------------------------------

-- Next, we define multiplication and inversion for subsets and subgroups of G.
/-
  DEFINITION. For any A, B ⊆ G and any g ∈ G, define
      g * A = { g * a | a ∈ A }
      A * g = { a * g | a ∈ A }
      A * B = { a * b | a ∈ A, b ∈ B }
      A⁻¹   = { a⁻¹   | a ∈ A }
-/
instance : HMul G (Set G) (Set G) where
  hMul g A := {h : G | ∃ a ∈ A, h = g * a}
instance : HMul (Set G) G (Set G) where
  hMul A g := {h : G | ∃ a ∈ A, h = a * g}
instance : Mul (Set G) where
  mul A B := {h : G | ∃ a ∈ A, ∃ b ∈ B, h = a * b}
instance : Inv (Set G) where
  inv H := {a : G | a⁻¹ ∈ H}

/-
  DEFINITION. For any subgroup H of G and any g ∈ G, define
      g * H = g * H.uset
      H * g = H.uset * g
-/
instance : HMul G (Subgroup G) (Set G) where
  hMul g H := g * H.uset
instance : HMul (Subgroup G) G (Set G) where
  hMul H g := H.uset * g

-- Lemmas about set and subgroup multiplication
------------------------------------------------------------
                lemma set_one_mul
                  (A : Set G)
                :------------------
                  (1 : G) * A = A
:= by sorry
------------------------------------------------------------
                lemma set_mul_assoc
                  (A B C : Set G)
                :--------------------------
                  A * B * C = A * (B * C)
:= by sorry
------------------------------------------------------------
                lemma subgroup_one_mul
                  (H : Subgroup G)
                :--------------------------
                  (1 : G) * H = H.uset
:= by sorry
------------------------------------------------------------
