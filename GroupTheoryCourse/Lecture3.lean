-- Group Theory Lecture 3. Quotient groups
--
-- Motivation. Informal discussion. Definition of normal subgroup. Definition of quotient group.
---------------------------------

import GroupTheoryCourse.Lecture1
import GroupTheoryCourse.Lecture2

-- Throughout this lecture, let G be a group.
variable {G} [Group G]

-- Recall the definition of set multiplication:
example
                  (A B : Set G)
                :----------------------------------------------------
                  A * B = { ab : G | ∃ a ∈ A, ∃ b ∈ B, ab = a * b }
:= by definition

-- And the definition of set inverse:
example
                  (A : Set G)
                :--------------
                  A⁻¹ = { a : G | a⁻¹ ∈ A }
:= by definition

-- These operations make sense, and suggest a possible group-like structure on the subsets of G.

-- However, using *all* the subsets doesn't work.

-- Suppose we picked some collection of subsets of G, call this collection Γ : Set (Set G), and we
-- were clever enough to have picked a collection that formed a group under the above definitions of
-- multiplication and inverse.

def Γ : Set (Set G) := sorry
-- Suppose we have an instance for a group on Γ
def Γ_group : Group (Subtype Γ : Type u) :=


-- [TODO] Pictures

-- We must have an identity element `N ∈ Γ` satisfying:
-- ```
--   N * A = A * N = A, for all A ∈ Γ
-- ```
-- [TODO] notational note on `N` rather than `1`
-- Since `A = A * N`, we have
-- ```
--   A = { an : G | ∃ a ∈ A, ∃ n ∈ N, an = a * n }
--     =
-- ```
--
--
