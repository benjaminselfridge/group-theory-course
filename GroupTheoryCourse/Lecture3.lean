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

section
open Examples
def Γ  : Set (Set (Perm ℤ)) := sorry

noncomputable instance Γ_group : Group Γ :=
  {
    mul A B := Subtype.mk (A.val * B.val) sorry
    one := sorry
    inv := sorry
    mul_assoc' := sorry
    one_mul' := sorry
    inv_mul' := sorry
  }

-- Then Γ would need an identity element, call it `N`:
def N := Γ_group.one

-- We would of course have N * N = N:
example : N * N = N := by
  show 1 * 1 = 1
  rw [Group.one_mul]

-- Which would then imply that N is closed under multiplication.

-- [TODO]
example : n_is_closed := sorry

-- Likewise, we know that N is closed under inversion, thanks to 1⁻¹ = 1:

-- [TODO]

-- We can also see that (1 : G) ∈ N, since N is assumed to be nonempty [TODO] and using the above
-- two properties. There, N must be a *subgroup*.

-- We can also show something about the other subsets in Γ. Let `A ∈ Γ`, and pick *any* `a ∈ A`.
-- Next, let `b ∈ A` be any element of `A`. We have
--
-- ```
--   b = a * a⁻¹ * b ∈ a * (A⁻¹ * A) = a * N
-- ```
--
-- Therefore, given an element `a ∈ A`, picked arbitrarily, we know `A = aN`.
--
-- Similarly, we can argue that `A = Na`.
--
-- Putting these two facts together, notice that for any `a ∈ A`, `aN = A = Na`. Let `a ∈ A`, and
-- `n ∈ N` be arbitrary. Then because `aN = Na`, we know there exists `n' ∈ N` with `an = n'a`. Then
--
-- ```
--   an = n'a
--   n' = ana⁻¹
-- ```
-- Since `n' ∈ N`, and `n` was picked arbitrarily, this tells us that `ana⁻¹` ∈ N.

end

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
