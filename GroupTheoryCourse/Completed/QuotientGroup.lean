-- Quotient groups
--
-- Generalizing group operations to subsets. Quotient groups. Cosets. Normal subgroups.
------------------------------------------------------------
import GroupTheoryCourse.Group
import GroupTheoryCourse.Subgroup
------------------------------------------------------------
-- Throughout this file, let G be a group.
------------------------------------------------------------
variable {G} [Group G]
------------------------------------------------------------
-- Generalizing group operations to subsets
-------------------------------------------
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
  mul A B  := {h : G | ∃ a ∈ A, ∃ b ∈ B, h = a * b}
instance : Inv (Set G) where
  inv H    := {ainv : G | ∃ a ∈ H, ainv = a⁻¹}
------------------------------------------------------------
-- Generalized associativity laws
---------------------------------
                lemma elt_mul_elt_mul_set_assoc
                  (g₁ g₂ : G)
                  (A : Set G)
                :------------------------------
                  g₁ * g₂ * A = g₁ * (g₂ * A)
:= by
  ext x; constructor <;> intro h
  . have ⟨a, ha, hx⟩ := h
    use g₂ * a; constructor
    . use a
    . rw [hx]; group
  . have ⟨g₂a, hg₂a, hx⟩ := h
    have ⟨a, ha, hg₂a⟩ := hg₂a
    use a; constructor; exact ha
    rw [hx, hg₂a]; group
------------------------------------------------------------
                lemma elt_mul_set_mul_elt_assoc
                  (a b : G)
                  (A : Set G)
                :--------------
                  a * A * b = a * (A * b)
:= by
  ext x; constructor <;> intro hx
  . have ⟨aa', ⟨a', ha', haa'⟩, hx⟩ := hx
    rw [hx, haa']
    use a' * b; constructor; use a'; group
  . have ⟨a'b, ⟨a', ha', ha'b⟩, hx⟩ := hx
    rw [hx, ha'b]
    use a * a'; constructor; use a'; group
------------------------------------------------------------
                lemma set_mul_set_mul_set_assoc
                  (A B C : Set G)
                :--------------------------
                  A * B * C = A * (B * C)
:= by
  ext abc
  constructor <;> intro h
  . have ⟨ab, ⟨a, ha, b, hb, hab⟩, ⟨c, hc, habc⟩⟩ := h
    use a; constructor
    . exact ha
    . use b * c; constructor
      . use b; constructor
        . exact hb
        . use c
      . rw [habc, hab]; group
  . have ⟨a, ha, bc, ⟨b, hb, c, hc, hbc⟩, habc⟩ := h
    use a * b; constructor
    . use a; constructor
      . exact ha
      . use b
    . use c; constructor
      . exact hc
      . rw [habc, hbc]; group
------------------------------------------------------------
                lemma set_mul_elt_mul_elt_assoc
                  (g₁ g₂ : G)
                  (A : Set G)
                :--------------------------------
                  A * g₁ * g₂ = A * (g₁ * g₂)
:= by
  ext x; constructor <;> intro h
  . have ⟨ag₁, hag₁, hx⟩ := h
    have ⟨a, ha, hag₁⟩ := hag₁
    rw [hx, hag₁]
    use a; constructor; exact ha; group
  . have ⟨a, ha, hx⟩ := h
    use a * g₁; constructor
    . use a
    . rw [hx]; group
------------------------------------------------------------
                lemma set_mul_set_mul_elt_assoc
                  (a : G)
                  (A B : Set G)
                :----------------
                  A * B * a = A * (B * a)
:= by
  ext x; constructor <;> intro hx
  . have ⟨a'b, ⟨a', ha', b, hb, ha'b⟩, hx⟩ := hx
    rw [hx, ha'b]
    use a'; constructor; exact ha'; use b * a; constructor; use b; group
  . have ⟨a', ha', ba, ⟨b, hb, hba⟩, hx⟩ := hx
    rw [hx, hba]
    use a' * b; constructor; use a'; constructor; exact ha'; use b; group
------------------------------------------------------------
                lemma elt_mul_set_mul_set_assoc
                  (a : G)
                  (A B : Set G)
                :----------------
                  a * A * B = a * (A * B)
:= by
  ext x; constructor <;> intro hx
  . have ⟨aa', ⟨a', ha', haa'⟩, b, hb, hx⟩ := hx
    rw [hx, haa']
    use a' * b; constructor; use a'; constructor; exact ha'; use b; group
  . have ⟨a'b, ⟨a', ha', b, hb, ha'b⟩, hx⟩ := hx
    rw [hx, ha'b]
    use a * a'; constructor; use a'; use b; constructor; exact hb; group
------------------------------------------------------------
                lemma set_mul_elt_mul_set_assoc
                  (a : G)
                  (A B : Set G)
                :---------------
                  A * a * B = A * (a * B)
:= by
  ext x; constructor <;> intro hx
  . have ⟨a'a, ⟨a', ha', ha'a⟩, b, hb, hx⟩ := hx
    rw [hx, ha'a]
    use a'; constructor; exact ha'; use a * b; constructor; use b; group
  . have ⟨a', ha', ab, ⟨b, hb, hab⟩, hx⟩ := hx
    rw [hx, hab]
    use a' * a; constructor; use a'; use b; constructor; exact hb; group
------------------------------------------------------------
-- Generalized identity laws
----------------------------
                lemma one_mul_set
                  (A : Set G)
                :------------------
                  (1 : G) * A = A
:= by
  ext x
  constructor <;> intro h
  . have ⟨a, ha, hx⟩ := h
    rw [hx]; group; exact ha
  . use x; group; exact h
------------------------------------------------------------
                lemma set_mul_one
                  (A : Set G)
                :------------------
                  A * (1 : G) = A
:= by
  ext x
  constructor <;> intro h
  . have ⟨a, ha, hx⟩ := h
    rw [hx]; group; exact ha
  . use x; group; exact h
------------------------------------------------------------
-- Generalized inversion laws
-----------------------------
                lemma inv_set_mul_set
                  (A B : Set G)
                :------------------------
                  (A * B)⁻¹ = B⁻¹ * A⁻¹
:= by
  ext x; constructor <;> intro hx
  . have ⟨ab, ⟨a, ha, b, hb, hab⟩, hx⟩ := hx
    use b⁻¹; constructor; use b; use a⁻¹; constructor; use a; rw [hx, hab]; group
  . have ⟨b_inv, ⟨b, hb, hb_inv⟩, a_inv, ⟨a, ha, ha_inv⟩, hx⟩ := hx
    use a * b; constructor; use a; constructor; exact ha; use b;
    rw [hx, hb_inv, ha_inv]; group
------------------------------------------------------------
                lemma inv_inv_set
                  (A : Set G)
                :--------------
                  A⁻¹⁻¹ = A
:= by
  ext x; constructor <;> intro hx
  . have ⟨a_inv, ⟨a, ha, ha_inv⟩, hx⟩ := hx
    rw [hx, ha_inv]; group; exact ha
  . use x⁻¹; constructor; use x; group
------------------------------------------------------------
                lemma inv_elt_mul_set
                  (A : Set G)
                  (a : G)
                :----------
                  (a * A)⁻¹ = A⁻¹ * a⁻¹
:= by
  ext x; constructor <;> intro hx
  . have ⟨na', ⟨a', ha', hna'⟩, hx⟩ := hx
    rw [hx, hna']
    group
    use a'⁻¹; constructor; use a'; rfl
  . have ⟨a'_inv, ⟨a', ha', ha'_inv⟩, hx⟩ := hx
    rw [hx, ha'_inv]
    use a * a'; constructor; use a'; group
------------------------------------------------------------
                lemma inv_set_mul_elt
                  (A : Set G)
                  (a : G)
                :-------------------
                  (A * a)⁻¹ = a⁻¹ * A⁻¹
:= by
  ext x; constructor <;> intro hx
  . have ⟨a'a, ⟨a', ha', ha'a⟩, hx⟩ := hx
    rw [hx, ha'a]
    use a'⁻¹; constructor; use a'; group
  . have ⟨a'_inv, ⟨a', ha', ha'_inv⟩, hx⟩ := hx
    rw [hx, ha'_inv]
    use a' * a; constructor; use a'; group
------------------------------------------------------------
-- Subgroup laws
----------------
                lemma elt_mul_subgroup
                  (N : Subgroup G)
                  (n : G) (hn : n ∈ N)
                :----------------------------
                  n * N.uset = N.uset
:= by
  ext x; constructor <;> intro hx
  . have ⟨n', hn', hx⟩ := hx; rw [hx]; apply Subgroup.mul_mem <;> assumption
  . use n⁻¹ * x; constructor; apply Subgroup.mul_mem; apply Subgroup.inv_mem;
    assumption; assumption; group
------------------------------------------------------------
                lemma subgroup_mul_elt
                  (N : Subgroup G)
                  (a : G) (ha : a ∈ N)
                :-----------------------
                  N.uset * a = N.uset
:= by
  ext x
  constructor <;> intro h
  . have ⟨b, hb, hx⟩ := h
    rw [hx]
    apply Subgroup.mul_mem; exact hb; exact ha
  . use x * a⁻¹; constructor
    . apply Subgroup.mul_mem; exact h; apply Subgroup.inv_mem; exact ha
    . group
------------------------------------------------------------
                lemma subgroup_mul_self
                  (N : Subgroup G)
                :---------------------------
                  N.uset * N.uset = N.uset
:= by ext x; constructor <;> intro h
      . have ⟨n₁, hn₁, n₂, hn₂, hx⟩ := h; rw [hx]; apply Subgroup.mul_mem <;> assumption
      . use 1; constructor; apply Subgroup.one_mem; use x; constructor; assumption; group

------------------------------------------------------------
                lemma inv_subgroup
                  (N : Subgroup G)
                :-------------------
                  N.uset⁻¹ = N.uset
:= by
  ext x; constructor <;> intro hx;
  . have ⟨n, hn, hx⟩ := hx
    rw [hx]; apply N.inv_mem; exact hn
  . use x⁻¹; constructor; apply N.inv_mem; exact hx; group
------------------------------------------------------------
-- The group_subset tactic
--------------------------
                lemma reassoc_right_inv_mul_elt_mul_set
                  (A : Set G)
                  (a : G)
                :--------------------
                  a⁻¹ * (a * A) = A
:= by rw [←elt_mul_elt_mul_set_assoc]; group; rw [one_mul_set]
------------------------------------------------------------
                lemma reassoc_right_elt_mul_inv_mul_set
                  (A : Set G)
                  (a : G)
                :--------------------
                  a * (a⁻¹ * A) = A
:= by rw [←elt_mul_elt_mul_set_assoc]; group; rw [one_mul_set]
------------------------------------------------------------
                lemma reassoc_right_subgroup_mul_self_mul_set
                  (N : Subgroup G)
                  (A : Set G)
                :--------------
                  N.uset * (N.uset * A) = N.uset * A
:= by rw [←set_mul_set_mul_set_assoc, subgroup_mul_self]
------------------------------------------------------------
                lemma reassoc_right_subgroup_mul_self_mul_elt
                  (N : Subgroup G)
                  (a : G)
                :--------------
                  N.uset * (N.uset * a) = N.uset * a
:= by rw [←set_mul_set_mul_elt_assoc, subgroup_mul_self]
------------------------------------------------------------
macro "group_subset" : tactic =>
  `(tactic| simp [Group.mul_assoc,
                  Group.one_mul, Group.mul_one, Group.inv_one,
                  Group.reassoc_right_inv_mul, Group.reassoc_right_mul_inv,
                  Group.inv_mul, Group.mul_inv, Group.mul_inv_rev, Group.inv_inv,

                  elt_mul_elt_mul_set_assoc,
                  elt_mul_set_mul_elt_assoc,
                  elt_mul_set_mul_set_assoc,
                  set_mul_elt_mul_elt_assoc,
                  set_mul_elt_mul_set_assoc,
                  set_mul_set_mul_elt_assoc,
                  set_mul_set_mul_set_assoc,

                  one_mul_set, set_mul_one, inv_subgroup, subgroup_mul_self,
                  reassoc_right_inv_mul_elt_mul_set,
                  reassoc_right_elt_mul_inv_mul_set,
                  reassoc_right_subgroup_mul_self_mul_set,
                  reassoc_right_subgroup_mul_self_mul_elt,
                  inv_elt_mul_set, inv_set_mul_elt, inv_set_mul_set, inv_inv_set
                  ])
------------------------------------------------------------
-- Cosets
---------
--
-- The above definitions and lemmas suggest a group-like structure on the subsets of G.
--
-- Let Γ = {Γᵢ}ᵢ be some collection of nonempty subsets of G; furthermore, suppose that the elements
-- of Γ are closed under multiplication and inversion as defined above, and that those operations
-- satisfy the group laws, thus making Γ a group.
--
-- Since Γ is a group, it must have an identity element N ∈ Γ satisfying
--
--   N * N = N, N⁻¹ = N
--
-- from the one_mul and inv_one laws. N also must satisfy
--
--   (1 : G) ∈ N
--
-- (this is left as an exercise). Therefore, N must be a *subgroup* of G. Furthermore, by the group
-- laws, it must be the case that
--
--   A * N  =  A  =  N * A
--
-- and
--
--   A⁻¹ * A = A * A⁻¹ = N
--
-- for all A ∈ Γ.
--
-- Given a subgroup N of G, any A : Set G satisfying the above laws will be called a *coset* of N:
------------------------------------------------------------
/- DEFINITION. A coset of a subgroup N is -/
structure Coset (N : Subgroup G) where
  /- A set A of elements of G, -/
  uset : Set G

  /- satisfying:
       1) A must be nonempty -/
  is_nonempty : ∃ a, a ∈ uset
  /-   2) A must satisfy A * N = A and N * A = A -/
  mul_subgroup : uset * N.uset = uset
  subgroup_mul : N.uset * uset = uset
  /-   3) A must satisfy A * A⁻¹ = N and A⁻¹ * A = N -/
  mul_inv : uset * uset⁻¹ = N.uset
  inv_mul : uset⁻¹ * uset = N.uset
------------------------------------------------------------
namespace Coset

variable {N : Subgroup G}
------------------------------------------------------------
                lemma Coset_eq
                  (A B : Coset N)
                  (h : A.uset = B.uset)
                :------------------------
                  A = B
:= by
  calc  A = ⟨A.uset, _, _, _, _, _⟩  := by definition
        _ = ⟨B.uset, _, _, _, _, _⟩  := by simp [h]
        _ = B                        := by definition
------------------------------------------------------------
-- As it turns out, the cosets of N are closed under multiplication and inversion; and N (a coset of
-- itself) acts as an identity:
------------------------------------------------------------
instance instMul : Mul (Coset N) where
  mul A B := by
    apply Coset.mk (A.uset * B.uset)
    . have ⟨a, ha⟩ := A.is_nonempty
      have ⟨b, hb⟩ := B.is_nonempty
      use a * b; use a; constructor; exact ha; use b
    . calc  A.uset * B.uset * N.uset  = A.uset * (B.uset * N.uset) := by group_subset
            _                         = A.uset * B.uset := by rw [B.mul_subgroup]
    . calc  N.uset * (A.uset * B.uset)
            = N.uset * A.uset * B.uset  := by group_subset
          _ = A.uset * B.uset           := by rw [A.subgroup_mul]
    . calc  A.uset * B.uset * (A.uset * B.uset)⁻¹
            = A.uset * (B.uset * B.uset⁻¹) * A.uset⁻¹ := by group_subset
          _ = N.uset := by rw [B.mul_inv, A.mul_subgroup, A.mul_inv]
    . calc  (A.uset * B.uset)⁻¹ * (A.uset * B.uset)
            = B.uset⁻¹ * ((A.uset⁻¹ * A.uset) * B.uset) := by group_subset
          _ = N.uset := by rw [A.inv_mul, B.subgroup_mul, B.inv_mul]
------------------------------------------------------------
instance instOne : One (Coset N) where
  one := by
    apply Coset.mk N.uset; use 1; apply Subgroup.one_mem
    repeat group_subset
------------------------------------------------------------
instance instInv : Inv (Coset N) where
  inv A := by
    apply Coset.mk A.uset⁻¹
    . have ⟨a, ha⟩ := A.is_nonempty
      use a⁻¹; use a
    . calc  A.uset⁻¹ * N.uset = (N.uset * A.uset)⁻¹ := by group_subset
            _                 = A.uset⁻¹ := by rw [A.subgroup_mul]
    . calc  N.uset * A.uset⁻¹ = (A.uset * N.uset)⁻¹ := by group_subset
            _                 = A.uset⁻¹ := by rw [A.mul_subgroup]
    . group_subset; rw [A.inv_mul]
    . group_subset; rw [A.mul_inv]
------------------------------------------------------------
-- In summary: *for any subgroup N of G, the cosets of N form a group.*
------------------------------------------------------------
instance instGroup : Group (Coset N) where
  mul_assoc' A B C := by
    apply Coset_eq
    show A.uset * B.uset * C.uset = A.uset * (B.uset * C.uset)
    apply set_mul_set_mul_set_assoc
  one_mul' A := by
    apply Coset_eq
    show N.uset * A.uset = A.uset
    apply A.subgroup_mul
  inv_mul' A := by
    apply Coset_eq
    show A.uset⁻¹ * A.uset = N.uset
    apply A.inv_mul
------------------------------------------------------------
-- Now, it turns out that given a coset A of a subgroup N, and any element a ∈ A, we can show that a
-- *conjugates* N, or a * N.uset * a⁻¹ = N.uset:
------------------------------------------------------------
                theorem Coset_elt_conj_subgroup
                  (A : Coset N) (a : G) (ha : a ∈ A.uset)
                :-------------------------------------
                  a * N.uset * a⁻¹ = N.uset
:= by
  ext x; constructor <;> intro hx
  . have ⟨a', ⟨n, hn, ha'⟩, hx⟩ := hx
    rw [hx, ha']
    have h : A.uset * N.uset * A.uset⁻¹ = N.uset := by
      calc  A.uset * N.uset * A.uset⁻¹  = A.uset * A.uset⁻¹ := by rw [A.mul_subgroup]
            _                           = N.uset := by rw [A.mul_inv]
    have : a * n * a⁻¹ ∈ A.uset * N.uset * A.uset⁻¹ := by
      use a * n; constructor; use a; constructor; exact ha; use n; use a⁻¹; constructor; use a; rfl
    rw [h] at this; exact this
  . use a * a⁻¹ * x * a; constructor; use a⁻¹ * x * a; constructor;
    . show a⁻¹ * x * a ∈ N.uset
      have h : A.uset⁻¹ * N.uset * A.uset = N.uset := by
        calc  A.uset⁻¹ * N.uset * A.uset  = (N.uset * A.uset)⁻¹ * A.uset := by group_subset
              _                           = A.uset⁻¹ * A.uset := by rw [A.subgroup_mul]
              _                           = N.uset := by rw [A.inv_mul]
      have : a⁻¹ * x * a ∈ A.uset⁻¹ * N.uset * A.uset := by
        use a⁻¹ * x; constructor; use a⁻¹; constructor; use a; use x; use a
      rw [h] at this; exact this
    . group
    . group
------------------------------------------------------------
-- Furthermore, this goes in the other direction -- if a : G conjugates N, then there is a Coset
-- which contains a:
------------------------------------------------------------
                def Coset_of_conjugate
                  (a : G) (ha : a * N.uset * a⁻¹ = N.uset)
                :-------------------------------------------
                  Coset N
:= by
  apply Coset.mk (a * N.uset)
  . use a; use 1; constructor; apply Subgroup.one_mem; group
  . group_subset
  . calc  N.uset * (a * N.uset) = a * (a⁻¹ * N.uset * a) * N.uset := by group_subset
          _                     = a * (a⁻¹ * (a * N.uset * a⁻¹) * a) * N.uset := by rw [ha]
          _                     = a * N.uset := by group_subset
  . group_subset; rw [elt_mul_set_mul_elt_assoc] at ha; exact ha
  . group_subset
------------------------------------------------------------
                lemma conjugate_mem_coset
                  (a : G) (ha : a * N.uset * a⁻¹ = N.uset)
                :-------------------------------------------
                  a ∈ (Coset_of_conjugate a ha).uset
:= by
  simp [Coset_of_conjugate]
  use 1; constructor; apply Subgroup.one_mem; group
------------------------------------------------------------
-- The set of all conjugates of N is called the *normalizer* of N.
------------------------------------------------------------
def normalizer (N : Subgroup G) : Set G :=
  { a : G | a * N.uset * a⁻¹ = N.uset }
------------------------------------------------------------
-- In other words, the normalizer of a subgroup N is both:
-- 1) the set of all conjugates of N (by definition)
-- 2) the elements of G which belong to a coset of N (by Coset_of_conjugate)
--
-- Unsurprisingly, the normalizer is also a subgroup:
------------------------------------------------------------
def Normalizer (N : Subgroup G) : Subgroup G := by
  apply Subgroup.mk (normalizer N)
  . intro a b ha hb
    dsimp [normalizer]
    calc  a * b * N.uset * (a * b)⁻¹  = a * (b * N.uset * b⁻¹) * a⁻¹ := by group_subset
          _                           = N.uset := by rw [hb, ha]
  . dsimp [normalizer]
    group_subset
  . intro a ha
    show a⁻¹ * N.uset * a⁻¹⁻¹ = N.uset
    calc  a⁻¹ * N.uset * a⁻¹⁻¹  = a⁻¹ * (a * N.uset * a⁻¹) * a⁻¹⁻¹ := by rw [ha]
          _                     = N.uset := by group_subset
------------------------------------------------------------
namespace Exercises

-- Exercise 1.
-- Fill in all of the `sorry`s in this file.

end Exercises
end Coset
