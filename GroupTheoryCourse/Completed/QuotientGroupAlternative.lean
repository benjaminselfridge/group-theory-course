-- Quotient groups
--
-- Generalizing group operations to subsets. Quotient groups. Cosets. Normal subgroups.
---------------------------------

import GroupTheoryCourse.Group
import GroupTheoryCourse.Subgroup

-- Throughout this section, let G be a group.
variable {G} [Group G]

-- Generalizing group operations to subsets
---------------------------------------------------------

-- Next, we define multiplication and inversion for subsets of G.
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

-- Lemmas about set and subgroup multiplication
------------------------------------------------------------
                lemma elt_mul_eq
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
                  (H : Subgroup G)
                  (a : G) (ha : a ∈ H)
                :-----------------------
                  H.uset * a = H.uset
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
                lemma elt_mul_set_assoc
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
                lemma set_mul_elt_assoc
                  (g₁ g₂ : G)
                  (A : Set G)
                :--------------------------------
                  A * (g₁ * g₂) = (A * g₁) * g₂
:= by
  ext x; constructor <;> intro h
  . have ⟨a, ha, hx⟩ := h
    use a * g₁; constructor
    . use a
    . rw [hx]; group
  . have ⟨ag₁, hag₁, hx⟩ := h
    have ⟨a, ha, hag₁⟩ := hag₁
    rw [hx, hag₁]
    use a; constructor; exact ha; group
------------------------------------------------------------
                lemma set_one_mul
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
                lemma set_mul_set_assoc
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
                lemma set_inv_mul
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
                lemma set_inv_inv
                  (A : Set G)
                :--------------
                  A⁻¹⁻¹ = A
:= by
  ext x; constructor <;> intro hx
  . have ⟨a_inv, ⟨a, ha, ha_inv⟩, hx⟩ := hx
    rw [hx, ha_inv]; group; exact ha
  . use x⁻¹; constructor; use x; group
------------------------------------------------------------
                lemma subgroup_inv
                  (N : Subgroup G)
                :-------------------
                  N.uset⁻¹ = N.uset
:= by
  ext x; constructor <;> intro hx;
  . have ⟨n, hn, hx⟩ := hx
    rw [hx]; apply N.inv_mem; exact hn
  . use x⁻¹; constructor; apply N.inv_mem; exact hx; group
------------------------------------------------------------
                lemma subgroup_mul_self
                  (N : Subgroup G)
                :---------------------------
                  N.uset * N.uset = N.uset
:= by ext x; constructor <;> intro h
      . have ⟨n₁, hn₁, n₂, hn₂, hx⟩ := h; rw [hx]; apply Subgroup.mul_mem <;> assumption
      . use 1; constructor; apply Subgroup.one_mem; use x; constructor; assumption; group

-- Cosets
---------
--
-- The above definitions and lemmas suggests a group-like structure on the *subsets* of G. Suppose
-- Γ = {Γᵢ}ᵢ is a collection of *nonempty subsets* of G. Let's further suppose that Γ forms a group.
--
-- Since Γ is a group, it must have an identity element N ∈ Γ satisfying
--
--   N * N = N, N⁻¹ = N
--
-- from the one_mul and inv_one laws; N also must satisfy (1 : G) ∈ N (exercise). Therefore, N
-- must be a *subgroup* of G. Furthermore, it must satisfy
--
--   A * N  =  A  =  N * A
--
-- and
--
--   A⁻¹ * A = A * A⁻¹ = N
--
-- for all A ∈ Γ. Any A satisfying the above laws will be termed a *coset* of N:

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

namespace Coset

variable {N : Subgroup G}

                lemma Coset_eq
                  (A B : Coset N)
                  (h : A.uset = B.uset)
                :------------------------
                  A = B
:= by
  calc  A = ⟨A.uset, _, _, _, _, _⟩  := by definition
        _ = ⟨B.uset, _, _, _, _, _⟩  := by simp [h]
        _ = B                        := by definition

-- Notice that by definition, cosets are closed under multiplication.

instance instMul : Mul (Coset N) where
  mul A B := by
    apply Coset.mk (A.uset * B.uset)
    . have ⟨a, ha⟩ := A.is_nonempty
      have ⟨b, hb⟩ := B.is_nonempty
      use a * b; use a; constructor; exact ha; use b
    . calc  A.uset * B.uset * N.uset  = A.uset * (B.uset * N.uset) := by rw [set_mul_set_assoc]
            _                         = A.uset * B.uset := by rw [B.mul_subgroup]
    . calc  N.uset * (A.uset * B.uset)  = N.uset * A.uset * B.uset  := by rw [set_mul_set_assoc]
            _                           = A.uset * B.uset           := by rw [A.subgroup_mul]
    . calc  A.uset * B.uset * (A.uset * B.uset)⁻¹ = A.uset * B.uset * (B.uset⁻¹ * A.uset⁻¹) := by
              rw [set_inv_mul]
            _                                     = A.uset * (B.uset * B.uset⁻¹) * A.uset⁻¹ := by
              repeat rw [set_mul_set_assoc]
            _                                     = A.uset * N.uset * A.uset⁻¹ := by
              rw [B.mul_inv]
            _                                     = A.uset * A.uset⁻¹ := by rw [A.mul_subgroup]
            _                                     = N.uset := by rw [A.mul_inv]
    . calc  (A.uset * B.uset)⁻¹ * (A.uset * B.uset) = B.uset⁻¹ * A.uset⁻¹ * (A.uset * B.uset) := by
              rw [set_inv_mul]
            _                                       = B.uset⁻¹ * ((A.uset⁻¹ * A.uset) * B.uset) :=
              by repeat rw [set_mul_set_assoc]
            _                                       = B.uset⁻¹ * (N.uset * B.uset) := by
              rw [A.inv_mul]
            _                                       = B.uset⁻¹ * B.uset := by rw [B.subgroup_mul]
            _                                       = N.uset := by rw [B.inv_mul]

-- They also contain an identity element, since N is a coset of itself and N is a subgroup:

instance instOne : One (Coset N) where
  one := by
    apply Coset.mk N.uset
    . use 1; apply Subgroup.one_mem
    . apply subgroup_mul_self
    . apply subgroup_mul_self
    . rw [subgroup_inv]; apply subgroup_mul_self
    . rw [subgroup_inv]; apply subgroup_mul_self

-- Finally, they are closed under inversion, also by definition:

instance instInv : Inv (Coset N) where
  inv A := by
    apply Coset.mk A.uset⁻¹
    . have ⟨a, ha⟩ := A.is_nonempty
      use a⁻¹; use a
    . calc  A.uset⁻¹ * N.uset = (N.uset * A.uset)⁻¹ := by rw [set_inv_mul, subgroup_inv]
            _                 = A.uset⁻¹ := by rw [A.subgroup_mul]
    . calc  N.uset * A.uset⁻¹ = (A.uset * N.uset)⁻¹ := by rw [set_inv_mul, subgroup_inv]
            _                 = A.uset⁻¹ := by rw [A.mul_subgroup]
    . rw [set_inv_inv, A.inv_mul]
    . rw [set_inv_inv, A.mul_inv]

instance instGroup : Group (Coset N) where
  mul_assoc' A B C := by
    apply Coset_eq
    show A.uset * B.uset * C.uset = A.uset * (B.uset * C.uset)
    apply set_mul_set_assoc
  one_mul' A := by
    apply Coset_eq
    show N.uset * A.uset = A.uset
    apply A.subgroup_mul
  inv_mul' A := by
    apply Coset_eq
    show A.uset⁻¹ * A.uset = N.uset
    apply A.inv_mul

end Coset
