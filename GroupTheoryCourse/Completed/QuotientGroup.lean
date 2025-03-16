-- Quotient groups
--
-- Generalizing group operations to subsets. Quotient groups. Cosets. Normal subgroups.
---------------------------------

import GroupTheoryCourse.Group
import GroupTheoryCourse.Subgroup

section
-- Throughout this section, let G be a group.
variable {G} [Group G]

-- Generalizing group operations to subsets
---------------------------------------------------------

-- Next, we define multiplication and inversion for subsets of G.
/-
  DEFINITION. For any A, B ⊆ G and any g ∈ G, define
      g * A = { g * a | a ∈ A }
      A * g = { a * g | a ∈ A }
      A * B = { a * B | a ∈ A } = { A * b | b ∈ B }
              { a * b | a ∈ A, b ∈ B }
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
                  (H : Subgroup G)
                  (a : G) (ha : a ∈ H)
                :----------------------------
                  a * H.uset = H.uset
:= by
  ext x; constructor <;> intro hx
  . have ⟨a', ha', hx'⟩ := hx
    rw [hx']
    apply Subgroup.mul_mem; exact ha; exact ha'
  . use a⁻¹ * x; constructor
    . apply Subgroup.mul_mem; apply Subgroup.inv_mem; exact ha; exact hx
    . group
------------------------------------------------------------
                lemma elt_mul_subgroup
                  (H : Subgroup G)
                  (a : G) (ha : a ∈ H)
                :----------------------
                  a * H.uset = H.uset
:= by
  ext x
  constructor <;> intro h
  . have ⟨b, hb, hx⟩ := h
    rw [hx]
    apply Subgroup.mul_mem; exact ha; exact hb
  . use a⁻¹ * x; constructor
    . apply Subgroup.mul_mem; apply Subgroup.inv_mem; exact ha; exact h
    . group
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

-- Cosets
---------
--
-- The above definitions and lemmas suggests a group-like structure on the *subsets* of G. Suppose
-- Γ = {Γᵢ}ᵢ is a collection of subsets of G such that ⋃ᵢΓᵢ = G. Let's further suppose that Γ forms
-- a group.
--
-- Since Γ is a group, it must have an identity element N ∈ Γ satisfying
--
--   N * N = N
--
-- and
--
--   N⁻¹ = N
--
-- from the one_mul and inv_one laws; N also must satisfy (1 : G) ∈ N (exercise). Therefore, N
-- must be a *subgroup* of G. Furthermore, it must satisfy
--
--   A * N  =  A  =  N * A
--
-- for all A ∈ Γ. Since A = A * N, it can be shown that for every a ∈ A, we have A = a * N = N * a.
-- This motivates the definition of a *left coset* and *right coset* of a subgroup N:

structure LCoset (N : Subgroup G) where
  uset : Set G
  is_nonempty : ∃ a, a ∈ uset
  is_lcoset (a : G) (ha : a ∈ uset) : uset = a * N.uset


def lcoset (a : G) (N : Subgroup G) : LCoset N := LCoset.mk
  (a * N.uset)
  (by use a; use 1; constructor; apply Subgroup.one_mem; group)
  (by intro a₁ ⟨n, hn, ha₁⟩
      have ha : a = a₁ * n⁻¹ := by rw [ha₁]; group
      calc  a * N.uset  = a₁ * n⁻¹ * N.uset := by rw [ha]
            _           = a₁ * N.uset := by
              have  hn_inv : n⁻¹ * N.uset = N.uset := by
                      apply elt_mul_subgroup; apply Subgroup.inv_mem; exact hn
              rw [elt_mul_set_assoc, hn_inv])

structure RCoset (N : Subgroup G) where
  uset : Set G
  is_rcoset (a : G) (ha : a ∈ uset) : uset = N.uset * a

def rcoset (N : Subgroup G) (a : G) : RCoset N := RCoset.mk
  (N.uset * a)
  (by intro a₁ ⟨n, hn, ha₁⟩
      have ha : n⁻¹ * a₁ = a := by rw [ha₁]; group
      calc  N.uset * a  = N.uset * (n⁻¹ * a₁) := by rw [ha]
            _           = N.uset * a₁ := by
              have  hn_inv : N.uset * n⁻¹ = N.uset := by
                      apply subgroup_mul_elt; apply Subgroup.inv_mem; exact hn
              rw [set_mul_elt_assoc, hn_inv])

-- Furthermore, A * N = N * A implies that for all a ∈ G,
--
--   a * N = N * a
--
-- or (as it's sometimes stated)
--
--   a * N * a⁻¹ = N.
--
-- Notice that this extra condition, called the "normality" condition on N, follows directly from
-- the assumption that N is the identity, and the knowledge that A * N = N * A. Recall that when we
-- defined a group, we only assumed left identity and left inverse, and *derived* right identity and
-- right inverse. This turns out to be very important, as it implies that only subgroups which
-- satisfy this identity A * N = N * A will work as identities in Γ.

-- The above considerations motivate the notion of a normal subgroup:

class Normal (N : Subgroup G) where
  lcoset_eq_rcoset' (a : G) : (lcoset a N).uset = (rcoset N a).uset

namespace Normal

--------------------------------
-- Lemmas about normal subgroups
------------------------------------------------------------
                lemma lcoset_eq_rcoset
                  (N : Subgroup G) [Normal N]
                  (a : G)
                :----------------------------------------
                  (lcoset a N).uset = (rcoset N a).uset
:= by apply lcoset_eq_rcoset'
------------------------------------------------------------
                lemma conj_eq
                  (N : Subgroup G) [Normal N]
                  (a : G)
                :------------------------------
                  a * N.uset * a⁻¹ = N.uset
:= by
  have h : a * N.uset = N.uset * a := lcoset_eq_rcoset N a
  rw [h]
  calc  N.uset * a * a⁻¹  = N.uset * (a * a⁻¹)  := by rw [set_mul_elt_assoc]
        _                 = N.uset * (1 : G)    := by group
        _                 = N.uset              := by rw [set_mul_one]
------------------------------------------------------------
                lemma conj_mem
                  (N : Subgroup G) [Normal N]
                  (a : G) (n : G) (hn : n ∈ N)
                :------------------------------
                  a * n * a⁻¹ ∈ N.uset
:= by
  have h_conj_eq := conj_eq N a
  have h : a * n * a⁻¹ ∈ a * N.uset * a⁻¹ := by
    use a * n; constructor
    . use n; constructor; exact hn; definition
    . definition
  rw [h_conj_eq] at h
  exact h
------------------------------------------------------------

end Normal

-- Now, we can define the group structure for cosets of a normal subgroup N:

namespace LCoset
------------------------------------------------------------
                lemma lcoset_eq
                  {N : Subgroup G}
                  (A B : LCoset N)
                  (h : A.uset = B.uset)
                :------------------------
                  A = B
:= by
  calc  A = LCoset.mk A.uset A.is_nonempty A.is_lcoset := by definition
        _ = LCoset.mk B.uset B.is_nonempty B.is_lcoset := by simp [h]
        _ = B := by definition
------------------------------------------------------------

instance instMul {N : Subgroup G} [Normal N] : Mul (LCoset N) where
  mul aN bN := LCoset.mk (aN.uset * bN.uset)
    (by have ⟨a, ha⟩ := aN.is_nonempty
        have ⟨b, hb⟩ := bN.is_nonempty
        use a * b
        use a; constructor; exact ha
        use b)
    (by intro ab ⟨a, ha, b, hb, hab⟩
        have haN: aN.uset = a * N.uset := by apply LCoset.is_lcoset; exact ha
        have hbN: bN.uset = b * N.uset := by apply LCoset.is_lcoset; exact hb
        rw [haN, hbN, hab]
        show a * N.uset * (b * N.uset) = a * b * N.uset
        ext x; constructor <;> intro hx
        . have ⟨a', ⟨n₁, hn₁, ha'⟩, b', ⟨n₂, hn₂, hb'⟩, hx'⟩ := hx
          rw [hx', ha', hb']
          show a * n₁ * (b * n₂) ∈ a * b * N.uset
          use b⁻¹ * n₁ * b * n₂; constructor
          . apply Subgroup.mul_mem
            . have h_conj_mem := Normal.conj_mem N b⁻¹ n₁ hn₁
              rw [Group.inv_inv] at h_conj_mem
              exact h_conj_mem
            . exact hn₂
          . group
        . have ⟨n, hn, hx'⟩ := hx
          use a; constructor
          . use 1; constructor; apply Subgroup.one_mem; group
          . use b * n; constructor
            . use n
            . rw [hx']; group)

instance instOne {N : Subgroup G} [Normal N] : One (LCoset N) where
  one := LCoset.mk N.uset
    (by use 1; apply Subgroup.one_mem)
    (by intro n hn
        rw [elt_mul_eq]
        exact hn)

instance instInv {N : Subgroup G} [Normal N] : Inv (LCoset N) where
  inv aN := LCoset.mk aN.uset⁻¹
    (by have ⟨a, ha⟩ := aN.is_nonempty
        use a⁻¹
        have : aN.uset = a * N.uset := by apply LCoset.is_lcoset; exact ha
        rw [this] at ha;
        rw [this]
        use a)
    (by intro ainv ⟨a, ha, hainv⟩
        have : aN.uset = a * N.uset := by apply LCoset.is_lcoset; exact ha
        rw [this, hainv]
        ext x; constructor <;> intro h
        . have ⟨a', ⟨n, hn, ha'⟩, hx⟩ := h
          rw [hx, ha']; group
          use a * n⁻¹ * a⁻¹; constructor
          . apply Normal.conj_mem; apply Subgroup.inv_mem; exact hn
          . group
        . have ⟨n, hn, hx⟩ := h
          rw [hx]; use n⁻¹ * a; constructor
          . use a⁻¹ * n⁻¹ * a; constructor
            . have h_conj_mem := Normal.conj_mem N a⁻¹ n⁻¹ (Subgroup.inv_mem n hn)
              rw [Group.inv_inv] at h_conj_mem
              exact h_conj_mem
            . group
          . group)

instance instGroup {N : Subgroup G} [Normal N] : Group (LCoset N) where
  mul_assoc' A B C := by
    apply lcoset_eq
    show A.uset * B.uset * C.uset = A.uset * (B.uset * C.uset)
    apply set_mul_set_assoc
  one_mul' := by
    intro aN
    apply lcoset_eq
    show N.uset * aN.uset = aN.uset
    ext x; constructor <;> intro h
    . have ⟨n, hn, a, ha, hx⟩ := h
      have: aN.uset = a * N.uset := by apply LCoset.is_lcoset; exact ha
      rw [this]
      rw [hx]
      use a⁻¹ * n * a; constructor
      . have h_conj_mem := Normal.conj_mem N a⁻¹ n hn
        rw [Group.inv_inv] at h_conj_mem;
        exact h_conj_mem
      . group
    . use 1; constructor
      . apply Subgroup.one_mem
      . use x; constructor; exact h; group
  inv_mul' aN := by
    apply lcoset_eq
    show aN.uset⁻¹ * aN.uset = N.uset
    ext x; constructor <;> intro h
    . have ⟨ainv, ⟨a, ha, hainv⟩, a', ha', hx⟩ := h
      have haN : aN.uset = a * N.uset := by apply LCoset.is_lcoset; exact ha
      rw [haN] at ha'
      rw [hx, hainv]
      have ⟨n, hn, ha'⟩ := ha'
      rw [ha']; group; exact hn
    . show x ∈ aN⁻¹.uset * aN.uset
      have ⟨a, ha⟩ := aN.is_nonempty
      use a⁻¹; constructor;
      . use a
      . use a * x; constructor
        . have haN : aN.uset = a * N.uset := by apply LCoset.is_lcoset; exact ha
          rw [haN]
          use x
        . group

end LCoset
