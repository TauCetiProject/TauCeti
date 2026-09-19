/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.WeightEnumerator

/-!
# Semilinear equivalence of codes

A semilinear monomial transformation applies one automorphism of the alphabet to every
coordinate, rescales by coordinate units, and permutes coordinates. Its induced equivalence
of codes preserves dimension, cardinality, Hamming data, and weight enumerators. This
allows conjugate codes over a finite field to be compared without treating field
conjugation as a linear map over that field.

The conventions extend `TauCeti.monomialEquiv`: the units are applied after the alphabet
automorphism and before relabelling. Codes remain ordinary submodules, and their images
are formed with Mathlib's semilinear `Submodule.map`. When using the semilinear
map projections, make `RingHomInvPair.of_ringEquiv` and
`RingHomInvPair.of_ringEquiv_symm` local instances, as in this file.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.7.
-/

public section

namespace TauCeti

open Function

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {R ι κ μ : Type*} [CommSemiring R]

/-- Apply `σ` to the alphabet, multiply coordinate `i` by `u i`, then move it to `e i`. -/
def semilinearMonomialEquiv (σ : R ≃+* R) (u : ι → Rˣ) (e : ι ≃ κ) :
    (ι → R) ≃ₛₗ[(σ : R →+* R)] (κ → R) :=
  { (AddEquiv.piCongrRight fun _ ↦ σ.toAddEquiv).trans (monomialEquiv u e).toAddEquiv with
    map_smul' := by
      intro a x
      ext j
      simp [mul_left_comm] }

@[simp]
theorem semilinearMonomialEquiv_apply (σ : R ≃+* R) (u : ι → Rˣ) (e : ι ≃ κ)
    (x : ι → R) (j : κ) :
    semilinearMonomialEquiv σ u e x j = (u (e.symm j) : R) * σ (x (e.symm j)) := by
  simp [semilinearMonomialEquiv]

@[simp]
theorem semilinearMonomialEquiv_symm_apply (σ : R ≃+* R) (u : ι → Rˣ) (e : ι ≃ κ)
    (y : κ → R) (i : ι) :
    (semilinearMonomialEquiv σ u e).symm y i = σ.symm ((↑(u i)⁻¹ : R) * y (e i)) := by
  simp [semilinearMonomialEquiv]

/-- The identity alphabet automorphism recovers the monomial transformation. -/
@[simp]
theorem semilinearMonomialEquiv_refl (u : ι → Rˣ) (e : ι ≃ κ) :
    semilinearMonomialEquiv (RingEquiv.refl R) u e = monomialEquiv u e := by
  ext x j
  simp only [semilinearMonomialEquiv_apply, RingEquiv.refl_apply]
  exact (monomialEquiv_apply u e x j).symm

/-- The inverse uses the inverse alphabet automorphism and its images of the inverse units. -/
theorem semilinearMonomialEquiv_symm (σ : R ≃+* R) (u : ι → Rˣ) (e : ι ≃ κ)
    (y : κ → R) :
    (semilinearMonomialEquiv σ u e).symm y =
      semilinearMonomialEquiv σ.symm
        (fun j ↦ Units.map σ.symm.toMonoidHom (u (e.symm j))⁻¹) e.symm y := by
  apply funext
  intro i
  simp only [semilinearMonomialEquiv_apply, semilinearMonomialEquiv_symm_apply]
  simp

/-- Composition conjugates the first scaling by the second alphabet automorphism. -/
@[simp]
theorem semilinearMonomialEquiv_trans (σ τ : R ≃+* R) (u : ι → Rˣ) (v : κ → Rˣ)
    (e : ι ≃ κ) (f : κ ≃ μ) (x : ι → R) :
    semilinearMonomialEquiv τ v f (semilinearMonomialEquiv σ u e x) =
      semilinearMonomialEquiv (σ.trans τ)
        (fun i ↦ v (e i) * Units.map τ.toMonoidHom (u i)) (e.trans f) x := by
  apply funext
  intro j
  simp only [semilinearMonomialEquiv_apply]
  simp [mul_assoc]

/-- Semilinear monomial transformations transport support by their coordinate equivalence. -/
@[simp]
theorem support_semilinearMonomialEquiv (σ : R ≃+* R) (u : ι → Rˣ) (e : ι ≃ κ)
    (x : ι → R) : support (semilinearMonomialEquiv σ u e x) = e '' support x := by
  rw [Equiv.image_eq_preimage_symm]
  ext j
  simp [Units.mul_right_eq_zero]

section Hamming

variable [Fintype ι] [Fintype κ] [DecidableEq R]

/-- A semilinear monomial transformation preserves Hamming weight. -/
@[simp]
theorem hammingNorm_semilinearMonomialEquiv (σ : R ≃+* R) (u : ι → Rˣ)
    (e : ι ≃ κ) (x : ι → R) :
    hammingNorm (semilinearMonomialEquiv σ u e x) = hammingNorm x := by
  have h : semilinearMonomialEquiv σ u e x = monomialEquiv u e (fun i ↦ σ (x i)) := by
    ext j
    simp
  rw [h, hammingNorm_monomialEquiv]
  exact hammingNorm_comp (fun _ ↦ σ) (fun _ ↦ σ.injective) (fun _ ↦ σ.map_zero)

/-- A semilinear monomial transformation preserves Hamming distance. -/
@[simp]
theorem hammingDist_semilinearMonomialEquiv (σ : R ≃+* R) (u : ι → Rˣ)
    (e : ι ≃ κ) (x y : ι → R) :
    hammingDist (semilinearMonomialEquiv σ u e x) (semilinearMonomialEquiv σ u e y) =
      hammingDist x y := by
  have h (z : ι → R) :
      semilinearMonomialEquiv σ u e z = monomialEquiv u e (fun i ↦ σ (z i)) := by
    ext j
    simp
  rw [h, h, hammingDist_monomialEquiv]
  exact hammingDist_comp (fun _ ↦ σ) (fun _ ↦ σ.injective)

end Hamming

/-- Codes are semilinearly equivalent when a semilinear monomial transformation carries
one onto the other. The alphabet automorphism is shared by all coordinates. -/
def IsSemilinearEquivalent (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) : Prop :=
  ∃ (σ : R ≃+* R) (u : ι → Rˣ) (e : ι ≃ κ),
    C.map (semilinearMonomialEquiv σ u e).toLinearMap = D

variable {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}
  {E : Submodule R (μ → R)}

/-- Characterize semilinear equivalence by a semilinear image equality. -/
theorem isSemilinearEquivalent_iff : IsSemilinearEquivalent C D ↔
    ∃ (σ : R ≃+* R) (u : ι → Rˣ) (e : ι ≃ κ),
      C.map (semilinearMonomialEquiv σ u e).toLinearMap = D := Iff.rfl

/-- Monomial equivalence is semilinear equivalence with the identity alphabet automorphism. -/
theorem IsMonomialEquivalent.isSemilinearEquivalent (h : IsMonomialEquivalent C D) :
    IsSemilinearEquivalent C D := by
  obtain ⟨u, e, he⟩ := isMonomialEquivalent_iff.mp h
  exact ⟨RingEquiv.refl R, u, e, by simpa using he⟩

/-- Semilinear equivalence of codes is reflexive. -/
@[refl]
theorem IsSemilinearEquivalent.refl (C : Submodule R (ι → R)) :
    IsSemilinearEquivalent C C := (IsMonomialEquivalent.refl C).isSemilinearEquivalent

/-- Semilinear equivalence of codes is symmetric. -/
@[symm]
theorem IsSemilinearEquivalent.symm (h : IsSemilinearEquivalent C D) :
    IsSemilinearEquivalent D C := by
  obtain ⟨σ, u, e, he⟩ := h
  refine ⟨σ.symm, (fun j ↦ Units.map σ.symm.toMonoidHom (u (e.symm j))⁻¹), e.symm, ?_⟩
  have hinv := (Submodule.map_symm_eq_iff (semilinearMonomialEquiv σ u e)).2 he
  convert hinv using 1
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, semilinearMonomialEquiv_symm]

/-- Semilinear equivalence of codes is transitive. -/
@[trans]
theorem IsSemilinearEquivalent.trans (h : IsSemilinearEquivalent C D)
    (h' : IsSemilinearEquivalent D E) : IsSemilinearEquivalent C E := by
  obtain ⟨σ, u, e, rfl⟩ := h
  obtain ⟨τ, v, f, rfl⟩ := h'
  refine ⟨σ.trans τ, (fun i ↦ v (e i) * Units.map τ.toMonoidHom (u i)), e.trans f, ?_⟩
  ext z
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, semilinearMonomialEquiv_trans σ τ u v e f x⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, hx, (semilinearMonomialEquiv_trans σ τ u v e f x).symm.trans hz⟩

/-- Semilinearly equivalent codes have the same cardinality. -/
theorem IsSemilinearEquivalent.card_eq (h : IsSemilinearEquivalent C D) :
    Nat.card C = Nat.card D := by
  obtain ⟨σ, u, e, rfl⟩ := h
  exact Nat.card_congr ((semilinearMonomialEquiv σ u e).submoduleMap C).toEquiv

/-- Semilinearly equivalent codes have the same dimension. -/
theorem IsSemilinearEquivalent.finrank_eq (h : IsSemilinearEquivalent C D) :
    Module.finrank R C = Module.finrank R D := by
  obtain ⟨σ, u, e, rfl⟩ := h
  let g := (semilinearMonomialEquiv σ u e).submoduleMap C
  simpa only [Cardinal.toNat_lift, Module.finrank] using congrArg Cardinal.toNat
    (lift_rank_eq_of_equiv_equiv σ g.toAddEquiv σ.bijective (fun r x ↦ g.map_smulₛₗ r x))

section Invariants

variable [Fintype ι] [Fintype κ] [DecidableEq R]

/-- Semilinearly equivalent codes have the same minimum Hamming distance. -/
theorem IsSemilinearEquivalent.hammingMinDist_eq (h : IsSemilinearEquivalent C D) :
    (C : Set (ι → R)).hammingMinDist = (D : Set (κ → R)).hammingMinDist := by
  obtain ⟨σ, u, e, rfl⟩ := h
  exact (Set.hammingMinDist_image _
    (fun x _ y _ _ ↦ hammingDist_semilinearMonomialEquiv σ u e x y)).symm

/-- Semilinearly equivalent codes have the same weight distribution. -/
theorem IsSemilinearEquivalent.weightDistribution_eq (h : IsSemilinearEquivalent C D)
    (w : ℕ) :
    (C : Set (ι → R)).weightDistribution w = (D : Set (κ → R)).weightDistribution w := by
  obtain ⟨σ, u, e, rfl⟩ := h
  rw [Set.weightDistribution_def, Set.weightDistribution_def]
  exact Nat.card_congr
    (Equiv.subtypeEquiv (semilinearMonomialEquiv σ u e).toEquiv fun x ↦ by simp)

/-- Semilinearly equivalent codes have the same homogeneous weight enumerator. -/
theorem IsSemilinearEquivalent.weightEnumerator_eq (h : IsSemilinearEquivalent C D) :
    (C : Set (ι → R)).weightEnumerator = (D : Set (κ → R)).weightEnumerator := by
  have hcard : Fintype.card ι = Fintype.card κ := by
    obtain ⟨_, _, e, _⟩ := h
    exact Fintype.card_congr e
  simp_rw [Set.weightEnumerator_def, hcard, h.weightDistribution_eq]

/-- Semilinearly equivalent codes have the same one-variable weight polynomial. -/
theorem IsSemilinearEquivalent.weightPolynomial_eq (h : IsSemilinearEquivalent C D) :
    (C : Set (ι → R)).weightPolynomial = (D : Set (κ → R)).weightPolynomial := by
  rw [← Set.aeval_weightEnumerator, ← Set.aeval_weightEnumerator, h.weightEnumerator_eq]

end Invariants

end TauCeti
