/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.RingTheory.MvPolynomial.Monogenic.Basic
import Mathlib.Algebra.Algebra.Rat
import TauCeti.LinearAlgebra.Eigenspace.Anticommute
import TauCeti.LinearAlgebra.Eigenspace.Involution

/-!
# Chiral homogeneous and monogenic polynomials

Extending a chirality endomorphism `γ : Module.End R M` via `γ.lTensor (MvPolynomial σ R)`
preserves degree and defines `MvPolynomial.chiralHomogeneousSubmodule σ γ ε k` (isomorphic to
`homogeneousTensorSubmodule σ R (γ.eigenspace ε) k`) and
`MvPolynomial.chiralMonogenicSubmodule c γ ε k`. When `γ` anticommutes with every `cᵢ`, both
`cliffordMul c` and `cliffordDirac c` reverse `ε ↦ -ε`, giving the **chiral Clifford Fischer
decomposition**, `±1` chirality splittings when `γ ∘ₗ γ = 1` and `[Invertible (2 : R)]`, and
the rank `(card σ - 1).multichoose k * finrank K (γ.eigenspace ε)`.

## Main definitions

* `MvPolynomial.chiralHomogeneousSubmodule`, `MvPolynomial.chiralHomogeneousEquiv`,
  `MvPolynomial.chiralHomogeneousZeroEquiv`, and `MvPolynomial.chiralMonogenicSubmodule`.

## Main results

* `MvPolynomial.chiralHomogeneousSubmodule_sup_neg` and
  `MvPolynomial.chiralMonogenicSubmodule_sup_neg`.
* `MvPolynomial.disjoint_chiralMonogenicSubmodule_map_cliffordMul`,
  `MvPolynomial.chiralMonogenicSubmodule_sup_map_cliffordMul`, and
  `MvPolynomial.finrank_chiralMonogenicSubmodule`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Math. Series 38 (1989), Ch. II, §8.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section General

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem mem_eigenspace_lTensor_iff (γ : Module.End R M) (ε : R) (u : MvPolynomial σ R ⊗[R] M) :
    u ∈ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) ε ↔
      ∀ s : σ →₀ ℕ, coeffTensor s u ∈ γ.eigenspace ε := by
  simp only [Module.End.mem_eigenspace_iff]
  exact ⟨fun h s ↦ by rw [← coeffTensor_lTensor, h, map_smul],
    fun h ↦ ext_coeffTensor fun s ↦ by rw [coeffTensor_lTensor, h s, map_smul]⟩

variable (σ) in
/-- Degree-`k` `M`-valued homogeneous polynomials in the `ε`-eigenspace of `γ.lTensor`. -/
noncomputable def chiralHomogeneousSubmodule (γ : Module.End R M) (ε : R) (k : ℕ) :
    Submodule R (MvPolynomial σ R ⊗[R] M) :=
  homogeneousTensorSubmodule σ R M k ⊓ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) ε

@[simp] theorem mem_chiralHomogeneousSubmodule {γ : Module.End R M} {ε : R} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ chiralHomogeneousSubmodule σ γ ε k ↔
      u ∈ homogeneousTensorSubmodule σ R M k ∧ γ.lTensor (MvPolynomial σ R) u = ε • u := by
  rw [chiralHomogeneousSubmodule, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

theorem chiralHomogeneousSubmodule_le_homogeneousTensorSubmodule (γ : Module.End R M) (ε : R)
    (k : ℕ) : chiralHomogeneousSubmodule σ γ ε k ≤ homogeneousTensorSubmodule σ R M k := inf_le_left

@[simp] theorem chiralHomogeneousSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ] (γ : Module.End R M)
    (ε : R) (k : ℕ) : chiralHomogeneousSubmodule σ γ ε (k + 1) = ⊥ := by
  simp [chiralHomogeneousSubmodule]

private theorem subtype_lTensor_mem_chiralHomogeneousSubmodule (γ : Module.End R M) (ε : R)
    (k : ℕ) (x : homogeneousTensorSubmodule σ R (γ.eigenspace ε) k) :
    (((γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R)) ∘ₗ
        (homogeneousTensorSubmodule σ R (γ.eigenspace ε) k).subtype) x ∈
      chiralHomogeneousSubmodule σ γ ε k := by
  rw [LinearMap.comp_apply, Submodule.coe_subtype, chiralHomogeneousSubmodule, Submodule.mem_inf,
    mem_eigenspace_lTensor_iff]
  exact ⟨lTensor_mem_homogeneousTensorSubmodule (γ.eigenspace ε).subtype x.2, fun s ↦ by
    rw [coeffTensor_lTensor]; exact (coeffTensor s x.1).2⟩

private theorem subtype_lTensor_bijective (γ : Module.End R M) (ε : R) (k : ℕ) :
    Function.Bijective
      ((((γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R)) ∘ₗ
          (homogeneousTensorSubmodule σ R (γ.eigenspace ε) k).subtype).codRestrict
        (chiralHomogeneousSubmodule σ γ ε k)
        (subtype_lTensor_mem_chiralHomogeneousSubmodule γ ε k)) := by
  refine ⟨fun ⟨x, _⟩ ⟨y, _⟩ h ↦ Subtype.ext (ext_coeffTensor fun s ↦ ?_), fun ⟨u, hu⟩ ↦ ?_⟩
  · have hs := congrArg (fun z ↦ coeffTensor s z.1) h
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype,
      coeffTensor_lTensor] at hs
    exact Subtype.ext hs
  · obtain ⟨hu_hom, hγu⟩ := mem_chiralHomogeneousSubmodule.mp hu
    have hc := (mem_eigenspace_lTensor_iff γ ε u).mp (Module.End.mem_eigenspace_iff.mpr hγu)
    obtain ⟨I, hdeg, -, hsum⟩ := exists_finset_sum_monomial_tmul_coeffTensor hu_hom
    refine ⟨⟨∑ s ∈ I, monomial s (1 : R) ⊗ₜ[R] ⟨coeffTensor s u, hc s⟩,
      Submodule.sum_mem _ fun s hs ↦
        tmul_mem_homogeneousTensorSubmodule (isHomogeneous_monomial (1 : R) (hdeg s hs)) _⟩,
      Subtype.ext ?_⟩
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.coe_subtype, map_sum,
      LinearMap.lTensor_tmul, hsum]

variable (σ) in
/-- Canonical equivalence with `(γ.eigenspace ε)`-valued degree-`k` homogeneous polynomials. -/
noncomputable def chiralHomogeneousEquiv (γ : Module.End R M) (ε : R) (k : ℕ) :
    homogeneousTensorSubmodule σ R (γ.eigenspace ε) k ≃ₗ[R] chiralHomogeneousSubmodule σ γ ε k :=
  LinearEquiv.ofBijective _ (subtype_lTensor_bijective γ ε k)

@[simp] theorem coe_chiralHomogeneousEquiv_apply (γ : Module.End R M) (ε : R) (k : ℕ)
    (x : homogeneousTensorSubmodule σ R (γ.eigenspace ε) k) :
    (chiralHomogeneousEquiv σ γ ε k x : MvPolynomial σ R ⊗[R] M) =
      (γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R) x.1 := (rfl)

variable (σ) in
/-- Canonical linear equivalence `γ.eigenspace ε ≃ₗ[R] chiralHomogeneousSubmodule σ γ ε 0`. -/
noncomputable def chiralHomogeneousZeroEquiv (γ : Module.End R M) (ε : R) :
    γ.eigenspace ε ≃ₗ[R] chiralHomogeneousSubmodule σ γ ε 0 :=
  homogeneousTensorZeroEquiv σ R (γ.eigenspace ε) ≪≫ₗ chiralHomogeneousEquiv σ γ ε 0

@[simp] theorem coe_chiralHomogeneousZeroEquiv_apply (γ : Module.End R M) (ε : R)
    (m : γ.eigenspace ε) :
    (chiralHomogeneousZeroEquiv σ γ ε m : MvPolynomial σ R ⊗[R] M) = 1 ⊗ₜ[R] (m : M) := by
  simp [chiralHomogeneousZeroEquiv]

/-- Rank of `chiralHomogeneousSubmodule σ γ ε k` when `γ.eigenspace ε` is free over `R`. -/
theorem finrank_chiralHomogeneousSubmodule [StrongRankCondition R] [Fintype σ]
    (γ : Module.End R M) (ε : R) [Module.Free R (γ.eigenspace ε)] (k : ℕ) :
    Module.finrank R (chiralHomogeneousSubmodule σ γ ε k) =
      (Fintype.card σ).multichoose k * Module.finrank R (γ.eigenspace ε) := by
  rw [← (chiralHomogeneousEquiv σ γ ε k).finrank_eq, finrank_homogeneousTensorSubmodule]

end General

section Operators

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]

/-- Degree-`k` **chiral monogenic polynomials**: `monogenicSubmodule c k` on the `ε`-eigenspace. -/
noncomputable def chiralMonogenicSubmodule (c : σ → Module.End R M) (γ : Module.End R M)
    (ε : R) (k : ℕ) : Submodule R (MvPolynomial σ R ⊗[R] M) :=
  monogenicSubmodule c k ⊓ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) ε

@[simp] theorem mem_chiralMonogenicSubmodule {c : σ → Module.End R M} {γ : Module.End R M} {ε : R}
    {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ chiralMonogenicSubmodule c γ ε k ↔
      u ∈ chiralHomogeneousSubmodule σ γ ε k ∧ cliffordDirac c u = 0 := by
  rw [chiralMonogenicSubmodule, chiralHomogeneousSubmodule, Submodule.mem_inf, Submodule.mem_inf,
    mem_monogenicSubmodule, and_right_comm]

theorem chiralMonogenicSubmodule_le_monogenicSubmodule (c : σ → Module.End R M)
    (γ : Module.End R M) (ε : R) (k : ℕ) :
    chiralMonogenicSubmodule c γ ε k ≤ monogenicSubmodule c k := inf_le_left

theorem chiralMonogenicSubmodule_le_chiralHomogeneousSubmodule (c : σ → Module.End R M)
    (γ : Module.End R M) (ε : R) (k : ℕ) :
    chiralMonogenicSubmodule c γ ε k ≤ chiralHomogeneousSubmodule σ γ ε k :=
  fun _ hu ↦ (mem_chiralMonogenicSubmodule.mp hu).1

@[simp] theorem chiralMonogenicSubmodule_zero (c : σ → Module.End R M) (γ : Module.End R M)
    (ε : R) : chiralMonogenicSubmodule c γ ε 0 = chiralHomogeneousSubmodule σ γ ε 0 := by
  simp [chiralMonogenicSubmodule, chiralHomogeneousSubmodule]

@[simp] theorem chiralMonogenicSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ] (c : σ → Module.End R M)
    (γ : Module.End R M) (ε : R) (k : ℕ) : chiralMonogenicSubmodule c γ ε (k + 1) = ⊥ := by
  simp [chiralMonogenicSubmodule]

private theorem lTensor_comp_add_eq_zero {c : σ → Module.End R M} {γ : Module.End R M}
    {L : Module.End R (MvPolynomial σ R ⊗[R] M)} (f : σ → MvPolynomial σ R → MvPolynomial σ R)
    (hL : ∀ p m, L (p ⊗ₜ[R] m) = ∑ i : σ, f i p ⊗ₜ[R] c i m)
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) :
    γ.lTensor (MvPolynomial σ R) ∘ₗ L + L ∘ₗ γ.lTensor (MvPolynomial σ R) = 0 := by
  refine TensorProduct.ext' fun p m ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    LinearMap.lTensor_tmul, hL, map_sum, ← Finset.sum_add_distrib, ← TensorProduct.tmul_add]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi : γ (c i m) + c i (γ m) = 0 := by simpa using LinearMap.congr_fun (hγ_anti i) m
  rw [hi, TensorProduct.tmul_zero]

theorem lTensor_comp_cliffordMul_add_cliffordMul_comp_lTensor {c : σ → Module.End R M}
    {γ : Module.End R M} (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) :
    γ.lTensor (MvPolynomial σ R) ∘ₗ cliffordMul c +
      cliffordMul c ∘ₗ γ.lTensor (MvPolynomial σ R) = 0 :=
  lTensor_comp_add_eq_zero (X · * ·) (cliffordMul_tmul c) hγ_anti

theorem lTensor_comp_cliffordDirac_add_cliffordDirac_comp_lTensor {c : σ → Module.End R M}
    {γ : Module.End R M} (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) :
    γ.lTensor (MvPolynomial σ R) ∘ₗ cliffordDirac c +
      cliffordDirac c ∘ₗ γ.lTensor (MvPolynomial σ R) = 0 :=
  lTensor_comp_add_eq_zero (pderiv · ·) (cliffordDirac_tmul c) hγ_anti

theorem cliffordMul_mem_chiralHomogeneousSubmodule {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) {ε : R} {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ chiralHomogeneousSubmodule σ γ ε k) :
    cliffordMul c u ∈ chiralHomogeneousSubmodule σ γ (-ε) (k + 1) :=
  ⟨cliffordMul_mem_homogeneousTensorSubmodule hu.1,
    Module.End.mapsTo_genEigenspace_neg_of_anticommute
      (lTensor_comp_cliffordMul_add_cliffordMul_comp_lTensor hγ_anti) ε 1 hu.2⟩

theorem cliffordDirac_mem_chiralHomogeneousSubmodule {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) {ε : R} {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ chiralHomogeneousSubmodule σ γ ε k) :
    cliffordDirac c u ∈ chiralHomogeneousSubmodule σ γ (-ε) (k - 1) :=
  ⟨cliffordDirac_mem_homogeneousTensorSubmodule hu.1,
    Module.End.mapsTo_genEigenspace_neg_of_anticommute
      (lTensor_comp_cliffordDirac_add_cliffordDirac_comp_lTensor hγ_anti) ε 1 hu.2⟩

theorem lTensor_mem_monogenicSubmodule {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ monogenicSubmodule c k) : γ.lTensor (MvPolynomial σ R) u ∈ monogenicSubmodule c k :=
  mem_monogenicSubmodule.mpr
    ⟨lTensor_mem_homogeneousTensorSubmodule γ (mem_monogenicSubmodule.mp hu).1, by
      simpa [(mem_monogenicSubmodule.mp hu).2] using LinearMap.congr_fun
        (lTensor_comp_cliffordDirac_add_cliffordDirac_comp_lTensor hγ_anti) u⟩

end Operators

section Involution

variable {σ R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

private theorem disjoint_eigenspace_lTensor_one_neg_one (γ : Module.End R M) :
    Disjoint (Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) 1)
      (Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) (-1)) :=
  Submodule.disjoint_def.mpr fun u hu₁ hu₂ ↦ by
    have h2u : (2 : R) • u = 0 := by
      have h := (Module.End.mem_eigenspace_iff.mp hu₁).symm.trans
        (Module.End.mem_eigenspace_iff.mp hu₂)
      rw [one_smul, neg_one_smul] at h; rw [two_smul]; nth_rw 2 [h]; exact add_neg_cancel u
    simpa using congrArg ((⅟2 : R) • ·) h2u

private theorem inf_eigenspace_lTensor_sup_neg {N : Submodule R (MvPolynomial σ R ⊗[R] M)}
    {γ : Module.End R M} (hγ_sq : γ ∘ₗ γ = 1)
    (hN : ∀ u ∈ N, γ.lTensor (MvPolynomial σ R) u ∈ N) :
    (N ⊓ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) 1) ⊔
      (N ⊓ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) (-1)) = N := by
  have hT : Function.Involutive
      (γ.lTensor (MvPolynomial σ R) : Module.End R (MvPolynomial σ R ⊗[R] M)) := fun u ↦ by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hγ_sq]
    exact LinearMap.lTensor_id_apply (MvPolynomial σ R) M u
  have h1 : (1 : R) * 1 = 1 := one_mul 1
  have h2 : (-1 : R) * -1 = 1 := by ring
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun u hu ↦ Submodule.mem_sup.mpr
    ⟨Module.End.eigenProjOfInvolutive hT h1 u, ⟨?_, (Module.End.eigenProjOfInvolutive hT h1 u).2⟩,
      Module.End.eigenProjOfInvolutive hT h2 u, ⟨?_, (Module.End.eigenProjOfInvolutive hT h2 u).2⟩,
      Module.End.eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg hT h1 h2 u⟩
  · rw [Module.End.coe_eigenProjOfInvolutive_apply, one_smul]
    exact N.smul_mem _ (N.add_mem hu (hN u hu))
  · rw [Module.End.coe_eigenProjOfInvolutive_apply, neg_one_smul]
    exact N.smul_mem _ (N.add_mem hu (N.neg_mem (hN u hu)))

theorem disjoint_chiralHomogeneousSubmodule_neg (σ : Type*) (γ : Module.End R M) (k : ℕ) :
    Disjoint (chiralHomogeneousSubmodule σ γ 1 k) (chiralHomogeneousSubmodule σ γ (-1) k) :=
  (disjoint_eigenspace_lTensor_one_neg_one γ).mono inf_le_right inf_le_right

/-- `±1` chirality splitting of `homogeneousTensorSubmodule σ R M k` when `γ ∘ₗ γ = 1`. -/
theorem chiralHomogeneousSubmodule_sup_neg {γ : Module.End R M} (hγ_sq : γ ∘ₗ γ = 1)
    (σ : Type*) (k : ℕ) :
    chiralHomogeneousSubmodule σ γ 1 k ⊔ chiralHomogeneousSubmodule σ γ (-1) k =
      homogeneousTensorSubmodule σ R M k :=
  inf_eigenspace_lTensor_sup_neg hγ_sq fun _ ↦ lTensor_mem_homogeneousTensorSubmodule γ

theorem disjoint_chiralMonogenicSubmodule_neg [Fintype σ] (c : σ → Module.End R M)
    (γ : Module.End R M) (k : ℕ) :
    Disjoint (chiralMonogenicSubmodule c γ 1 k) (chiralMonogenicSubmodule c γ (-1) k) :=
  (disjoint_eigenspace_lTensor_one_neg_one γ).mono inf_le_right inf_le_right

/-- `±1` chirality splitting of `monogenicSubmodule c k` when `γ ∘ₗ γ = 1` and `γ` anticommutes. -/
theorem chiralMonogenicSubmodule_sup_neg [Fintype σ] {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_sq : γ ∘ₗ γ = 1) (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) (k : ℕ) :
    chiralMonogenicSubmodule c γ 1 k ⊔ chiralMonogenicSubmodule c γ (-1) k =
      monogenicSubmodule c k :=
  inf_eigenspace_lTensor_sup_neg hγ_sq fun _ ↦ lTensor_mem_monogenicSubmodule hγ_anti

end Involution

section Fischer

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]

/-- **Directness of the chiral Clifford Fischer decomposition**. -/
theorem disjoint_chiralMonogenicSubmodule_map_cliffordMul [HasUniqueDiv M] {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    (γ : Module.End R M) (ε : R) (k : ℕ) (N : Submodule R (MvPolynomial σ R ⊗[R] M)) :
    Disjoint (chiralMonogenicSubmodule c γ ε k) (N.map (cliffordMul c)) :=
  ((disjoint_ker_cliffordDirac_range_cliffordMul hc_sq hc_anti).mono_left
    ((chiralMonogenicSubmodule_le_monogenicSubmodule c γ ε k).trans
      (monogenicSubmodule_le_ker_cliffordDirac c k))).mono_right LinearMap.map_le_range

/-- **The chiral Clifford Fischer decomposition** over a commutative `ℚ`-algebra `R`. -/
theorem chiralMonogenicSubmodule_sup_map_cliffordMul [Algebra ℚ R] {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1) (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {γ : Module.End R M} (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) (ε : R) (k : ℕ) :
    chiralMonogenicSubmodule c γ ε (k + 1) ⊔
        (chiralHomogeneousSubmodule σ γ (-ε) k).map (cliffordMul c) =
      chiralHomogeneousSubmodule σ γ ε (k + 1) := by
  rcases isEmpty_or_nonempty σ with _ | ⟨⟨i₀⟩⟩
  · simp
  refine le_antisymm
    (sup_le (chiralMonogenicSubmodule_le_chiralHomogeneousSubmodule c γ ε (k + 1)) ?_)
    fun u hu_chiral ↦ ?_
  · rintro _ ⟨w, hw, rfl⟩
    simpa only [neg_neg] using cliffordMul_mem_chiralHomogeneousSubmodule hγ_anti hw
  · obtain ⟨hu, hγu⟩ := mem_chiralHomogeneousSubmodule.mp hu_chiral
    have : HasUniqueDiv M := @HasUniqueDiv.of_module_rat M _ (Module.compHom M (algebraMap ℚ R))
    obtain ⟨m, hm, _, ⟨w, hw, rfl⟩, rfl⟩ :=
      Submodule.mem_sup.mp (monogenicSubmodule_sup_map_cliffordMul hc_sq hc_anti k ▸ hu)
    set Γ : Module.End R (MvPolynomial σ R ⊗[R] M) := γ.lTensor (MvPolynomial σ R)
    have hΓX : Γ (cliffordMul c w) = -cliffordMul c (Γ w) := eq_neg_of_add_eq_zero_left
      (LinearMap.congr_fun (lTensor_comp_cliffordMul_add_cliffordMul_comp_lTensor hγ_anti) w)
    have heq : Γ m - ε • m = cliffordMul c (Γ w + ε • w) := by
      rw [map_add, hΓX, smul_add] at hγu
      calc Γ m - ε • m = (Γ m + -cliffordMul c (Γ w)) - (ε • m + ε • cliffordMul c w) +
            cliffordMul c (Γ w + ε • w) := by rw [map_add, map_smul]; abel
        _ = cliffordMul c (Γ w + ε • w) := by rw [hγu, sub_self, zero_add]
    have hzero : Γ m - ε • m = 0 :=
      (Submodule.disjoint_def.mp (disjoint_ker_cliffordDirac_range_cliffordMul hc_sq hc_anti)) _
        (monogenicSubmodule_le_ker_cliffordDirac c (k + 1)
          (Submodule.sub_mem _ (lTensor_mem_monogenicSubmodule hγ_anti hm)
            (Submodule.smul_mem _ ε hm))) ⟨Γ w + ε • w, heq.symm⟩
    have hw_zero : Γ w + ε • w = 0 := cliffordMul_injective
      (bijective_of_comp_self_eq_neg_one (hc_sq i₀)).1 (by rw [← heq, hzero, map_zero])
    exact Submodule.mem_sup.mpr
      ⟨m, ⟨hm, Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hzero)⟩, cliffordMul c w,
        ⟨w, ⟨hw, Module.End.mem_eigenspace_iff.mpr
          (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hw_zero)⟩, rfl⟩, rfl⟩

/-- **Chiral polynomial Cauchy-Kowalewskaya for `cliffordDirac`**. -/
theorem exists_cliffordDirac_eq_of_mem_chiralHomogeneousSubmodule [Algebra ℚ R]
    {c : σ → Module.End R M} {γ : Module.End R M} (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0)
    {i₀ : σ} (hc : Function.Bijective (c i₀)) {ε : R} {k : ℕ} {v : MvPolynomial σ R ⊗[R] M}
    (hv : v ∈ chiralHomogeneousSubmodule σ γ (-ε) k) :
    ∃ u ∈ chiralHomogeneousSubmodule σ γ ε (k + 1), cliffordDirac c u = v := by
  have hmap : (γ.eigenspace ε).map (c i₀) = γ.eigenspace (-ε) :=
    Module.End.map_genEigenspace_of_anticommute (LinearEquiv.ofBijective (c i₀) hc)
      (hγ_anti i₀) ε 1
  obtain ⟨u, hu, huP, -, hDu⟩ := exists_cliffordDirac_eq_of_mapsTo
    (P := γ.eigenspace ε) (Q := γ.eigenspace (-ε)) (fun m hm ↦ by simpa [← hmap] using hm)
    (fun j ↦ Module.End.mapsTo_genEigenspace_neg_of_anticommute (hγ_anti j) ε 1)
    hv.1 ((mem_eigenspace_lTensor_iff γ (-ε) v).mp hv.2)
  exact ⟨u, ⟨hu, (mem_eigenspace_lTensor_iff γ ε u).mpr huP⟩, hDu⟩

end Fischer

section Field

variable {σ K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]

omit [CharZero K] in
instance [Finite σ] [Module.Finite K M] (γ : Module.End K M) (ε : K) (k : ℕ) :
    FiniteDimensional K (chiralHomogeneousSubmodule σ γ ε k) :=
  Submodule.finiteDimensional_of_le (chiralHomogeneousSubmodule_le_homogeneousTensorSubmodule γ ε k)

variable [Fintype σ]

omit [CharZero K] in
instance [Module.Finite K M] (c : σ → Module.End K M) (γ : Module.End K M) (ε : K) (k : ℕ) :
    FiniteDimensional K (chiralMonogenicSubmodule c γ ε k) :=
  Submodule.finiteDimensional_of_le (chiralMonogenicSubmodule_le_monogenicSubmodule c γ ε k)

theorem finrank_chiralMonogenicSubmodule_add_finrank [Module.Finite K M] {c : σ → Module.End K M}
    {i₀ : σ} (hc : Function.Surjective (c i₀)) {γ : Module.End K M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) (ε : K) (k : ℕ) :
    Module.finrank K (chiralMonogenicSubmodule c γ ε (k + 1)) +
        Module.finrank K (chiralHomogeneousSubmodule σ γ (-ε) k) =
      Module.finrank K (chiralHomogeneousSubmodule σ γ ε (k + 1)) := by
  have hbij : Function.Bijective (c i₀) := ⟨LinearMap.injective_iff_surjective.mpr hc, hc⟩
  let Dk : chiralHomogeneousSubmodule σ γ ε (k + 1) →ₗ[K]
      chiralHomogeneousSubmodule σ γ (-ε) k :=
    { toFun := fun u ↦ ⟨cliffordDirac c u.1,
        by simpa using cliffordDirac_mem_chiralHomogeneousSubmodule hγ_anti u.2⟩
      map_add' := fun u v ↦ Subtype.ext (map_add (cliffordDirac c) u.1 v.1)
      map_smul' := fun r u ↦ Subtype.ext (map_smul (cliffordDirac c) r u.1) }
  have hsurj : Function.Surjective Dk := fun ⟨v, hv⟩ ↦
    let ⟨u, hu, hDu⟩ := exists_cliffordDirac_eq_of_mem_chiralHomogeneousSubmodule hγ_anti hbij hv
    ⟨⟨u, hu⟩, Subtype.ext hDu⟩
  have hker : LinearMap.ker Dk =
      (chiralMonogenicSubmodule c γ ε (k + 1)).comap
        (chiralHomogeneousSubmodule σ γ ε (k + 1)).subtype := by
    ext ⟨u, hu⟩; simp [Dk, mem_chiralMonogenicSubmodule, hu]
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := chiralHomogeneousSubmodule σ γ ε (k + 1))
    (V₂ := chiralHomogeneousSubmodule σ γ (-ε) k) Dk
  rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    (Submodule.comapSubtypeEquivOfLe
      (chiralMonogenicSubmodule_le_chiralHomogeneousSubmodule c γ ε (k + 1))).finrank_eq,
    add_comm] at h

/-- **Dimension of `chiralMonogenicSubmodule c γ ε k`** over a field of characteristic zero. -/
theorem finrank_chiralMonogenicSubmodule [Module.Finite K M] {c : σ → Module.End K M} {i₀ : σ}
    (hc : Function.Surjective (c i₀)) {γ : Module.End K M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) (ε : K) (k : ℕ) :
    Module.finrank K (chiralMonogenicSubmodule c γ ε k) =
      (Fintype.card σ - 1).multichoose k * Module.finrank K (γ.eigenspace ε) := by
  have : Nonempty σ := ⟨i₀⟩
  rcases k with _ | k
  · rw [chiralMonogenicSubmodule_zero, ← (chiralHomogeneousZeroEquiv σ γ ε).finrank_eq,
      Nat.multichoose_zero_right, one_mul]
  · have heig : Module.finrank K (γ.eigenspace (-ε)) = Module.finrank K (γ.eigenspace ε) :=
      Module.End.finrank_genEigenspace_neg_of_anticommute
        (LinearEquiv.ofBijective (c i₀) ⟨LinearMap.injective_iff_surjective.mpr hc, hc⟩)
        (hγ_anti i₀) ε 1
    have h := finrank_chiralMonogenicSubmodule_add_finrank hc hγ_anti ε k
    rw [finrank_chiralHomogeneousSubmodule, finrank_chiralHomogeneousSubmodule, heig] at h
    have ⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 := ⟨_, (Nat.sub_add_cancel Fintype.card_pos).symm⟩
    rw [hm, Nat.add_sub_cancel]; rw [hm, Nat.multichoose_succ_succ, add_mul] at h
    exact Nat.add_right_cancel h

end Field

end MvPolynomial
