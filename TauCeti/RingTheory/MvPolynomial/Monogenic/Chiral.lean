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

Given an `R`-module `M` equipped with a grading or chirality endomorphism `γ : Module.End R M`,
extending `γ` along the polynomial factor via `γ.lTensor (MvPolynomial σ R)` preserves homogeneous
degree. For each scalar `ε : R` and degree `k : ℕ`, this cuts out:

* **the chiral homogeneous submodule** `MvPolynomial.chiralHomogeneousSubmodule σ γ ε k`, the
  intersection of `homogeneousTensorSubmodule σ R M k` with the `ε`-eigenspace of
  `γ.lTensor (MvPolynomial σ R)`, canonically isomorphic to `(γ.eigenspace ε)`-valued homogeneous
  polynomials (`MvPolynomial.chiralHomogeneousEquiv`);
* **the chiral monogenic submodule** `MvPolynomial.chiralMonogenicSubmodule c γ ε k`, the
  intersection of `monogenicSubmodule c k` with the `ε`-eigenspace of
  `γ.lTensor (MvPolynomial σ R)`.

When `γ` anticommutes with every coordinate operator `cᵢ` (`γ ∘ₗ cᵢ + cᵢ ∘ₗ γ = 0`), both
`cliffordMul c` and `cliffordDirac c` anticommute with `γ.lTensor (MvPolynomial σ R)` and therefore
reverse the eigenvalue `ε ↦ -ε`. Under the Riemannian Clifford relations `cᵢ ∘ₗ cᵢ = -1` and
`cᵢ ∘ₗ cⱼ + cⱼ ∘ₗ cᵢ = 0` (`i ≠ j`), this yields the **chiral Clifford Fischer decomposition**
`chiralHomogeneousSubmodule σ γ ε (k + 1) =
  chiralMonogenicSubmodule c γ ε (k + 1) ⊔ (chiralHomogeneousSubmodule σ γ (-ε) k).map X`
over any commutative `ℚ`-algebra `R`, for every `ε : R` without assuming `γ ∘ₗ γ = 1`.

When `γ ∘ₗ γ = 1` and `2` is invertible in `R`, the `+1` and `-1` chiral pieces split both
`homogeneousTensorSubmodule σ R M k` and `monogenicSubmodule c k`. Over a field `K` of
characteristic zero, chiral Cauchy-Kowalewskaya along a single surjective coordinate operator
`c i₀` gives the rank formula
`finrank K (chiralMonogenicSubmodule c γ ε k) =
  (card σ - 1).multichoose k * finrank K (γ.eigenspace ε)`
without requiring the Clifford relations or `γ ∘ₗ γ = 1`.

## Main definitions

* `MvPolynomial.chiralHomogeneousSubmodule σ γ ε k`: degree-`k` polynomials in the `ε`-eigenspace of
  `γ.lTensor (MvPolynomial σ R)`.
* `MvPolynomial.chiralHomogeneousEquiv σ γ ε k`: canonical linear equivalence between
  `homogeneousTensorSubmodule σ R (γ.eigenspace ε) k` and `chiralHomogeneousSubmodule σ γ ε k`.
* `MvPolynomial.chiralHomogeneousZeroEquiv σ γ ε`: canonical linear equivalence between
  `γ.eigenspace ε` and `chiralHomogeneousSubmodule σ γ ε 0`.
* `MvPolynomial.chiralMonogenicSubmodule c γ ε k`: degree-`k` monogenic polynomials in the
  `ε`-eigenspace of `γ.lTensor (MvPolynomial σ R)`.

## Main results

* `MvPolynomial.cliffordMul_mem_chiralHomogeneousSubmodule` and
  `MvPolynomial.cliffordDirac_mem_chiralHomogeneousSubmodule`: `X` and `D` send eigenvalue `ε` to
  `-ε`.
* `MvPolynomial.chiralHomogeneousSubmodule_sup_neg` and
  `MvPolynomial.chiralMonogenicSubmodule_sup_neg`: `±1` involution splittings when `γ ∘ₗ γ = 1` and
  `2` is invertible.
* `MvPolynomial.disjoint_chiralMonogenicSubmodule_map_cliffordMul` and
  `MvPolynomial.chiralMonogenicSubmodule_sup_map_cliffordMul`: directness and spanning of the chiral
  Clifford Fischer decomposition.
* `MvPolynomial.exists_cliffordDirac_eq_of_mem_chiralHomogeneousSubmodule`: chiral polynomial
  Cauchy-Kowalewskaya when some `c i₀` is bijective.
* `MvPolynomial.finrank_chiralMonogenicSubmodule`: rank of `chiralMonogenicSubmodule c γ ε k` over a
  field of characteristic zero.

## References

* R. Delanghe, F. Sommen, and V. Souček, *Clifford Algebra and Spinor-Valued Functions*,
  Mathematics and its Applications 53, Kluwer Academic Publishers (1992).
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton Mathematical Series 38 (1989),
  Chapter II, §8.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section General

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An `M`-valued polynomial lies in the `ε`-eigenspace of `γ.lTensor (MvPolynomial σ R)` iff every
monomial coefficient lies in `γ.eigenspace ε`. -/
theorem mem_eigenspace_lTensor_iff (γ : Module.End R M) (ε : R) (u : MvPolynomial σ R ⊗[R] M) :
    u ∈ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) ε ↔
      ∀ s : σ →₀ ℕ, coeffTensor s u ∈ γ.eigenspace ε := by
  simp only [Module.End.mem_eigenspace_iff]
  refine ⟨fun h s ↦ by rw [← coeffTensor_lTensor, h, map_smul],
    fun h ↦ ext_coeffTensor fun s ↦ by rw [coeffTensor_lTensor, h s, map_smul]⟩

variable (σ) in
/-- The submodule of `M`-valued homogeneous polynomials of degree `k` on which
`γ.lTensor (MvPolynomial σ R)` acts by the scalar `ε`. -/
noncomputable def chiralHomogeneousSubmodule (γ : Module.End R M) (ε : R) (k : ℕ) :
    Submodule R (MvPolynomial σ R ⊗[R] M) :=
  homogeneousTensorSubmodule σ R M k ⊓ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) ε

/-- Membership in `chiralHomogeneousSubmodule σ γ ε k` is degree-`k` homogeneity together with the
eigenvalue equation `γ.lTensor (MvPolynomial σ R) u = ε • u`. -/
@[simp]
theorem mem_chiralHomogeneousSubmodule {γ : Module.End R M} {ε : R} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ chiralHomogeneousSubmodule σ γ ε k ↔
      u ∈ homogeneousTensorSubmodule σ R M k ∧ γ.lTensor (MvPolynomial σ R) u = ε • u := by
  rw [chiralHomogeneousSubmodule, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

/-- Every chiral homogeneous polynomial of degree `k` is homogeneous of degree `k`. -/
theorem chiralHomogeneousSubmodule_le_homogeneousTensorSubmodule
    (γ : Module.End R M) (ε : R) (k : ℕ) :
    chiralHomogeneousSubmodule σ γ ε k ≤ homogeneousTensorSubmodule σ R M k :=
  inf_le_left

/-- When `σ` is empty, all positive-degree chiral homogeneous submodules vanish. -/
@[simp]
theorem chiralHomogeneousSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ]
    (γ : Module.End R M) (ε : R) (k : ℕ) :
    chiralHomogeneousSubmodule σ γ ε (k + 1) = ⊥ := by
  simp [chiralHomogeneousSubmodule]

private theorem subtype_lTensor_mem_chiralHomogeneousSubmodule (γ : Module.End R M) (ε : R)
    (k : ℕ) (x : homogeneousTensorSubmodule σ R (γ.eigenspace ε) k) :
    (γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R) x.1 ∈
      chiralHomogeneousSubmodule σ γ ε k := by
  rw [chiralHomogeneousSubmodule, Submodule.mem_inf, mem_eigenspace_lTensor_iff]
  refine ⟨lTensor_mem_homogeneousTensorSubmodule (γ.eigenspace ε).subtype x.2, fun s ↦ ?_⟩
  rw [coeffTensor_lTensor]
  exact (coeffTensor s x.1).2

private theorem subtype_lTensor_bijective (γ : Module.End R M) (ε : R) (k : ℕ) :
    Function.Bijective
      ((((γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R)) ∘ₗ
          (homogeneousTensorSubmodule σ R (γ.eigenspace ε) k).subtype).codRestrict
        (chiralHomogeneousSubmodule σ γ ε k)
        (subtype_lTensor_mem_chiralHomogeneousSubmodule γ ε k)) := by
  refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ h ↦ Subtype.ext (ext_coeffTensor fun s ↦ ?_), fun ⟨u, hu⟩ ↦ ?_⟩
  · have hs : coeffTensor s ((γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R) x) =
        coeffTensor s ((γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R) y) :=
      congrArg (fun z ↦ coeffTensor s z.1) h
    rw [coeffTensor_lTensor, coeffTensor_lTensor] at hs
    exact Subtype.ext hs
  · obtain ⟨hu_hom, hγu⟩ := mem_chiralHomogeneousSubmodule.mp hu
    have hc : ∀ s, coeffTensor s u ∈ γ.eigenspace ε :=
      (mem_eigenspace_lTensor_iff γ ε u).mp (Module.End.mem_eigenspace_iff.mpr hγu)
    obtain ⟨I, hdeg, -, hsum⟩ := exists_finset_sum_monomial_tmul_coeffTensor hu_hom
    let x : MvPolynomial σ R ⊗[R] γ.eigenspace ε :=
      ∑ s ∈ I, monomial s (1 : R) ⊗ₜ[R] ⟨coeffTensor s u, hc s⟩
    have hx : x ∈ homogeneousTensorSubmodule σ R (γ.eigenspace ε) k :=
      Submodule.sum_mem _ fun s hs ↦
        tmul_mem_homogeneousTensorSubmodule (isHomogeneous_monomial (1 : R) (hdeg s hs)) _
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change (γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R) x = u
    simp only [x, map_sum, LinearMap.lTensor_tmul, Submodule.coe_subtype, hsum]

variable (σ) in
/-- Canonical linear equivalence identifying `(γ.eigenspace ε)`-valued homogeneous polynomials of
degree `k` with `chiralHomogeneousSubmodule σ γ ε k`. -/
noncomputable def chiralHomogeneousEquiv (γ : Module.End R M) (ε : R) (k : ℕ) :
    homogeneousTensorSubmodule σ R (γ.eigenspace ε) k ≃ₗ[R]
      chiralHomogeneousSubmodule σ γ ε k :=
  LinearEquiv.ofBijective _ (subtype_lTensor_bijective γ ε k)

/-- `chiralHomogeneousEquiv` acts by extending `(γ.eigenspace ε).subtype` along the polynomial
factor. -/
@[simp]
theorem coe_chiralHomogeneousEquiv_apply (γ : Module.End R M) (ε : R) (k : ℕ)
    (x : homogeneousTensorSubmodule σ R (γ.eigenspace ε) k) :
    (chiralHomogeneousEquiv σ γ ε k x : MvPolynomial σ R ⊗[R] M) =
      (γ.eigenspace ε).subtype.lTensor (MvPolynomial σ R) x.1 :=
  (rfl)

variable (σ) in
/-- Canonical linear equivalence identifying `γ.eigenspace ε` with the degree-zero chiral
homogeneous polynomials `chiralHomogeneousSubmodule σ γ ε 0`, sending `m` to `1 ⊗ₜ m.1`. -/
noncomputable def chiralHomogeneousZeroEquiv (γ : Module.End R M) (ε : R) :
    γ.eigenspace ε ≃ₗ[R] chiralHomogeneousSubmodule σ γ ε 0 :=
  homogeneousTensorZeroEquiv σ R (γ.eigenspace ε) ≪≫ₗ chiralHomogeneousEquiv σ γ ε 0

/-- `chiralHomogeneousZeroEquiv` sends `m : γ.eigenspace ε` to `1 ⊗ₜ m.1`. -/
@[simp]
theorem coe_chiralHomogeneousZeroEquiv_apply (γ : Module.End R M) (ε : R) (m : γ.eigenspace ε) :
    (chiralHomogeneousZeroEquiv σ γ ε m : MvPolynomial σ R ⊗[R] M) = 1 ⊗ₜ[R] (m : M) := by
  simp [chiralHomogeneousZeroEquiv]

/-- When `γ.eigenspace ε` is free over `R`, the rank of `chiralHomogeneousSubmodule σ γ ε k` is
`(Fintype.card σ).multichoose k * Module.finrank R (γ.eigenspace ε)`. -/
theorem finrank_chiralHomogeneousSubmodule [StrongRankCondition R] [Fintype σ]
    (γ : Module.End R M) (ε : R) [Module.Free R (γ.eigenspace ε)] (k : ℕ) :
    Module.finrank R (chiralHomogeneousSubmodule σ γ ε k) =
      (Fintype.card σ).multichoose k * Module.finrank R (γ.eigenspace ε) := by
  rw [← (chiralHomogeneousEquiv σ γ ε k).finrank_eq, finrank_homogeneousTensorSubmodule]

end General

section Operators

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]

/-- The **degree-`k` chiral monogenic submodule**: homogeneous polynomials of degree `k` in both
`ker (cliffordDirac c)` and the `ε`-eigenspace of `γ.lTensor (MvPolynomial σ R)`. -/
noncomputable def chiralMonogenicSubmodule (c : σ → Module.End R M) (γ : Module.End R M)
    (ε : R) (k : ℕ) : Submodule R (MvPolynomial σ R ⊗[R] M) :=
  monogenicSubmodule c k ⊓ Module.End.eigenspace (γ.lTensor (MvPolynomial σ R)) ε

/-- Membership in `chiralMonogenicSubmodule c γ ε k` is membership in
`chiralHomogeneousSubmodule σ γ ε k` together with `cliffordDirac c u = 0`. -/
@[simp]
theorem mem_chiralMonogenicSubmodule {c : σ → Module.End R M} {γ : Module.End R M} {ε : R} {k : ℕ}
    {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ chiralMonogenicSubmodule c γ ε k ↔
      u ∈ chiralHomogeneousSubmodule σ γ ε k ∧ cliffordDirac c u = 0 := by
  rw [chiralMonogenicSubmodule, chiralHomogeneousSubmodule, Submodule.mem_inf, Submodule.mem_inf,
    mem_monogenicSubmodule, and_right_comm]

/-- Every chiral monogenic polynomial of degree `k` is monogenic of degree `k`. -/
theorem chiralMonogenicSubmodule_le_monogenicSubmodule (c : σ → Module.End R M)
    (γ : Module.End R M) (ε : R) (k : ℕ) :
    chiralMonogenicSubmodule c γ ε k ≤ monogenicSubmodule c k :=
  inf_le_left

/-- Every chiral monogenic polynomial of degree `k` is chiral homogeneous of degree `k`. -/
theorem chiralMonogenicSubmodule_le_chiralHomogeneousSubmodule (c : σ → Module.End R M)
    (γ : Module.End R M) (ε : R) (k : ℕ) :
    chiralMonogenicSubmodule c γ ε k ≤ chiralHomogeneousSubmodule σ γ ε k :=
  fun _ hu ↦ (mem_chiralMonogenicSubmodule.mp hu).1

/-- In degree zero, `chiralMonogenicSubmodule c γ ε 0` coincides with
`chiralHomogeneousSubmodule σ γ ε 0`. -/
@[simp]
theorem chiralMonogenicSubmodule_zero (c : σ → Module.End R M) (γ : Module.End R M) (ε : R) :
    chiralMonogenicSubmodule c γ ε 0 = chiralHomogeneousSubmodule σ γ ε 0 := by
  simp [chiralMonogenicSubmodule, chiralHomogeneousSubmodule]

/-- When `σ` is empty, all positive-degree chiral monogenic submodules vanish. -/
@[simp]
theorem chiralMonogenicSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ]
    (c : σ → Module.End R M) (γ : Module.End R M) (ε : R) (k : ℕ) :
    chiralMonogenicSubmodule c γ ε (k + 1) = ⊥ := by
  simp [chiralMonogenicSubmodule]

/-- If `γ` anticommutes with every coordinate operator `c i`, then `γ.lTensor (MvPolynomial σ R)`
anticommutes with `cliffordMul c`. -/
theorem lTensor_comp_cliffordMul_add_cliffordMul_comp_lTensor
    {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) :
    γ.lTensor (MvPolynomial σ R) ∘ₗ cliffordMul c +
      cliffordMul c ∘ₗ γ.lTensor (MvPolynomial σ R) = 0 := by
  apply TensorProduct.ext'
  intro p m
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    cliffordMul_tmul, LinearMap.lTensor_tmul, map_sum, ← Finset.sum_add_distrib,
    ← TensorProduct.tmul_add]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi := LinearMap.congr_fun (hγ_anti i) m
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hi
  rw [hi, TensorProduct.tmul_zero]

/-- If `γ` anticommutes with every coordinate operator `c i`, then `γ.lTensor (MvPolynomial σ R)`
anticommutes with `cliffordDirac c`. -/
theorem lTensor_comp_cliffordDirac_add_cliffordDirac_comp_lTensor
    {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) :
    γ.lTensor (MvPolynomial σ R) ∘ₗ cliffordDirac c +
      cliffordDirac c ∘ₗ γ.lTensor (MvPolynomial σ R) = 0 := by
  apply TensorProduct.ext'
  intro p m
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    cliffordDirac_tmul, LinearMap.lTensor_tmul, map_sum, ← Finset.sum_add_distrib,
    ← TensorProduct.tmul_add]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hi := LinearMap.congr_fun (hγ_anti i) m
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hi
  rw [hi, TensorProduct.tmul_zero]

/-- When `γ` anticommutes with `c`, `cliffordMul c` maps `chiralHomogeneousSubmodule σ γ ε k` into
`chiralHomogeneousSubmodule σ γ (-ε) (k + 1)`. -/
theorem cliffordMul_mem_chiralHomogeneousSubmodule
    {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) {ε : R} {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ chiralHomogeneousSubmodule σ γ ε k) :
    cliffordMul c u ∈ chiralHomogeneousSubmodule σ γ (-ε) (k + 1) := by
  rw [chiralHomogeneousSubmodule, Submodule.mem_inf] at hu ⊢
  exact ⟨cliffordMul_mem_homogeneousTensorSubmodule hu.1,
    Module.End.mapsTo_genEigenspace_neg_of_anticommute
      (lTensor_comp_cliffordMul_add_cliffordMul_comp_lTensor hγ_anti) ε 1 hu.2⟩

/-- When `γ` anticommutes with `c`, `cliffordDirac c` maps `chiralHomogeneousSubmodule σ γ ε k` into
`chiralHomogeneousSubmodule σ γ (-ε) (k - 1)`. -/
theorem cliffordDirac_mem_chiralHomogeneousSubmodule
    {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) {ε : R} {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ chiralHomogeneousSubmodule σ γ ε k) :
    cliffordDirac c u ∈ chiralHomogeneousSubmodule σ γ (-ε) (k - 1) := by
  rw [chiralHomogeneousSubmodule, Submodule.mem_inf] at hu ⊢
  exact ⟨cliffordDirac_mem_homogeneousTensorSubmodule hu.1,
    Module.End.mapsTo_genEigenspace_neg_of_anticommute
      (lTensor_comp_cliffordDirac_add_cliffordDirac_comp_lTensor hγ_anti) ε 1 hu.2⟩

/-- When `γ` anticommutes with `c`, `γ.lTensor (MvPolynomial σ R)` preserves
`monogenicSubmodule c k`. -/
theorem lTensor_mem_monogenicSubmodule
    {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ monogenicSubmodule c k) :
    γ.lTensor (MvPolynomial σ R) u ∈ monogenicSubmodule c k := by
  rw [mem_monogenicSubmodule] at hu ⊢
  refine ⟨lTensor_mem_homogeneousTensorSubmodule γ hu.1, ?_⟩
  have h := LinearMap.congr_fun
    (lTensor_comp_cliffordDirac_add_cliffordDirac_comp_lTensor hγ_anti) u
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply,
    hu.2, map_zero, zero_add] at h
  exact h

end Operators

section Involution

variable {σ R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

private theorem disjoint_inf_eigenspace_one_neg_one {V : Type*} [AddCommGroup V] [Module R V]
    (N : Submodule R V) (T : Module.End R V) :
    Disjoint (N ⊓ T.eigenspace 1) (N ⊓ T.eigenspace (-1)) := by
  rw [Submodule.disjoint_def]
  intro x hx₁ hx₂
  have h₁ : T x = x := by
    simpa using Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hx₁).2
  have h₂ : T x = -x := by
    simpa using Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hx₂).2
  have h2x : (2 : R) • x = 0 := by
    rw [two_smul]
    calc x + x = x + -x := by rw [← h₁.symm.trans h₂]
      _ = 0 := add_neg_cancel x
  simpa using congrArg ((⅟2 : R) • ·) h2x

private theorem inf_eigenspace_one_sup_neg_one_of_mapsTo {V : Type*} [AddCommGroup V] [Module R V]
    {N : Submodule R V} {T : Module.End R V} (hT : Function.Involutive T)
    (hN : ∀ x ∈ N, T x ∈ N) :
    (N ⊓ T.eigenspace 1) ⊔ (N ⊓ T.eigenspace (-1)) = N := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx ↦ ?_
  have h1 : (1 : R) * 1 = 1 := one_mul 1
  have h2 : (-1 : R) * -1 = 1 := by ring
  let p1 : V := Module.End.eigenProjOfInvolutive hT h1 x
  let p2 : V := Module.End.eigenProjOfInvolutive hT h2 x
  have hp1 : p1 ∈ N := by
    dsimp [p1]
    rw [Module.End.coe_eigenProjOfInvolutive_apply, one_smul]
    exact N.smul_mem _ (N.add_mem hx (hN x hx))
  have hp2 : p2 ∈ N := by
    dsimp [p2]
    rw [Module.End.coe_eigenProjOfInvolutive_apply, neg_one_smul]
    exact N.smul_mem _ (N.add_mem hx (N.neg_mem (hN x hx)))
  exact Submodule.mem_sup.mpr
    ⟨p1, ⟨hp1, (Module.End.eigenProjOfInvolutive hT h1 x).2⟩,
      p2, ⟨hp2, (Module.End.eigenProjOfInvolutive hT h2 x).2⟩,
      Module.End.eigenProjOfInvolutive_add_eigenProjOfInvolutive_neg hT h1 h2 x⟩

omit [Invertible (2 : R)] in
private theorem involutive_lTensor_of_comp_self_eq_one {γ : Module.End R M} (hγ_sq : γ ∘ₗ γ = 1) :
    Function.Involutive (γ.lTensor (MvPolynomial σ R) : Module.End R (MvPolynomial σ R ⊗[R] M)) :=
  fun u ↦ by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hγ_sq]
    exact LinearMap.lTensor_id_apply (MvPolynomial σ R) M u

/-- When `2` is invertible in `R`, the `+1` and `-1` chiral homogeneous submodules of degree `k` are
disjoint. -/
theorem disjoint_chiralHomogeneousSubmodule_neg (σ : Type*) (γ : Module.End R M) (k : ℕ) :
    Disjoint (chiralHomogeneousSubmodule σ γ 1 k) (chiralHomogeneousSubmodule σ γ (-1) k) := by
  rw [chiralHomogeneousSubmodule, chiralHomogeneousSubmodule]
  exact disjoint_inf_eigenspace_one_neg_one (homogeneousTensorSubmodule σ R M k)
    (γ.lTensor (MvPolynomial σ R))

/-- When `γ ∘ₗ γ = 1` and `2` is invertible in `R`, `homogeneousTensorSubmodule σ R M k` splits into
its `+1` and `-1` chiral submodules. -/
theorem chiralHomogeneousSubmodule_sup_neg {γ : Module.End R M} (hγ_sq : γ ∘ₗ γ = 1)
    (σ : Type*) (k : ℕ) :
    chiralHomogeneousSubmodule σ γ 1 k ⊔ chiralHomogeneousSubmodule σ γ (-1) k =
      homogeneousTensorSubmodule σ R M k := by
  rw [chiralHomogeneousSubmodule, chiralHomogeneousSubmodule]
  exact inf_eigenspace_one_sup_neg_one_of_mapsTo
    (T := (γ.lTensor (MvPolynomial σ R) : Module.End R (MvPolynomial σ R ⊗[R] M)))
    (involutive_lTensor_of_comp_self_eq_one hγ_sq)
    fun _ hu ↦ lTensor_mem_homogeneousTensorSubmodule γ hu

/-- When `2` is invertible in `R`, the `+1` and `-1` chiral monogenic submodules of degree `k` are
disjoint. -/
theorem disjoint_chiralMonogenicSubmodule_neg [Fintype σ] (c : σ → Module.End R M)
    (γ : Module.End R M) (k : ℕ) :
    Disjoint (chiralMonogenicSubmodule c γ 1 k) (chiralMonogenicSubmodule c γ (-1) k) := by
  rw [chiralMonogenicSubmodule, chiralMonogenicSubmodule]
  exact disjoint_inf_eigenspace_one_neg_one (monogenicSubmodule c k)
    (γ.lTensor (MvPolynomial σ R))

/-- When `γ ∘ₗ γ = 1`, `γ` anticommutes with `c`, and `2` is invertible in `R`,
`monogenicSubmodule c k` splits into its `+1` and `-1` chiral monogenic submodules. -/
theorem chiralMonogenicSubmodule_sup_neg [Fintype σ] {c : σ → Module.End R M}
    {γ : Module.End R M} (hγ_sq : γ ∘ₗ γ = 1) (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) (k : ℕ) :
    chiralMonogenicSubmodule c γ 1 k ⊔ chiralMonogenicSubmodule c γ (-1) k =
      monogenicSubmodule c k := by
  rw [chiralMonogenicSubmodule, chiralMonogenicSubmodule]
  exact inf_eigenspace_one_sup_neg_one_of_mapsTo
    (T := (γ.lTensor (MvPolynomial σ R) : Module.End R (MvPolynomial σ R ⊗[R] M)))
    (involutive_lTensor_of_comp_self_eq_one hγ_sq)
    fun _ hu ↦ lTensor_mem_monogenicSubmodule hγ_anti hu

end Involution

section Fischer

variable {σ R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype σ]

/-- **Directness of the chiral Clifford Fischer decomposition**: under `[HasUniqueDiv M]` and the
Clifford relations on `c`, `chiralMonogenicSubmodule c γ ε k` is disjoint from the image of any
submodule under `cliffordMul c`. -/
theorem disjoint_chiralMonogenicSubmodule_map_cliffordMul [HasUniqueDiv M]
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    (γ : Module.End R M) (ε : R) (k : ℕ) (N : Submodule R (MvPolynomial σ R ⊗[R] M)) :
    Disjoint (chiralMonogenicSubmodule c γ ε k) (N.map (cliffordMul c)) :=
  ((disjoint_ker_cliffordDirac_range_cliffordMul hc_sq hc_anti).mono_left
    ((chiralMonogenicSubmodule_le_monogenicSubmodule c γ ε k).trans
      (monogenicSubmodule_le_ker_cliffordDirac c k))).mono_right LinearMap.map_le_range

/-- **The chiral Clifford Fischer decomposition**: over any commutative `ℚ`-algebra `R`, when `c`
satisfies the Riemannian Clifford relations and `γ` anticommutes with `c`, every chiral homogeneous
polynomial of degree `k + 1` and eigenvalue `ε` decomposes into a chiral monogenic polynomial of
degree `k + 1` and eigenvalue `ε` plus `cliffordMul c` applied to a chiral homogeneous polynomial of
degree `k` and eigenvalue `-ε`. -/
theorem chiralMonogenicSubmodule_sup_map_cliffordMul [Algebra ℚ R]
    {c : σ → Module.End R M}
    (hc_sq : ∀ i, c i ∘ₗ c i = -1)
    (hc_anti : Pairwise fun i j ↦ c i ∘ₗ c j + c j ∘ₗ c i = 0)
    {γ : Module.End R M} (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0)
    (ε : R) (k : ℕ) :
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
    have hsplit : u ∈ monogenicSubmodule c (k + 1) ⊔
        (homogeneousTensorSubmodule σ R M k).map (cliffordMul c) :=
      monogenicSubmodule_sup_map_cliffordMul hc_sq hc_anti k ▸ hu
    obtain ⟨m, hm, _, ⟨w, hw, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hsplit
    set Γ : Module.End R (MvPolynomial σ R ⊗[R] M) := γ.lTensor (MvPolynomial σ R)
    have hΓX : Γ (cliffordMul c w) = -cliffordMul c (Γ w) :=
      eq_neg_of_add_eq_zero_left
        (LinearMap.congr_fun (lTensor_comp_cliffordMul_add_cliffordMul_comp_lTensor hγ_anti) w)
    have heq : Γ m - ε • m = cliffordMul c (Γ w + ε • w) := by
      have h : Γ (m + cliffordMul c w) = ε • (m + cliffordMul c w) := hγu
      rw [map_add, hΓX, smul_add] at h
      calc Γ m - ε • m = (Γ m + -cliffordMul c (Γ w)) - (ε • m + ε • cliffordMul c w) +
            cliffordMul c (Γ w + ε • w) := by rw [map_add, map_smul]; abel
        _ = cliffordMul c (Γ w + ε • w) := by rw [h, sub_self, zero_add]
    have hmem_m : Γ m - ε • m ∈ monogenicSubmodule c (k + 1) :=
      Submodule.sub_mem _ (lTensor_mem_monogenicSubmodule hγ_anti hm) (Submodule.smul_mem _ ε hm)
    have hzero : Γ m - ε • m = 0 :=
      (Submodule.disjoint_def.mp (disjoint_ker_cliffordDirac_range_cliffordMul hc_sq hc_anti))
        _ (monogenicSubmodule_le_ker_cliffordDirac c (k + 1) hmem_m) ⟨Γ w + ε • w, heq.symm⟩
    have hm_eig : m ∈ Γ.eigenspace ε :=
      Module.End.mem_eigenspace_iff.mpr (sub_eq_zero.mp hzero)
    have hw_zero : Γ w + ε • w = 0 :=
      cliffordMul_injective (bijective_of_comp_self_eq_neg_one (hc_sq i₀)).1
        (by rw [← heq, hzero, map_zero])
    have hw_eig : w ∈ Γ.eigenspace (-ε) :=
      Module.End.mem_eigenspace_iff.mpr (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hw_zero)
    exact Submodule.mem_sup.mpr
      ⟨m, Submodule.mem_inf.mpr ⟨hm, hm_eig⟩,
        cliffordMul c w, ⟨w, Submodule.mem_inf.mpr ⟨hw, hw_eig⟩, rfl⟩, rfl⟩

/-- **Chiral polynomial Cauchy-Kowalewskaya for `cliffordDirac`**: over any commutative `ℚ`-algebra
`R`, if `γ` anticommutes with `c` and `c i₀` is bijective for some coordinate `i₀ : σ`, then
`cliffordDirac c` maps `chiralHomogeneousSubmodule σ γ ε (k + 1)` surjectively onto
`chiralHomogeneousSubmodule σ γ (-ε) k`. -/
theorem exists_cliffordDirac_eq_of_mem_chiralHomogeneousSubmodule [Algebra ℚ R]
    {c : σ → Module.End R M} {γ : Module.End R M}
    (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0) {i₀ : σ} (hc : Function.Bijective (c i₀))
    {ε : R} {k : ℕ} {v : MvPolynomial σ R ⊗[R] M}
    (hv : v ∈ chiralHomogeneousSubmodule σ γ (-ε) k) :
    ∃ u ∈ chiralHomogeneousSubmodule σ γ ε (k + 1), cliffordDirac c u = v := by
  rw [chiralHomogeneousSubmodule, Submodule.mem_inf] at hv
  let e : M ≃ₗ[R] M := LinearEquiv.ofBijective (c i₀) hc
  have hmap : (γ.eigenspace ε).map (c i₀) = γ.eigenspace (-ε) :=
    Module.End.map_genEigenspace_of_anticommute e (hγ_anti i₀) ε 1
  obtain ⟨u, hu, huP, -, hDu⟩ := exists_cliffordDirac_eq_of_mapsTo
    (P := γ.eigenspace ε) (Q := γ.eigenspace (-ε))
    (fun m hm ↦ by simpa [← hmap] using hm)
    (fun j ↦ Module.End.mapsTo_genEigenspace_neg_of_anticommute (hγ_anti j) ε 1)
    hv.1 ((mem_eigenspace_lTensor_iff γ (-ε) v).mp hv.2)
  exact ⟨u, Submodule.mem_inf.mpr ⟨hu, (mem_eigenspace_lTensor_iff γ ε u).mpr huP⟩, hDu⟩

end Fischer

section Field

variable {σ K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]

omit [CharZero K] in
/-- When `σ` is finite and `M` is finite-dimensional over `K`, every chiral homogeneous submodule is
finite-dimensional. -/
instance [Finite σ] [Module.Finite K M] (γ : Module.End K M) (ε : K) (k : ℕ) :
    FiniteDimensional K (chiralHomogeneousSubmodule σ γ ε k) :=
  Submodule.finiteDimensional_of_le (chiralHomogeneousSubmodule_le_homogeneousTensorSubmodule γ ε k)

variable [Fintype σ]

omit [CharZero K] in
/-- When `M` is finite-dimensional over `K`, every chiral monogenic submodule is
finite-dimensional. -/
instance [Module.Finite K M] (c : σ → Module.End K M) (γ : Module.End K M) (ε : K) (k : ℕ) :
    FiniteDimensional K (chiralMonogenicSubmodule c γ ε k) :=
  Submodule.finiteDimensional_of_le (chiralMonogenicSubmodule_le_monogenicSubmodule c γ ε k)

/-- **Rank relation for chiral monogenic polynomials**: over a field of characteristic zero, if `M`
is finite-dimensional, `γ` anticommutes with `c`, and `c i₀` is surjective for some coordinate
`i₀ : σ`, then
`finrank K (chiralMonogenicSubmodule c γ ε (k + 1)) +
  finrank K (chiralHomogeneousSubmodule σ γ (-ε) k) =
  finrank K (chiralHomogeneousSubmodule σ γ ε (k + 1))`. -/
theorem finrank_chiralMonogenicSubmodule_add_finrank [Module.Finite K M]
    {c : σ → Module.End K M} {i₀ : σ} (hc : Function.Surjective (c i₀))
    {γ : Module.End K M} (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0)
    (ε : K) (k : ℕ) :
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
  have hsurj : Function.Surjective Dk := fun ⟨v, hv⟩ ↦ by
    obtain ⟨u, hu, hDu⟩ := exists_cliffordDirac_eq_of_mem_chiralHomogeneousSubmodule hγ_anti hbij hv
    exact ⟨⟨u, hu⟩, Subtype.ext hDu⟩
  have hker : LinearMap.ker Dk =
      (chiralMonogenicSubmodule c γ ε (k + 1)).comap
        (chiralHomogeneousSubmodule σ γ ε (k + 1)).subtype := by
    ext ⟨u, hu⟩
    simp [Dk, mem_chiralMonogenicSubmodule, hu]
  have hker_eq : Module.finrank K (LinearMap.ker Dk) =
      Module.finrank K (chiralMonogenicSubmodule c γ ε (k + 1)) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe
      (chiralMonogenicSubmodule_le_chiralHomogeneousSubmodule c γ ε (k + 1))).finrank_eq
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := chiralHomogeneousSubmodule σ γ ε (k + 1))
    (V₂ := chiralHomogeneousSubmodule σ γ (-ε) k) Dk
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker_eq, add_comm] at h
  exact h

/-- **Dimension of the degree-`k` chiral monogenic submodule**: over a field of characteristic zero,
if `M` is finite-dimensional, `γ` anticommutes with `c`, and `c i₀` is surjective for some
coordinate `i₀ : σ`, then
`finrank K (chiralMonogenicSubmodule c γ ε k) =
  (Fintype.card σ - 1).multichoose k * finrank K (γ.eigenspace ε)`. -/
theorem finrank_chiralMonogenicSubmodule [Module.Finite K M]
    {c : σ → Module.End K M} {i₀ : σ} (hc : Function.Surjective (c i₀))
    {γ : Module.End K M} (hγ_anti : ∀ i, γ ∘ₗ c i + c i ∘ₗ γ = 0)
    (ε : K) (k : ℕ) :
    Module.finrank K (chiralMonogenicSubmodule c γ ε k) =
      (Fintype.card σ - 1).multichoose k * Module.finrank K (γ.eigenspace ε) := by
  have : Nonempty σ := ⟨i₀⟩
  rcases k with _ | k
  · rw [chiralMonogenicSubmodule_zero, ← (chiralHomogeneousZeroEquiv σ γ ε).finrank_eq,
      Nat.multichoose_zero_right, one_mul]
  · let e : M ≃ₗ[K] M :=
      LinearEquiv.ofBijective (c i₀) ⟨LinearMap.injective_iff_surjective.mpr hc, hc⟩
    have heig : Module.finrank K (γ.eigenspace (-ε)) = Module.finrank K (γ.eigenspace ε) :=
      Module.End.finrank_genEigenspace_neg_of_anticommute e (hγ_anti i₀) ε 1
    have h := finrank_chiralMonogenicSubmodule_add_finrank hc hγ_anti ε k
    rw [finrank_chiralHomogeneousSubmodule, finrank_chiralHomogeneousSubmodule, heig] at h
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card σ = m + 1 :=
      ⟨Fintype.card σ - 1, (Nat.sub_add_cancel Fintype.card_pos).symm⟩
    rw [hm, Nat.add_sub_cancel]
    rw [hm, Nat.multichoose_succ_succ, add_mul] at h
    exact Nat.add_right_cancel h

end Field

end MvPolynomial
