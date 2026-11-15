/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.RingTheory.MvPolynomial.Euler
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Module-valued multivariate polynomials and their homogeneous grading

For an `R`-module `M`, the tensor product `MvPolynomial σ R ⊗[R] M` is the space of `M`-valued
polynomials in variables indexed by `σ`. Tensoring `MvPolynomial.lcoeff R s` and
`MvPolynomial.homogeneousComponent k` on the right with `M` extracts monomial coefficients in `M`
and projects onto the submodule `MvPolynomial.homogeneousTensorSubmodule σ R M k` of homogeneous
degree-`k` elements.

Because `homogeneousComponent k` retracts `MvPolynomial σ R` onto `homogeneousSubmodule σ R k`, the
canonical map `homogeneousSubmodule σ R k ⊗[R] M →ₗ[R] MvPolynomial σ R ⊗[R] M` is injective over
every commutative semiring `R` and every `R`-module `M`, giving the canonical linear equivalence
`MvPolynomial.homogeneousTensorEquiv`. Extending the scalar Laplacian `Δ` and multiplication by
`r² = ∑ᵢ Xᵢ²` via `LinearMap.rTensor M` transfers the identity
`Δ (r² u) = r² (Δ u) + (2n + 4k) u` and the injectivity `Δ (r² u) = 0 → u = 0` under
`[Nonempty σ]` and `[HasUniqueDiv M]`.

## Main definitions

* `MvPolynomial.coeffTensor s`: the monomial coefficient map `MvPolynomial σ R ⊗[R] M →ₗ[R] M`.
* `MvPolynomial.homogeneousComponentTensor k`: the degree-`k` projection on
  `MvPolynomial σ R ⊗[R] M`.
* `MvPolynomial.homogeneousTensorSubmodule σ R M k`: the homogeneous degree-`k` submodule of
  `MvPolynomial σ R ⊗[R] M`.
* `MvPolynomial.homogeneousTensorEquiv σ R M k`: the canonical equivalence
  `homogeneousSubmodule σ R k ⊗[R] M ≃ₗ[R] homogeneousTensorSubmodule σ R M k`.
* `MvPolynomial.homogeneousTensorZeroEquiv σ R M`: the degree-zero equivalence
  `M ≃ₗ[R] homogeneousTensorSubmodule σ R M 0`.

## Main results

* `MvPolynomial.ext_coeffTensor`: two `M`-valued polynomials agree iff all their monomial
  coefficients agree.
* `MvPolynomial.mem_homogeneousTensorSubmodule_iff`: `u` is homogeneous of degree `k` iff
  `homogeneousComponentTensor k u = u`.
* `MvPolynomial.finrank_homogeneousTensorSubmodule`: the rank of degree-`k` `M`-valued polynomials
  is `(Fintype.card σ).multichoose k * Module.finrank R M`.
* `MvPolynomial.eq_zero_of_laplacian_normSq_mul_rTensor_eq_zero`: with `[Nonempty σ]` and
  `[HasUniqueDiv M]`, `(laplacian.rTensor M) ((mulLeft R (normSq σ R)).rTensor M u) = 0` implies
  `u = 0`.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section General

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The monomial `s`-coefficient of an `M`-valued polynomial `u : MvPolynomial σ R ⊗[R] M`, sending
`p ⊗ₜ m` to `p.coeff s • m`. -/
noncomputable def coeffTensor (s : σ →₀ ℕ) : (MvPolynomial σ R ⊗[R] M) →ₗ[R] M :=
  TensorProduct.lid R M ∘ₗ (lcoeff R s).rTensor M

@[simp]
theorem coeffTensor_tmul (s : σ →₀ ℕ) (p : MvPolynomial σ R) (m : M) :
    coeffTensor s (p ⊗ₜ[R] m) = p.coeff s • m := by
  simp [coeffTensor]

/-- Extracting a monomial coefficient commutes with extending a linear map along the right tensor
factor. -/
@[simp]
theorem coeffTensor_lTensor {N : Type*} [AddCommMonoid N] [Module R N] (s : σ →₀ ℕ)
    (f : M →ₗ[R] N) (u : MvPolynomial σ R ⊗[R] M) :
    coeffTensor s (f.lTensor (MvPolynomial σ R) u) = f (coeffTensor s u) := by
  induction u using TensorProduct.inductionOn with
  | tmul p m => simp
  | add x y hx hy => simp [hx, hy]

/-- Two `M`-valued polynomials are equal iff all their monomial coefficients in `M` coincide. -/
theorem ext_coeffTensor {u v : MvPolynomial σ R ⊗[R] M}
    (h : ∀ s : σ →₀ ℕ, coeffTensor s u = coeffTensor s v) : u = v := by
  classical
  apply (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials σ R)).injective
  ext s
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  have hcoord : (basisMonomials σ R).coord s = lcoeff R s :=
    (basisMonomials σ R).ext fun t ↦ by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, coe_basisMonomials, lcoeff_apply,
        coeff_monomial, Finsupp.single_apply]
  simpa [hcoord, coeffTensor] using h s

/-- If `M` has unique division by positive natural numbers (`HasUniqueDiv M`), so does
`MvPolynomial σ R ⊗[R] M`. -/
instance [HasUniqueDiv M] : HasUniqueDiv (MvPolynomial σ R ⊗[R] M) := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials σ R)).injective.hasUniqueDiv
    (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials σ R)).toAddMonoidHom

/-- Projection onto the homogeneous component of degree `k` in `MvPolynomial σ R ⊗[R] M`. -/
noncomputable def homogeneousComponentTensor (k : ℕ) :
    Module.End R (MvPolynomial σ R ⊗[R] M) :=
  (homogeneousComponent k).rTensor M

theorem homogeneousComponentTensor_def (k : ℕ) :
    (homogeneousComponentTensor k : Module.End R (MvPolynomial σ R ⊗[R] M)) =
      (homogeneousComponent k).rTensor M :=
  (rfl)

@[simp]
theorem homogeneousComponentTensor_tmul (k : ℕ) (p : MvPolynomial σ R) (m : M) :
    homogeneousComponentTensor k (p ⊗ₜ[R] m) = homogeneousComponent k p ⊗ₜ[R] m :=
  (rfl)

variable (σ R M) in
/-- The submodule of `MvPolynomial σ R ⊗[R] M` consisting of `M`-valued homogeneous polynomials of
degree `k`: the image of `homogeneousSubmodule σ R k ⊗[R] M`. -/
noncomputable def homogeneousTensorSubmodule (k : ℕ) : Submodule R (MvPolynomial σ R ⊗[R] M) :=
  LinearMap.range ((homogeneousSubmodule σ R k).subtype.rTensor M)

/-- The canonical retraction `MvPolynomial σ R →ₗ[R] homogeneousSubmodule σ R k` given by
`homogeneousComponent k`. -/
private noncomputable def homogeneousComponentRestrict (k : ℕ) :
    MvPolynomial σ R →ₗ[R] homogeneousSubmodule σ R k :=
  (homogeneousComponent k).codRestrict (homogeneousSubmodule σ R k) fun p ↦
    homogeneousComponent_isHomogeneous k p

private theorem subtype_comp_homogeneousComponentRestrict (k : ℕ) :
    (homogeneousSubmodule σ R k).subtype ∘ₗ homogeneousComponentRestrict k =
      homogeneousComponent (R := R) (σ := σ) k :=
  rfl

private theorem homogeneousComponentRestrict_comp_subtype (k : ℕ) :
    homogeneousComponentRestrict k ∘ₗ (homogeneousSubmodule σ R k).subtype = LinearMap.id :=
  LinearMap.ext fun ⟨_, hp⟩ ↦ Subtype.ext (homogeneousComponent_eq_self hp)

/-- An `M`-valued polynomial belongs to `homogeneousTensorSubmodule σ R M k` iff it is fixed by
`homogeneousComponentTensor k`. -/
theorem mem_homogeneousTensorSubmodule_iff {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ homogeneousTensorSubmodule σ R M k ↔ homogeneousComponentTensor k u = u := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [homogeneousComponentTensor_def, ← LinearMap.rTensor_comp_apply,
      ← subtype_comp_homogeneousComponentRestrict, LinearMap.comp_assoc,
      homogeneousComponentRestrict_comp_subtype, LinearMap.comp_id]
  · intro hu
    rw [← hu, homogeneousComponentTensor_def, ← subtype_comp_homogeneousComponentRestrict,
      LinearMap.rTensor_comp_apply]
    exact ⟨(homogeneousComponentRestrict k).rTensor M u, rfl⟩

theorem tmul_mem_homogeneousTensorSubmodule {p : MvPolynomial σ R} {k : ℕ}
    (hp : p.IsHomogeneous k) (m : M) :
    p ⊗ₜ[R] m ∈ homogeneousTensorSubmodule σ R M k := by
  rw [mem_homogeneousTensorSubmodule_iff, homogeneousComponentTensor_tmul,
    homogeneousComponent_eq_self hp]

/-- Elimination principle for `homogeneousTensorSubmodule σ R M k`: to prove a property of an
element of `homogeneousTensorSubmodule σ R M k`, it suffices to prove it for pure tensors `p ⊗ₜ m`
with `p` homogeneous of degree `k` and show closure under addition. -/
@[elab_as_elim]
theorem homogeneousTensorSubmodule_inductionOn {k : ℕ}
    {motive : MvPolynomial σ R ⊗[R] M → Prop}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k)
    (tmul : ∀ {p : MvPolynomial σ R}, p.IsHomogeneous k → ∀ m : M, motive (p ⊗ₜ[R] m))
    (add : ∀ {x y}, motive x → motive y → motive (x + y)) : motive u := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m => exact tmul p.2 m
  | add x y hx hy =>
    rw [map_add]
    exact add hx hy

/-- Extending a linear map `f : M →ₗ[R] N` along `MvPolynomial σ R` preserves homogeneous degree. -/
theorem lTensor_mem_homogeneousTensorSubmodule {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    f.lTensor (MvPolynomial σ R) u ∈ homogeneousTensorSubmodule σ R N k :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp m ↦ tmul_mem_homogeneousTensorSubmodule hp (f m))
    fun hx hy ↦ by rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Every homogeneous `M`-valued polynomial of degree `k` expands over a finite set of degree-`k`
multi-indices as `∑ s ∈ S, monomial s 1 ⊗ₜ coeffTensor s u`, with all other monomial coefficients
equal to zero. -/
theorem exists_finset_sum_monomial_tmul_coeffTensor {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    ∃ S : Finset (σ →₀ ℕ), (∀ s ∈ S, s.degree = k) ∧ (∀ s ∉ S, coeffTensor s u = 0) ∧
      ∑ s ∈ S, monomial s (1 : R) ⊗ₜ[R] coeffTensor s u = u := by
  classical
  refine homogeneousTensorSubmodule_inductionOn hu (fun {p} hp m ↦ ?_) fun {x y} hx hy ↦ ?_
  · refine ⟨p.support, fun s hs ↦ ?_, fun s hs ↦ ?_, ?_⟩
    · rw [Finsupp.degree_eq_weight_one]
      exact hp (mem_support_iff.mp hs)
    · rw [coeffTensor_tmul, notMem_support_iff.mp hs, zero_smul]
    · conv_rhs => rw [as_sum p, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [coeffTensor_tmul, ← TensorProduct.smul_tmul, smul_monomial, smul_eq_mul, mul_one]
  · obtain ⟨S₁, hdeg₁, hzero₁, hsum₁⟩ := hx
    obtain ⟨S₂, hdeg₂, hzero₂, hsum₂⟩ := hy
    refine ⟨S₁ ∪ S₂, fun s hs ↦ ?_, fun s hs ↦ ?_, ?_⟩
    · exact (Finset.mem_union.mp hs).elim (hdeg₁ s) (hdeg₂ s)
    · rw [Finset.mem_union, not_or] at hs
      rw [map_add, hzero₁ s hs.1, hzero₂ s hs.2, add_zero]
    · simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      have h₁ : ∑ s ∈ S₁ ∪ S₂, monomial s (1 : R) ⊗ₜ[R] coeffTensor s x = x := by
        rw [← Finset.sum_subset Finset.subset_union_left fun s _ hs ↦ by
          rw [hzero₁ s hs, TensorProduct.tmul_zero]]
        exact hsum₁
      have h₂ : ∑ s ∈ S₁ ∪ S₂, monomial s (1 : R) ⊗ₜ[R] coeffTensor s y = y := by
        rw [← Finset.sum_subset Finset.subset_union_right fun s _ hs ↦ by
          rw [hzero₂ s hs, TensorProduct.tmul_zero]]
        exact hsum₂
      rw [h₁, h₂]

@[simp]
theorem homogeneousComponentTensor_mem (k : ℕ) (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k u ∈ homogeneousTensorSubmodule σ R M k := by
  rw [homogeneousComponentTensor_def, ← subtype_comp_homogeneousComponentRestrict,
    LinearMap.rTensor_comp_apply]
  exact ⟨(homogeneousComponentRestrict k).rTensor M u, rfl⟩

theorem homogeneousComponentTensor_eq_self {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    homogeneousComponentTensor k u = u :=
  mem_homogeneousTensorSubmodule_iff.mp hu

@[simp]
theorem homogeneousComponentTensor_idem (k : ℕ) (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k (homogeneousComponentTensor k u) =
      homogeneousComponentTensor k u :=
  homogeneousComponentTensor_eq_self (homogeneousComponentTensor_mem k u)

theorem homogeneousComponentTensor_of_mem {k j : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    homogeneousComponentTensor j u = if j = k then u else 0 := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m =>
    rw [LinearMap.rTensor_tmul, Submodule.coe_subtype, homogeneousComponentTensor_tmul,
      homogeneousComponent_of_mem p.2]
    split_ifs <;> simp
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    split_ifs <;> simp

theorem homogeneousComponentTensor_eq_zero_of_ne {k j : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) (hjk : j ≠ k) :
    homogeneousComponentTensor j u = 0 := by
  rw [homogeneousComponentTensor_of_mem hu, ite_eq_right_iff.mpr fun h ↦ (hjk h).elim]

private theorem sum_range_homogeneousComponentTensor_of_le {u : MvPolynomial σ R ⊗[R] M}
    {N M' : ℕ} (hN : ∑ k ∈ Finset.range N, homogeneousComponentTensor k u = u) (hNM : N ≤ M') :
    ∑ k ∈ Finset.range M', homogeneousComponentTensor k u = u := by
  rw [← Finset.sum_subset (Finset.range_mono hNM)]
  · exact hN
  · intro k _ hk
    rw [← hN, map_sum]
    refine Finset.sum_eq_zero fun j hj ↦
      homogeneousComponentTensor_eq_zero_of_ne (homogeneousComponentTensor_mem j u) ?_
    simp only [Finset.mem_range] at hj hk
    omega

/-- Every `M`-valued polynomial is the finite sum of its homogeneous components. -/
theorem exists_sum_homogeneousComponentTensor_eq (u : MvPolynomial σ R ⊗[R] M) :
    ∃ N : ℕ, ∑ k ∈ Finset.range N, homogeneousComponentTensor k u = u := by
  induction u using TensorProduct.inductionOn with
  | tmul p m =>
    refine ⟨p.totalDegree + 1, ?_⟩
    simp_rw [homogeneousComponentTensor_tmul, ← TensorProduct.sum_tmul, sum_homogeneousComponent]
  | add u₁ u₂ hu₁ hu₂ =>
    obtain ⟨N₁, hN₁⟩ := hu₁
    obtain ⟨N₂, hN₂⟩ := hu₂
    refine ⟨max N₁ N₂, ?_⟩
    rw [Finset.sum_congr rfl fun k _ ↦ map_add (homogeneousComponentTensor k) u₁ u₂,
      Finset.sum_add_distrib,
      sum_range_homogeneousComponentTensor_of_le hN₁ (le_max_left N₁ N₂),
      sum_range_homogeneousComponentTensor_of_le hN₂ (le_max_right N₁ N₂)]

/-- Every `M`-valued polynomial is the sum of its homogeneous components below some bound
`N ≥ m`. -/
theorem exists_sum_homogeneousComponentTensor_eq_of_le (u : MvPolynomial σ R ⊗[R] M) (m : ℕ) :
    ∃ N : ℕ, m ≤ N ∧ ∑ k ∈ Finset.range N, homogeneousComponentTensor k u = u := by
  obtain ⟨N, hN⟩ := exists_sum_homogeneousComponentTensor_eq u
  exact ⟨max m N, le_max_left m N,
    sum_range_homogeneousComponentTensor_of_le hN (le_max_right m N)⟩

/-- Two `M`-valued polynomials agree iff all their homogeneous components agree. -/
theorem ext_homogeneousComponentTensor {u v : MvPolynomial σ R ⊗[R] M}
    (h : ∀ k : ℕ, homogeneousComponentTensor k u = homogeneousComponentTensor k v) : u = v := by
  obtain ⟨N₁, hN₁⟩ := exists_sum_homogeneousComponentTensor_eq u
  obtain ⟨N₂, hN₂⟩ := exists_sum_homogeneousComponentTensor_eq v
  rw [← sum_range_homogeneousComponentTensor_of_le hN₁ (le_max_left N₁ N₂),
    ← sum_range_homogeneousComponentTensor_of_le hN₂ (le_max_right N₁ N₂)]
  exact Finset.sum_congr rfl fun k _ ↦ h k

theorem eq_zero_of_forall_homogeneousComponentTensor_eq_zero {u : MvPolynomial σ R ⊗[R] M}
    (h : ∀ k : ℕ, homogeneousComponentTensor k u = 0) : u = 0 :=
  ext_homogeneousComponentTensor fun k ↦ by simp [h k]

private theorem subtype_rTensor_mem_homogeneousTensorSubmodule (k : ℕ)
    (z : homogeneousSubmodule σ R k ⊗[R] M) :
    (homogeneousSubmodule σ R k).subtype.rTensor M z ∈
      homogeneousTensorSubmodule σ R M k :=
  ⟨z, rfl⟩

variable (σ R M) in
/-- Canonical linear equivalence between `homogeneousSubmodule σ R k ⊗[R] M` and
`homogeneousTensorSubmodule σ R M k`. -/
noncomputable def homogeneousTensorEquiv (k : ℕ) :
    homogeneousSubmodule σ R k ⊗[R] M ≃ₗ[R] homogeneousTensorSubmodule σ R M k :=
  LinearEquiv.ofLinearMap
    (((homogeneousSubmodule σ R k).subtype.rTensor M).codRestrict
      (homogeneousTensorSubmodule σ R M k)
      (subtype_rTensor_mem_homogeneousTensorSubmodule k))
    ((homogeneousComponentRestrict k).rTensor M ∘ₗ
      (homogeneousTensorSubmodule σ R M k).subtype)
    (LinearMap.ext fun ⟨u, hu⟩ ↦ Subtype.ext <| by
      rw [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.comp_apply,
        Submodule.coe_subtype, ← LinearMap.rTensor_comp_apply,
        subtype_comp_homogeneousComponentRestrict, ← homogeneousComponentTensor_def,
        homogeneousComponentTensor_eq_self hu, LinearMap.id_apply])
    (LinearMap.ext fun z ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_subtype,
        LinearMap.codRestrict_apply, ← LinearMap.rTensor_comp_apply,
        homogeneousComponentRestrict_comp_subtype, LinearMap.rTensor_id, LinearMap.id_apply])

@[simp]
theorem coe_homogeneousTensorEquiv_tmul (k : ℕ) (p : homogeneousSubmodule σ R k) (m : M) :
    (homogeneousTensorEquiv σ R M k (p ⊗ₜ[R] m) : MvPolynomial σ R ⊗[R] M) =
      (p : MvPolynomial σ R) ⊗ₜ[R] m :=
  (rfl)

variable (σ R M) in
private noncomputable def zeroIncl : M →ₗ[R] homogeneousTensorSubmodule σ R M 0 :=
  ((TensorProduct.mk R (MvPolynomial σ R) M) 1).codRestrict
    (homogeneousTensorSubmodule σ R M 0) fun m ↦
    tmul_mem_homogeneousTensorSubmodule (isHomogeneous_one σ R) m

private theorem coe_zeroIncl_apply (m : M) :
    (zeroIncl σ R M m : MvPolynomial σ R ⊗[R] M) = 1 ⊗ₜ[R] m :=
  rfl

private theorem zeroIncl_coeffTensor_zero {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M 0) :
    (zeroIncl σ R M (coeffTensor 0 u) : MvPolynomial σ R ⊗[R] M) = u := by
  rw [coe_zeroIncl_apply]
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m =>
    have hp : (p : MvPolynomial σ R) = C ((p : MvPolynomial σ R).coeff 0) := by
      classical
      ext s
      rw [coeff_C]
      split_ifs with hs
      · subst hs; rfl
      · exact p.2.coeff_eq_zero fun hdeg ↦ hs ((Finsupp.degree_eq_zero_iff s).mp hdeg).symm
    rw [LinearMap.rTensor_tmul, Submodule.coe_subtype, coeffTensor_tmul,
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, algebraMap_eq, ← hp]
  | add x y hx hy =>
    rw [map_add, map_add, TensorProduct.tmul_add, hx, hy]

variable (σ R M) in
/-- Canonical linear equivalence between `M` and the degree-zero `M`-valued polynomials
`homogeneousTensorSubmodule σ R M 0`, sending `m` to `1 ⊗ₜ m`. -/
noncomputable def homogeneousTensorZeroEquiv :
    M ≃ₗ[R] homogeneousTensorSubmodule σ R M 0 :=
  LinearEquiv.ofLinearMap (zeroIncl σ R M)
    (coeffTensor 0 ∘ₗ (homogeneousTensorSubmodule σ R M 0).subtype)
    (LinearMap.ext fun ⟨u, hu⟩ ↦ Subtype.ext (zeroIncl_coeffTensor_zero hu))
    (LinearMap.ext fun m ↦ by simp [coe_zeroIncl_apply])

@[simp]
theorem coe_homogeneousTensorZeroEquiv_apply (m : M) :
    (homogeneousTensorZeroEquiv σ R M m : MvPolynomial σ R ⊗[R] M) = 1 ⊗ₜ[R] m :=
  (rfl)

@[simp]
theorem homogeneousTensorZeroEquiv_symm_apply (u : homogeneousTensorSubmodule σ R M 0) :
    (homogeneousTensorZeroEquiv σ R M).symm u = coeffTensor 0 (u : MvPolynomial σ R ⊗[R] M) :=
  (rfl)

@[simp]
theorem homogeneousTensorSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ] (k : ℕ) :
    homogeneousTensorSubmodule σ R M (k + 1) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, rfl⟩
  have hbot : homogeneousSubmodule σ R (k + 1) = ⊥ :=
    homogeneousSubmodule_succ_eq_bot_of_isEmpty k
  induction z using TensorProduct.inductionOn with
  | tmul p m =>
    have hp : (p : MvPolynomial σ R) = 0 :=
      (Submodule.mem_bot R).mp (hbot ▸ p.2)
    simp [hp]
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem ⊥ hx hy

/-- Over a finite index type `σ` and a finite `R`-module `M`, the submodule of degree-`k`
`M`-valued homogeneous polynomials is finite over `R`. -/
instance [Finite σ] [Module.Finite R M] (k : ℕ) :
    Module.Finite R (homogeneousTensorSubmodule σ R M k) :=
  Module.Finite.range _

/-- On `homogeneousTensorSubmodule σ R M k`, the lifted Euler derivation acts as scalar
multiplication by `k`. -/
theorem euler_rTensor_eq_nsmul {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    euler.toLinearMap.rTensor M u = k • u := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m =>
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Submodule.coe_subtype,
      Derivation.coeFn_coe, p.2.euler_eq, ← TensorProduct.smul_tmul']
  | add x y hx hy => simp [map_add, hx, hy]

end General

section Fintype

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype σ]

/-- The rank of the degree-`k` `M`-valued homogeneous polynomials is
`(Fintype.card σ).multichoose k * Module.finrank R M`. -/
theorem finrank_homogeneousTensorSubmodule [StrongRankCondition R] [Module.Free R M] (k : ℕ) :
    Module.finrank R (homogeneousTensorSubmodule σ R M k) =
      (Fintype.card σ).multichoose k * Module.finrank R M := by
  rw [← (homogeneousTensorEquiv σ R M k).finrank_eq, Module.finrank_tensorProduct,
    TauCeti.finrank_homogeneousSubmodule_eq_multichoose]

/-- The lifted Laplacian lowers the homogeneous degree of `M`-valued polynomials by two. -/
theorem laplacian_rTensor_mem_homogeneousTensorSubmodule {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    laplacian.rTensor M u ∈ homogeneousTensorSubmodule σ R M (k - 2) := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m => exact tmul_mem_homogeneousTensorSubmodule p.2.laplacian m
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

/-- An `M`-valued homogeneous polynomial of degree at most one is harmonic. -/
theorem laplacian_rTensor_eq_zero_of_le_one {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) (hk : k ≤ 1) :
    laplacian.rTensor M u = 0 := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m =>
    have hp : laplacian (p : MvPolynomial σ R) = 0 := p.2.laplacian_eq_zero_of_le_one hk
    simp [hp]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Multiplying on the left by `normSq σ R` raises the homogeneous degree of `M`-valued
polynomials by two. -/
theorem normSq_mul_rTensor_mem_homogeneousTensorSubmodule {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    (LinearMap.mulLeft R (normSq σ R)).rTensor M u ∈
      homogeneousTensorSubmodule σ R M (k + 2) := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m =>
    refine tmul_mem_homogeneousTensorSubmodule ?_ m
    simpa [add_comm] using (isHomogeneous_normSq σ R).mul p.2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy

/-- **The Laplacian of `r² u`** for `M`-valued homogeneous polynomials: for `u` of degree `k` in
`n = Fintype.card σ` variables, `Δ (r² u) = r² (Δ u) + (2n + 4k) • u`. -/
theorem laplacian_normSq_mul_rTensor {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M u) =
      (LinearMap.mulLeft R (normSq σ R)).rTensor M (laplacian.rTensor M u) +
        (2 * Fintype.card σ + 4 * k) • u := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m =>
    simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype, LinearMap.mulLeft_apply,
      laplacian_normSq_mul p.2, TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]
    abel

private theorem eq_zero_of_laplacian_normSq_mul_rTensor_add_nsmul_eq_zero [Nonempty σ]
    [HasUniqueDiv M] {e : ℕ} :
    ∀ {u : MvPolynomial σ R ⊗[R] M} {m : ℕ}, u ∈ homogeneousTensorSubmodule σ R M e →
      laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M u) + m • u = 0 →
      u = 0 := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro u m hu h
  rw [laplacian_normSq_mul_rTensor hu, add_assoc, ← add_smul] at h
  set N := 2 * Fintype.card σ + 4 * e + m
  have hN : N ≠ 0 := by
    have : 0 < Fintype.card σ := Fintype.card_pos
    omega
  suffices hΔ : laplacian.rTensor M u = 0 by
    rw [hΔ, map_zero, zero_add] at h
    exact IsSMulRegular.nat_of_hasUniqueDiv hN (by simpa using h)
  rcases lt_or_ge e 2 with he | he
  · exact laplacian_rTensor_eq_zero_of_le_one hu (by omega)
  exact @ih (e - 2) (by omega) _ N (laplacian_rTensor_mem_homogeneousTensorSubmodule hu) <| by
    simpa only [map_add, map_nsmul, map_zero] using congrArg (laplacian.rTensor M) h

@[simp]
theorem homogeneousComponentTensor_laplacian_normSq_mul (k : ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k
        (laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M u)) =
      laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M
        (homogeneousComponentTensor k u)) := by
  obtain ⟨N, hkN, hN⟩ := exists_sum_homogeneousComponentTensor_eq_of_le u (k + 1)
  have hmem (j : ℕ) :
      laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M
        (homogeneousComponentTensor j u)) ∈ homogeneousTensorSubmodule σ R M j := by
    simpa using laplacian_rTensor_mem_homogeneousTensorSubmodule
      (normSq_mul_rTensor_mem_homogeneousTensorSubmodule (homogeneousComponentTensor_mem j u))
  conv_lhs => rw [← hN]
  simp only [map_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hkN),
    homogeneousComponentTensor_eq_self (hmem k)]
  intro j _ hj
  exact homogeneousComponentTensor_eq_zero_of_ne (hmem j) (Ne.symm hj)

/-- **Trivial kernel of `u ↦ Δ (r² u)`** on `M`-valued polynomials: with at least one variable and
`[HasUniqueDiv M]`, if `Δ (r² u) = 0` then `u = 0`. -/
theorem eq_zero_of_laplacian_normSq_mul_rTensor_eq_zero [Nonempty σ] [HasUniqueDiv M]
    {u : MvPolynomial σ R ⊗[R] M}
    (h : laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M u) = 0) :
    u = 0 := by
  refine eq_zero_of_forall_homogeneousComponentTensor_eq_zero fun k ↦ ?_
  have hk : laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M
      (homogeneousComponentTensor k u)) = 0 := by
    rw [← homogeneousComponentTensor_laplacian_normSq_mul, h, map_zero]
  exact eq_zero_of_laplacian_normSq_mul_rTensor_add_nsmul_eq_zero (m := 0)
    (homogeneousComponentTensor_mem k u) (by simpa using hk)

end Fintype

end MvPolynomial
