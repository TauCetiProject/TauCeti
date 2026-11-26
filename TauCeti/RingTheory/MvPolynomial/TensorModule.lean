/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import TauCeti.RingTheory.MvPolynomial.Euler
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# Module-valued multivariate polynomials and their homogeneous grading

For an `R`-module `M`, `MvPolynomial σ R ⊗[R] M` is the space of `M`-valued multivariate
polynomials. Tensoring `MvPolynomial.lcoeff R s` and `MvPolynomial.homogeneousComponent k` on the
right with `M` extracts monomial coefficients (`MvPolynomial.coeffTensor`) and projects onto the
degree-`k` submodule `MvPolynomial.homogeneousTensorSubmodule σ R M k`, which is canonically
isomorphic to `homogeneousSubmodule σ R k ⊗[R] M` (`MvPolynomial.homogeneousTensorEquiv`). Lifted
`laplacian` and `normSq` operators satisfy `Δ (r² u) = r² (Δ u) + (2n + 4k) • u` with trivial
kernel `ker (Δ ∘ r²)` under `[Nonempty σ] [HasUniqueDiv M]`.

## Main definitions

* `MvPolynomial.coeffTensor`, `MvPolynomial.homogeneousComponentTensor`,
  `MvPolynomial.homogeneousTensorSubmodule`, `MvPolynomial.homogeneousTensorEquiv`, and
  `MvPolynomial.homogeneousTensorZeroEquiv`.

## Main results

* `MvPolynomial.mem_homogeneousTensorSubmodule_iff`,
  `MvPolynomial.mem_homogeneousTensorSubmodule_iff_coeffTensor`,
  `MvPolynomial.finrank_homogeneousTensorSubmodule`, `MvPolynomial.laplacian_normSq_mul_rTensor`,
  and `MvPolynomial.eq_zero_of_laplacian_normSq_mul_rTensor_eq_zero`.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section General

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Monomial `s`-coefficient on `MvPolynomial σ R ⊗[R] M`, sending `p ⊗ₜ m` to `p.coeff s • m`. -/
noncomputable def coeffTensor (s : σ →₀ ℕ) : (MvPolynomial σ R ⊗[R] M) →ₗ[R] M :=
  TensorProduct.lid R M ∘ₗ (lcoeff R s).rTensor M

theorem coeffTensor_apply (s : σ →₀ ℕ) (u : MvPolynomial σ R ⊗[R] M) :
    coeffTensor s u = TensorProduct.lid R M ((lcoeff R s).rTensor M u) := (rfl)

@[simp] theorem coeffTensor_tmul (s : σ →₀ ℕ) (p : MvPolynomial σ R) (m : M) :
    coeffTensor s (p ⊗ₜ[R] m) = p.coeff s • m := by simp [coeffTensor]

@[simp] theorem coeffTensor_lTensor {N : Type*} [AddCommMonoid N] [Module R N] (s : σ →₀ ℕ)
    (f : M →ₗ[R] N) (u : MvPolynomial σ R ⊗[R] M) :
    coeffTensor s (f.lTensor (MvPolynomial σ R) u) = f (coeffTensor s u) := by
  induction u using TensorProduct.inductionOn with
  | tmul p m => simp
  | add x y hx hy => simp [hx, hy]

/-- Unique natural division transfers from `M` to `MvPolynomial σ R ⊗[R] M`. -/
instance [HasUniqueDiv M] : HasUniqueDiv (MvPolynomial σ R ⊗[R] M) := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials σ R)).injective.hasUniqueDiv
    (TensorProduct.equivFinsuppOfBasisLeft (basisMonomials σ R)).toAddMonoidHom

/-- Projection onto the homogeneous component of degree `k` in `MvPolynomial σ R ⊗[R] M`. -/
noncomputable def homogeneousComponentTensor (k : ℕ) : Module.End R (MvPolynomial σ R ⊗[R] M) :=
  (homogeneousComponent k).rTensor M

theorem homogeneousComponentTensor_def (k : ℕ) :
    (homogeneousComponentTensor k : Module.End R (MvPolynomial σ R ⊗[R] M)) =
      (homogeneousComponent k).rTensor M := (rfl)

@[simp] theorem homogeneousComponentTensor_tmul (k : ℕ) (p : MvPolynomial σ R) (m : M) :
    homogeneousComponentTensor k (p ⊗ₜ[R] m) = homogeneousComponent k p ⊗ₜ[R] m := (rfl)

/-- Extracting the `s`-coefficient after projecting to degree `k` keeps degree-`k` terms. -/
@[simp] theorem coeffTensor_homogeneousComponentTensor (s : σ →₀ ℕ) (k : ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    coeffTensor s (homogeneousComponentTensor k u) =
      if s.degree = k then coeffTensor s u else 0 := by
  induction u using TensorProduct.inductionOn with
  | tmul p m => simp [coeff_homogeneousComponent, ite_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; split_ifs <;> simp

variable (σ R M) in
/-- Degree-`k` `M`-valued homogeneous polynomials in `MvPolynomial σ R ⊗[R] M`. -/
noncomputable def homogeneousTensorSubmodule (k : ℕ) : Submodule R (MvPolynomial σ R ⊗[R] M) :=
  LinearMap.range ((homogeneousSubmodule σ R k).subtype.rTensor M)

private noncomputable def homogeneousComponentRestrict (k : ℕ) :
    MvPolynomial σ R →ₗ[R] homogeneousSubmodule σ R k :=
  (homogeneousComponent k).codRestrict (homogeneousSubmodule σ R k)
    (homogeneousComponent_isHomogeneous k)

private theorem subtype_comp_homogeneousComponentRestrict (k : ℕ) :
    (homogeneousSubmodule σ R k).subtype ∘ₗ homogeneousComponentRestrict k =
      homogeneousComponent (R := R) (σ := σ) k := rfl

private theorem homogeneousComponentRestrict_comp_subtype (k : ℕ) :
    homogeneousComponentRestrict k ∘ₗ (homogeneousSubmodule σ R k).subtype = LinearMap.id :=
  LinearMap.ext fun ⟨_, hp⟩ ↦ Subtype.ext (homogeneousComponent_eq_self hp)

/-- Membership in `homogeneousTensorSubmodule` is fixedness under `homogeneousComponentTensor`. -/
theorem mem_homogeneousTensorSubmodule_iff {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ homogeneousTensorSubmodule σ R M k ↔ homogeneousComponentTensor k u = u := by
  refine ⟨?_, fun hu ↦ ?_⟩
  · rintro ⟨z, rfl⟩
    rw [homogeneousComponentTensor_def, ← LinearMap.rTensor_comp_apply,
      ← subtype_comp_homogeneousComponentRestrict, LinearMap.comp_assoc,
      homogeneousComponentRestrict_comp_subtype, LinearMap.comp_id]
  · rw [← hu, homogeneousComponentTensor_def, ← subtype_comp_homogeneousComponentRestrict,
      LinearMap.rTensor_comp_apply]
    exact ⟨(homogeneousComponentRestrict k).rTensor M u, rfl⟩

/-- Coefficientwise membership criterion for `homogeneousTensorSubmodule σ R M k`. -/
theorem mem_homogeneousTensorSubmodule_iff_coeffTensor {k : ℕ} {u : MvPolynomial σ R ⊗[R] M} :
    u ∈ homogeneousTensorSubmodule σ R M k ↔
      ∀ s : σ →₀ ℕ, s.degree ≠ k → coeffTensor s u = 0 := by
  rw [mem_homogeneousTensorSubmodule_iff]
  refine ⟨fun hu s hs ↦ ?_, fun h ↦ ext_lid_rTensor_lcoeff fun s ↦ ?_⟩
  · rw [← hu, coeffTensor_homogeneousComponentTensor, ite_eq_right_iff.mpr fun hk ↦ (hs hk).elim]
  · rw [← coeffTensor_apply, ← coeffTensor_apply, coeffTensor_homogeneousComponentTensor]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm

theorem tmul_mem_homogeneousTensorSubmodule {p : MvPolynomial σ R} {k : ℕ}
    (hp : p.IsHomogeneous k) (m : M) : p ⊗ₜ[R] m ∈ homogeneousTensorSubmodule σ R M k := by
  rw [mem_homogeneousTensorSubmodule_iff, homogeneousComponentTensor_tmul,
    homogeneousComponent_eq_self hp]

/-- Elimination principle for `homogeneousTensorSubmodule σ R M k` via homogeneous pure tensors. -/
@[elab_as_elim]
theorem homogeneousTensorSubmodule_inductionOn {k : ℕ}
    {motive : MvPolynomial σ R ⊗[R] M → Prop}
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k)
    (tmul : ∀ {p : MvPolynomial σ R}, p.IsHomogeneous k → ∀ m : M, motive (p ⊗ₜ[R] m))
    (add : ∀ {x y}, motive x → motive y → motive (x + y)) : motive u := by
  obtain ⟨z, rfl⟩ := hu
  induction z using TensorProduct.inductionOn with
  | tmul p m => exact tmul p.property m
  | add x y hx hy => rw [map_add]; exact add hx hy

/-- Lifting a module linear map preserves `homogeneousTensorSubmodule` of degree `k`. -/
theorem lTensor_mem_homogeneousTensorSubmodule {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    f.lTensor (MvPolynomial σ R) u ∈ homogeneousTensorSubmodule σ R N k :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp m ↦ tmul_mem_homogeneousTensorSubmodule hp (f m))
    fun hx hy ↦ by rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Lifting a polynomial endomorphism sending degree `k` to degree `d` maps
`homogeneousTensorSubmodule σ R M k` into `homogeneousTensorSubmodule σ R M d`. -/
theorem rTensor_mem_homogeneousTensorSubmodule {f : Module.End R (MvPolynomial σ R)}
    {k d : ℕ} (hf : ∀ {p : MvPolynomial σ R}, p.IsHomogeneous k → (f p).IsHomogeneous d)
    {u : MvPolynomial σ R ⊗[R] M} (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    f.rTensor M u ∈ homogeneousTensorSubmodule σ R M d :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp m ↦ tmul_mem_homogeneousTensorSubmodule (hf hp) m)
    fun hx hy ↦ by rw [map_add]; exact Submodule.add_mem _ hx hy

theorem exists_finset_sum_monomial_tmul_coeffTensor {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    ∃ S : Finset (σ →₀ ℕ), (∀ s ∈ S, s.degree = k) ∧ (∀ s ∉ S, coeffTensor s u = 0) ∧
      ∑ s ∈ S, monomial s (1 : R) ⊗ₜ[R] coeffTensor s u = u := by
  classical
  refine homogeneousTensorSubmodule_inductionOn hu (fun {p} hp m ↦ ?_) fun {x y} hx hy ↦ ?_
  · refine ⟨p.support, fun s hs ↦ by
        rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.mp hs),
      fun s hs ↦ by rw [coeffTensor_tmul, notMem_support_iff.mp hs, zero_smul], ?_⟩
    conv_rhs => rw [as_sum p, TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun s _ ↦ by
      rw [coeffTensor_tmul, ← TensorProduct.smul_tmul, smul_monomial, smul_eq_mul, mul_one]
  · obtain ⟨⟨S₁, hdeg₁, h0₁, hsum₁⟩, ⟨S₂, hdeg₂, h0₂, hsum₂⟩⟩ := hx, hy
    refine ⟨S₁ ∪ S₂, fun s hs ↦ (Finset.mem_union.mp hs).elim (hdeg₁ s) (hdeg₂ s), fun s hs ↦ ?_,
      ?_⟩
    · rw [Finset.mem_union, not_or] at hs; simp [h0₁ s hs.1, h0₂ s hs.2]
    · have hsub {z : MvPolynomial σ R ⊗[R] M} {S} (h0 : ∀ s ∉ S, coeffTensor s z = 0)
          (hs : S ⊆ S₁ ∪ S₂) :
          ∑ s ∈ S₁ ∪ S₂, monomial s (1 : R) ⊗ₜ[R] coeffTensor s z =
            ∑ s ∈ S, monomial s (1 : R) ⊗ₜ[R] coeffTensor s z :=
        (Finset.sum_subset hs fun s _ h ↦ by rw [h0 s h, TensorProduct.tmul_zero]).symm
      simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib,
        hsub h0₁ Finset.subset_union_left, hsub h0₂ Finset.subset_union_right, hsum₁, hsum₂]

@[simp] theorem homogeneousComponentTensor_mem (k : ℕ) (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k u ∈ homogeneousTensorSubmodule σ R M k := by
  rw [homogeneousComponentTensor_def, ← subtype_comp_homogeneousComponentRestrict,
    LinearMap.rTensor_comp_apply]
  exact ⟨(homogeneousComponentRestrict k).rTensor M u, rfl⟩

theorem homogeneousComponentTensor_eq_self {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) : homogeneousComponentTensor k u = u :=
  mem_homogeneousTensorSubmodule_iff.mp hu

@[simp] theorem homogeneousComponentTensor_idem (k : ℕ) (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k (homogeneousComponentTensor k u) =
      homogeneousComponentTensor k u :=
  homogeneousComponentTensor_eq_self (homogeneousComponentTensor_mem k u)

theorem homogeneousComponentTensor_of_mem {k j : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    homogeneousComponentTensor j u = if j = k then u else 0 :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp _ ↦ by
      rw [homogeneousComponentTensor_tmul, homogeneousComponent_of_mem hp]; split_ifs <;> simp)
    fun hx hy ↦ by rw [map_add, hx, hy]; split_ifs <;> simp

theorem homogeneousComponentTensor_eq_zero_of_ne {k j : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) (hjk : j ≠ k) :
    homogeneousComponentTensor j u = 0 := by
  rw [homogeneousComponentTensor_of_mem hu, ite_eq_right_iff.mpr fun h ↦ (hjk h).elim]

private theorem sum_range_homogeneousComponentTensor_of_le {u : MvPolynomial σ R ⊗[R] M}
    {N M' : ℕ} (hN : ∑ k ∈ Finset.range N, homogeneousComponentTensor k u = u) (hNM : N ≤ M') :
    ∑ k ∈ Finset.range M', homogeneousComponentTensor k u = u := by
  refine (Finset.sum_subset (Finset.range_mono hNM) fun k _ hk ↦ ?_).symm.trans hN
  rw [← hN, map_sum]
  refine Finset.sum_eq_zero fun j hj ↦
    homogeneousComponentTensor_eq_zero_of_ne (homogeneousComponentTensor_mem j u) ?_
  simp only [Finset.mem_range] at hj hk; omega

theorem exists_sum_homogeneousComponentTensor_eq (u : MvPolynomial σ R ⊗[R] M) :
    ∃ N : ℕ, ∑ k ∈ Finset.range N, homogeneousComponentTensor k u = u := by
  induction u using TensorProduct.inductionOn with
  | tmul p m =>
    exact ⟨p.totalDegree + 1, by
      simp_rw [homogeneousComponentTensor_tmul, ← TensorProduct.sum_tmul, sum_homogeneousComponent]⟩
  | add u₁ u₂ hu₁ hu₂ =>
    obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := hu₁, hu₂
    exact ⟨max N₁ N₂, by
      rw [Finset.sum_congr rfl fun k _ ↦ map_add (homogeneousComponentTensor k) u₁ u₂,
        Finset.sum_add_distrib, sum_range_homogeneousComponentTensor_of_le hN₁ (le_max_left _ _),
        sum_range_homogeneousComponentTensor_of_le hN₂ (le_max_right _ _)]⟩

theorem exists_sum_homogeneousComponentTensor_eq_of_le (u : MvPolynomial σ R ⊗[R] M) (m : ℕ) :
    ∃ N : ℕ, m ≤ N ∧ ∑ k ∈ Finset.range N, homogeneousComponentTensor k u = u :=
  let ⟨N, hN⟩ := exists_sum_homogeneousComponentTensor_eq u
  ⟨max m N, le_max_left m N, sum_range_homogeneousComponentTensor_of_le hN (le_max_right m N)⟩

theorem ext_homogeneousComponentTensor {u v : MvPolynomial σ R ⊗[R] M}
    (h : ∀ k : ℕ, homogeneousComponentTensor k u = homogeneousComponentTensor k v) : u = v := by
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ :=
    exists_sum_homogeneousComponentTensor_eq u, exists_sum_homogeneousComponentTensor_eq v
  rw [← sum_range_homogeneousComponentTensor_of_le hN₁ (le_max_left N₁ N₂),
    ← sum_range_homogeneousComponentTensor_of_le hN₂ (le_max_right N₁ N₂)]
  exact Finset.sum_congr rfl fun k _ ↦ h k

theorem eq_zero_of_forall_homogeneousComponentTensor_eq_zero {u : MvPolynomial σ R ⊗[R] M}
    (h : ∀ k : ℕ, homogeneousComponentTensor k u = 0) : u = 0 :=
  ext_homogeneousComponentTensor fun k ↦ by simp [h k]

section HomogeneousTensorEquiv

attribute [local instance] MvPolynomial.decomposition

-- `DirectSum.decomposeTensor` is not `@[expose]` under Lean's `module` system, so
-- `LinearEquiv.ofEq` with `DirectSum.decomposeTensor_apply` is needed to match the codomain.
variable (σ R M) in
/-- Canonical equivalence `homogeneousSubmodule σ R k ⊗[R] M ≃ₗ[R] homogeneousTensorSubmodule`. -/
noncomputable def homogeneousTensorEquiv (k : ℕ) :
    homogeneousSubmodule σ R k ⊗[R] M ≃ₗ[R] homogeneousTensorSubmodule σ R M k :=
  (DirectSum.decomposeTensorEquiv (homogeneousSubmodule σ R) M k).trans
    (LinearEquiv.ofEq _ _ (by rw [DirectSum.decomposeTensor_apply]; rfl))

@[simp] theorem coe_homogeneousTensorEquiv_tmul (k : ℕ) (p : homogeneousSubmodule σ R k) (m : M) :
    (homogeneousTensorEquiv σ R M k (p ⊗ₜ[R] m) : MvPolynomial σ R ⊗[R] M) =
      (p : MvPolynomial σ R) ⊗ₜ[R] m := by
  simp [homogeneousTensorEquiv]

end HomogeneousTensorEquiv

private theorem one_tmul_coeffTensor_zero {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M 0) :
    (1 : MvPolynomial σ R) ⊗ₜ[R] coeffTensor 0 u = u :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun {p} hp _ ↦ by
      have hpC : p = C (p.coeff 0) := ext _ _ fun s ↦ by
        classical rw [coeff_C]; split_ifs with hs
        · exact congrArg p.coeff hs.symm
        · exact hp.coeff_eq_zero fun hd ↦ hs ((Finsupp.degree_eq_zero_iff s).mp hd).symm
      rw [coeffTensor_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, algebraMap_eq,
        ← hpC])
    fun hx hy ↦ by rw [map_add, TensorProduct.tmul_add, hx, hy]

variable (σ R M) in
/-- Canonical linear equivalence `M ≃ₗ[R] homogeneousTensorSubmodule σ R M 0` (`m ↦ 1 ⊗ₜ m`). -/
noncomputable def homogeneousTensorZeroEquiv : M ≃ₗ[R] homogeneousTensorSubmodule σ R M 0 :=
  LinearEquiv.ofLinearMap
    ((TensorProduct.mk R (MvPolynomial σ R) M 1).codRestrict (homogeneousTensorSubmodule σ R M 0)
      fun m ↦ (TensorProduct.mk_apply (R := R) (1 : MvPolynomial σ R) m).symm ▸
        tmul_mem_homogeneousTensorSubmodule (isHomogeneous_one σ R) m)
    (coeffTensor 0 ∘ₗ (homogeneousTensorSubmodule σ R M 0).subtype)
    (LinearMap.ext fun ⟨_, hu⟩ ↦ Subtype.ext (one_tmul_coeffTensor_zero hu))
    (LinearMap.ext fun _ ↦ by simp)

@[simp] theorem coe_homogeneousTensorZeroEquiv_apply (m : M) :
    (homogeneousTensorZeroEquiv σ R M m : MvPolynomial σ R ⊗[R] M) = 1 ⊗ₜ[R] m := (rfl)

@[simp] theorem homogeneousTensorZeroEquiv_symm_apply (u : homogeneousTensorSubmodule σ R M 0) :
    (homogeneousTensorZeroEquiv σ R M).symm u = coeffTensor 0 (u : MvPolynomial σ R ⊗[R] M) :=
  (rfl)

@[simp] theorem homogeneousTensorSubmodule_succ_eq_bot_of_isEmpty [IsEmpty σ] (k : ℕ) :
    homogeneousTensorSubmodule σ R M (k + 1) = ⊥ :=
  eq_bot_iff.mpr fun _ hu ↦ homogeneousTensorSubmodule_inductionOn hu
    (fun {p} hp _ ↦ by
      have hp0 : p ∈ (⊥ : Submodule R (MvPolynomial σ R)) :=
        homogeneousSubmodule_succ_eq_bot_of_isEmpty (R := R) (σ := σ) k ▸ hp
      simp [(Submodule.mem_bot R).mp hp0])
    fun hx hy ↦ Submodule.add_mem ⊥ hx hy

/-- Finite variables and a finite coefficient module make `homogeneousTensorSubmodule` finite. -/
instance [Finite σ] [Module.Finite R M] (k : ℕ) :
    Module.Finite R (homogeneousTensorSubmodule σ R M k) := Module.Finite.range _

theorem euler_rTensor_eq_nsmul {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) : euler.toLinearMap.rTensor M u = k • u :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp _ ↦ by rw [LinearMap.rTensor_tmul, Derivation.coeFn_coe, hp.euler_eq,
      ← TensorProduct.smul_tmul'])
    fun hx hy ↦ by simp [map_add, hx, hy]

end General

section Fintype

variable {σ R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype σ]

/-- Rank of degree-`k` `M`-valued homogeneous polynomials over a free `R`-module `M`. -/
theorem finrank_homogeneousTensorSubmodule [StrongRankCondition R] [Module.Free R M] (k : ℕ) :
    Module.finrank R (homogeneousTensorSubmodule σ R M k) =
      (Fintype.card σ).multichoose k * Module.finrank R M := by
  rw [← (homogeneousTensorEquiv σ R M k).finrank_eq, Module.finrank_tensorProduct,
    TauCeti.finrank_homogeneousSubmodule_eq_multichoose]

theorem laplacian_rTensor_mem_homogeneousTensorSubmodule {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    laplacian.rTensor M u ∈ homogeneousTensorSubmodule σ R M (k - 2) :=
  rTensor_mem_homogeneousTensorSubmodule IsHomogeneous.laplacian hu

theorem laplacian_rTensor_eq_zero_of_le_one {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) (hk : k ≤ 1) : laplacian.rTensor M u = 0 :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp _ ↦ by simp [hp.laplacian_eq_zero_of_le_one hk])
    fun hx hy ↦ by simp [map_add, hx, hy]

theorem normSq_mul_rTensor_mem_homogeneousTensorSubmodule {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    (LinearMap.mulLeft R (normSq σ R)).rTensor M u ∈ homogeneousTensorSubmodule σ R M (k + 2) :=
  rTensor_mem_homogeneousTensorSubmodule
    (fun hp ↦ by simpa [add_comm] using (isHomogeneous_normSq σ R).mul hp) hu

/-- **The Laplacian of `r² u`** on `homogeneousTensorSubmodule σ R M k`. -/
theorem laplacian_normSq_mul_rTensor {k : ℕ} {u : MvPolynomial σ R ⊗[R] M}
    (hu : u ∈ homogeneousTensorSubmodule σ R M k) :
    laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M u) =
      (LinearMap.mulLeft R (normSq σ R)).rTensor M (laplacian.rTensor M u) +
        (2 * Fintype.card σ + 4 * k) • u :=
  homogeneousTensorSubmodule_inductionOn hu
    (fun hp _ ↦ by simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply,
      laplacian_normSq_mul hp, TensorProduct.add_tmul, ← TensorProduct.smul_tmul'])
    fun hx hy ↦ by simp only [map_add, hx, hy, smul_add]; abel

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
  have hN : N ≠ 0 := by have := Fintype.card_pos (α := σ); omega
  suffices hΔ : laplacian.rTensor M u = 0 by
    rw [hΔ, map_zero, zero_add] at h
    exact IsSMulRegular.nat_of_hasUniqueDiv hN (by simpa using h)
  rcases lt_or_ge e 2 with he | he
  · exact laplacian_rTensor_eq_zero_of_le_one hu (by omega)
  exact @ih (e - 2) (by omega) _ N (laplacian_rTensor_mem_homogeneousTensorSubmodule hu) <| by
    simpa only [map_add, map_nsmul, map_zero] using congrArg (laplacian.rTensor M) h

@[simp] theorem homogeneousComponentTensor_laplacian_normSq_mul (k : ℕ)
    (u : MvPolynomial σ R ⊗[R] M) :
    homogeneousComponentTensor k
        (laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M u)) =
      laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M
        (homogeneousComponentTensor k u)) := by
  obtain ⟨N, hkN, hN⟩ := exists_sum_homogeneousComponentTensor_eq_of_le u (k + 1)
  have hmem (j : ℕ) : laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M
      (homogeneousComponentTensor j u)) ∈ homogeneousTensorSubmodule σ R M j := by
    simpa using laplacian_rTensor_mem_homogeneousTensorSubmodule
      (normSq_mul_rTensor_mem_homogeneousTensorSubmodule (homogeneousComponentTensor_mem j u))
  conv_lhs => rw [← hN]
  simp only [map_sum]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hkN),
    homogeneousComponentTensor_eq_self (hmem k)]
  exact fun j _ hj ↦ homogeneousComponentTensor_eq_zero_of_ne (hmem j) (Ne.symm hj)

/-- **Trivial kernel of `u ↦ Δ (r² u)`** under `[Nonempty σ]` and `[HasUniqueDiv M]`. -/
theorem eq_zero_of_laplacian_normSq_mul_rTensor_eq_zero [Nonempty σ] [HasUniqueDiv M]
    {u : MvPolynomial σ R ⊗[R] M}
    (h : laplacian.rTensor M ((LinearMap.mulLeft R (normSq σ R)).rTensor M u) = 0) : u = 0 := by
  refine eq_zero_of_forall_homogeneousComponentTensor_eq_zero fun k ↦
    eq_zero_of_laplacian_normSq_mul_rTensor_add_nsmul_eq_zero (m := 0)
      (homogeneousComponentTensor_mem k u) ?_
  rw [zero_smul, add_zero, ← homogeneousComponentTensor_laplacian_normSq_mul, h, map_zero]

end Fintype

end MvPolynomial
