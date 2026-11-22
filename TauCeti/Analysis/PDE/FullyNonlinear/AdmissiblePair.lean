/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.Convex.Strong
import TauCeti.Analysis.MeanInequalities

/-!
# Admissible cones and admissible pairs

A fully nonlinear equation of eigenvalue type, such as a complex Hessian equation, prescribes a
symmetric function `f` of the eigenvalue vector `λ` of a Hermitian form, which is required to lie
in an open cone `Γ ⊆ ℝⁿ`. The standard hypotheses on
the pair `(f, Γ)` are the following.

* `Γ` is an *admissible cone* (`TauCeti.IsAdmissibleCone`): it is open, invariant under
  permutations of the coordinates and under positive dilations, and lies between the positive
  orthant `Γ_n = {μ | ∀ i, 0 < μ i}` and the half-space `Γ_1 = {μ | 0 < ∑ i, μ i}`.
* `(f, Γ)` is an *admissible pair* (`TauCeti.IsAdmissiblePair`): `Γ` is an admissible cone and
  `f` is `C¹` on `Γ`, symmetric, positively homogeneous of degree one and elliptic, that is,
  `∂_j f > 0` on `Γ` for every `j`.
* The pair satisfies the *structural condition* of Guo, Phong and Tong with constant `γ`
  (`TauCeti.HasStructuralConstant`) when `∏_j ∂_j f ≥ γ` on `Γ`.

Only the values of `f` on `Γ` enter, so the conditions are stated as predicates on a set and a
function on all of `ℝⁿ`. The model pairs are the Laplace pair `(σ_1, Γ_1)` with constant `1`, and
the Monge–Ampère pair `((∏_i μ_i)^{1/n}, Γ_n)` with constant `n^{-n}`.

This file proves the basic theory: an admissible pair is positive on `Γ_n`, by Euler's identity
`∑_j μ_j ∂_j f(μ) = f(μ)`; admissible pairs and their structural constants restrict to smaller
admissible cones; and positive combinations `a f₁ + b f₂` on `Γ₁ ∩ Γ₂` are admissible pairs, with
structural constant `(a c₁ + b c₂)ⁿ` when `f₁` and `f₂` have constants `c₁ⁿ` and `c₂ⁿ`, by the
superadditivity of the geometric mean (`Real.prod_rpow_add_prod_rpow_le_prod_add_rpow`). The
structural constant of a concave pair can be read off from a lower bound on `Γ_n`: if
`f(μ) ≥ n c (∏_i μ_i)^{1/n}` there, the pair has structural constant `cⁿ`
(`TauCeti.IsAdmissiblePair.hasStructuralConstant_pow_of_concaveOn`). The proof evaluates the
tangent inequality `f(ν) ≤ ∑_j ν_j ∂_j f(μ)` of a concave homogeneous function
(`ConcaveOn.le_apply_of_hasFDerivAt_of_homogeneous`) at `ν_j = 1/∂_j f(μ)`.

## Main definitions

* `TauCeti.IsAdmissibleCone`: admissible cones in `ℝ^ι`.
* `TauCeti.IsAdmissiblePair`: admissible pairs `(f, Γ)`.
* `TauCeti.HasStructuralConstant`: the structural condition `∏_j ∂_j f ≥ γ` on `Γ`.

## Main results

* `TauCeti.IsAdmissibleCone.inter`, `TauCeti.isAdmissibleCone_setOf_sum_pos`,
  `TauCeti.isAdmissibleCone_setOf_forall_pos`: intersections of admissible cones, `Γ_1` and `Γ_n`
  are admissible.
* `TauCeti.IsAdmissiblePair.sum_mul_fderiv_single`: Euler's identity.
* `TauCeti.IsAdmissiblePair.pos_of_forall_pos`: an admissible pair is positive on `Γ_n`.
* `TauCeti.IsAdmissiblePair.const_smul`, `TauCeti.IsAdmissiblePair.add`, and the corresponding
  `TauCeti.HasStructuralConstant.const_smul` and `TauCeti.HasStructuralConstant.add`: positive
  combinations of admissible pairs and their structural constants.
* `TauCeti.IsAdmissiblePair.hasStructuralConstant_pow_of_concaveOn`: the structural constant of a
  concave admissible pair from a lower bound on `Γ_n` (Guo–Phong–Tong, Lemma 4).
* `TauCeti.isAdmissiblePair_sum`, `TauCeti.hasStructuralConstant_sum`: the Laplace pair.
* `TauCeti.isAdmissiblePair_prod_rpow`, `TauCeti.hasStructuralConstant_prod_rpow`: the
  Monge–Ampère pair, which is concave by `Real.concaveOn_prod_rpow`.

## References

* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), §1 and Lemma 4.
* B. Guo and D. H. Phong, *On the lower bound of the Green's function and applications*,
  (2024), conditions (1)–(3) and (1.2).
* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), §2.
-/

public section

open Finset Filter Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ### Admissible cones -/

/-- An **admissible cone** `Γ ⊆ ℝ^ι`: an open set, invariant under permutations of the coordinates
and under positive dilations, that contains the positive orthant `Γ_n = {μ | ∀ i, 0 < μ i}` and is
contained in the half-space `Γ_1 = {μ | 0 < ∑ i, μ i}`. -/
structure IsAdmissibleCone (Γ : Set (ι → ℝ)) : Prop where
  isOpen : IsOpen Γ
  comp_perm_mem (σ : Equiv.Perm ι) {μ : ι → ℝ} : μ ∈ Γ → μ ∘ σ ∈ Γ
  smul_mem {t : ℝ} (ht : 0 < t) {μ : ι → ℝ} : μ ∈ Γ → t • μ ∈ Γ
  mem_of_forall_pos {μ : ι → ℝ} : (∀ i, 0 < μ i) → μ ∈ Γ
  sum_pos {μ : ι → ℝ} : μ ∈ Γ → 0 < ∑ i, μ i

namespace IsAdmissibleCone

variable {Γ Γ' : Set (ι → ℝ)}

/-- An admissible cone exists only in positive dimension: in `ℝ⁰` the zero vector would lie in
the positive orthant but not in the half-space `Γ_1`. -/
theorem nonempty (hΓ : IsAdmissibleCone Γ) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  simpa using hΓ.sum_pos (hΓ.mem_of_forall_pos (μ := 0) isEmptyElim)

/-- An admissible cone contains the positive orthant `Γ_n`. -/
theorem setOf_forall_pos_subset (hΓ : IsAdmissibleCone Γ) : {μ : ι → ℝ | ∀ i, 0 < μ i} ⊆ Γ :=
  fun _ ↦ hΓ.mem_of_forall_pos

/-- An admissible cone is contained in the half-space `Γ_1`. -/
theorem subset_setOf_sum_pos (hΓ : IsAdmissibleCone Γ) : Γ ⊆ {μ : ι → ℝ | 0 < ∑ i, μ i} :=
  fun _ ↦ hΓ.sum_pos

/-- The intersection of two admissible cones is an admissible cone. -/
theorem inter (hΓ : IsAdmissibleCone Γ) (hΓ' : IsAdmissibleCone Γ') :
    IsAdmissibleCone (Γ ∩ Γ') where
  isOpen := hΓ.isOpen.inter hΓ'.isOpen
  comp_perm_mem σ _ hμ := ⟨hΓ.comp_perm_mem σ hμ.1, hΓ'.comp_perm_mem σ hμ.2⟩
  smul_mem ht _ hμ := ⟨hΓ.smul_mem ht hμ.1, hΓ'.smul_mem ht hμ.2⟩
  mem_of_forall_pos hμ := ⟨hΓ.mem_of_forall_pos hμ, hΓ'.mem_of_forall_pos hμ⟩
  sum_pos hμ := hΓ.sum_pos hμ.1

end IsAdmissibleCone

/-- The half-space `Γ_1 = {μ | 0 < ∑ i, μ i}` is an admissible cone, the largest one. -/
theorem isAdmissibleCone_setOf_sum_pos [Nonempty ι] :
    IsAdmissibleCone {μ : ι → ℝ | 0 < ∑ i, μ i} where
  isOpen := isOpen_lt continuous_const (by fun_prop)
  comp_perm_mem σ μ hμ := by simpa [Equiv.sum_comp σ μ] using hμ
  smul_mem ht μ hμ := by simpa [← mul_sum] using mul_pos ht hμ
  mem_of_forall_pos hμ := sum_pos (fun i _ ↦ hμ i) univ_nonempty
  sum_pos hμ := hμ

/-- The positive orthant `Γ_n = {μ | ∀ i, 0 < μ i}` is an admissible cone, the smallest one. -/
theorem isAdmissibleCone_setOf_forall_pos [Nonempty ι] :
    IsAdmissibleCone {μ : ι → ℝ | ∀ i, 0 < μ i} where
  isOpen := by
    simpa only [Set.ofPred_forall] using
      isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)
  comp_perm_mem σ μ hμ i := hμ (σ i)
  smul_mem ht μ hμ i := mul_pos ht (hμ i)
  mem_of_forall_pos hμ := hμ
  sum_pos hμ := sum_pos (fun i _ ↦ hμ i) univ_nonempty

/-! ### Admissible pairs and the structural condition -/

variable [DecidableEq ι]

/-- An **admissible pair** `(f, Γ)`: `Γ` is an admissible cone and `f` is `C¹` on `Γ`, symmetric
under permutations of the coordinates, positively homogeneous of degree one and elliptic, that is,
its partial derivatives `∂_j f = fderiv ℝ f μ (Pi.single j 1)` are positive on `Γ`. Only the
values of `f` on `Γ` matter. -/
structure IsAdmissiblePair (Γ : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) : Prop where
  isAdmissibleCone : IsAdmissibleCone Γ
  contDiffOn : ContDiffOn ℝ 1 f Γ
  apply_comp_perm (σ : Equiv.Perm ι) {μ : ι → ℝ} : μ ∈ Γ → f (μ ∘ σ) = f μ
  apply_smul {t : ℝ} (ht : 0 < t) {μ : ι → ℝ} : μ ∈ Γ → f (t • μ) = t * f μ
  fderiv_single_pos {μ : ι → ℝ} : μ ∈ Γ → ∀ j, 0 < fderiv ℝ f μ (Pi.single j 1)

/-- The **structural condition** with constant `γ`: the product of the partial derivatives of `f`
is at least `γ` on `Γ`. -/
structure HasStructuralConstant (Γ : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) (γ : ℝ) : Prop where
  le_prod_fderiv_single {μ : ι → ℝ} : μ ∈ Γ → γ ≤ ∏ j, fderiv ℝ f μ (Pi.single j 1)

/-- `LinearMap.pi_apply_eq_sum_univ` for a continuous linear functional, with the standard basis
written as `Pi.single j 1`. -/
private theorem apply_eq_sum_mul_single (L : (ι → ℝ) →L[ℝ] ℝ) (ν : ι → ℝ) :
    L ν = ∑ j, ν j * L (Pi.single j 1) := by
  have hsingle (j : ι) : (fun k ↦ if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    ext k
    simp [Pi.single_apply, eq_comm]
  simpa only [hsingle, smul_eq_mul, ContinuousLinearMap.coe_coe] using
    L.toLinearMap.pi_apply_eq_sum_univ ν

namespace IsAdmissiblePair

variable {Γ Γ' Γ₁ Γ₂ : Set (ι → ℝ)} {f f₁ f₂ : (ι → ℝ) → ℝ} {μ : ι → ℝ}

/-- The function of an admissible pair is differentiable at every point of its cone. -/
theorem differentiableAt (h : IsAdmissiblePair Γ f) (hμ : μ ∈ Γ) : DifferentiableAt ℝ f μ :=
  (h.contDiffOn.differentiableOn one_ne_zero μ hμ).differentiableAt
    (h.isAdmissibleCone.isOpen.mem_nhds hμ)

/-- `f (t • μ) = t * f μ` for `t` near `1`, the form of homogeneity used by Euler's identity. -/
theorem eventually_apply_smul (h : IsAdmissiblePair Γ f) (hμ : μ ∈ Γ) :
    ∀ᶠ t in 𝓝 (1 : ℝ), f (t • μ) = t * f μ := by
  filter_upwards [lt_mem_nhds one_pos] with t ht using h.apply_smul ht hμ

/-- **Euler's identity** for an admissible pair: `Df(μ) μ = f(μ)` on `Γ`. -/
theorem fderiv_apply_self (h : IsAdmissiblePair Γ f) (hμ : μ ∈ Γ) : fderiv ℝ f μ μ = f μ := by
  simpa using (h.differentiableAt hμ).hasFDerivAt.apply_self_eq_smul_of_eventuallyEq
    (hasDerivAt_id (1 : ℝ)) (h.eventually_apply_smul hμ)

/-- **Euler's identity** for an admissible pair: `∑_j μ_j ∂_j f(μ) = f(μ)` on `Γ`. -/
theorem sum_mul_fderiv_single (h : IsAdmissiblePair Γ f) (hμ : μ ∈ Γ) :
    ∑ j, μ j * fderiv ℝ f μ (Pi.single j 1) = f μ := by
  rw [← apply_eq_sum_mul_single, h.fderiv_apply_self hμ]

/-- An admissible pair is positive on the positive orthant `Γ_n`. -/
theorem pos_of_forall_pos (h : IsAdmissiblePair Γ f) (hμ : ∀ i, 0 < μ i) : 0 < f μ := by
  have := h.isAdmissibleCone.nonempty
  have hμΓ := h.isAdmissibleCone.mem_of_forall_pos hμ
  rw [← h.sum_mul_fderiv_single hμΓ]
  exact sum_pos (fun j _ ↦ mul_pos (hμ j) (h.fderiv_single_pos hμΓ j)) univ_nonempty

/-- The restriction of an admissible pair to a smaller admissible cone is an admissible pair. -/
theorem mono (h : IsAdmissiblePair Γ f) (hΓ' : IsAdmissibleCone Γ') (hsub : Γ' ⊆ Γ) :
    IsAdmissiblePair Γ' f where
  isAdmissibleCone := hΓ'
  contDiffOn := h.contDiffOn.mono hsub
  apply_comp_perm σ _ hμ := h.apply_comp_perm σ (hsub hμ)
  apply_smul ht _ hμ := h.apply_smul ht (hsub hμ)
  fderiv_single_pos hμ := h.fderiv_single_pos (hsub hμ)

/-- A positive multiple of an admissible pair is an admissible pair. -/
theorem const_smul (h : IsAdmissiblePair Γ f) {c : ℝ} (hc : 0 < c) :
    IsAdmissiblePair Γ (c • f) where
  isAdmissibleCone := h.isAdmissibleCone
  contDiffOn := h.contDiffOn.const_smul c
  apply_comp_perm σ _ hμ := by simp [h.apply_comp_perm σ hμ]
  apply_smul ht _ hμ := by simp only [Pi.smul_apply, smul_eq_mul, h.apply_smul ht hμ]; ring
  fderiv_single_pos hμ j := by
    simp only [fderiv_const_smul_field, Pi.smul_apply, FunLike.coe_smul, smul_eq_mul]
    exact mul_pos hc (h.fderiv_single_pos hμ j)

private theorem fderiv_add_apply (h₁ : IsAdmissiblePair Γ₁ f₁) (h₂ : IsAdmissiblePair Γ₂ f₂)
    (hμ : μ ∈ Γ₁ ∩ Γ₂) (v : ι → ℝ) :
    fderiv ℝ (f₁ + f₂) μ v = fderiv ℝ f₁ μ v + fderiv ℝ f₂ μ v := by
  simp [fderiv_add (h₁.differentiableAt hμ.1) (h₂.differentiableAt hμ.2)]

/-- The sum of two admissible pairs is an admissible pair on the intersection of their cones. -/
theorem add (h₁ : IsAdmissiblePair Γ₁ f₁) (h₂ : IsAdmissiblePair Γ₂ f₂) :
    IsAdmissiblePair (Γ₁ ∩ Γ₂) (f₁ + f₂) where
  isAdmissibleCone := h₁.isAdmissibleCone.inter h₂.isAdmissibleCone
  contDiffOn := (h₁.contDiffOn.mono Set.inter_subset_left).add
    (h₂.contDiffOn.mono Set.inter_subset_right)
  apply_comp_perm σ _ hμ := by simp [h₁.apply_comp_perm σ hμ.1, h₂.apply_comp_perm σ hμ.2]
  apply_smul ht _ hμ := by
    simp only [Pi.add_apply, h₁.apply_smul ht hμ.1, h₂.apply_smul ht hμ.2]; ring
  fderiv_single_pos hμ j := by
    rw [fderiv_add_apply h₁ h₂ hμ]
    exact add_pos (h₁.fderiv_single_pos hμ.1 j) (h₂.fderiv_single_pos hμ.2 j)

/-- Every admissible pair satisfies the structural condition with constant `0`. -/
theorem hasStructuralConstant_zero (h : IsAdmissiblePair Γ f) : HasStructuralConstant Γ f 0 :=
  ⟨fun hμ ↦ (prod_pos fun j _ ↦ h.fderiv_single_pos hμ j).le⟩

/-- **The structural constant from a lower bound on `Γ_n`** (Guo–Phong–Tong 2023, Lemma 4). A
concave admissible pair with `f(μ) ≥ n c (∏_i μ_i)^{1/n}` on the positive orthant, where
`n = card ι` and `c ≥ 0`, satisfies the structural condition with constant `cⁿ`. -/
theorem hasStructuralConstant_pow_of_concaveOn (h : IsAdmissiblePair Γ f)
    (hf : ConcaveOn ℝ Γ f) {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ μ : ι → ℝ, (∀ i, 0 < μ i) →
      Fintype.card ι * c * (∏ i, μ i) ^ (Fintype.card ι : ℝ)⁻¹ ≤ f μ) :
    HasStructuralConstant Γ f (c ^ Fintype.card ι) := by
  refine ⟨fun {μ} hμ ↦ ?_⟩
  have := h.isAdmissibleCone.nonempty
  set n := Fintype.card ι
  set a : ι → ℝ := fun j ↦ fderiv ℝ f μ (Pi.single j 1)
  have ha (j : ι) : 0 < a j := h.fderiv_single_pos hμ j
  have hP : 0 < ∏ j, a j := prod_pos fun j _ ↦ ha j
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 Fintype.card_pos
  -- Evaluate the tangent inequality at `ν = (1 / a j)_j`, where `∑_j ν_j a_j = n`.
  set ν : ι → ℝ := fun j ↦ (a j)⁻¹
  have hν (j : ι) : 0 < ν j := inv_pos.2 (ha j)
  have htan : f ν ≤ n := by
    have := hf.le_apply_of_hasFDerivAt_of_homogeneous hμ
      (h.isAdmissibleCone.mem_of_forall_pos hν) (h.differentiableAt hμ).hasFDerivAt
      (h.eventually_apply_smul hμ)
    rwa [apply_eq_sum_mul_single, sum_congr rfl fun j _ ↦ inv_mul_cancel₀ (ha j).ne',
      sum_const, card_univ, nsmul_eq_mul, mul_one] at this
  -- With `G = (∏_j a_j)^{1/n}`, the lower bound at `ν` reads `n c / G ≤ f ν`.
  set G := (∏ j, a j) ^ (n : ℝ)⁻¹
  have hG : 0 < G := Real.rpow_pos_of_pos hP _
  have hνG : (∏ j, ν j) ^ (n : ℝ)⁻¹ = G⁻¹ := by
    rw [prod_inv_distrib, Real.inv_rpow hP.le]
  have hcG : c ≤ G := by
    have := (hle ν hν).trans htan
    rw [hνG, ← div_eq_mul_inv, div_le_iff₀ hG] at this
    nlinarith
  calc c ^ n ≤ G ^ n := pow_le_pow_left₀ hc hcG n
    _ = ∏ j, a j := Real.rpow_inv_natCast_pow hP.le Fintype.card_ne_zero

end IsAdmissiblePair

namespace HasStructuralConstant

variable {Γ Γ' Γ₁ Γ₂ : Set (ι → ℝ)} {f f₁ f₂ : (ι → ℝ) → ℝ} {γ c₁ c₂ : ℝ}

/-- A structural constant on `Γ` is a structural constant on every subset of `Γ`. -/
theorem mono (h : HasStructuralConstant Γ f γ) (hsub : Γ' ⊆ Γ) :
    HasStructuralConstant Γ' f γ :=
  ⟨fun hμ ↦ h.le_prod_fderiv_single (hsub hμ)⟩

/-- If `f` has structural constant `γ`, then `c • f` has structural constant `cⁿ γ` for `c ≥ 0`,
where `n = card ι`. -/
theorem const_smul (h : HasStructuralConstant Γ f γ) {c : ℝ} (hc : 0 ≤ c) :
    HasStructuralConstant Γ (c • f) (c ^ Fintype.card ι * γ) := by
  refine ⟨fun {μ} hμ ↦ ?_⟩
  simp only [fderiv_const_smul_field, Pi.smul_apply, FunLike.coe_smul, smul_eq_mul,
    prod_mul_distrib, prod_const, card_univ]
  exact mul_le_mul_of_nonneg_left (h.le_prod_fderiv_single hμ) (pow_nonneg hc _)

/-- **Structural constants of a sum** (Guo–Phong 2024). If `f₁` and `f₂` form admissible pairs
with structural constants `c₁ⁿ` and `c₂ⁿ`, where `n = card ι` and `c₁, c₂ ≥ 0`, then `f₁ + f₂`
has structural constant `(c₁ + c₂)ⁿ` on `Γ₁ ∩ Γ₂`. -/
theorem add (hs₁ : HasStructuralConstant Γ₁ f₁ (c₁ ^ Fintype.card ι))
    (hs₂ : HasStructuralConstant Γ₂ f₂ (c₂ ^ Fintype.card ι)) (h₁ : IsAdmissiblePair Γ₁ f₁)
    (h₂ : IsAdmissiblePair Γ₂ f₂) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    HasStructuralConstant (Γ₁ ∩ Γ₂) (f₁ + f₂) ((c₁ + c₂) ^ Fintype.card ι) := by
  refine ⟨fun {μ} hμ ↦ ?_⟩
  have := h₁.isAdmissibleCone.nonempty
  set n := Fintype.card ι
  have hn' : n ≠ 0 := Fintype.card_ne_zero
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn'
  set a : ι → ℝ := fun j ↦ fderiv ℝ f₁ μ (Pi.single j 1)
  set b : ι → ℝ := fun j ↦ fderiv ℝ f₂ μ (Pi.single j 1)
  have ha (j : ι) : 0 ≤ a j := (h₁.fderiv_single_pos hμ.1 j).le
  have hb (j : ι) : 0 ≤ b j := (h₂.fderiv_single_pos hμ.2 j).le
  -- The `n`-th root of a structural constant `cⁿ ≤ ∏_j a_j` is a lower bound for the geometric
  -- mean of the `a_j`.
  have hroot {c : ℝ} {a : ι → ℝ} (hc : 0 ≤ c) (ha : ∀ j, 0 ≤ a j) (hle : c ^ n ≤ ∏ j, a j) :
      c ≤ ∏ j, a j ^ (n : ℝ)⁻¹ := by
    rw [Real.finsetProd_rpow _ _ fun j _ ↦ ha j, ← Real.pow_rpow_inv_natCast hc hn']
    exact Real.rpow_le_rpow (pow_nonneg hc n) hle (inv_nonneg.2 (Nat.cast_nonneg n))
  have hsuper := Real.prod_rpow_add_prod_rpow_le_prod_add_rpow univ (w := fun _ ↦ (n : ℝ)⁻¹)
    (fun _ _ ↦ inv_nonneg.2 (Nat.cast_nonneg n))
    (by rw [sum_const, card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn]) (fun j _ ↦ ha j)
    (fun j _ ↦ hb j)
  have hsum : c₁ + c₂ ≤ (∏ j, (a j + b j)) ^ (n : ℝ)⁻¹ := by
    rw [← Real.finsetProd_rpow _ _ fun j _ ↦ add_nonneg (ha j) (hb j)]
    exact (add_le_add (hroot hc₁ ha (hs₁.le_prod_fderiv_single hμ.1))
      (hroot hc₂ hb (hs₂.le_prod_fderiv_single hμ.2))).trans hsuper
  simp only [h₁.fderiv_add_apply h₂ hμ]
  calc (c₁ + c₂) ^ n ≤ ((∏ j, (a j + b j)) ^ (n : ℝ)⁻¹) ^ n :=
        pow_le_pow_left₀ (add_nonneg hc₁ hc₂) hsum n
    _ = ∏ j, (a j + b j) :=
        Real.rpow_inv_natCast_pow (prod_nonneg fun j _ ↦ add_nonneg (ha j) (hb j)) hn'

end HasStructuralConstant

/-! ### The Laplace pair -/

/-- The partial derivatives of `σ_1` are all `1`. -/
private theorem fderiv_sum_apply_single (μ : ι → ℝ) (j : ι) :
    fderiv ℝ (fun ν : ι → ℝ ↦ ∑ i, ν i) μ (Pi.single j 1) = 1 := by
  rw [(HasFDerivAt.fun_sum fun i _ ↦ hasFDerivAt_apply i μ).fderiv]
  simp [Pi.single_apply]

/-- **The Laplace pair** `(σ_1, Γ_1)` is an admissible pair. -/
theorem isAdmissiblePair_sum [Nonempty ι] :
    IsAdmissiblePair {μ : ι → ℝ | 0 < ∑ i, μ i} fun μ ↦ ∑ i, μ i where
  isAdmissibleCone := isAdmissibleCone_setOf_sum_pos
  contDiffOn := (by fun_prop : ContDiff ℝ 1 fun μ : ι → ℝ ↦ ∑ i, μ i).contDiffOn
  apply_comp_perm σ μ _ := Equiv.sum_comp σ μ
  apply_smul _ _ _ := by simp [← mul_sum]
  fderiv_single_pos _ j := by rw [fderiv_sum_apply_single]; exact one_pos

/-- The partial derivatives of `σ_1` are all `1`, so its structural constant is `1`. -/
theorem hasStructuralConstant_sum (Γ : Set (ι → ℝ)) :
    HasStructuralConstant Γ (fun μ ↦ ∑ i, μ i) 1 :=
  ⟨fun _ ↦ by simp [fderiv_sum_apply_single]⟩

/-! ### The Monge–Ampère pair -/

/-- **The Monge–Ampère pair** `((∏_i μ_i)^{1/n}, Γ_n)`, `n = card ι`, is an admissible pair. -/
theorem isAdmissiblePair_prod_rpow [Nonempty ι] :
    IsAdmissiblePair {μ : ι → ℝ | ∀ i, 0 < μ i}
      fun μ ↦ (∏ i, μ i) ^ (Fintype.card ι : ℝ)⁻¹ where
  isAdmissibleCone := isAdmissibleCone_setOf_forall_pos
  contDiffOn := (contDiff_prod fun i _ ↦ (by fun_prop : ContDiff ℝ 1 fun μ : ι → ℝ ↦ μ i))
    |>.contDiffOn.rpow_const_of_ne fun _ hμ ↦ (prod_pos fun i _ ↦ hμ i).ne'
  apply_comp_perm σ μ _ := by simp only [Function.comp_apply, Equiv.prod_comp σ μ]
  apply_smul ht μ hμ := by simpa using Real.prod_mul_rpow_inv_card ht.le fun i ↦ (hμ i).le
  fderiv_single_pos {μ} hμ j := by
    have hP : 0 < ∏ i, μ i := prod_pos fun i _ ↦ hμ i
    rw [((hasFDerivAt_finsetProd (u := univ) (x := μ)).rpow_const (Or.inl hP.ne')).fderiv]
    simp only [FunLike.coe_smul, FunLike.coe_sum, Pi.smul_apply,
      Finset.sum_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
    exact mul_pos (mul_pos (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))
      (Real.rpow_pos_of_pos hP _)) (prod_pos fun i _ ↦ hμ i)

/-- The Monge–Ampère pair satisfies the structural condition with constant `n⁻ⁿ`, where
`n = card ι`. -/
theorem hasStructuralConstant_prod_rpow :
    HasStructuralConstant {μ : ι → ℝ | ∀ i, 0 < μ i}
      (fun μ ↦ (∏ i, μ i) ^ (Fintype.card ι : ℝ)⁻¹)
      ((Fintype.card ι : ℝ)⁻¹ ^ Fintype.card ι) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ ↦ by simp⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine isAdmissiblePair_prod_rpow.hasStructuralConstant_pow_of_concaveOn
    (Real.concaveOn_prod_rpow.subset (fun μ hμ i ↦ (hμ i).le)
      fun μ hμ ν hν a b ha hb hab i ↦ ?_) (inv_nonneg.2 (Nat.cast_nonneg _)) fun μ _ ↦ ?_
  · simpa using convex_Ioi (0 : ℝ) (hμ i) (hν i) ha hb hab
  · rw [mul_inv_cancel₀ hn, one_mul]

end TauCeti
