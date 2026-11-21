/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Basic
import TauCeti.Analysis.Fourier.Torus.UnitCube
import TauCeti.Analysis.InnerProductSpace.WeakSolution
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The inverse of the Cauchy–Riemann operator on a nontrivial flat line over a torus

Let `ω₁, ω₂ ∈ ℂ` be linearly independent over `ℝ`, and consider the flat Hermitian line over the
torus `ℂ / (ℤ ω₁ + ℤ ω₂)` with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂`, as in
`TauCeti.Analysis.Complex.Wirtinger.FlatTorus.Basic`. Its sections are the functions `u : ℂ → ℂ`
with `u (z + ω₁) = exp (2πiθ₁) u z` and `u (z + ω₂) = exp (2πiθ₂) u z`, and a section is
determined by its values `u (s ω₁ + t ω₂)` in lattice coordinates `(s, t) ∈ [0, 1]²`. The
square-integrable sections are therefore the elements of `L²([0, 1]²)`.

The operators `∂bar` and `-∂` are formally adjoint on sections of a unitary flat line: for `C¹`
sections `u` and `φ` with the same twists,

`∫ ∂bar u · conj φ = -∫ u · conj (∂φ)`

over the fundamental domain in lattice coordinates
(`TauCeti.setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv`).
Accordingly a square-integrable section `y` is a *weak solution* of `∂bar y = f`, for `f` in
`L²([0, 1]²)`, if `∫ y · conj (∂φ) = -∫ f · conj φ` for every `C²` section `φ`; a `C¹` section
`y` with `∂bar y = f` is one.

When the holonomy is nontrivial, the coercivity estimate
`C ∫ |φ|² ≤ ∫ |∂φ|²` of `TauCeti.mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq`,
with `C = π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²) > 0`, bounds the formal adjoint below. This
gives a bounded operator `Q` on `L²([0, 1]²)` of norm at most `C^(-1/2)` such that `Q f` is a weak
solution of `∂bar y = f` for every `f`
(`TauCeti.exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq`), chosen as
`TauCeti.flatLineCRInverse`. Since the
twisted exponentials `exp (2πi ((k₁ + θ₁) s + (k₂ + θ₂) t))`, `k ∈ ℤ²`, are smooth sections whose
`∂` is a nonzero multiple of themselves, and span a dense subspace of `L²([0, 1]²)`
(`TauCeti.UnitAddTorus.ae_eq_zero_of_forall_setIntegral_cexp_mul_eq_zero`), the weak kernel of
`∂bar` is zero (`TauCeti.eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero`): weak
solutions are unique. So `∂bar` is invertible on square-integrable sections of every flat line with
nontrivial holonomy, in the weak sense, and `Q` is its inverse.

If the holonomy has infinite image, every power of the line and every pullback to a finite cover
of the torus has nontrivial holonomy
(`TauCeti.notMem_range_intCast_or_notMem_range_intCast_of_irrational`), on a lattice whose basis
is again linearly independent (`TauCeti.im_conj_intCast_mul_add_mul_intCast_mul_add_ne_zero`), so
`∂bar` is invertible on all of them. These are the leading-order inverses in Taubes's construction
of Seiberg–Witten solutions near a square-zero pseudoholomorphic torus whose normal line is flat
with irrational holonomy, where the leading operator acts on the divisor bundle
`N ⊕ N² ⊕ ⋯ ⊕ Nᵐ` of the normal line `N`.

## Main definitions

* `TauCeti.flatLineTestSections`: the `C²` sections of a flat line, the test sections of the weak
  formulation.
* `TauCeti.flatLineCRInverse`: the inverse of `∂bar` on square-integrable sections of a flat line
  with nontrivial holonomy.

## Main results

* `TauCeti.setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv`:
  integration by parts for sections of a unitary flat line.
* `TauCeti.exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq`: the bounded weak
  inverse of `∂bar` on a flat line with nontrivial holonomy.
* `TauCeti.eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero`: uniqueness of weak
  solutions.
* `TauCeti.norm_flatLineCRInverse_le`, `TauCeti.flatLineCRInverse_apply_eq_iff`: the inverse of
  `∂bar` is bounded and sends `f` to the unique weak solution of `∂bar y = f`.
* `TauCeti.flatLineCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv`: it inverts `∂bar` on `C¹`
  sections.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
-/

public section

open Complex ComplexConjugate MeasureTheory Set
open scoped Real

namespace TauCeti

variable {u φ : ℂ → ℂ} {ω₁ ω₂ χ₁ χ₂ : ℂ} {θ₁ θ₂ : ℝ}

section IntegrationByParts

/-- Pointwise, with `D = Im (conj ω₁ ω₂)`, `2 i D (∂bar u conj φ + u conj ∂φ)` is the combination
`ω₂ F₁ - ω₁ F₂` of the derivatives `F_j = Du ω_j conj φ + u conj (Dφ ω_j)` of `u conj φ` along
the lattice vectors. -/
private theorem two_mul_I_mul_im_mul_conjWirtingerDeriv_mul_conj_add (z : ℂ) :
    (2 * I * (conj ω₁ * ω₂).im : ℂ) *
        (conjWirtingerDeriv u z 1 * conj (φ z) + u z * conj (wirtingerDeriv φ z 1)) =
      ω₂ * (fderiv ℝ u z ω₁ * conj (φ z) + u z * conj (fderiv ℝ φ z ω₁)) -
        ω₁ * (fderiv ℝ u z ω₂ * conj (φ z) + u z * conj (fderiv ℝ φ z ω₂)) := by
  have hD : (2 * I * (conj ω₁ * ω₂).im : ℂ) = ω₂ * conj ω₁ - ω₁ * conj ω₂ := by
    have h := sub_conj (ω₂ * conj ω₁)
    simp only [map_mul, conj_conj] at h
    rw [show (ω₂ * conj ω₁).im = (conj ω₁ * ω₂).im by rw [mul_comm]] at h
    push_cast at h
    linear_combination -h
  simp only [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := u),
    fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv (f := φ), smul_eq_mul,
    map_add, map_mul, conj_conj]
  linear_combination (conjWirtingerDeriv u z 1 * conj (φ z) +
    u z * conj (wirtingerDeriv φ z 1)) * hD

/-- **`∂bar` and `-∂` are formally adjoint on a unitary flat line.** Let `ω₁, ω₂` be linearly
independent over `ℝ`, and let `u` and `φ` be `C¹` functions twisted by the same unit complex numbers
`χ₁`, `χ₂` along `ω₁`, `ω₂`, that is, sections of the same flat Hermitian line over the torus
`ℂ / (ℤ ω₁ + ℤ ω₂)`. Then, over the fundamental domain in lattice coordinates,
`∫ ∂bar u · conj φ = -∫ u · conj (∂φ)`. -/
theorem setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv
    (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 1 φ) (hω : (conj ω₁ * ω₂).im ≠ 0) (hχ₁ : ‖χ₁‖ = 1)
    (hχ₂ : ‖χ₂‖ = 1) (hu₁ : ∀ z, u (z + ω₁) = χ₁ * u z) (hu₂ : ∀ z, u (z + ω₂) = χ₂ * u z)
    (hφ₁ : ∀ z, φ (z + ω₁) = χ₁ * φ z) (hφ₂ : ∀ z, φ (z + ω₂) = χ₂ * φ z) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 * conj (φ (p.1 * ω₁ + p.2 * ω₂)) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        u (p.1 * ω₁ + p.2 * ω₂) * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) := by
  have hcont {g : ℂ → ℂ} (hg : Continuous g) :
      IntegrableOn (fun p : ℝ × ℝ ↦ g (p.1 * ω₁ + p.2 * ω₂)) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (hg.comp continuous_ofReal_fst_mul_add_ofReal_snd_mul).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hint₁ := setIntegral_fderiv_mul_conj_add_mul_conj_fderiv_eq_zero (ω₂ := ω₂) hu hφ hχ₁ hu₁
    hφ₁
  have hint₂ := setIntegral_fderiv_mul_conj_add_mul_conj_fderiv_eq_zero (ω₂ := ω₁) hu hφ hχ₂ hu₂
    hφ₂
  rw [setIntegral_comp_ofReal_fst_mul_add_ofReal_snd_mul_swap (fun z ↦
    fderiv ℝ u z ω₂ * conj (φ z) + u z * conj (fderiv ℝ φ z ω₂))] at hint₂
  -- The integral of `∂bar u conj φ + u conj ∂φ` is `(2 i D)⁻¹ (ω₂ ∫ F₁ - ω₁ ∫ F₂) = 0`.
  have h := integral_sub
    ((hcont (continuous_fderiv_mul_conj_add_mul_conj_fderiv hu hφ ω₁)).const_mul ω₂)
    ((hcont (continuous_fderiv_mul_conj_add_mul_conj_fderiv hu hφ ω₂)).const_mul ω₁)
  simp only [← two_mul_I_mul_im_mul_conjWirtingerDeriv_mul_conj_add, integral_const_mul, hint₁,
    hint₂, mul_zero, sub_zero, mul_eq_zero, mul_ne_zero two_ne_zero I_ne_zero,
    ofReal_eq_zero, hω, false_or] at h
  rw [eq_neg_iff_add_eq_zero, ← integral_add
    (hcont (g := fun z ↦ conjWirtingerDeriv u z 1 * conj (φ z))
      ((hu.continuous_conjWirtingerDeriv_apply 1).mul (continuous_conj.comp hφ.continuous)))
    (hcont (g := fun z ↦ u z * conj (wirtingerDeriv φ z 1))
      (hu.continuous.mul (continuous_conj.comp (hφ.continuous_wirtingerDeriv_apply 1))))]
  exact h

end IntegrationByParts

section WeakInverse

/-- The `C²` sections of the flat line with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`,
`ω₂`: the test sections of the weak formulation. -/
def flatLineTestSections (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {u | ContDiff ℝ 2 u ∧ (∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z) ∧
    ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z}
  add_mem' := by
    rintro u v ⟨hu, hu₁, hu₂⟩ ⟨hv, hv₁, hv₂⟩
    exact ⟨hu.add hv, fun z ↦ by simp [hu₁, hv₁, mul_add], fun z ↦ by simp [hu₂, hv₂, mul_add]⟩
  zero_mem' := ⟨contDiff_const, by simp, by simp⟩
  smul_mem' := by
    rintro c u ⟨hu, hu₁, hu₂⟩
    exact ⟨hu.const_smul c, fun z ↦ by simp [hu₁, mul_left_comm],
      fun z ↦ by simp [hu₂, mul_left_comm]⟩

@[simp]
theorem mem_flatLineTestSections_iff :
    u ∈ flatLineTestSections ω₁ ω₂ θ₁ θ₂ ↔ ContDiff ℝ 2 u ∧
      (∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z) ∧
        ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z :=
  Iff.rfl

/-- A continuous function read in lattice coordinates is square integrable over the fundamental
domain. -/
private theorem memLp_comp_latticeCoord {g : ℂ → ℂ} (hg : Continuous g) :
    MemLp (fun p : ℝ × ℝ ↦ g (p.1 * ω₁ + p.2 * ω₂)) 2
      ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
  (hg.comp continuous_ofReal_fst_mul_add_ofReal_snd_mul).continuousOn
    |>.memLp_restrict_of_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
      (measurableSet_Icc.prod measurableSet_Icc) subset_rfl 2

/-- The inclusion of the test sections into `L²` of the fundamental domain. -/
private noncomputable def sectionToLp (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    flatLineTestSections ω₁ ω₂ θ₁ θ₂ →ₗ[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) where
  toFun u := (memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂) u.property.1.continuous).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ by simp)
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ by simp)

private theorem sectionToLp_apply (u : flatLineTestSections ω₁ ω₂ θ₁ θ₂) :
    sectionToLp ω₁ ω₂ θ₁ θ₂ u = (memLp_comp_latticeCoord u.property.1.continuous).toLp
      (fun p : ℝ × ℝ ↦ (u : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂)) :=
  rfl

/-- The formal adjoint `-∂` of `∂bar` on test sections, with values in `L²` of the fundamental
domain. -/
private noncomputable def negWirtingerToLp (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    flatLineTestSections ω₁ ω₂ θ₁ θ₂ →ₗ[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) where
  toFun u := (memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂)
    ((u.property.1.of_le one_le_two).continuous_wirtingerDeriv_apply 1).neg).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ ?_)
    simp [wirtingerDeriv_add (u.property.1.differentiable two_ne_zero _)
      (v.property.1.differentiable two_ne_zero _), add_comm]
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun p ↦ by simp [wirtingerDeriv_const_smul])

private theorem negWirtingerToLp_apply (u : flatLineTestSections ω₁ ω₂ θ₁ θ₂) :
    negWirtingerToLp ω₁ ω₂ θ₁ θ₂ u = (memLp_comp_latticeCoord
      ((u.property.1.of_le one_le_two).continuous_wirtingerDeriv_apply 1).neg).toLp
      (fun p : ℝ × ℝ ↦ -wirtingerDeriv (u : ℂ → ℂ) (p.1 * ω₁ + p.2 * ω₂) 1) :=
  rfl

/-- The coercivity estimate of `∂` in `L²` of the fundamental domain. -/
private theorem sqrt_mul_norm_sectionToLp_le (hω : (conj ω₁ * ω₂).im ≠ 0)
    (u : flatLineTestSections ω₁ ω₂ θ₁ θ₂) :
    √(π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2)) *
        ‖sectionToLp ω₁ ω₂ θ₁ θ₂ u‖ ≤ ‖negWirtingerToLp ω₁ ω₂ θ₁ θ₂ u‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [mul_pow, Real.sq_sqrt (by positivity), sectionToLp_apply, negWirtingerToLp_apply,
    MemLp.norm_toLp_sq, MemLp.norm_toLp_sq]
  simpa only [norm_neg] using
    mul_setIntegral_norm_sq_le_setIntegral_norm_wirtingerDeriv_sq u.property.1 hω u.property.2.1
        u.property.2.2

/-- **The bounded weak inverse of `∂bar` on a flat line with nontrivial holonomy.** Let
`ω₁, ω₂` be linearly independent over `ℝ`, and let `θ₁` or `θ₂` not be an integer, so that the
flat line with holonomy `exp (2πiθ₁)`, `exp (2πiθ₂)` along `ω₁`, `ω₂` is nontrivial. Then there is
a bounded operator `Q` on `L²([0, 1]²)`, the square-integrable sections in lattice coordinates,
with `‖Q‖ ≤ C^(-1/2)` for `C = π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²)`, such that `Q f` is a
weak solution of `∂bar y = f` for every `f`: `∫ Q f · conj (∂φ) = -∫ f · conj φ` for every `C²`
section `φ`. -/
theorem exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq
    (hω : (conj ω₁ * ω₂).im ≠ 0) (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    ∃ Q : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) →L[ℂ]
        Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)),
      ‖Q‖ ≤ (√(π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2)))⁻¹ ∧
      ∀ f, ∀ φ ∈ flatLineTestSections ω₁ ω₂ θ₁ θ₂,
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
            Q f p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
          -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  have hne (h : ω₁ = 0 ∨ ω₂ = 0) : False := by rcases h with h | h <;> simp [h] at hω
  have hC := pi_sq_div_two_mul_sq_abs_sub_round_div_add_pos hθ (fun h ↦ hne (.inl h))
    (fun h ↦ hne (.inr h))
  obtain ⟨Q, hQn, -, hQ⟩ := LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le
    (negWirtingerToLp ω₁ ω₂ θ₁ θ₂) (sectionToLp ω₁ ω₂ θ₁ θ₂) (Real.sqrt_pos.2 hC)
    (sqrt_mul_norm_sectionToLp_le hω)
  refine ⟨Q, hQn, fun f φ hφ ↦ ?_⟩
  have h := hQ f ⟨φ, hφ⟩
  rw [negWirtingerToLp_apply, sectionToLp_apply, L2.inner_toLp, L2.inner_toLp] at h
  have h' := congrArg conj h
  rw [← integral_conj, ← integral_conj] at h'
  simp only [RCLike.inner_apply, map_mul, map_neg, conj_conj, neg_mul,
    integral_neg] at h'
  simp only [mul_comm (Q f _), mul_comm (f _)]
  linear_combination -h'

end WeakInverse

section Uniqueness

/-- The coefficient `a` of the twisted exponential with `Im (a ω₁) = π c₁` and
`Im (a ω₂) = π c₂`. -/
private noncomputable def dualCoeff (ω₁ ω₂ : ℂ) (c₁ c₂ : ℝ) : ℂ :=
  ((π / (conj ω₁ * ω₂).im : ℝ) : ℂ) * (c₂ * conj ω₁ - c₁ * conj ω₂)

private theorem im_dualCoeff_mul (hω : (conj ω₁ * ω₂).im ≠ 0) (c₁ c₂ : ℝ) :
    (dualCoeff ω₁ ω₂ c₁ c₂ * ω₁).im = π * c₁ ∧ (dualCoeff ω₁ ω₂ c₁ c₂ * ω₂).im = π * c₂ := by
  have h₁ : ((c₂ * conj ω₁ - c₁ * conj ω₂ : ℂ) * ω₁).im = c₁ * (conj ω₁ * ω₂).im := by
    simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im]
    ring
  have h₂ : ((c₂ * conj ω₁ - c₁ * conj ω₂ : ℂ) * ω₂).im = c₂ * (conj ω₁ * ω₂).im := by
    simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, conj_re, conj_im]
    ring
  rw [dualCoeff, mul_assoc, mul_assoc, im_ofReal_mul, im_ofReal_mul, h₁, h₂]
  constructor <;> field_simp

/-- In lattice coordinates the twisted exponential is `exp (2πi (c₁ s + c₂ t))`. -/
private theorem cexp_dualCoeff_mul_sub_conj_mul_conj_latticeCoord (hω : (conj ω₁ * ω₂).im ≠ 0)
    (c₁ c₂ : ℝ) (p : ℝ × ℝ) :
    cexp (dualCoeff ω₁ ω₂ c₁ c₂ * (p.1 * ω₁ + p.2 * ω₂) -
        conj (dualCoeff ω₁ ω₂ c₁ c₂) * conj (p.1 * ω₁ + p.2 * ω₂)) =
      cexp (2 * π * I * (c₁ * p.1 + c₂ * p.2)) := by
  obtain ⟨h₁, h₂⟩ := im_dualCoeff_mul hω c₁ c₂
  have him : (dualCoeff ω₁ ω₂ c₁ c₂ * (p.1 * ω₁ + p.2 * ω₂)).im =
      p.1 * (π * c₁) + p.2 * (π * c₂) := by
    rw [← h₁, ← h₂, mul_add, add_im, mul_left_comm, mul_left_comm _ (p.2 : ℂ), im_ofReal_mul,
      im_ofReal_mul]
  rw [← map_mul, sub_conj, him]
  push_cast
  ring_nf

/-- **Uniqueness of weak solutions of `∂bar y = f` on a flat line with nontrivial holonomy.** Let
`ω₁, ω₂` be linearly independent over `ℝ`, and let `θ₁` or `θ₂` not be an integer. If `y` is a
square-integrable section in lattice coordinates which is a weak solution of `∂bar y = 0`, that is,
`∫ y · conj (∂φ) = 0` for every `C²` section `φ` of the flat line with holonomy `exp (2πiθ₁)`,
`exp (2πiθ₂)` along `ω₁`, `ω₂`, then `y = 0`. -/
theorem eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero
    (hω : (conj ω₁ * ω₂).im ≠ 0) (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    {y : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))}
    (hy : ∀ φ ∈ flatLineTestSections ω₁ ω₂ θ₁ θ₂,
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        y p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) = 0) :
    y = 0 := by
  -- Untwisted by `exp (-2πi (θ₁ s + θ₂ t))`, the section `y` becomes a function with vanishing
  -- Fourier coefficients.
  have hg : MemLp (fun p : ℝ × ℝ ↦ cexp (((-(2 * π * (θ₁ * p.1 + θ₂ * p.2)) : ℝ) : ℂ) * I) * y p)
      2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (Lp.memLp y).of_le ((by fun_prop : Continuous fun p : ℝ × ℝ ↦
      cexp (((-(2 * π * (θ₁ * p.1 + θ₂ * p.2)) : ℝ) : ℂ) * I)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable y))
      (ae_of_all _ fun p ↦ by simp only [norm_mul, norm_exp_ofReal_mul_I, one_mul, le_refl])
  have hzero := UnitAddTorus.ae_eq_zero_of_forall_setIntegral_cexp_mul_eq_zero hg fun k₁ k₂ ↦ by
    obtain ⟨ha₁, ha₂⟩ := im_dualCoeff_mul hω (k₁ + θ₁) (k₂ + θ₂)
    -- The test section is the twisted exponential with coefficient `a ≠ 0`.
    have ha : dualCoeff ω₁ ω₂ (k₁ + θ₁) (k₂ + θ₂) ≠ 0 := by
      intro h0
      simp only [h0, zero_mul, zero_im, eq_comm (a := (0 : ℝ)), mul_eq_zero, Real.pi_ne_zero,
        false_or] at ha₁ ha₂
      rcases hθ with h | h
      · exact h ⟨-k₁, by push_cast; linarith⟩
      · exact h ⟨-k₂, by push_cast; linarith⟩
    have h := hy _ ⟨contDiff_cexp_mul_sub_conj_mul_conj _,
      cexp_mul_add_sub_conj_mul_conj_add_of_im_mul_eq _ ha₁,
      cexp_mul_add_sub_conj_mul_conj_add_of_im_mul_eq _ ha₂⟩
    simp only [wirtingerDeriv_cexp_mul_sub_conj_mul_conj, map_mul, mul_left_comm (y _) (conj _),
      integral_const_mul, mul_eq_zero, map_eq_zero, ha, false_or] at h
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun p ↦ ?_)
    dsimp only
    rw [cexp_dualCoeff_mul_sub_conj_mul_conj_latticeCoord hω, ← exp_conj, ← mul_assoc,
      ← Complex.exp_add, mul_comm]
    congr 2
    simp only [map_mul, map_add, conj_ofReal, conj_I, map_ofNat]
    push_cast
    ring
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hzero] with p hp
  exact (mul_eq_zero.1 hp).resolve_left (Complex.exp_ne_zero _)

end Uniqueness

section Inverse

/-- Against a continuous section read in lattice coordinates, the integral over the fundamental
domain is an `L²` inner product. -/
private theorem setIntegral_mul_conj_comp_latticeCoord_eq_inner {g : ℂ → ℂ} (hg : Continuous g)
    (y : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, y p * conj (g (p.1 * ω₁ + p.2 * ω₂)) =
      inner ℂ ((memLp_comp_latticeCoord hg).toLp fun p : ℝ × ℝ ↦ g (p.1 * ω₁ + p.2 * ω₂)) y := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_comp_latticeCoord hg).coeFn_toLp] with p hp
  rw [hp, RCLike.inner_apply, mul_comm]

open scoped Classical in
/-- **The inverse of `∂bar` on a flat line over a torus.** When `ω₁, ω₂` are linearly independent
over `ℝ` and `θ₁` or `θ₂` is not an integer, this is the bounded operator on `L²([0, 1]²)`, the
square-integrable sections in lattice coordinates of the flat line with holonomy `exp (2πiθ₁)`,
`exp (2πiθ₂)` along `ω₁`, `ω₂`, sending `f` to the unique weak solution of `∂bar y = f`
(`TauCeti.flatLineCRInverse_apply_eq_iff`). Otherwise it is `0`. -/
noncomputable def flatLineCRInverse (ω₁ ω₂ : ℂ) (θ₁ θ₂ : ℝ) :
    Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
  if h : (conj ω₁ * ω₂).im ≠ 0 ∧ (θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) then
    (exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq h.1 h.2).choose
  else 0

/-- For a degenerate lattice or trivial holonomy, `flatLineCRInverse ω₁ ω₂ θ₁ θ₂` is `0`. -/
theorem flatLineCRInverse_of_not
    (h : ¬((conj ω₁ * ω₂).im ≠ 0 ∧ (θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)))) :
    flatLineCRInverse ω₁ ω₂ θ₁ θ₂ = 0 := by
  rw [flatLineCRInverse, dite_eq_right_of_eq_false (eq_false h)]

/-- On the trivial flat line, with integer `θ₁, θ₂`, `flatLineCRInverse ω₁ ω₂ θ₁ θ₂` is `0`. -/
@[simp]
theorem flatLineCRInverse_intCast (k₁ k₂ : ℤ) : flatLineCRInverse ω₁ ω₂ k₁ k₂ = 0 :=
  flatLineCRInverse_of_not fun h ↦ h.2.elim (· ⟨k₁, rfl⟩) (· ⟨k₂, rfl⟩)

/-- The inverse of `∂bar` on a flat line with nontrivial holonomy has norm at most `C^(-1/2)`, for
`C = π² / 2 · (‖θ₁‖ℤ² / |ω₁|² + ‖θ₂‖ℤ² / |ω₂|²)`. -/
theorem norm_flatLineCRInverse_le (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) :
    ‖flatLineCRInverse ω₁ ω₂ θ₁ θ₂‖ ≤
      (√(π ^ 2 / 2 * (|θ₁ - round θ₁| ^ 2 / ‖ω₁‖ ^ 2 + |θ₂ - round θ₂| ^ 2 / ‖ω₂‖ ^ 2)))⁻¹ := by
  rw [flatLineCRInverse, dite_eq_left_of_eq_true (eq_true ⟨hω, hθ⟩)]
  exact (exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq hω hθ).choose_spec.1

/-- On a flat line with nontrivial holonomy, `flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f` is a weak solution of
`∂bar y = f`: `∫ y · conj (∂φ) = -∫ f · conj φ` for every `C²` section `φ`. -/
theorem setIntegral_flatLineCRInverse_mul_conj_wirtingerDeriv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    (f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)))
    (hφ : φ ∈ flatLineTestSections ω₁ ω₂ θ₁ θ₂) :
    ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
      -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  rw [flatLineCRInverse, dite_eq_left_of_eq_true (eq_true ⟨hω, hθ⟩)]
  exact (exists_continuousLinearMap_setIntegral_mul_conj_wirtingerDeriv_eq hω hθ).choose_spec.2
    f φ hφ

/-- **Characterization of the inverse of `∂bar`.** On a flat line with nontrivial holonomy,
`flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f = y` exactly when `y` is a weak solution of `∂bar y = f`, that is,
`∫ y · conj (∂φ) = -∫ f · conj φ` for every `C²` section `φ`. -/
theorem flatLineCRInverse_apply_eq_iff (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ))
    {f y : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))} :
    flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f = y ↔ ∀ φ ∈ flatLineTestSections ω₁ ω₂ θ₁ θ₂,
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          y p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
        -∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl φ hφ
    exact setIntegral_flatLineCRInverse_mul_conj_wirtingerDeriv hω hθ f hφ
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_setIntegral_mul_conj_wirtingerDeriv_eq_zero hω hθ
    fun φ hφ ↦ ?_
  have hg := (hφ.1.of_le one_le_two).continuous_wirtingerDeriv_apply 1
  rw [setIntegral_mul_conj_comp_latticeCoord_eq_inner hg, inner_sub_right,
    ← setIntegral_mul_conj_comp_latticeCoord_eq_inner hg,
    ← setIntegral_mul_conj_comp_latticeCoord_eq_inner hg,
    setIntegral_flatLineCRInverse_mul_conj_wirtingerDeriv hω hθ f hφ, h φ hφ,
    sub_self]

/-- **The inverse of `∂bar` inverts `∂bar` on `C¹` sections.** On a flat line with nontrivial
holonomy, if `u` is a `C¹` section and `f` represents `∂bar u` in lattice coordinates, then
`flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f` represents `u`. -/
theorem flatLineCRInverse_ae_eq_of_ae_eq_conjWirtingerDeriv (hω : (conj ω₁ * ω₂).im ≠ 0)
    (hθ : θ₁ ∉ range ((↑) : ℤ → ℝ) ∨ θ₂ ∉ range ((↑) : ℤ → ℝ)) (hu : ContDiff ℝ 1 u)
    (hu₁ : ∀ z, u (z + ω₁) = exp (2 * π * θ₁ * I) * u z)
    (hu₂ : ∀ z, u (z + ω₂) = exp (2 * π * θ₂ * I) * u z)
    {f : Lp ℂ 2 ((volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))}
    (hf : f =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)]
      fun p ↦ conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1) :
    flatLineCRInverse ω₁ ω₂ θ₁ θ₂ f =ᵐ[(volume : Measure (ℝ × ℝ)).restrict
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)] fun p ↦ u (p.1 * ω₁ + p.2 * ω₂) := by
  have hmem := memLp_comp_latticeCoord (ω₁ := ω₁) (ω₂ := ω₂) hu.continuous
  have hχ (θ : ℝ) : ‖exp (2 * π * θ * I)‖ = 1 := by
    simpa using norm_exp_ofReal_mul_I (2 * π * θ)
  rw [(flatLineCRInverse_apply_eq_iff hω hθ).2 fun φ hφ ↦ ?_]
  · exact hmem.coeFn_toLp
  have h₁ : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      hmem.toLp _ p * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) =
        ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          u (p.1 * ω₁ + p.2 * ω₂) * conj (wirtingerDeriv φ (p.1 * ω₁ + p.2 * ω₂) 1) :=
    integral_congr_ae (by filter_upwards [hmem.coeFn_toLp] with p hp; rw [hp])
  have h₂ : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f p * conj (φ (p.1 * ω₁ + p.2 * ω₂)) =
      ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
        conjWirtingerDeriv u (p.1 * ω₁ + p.2 * ω₂) 1 * conj (φ (p.1 * ω₁ + p.2 * ω₂)) :=
    integral_congr_ae (by filter_upwards [hf] with p hp; rw [hp])
  rw [h₁, h₂, setIntegral_conjWirtingerDeriv_mul_conj_eq_neg_setIntegral_mul_conj_wirtingerDeriv hu
    (hφ.1.of_le one_le_two) hω (hχ θ₁) (hχ θ₂) hu₁ hu₂ hφ.2.1 hφ.2.2, neg_neg]

end Inverse

end TauCeti
