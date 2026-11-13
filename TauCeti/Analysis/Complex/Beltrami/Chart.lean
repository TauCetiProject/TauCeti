/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Beltrami.Holder
public import TauCeti.Analysis.Complex.Beltrami.Linear
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Planar `J`-holomorphic charts from the Beltrami equation

Let `J` be a tame almost complex structure on the plane, varying with the point, and let
`μ_J = (coefficientEquiv ⟨J, hJ⟩).val` be its scalar Beltrami coefficient. A real-linear map
`A : ℂ →L[ℝ] ℂ` intertwines `J` with multiplication by `i` exactly when its Wirtinger parts
satisfy `\bar∂A = μ_J ∂A`: the affine normalizer `z ↦ z + μ_J conj z` intertwines `J` with `i`
(`TauCeti.Beltrami.linearMap_intertwines`), and every such `A` is a complex multiple of it.

Consequently a solution `ψ = z + T h` of the Beltrami equation `\bar∂ψ = μ ∂ψ` with small
Hölder coefficient `μ` (`TauCeti.exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv`), where `μ`
agrees with `μ_J` on a closed disc, has a `J`-complex-linear differential on that disc. Its
holomorphic derivative at the centre is nonzero, and after subtracting `ψ(c)` and dividing by
`∂ψ(c)` it is a local homeomorphism near `c` with value `0` and holomorphic derivative `1` at the
centre, in which `J` becomes the standard structure. This is the planar chart step in the
construction of isothermal coordinates.

The pointwise statements are `TauCeti.Beltrami.isComplexLinear_iff_conjWirtingerDeriv_eq` and
`TauCeti.Beltrami.coefficientEquiv_eq_zero_iff`.

## Main results

* `TauCeti.Beltrami.wirtingerDeriv_normalizedChart_self`: normalizing at `c` gives holomorphic
  derivative `1` at `c` whenever `∂ψ(c) ≠ 0`.
* `TauCeti.Beltrami.exists_isComplexLinear_chart`: the normalized Beltrami solution is a
  `C¹` local chart at `c`, `J`-holomorphic on its source, with value `0` and holomorphic derivative
  `1` at `c`.
* `TauCeti.Beltrami.cauchySolution_zero`, `TauCeti.Beltrami.normalizedChart_id`: for `μ = 0` the
  source `h = 0` gives `ψ = z`, and its normalized chart at `0` is the identity.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix E.
-/

public noncomputable section

open Complex Metric
open scoped ComplexConjugate NNReal

namespace TauCeti.Beltrami

/-- The function `w ↦ w + T h(w)` built from a source `h` through the Cauchy transform `T`. -/
def cauchySolution (h : ℂ → ℂ) : ℂ → ℂ :=
  fun w ↦ w + cauchyTransform h w

/-- The normalization of `ψ` at `c`: subtract `ψ(c)` and divide by the holomorphic derivative
`∂ψ(c)`. -/
def normalizedChart (ψ : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  fun w ↦ (wirtingerDeriv ψ c 1)⁻¹ • (ψ w - ψ c)

/-- Unfolding lemma for `cauchySolution`. -/
theorem cauchySolution_apply (h : ℂ → ℂ) (w : ℂ) :
    cauchySolution h w = w + cauchyTransform h w :=
  (rfl)

/-- Unfolding lemma for `normalizedChart`. -/
theorem normalizedChart_apply (ψ : ℂ → ℂ) (c w : ℂ) :
    normalizedChart ψ c w = (wirtingerDeriv ψ c 1)⁻¹ • (ψ w - ψ c) :=
  (rfl)

/-- The normalized chart vanishes at the base point. -/
@[simp]
theorem normalizedChart_self (ψ : ℂ → ℂ) (c : ℂ) : normalizedChart ψ c c = 0 := by
  simp [normalizedChart]

/-- The zero source gives the identity. -/
@[simp]
theorem cauchySolution_zero : cauchySolution 0 = id := by
  ext w
  simp [cauchySolution]

/-- The normalized chart of the identity is a translation. -/
@[simp]
theorem normalizedChart_id (c : ℂ) : normalizedChart id c = fun w ↦ w - c := by
  ext w
  simp [normalizedChart]

/-- **Check for `μ = 0`.** The zero source solves the Beltrami equation with zero coefficient, the
resulting `ψ` is the identity, and its normalized chart at `0` is the identity. -/
example :
    cauchySolution 0 = id ∧
      (∀ z, conjWirtingerDeriv (cauchySolution 0) z 1 = 0 * wirtingerDeriv (cauchySolution 0) z 1) ∧
      normalizedChart (cauchySolution 0) 0 = id := by
  refine ⟨cauchySolution_zero, fun z => ?_, ?_⟩
  · simp
  · rw [cauchySolution_zero, normalizedChart_id]
    ext w
    simp

/-- The real derivative of the normalized chart is that of `ψ` divided by `∂ψ(c)`. -/
theorem hasFDerivAt_normalizedChart {ψ : ℂ → ℂ} {c z : ℂ} {L : ℂ →L[ℝ] ℂ}
    (hψ : HasFDerivAt ψ L z) :
    HasFDerivAt (normalizedChart ψ c) ((wirtingerDeriv ψ c 1)⁻¹ • L) z :=
  (hψ.sub_const (ψ c)).const_smul (wirtingerDeriv ψ c 1)⁻¹

/-- The real differential of the normalized chart is that of `ψ` divided by `∂ψ(c)`. -/
theorem fderiv_normalizedChart {ψ : ℂ → ℂ} {c z : ℂ} :
    fderiv ℝ (normalizedChart ψ c) z = (wirtingerDeriv ψ c 1)⁻¹ • fderiv ℝ ψ z := by
  have hφ : normalizedChart ψ c = (wirtingerDeriv ψ c 1)⁻¹ • fun w ↦ ψ w - ψ c := rfl
  rw [hφ, fderiv_const_smul_field, Pi.smul_apply, fderiv_sub_const]

/-- The holomorphic derivative of the normalized chart is that of `ψ` divided by `∂ψ(c)`. -/
theorem wirtingerDeriv_normalizedChart {ψ : ℂ → ℂ} {c z : ℂ} :
    wirtingerDeriv (normalizedChart ψ c) z 1 = (wirtingerDeriv ψ c 1)⁻¹ * wirtingerDeriv ψ z 1 := by
  simp only [wirtingerDeriv_apply, fderiv_normalizedChart, smul_apply, smul_eq_mul]
  ring

/-- **Normalization at the centre.** If `∂ψ(c) ≠ 0`, the normalized chart has holomorphic
derivative `1` at `c`. -/
@[simp]
theorem wirtingerDeriv_normalizedChart_self {ψ : ℂ → ℂ} {c : ℂ} (hc : wirtingerDeriv ψ c 1 ≠ 0) :
    wirtingerDeriv (normalizedChart ψ c) c 1 = 1 := by
  rw [wirtingerDeriv_normalizedChart, inv_mul_cancel₀ hc]

/-- **The planar Beltrami chart.** Let `0 < α < 1` and `0 < r`. There are `δ > 0` and `C` such
that the following holds. Let `J` be a field of almost complex structures on the plane, tame on
`closedBall c r`, and let `μ` be an `α`-Hölder function vanishing off that disc, equal there to the
scalar coefficient `μ_J` and with `‖μ‖ < δ`. Then there is a source `h`, vanishing off the disc
with `‖h‖ ≤ 2 ‖μ‖`, such that `ψ = z + T h`

* is `C¹` on `ball c (r + 1)` and solves `\bar∂ψ = μ ∂ψ` there;
* has real derivative within `C ‖μ‖` of the identity on the disc, `α`-Hölder with constant
  `C ‖μ‖` there;
* has a differential that is complex linear from `J` to `i` at every point of the disc;
* has nonzero holomorphic derivative `∂ψ(c)`;

and the normalized map `φ = (ψ - ψ(c)) / ∂ψ(c)` is `C¹` on `ball c (r + 1)`, has `φ(c) = 0` and
`∂φ(c) = 1`, has a differential complex linear from `J` to `i` at every point of the disc, and is
an open partial homeomorphism on a neighbourhood of `c` inside `ball c r`. -/
theorem exists_isComplexLinear_chart {α : ℝ≥0} {r : ℝ} (hα : 0 < α) (hα1 : α < 1) (c : ℂ)
    (hr : 0 < r) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ (J : ℂ → AlmostComplexStructure ℂ)
      (hJ : ∀ z ∈ closedBall c r, stdComplexSymplecticForm.Tames (J z)),
      ∀ μ ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall c r),
      (∀ z (hz : z ∈ closedBall c r), μ z = (coefficientEquiv ⟨J z, hJ z hz⟩).val) →
      ‖μ‖ < δ →
      ∃ h ∈ supportedHolderSubmodule (Y := ℂ) α (closedBall c r), ‖h‖ ≤ 2 * ‖μ‖ ∧
        ContDiffOn ℝ 1 (cauchySolution h) (ball c (r + 1)) ∧
        (∀ z ∈ ball c (r + 1), conjWirtingerDeriv (cauchySolution h) z 1 =
          μ z * wirtingerDeriv (cauchySolution h) z 1) ∧
        (∀ z ∈ closedBall c r,
          ‖fderiv ℝ (cauchySolution h) z - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖μ‖) ∧
        HolderOnWith (C * ‖μ‖₊) α (fderiv ℝ (cauchySolution h)) (closedBall c r) ∧
        (∀ z ∈ closedBall c r, IsComplexLinear (J z).toLinearMap
          (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
          (fderiv ℝ (cauchySolution h) z).toLinearMap) ∧
        wirtingerDeriv (cauchySolution h) c 1 ≠ 0 ∧
        ContDiffOn ℝ 1 (normalizedChart (cauchySolution h) c) (ball c (r + 1)) ∧
        normalizedChart (cauchySolution h) c c = 0 ∧
        wirtingerDeriv (normalizedChart (cauchySolution h) c) c 1 = 1 ∧
        (∀ z ∈ closedBall c r, IsComplexLinear (J z).toLinearMap
          (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
          (fderiv ℝ (normalizedChart (cauchySolution h) c) z).toLinearMap) ∧
        ∃ e : OpenPartialHomeomorph ℂ ℂ, ⇑e = normalizedChart (cauchySolution h) c ∧
          c ∈ e.source ∧ e.source ⊆ ball c r := by
  obtain ⟨δ, hδ, C, hsol⟩ := exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv hα hα1 c hr.le
  refine ⟨δ, hδ, C, fun J hJ μ hμ hμJ hμδ => ?_⟩
  obtain ⟨h, hh, hhμ, hC1, -, hbel, hnear, hhol, hinv⟩ := hsol μ hμ hμδ
  -- The solver states its conclusions for the explicit map `w ↦ w + T h(w)`; fold it.
  have hfold : (fun w ↦ w + (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z) = cauchySolution h :=
    funext fun w ↦ by rw [cauchySolution_apply, cauchyTransform_apply]
  rw [hfold] at hC1 hbel hnear hhol hinv
  set ψ := cauchySolution h
  have hsub : closedBall c r ⊆ ball c (r + 1) := closedBall_subset_ball (by linarith)
  have hc : c ∈ closedBall c r := mem_closedBall_self hr.le
  -- `J`-linearity of `dψ` on the disc, from the Beltrami equation.
  have hlin : ∀ z ∈ closedBall c r, IsComplexLinear (J z).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ ψ z).toLinearMap :=
    fun z hz ↦ (isComplexLinear_iff_conjWirtingerDeriv_eq (J z) (hJ z hz) ψ z).mpr
      (by rw [← hμJ z hz]; exact hbel z (hsub hz))
  -- `∂ψ(c) ≠ 0`: otherwise `\bar∂ψ(c) = 0` too and `dψ(c) = 0` would not be invertible.
  have ha : wirtingerDeriv ψ c 1 ≠ 0 := by
    intro h0
    obtain ⟨L, hL⟩ := hinv c hc
    have hbar : conjWirtingerDeriv ψ c 1 = 0 := by rw [hbel c (hsub hc), h0, mul_zero]
    have hzero : fderiv ℝ ψ c 1 = 0 := by
      rw [fderiv_apply_eq_smul_wirtingerDeriv_add_smul_conjWirtingerDeriv, h0, hbar]
      simp
    rw [hL.hasFDerivAt.fderiv] at hzero
    exact one_ne_zero (L.injective (hzero.trans L.map_zero.symm))
  set a := wirtingerDeriv ψ c 1
  set φ := normalizedChart ψ c
  refine ⟨h, hh, hhμ, hC1, hbel, hnear, hhol, hlin, ha, ?_, normalizedChart_self ψ c, ?_, ?_, ?_⟩
  · exact (hC1.sub contDiffOn_const).const_smul a⁻¹
  · exact wirtingerDeriv_normalizedChart_self ha
  · intro z hz
    rw [fderiv_normalizedChart]
    apply isComplexLinear_of_apply
    intro v
    have := (hlin z hz).apply v
    simp only [ContinuousLinearMap.coe_coe, smul_apply] at this ⊢
    rw [this]
    simp only [AlmostComplexStructure.ofComplexModule_apply, smul_eq_mul]
    ring
  · -- The inverse function theorem at `c`, restricted to `ball c r`.
    obtain ⟨L, hL⟩ := hinv c hc
    let M : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 a⁻¹ (inv_ne_zero ha))
    have hφs : HasStrictFDerivAt φ ((L.trans M : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) c := by
      have hLM : ((L.trans M : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) = a⁻¹ • (L : ℂ →L[ℝ] ℂ) :=
        ContinuousLinearMap.ext fun v ↦ by simp [M, Units.smul_def]
      rw [hLM]
      exact (hL.sub_const (ψ c)).const_smul a⁻¹
    let e := hφs.toOpenPartialHomeomorph φ
    refine ⟨e.restrOpen (ball c r) isOpen_ball, ?_, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.coe_restrOpen]
      exact hφs.toOpenPartialHomeomorph_coe
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨hφs.mem_toOpenPartialHomeomorph_source, mem_ball_self hr⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact Set.inter_subset_right

end TauCeti.Beltrami
