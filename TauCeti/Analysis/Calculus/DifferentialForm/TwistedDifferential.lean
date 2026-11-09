/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import TauCeti.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The twisted differential of a real function

Given an almost complex structure `J` on a finite-dimensional real normed space, the twisted
differential of a real function `f` is the one-form `d^c_J f = -(1/2) df ∘ J`.

## Main definitions

* `TauCeti.AlmostComplexStructure.twistedDifferential J f`: the one-form `d^c_J f = -(1/2) df ∘ J`.

## Main results

* `TauCeti.AlmostComplexStructure.twistedDifferential_comp`: the chain rule
  `d^c_J (H ∘ f) = H'(f) • d^c_J f`.
* `TauCeti.AlmostComplexStructure.twistedDifferential_add`,
  `TauCeti.AlmostComplexStructure.twistedDifferential_const_smul`: linearity.
* `TauCeti.AlmostComplexStructure.integral_twistedDifferential_wedge_eq`: integration by parts.
  For a compactly supported form `η` of complementary degree,
  `∫ d^c_J g ∧ η = (det J / 2) ∫ g d((-J)^* η)`, where `((-J)^* η)(x)(v₁, …, vₘ) =
  η(x)(-J v₁, …, -J vₘ)` precomposes each value of `η` with `-J` and keeps the base point fixed.
  Precomposing the integrand with `J` in each fibre moves `J` from `dg` onto `η` at the cost of
  `det J`, and then `g` absorbs the derivative. The right side involves `g` but not its
  derivative.
* `TauCeti.AlmostComplexStructure.exists_abs_integral_twistedDifferential_wedge_le`: the
  resulting bound of `∫ d^c_J g ∧ η` by a constant times `sup ‖Dη‖ ∫_K |g|`.
-/

public section

noncomputable section

open ContinuousAlternatingMap

namespace TauCeti.AlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (J : AlmostComplexStructure E)

/-- The twisted differential `d^c_J f = -(1/2) df ∘ J` of a real function `f`. -/
def twistedDifferential (f : E → ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1)
    ((-2⁻¹ : ℝ) • (fderiv ℝ f x).comp (LinearMap.toContinuousLinearMap J.toLinearMap))

/-- The twisted differential evaluated on a vector. -/
@[simp]
theorem twistedDifferential_apply (f : E → ℝ) (x : E) (v : Fin 1 → E) :
    J.twistedDifferential f x v = -2⁻¹ * fderiv ℝ f x (J (v 0)) := by
  simp [twistedDifferential]

/-- **Chain rule for the twisted differential.** If `H` has derivative `h'` at `f x`, then
`d^c_J (H ∘ f) = h' • d^c_J f` at `x`. -/
theorem twistedDifferential_comp {H : ℝ → ℝ} {h' : ℝ} {f : E → ℝ} {x : E}
    (hH : HasDerivAt H h' (f x)) (hf : DifferentiableAt ℝ f x) :
    J.twistedDifferential (H ∘ f) x = h' • J.twistedDifferential f x := by
  ext v
  simp [(hH.comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  ring

/-- The twisted differential is additive on functions differentiable at the point. -/
theorem twistedDifferential_add {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    J.twistedDifferential (f + g) x = J.twistedDifferential f x + J.twistedDifferential g x := by
  ext v
  simp [fderiv_add hf hg]
  ring

/-- The twisted differential commutes with scalar multiplication. -/
theorem twistedDifferential_const_smul (c : ℝ) (f : E → ℝ) (x : E) :
    J.twistedDifferential (c • f) x = c • J.twistedDifferential f x := by
  ext v
  simp [fderiv_const_smul_field]
  ring

/-- The twisted differential of a `C^(n+1)` function is `C^n`. -/
theorem contDiff_twistedDifferential {n : WithTop ℕ∞} {f : E → ℝ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (J.twistedDifferential f) := by
  unfold twistedDifferential
  exact (ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ) (0 : Fin 1)).contDiff.comp
    (((hf.fderiv_right le_rfl).clm_comp contDiff_const).const_smul _)

open MeasureTheory in
/-- **Integration by parts for the twisted differential.** For a C1 function `g` and a compactly
supported C1 form `η` of degree `m` on a space of dimension `1 + m`,
`∫ d^c_J g ∧ η = (det J / 2) ∫ g d((-J)^* η)`, the top-degree coefficients being taken on a basis
`b` and integrated against its Haar measure. Here `(-J)^* η` is the form
`x ↦ η(x)(-J v₁, …, -J vₘ)`, which precomposes each value of `η` with the inverse `-J` of `J` and
keeps the base point fixed. -/
theorem integral_twistedDifferential_wedge_eq [MeasurableSpace E] [BorelSpace E] {m : ℕ}
    (b : Module.Basis (Fin (1 + m)) ℝ E) {g : E → ℝ} {η : E → E [⋀^Fin m]→L[ℝ] ℝ}
    (hg : ContDiff ℝ 1 g) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    ∫ x, wedge (J.twistedDifferential g x) (η x) b ∂b.addHaar =
      LinearMap.det J.toLinearMap / 2 * ∫ x, g x * extDeriv
        (fun y ↦ (η y).compContinuousLinearMap (-LinearMap.toContinuousLinearMap J.toLinearMap)) x
        (b ∘ Fin.cast (by omega)) ∂b.addHaar := by
  set J' := LinearMap.toContinuousLinearMap J.toLinearMap
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J')
  -- Pointwise, precomposing with `J` in the fibre turns `d^c_J g ∧ η` into `-(det J / 2) dg ∧ η'`.
  have hpt (x : E) : wedge (J.twistedDifferential g x) (η x) b =
      -(LinearMap.det J.toLinearMap / 2) *
        wedge (ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ g x)) (η' x) b := by
    have h₁ : J.twistedDifferential g x = (-2⁻¹ : ℝ) •
        (ofSubsingleton ℝ E ℝ (0 : Fin 1) (fderiv ℝ g x)).compContinuousLinearMap J' := by
      ext v
      simp [J']
    have h₂ : η x = (η' x).compContinuousLinearMap J' := by
      ext v
      simp only [η', compContinuousLinearMap_apply]
      congr 1
      funext i
      simp [J', J.apply_apply]
    rw [h₁, h₂, wedge_smul_left, wedge_compContinuousLinearMap,
      ContinuousAlternatingMap.smul_apply, compContinuousLinearMap_apply_basis]
    simp [J']
    ring
  have hη' : ContDiff ℝ 1 η' :=
    (compContinuousLinearMapCLM (F := ℝ) (ι := Fin m) (-J')).contDiff.comp hη
  have hcη' : HasCompactSupport η' := hc.mono fun x hx h ↦ hx (by ext; simp [η', h])
  have hg' : ContDiff ℝ 1 fun x ↦ constOfIsEmpty ℝ E (Fin 0) (g x) :=
    (constOfIsEmptyLIE ℝ E ℝ (Fin 0)).contDiff.comp hg
  -- Integrate by parts the degree-zero form `g` against `η'`.
  have hibp := b.integral_extDeriv_wedge_eq_integral_wedge_extDeriv (by omega) hg' hη' hcη'
  simp only [extDeriv_constOfIsEmpty, wedge_def, pairedWedge_apply_zero_left] at hibp
  -- The index casts produced by the two wedges are the identity, up to the cast `m + 1 = 1 + m`.
  have e₁ : ⇑b ∘ Fin.cast (show 0 + 1 + m = 1 + m by omega) = ⇑b := rfl
  have e₂ : (⇑b ∘ Fin.cast (show 0 + (m + 1) = 1 + m by omega)) ∘
      Fin.cast (Nat.zero_add (m + 1)).symm = ⇑b ∘ Fin.cast (show m + 1 = 1 + m by omega) := rfl
  rw [e₁, e₂] at hibp
  simp only [ContinuousLinearMap.mul_apply', constOfIsEmpty_apply, pow_zero] at hibp
  simp only [hpt, integral_const_mul]
  simp only [wedge_def, hibp]
  ring

open MeasureTheory in
/-- The integral of `d^c_J g ∧ η`, for a C1 function `g` with `|g| ≤ G` on a compact set `K` and
a C1 form `η` supported in `K` with `‖Dη‖ ≤ A`, is at most a constant depending only on `J` and
the basis `b` times `A ∫_K G`. Integration by parts moves the derivative from `g` onto `η`. -/
theorem exists_abs_integral_twistedDifferential_wedge_le [MeasurableSpace E] [BorelSpace E]
    {m : ℕ} (b : Module.Basis (Fin (1 + m)) ℝ E) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃g : E → ℝ⦄ ⦃η : E → E [⋀^Fin m]→L[ℝ] ℝ⦄ ⦃K : Set E⦄ ⦃G : E → ℝ⦄
      ⦃A : ℝ⦄, ContDiff ℝ 1 g → ContDiff ℝ 1 η → IsCompact K → tsupport η ⊆ K →
      IntegrableOn G K b.addHaar → (∀ x ∈ K, |g x| ≤ G x) → (∀ x, ‖fderiv ℝ η x‖ ≤ A) →
      |∫ x, wedge (J.twistedDifferential g x) (η x) b ∂b.addHaar| ≤
        C * (A * ∫ x in K, G x ∂b.addHaar) := by
  let J' := LinearMap.toContinuousLinearMap J.toLinearMap
  let L := compContinuousLinearMapCLM (F := ℝ) (ι := Fin m) (-J')
  let b' := ⇑b ∘ Fin.cast (show m + 1 = 1 + m by omega)
  refine ⟨|LinearMap.det J.toLinearMap| / 2 * ((m + 1) * ‖L‖ * ∏ i, ‖b' i‖), by positivity, ?_⟩
  intro g η K G A hg hη hK hηK hG hgG hηA
  have hDη0 (x) (hx : x ∉ K) : fderiv ℝ η x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hηK (tsupport_fderiv_subset ℝ h))
  rw [J.integral_twistedDifferential_wedge_eq b hg hη
    (hK.of_isClosed_subset (isClosed_tsupport η) hηK)]
  set η' := fun y ↦ (η y).compContinuousLinearMap (-J')
  have hDη' (x : E) : fderiv ℝ η' x = L.comp (fderiv ℝ η x) :=
    (L.hasFDerivAt.comp x (hη.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hnorm (x : E) : ‖extDeriv η' x‖ ≤ (m + 1) * ‖L‖ * A :=
    calc ‖extDeriv η' x‖ ≤ (m + 1) * ‖fderiv ℝ η' x‖ := norm_alternatizeUncurryFin_le _
      _ ≤ (m + 1) * (‖L‖ * A) := by
          rw [hDη']
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact hηA x)
      _ = _ := by ring
  have hvan (x : E) (hx : x ∉ K) : g x * extDeriv η' x b' = 0 := by
    simp [extDeriv, hDη', hDη0 x hx, ← alternatizeUncurryFinCLM_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, abs_mul, abs_div, abs_two]
  calc |LinearMap.det J.toLinearMap| / 2 * |∫ x in K, g x * extDeriv η' x b' ∂b.addHaar|
      ≤ |LinearMap.det J.toLinearMap| / 2 *
          ∫ x in K, (m + 1) * ‖L‖ * A * (∏ i, ‖b' i‖) * G x ∂b.addHaar := by
        gcongr
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hG.const_mul _)
          (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ ?_)
        have hD : |extDeriv η' x b'| ≤ (m + 1) * ‖L‖ * A * ∏ i, ‖b' i‖ := by
          rw [← Real.norm_eq_abs]
          exact ((extDeriv η' x).le_opNorm b').trans (by gcongr; exact hnorm x)
        rw [Real.norm_eq_abs, abs_mul, mul_comm _ (G x)]
        exact mul_le_mul (hgG x hx) hD (abs_nonneg _) ((abs_nonneg _).trans (hgG x hx))
    _ = _ := by
        rw [integral_const_mul]
        ring

end TauCeti.AlmostComplexStructure
