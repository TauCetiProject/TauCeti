/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The diagonal measure of a normal operator

Let `a` be a normal bounded operator on a complex Hilbert space `H` and let `ξ ∈ H`. The
functional `f ↦ ⟪ξ, f(a) ξ⟫` on continuous functions on `spectrum ℂ a` is positive, because the
continuous functional calculus sends nonnegative functions to positive operators. By the
Riesz–Markov–Kakutani theorem it is integration against a unique finite Borel measure `μ_ξ` on the
spectrum:

`⟪ξ, f(a) ξ⟫ = ∫ f dμ_ξ`.

This measure is the scalar spectral measure of `a` at `ξ`. Its total mass is `‖ξ‖²`, and it
computes `‖f(a) ξ‖²` as the squared `L²(μ_ξ)` norm of `f`. Polarizing these diagonal measures
gives the matrix elements of the bounded Borel functional calculus, which extends the continuous
calculus from continuous to bounded Borel symbols.

`LinearMap.exists_isFiniteMeasure_integral_characterSpace_eq` gives the analogous representation
on the character space of a commutative C⋆-algebra, as an existence statement. Here the measure
lives on the spectrum itself and is a named definition, so later constructions can refer to it.

## Main declarations

* `ContinuousLinearMap.diagMeasure a ξ`: the diagonal measure of a normal operator `a` at `ξ`, a
  finite measure on `spectrum ℂ a`.
* `ContinuousLinearMap.integral_diagMeasure_eq_inner_cfcHom`,
  `ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc`: `∫ f dμ_ξ = ⟪ξ, f(a) ξ⟫`.
* `ContinuousLinearMap.eq_diagMeasure_iff`: `μ_ξ` is the only finite measure with this property.
* `ContinuousLinearMap.diagMeasure_univ`: the total mass of `μ_ξ` is `‖ξ‖²`.
* `ContinuousLinearMap.integral_norm_sq_diagMeasure`: `∫ |f|² dμ_ξ = ‖f(a) ξ‖²`.

## References

* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  rev. ed., Academic Press (1980), §VII.2.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
-/

public section

noncomputable section

open MeasureTheory ContinuousMap
open scoped InnerProductSpace ComplexOrder CompactlySupported

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- The positive functional `g ↦ Re ⟪ξ, g(a) ξ⟫` on real continuous functions on the spectrum of
a normal operator `a`, whose Riesz–Markov–Kakutani measure is the diagonal measure. -/
private def diagFunctional (ξ : H) : C_c(spectrum ℂ a, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun g := RCLike.re ⟪ξ, cfcHom (a := a) ‹_› (g.toContinuousMap.realToRCLike ℂ) ξ⟫_ℂ
      map_add' g h := by
        have : (g + h).toContinuousMap.realToRCLike ℂ =
            g.toContinuousMap.realToRCLike ℂ + h.toContinuousMap.realToRCLike ℂ := by
          ext; simp
        rw [this, map_add, _root_.add_apply, inner_add_right, map_add]
      map_smul' c g := by
        have : (c • g).toContinuousMap.realToRCLike ℂ =
            (c : ℂ) • g.toContinuousMap.realToRCLike ℂ := by
          ext; simp
        rw [this, map_smul, _root_.smul_apply, inner_smul_right]
        simp }
    fun g hg => by
      have hT : 0 ≤ cfcHom (a := a) ‹_› (g.toContinuousMap.realToRCLike ℂ) := by
        rw [cfcHom_nonneg_iff]
        intro x
        simpa using hg x
      exact (nonneg_iff_isPositive.mp hT).re_inner_nonneg_right ξ

private lemma diagFunctional_apply (ξ : H) (g : C_c(spectrum ℂ a, ℝ)) :
    diagFunctional a ξ g =
      RCLike.re ⟪ξ, cfcHom (a := a) ‹_› (g.toContinuousMap.realToRCLike ℂ) ξ⟫_ℂ :=
  rfl

/-- The **diagonal measure** `μ_ξ` of a normal operator `a` at a vector `ξ`: the finite Borel
measure on `spectrum ℂ a` with `∫ f dμ_ξ = ⟪ξ, f(a) ξ⟫` for every continuous `f`
(`integral_diagMeasure_eq_inner_cfcHom`), characterized by this property among finite measures
(`eq_diagMeasure_iff`). -/
def diagMeasure (ξ : H) : Measure (spectrum ℂ a) :=
  RealRMK.rieszMeasure (diagFunctional a ξ)

instance (ξ : H) : IsFiniteMeasure (a.diagMeasure ξ) := by
  unfold diagMeasure; infer_instance

/-- The defining identity of the diagonal measure on real symbols. -/
private lemma ofReal_integral_diagMeasure (ξ : H) (g : C(spectrum ℂ a, ℝ)) :
    ((∫ x, g x ∂(a.diagMeasure ξ) : ℝ) : ℂ) = ⟪ξ, cfcHom ‹_› (g.realToRCLike ℂ) ξ⟫_ℂ := by
  have h := RealRMK.integral_rieszMeasure (diagFunctional a ξ) ⟨g, .of_compactSpace _⟩
  rw [CompactlySupportedContinuousMap.coe_mk, diagFunctional_apply] at h
  -- A real symbol gives a self-adjoint operator, whose diagonal matrix elements are real.
  have hsa : IsSelfAdjoint (cfcHom ‹IsStarNormal a› (g.realToRCLike ℂ)) := by
    refine IsSelfAdjoint.map (f := cfcHom ‹IsStarNormal a›) ?_
    rw [IsSelfAdjoint, ← realToRCLike_star, star_trivial]
  rw [diagMeasure, h]
  exact RCLike.conj_eq_iff_re.mp ((inner_conj_symm _ _).trans (hsa.isSymmetric ξ ξ))

/-- Integration against the diagonal measure `μ_ξ` of a normal operator `a` computes the diagonal
matrix elements of the continuous functional calculus: `∫ f dμ_ξ = ⟪ξ, f(a) ξ⟫`. -/
theorem integral_diagMeasure_eq_inner_cfcHom (ξ : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ x, f x ∂(a.diagMeasure ξ) = ⟪ξ, cfcHom ‹_› f ξ⟫_ℂ := by
  -- Split `f` into its real and imaginary parts, and apply the real case to each.
  let u : C(spectrum ℂ a, ℝ) := ⟨fun x ↦ (f x).re, by fun_prop⟩
  let v : C(spectrum ℂ a, ℝ) := ⟨fun x ↦ (f x).im, by fun_prop⟩
  have hf : f = u.realToRCLike ℂ + Complex.I • v.realToRCLike ℂ := by
    ext x
    simp [u, v, mul_comm Complex.I]
  rw [← integral_re_add_im (f.continuous.integrable_of_hasCompactSupport (.of_compactSpace _))]
  conv_rhs => rw [hf, map_add, map_smul, _root_.add_apply, _root_.smul_apply, inner_add_right,
    inner_smul_right, ← ofReal_integral_diagMeasure, ← ofReal_integral_diagMeasure]
  simp [u, v, mul_comm Complex.I]

/-- The `cfc` form of `integral_diagMeasure_eq_inner_cfcHom`: for `f` continuous on the spectrum
of a normal operator `a`, `∫ f dμ_ξ = ⟪ξ, cfc f a ξ⟫`. -/
theorem integral_diagMeasure_eq_inner_cfc (ξ : H) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ a) := by cfc_cont_tac) :
    ∫ x, f x ∂(a.diagMeasure ξ) = ⟪ξ, cfc f a ξ⟫_ℂ := by
  rw [cfc_apply f a, ← integral_diagMeasure_eq_inner_cfcHom]
  simp

/-- The diagonal measure `μ_ξ` is the unique finite measure on the spectrum of a normal
operator `a` that represents `f ↦ ⟪ξ, f(a) ξ⟫` on continuous functions. -/
theorem eq_diagMeasure_iff (ξ : H) (μ : Measure (spectrum ℂ a)) [IsFiniteMeasure μ] :
    μ = a.diagMeasure ξ ↔ ∀ f : C(spectrum ℂ a, ℂ), ∫ x, f x ∂μ = ⟪ξ, cfcHom ‹_› f ξ⟫_ℂ := by
  refine ⟨fun h ↦ h ▸ integral_diagMeasure_eq_inner_cfcHom a ξ, fun h ↦ ?_⟩
  -- Finite measures on the compact metrizable spectrum are regular, so they are determined
  -- by their integrals of real continuous functions.
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g ↦ ?_
  have hg := h (g.toContinuousMap.realToRCLike ℂ)
  rw [← integral_diagMeasure_eq_inner_cfcHom] at hg
  simpa [integral_complex_ofReal] using hg

/-- The total mass of the diagonal measure `μ_ξ`, as a real number, is `‖ξ‖²`. -/
@[simp]
theorem diagMeasure_real_univ (ξ : H) : (a.diagMeasure ξ).real Set.univ = ‖ξ‖ ^ 2 := by
  simpa [← Complex.ofReal_pow] using
    congrArg Complex.re (integral_diagMeasure_eq_inner_cfcHom a ξ 1)

/-- The total mass of the diagonal measure `μ_ξ` is `‖ξ‖²`. -/
@[simp]
theorem diagMeasure_univ (ξ : H) : a.diagMeasure ξ Set.univ = ‖ξ‖ₑ ^ 2 := by
  rw [← ofReal_measureReal, diagMeasure_real_univ, ENNReal.ofReal_pow (norm_nonneg ξ),
    ofReal_norm]

/-- The diagonal measure `μ_ξ` computes `‖f(a) ξ‖²` as the squared `L²(μ_ξ)` norm of `f`:
`∫ |f|² dμ_ξ = ‖f(a) ξ‖²`. -/
theorem integral_norm_sq_diagMeasure (ξ : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ x, ‖f x‖ ^ 2 ∂(a.diagMeasure ξ) = ‖cfcHom ‹_› f ξ‖ ^ 2 := by
  rw [apply_norm_sq_eq_inner_adjoint_right, ← star_eq_adjoint, ← mul_def, ← map_star, ← map_mul,
    ← integral_diagMeasure_eq_inner_cfcHom]
  simp [Complex.conj_mul', ← Complex.ofReal_pow, integral_complex_ofReal]

end ContinuousLinearMap
