/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Diagonal spectral measures of a normal operator

For a normal `a : H →L[ℂ] H` on a complex Hilbert space and a vector `ξ`, the
map `f ↦ ⟪ξ, cfcHom f ξ⟫` is a positive linear functional on the continuous
functions over `spectrum ℂ a`.  Riesz–Markov–Kakutani turns it into a finite
regular Borel measure `diagMeasure ha ξ`, the **diagonal spectral measure**,
characterised by

`∫ x, f x ∂(diagMeasure ha ξ) = ⟪ξ, cfcHom ha f ξ⟫`  for every `f : C(σ, ℂ)`.

These measures are the raw material for the bounded Borel functional calculus:
that calculus is built by polarising `ξ ↦ ∫ f ∂(diagMeasure ha ξ)` for bounded
Borel `f`, and every identity is transported from the continuous case by
approximating `f` in `L¹` of a *finite sum* of diagonal measures.

## Why this exists

Mathlib has the continuous functional calculus but no Borel calculus and no
spectral measures.  The Davis–Kahan development needs projection-valued
measures, so the gap has to be closed somewhere.

## Provenance

* **Extraction class:** *new*.  Neither the definitions nor the proofs come from
  Spectra; the construction is assembled directly from Mathlib's
  `RealRMK.rieszMeasure` and `cfcHom`.
* **Endpoints it is aimed at:** the Spectra declarations
  `Spectra.QuantumMechanics.SpectralTheory.spectralPVM` and the surrounding
  `Spectra.SpectralTheory.Calculus.*` bounded Borel calculus, which
  `DavisKahan/SpectralTheory/Real/SpectralRestriction.lean` and its siblings
  consume.  Spectra reaches them through Stone's theorem and a Herglotz/Poisson
  representation; this file's route (Riesz–Markov–Kakutani applied to the
  continuous functional calculus of the Cayley transform) is independent and
  shorter, so nothing is being copied.  See the Spectra-removal plan for the
  comparison that chose it.
-/

public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

section OfReal

variable {X : Type*} [TopologicalSpace X]

/-- Complexification of a real continuous function, as an `ℝ`-linear map. -/
noncomputable def ofRealLM : C(X, ℝ) →ₗ[ℝ] C(X, ℂ) where
  toFun g := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  map_add' g g' := by ext x; simp
  map_smul' r g := by ext x; simp

/-- The real-to-complex coercion of a continuous function, pointwise. -/
@[simp] theorem ofRealLM_apply (g : C(X, ℝ)) (x : X) :
    ofRealLM g x = (g x : ℂ) := (rfl)
/-- A real-valued symbol is star-invariant, which is why its calculus is self-adjoint. -/
@[simp] theorem star_ofRealLM (g : C(X, ℝ)) : star (ofRealLM g) = ofRealLM g := by
  ext x; simp

end OfReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Positivity

variable (ha : IsStarNormal a)

/-- A real continuous symbol has self-adjoint functional-calculus image. -/
theorem isSelfAdjoint_cfcHom_ofReal (g : C(spectrum ℂ a, ℝ)) :
    IsSelfAdjoint (cfcHom ha (ofRealLM g)) := by
  rw [IsSelfAdjoint, ← map_star, star_ofRealLM]

/-- The diagonal value of a real symbol is real. -/
theorem inner_cfcHom_ofReal_conj (g : C(spectrum ℂ a, ℝ)) (ξ : H) :
    (starRingEnd ℂ) ⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ = ⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ := by
  rw [inner_conj_symm]
  conv_lhs => rw [← (isSelfAdjoint_cfcHom_ofReal ha g).star_eq]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- For a real symbol the diagonal matrix element is real, so taking `re` and coercing back is the
identity.  This is what lets the diagonal functional be defined over `ℝ`. -/
theorem inner_cfcHom_ofReal_re (g : C(spectrum ℂ a, ℝ)) (ξ : H) :
    (((⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ).re : ℝ) : ℂ) =
      ⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ :=
  Complex.conj_eq_iff_re.mp (inner_cfcHom_ofReal_conj ha g ξ)

/-- Positivity: a nonnegative real symbol has nonnegative diagonal values. -/
theorem inner_cfcHom_ofReal_nonneg {g : C(spectrum ℂ a, ℝ)} (hg : ∀ x, 0 ≤ g x) (ξ : H) :
    0 ≤ (⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ).re := by
  set k : C(spectrum ℂ a, ℝ) :=
    ⟨fun x => Real.sqrt (g x), Real.continuous_sqrt.comp g.continuous⟩ with hk
  have hsq : ofRealLM k * ofRealLM k = ofRealLM g := by
    ext x
    simp only [ContinuousMap.mul_apply, ofRealLM_apply, hk, ContinuousMap.coe_mk,
      ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt (hg x)]
  have hstar : cfcHom ha (ofRealLM k) =
      ContinuousLinearMap.adjoint (cfcHom ha (ofRealLM k)) := by
    conv_lhs => rw [← star_ofRealLM k, map_star]
    rfl
  have h1 : cfcHom ha (ofRealLM g) ξ =
      ContinuousLinearMap.adjoint (cfcHom ha (ofRealLM k)) (cfcHom ha (ofRealLM k) ξ) := by
    rw [← hsq, map_mul, ← hstar]; rfl
  have hnorm : ⟪cfcHom ha (ofRealLM k) ξ, cfcHom ha (ofRealLM k) ξ⟫_ℂ =
      ((‖cfcHom ha (ofRealLM k) ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h1, ContinuousLinearMap.adjoint_inner_right, hnorm, Complex.ofReal_re]
  positivity

end Positivity

section Functional

variable (ha : IsStarNormal a)

/-- The positive linear functional `f ↦ ⟪ξ, cfcHom f ξ⟫` on real continuous
functions over the spectrum. -/
noncomputable def diagFunctional (ξ : H) :
    C_c(spectrum ℂ a, ℝ) →ₚ[ℝ] ℝ where
  toFun g := (⟪ξ, cfcHom ha (ofRealLM g.toContinuousMap) ξ⟫_ℂ).re
  map_add' g g' := by
    have h : (g + g').toContinuousMap = g.toContinuousMap + g'.toContinuousMap := (rfl)
    rw [h, map_add, map_add, _root_.add_apply, inner_add_right, Complex.add_re]
  map_smul' r g := by
    have h : (r • g).toContinuousMap = r • g.toContinuousMap := (rfl)
    have hc : ofRealLM (r • g.toContinuousMap) =
        (r : ℂ) • ofRealLM g.toContinuousMap := by
      ext x; simp [Complex.real_smul]
    rw [h, hc, map_smul, _root_.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
    rfl
  monotone' g g' hgg' := by
    have hle : ∀ x, g x ≤ g' x := fun x => hgg' x
    have hdnn : ∀ x, 0 ≤ (g'.toContinuousMap - g.toContinuousMap) x :=
      fun x => sub_nonneg.mpr (hle x)
    have hpos := inner_cfcHom_ofReal_nonneg ha hdnn ξ
    rw [map_sub, map_sub, _root_.sub_apply, inner_sub_right, Complex.sub_re] at hpos
    linarith

/-- The diagonal functional, unfolded to the integral it is. -/
@[simp] theorem diagFunctional_apply (ξ : H) (g : C_c(spectrum ℂ a, ℝ)) :
    diagFunctional ha ξ g = (⟪ξ, cfcHom ha (ofRealLM g.toContinuousMap) ξ⟫_ℂ).re := (rfl)
/-- The **diagonal spectral measure** of a normal operator at a vector. -/
noncomputable def diagMeasure (ξ : H) : Measure (spectrum ℂ a) :=
  RealRMK.rieszMeasure (diagFunctional ha ξ)

/-- Equal diagonal functionals give equal diagonal measures, since the measure is produced from the
functional by Riesz representation. -/
theorem diagMeasure_congr {ξ η : H} (h : diagFunctional ha ξ = diagFunctional ha η) :
    diagMeasure ha ξ = diagMeasure ha η := by
  rw [diagMeasure, diagMeasure, h]

/-- Diagonal measures are finite, inherited from the Riesz measure of a bounded functional. -/
instance instIsFiniteMeasure_diagMeasure (ξ : H) :
    IsFiniteMeasure (diagMeasure ha ξ) := by
  unfold diagMeasure; infer_instance

/-- Diagonal measures are regular, which is what allows continuous symbols to be approximated by
simple ones in the Borel calculus. -/
instance instRegular_diagMeasure (ξ : H) : (diagMeasure ha ξ).Regular := by
  unfold diagMeasure; infer_instance

/-- Continuous functions are integrable against a diagonal measure: the
spectrum is compact and the measure is finite. -/
theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ξ : H) (f : C(spectrum ℂ a, E)) : Integrable f (diagMeasure ha ξ) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Riesz–Markov–Kakutani, specialised: real symbols integrate to diagonal
values of the continuous functional calculus. -/
theorem integral_diagMeasure_ofReal (ξ : H) (g : C(spectrum ℂ a, ℝ)) :
    ∫ x, g x ∂(diagMeasure ha ξ) = (⟪ξ, cfcHom ha (ofRealLM g) ξ⟫_ℂ).re :=
  RealRMK.integral_rieszMeasure (diagFunctional ha ξ)
    (⟨g, HasCompactSupport.of_compactSpace g⟩ : C_c(spectrum ℂ a, ℝ))

/-- **The defining property of the diagonal measure.**  Integrating a
continuous symbol against `diagMeasure ha ξ` reproduces the diagonal matrix
element of its functional-calculus image. -/
theorem integral_diagMeasure (ξ : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ x, f x ∂(diagMeasure ha ξ) = ⟪ξ, cfcHom ha f ξ⟫_ℂ := by
  set u : C(spectrum ℂ a, ℝ) :=
    ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩ with hu
  set v : C(spectrum ℂ a, ℝ) :=
    ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩ with hv
  have hf : f = ofRealLM u + Complex.I • ofRealLM v := by
    ext x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im (f x)).symm
  have hiu : Integrable (fun x => ((u x : ℝ) : ℂ)) (diagMeasure ha ξ) :=
    integrable_of_continuous ha ξ (ofRealLM u)
  have hiv : Integrable (fun x => ((v x : ℝ) : ℂ)) (diagMeasure ha ξ) :=
    integrable_of_continuous ha ξ (ofRealLM v)
  have hlhs : ∫ x, f x ∂(diagMeasure ha ξ) =
      ((∫ x, u x ∂(diagMeasure ha ξ) : ℝ) : ℂ) +
        Complex.I * ((∫ x, v x ∂(diagMeasure ha ξ) : ℝ) : ℂ) := by
    conv_lhs => rw [hf]
    rw [show (fun x => (ofRealLM u + Complex.I • ofRealLM v) x) =
        (fun x => ((u x : ℝ) : ℂ) + Complex.I * ((v x : ℝ) : ℂ)) from rfl,
      integral_add hiu (hiv.const_mul Complex.I), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal]
  rw [hlhs, integral_diagMeasure_ofReal, integral_diagMeasure_ofReal,
    inner_cfcHom_ofReal_re, inner_cfcHom_ofReal_re]
  conv_rhs => rw [hf]
  rw [map_add, map_smul, _root_.add_apply, _root_.smul_apply, inner_add_right,
    inner_smul_right]

/-- The total mass of a diagonal measure is `‖ξ‖ ^ 2`. -/
@[simp] theorem diagMeasure_univ_toReal (ξ : H) :
    ((diagMeasure ha ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  have h := integral_diagMeasure ha ξ 1
  simp only [ContinuousMap.one_apply] at h
  rw [integral_const, Complex.real_smul, mul_one, MeasureTheory.measureReal_def, map_one] at h
  have h2 : ⟪ξ, (1 : H →L[ℂ] H) ξ⟫_ℂ = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [one_apply_eq_self, inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h2] at h
  exact_mod_cast h

end Functional

end BorelCalculus
end TauCeti
