/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import TauCeti.Analysis.Calculus.Morse.ScalarComposition
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Scalar reparametrization of manifold Morse functions

For a scalar change of values `φ : ℝ → ℝ`, the differential of `φ ∘ f` is `φ'(f x)` times the
differential of `f` (`TauCeti.mvfderiv_scalar_comp`), so the critical points of `φ ∘ f` are those
of `f` together with the points where `f` takes a critical point of `φ`. At a critical point of
`f` the critical Hessian of `φ ∘ f` is `φ'(f x)` times that of `f`. In particular, when
`φ'(f x) = 0` it vanishes, so a scalar change with a critical point can turn a nondegenerate
critical point into a degenerate one. At a point where `φ'(f x) = 0`, whether or not it is a
critical point of `f`, the second-order chain rule gives the critical Hessian `φ''(f x) df ⊗ df`
instead; this is how a scalar change turns regular levels of `f` into critical submanifolds of
`φ ∘ f` (`TauCeti.Geometry.Manifold.Morse.Bott.ScalarComposition`).

A smooth scalar change of values with nonvanishing derivative preserves Morse functions.
An increasing change preserves the Morse index at a critical point, and at a nondegenerate
critical point a decreasing change complements it.
In particular, for a nonnegative Morse exhaustion ρ, the reciprocal function `(1 + ρ)⁻¹`
is Morse and its indices are complementary to those of ρ. This local statement does not
assert properness of the reciprocal function or extension to a compactification.

## Main results

* `TauCeti.criticalPoints_scalar_comp`: the critical points of `φ ∘ f`.
* `TauCeti.criticalHessian_scalar_comp`: the critical Hessian of `φ ∘ f` at a critical point
  of `f`.
* `TauCeti.manifoldMorseIndex_scalar_comp_of_pos`: an increasing scalar change preserves the Morse
  index at a critical point.
* `TauCeti.criticalHessian_scalar_comp_apply_of_deriv_eq_zero`: where `φ` is critical at the value
  `f x`, the critical Hessian of `φ ∘ f` is `φ''(f x) df ⊗ df`.
* `TauCeti.manifoldMorseIndex_scalar_comp_eq_zero_of_iteratedDeriv_two_nonneg`: there, if
  `φ''(f x) ≥ 0`, the Morse index of `φ ∘ f` is `0`.
* `TauCeti.ker_criticalHessian_scalar_comp_of_deriv_eq_zero`: there, if `φ''(f x) ≠ 0` and `x` is
  a regular point of `f`, the kernel of the critical Hessian of `φ ∘ f` is `ker df`.
* `TauCeti.manifoldMorseIndex_scalar_comp_eq_one_of_iteratedDeriv_two_neg`: there, if
  `φ''(f x) < 0` and `x` is a regular point of `f`, the Morse index of `φ ∘ f` is `1`.
* `TauCeti.IsMorse.scalar_comp`: a scalar change with nonzero derivative preserves Morse functions.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Sections 3 and 7.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {φ : ℝ → ℝ} {x : M}

namespace IsManifoldNondegenerateCriticalPoint

/-- Scalar post-composition with nonzero derivative preserves nondegenerate critical points. -/
theorem scalar_comp
    (h : IsManifoldNondegenerateCriticalPoint I f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) ≠ 0) :
    IsManifoldNondegenerateCriticalPoint I (φ ∘ f) x := by
  rw [isManifoldNondegenerateCriticalPoint_iff] at h ⊢
  have hφcoord : ContDiffAt ℝ 2 φ ((f ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
    simpa using hφ
  have hφcoord' : deriv φ ((f ∘ (extChartAt I x).symm) (extChartAt I x x)) ≠ 0 := by
    simpa using hφ'
  exact h.scalar_comp hφcoord hφcoord'

/-- A decreasing scalar change of values complements the manifold Morse index at a
nondegenerate critical point. -/
theorem manifoldMorseIndex_scalar_comp_add_manifoldMorseIndex_eq_finrank
    (h : IsManifoldNondegenerateCriticalPoint I f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) < 0) :
    manifoldMorseIndex I (φ ∘ f) x + manifoldMorseIndex I f x = Module.finrank ℝ E := by
  by_cases hE : FiniteDimensional ℝ E
  · rw [isManifoldNondegenerateCriticalPoint_iff] at h
    rw [manifoldMorseIndex_def, manifoldMorseIndex_def, Function.comp_assoc]
    apply h.morseIndex_scalar_comp_add_morseIndex_eq_finrank
    · simpa using hφ
    · simpa using hφ'
  · have h0 : Module.finrank ℝ E = 0 := Module.finrank_of_not_finite (by simpa using hE)
    have h1 := manifoldMorseIndex_le_finrank (I := I) (f := φ ∘ f) (x := x)
    have h2 := manifoldMorseIndex_le_finrank (I := I) (f := f) (x := x)
    omega

end IsManifoldNondegenerateCriticalPoint

/-- A point is critical for `φ ∘ f` exactly when `φ` is critical at `f x` or `x` is critical
for `f`. -/
theorem mem_criticalPoints_scalar_comp_iff_or (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hφ : DifferentiableAt ℝ φ (f x)) :
    x ∈ criticalPoints I (φ ∘ f) ↔ deriv φ (f x) = 0 ∨ x ∈ criticalPoints I f := by
  rw [mem_criticalPoints, mem_criticalPoints, mvfderiv_scalar_comp hf hφ, smul_eq_zero]

/-- A scalar change with nonzero derivative preserves critical points. -/
theorem mem_criticalPoints_scalar_comp_iff (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hφ' : deriv φ (f x) ≠ 0) :
    x ∈ criticalPoints I (φ ∘ f) ↔ x ∈ criticalPoints I f := by
  rw [mem_criticalPoints_scalar_comp_iff_or hf (differentiableAt_of_deriv_ne_zero hφ'),
    or_iff_right hφ']

/-- The critical points of `φ ∘ f` are the critical points of `f` together with the points where
`f` takes a critical point of `φ`, that is, a value at which `φ'` vanishes. -/
theorem criticalPoints_scalar_comp (hf : MDifferentiable I 𝓘(ℝ) f) (hφ : Differentiable ℝ φ) :
    criticalPoints I (φ ∘ f) = f ⁻¹' {t | deriv φ t = 0} ∪ criticalPoints I f :=
  Set.ext fun x ↦ mem_criticalPoints_scalar_comp_iff_or (hf x) (hφ (f x))

/-- At a critical point of `f`, a scalar change of values scales the critical Hessian by
`φ'(f x)`. -/
theorem criticalHessian_scalar_comp [I.Boundaryless] (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hx : x ∈ criticalPoints I f) :
    criticalHessian I (φ ∘ f) x = deriv φ (f x) • criticalHessian I f x := by
  have hφcoord : ContDiffAt ℝ 2 φ ((f ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
    simpa using hφ
  rw [criticalHessian_def, criticalHessian_def, Function.comp_assoc,
    fderiv_fderiv_scalar_comp_of_fderiv_eq_zero hφcoord hf.contDiffAt_comp_extChartAt_symm
      (mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.1 hx), comp_apply,
    extChartAt_to_inv]
  -- The two sides differ only in reading the model space `E` as `TangentSpace I x`.
  rfl

/-- An increasing scalar change of values preserves the Morse index at a critical point. -/
theorem manifoldMorseIndex_scalar_comp_of_pos [I.Boundaryless] (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hx : x ∈ criticalPoints I f) (hφ' : 0 < deriv φ (f x)) :
    manifoldMorseIndex I (φ ∘ f) x = manifoldMorseIndex I f x := by
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, Function.comp_assoc]
  exact morseIndex_scalar_comp_of_pos (by simpa using hφ) hf.contDiffAt_comp_extChartAt_symm
    (mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.1 hx) (by simpa using hφ')

/-- Where the value `f x` is a critical point of `φ`, the critical Hessian of `φ ∘ f` at `x` is
`φ''(f x) df ⊗ df`, whether or not `x` is a critical point of `f`. -/
theorem criticalHessian_scalar_comp_apply_of_deriv_eq_zero [I.Boundaryless]
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) = 0)
    (v w : TangentSpace I x) :
    criticalHessian I (φ ∘ f) x v w =
      iteratedDeriv 2 φ (f x) * (mvfderiv I f x v * mvfderiv I f x w) := by
  have hφcoord : ContDiffAt ℝ 2 φ ((f ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
    simpa using hφ
  have h := fderiv_fderiv_scalar_comp_apply hφcoord hf.contDiffAt_comp_extChartAt_symm
    (v : E) (w : E)
  simp only [comp_apply, extChartAt_to_inv, hφ', smul_eq_mul, mul_zero, add_zero] at h
  rw [criticalHessian_def, Function.comp_assoc, mvfderiv_eq_fderiv_comp_extChartAt_symm]
  -- The two sides differ only in reading the model space `E` as `TangentSpace I x`.
  exact h.trans (mul_comm _ _)

/-- Where the value `f x` is a critical point of `φ` with `φ''(f x) ≥ 0`, the Morse index of
`φ ∘ f` at `x` is `0`: its critical Hessian `φ''(f x) df ⊗ df` is nonnegative. -/
theorem manifoldMorseIndex_scalar_comp_eq_zero_of_iteratedDeriv_two_nonneg [I.Boundaryless]
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) = 0)
    (hφ'' : 0 ≤ iteratedDeriv 2 φ (f x)) :
    manifoldMorseIndex I (φ ∘ f) x = 0 := by
  by_cases hE : FiniteDimensional ℝ E
  swap
  · rw [manifoldMorseIndex_def, morseIndex_eq_zero_of_not_finiteDimensional hE]
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian,
    ← QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero]
  intro v
  rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply,
    criticalHessian_scalar_comp_apply_of_deriv_eq_zero hf hφ hφ']
  exact mul_nonneg hφ'' (mul_self_nonneg _)

/-- Where the value `f x` is a nondegenerate critical point of `φ` and `x` is a regular point of
`f`, the kernel of the critical Hessian `φ''(f x) df ⊗ df` of `φ ∘ f` at `x` is the hyperplane
`ker df`. -/
theorem ker_criticalHessian_scalar_comp_of_deriv_eq_zero [I.Boundaryless]
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hreg : IsRegularPoint I 𝓘(ℝ) f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) = 0)
    (hφ'' : iteratedDeriv 2 φ (f x) ≠ 0) :
    (criticalHessian I (φ ∘ f) x).ker = (mfderiv I 𝓘(ℝ) f x).ker := by
  have hH := criticalHessian_scalar_comp_apply_of_deriv_eq_zero hf hφ hφ'
  rw [← ker_mvfderiv]
  -- Pair a vector `v` with a vector `w` on which `df` is `1`.
  obtain ⟨w, hw⟩ := isRegularPoint_iff_surjective_mvfderiv.1 hreg 1
  ext v
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine ⟨fun hv ↦ ?_, fun hv ↦ ContinuousLinearMap.ext fun u ↦ ?_⟩
  · have hvw := congr($hv w)
    rw [hH, hw, mul_one, zero_apply] at hvw
    exact (mul_eq_zero.1 hvw).resolve_left hφ''
  · rw [hH, hv, zero_mul, mul_zero, zero_apply]

/-- Where the value `f x` is a critical point of `φ` with `φ''(f x) < 0` and `x` is a regular
point of `f`, the Morse index of `φ ∘ f` at `x` is `1`: its critical Hessian
`φ''(f x) df ⊗ df` is nonpositive, and its kernel is the hyperplane `ker df`. -/
theorem manifoldMorseIndex_scalar_comp_eq_one_of_iteratedDeriv_two_neg [I.Boundaryless]
    [FiniteDimensional ℝ E] (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hreg : IsRegularPoint I 𝓘(ℝ) f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) = 0)
    (hφ'' : iteratedDeriv 2 φ (f x) < 0) :
    manifoldMorseIndex I (φ ∘ f) x = 1 := by
  have hH := criticalHessian_scalar_comp_apply_of_deriv_eq_zero hf hφ hφ'
  -- The coindex vanishes, since the Hessian is nonpositive.
  have hpos : sigPos (criticalHessian I (φ ∘ f) x).toBilinForm.toQuadraticMap = 0 := by
    rw [← QuadraticForm.forall_nonpos_iff_sigPos_eq_zero]
    intro v
    rw [LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply, hH]
    exact mul_nonpos_of_nonpos_of_nonneg hφ''.le (mul_self_nonneg _)
  -- The radical is `ker df`.
  have hrad : (criticalHessian I (φ ∘ f) x).toBilinForm.toQuadraticMap.radical =
      (mfderiv I 𝓘(ℝ) f x).ker := by
    rw [radical_toQuadraticMap_toBilinForm_criticalHessian (hφ.contMDiffAt.comp x hf),
      ker_criticalHessian_scalar_comp_of_deriv_eq_zero hf hreg hφ hφ' hφ''.ne]
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (criticalHessian I (φ ∘ f) x).toBilinForm.toQuadraticMap)
  have hdim := hreg.finrank_ker_mfderiv_add_finrank
  rw [hpos, hrad] at hsum
  rw [Module.finrank_self] at hdim
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian]
  have : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  omega

/-- A scalar change smooth near the values of a Morse function, with nonzero derivative there,
preserves the property of being Morse on a set. -/
theorem IsMorseOn.scalar_comp {s : Set M} (h : IsMorseOn I f s)
    (hφ : ∀ x ∈ s, ContDiffAt ℝ ∞ φ (f x))
    (hφ' : ∀ x ∈ s, deriv φ (f x) ≠ 0) : IsMorseOn I (φ ∘ f) s := by
  apply isMorseOn_iff.mpr
  refine ⟨fun x hx ↦ ?_, fun x hx hc ↦ ?_⟩
  · exact (hφ x hx).contMDiffAt.comp_contMDiffWithinAt x (h.contMDiffOn x hx)
  · have hφcoord' : deriv φ ((f ∘ (extChartAt I x).symm) (extChartAt I x x)) ≠ 0 := by
      simpa using hφ' x hx
    rw [Function.comp_assoc] at hc
    have hc' := (fderiv_scalar_comp_eq_zero_iff
      (h.differentiableAt_comp_extChartAt_symm hx) hφcoord').mp hc
    exact (h.isManifoldNondegenerateCriticalPoint hx hc').scalar_comp
      ((hφ x hx).of_le (by simp)) (hφ' x hx)

/-- A smooth scalar change with nonzero derivative along the range preserves Morse functions. -/
theorem IsMorse.scalar_comp (h : IsMorse I f)
    (hφ : ∀ x, ContDiffAt ℝ ∞ φ (f x)) (hφ' : ∀ x, deriv φ (f x) ≠ 0) :
    IsMorse I (φ ∘ f) :=
  isMorseOn_univ.mp <|
    (isMorseOn_univ.mpr h).scalar_comp (fun x _ ↦ hφ x) (fun x _ ↦ hφ' x)

/-- The reciprocal of one plus a Morse function is Morse wherever the denominator is nonzero. -/
theorem IsMorse.inv_one_add (h : IsMorse I f) (hf : ∀ x, 1 + f x ≠ 0) :
    IsMorse I (fun x ↦ (1 + f x)⁻¹) := by
  apply h.scalar_comp (φ := fun t ↦ (1 + t)⁻¹)
  · intro x
    exact (contDiffAt_const.add contDiffAt_id).inv (hf x)
  · intro x
    rw [deriv_fun_inv'' (differentiableAt_id.const_add 1) (hf x)]
    simp [hf x]

namespace IsManifoldNondegenerateCriticalPoint

/-- At a nondegenerate critical point, taking the reciprocal of one plus the function
complements its index, provided the denominator is nonzero. -/
theorem manifoldMorseIndex_inv_one_add_add_manifoldMorseIndex_eq_finrank
    (h : IsManifoldNondegenerateCriticalPoint I f x) (hf : 1 + f x ≠ 0) :
    manifoldMorseIndex I (fun y ↦ (1 + f y)⁻¹) x + manifoldMorseIndex I f x =
      Module.finrank ℝ E := by
  apply h.manifoldMorseIndex_scalar_comp_add_manifoldMorseIndex_eq_finrank
    (φ := fun t ↦ (1 + t)⁻¹) ((contDiffAt_const.add contDiffAt_id).inv hf)
  rw [deriv_fun_inv'' (differentiableAt_id.const_add 1) hf]
  simpa using div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) (sq_pos_of_ne_zero hf)

end IsManifoldNondegenerateCriticalPoint

end TauCeti
