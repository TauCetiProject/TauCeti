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
critical point into a degenerate one.

A smooth scalar change of values with nonvanishing derivative preserves Morse functions.
At a nondegenerate critical point a decreasing change complements the Morse index.
In particular, for a nonnegative Morse exhaustion ρ, the reciprocal function `(1 + ρ)⁻¹`
is Morse and its indices are complementary to those of ρ. This local statement does not
assert properness of the reciprocal function or extension to a compactification.

## Main results

* `TauCeti.criticalPoints_scalar_comp`: the critical points of `φ ∘ f`.
* `TauCeti.criticalHessian_scalar_comp`: the critical Hessian of `φ ∘ f` at a critical point
  of `f`.
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
  · have hle (g : M → ℝ) : manifoldMorseIndex I g x ≤ Module.finrank ℝ E := by
      rw [manifoldMorseIndex_def, morseIndex_def]
      rw [← sigPos_neg]
      exact sigPos_le_finrank _
    have h0 : Module.finrank ℝ E = 0 := Module.finrank_of_not_finite (by simpa using hE)
    have h1 := hle (φ ∘ f)
    have h2 := hle f
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
