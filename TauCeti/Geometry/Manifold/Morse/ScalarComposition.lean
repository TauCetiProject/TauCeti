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

/-!
# Scalar reparametrization of manifold Morse functions

A smooth scalar change of values with nonvanishing derivative preserves Morse functions.
At a nondegenerate critical point a decreasing change complements the Morse index.
In particular, for a nonnegative Morse exhaustion ρ, the reciprocal function `(1 + ρ)⁻¹`
is Morse and its indices are complementary to those of ρ. This local statement does not
assert properness of the reciprocal function or extension to a compactification.

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

/-- Scalar post-composition with nonzero derivative preserves nondegenerate critical points. -/
theorem IsManifoldNondegenerateCriticalPoint.scalar_comp
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
theorem IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_scalar_comp_add_eq_finrank
    [FiniteDimensional ℝ E] (h : IsManifoldNondegenerateCriticalPoint I f x)
    (hφ : ContDiffAt ℝ 2 φ (f x)) (hφ' : deriv φ (f x) < 0) :
    manifoldMorseIndex I (φ ∘ f) x + manifoldMorseIndex I f x = Module.finrank ℝ E := by
  rw [isManifoldNondegenerateCriticalPoint_iff] at h
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, Function.comp_assoc]
  apply h.morseIndex_scalar_comp_add_morseIndex_eq_finrank
  · simpa using hφ
  · simpa using hφ'

/-- On a boundaryless manifold, a scalar change with nonzero derivative preserves critical
points. -/
theorem mem_criticalPoints_scalar_comp_iff [I.Boundaryless]
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (hφ : DifferentiableAt ℝ φ (f x))
    (hφ' : deriv φ (f x) ≠ 0) :
    x ∈ criticalPoints I (φ ∘ f) ↔ x ∈ criticalPoints I f := by
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero,
    mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero, Function.comp_assoc]
  apply fderiv_scalar_comp_eq_zero_iff
  · simpa using hφ
  · exact mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.mp hf
  · simpa using hφ'

/-- A scalar change smooth near the values of a Morse function, with nonzero derivative there,
preserves the property of being Morse on a set. -/
theorem IsMorseOn.scalar_comp {s : Set M} (h : IsMorseOn I f s)
    (hφ : ∀ x ∈ s, ContDiffAt ℝ ∞ φ (f x))
    (hφ' : ∀ x ∈ s, deriv φ (f x) ≠ 0) : IsMorseOn I (φ ∘ f) s := by
  apply isMorseOn_iff.mpr
  refine ⟨fun x hx ↦ ?_, fun x hx hc ↦ ?_⟩
  · exact (hφ x hx).contMDiffAt.comp_contMDiffWithinAt x (h.contMDiffOn x hx)
  · have hφcoord : DifferentiableAt ℝ φ
        ((f ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
      simpa using (hφ x hx).differentiableAt (by simp)
    have hφcoord' : deriv φ ((f ∘ (extChartAt I x).symm) (extChartAt I x x)) ≠ 0 := by
      simpa using hφ' x hx
    rw [Function.comp_assoc] at hc
    have hc' := (fderiv_scalar_comp_eq_zero_iff hφcoord
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
    have hne := hf x
    have hd : HasDerivAt (fun t : ℝ ↦ (1 + t)⁻¹) (-1 / (1 + f x) ^ 2) (f x) := by
      simpa using ((hasDerivAt_id (f x)).const_add 1).fun_inv hne
    rw [hd.deriv]
    simp [hne]

/-- At a nondegenerate critical point, taking the reciprocal of one plus the function
complements its index, provided the denominator is nonzero. -/
theorem IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_inv_one_add_add_eq_finrank
    [FiniteDimensional ℝ E] (h : IsManifoldNondegenerateCriticalPoint I f x)
    (hf : 1 + f x ≠ 0) :
    manifoldMorseIndex I (fun y ↦ (1 + f y)⁻¹) x + manifoldMorseIndex I f x =
      Module.finrank ℝ E := by
  apply h.manifoldMorseIndex_scalar_comp_add_eq_finrank (φ := fun t ↦ (1 + t)⁻¹)
    ((contDiffAt_const.add contDiffAt_id).inv hf)
  have hd : HasDerivAt (fun t : ℝ ↦ (1 + t)⁻¹) (-1 / (1 + f x) ^ 2) (f x) := by
    simpa using ((hasDerivAt_id (f x)).const_add 1).fun_inv hf
  rw [hd.deriv]
  exact div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_ne_zero hf)

end TauCeti
