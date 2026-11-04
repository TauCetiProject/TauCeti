/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Area forms on surfaces are symplectic

On a two-dimensional manifold, a smooth two-form is symplectic exactly when it vanishes nowhere,
that is, when it is an area form. Both halves of the symplectic condition simplify in this
dimension:

* closedness is automatic, because a three-form on a two-dimensional space vanishes
  (`TauCeti.SmoothForm.isClosed_of_finrank_le`);
* an alternating form on a two-dimensional space is nondegenerate exactly when it is nonzero
  (`LinearMap.BilinForm.IsAlt.nondegenerate_iff_ne_zero_of_finrank_eq_two`).

So every surface carrying a nowhere-vanishing two-form is a symplectic manifold. Such a form is
also a nowhere-vanishing top form, so it orients the surface through
`TauCeti.Manifold.Orientation.ofTopForm`, as the orientation on which it is positive.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`: on a surface, a
  smooth two-form is fiberwise nondegenerate exactly when it vanishes nowhere.
* `TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`: on a surface, a
  smooth two-form is symplectic exactly when it vanishes nowhere.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.3 (area forms on oriented surfaces).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- On a two-dimensional manifold, a smooth two-form is fiberwise nondegenerate exactly when it
vanishes nowhere. -/
theorem isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two (hE : Module.finrank ℝ E = 2) :
    σ.IsNondegenerate ↔ ∀ x, σ.1 x ≠ 0 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  refine ⟨fun h ↦ h.apply_ne_zero, fun h ↦ isNondegenerate_iff_separatingLeft.2 fun x v hv ↦ ?_⟩
  -- `TangentSpace I x` is the model space `E` by definition
  have hx : Module.finrank ℝ (TangentSpace I x) = 2 := hE
  have hnd : (σ.bilinFormAt x).Nondegenerate := by
    rw [(SmoothForm.isAlt_bilinFormAt σ x).nondegenerate_iff_ne_zero_of_finrank_eq_two hx, ne_eq,
      SmoothForm.bilinFormAt_eq_zero_iff]
    exact h x
  exact hnd.1 v fun w ↦ by rw [SmoothForm.bilinFormAt_apply, hv w]

/-- **Area forms on surfaces are symplectic.** On a two-dimensional manifold, a smooth two-form is
symplectic exactly when it vanishes nowhere: closedness is automatic in dimension two. -/
theorem isSymplectic_iff_forall_ne_zero_of_finrank_eq_two (hE : Module.finrank ℝ E = 2) :
    σ.IsSymplectic ↔ ∀ x, σ.1 x ≠ 0 := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ hE
  rw [← isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two hE]
  exact ⟨IsSymplectic.isNondegenerate, fun h ↦ ⟨SmoothForm.isClosed_of_finrank_le hE.le σ, h⟩⟩

end TauCeti.SmoothTwoForm
