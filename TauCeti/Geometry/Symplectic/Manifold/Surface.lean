/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# Symplectic and almost complex geometry on surfaces

On a two-dimensional manifold, both the symplectic condition on a two-form and the formal
integrability condition on an almost complex structure simplify:

* a smooth two-form is closed automatically, because a three-form on a two-dimensional space
  vanishes (`TauCeti.SmoothForm.isClosed_of_finrank_le`), and an alternating form on a
  two-dimensional space is nondegenerate exactly when it is nonzero
  (`LinearMap.BilinForm.IsAlt.nondegenerate_iff_ne_zero_of_finrank_eq_two`);
* the Nijenhuis tensor of every smooth almost complex structure `J` vanishes identically: it
  vanishes on `(v, v)` by skew-symmetry and on `(v, J v)` by anticommutation with `J`, and every
  nonzero vector `v` together with `J v` spans a two-dimensional tangent space.

So every surface carrying a nowhere-vanishing two-form is a symplectic manifold, oriented through
`TauCeti.Manifold.Orientation.ofTopForm`, and every smooth almost complex structure on a manifold
of dimension at most two has vanishing Nijenhuis tensor.

## Main results

* `TauCeti.SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two`: on a surface, a
  smooth two-form is fiberwise nondegenerate exactly when it vanishes nowhere.
* `TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`: on a surface, a
  smooth two-form is symplectic exactly when it vanishes nowhere.
* `TauCeti.SmoothAlmostComplexStructure.nijenhuis_eq_zero_of_finrank_le_two` and
  `TauCeti.SmoothAlmostComplexStructure.nijenhuis_eq_zero_of_finrank_eq_two`: on a manifold of
  real dimension at most two (in particular on any surface), the Nijenhuis tensor vanishes.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.3 (area forms on oriented surfaces).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Appendix C.6 (integrability in real dimension two).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable {σ : SmoothTwoForm I M}

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

end SmoothTwoForm

namespace SmoothAlmostComplexStructure

/-- On a finite-dimensional real manifold of dimension at most two, every smooth almost complex
structure has vanishing Nijenhuis tensor. -/
theorem nijenhuis_eq_zero_of_finrank_le_two [FiniteDimensional ℝ E]
    (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E ≤ 2) :
    J.nijenhuis = 0 := by
  ext x v w
  -- `TangentSpace I x` is the model space `E` by definition.
  have hx : Module.finrank ℝ (TangentSpace I x) ≤ 2 := hE
  have hB : (J.nijenhuis x).toLinearMap₁₂ = 0 :=
    (J.almostComplexStructureAt x).bilin_eq_zero_of_finrank_le_two hx
      (fun u ↦ J.nijenhuis_self u)
      (fun u ↦ by simp)
  exact LinearMap.congr_fun₂ hB v w

/-- **Every almost complex structure on a surface has vanishing Nijenhuis tensor.** -/
theorem nijenhuis_eq_zero_of_finrank_eq_two [FiniteDimensional ℝ E]
    (J : SmoothAlmostComplexStructure I M) (hE : Module.finrank ℝ E = 2) :
    J.nijenhuis = 0 :=
  J.nijenhuis_eq_zero_of_finrank_le_two hE.le

end SmoothAlmostComplexStructure

end TauCeti
