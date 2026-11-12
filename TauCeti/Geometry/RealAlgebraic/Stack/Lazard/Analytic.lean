/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors

/-!
# Analytic cells of Lazard stacks

Every ambient cell of a Lazard delineation over a real analytic submanifold is again an
analytic submanifold: sections retain the dimension of the base, and sectors have one more
dimension. Thus the analytic base condition is preserved by successive Lazard liftings,
including liftings where ordinary polynomial fibers are nullified.

## Main declarations

* `TauCeti.LazardDelineation.isAnalyticSubmanifold_sectionSet`: every ambient section over an
  analytic submanifold is analytic of the same dimension.
* `TauCeti.LazardDelineation.exists_isAnalyticSubmanifold_of_mem_stackCells`: every ambient
  stack cell over an analytic submanifold is analytic, with the section or sector dimension.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.
-/

public section

open Function MvPolynomial Set

namespace TauCeti.LazardDelineation

variable {ι : Type*} {n d : ℕ} {F : ι → MvPolynomial (Fin (n + 1)) ℝ}
  {S : Set (Fin n → ℝ)} (D : LazardDelineation F S)

/-- Every ambient section of a Lazard delineation over an analytic submanifold is an analytic
submanifold of the same dimension, even if ordinary fibers are nullified. -/
theorem isAnalyticSubmanifold_sectionSet (hS : IsAnalyticSubmanifold d S) (i : Fin D.count) :
    IsAnalyticSubmanifold d (cylinder S '' sectionSet D.root i) := by
  let r := Function.extend Subtype.val (D.root i) (fun _ ↦ 0)
  have hr (x : S) : r x = D.root i x := Subtype.val_injective.extend_apply _ _ x
  exact isAnalyticSubmanifold_image_cylinder_sectionSet hS i hr
    (D.analyticOnSubmanifold_root hS i hr)

/-- Every ambient cell of a Lazard delineation over a `d`-dimensional analytic submanifold is
analytic, of dimension `d` for sections and `d + 1` for sectors. -/
theorem exists_isAnalyticSubmanifold_of_mem_stackCells (hS : IsAnalyticSubmanifold d S)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    ∃ e, (e = d ∨ e = d + 1) ∧ IsAnalyticSubmanifold e E := by
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨d, Or.inl rfl, D.isAnalyticSubmanifold_sectionSet hS i⟩
  · exact ⟨d + 1, Or.inr rfl, isAnalyticSubmanifold_image_cylinder_sectorSet hS
      D.continuous_root D.strictMono_root j⟩

end TauCeti.LazardDelineation
