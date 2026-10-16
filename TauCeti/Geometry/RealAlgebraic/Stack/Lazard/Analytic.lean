/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Basic
public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Analytic cells and ambient invariance of Lazard stacks

Every ambient cell of a Lazard delineation over a real analytic submanifold is again an
analytic submanifold: sections retain the dimension of the base, and sectors have one more
dimension. Thus the analytic base condition is preserved by successive Lazard liftings,
including liftings where ordinary polynomial fibers are nullified.

The ambient stack convention places the distinguished coordinate first, while Lazard
evaluation places it last. The valuation theorem retains the original Lazard coordinate
order by evaluating at `Fin.snoc (Fin.tail x) (x 0)`. For signs, this is evaluation of the
polynomial renamed by `finRotate`; no invariance of Lazard valuation under permutation is
asserted. These statements apply to the actual ambient `stackCells` used in cylindrical
decompositions.

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

/-- On every ambient stack cell the Lazard valuation is constant when its coordinates are read
in the original order, with the distinguished coordinate last. This includes zero members. -/
theorem lazardValuation_snoc_eq_of_mem_stackCells (k : ι)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root)
    {x y : Fin (n + 1) → ℝ} (hx : x ∈ E) (hy : y ∈ E) :
    (F k).lazardValuation (Fin.snoc (Fin.tail x) (x 0)) =
      (F k).lazardValuation (Fin.snoc (Fin.tail y) (y 0)) := by
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    simpa only [tail_cylinder, cylinder_apply_zero] using
      D.lazardValuation_snoc_eq_of_mem_sectionSet k hz hz'
  · obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    simpa only [tail_cylinder, cylinder_apply_zero] using
      D.lazardValuation_snoc_eq_of_mem_sectorSet k hz hz'

/-- Over a preconnected base, every member of a Lazard delineation is sign-invariant on each
ambient stack cell after moving the distinguished coordinate to the front. -/
theorem signInvariant_rename_finRotate_of_mem_stackCells (hS : IsPreconnected S) (k : ι)
    {E : Set (Fin (n + 1) → ℝ)} (hE : E ∈ stackCells S D.root) :
    SignInvariant (fun x ↦ eval x (rename (finRotate (n + 1)) (F k))) E := by
  have key : (fun x ↦ eval x (rename (finRotate (n + 1)) (F k))) ∘ cylinder S =
      fun z ↦ eval (Fin.snoc z.1.1 z.2) (F k) := by
    funext z
    rw [Function.comp_apply, eval_rename, cylinder_def, Fin.snoc_eq_cons_rotate]
    rfl
  rcases mem_stackCells.1 hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rw [signInvariant_image, key]
  exacts [D.signInvariant_sectionSet hS k i, D.signInvariant_sectorSet hS k j]

end TauCeti.LazardDelineation
