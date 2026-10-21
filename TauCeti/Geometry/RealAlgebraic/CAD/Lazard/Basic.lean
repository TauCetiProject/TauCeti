/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.LazardInvariant
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Analytic
public import TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Semialgebraic
public import TauCeti.Geometry.RealAlgebraic.Stack.Map
public import TauCeti.RingTheory.MvPolynomial.Lazard.Reindex

/-!
# Lifting cylindrical decompositions by Lazard delineations

A cylindrical algebraic decomposition of the base lifts through a family of Lazard
delineations, one over each base cell. The resulting sections and sectors are semialgebraic,
form a cylindrical algebraic decomposition of the cylinder, and remain analytic submanifolds
when the base cells are analytic submanifolds.

The Lazard valuation of every input is constant on each lifted cell when the new cylinder
coordinate is read last, as required by Lazard evaluation. In the ambient CAD convention the
new coordinate is coordinate zero. Rotating the input variables reconciles these conventions;
the rotated inputs are sign-invariant, and `MvPolynomial.lazardValuationReindex` records the
inverse rotation in their valuation, on every lifted cell.

The delineations may also be taken over reordered base cells `{x | x ∘ e ∈ C}` for a fixed
permutation `e` of the base coordinates. Pulling their stacks back gives stacks over the original
cells, so the lifted decomposition is again cylindrical in the ambient coordinate order, while
the Lazard valuations are constant when the base coordinates are read in the order `e`. This is
what lets recursive Lazard lifting read all coordinates in one fixed order at every level.

This is the CAD-level assembly step in Lazard's projection-and-lifting construction. The
separate analytic lifting theorem supplies the Lazard delineation over each base cell.

## Main results

* `TauCeti.IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation_comp`: CAD lifting by
  Lazard delineations over reordered base cells.
* `TauCeti.IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation`: CAD lifting by Lazard
  delineations over the base cells themselves.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {n : ℕ} {ι : Type*} {F : ι → MvPolynomial (Fin (n + 1)) ℝ}

/-- **CAD lifting by Lazard delineations over permuted bases.** Let `e` permute the base
coordinates. Suppose every cell `C` of a cylindrical algebraic decomposition of `ℝ ^ n` is an
analytic submanifold, and a fixed family has a Lazard delineation over the reordered cell
`{x | x ∘ e ∈ C}`. The stacks of those delineations, pulled back to the original coordinates, form
a cylindrical algebraic decomposition of `ℝ ^ (n + 1)` whose projection is the original one.

Every lifted cell is an analytic submanifold. The Lazard valuation of every member is constant on
every lifted cell when it is evaluated at the reordered base point followed by the new
coordinate. -/
theorem IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation_comp
    {𝓓 : Set (Set (Fin n → ℝ))} (h𝓓 : IsCAD n 𝓓)
    (hanalytic : ∀ C ∈ 𝓓, ∃ d, IsAnalyticSubmanifold d C) (e : Equiv.Perm (Fin n))
    (hD : ∀ C ∈ 𝓓, Nonempty (LazardDelineation F ((fun x ↦ x ∘ e) ⁻¹' C))) :
    ∃ 𝓒, IsCAD (n + 1) 𝓒 ∧ image Fin.tail '' 𝓒 = 𝓓 ∧
      (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      ∀ k, ∀ E ∈ 𝓒, ∀ x ∈ E, ∀ y ∈ E,
        (F k).lazardValuation (Fin.snoc (Fin.tail x ∘ e.symm) (x 0)) =
          (F k).lazardValuation (Fin.snoc (Fin.tail y ∘ e.symm) (y 0)) := by
  obtain ⟨𝓒, h𝓒, htail, hP⟩ := h𝓓.exists_succ_of_forall_exists_stack
    (fun E ↦ (∃ d, IsAnalyticSubmanifold d E) ∧ ∀ k, ∀ x ∈ E, ∀ y ∈ E,
      (F k).lazardValuation (Fin.snoc (Fin.tail x ∘ e.symm) (x 0)) =
        (F k).lazardValuation (Fin.snoc (Fin.tail y ∘ e.symm) (y 0))) fun C hC ↦ by
    obtain ⟨D⟩ := hD C hC
    obtain ⟨d, hd⟩ := hanalytic C hC
    obtain ⟨hθ, ha⟩ := (D.isSemialgebraicStack ((h𝓓.isSemialgebraic hC).preimage_comp e)).reindex
      e.symm fun E hE ↦ (D.exists_isAnalyticSubmanifold_of_mem_stackCells
        (hd.preimage_comp_perm e) hE).imp fun _ h ↦ h.2
    -- Reordering back by `e.symm` recovers the cell `C` itself.
    have hC' : (fun x ↦ x ∘ e.symm) ⁻¹' ((fun x ↦ x ∘ e) ⁻¹' C) = C := by
      ext x
      simp [Function.comp_assoc]
    rw [← hC']
    refine ⟨D.count, _, hθ, fun E hE ↦ ⟨ha E hE, fun k x hx y hy ↦ ?_⟩⟩
    rw [stackCells_comp] at hE
    obtain ⟨E, hE, rfl⟩ := hE
    simpa only [Fin.tail_cons, Fin.cons_zero] using
      D.lazardValuation_snoc_eq_of_mem_stackCells k hE hx hy
  exact ⟨𝓒, h𝓒, htail, fun E hE ↦ (hP E hE).1, fun k E hE ↦ (hP E hE).2 k⟩

/-- **CAD lifting by Lazard delineations.** Suppose every cell of a cylindrical algebraic
decomposition of `ℝ ^ n` is an analytic submanifold and carries a Lazard delineation of a
fixed polynomial family. Then the stacks of those delineations form a cylindrical algebraic
decomposition of `ℝ ^ (n + 1)` with the original decomposition as its projection.

Every lifted cell is an analytic submanifold. For each rotated family member, its valuation in
the coordinate order given by the inverse rotation is constant there, and the same rotated
member is sign-invariant in the ambient coordinate order. -/
theorem IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation
    {𝓓 : Set (Set (Fin n → ℝ))} (h𝓓 : IsCAD n 𝓓)
    (hanalytic : ∀ C ∈ 𝓓, ∃ d, IsAnalyticSubmanifold d C)
    (hD : ∀ C ∈ 𝓓, Nonempty (LazardDelineation F C)) :
    ∃ 𝓒, IsCAD (n + 1) 𝓒 ∧ image Fin.tail '' 𝓒 = 𝓓 ∧
      (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      (∀ k E, E ∈ 𝓒 → ∀ x ∈ E, ∀ y ∈ E,
        (rename (finRotate (n + 1)) (F k)).lazardValuationReindex
            (finRotate (n + 1)).symm x =
          (rename (finRotate (n + 1)) (F k)).lazardValuationReindex
            (finRotate (n + 1)).symm y) ∧
      ∀ k E, E ∈ 𝓒 → SignInvariant
        (fun x ↦ eval x (rename (finRotate (n + 1)) (F k))) E := by
  obtain ⟨𝓒, h𝓒, htail, ha, hv⟩ :=
    h𝓓.exists_isCAD_lazardValuation_eq_of_lazardDelineation_comp hanalytic (Equiv.refl _)
      fun C hC ↦ by simpa using hD C hC
  have hval (k : ι) {E} (hE : E ∈ 𝓒) {x} (hx : x ∈ E) {y} (hy : y ∈ E) :
      (rename (finRotate (n + 1)) (F k)).lazardValuationReindex (finRotate (n + 1)).symm x =
        (rename (finRotate (n + 1)) (F k)).lazardValuationReindex (finRotate (n + 1)).symm y := by
    simpa only [lazardValuationReindex_finRotate_symm, rename_rename, Equiv.symm_comp_self,
      rename_id_apply, Equiv.coe_refl, Equiv.refl_symm, Function.comp_id] using hv k E hE x hx y hy
  exact ⟨𝓒, h𝓒, htail, ha, fun k E hE x hx y hy ↦ hval k hE hx hy, fun k E hE ↦
    (h𝓒.isConnected hE).isPreconnected.signInvariant_eval_of_lazardValuationReindex_eq
      fun x hx y hy ↦ hval k hE hx hy⟩

end TauCeti
