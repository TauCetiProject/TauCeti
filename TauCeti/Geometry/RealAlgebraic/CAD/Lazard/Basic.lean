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

The delineation over a base cell may also be given in a reordered presentation of the base:
over the cell read through a permutation of its coordinates. The stacks are then pulled back
to the original cells, and the Lazard valuation is constant when the base coordinates are read
through that permutation. This is how a recursive construction, whose base valuations are taken
in a coordinate order other than the native one, feeds its base cells to Lazard lifting.
Constant Lazard valuation in any coordinate order gives sign-invariance on connected sets.

This is the CAD-level assembly step in Lazard's projection-and-lifting construction. The
separate analytic lifting theorem supplies the Lazard delineation over each base cell.

## Main results

* `TauCeti.IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation_reindex`: lifting a CAD
  through Lazard delineations over its cells read in a permuted coordinate order.
* `TauCeti.IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation`: lifting a CAD through
  Lazard delineations over its cells in the native coordinate order.

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

/-- **CAD lifting by Lazard delineations in a reordered base.** Suppose every cell `C` of a
cylindrical algebraic decomposition of `ℝ ^ n` is an analytic submanifold, and its reordering
`(· ∘ e.symm) ⁻¹' C` by a permutation `e` of the base coordinates carries a Lazard delineation
of a fixed polynomial family. Then the stacks of those delineations, pulled back to the
original cells, form a cylindrical algebraic decomposition of `ℝ ^ (n + 1)` with the original
decomposition as its projection.

Every lifted cell is an analytic submanifold. On it, every family member has constant Lazard
valuation when the base coordinates are read through `e` and the new coordinate is read last. -/
theorem IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation_reindex
    {𝓓 : Set (Set (Fin n → ℝ))} (h𝓓 : IsCAD n 𝓓) (e : Equiv.Perm (Fin n))
    (hanalytic : ∀ C ∈ 𝓓, ∃ d, IsAnalyticSubmanifold d C)
    (hD : ∀ C ∈ 𝓓, Nonempty (LazardDelineation F ((fun x ↦ x ∘ e.symm) ⁻¹' C))) :
    ∃ 𝓒, IsCAD (n + 1) 𝓒 ∧ image Fin.tail '' 𝓒 = 𝓓 ∧
      (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      ∀ k E, E ∈ 𝓒 → ∀ x ∈ E, ∀ y ∈ E,
        (F k).lazardValuation (Fin.snoc (Fin.tail x ∘ e) (x 0)) =
          (F k).lazardValuation (Fin.snoc (Fin.tail y ∘ e) (y 0)) := by
  obtain ⟨𝓒, h𝓒, htail, hP⟩ := h𝓓.exists_succ_of_forall_exists_stack
    (fun E ↦ (∃ d, IsAnalyticSubmanifold d E) ∧
      ∀ i, ∀ x ∈ E, ∀ y ∈ E,
        (F i).lazardValuation (Fin.snoc (Fin.tail x ∘ e) (x 0)) =
          (F i).lazardValuation (Fin.snoc (Fin.tail y ∘ e) (y 0))) fun C hC ↦ by
    obtain ⟨D⟩ := hD C hC
    obtain ⟨d, hd⟩ := hanalytic C hC
    -- Write `C` as the pullback along `e` of the reordered cell carrying the delineation.
    generalize hS : (fun x ↦ x ∘ e.symm) ⁻¹' C = S at D
    have hSd : IsAnalyticSubmanifold d S := hS ▸ hd.preimage_comp_equiv e.symm
    have hSsemi : IsSemialgebraic S := hS ▸ (h𝓓.isSemialgebraic hC).preimage_comp e.symm
    have hCS : C = (fun x ↦ x ∘ e) ⁻¹' S := by
      ext x
      simp [← hS, Function.comp_assoc]
    subst hCS
    obtain ⟨hθ, ha⟩ := (D.isSemialgebraicStack hSsemi).reindex e
      fun E hE ↦ (D.exists_isAnalyticSubmanifold_of_mem_stackCells hSd hE).imp fun _ h ↦ h.2
    refine ⟨D.count, fun i x ↦ D.root i ⟨x.1 ∘ e, x.2⟩, hθ, fun E hE ↦ ⟨ha E hE, ?_⟩⟩
    rw [stackCells_comp] at hE
    obtain ⟨E, hE, rfl⟩ := hE
    intro i x hx y hy
    simpa only [Fin.tail_cons, Fin.cons_zero] using
      D.lazardValuation_snoc_eq_of_mem_stackCells i hE hx hy
  exact ⟨𝓒, h𝓒, htail, fun E hE ↦ (hP E hE).1, fun i E hE ↦ (hP E hE).2 i⟩

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
    h𝓓.exists_isCAD_lazardValuation_eq_of_lazardDelineation_reindex (Equiv.refl _) hanalytic
      (by simpa using hD)
  have hv' (k) (E) (hE : E ∈ 𝓒) (x) (hx : x ∈ E) (y) (hy : y ∈ E) :
      (rename (finRotate (n + 1)) (F k)).lazardValuationReindex (finRotate (n + 1)).symm x =
        (rename (finRotate (n + 1)) (F k)).lazardValuationReindex
          (finRotate (n + 1)).symm y := by
    simpa only [lazardValuationReindex_finRotate_symm, rename_rename, Equiv.symm_comp_self,
      rename_id_apply, Equiv.coe_refl, Function.comp_id] using hv k E hE x hx y hy
  exact ⟨𝓒, h𝓒, htail, ha, hv', fun k E hE ↦
    (h𝓒.isConnected hE).isPreconnected.signInvariant_eval_of_lazardValuationReindex_eq
      (hv' k E hE)⟩

end TauCeti
