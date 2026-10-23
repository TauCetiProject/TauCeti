/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fin.Tuple.Basic
public import TauCeti.Geometry.RealAlgebraic.CAD.Lazard.Basic
public import TauCeti.Geometry.RealAlgebraic.Projection.Lazard.Lifting

/-!
# Cylindrical algebraic decomposition by recursive Lazard projection

Every finite family of real polynomials in `n` variables has a cylindrical algebraic
decomposition of `ℝ ^ n` into analytic submanifolds on each cell of which every member has
constant Lazard valuation, and hence constant sign. No well-orientedness or nonnullification
hypothesis is needed: this is the validity of Lazard's projection-and-lifting method.

In the ambient convention of `TauCeti.IsCAD`, coordinate zero is the coordinate added by the
last lifting step and `Fin.tail` projects to the base. The coordinate added first is therefore
coordinate `n - 1`. The Lazard valuation is taken in the order in which Lazard evaluation
treats the coordinates during the recursion, from the coordinate added first to the one added
last: this is the reversed coordinate order `Fin.revPerm`, in which coordinate `n - 1` is the
most significant. Lazard valuation is not invariant under permutations of the coordinates, so
this order is part of the statement.

The construction is the recursion of McCallum–Parusiński–Paunescu. A family in `n + 1`
variables is rewritten with its coordinates reversed and its new coordinate as distinguished
variable, and an irreducible basis of the result is chosen. The recursion is applied to its
Lazard projection with the base coordinates reversed back. On each base cell, read with its
coordinates reversed, the Lazard projection is then valuation-invariant in the native order, so
the Lazard lifting theorem gives a Lazard delineation of the family over the reordered cell.
Pulling these delineations back to the original base cells gives the lifted decomposition.
Sign-invariance follows from valuation-invariance on the connected cells.

## Main results

* `TauCeti.exists_isCAD_lazardValuationReindex_eq`: every finite family has an analytic
  cylindrical algebraic decomposition on whose cells each member is Lazard valuation-invariant
  in the reversed coordinate order and sign-invariant.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5 and Theorem 5.1.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {n : ℕ}

/-- **Validity of Lazard's projection.** Every finite family of real polynomials in `n`
variables has a cylindrical algebraic decomposition of `ℝ ^ n` into analytic submanifolds on
each cell of which every member has constant Lazard valuation, when the coordinates are read in
reverse order, from the coordinate added first by the cylindrical structure to the one added
last. Every member is also sign-invariant on each cell. No well-orientedness hypothesis is
imposed, and members may be nullified over base cells of positive dimension. The normalized
gcd needed by the Lazard projection is chosen in the proof, so there is no
`NormalizedGCDMonoid` hypothesis. -/
theorem exists_isCAD_lazardValuationReindex_eq (F : Finset (MvPolynomial (Fin n) ℝ)) :
    ∃ 𝓒, IsCAD n 𝓒 ∧ (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      (∀ f ∈ F, ∀ E ∈ 𝓒, ∀ x ∈ E, ∀ y ∈ E,
        f.lazardValuationReindex Fin.revPerm x = f.lazardValuationReindex Fin.revPerm y) ∧
      ∀ f ∈ F, ∀ E ∈ 𝓒, SignInvariant (fun x ↦ eval x f) E := by
  -- Sign-invariance follows from valuation-invariance on the connected cells.
  suffices h : ∃ 𝓒, IsCAD n 𝓒 ∧ (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      ∀ f ∈ F, ∀ E ∈ 𝓒, ∀ x ∈ E, ∀ y ∈ E,
        f.lazardValuationReindex Fin.revPerm x = f.lazardValuationReindex Fin.revPerm y by
    obtain ⟨𝓒, h𝓒, ha, hv⟩ := h
    exact ⟨𝓒, h𝓒, ha, hv, fun f hf E hE ↦
      (h𝓒.isConnected hE).isPreconnected.signInvariant_eval_of_lazardValuationReindex_eq
        (hv f hf E hE)⟩
  induction n with
  | zero =>
    refine ⟨{univ}, .zero, fun E hE ↦ ⟨0, ?_⟩, fun f _ E _ x _ y _ ↦ by rw [Subsingleton.elim x y]⟩
    rw [mem_singleton_iff.1 hE, univ_unique]
    exact isAnalyticSubmanifold_singleton _
  | succ n ih =>
    classical
    -- The Lazard projection needs a normalized gcd; any choice works.
    let _ : NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ) := Classical.arbitrary _
    -- Reverse the coordinates and make the last one, formerly coordinate zero, distinguished.
    let Φ : MvPolynomial (Fin (n + 1)) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin n) ℝ) :=
      ((renameEquiv ℝ Fin.revPerm).trans (renameEquiv ℝ finSuccEquivLast)).trans
        (optionEquivLeft ℝ (Fin n))
    let A := F.image Φ
    obtain ⟨B, hB⟩ := A.exists_isIrreducibleBasis
    obtain ⟨𝓓, h𝓓, ha, hv⟩ := ih ((A.lazardProjection B).image (rename Fin.revPerm.symm))
    -- Read in reverse, each base cell carries a valuation-invariant Lazard projection.
    have hproj (q) (hq : q ∈ A.lazardProjection B) (C) (hC : C ∈ 𝓓)
        (x) (hx : x ∘ Fin.revPerm ∈ C) (y) (hy : y ∘ Fin.revPerm ∈ C) :
        q.lazardValuation x = q.lazardValuation y := by
      simpa only [lazardValuationReindex_rename_symm, Function.comp_assoc, Equiv.self_comp_symm,
        Function.comp_id] using hv _ (Finset.mem_image_of_mem _ hq) C hC _ hx _ hy
    have hD (C) (hC : C ∈ 𝓓) : Nonempty (LazardDelineation
        (fun f : A ↦ rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm f.1))
        ((fun x ↦ x ∘ Fin.revPerm.symm.symm) ⁻¹' C)) := by
      obtain ⟨d, hd⟩ := ha C hC
      -- Permuting coordinates is a homeomorphism, so the reordered cell stays preconnected.
      exact nonempty_lazardDelineation_of_lazardProjection hB (hd.preimage_comp_equiv _)
        ((Homeomorph.piCongrLeft _).symm.isPreconnected_preimage.2
          (h𝓓.isConnected hC).isPreconnected) fun q hq ↦ hproj q hq C hC
    obtain ⟨𝓒, h𝓒, -, h𝓒a, h𝓒v⟩ :=
      h𝓓.exists_isCAD_lazardValuation_eq_of_lazardDelineation_reindex Fin.revPerm.symm ha hD
    -- Undoing the presentation, the delineated members are the members with reversed coordinates.
    have hG (f : MvPolynomial (Fin (n + 1)) ℝ) :
        rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm (Φ f)) =
          rename Fin.revPerm f := by
      simp only [Φ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, renameEquiv_apply]
      rw [rename_rename, Equiv.symm_comp_self, rename_id_apply]
    -- Moving coordinate zero to the end of the reversed base is reversing all coordinates.
    have hsnoc (x : Fin (n + 1) → ℝ) :
        Fin.snoc (Fin.tail x ∘ Fin.revPerm.symm) (x 0) = x ∘ Fin.revPerm.symm :=
      Fin.snoc_tail_comp_rev x
    refine ⟨𝓒, h𝓒, h𝓒a, fun f hf E hE x hx y hy ↦ ?_⟩
    have h := h𝓒v ⟨Φ f, Finset.mem_image_of_mem _ hf⟩ E hE x hx y hy
    rw [hG, hsnoc, hsnoc] at h
    rwa [lazardValuationReindex_def, lazardValuationReindex_def]

end TauCeti
