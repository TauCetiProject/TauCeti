/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.Lazard.Projection

/-!
# Cylindrical algebraic decomposition by recursive Lazard projection

Every finite family of real polynomials in `n` variables has a cylindrical algebraic
decomposition of `ℝ ^ n` into analytic submanifolds on whose cells every member has constant
Lazard valuation and constant sign (`TauCeti.exists_isCAD_lazardValuationReindex_revPerm_eq`).
No well-orientedness condition is needed: unlike McCallum's projection, Lazard's projection
also controls members whose ordinary fibers vanish identically over positive-dimensional cells.

The Lazard valuation depends on an order of the coordinates. A CAD of `ℝ ^ (n + 1)` is built
over a CAD of `ℝ ^ n` by adding coordinate `0`, so the coordinates of `ℝ ^ n` are added in the
order `n - 1, …, 1, 0`. Lazard's method reads the coordinates in the order in which they are
added, the first one being the most significant, so the valuation is taken in reversed coordinate
order, `MvPolynomial.lazardValuationReindex` along `Fin.revPerm`. In this order, reading the base
coordinates in their own reversed order and then the new coordinate `0` is reading all
coordinates in reversed order, which is what makes the recursion close up.

The recursive step,
`TauCeti.IsCAD.exists_isCAD_lazardValuationReindex_revPerm_eq_of_lazardProjection`,
singles out coordinate `0` of each member and reverses the remaining coordinates. An irreducible
basis of the resulting family has a Lazard projection, a finite family in `n` variables. Over a
base CAD on which that projection has constant Lazard valuation in reversed order, Lazard lifting
applies over each base cell with its coordinates reversed, and the delineations assemble into a
CAD by `TauCeti.IsCAD.exists_isCAD_lazardValuation_eq_of_lazardDelineation_comp`. Sign-invariance
follows from valuation-invariance on the connected cells.

## Main results

* `TauCeti.IsCAD.exists_isCAD_lazardValuationReindex_revPerm_eq_of_lazardProjection`: one level
  of Lazard projection and lifting in reversed coordinate order.
* `TauCeti.exists_isCAD_lazardValuationReindex_revPerm_eq`: **CAD by recursive Lazard projection**.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.3.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {n : ℕ}

/-- **One level of Lazard lifting in reversed coordinate order.** Single out coordinate zero of
each member of `F` and list the remaining coordinates in reverse order. Suppose an analytic CAD
of the base has, on each of its cells, constant Lazard valuation of the Lazard projection of an
irreducible basis of this family, with the base coordinates read in reverse order. Then it lifts
to an analytic CAD of `ℝ ^ (n + 1)` with the given base as projection, on whose cells every
member of `F` has constant Lazard valuation in reversed coordinate order and is sign-invariant.

Ordinary fibers may be nullified over positive-dimensional base cells. -/
theorem IsCAD.exists_isCAD_lazardValuationReindex_revPerm_eq_of_lazardProjection
    [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)] {F : Finset (MvPolynomial (Fin (n + 1)) ℝ)}
    {B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))} {𝓓 : Set (Set (Fin n → ℝ))}
    (h𝓓 : IsCAD n 𝓓) (hanalytic : ∀ C ∈ 𝓓, ∃ d, IsAnalyticSubmanifold d C)
    (hB : (F.map ((finSuccEquiv ℝ n).trans (Polynomial.mapAlgEquiv
      (renameEquiv ℝ Fin.revPerm))).toEquiv.toEmbedding).IsIrreducibleBasis B)
    (hproj : ∀ q ∈ (F.map ((finSuccEquiv ℝ n).trans (Polynomial.mapAlgEquiv
      (renameEquiv ℝ Fin.revPerm))).toEquiv.toEmbedding).lazardProjection B,
      ∀ C ∈ 𝓓, ∀ x ∈ C, ∀ y ∈ C,
        q.lazardValuation (x ∘ Fin.revPerm) = q.lazardValuation (y ∘ Fin.revPerm)) :
    ∃ 𝓒, IsCAD (n + 1) 𝓒 ∧ image Fin.tail '' 𝓒 = 𝓓 ∧
      (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      (∀ f ∈ F, ∀ E ∈ 𝓒, ∀ x ∈ E, ∀ y ∈ E,
        f.lazardValuationReindex Fin.revPerm x = f.lazardValuationReindex Fin.revPerm y) ∧
      ∀ f ∈ F, ∀ E ∈ 𝓒, SignInvariant (fun x ↦ eval x f) E := by
  classical
  let φ := (finSuccEquiv ℝ n).trans (Polynomial.mapAlgEquiv (renameEquiv ℝ Fin.revPerm))
  let A := F.map φ.toEquiv.toEmbedding
  let G : A → MvPolynomial (Fin (n + 1)) ℝ := fun b ↦
    rename finSuccEquivLast.symm ((optionEquivLeft ℝ (Fin n)).symm b.1)
  have hD (C : Set (Fin n → ℝ)) (hC : C ∈ 𝓓) :
      Nonempty (LazardDelineation G ((fun x ↦ x ∘ Fin.revPerm) ⁻¹' C)) := by
    obtain ⟨d, hd⟩ := hanalytic C hC
    have hrr : (⇑(Fin.revPerm (n := n))) ∘ ⇑Fin.revPerm = id := Fin.rev_involutive.comp_self
    have hinv : Function.Involutive fun x : Fin n → ℝ ↦ x ∘ Fin.revPerm := fun x ↦ by
      simp only [Function.comp_assoc, hrr, Function.comp_id]
    have hconn : IsPreconnected ((fun x ↦ x ∘ Fin.revPerm) ⁻¹' C) := by
      rw [← image_eq_preimage_of_inverse hinv.leftInverse hinv.rightInverse]
      exact (h𝓓.isConnected hC).isPreconnected.image _ (Pi.continuous_precomp _).continuousOn
    refine nonempty_lazardDelineation_of_lazardProjection hB (hd.preimage_comp_perm _) hconn
      fun q hq x hx y hy ↦ ?_
    simpa only [hinv x, hinv y] using hproj q hq C hC _ hx _ hy
  obtain ⟨𝓒, h𝓒, htail, ha, hv⟩ :=
    h𝓓.exists_isCAD_lazardValuation_eq_of_lazardDelineation_comp hanalytic Fin.revPerm hD
  have hval (f : MvPolynomial (Fin (n + 1)) ℝ) (hf : f ∈ F) {E} (hE : E ∈ 𝓒) {x} (hx : x ∈ E)
      {y} (hy : y ∈ E) :
      f.lazardValuationReindex Fin.revPerm x = f.lazardValuationReindex Fin.revPerm y := by
    -- Reading the base in reverse order and then the new coordinate reverses all coordinates.
    have hsnoc (z : Fin (n + 1) → ℝ) :
        Fin.snoc (Fin.tail z ∘ Fin.revPerm) (z 0) = z ∘ Fin.revPerm := by
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [Fin.tail, Fin.rev_castSucc]
    -- The lifted family member attached to `f` is `f` with all coordinates reversed.
    have h := hv ⟨φ f, Finset.mem_map_of_mem _ hf⟩ E hE x hx y hy
    simp only [G, φ, AlgEquiv.trans_apply,
      ← optionEquivLeft_rename_finSuccEquivLast_rename_revPerm, AlgEquiv.symm_apply_apply,
      rename_rename, ← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp,
      Fin.revPerm_symm, hsnoc] at h
    simpa only [lazardValuationReindex_def, Fin.revPerm_symm] using h
  exact ⟨𝓒, h𝓒, htail, ha, fun f hf E hE x hx y hy ↦ hval f hf hE hx hy,
    fun f hf E hE ↦
      (h𝓒.isConnected hE).isPreconnected.signInvariant_eval_of_lazardValuationReindex_eq
        fun x hx y hy ↦ hval f hf hE hx hy⟩

/-- **Cylindrical algebraic decomposition by recursive Lazard projection.** For every finite
family `F` of real polynomials in `n` variables there is a cylindrical algebraic decomposition of
`ℝ ^ n` into analytic submanifolds, on each cell of which every member of `F` has constant Lazard
valuation, with the coordinates read in reverse order, and is sign-invariant. No
well-orientedness condition is imposed. -/
theorem exists_isCAD_lazardValuationReindex_revPerm_eq (F : Finset (MvPolynomial (Fin n) ℝ)) :
    ∃ 𝓒, IsCAD n 𝓒 ∧ (∀ E ∈ 𝓒, ∃ d, IsAnalyticSubmanifold d E) ∧
      (∀ f ∈ F, ∀ E ∈ 𝓒, ∀ x ∈ E, ∀ y ∈ E,
        f.lazardValuationReindex Fin.revPerm x = f.lazardValuationReindex Fin.revPerm y) ∧
      ∀ f ∈ F, ∀ E ∈ 𝓒, SignInvariant (fun x ↦ eval x f) E := by
  induction n with
  | zero =>
    refine ⟨{univ}, .zero, fun E hE ↦ ⟨0, ?_⟩, fun f _ E _ x _ y _ ↦ by
      rw [Subsingleton.elim x y], fun f _ E _ ↦ subsingleton_of_subsingleton.signInvariant⟩
    rw [mem_singleton_iff.1 hE, univ_unique]
    exact isAnalyticSubmanifold_singleton _
  | succ n ih =>
    classical
    let _ : NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ) := Classical.arbitrary _
    let A := F.map ((finSuccEquiv ℝ n).trans
      (Polynomial.mapAlgEquiv (renameEquiv ℝ Fin.revPerm))).toEquiv.toEmbedding
    obtain ⟨B, hB⟩ := Finset.exists_isIrreducibleBasis A
    have hrr : (⇑(Fin.revPerm (n := n))) ∘ ⇑Fin.revPerm = id := Fin.rev_involutive.comp_self
    obtain ⟨𝓓, h𝓓, ha, hv, -⟩ := ih ((A.lazardProjection B).image (rename Fin.revPerm))
    obtain ⟨𝓒, h𝓒, -, h⟩ :=
      h𝓓.exists_isCAD_lazardValuationReindex_revPerm_eq_of_lazardProjection ha hB
        fun q hq C hC x hx y hy ↦ by
          simpa [lazardValuationReindex_def, rename_rename, hrr] using
            hv _ (Finset.mem_image_of_mem _ hq) C hC x hx y hy
    exact ⟨𝓒, h𝓒, h⟩

end TauCeti
