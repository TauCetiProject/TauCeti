/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Restriction
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.ClosedMap

/-!
# Closedness of edgewise realization maps

A continuous map from an edgewise subdivision to the original weak polyhedron, with the
canonical barycentric formula, is closed. Neither injectivity nor surjectivity is needed.
Consequently establishing bijectivity suffices to identify the weak polyhedra homeomorphically.

The essential point is that over each original closed simplex only finitely many subdivision
vertices can occur: nonnegative barycentric coordinates prevent cancellation, so every entry of
every tuple in the support must be an original vertex of that simplex. The inverse image is
therefore a closed subset of a compact finite vertex restriction.

## References

* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
* H. Edelsbrunner, D. R. Grayson, *Edgewise subdivision of a simplex*, Discrete Comput. Geom. 24
  (2000), 707–719.
-/

public noncomputable section

open Set Finset AbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] {K : AbstractSimplicialComplex ι} {k : ℕ}
  {f : Realization (K.toPreAbstractSimplicialComplex.edgewiseSubdivision k) → Realization K}

/-- In the canonical edgewise barycentric formula, every tuple in the source support has all
its entries in the target support. This uses nonnegativity, not injectivity of the map. -/
theorem edgewiseVertex_entries_mem_support_of_formula
    (hformula : ∀ x, (f x).1 = Finsupp.linearCombination ℝ
      (fun u : K.toPreAbstractSimplicialComplex.EdgewiseVertex k => TauCeti.edgewisePoint u.1) x.1)
    (x : Realization (K.toPreAbstractSimplicialComplex.edgewiseSubdivision k))
    {u : K.toPreAbstractSimplicialComplex.EdgewiseVertex k} (hu : u ∈ x.1.support)
    (l : Fin k) : u.1 l ∈ (f x).1.support := by
  have hxpos : 0 < x.1 u := lt_of_le_of_ne
    (Realization.nonneg _ x u) (Ne.symm (Finsupp.mem_support_iff.mp hu))
  have hnonneg (w : K.toPreAbstractSimplicialComplex.EdgewiseVertex k) (i : ι) :
      0 ≤ TauCeti.edgewisePoint w.1 i := by
    rw [TauCeti.edgewisePoint_apply]
    positivity
  have hupos : 0 < TauCeti.edgewisePoint u.1 (u.1 l) :=
    lt_of_le_of_ne (hnonneg u _) (Ne.symm (Finsupp.mem_support_iff.mp
      (TauCeti.support_edgewisePoint u.1 ▸ Finset.mem_image.mpr ⟨l, mem_univ l, rfl⟩)))
  apply Finsupp.mem_support_iff.mpr
  apply ne_of_gt
  rw [hformula, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  exact (mul_pos hxpos hupos).trans_le
    (Finset.single_le_sum (fun w _ => mul_nonneg (Realization.nonneg _ x w)
      (hnonneg w _)) hu)

/-- A continuous map with the canonical edgewise barycentric formula is closed for the weak
realization topologies, including for infinite complexes. -/
theorem isClosedMap_of_edgewisePoint_formula (hf : Continuous f)
    (hformula : ∀ x, (f x).1 = Finsupp.linearCombination ℝ
      (fun u : K.toPreAbstractSimplicialComplex.EdgewiseVertex k =>
        TauCeti.edgewisePoint u.1) x.1) :
    IsClosedMap f := by
  apply isClosedMap_of_isCompact_preimage_faceInclusion hf
  intro σ
  have hclosed : IsClosed (f ⁻¹' range (faceInclusion K σ)) :=
    (isCompact_range (continuous_faceInclusion K σ)).isClosed.preimage hf
  have hc := (K.toPreAbstractSimplicialComplex.edgewiseSubdivision k).isCompact_setOf_support_subset
    _ (K.toPreAbstractSimplicialComplex.finite_edgewiseVertex_entries_subset k σ.1)
  apply hc.of_isClosed_subset hclosed
  rintro x ⟨y, hy⟩ u hu l
  have hmem := edgewiseVertex_entries_mem_support_of_formula hformula x hu l
  rw [← hy, faceInclusion_val] at hmem
  exact StandardSimplex.support_subset y hmem

end AbstractSimplicialComplex
