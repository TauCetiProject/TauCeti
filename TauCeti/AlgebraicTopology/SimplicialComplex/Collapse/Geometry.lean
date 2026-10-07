/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Precomplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
public import TauCeti.Geometry.Convex.ConvexSpace.SimplexHorn
import Mathlib.Data.Finset.Grade

/-!
# The geometric deformation of a free-pair simplex

Deleting a facet `σ` of a simplex `τ` retains a horn: the union of the facets of `τ`
other than `σ`. In barycentric coordinates this is the locus where some coordinate of
`σ` vanishes. The simplex strongly deformation retracts onto this retained part, fixing
it at every time. For a free pair in a complex, this is the local deformation that can
be extended by the identity on the other simplices to realize an elementary collapse.

The retained part is identified with the actual polyhedron of `deletion K σ`, rather than
with a complex obtained by adding singletons. Thus deleting a free vertex is included.
Only a nonempty facet and its upper face are needed for the local result; freeness is
needed when extending it to the whole complex.

The deformation transports `Convexity.StdSimplex.hornDeformationRetraction` through
`Finset.standardSimplexHomeomorph`, reusing the existing barycentric horn retraction.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapter 3 (elementary collapse and its geometric deformation).
-/

public noncomputable section

open Set AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : PreAbstractSimplicialComplex ι}
  {σ τ : Finset ι}

/-- A simplex point belongs to the polyhedron obtained by deleting a face exactly when
its support is a face of the original precomplex and a coordinate at a vertex of the deleted
face vanishes.
No assumption on the containing simplex is needed. -/
theorem mem_deletion_space_iff (K : PreAbstractSimplicialComplex ι)
    (x : StandardSimplex τ) :
    x.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (deletion K σ)).space ↔
      x.1.support ∈ K ∧ ∃ v ∈ σ, x.1 v = 0 := by
  rw [mem_onFinsupp_space_iff, mem_deletion]
  simp only [Finset.subset_iff, not_forall, exists_prop,
    Finsupp.mem_support_iff, not_not]

/-- A simplex strongly deformation retracts onto its intersection with the polyhedron
obtained by deleting one of its nonempty facets. This is the local geometric realization of a
free-pair collapse, including the case where the deleted facet is a vertex. -/
theorem exists_strong_deformation_retraction_simplex_deletion (K : PreAbstractSimplicialComplex ι)
    (hτ : τ ∈ K) (hστ : σ ⋖ τ) (hσne : σ.Nonempty) :
    let S : Set (StandardSimplex τ) :=
      {x | x.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (deletion K σ)).space}
    ∃ r : C(StandardSimplex τ, S), (∀ x : S, r x = x) ∧ Nonempty
      ((ContinuousMap.id (StandardSimplex τ)).HomotopyRel
        ((ContinuousMap.subtypeVal S).comp r) S) := by
  classical
  obtain ⟨a, ha, hσ⟩ := hστ.exists_finset_erase
  let a' : τ := ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hσne
  have hba : b ≠ a := by
    rw [← hσ] at hb
    exact (Finset.mem_erase.mp hb).1
  have hbτ : b ∈ τ := hστ.le hb
  let : Nontrivial τ := ⟨⟨a', ⟨b, hbτ⟩, fun h => hba (congrArg Subtype.val h).symm⟩⟩
  let e := Finset.standardSimplexHomeomorph τ
  let S : Set (StandardSimplex τ) :=
    {x | x.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (deletion K σ)).space}
  -- The geometric part retained by deletion is exactly the non-apex-coordinate horn.
  have hS (x : StandardSimplex τ) : x ∈ S ↔ e x ∈ Convexity.StdSimplex.horn a' := by
    have hx : x.1.support ∈ K := K.isRelLowerSet_faces.mem_of_le hτ
      (StandardSimplex.support_subset x)
      (Finsupp.support_nonempty_iff.mpr fun hz => by
        have hsum := StandardSimplex.sum_eq_one x
        simp [hz] at hsum)
    simp only [S, mem_ofPred_eq]
    rw [mem_deletion_space_iff K, Convexity.StdSimplex.mem_horn_iff]
    simp only [hx, true_and, e, Finset.standardSimplexHomeomorph_weights]
    constructor
    · rintro ⟨v, hv, hxv⟩
      have hvτ : v ∈ τ := hστ.le hv
      refine ⟨⟨v, hvτ⟩, ?_, ?_⟩
      · intro h
        have hval := congrArg Subtype.val h
        rw [← hσ] at hv
        exact (Finset.mem_erase.mp hv).1 hval
      · exact hxv
    · rintro ⟨v, hv, hxv⟩
      refine ⟨v.1, ?_, hxv⟩
      rw [← hσ, Finset.mem_erase]
      exact ⟨fun h => hv (Subtype.ext h), v.2⟩
  -- Conjugate the bundled horn retraction and transport its relative homotopy.
  let eS := e.subtype hS
  let r := (eS.symm : C(Convexity.StdSimplex.horn a', S)).comp
    ((Convexity.StdSimplex.hornRetraction a').comp
      (e : C(StandardSimplex τ, Convexity.StdSimplex ℝ τ)))
  have hr (x : S) : r x = x := by
    have h := Convexity.StdSimplex.hornRetraction_apply_coe a' (eS x)
    simpa only [r, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
      eS, Homeomorph.subtype_apply_coe, Homeomorph.symm_apply_apply] using congrArg eS.symm h
  let H := (Convexity.StdSimplex.hornDeformationRetraction a').compContinuousMap
    (e.symm : C(Convexity.StdSimplex ℝ τ, StandardSimplex τ))
  refine ⟨r, hr, ⟨?_⟩⟩
  refine
    { toHomotopy := (H.toHomotopy.compContinuousMap
        (e : C(StandardSimplex τ, Convexity.StdSimplex ℝ τ))).cast ?_ ?_
      prop' := ?_ }
  · simpa only [ContinuousMap.comp_id] using e.symm_comp_toContinuousMap
  · ext x
    rfl
  · intro t x hx
    -- The relative-homotopy field uses `toFun`, so the application simp lemmas do not match.
    -- Express the cast and precomposition as an application of the transported homotopy.
    change H (t, e x) = x
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_coe,
      ContinuousMap.id_apply, Homeomorph.symm_apply_apply] using H.eq_fst t ((hS x).mp hx)

end PreAbstractSimplicialComplex
