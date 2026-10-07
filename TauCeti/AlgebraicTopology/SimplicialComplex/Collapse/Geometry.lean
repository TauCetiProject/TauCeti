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

The deformation transports `Convexity.StdSimplex.hornDeformation` through
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

/-- Inside an upper face, deleting a lower face retains precisely the points with a zero
coordinate at some vertex of that lower face. -/
theorem mem_deletion_space_iff (K : PreAbstractSimplicialComplex ι) (hτ : τ ∈ K)
    (x : StandardSimplex τ) :
    x.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) (deletion K σ)).space ↔
      ∃ v ∈ σ, x.1 v = 0 := by
  rw [mem_onFinsupp_space_iff, mem_deletion]
  have hx : x.1.support ∈ K := K.isRelLowerSet_faces.mem_of_le hτ
    (StandardSimplex.support_subset x)
    (Finsupp.support_nonempty_iff.mpr fun hz => by
      have hsum := StandardSimplex.sum_eq_one x
      simp [hz] at hsum)
  simp only [hx, true_and, Finset.subset_iff, not_forall, exists_prop,
    Finsupp.mem_support_iff, not_not]

/-- A simplex strongly deformation retracts onto its intersection with the polyhedron
obtained by deleting one of its nonempty facets. This is the local geometric realization of a
free-pair collapse, including the case where the deleted facet is a vertex. -/
theorem exists_deformationRetraction_simplex_deletion (K : PreAbstractSimplicialComplex ι)
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
    simp only [S, mem_ofPred_eq]
    rw [mem_deletion_space_iff K hτ, Convexity.StdSimplex.mem_horn_iff]
    simp only [e, Finset.standardSimplexHomeomorph_weights]
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
  -- Transport the existing horn deformation, retaining its pointwise fixed-subset law.
  let d : unitInterval × StandardSimplex τ → StandardSimplex τ := fun p =>
    e.symm (Convexity.StdSimplex.hornDeformation a' p.1 (e p.2))
  have hd : Continuous d := e.symm.continuous.comp
    ((Convexity.StdSimplex.continuous_hornDeformation a').comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  have hd0 (x : StandardSimplex τ) : d (0, x) = x := by
    simp [d]
  have hdS (t : unitInterval) (x : StandardSimplex τ) (hx : x ∈ S) : d (t, x) = x := by
    simp [d, Convexity.StdSimplex.hornDeformation_of_mem ((hS x).mp hx)]
  have hd1 (x : StandardSimplex τ) : d (1, x) ∈ S := by
    apply (hS _).mpr
    simpa [d] using Convexity.StdSimplex.hornDeformation_one_mem a' (e x)
  let r : C(StandardSimplex τ, S) :=
    ⟨fun x => ⟨d (1, x), hd1 x⟩,
      (hd.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  refine ⟨r, fun x => Subtype.ext (hdS 1 x x.2), ⟨?_⟩⟩
  exact
    { toFun := d
      continuous_toFun := hd
      map_zero_left := hd0
      map_one_left := fun _ => rfl
      prop' := hdS }

end PreAbstractSimplicialComplex
