/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Realization
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Stellar.Equivalence
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finite stellar subdivisions preserve the weak polyhedron

Placing a new vertex at the barycenter of the starred face gives a homeomorphism from the
polyhedron of a finite stellar subdivision to the original polyhedron. Consequently a finite
sequence of stellar moves and inverse moves preserves the homeomorphism type of a finite
polyhedron. These identifications provide the topological part of the local sphere and ball
models used in triangulated manifolds; piecewise-linear regularity is a separate assertion.

A precomplex can omit vertices, so its polyhedron is the subset of an ambient weak realization
whose supports are its faces. The single-move theorem allows any ambient complex containing
both precomplexes. The sequence theorem uses the full complex as a common ambient space.
Finiteness means finitely many faces, with no restriction on the ambient vertex type.

The construction uses the bijective barycentric map of `Stellar.Realization` and the compact
subpolyhedron and coordinate-embedding theorems of `Realization.Finite`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapter 2 (starrings and stellar equivalence).
-/

public section

noncomputable section

open Set Topology AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K L : PreAbstractSimplicialComplex ι}
  {A : AbstractSimplicialComplex ι} {σ : Finset ι} {v : ι}

/-- The barycentric identification of a finite stellar subdivision is a homeomorphism for
the weak subpolyhedron topologies. The new vertex goes to the barycenter of `σ` and the old
vertices are fixed, as specified by the underlying linear map. -/
theorem exists_stellarSubdivision_homeomorph (hσ : σ ∈ K) (hv : ({v} : Finset ι) ∉ K)
    (hfin : K.faces.Finite) (hK : K ≤ A.toPreAbstractSimplicialComplex)
    (hS : stellarSubdivision K σ v ≤ A.toPreAbstractSimplicialComplex) :
    ∃ e : {x : Realization A // x.1.support ∈ stellarSubdivision K σ v} ≃ₜ
        {x : Realization A // x.1.support ∈ K},
      ∀ x, (e x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1 := by
  classical
  let S := {x : Realization A | x.1.support ∈ stellarSubdivision K σ v}
  let T := {x : Realization A | x.1.support ∈ K}
  have hcompactS : IsCompact S := A.isCompact_setOf_support_mem hS
    (finite_faces_stellarSubdivision hfin)
  have hcompactT : IsCompact T := A.isCompact_setOf_support_mem hK hfin
  let : CompactSpace S := isCompact_iff_compactSpace.mp hcompactS
  have hsource (x : S) :
      x.1.1 ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ)
        (stellarSubdivision K σ v)).space :=
    Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
      ⟨Realization.nonneg A x.1, Realization.sum_eq_one A x.1, x.2⟩
  -- Convert normalized coordinates in either precomplex into the containing realization.
  have hmem (P : PreAbstractSimplicialComplex ι) (hP : P ≤ A.toPreAbstractSimplicialComplex)
      (y : ι →₀ ℝ) (hy : y ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) P).space) :
      y ∈ (standardGeometricComplex A).space ∧ y.support ∈ P := by
    obtain ⟨hypos, hysum, hyface⟩ := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mp hy
    refine ⟨mem_realization_iff.mpr ⟨y.support, hP hyface, ?_⟩, hyface⟩
    simpa only [Finset.coe_image] using mem_standardSimplex_iff.mpr
      ⟨hypos, hysum, Finset.Subset.refl _⟩
  have hb := bijOn_stellarSubdivisionLinearMap hσ hv
  let f : S → T := fun x =>
    ⟨⟨Finset.stellarSubdivisionLinearMap σ v x.1.1,
      (hmem K hK _ (hb.mapsTo (hsource x))).1⟩,
      (hmem K hK _ (hb.mapsTo (hsource x))).2⟩
  have hfval (x : S) : (f x).1.1 = Finset.stellarSubdivisionLinearMap σ v x.1.1 :=
    rfl
  -- Restrict the existing point-set bijection to these two subpolyhedra.
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply hb.injOn (hsource x) (hsource y)
      simpa only [hfval] using congrArg (fun z : T => z.1.1) hxy
    · intro y
      have hy := Geometry.SimplicialComplex.mem_space_onFinsupp_iff.mpr
        ⟨Realization.nonneg A y.1, Realization.sum_eq_one A y.1, y.2⟩
      obtain ⟨x, hx, hxy⟩ := hb.surjOn hy
      obtain ⟨hxA, hxface⟩ := hmem _ hS x hx
      refine ⟨⟨⟨x, hxA⟩, hxface⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (hfval _).trans hxy
  -- Compact subpolyhedra carry their coordinate topology. Every output coordinate is an
  -- affine expression in two input coordinates, so the restricted barycentric map is continuous.
  have hc : Continuous f := by
    apply (A.isClosedEmbedding_realization_coe_restrict hcompactT).isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro i
    have hcoord (j : ι) : Continuous (fun x : S => x.1.1 j) :=
      ((continuous_apply j).comp (continuous_realization_coe A)).comp continuous_subtype_val
    simp only [Function.comp_def, hfval, Finset.stellarSubdivisionLinearMap_apply]
    exact (hcoord i).add ((hcoord v).mul continuous_const)
  let e := (Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed hc hc.isClosedMap
  exact ⟨e, hfval⟩

/-- Stellar equivalent finite precomplexes have homeomorphic weak polyhedra. The subtypes
exclude every unused vertex, even though their common ambient complex contains all vertices. -/
theorem StellarEquivalent.nonempty_homeomorph (h : StellarEquivalent K L)
    (hfin : K.faces.Finite) :
    Nonempty ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ K} ≃ₜ
      {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ L}) := by
  have hle (P : PreAbstractSimplicialComplex ι) :
      P ≤ (⊤ : AbstractSimplicialComplex ι).toPreAbstractSimplicialComplex :=
    fun _ hτ => TauCeti.AbstractSimplicialComplex.mem_top_iff.mpr
      (P.isRelLowerSet_faces.prop_of_mem hτ)
  -- Carry finiteness along the moves as well as the homeomorphisms, so that inverse
  -- moves and intermediate complexes meet the compactness hypothesis.
  suffices hp : (K.faces.Finite ↔ L.faces.Finite) ∧
      (K.faces.Finite → Nonempty
        ({x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ K} ≃ₜ
          {x : Realization (⊤ : AbstractSimplicialComplex ι) // x.1.support ∈ L})) from
    hp.2 hfin
  apply h.induction_on
  · intro P Q h
    refine ⟨h.finite_faces_iff, fun hP => ?_⟩
    obtain ⟨σ, v, hσ, hv, rfl⟩ := isStellarMove_iff.mp h
    obtain ⟨e, -⟩ := exists_stellarSubdivision_homeomorph hσ hv hP (hle P) (hle _)
    exact ⟨e.symm⟩
  · intro P
    exact ⟨Iff.rfl, fun _ => ⟨Homeomorph.refl _⟩⟩
  · intro P Q ih
    exact ⟨ih.1.symm, fun hQ => (ih.2 (ih.1.mpr hQ)).map Homeomorph.symm⟩
  · intro P Q R ihPQ ihQR
    refine ⟨ihPQ.1.trans ihQR.1, fun hP => ?_⟩
    obtain ⟨e⟩ := ihPQ.2 hP
    obtain ⟨e'⟩ := ihQR.2 (ihPQ.1.mp hP)
    exact ⟨e.trans e'⟩

end PreAbstractSimplicialComplex
