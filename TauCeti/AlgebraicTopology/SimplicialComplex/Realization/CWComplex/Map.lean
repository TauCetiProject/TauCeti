/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Skeleton
public import TauCeti.Topology.CWComplex.Classical.Map

/-!
# Simplicial realizations are cellular

The CW filtration of a weak simplicial realization agrees with its simplicial filtration:
`skeletonLT n` consists of points with at most `n` nonzero barycentric coordinates, and the
ordinary `n`-skeleton is the image of the realization of the simplicial `n`-skeleton.
Consequently every simplicial map induces a cellular map, including maps that identify vertices
and collapse dimensions. This supplies the cellularity hypothesis needed to apply cellular
chains to simplicial realizations.

The CW structures are the existing `AbstractSimplicialComplex.realizationCWComplex` structures.
The induced map is the existing `SimplicialMap.realizationMap`, restricted to the universal
subsets as required by `TauCeti.IsCellular`; no second realization map is introduced.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and Section 2.2 (simplicial CW structures
  and cellular maps).
-/

public noncomputable section

open Set Topology

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] (K : AbstractSimplicialComplex ι)

/-- Stage `n` of the CW filtration consists exactly of points with at most `n` nonzero
barycentric coordinates. Stage zero is empty and stage infinity is the whole realization. -/
@[simp]
theorem skeletonLT_realizationCWComplex (n : ℕ∞) :
    letI := realizationCWComplex K
    (RelCWComplex.skeletonLT (univ : Set (Realization K)) n : Set (Realization K)) =
      {x | (x.1.support.card : ℕ∞) ≤ n} := by
  let := realizationCWComplex K
  induction n using ENat.recTopCoe with
  | top => simp
  | coe n =>
    ext x
    simp only [SetLike.mem_coe, mem_ofPred_eq, ENat.natCast_le_natCast]
    rw [CWComplex.mem_skeletonLT_iff]
    constructor
    · rintro ⟨m, hmn, c, hxc⟩
      let d := realizationCellEquiv K m c
      have hx : x.1.support = d.1.1 := by
        rw [← (realizationCellEquiv K m).symm_apply_apply c,
          openCell_realizationCellEquiv_symm] at hxc
        exact hxc
      have hm : m < n := by exact_mod_cast hmn
      rw [hx, d.2]
      omega
    · intro hx
      have hpos : 0 < x.1.support.card :=
        Finset.card_pos.mpr (K.isRelLowerSet_faces.prop_of_mem (support_mem K x))
      let m := x.1.support.card - 1
      let d : RealizationCell K m :=
        ⟨⟨x.1.support, support_mem K x⟩, by dsimp [m]; omega⟩
      refine ⟨m, ?_, (realizationCellEquiv K m).symm d, ?_⟩
      · have hm : m < n := by dsimp [m]; omega
        exact_mod_cast hm
      · rw [openCell_realizationCellEquiv_symm]
        rfl

/-- The ordinary CW `n`-skeleton is the realized simplicial `n`-skeleton, with its existing
subspace inclusion into the weak realization. -/
theorem skeleton_realizationCWComplex (n : ℕ) :
    letI := realizationCWComplex K
    (RelCWComplex.skeleton (univ : Set (Realization K)) n : Set (Realization K)) =
      range (realizationMap (K.skeleton_le n)) := by
  rw [RelCWComplex.skeleton, ← Nat.cast_one, ← Nat.cast_add]
  simp only [skeletonLT_realizationCWComplex, ENat.natCast_le_natCast,
    range_realizationMap_skeleton]

end AbstractSimplicialComplex

namespace PreAbstractSimplicialComplex.SimplicialMap

open AbstractSimplicialComplex

section Filtration

variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}

/-- A simplicial realization preserves every stage of the classical CW filtration.
No injectivity assumption on the vertex map is needed. -/
theorem mapsTo_realizationMap_skeletonLT
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex)
    (n : ℕ∞) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    MapsTo f.realizationMap
      (RelCWComplex.skeletonLT (univ : Set (Realization K)) n)
      (RelCWComplex.skeletonLT (univ : Set (Realization L)) n) := by
  simp only [skeletonLT_realizationCWComplex]
  intro x hx
  exact (ENat.natCast_le_natCast.mpr (f.card_support_realizationMap_le x)).trans hx

end Filtration

universe u

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  {K : AbstractSimplicialComplex ι} {L : AbstractSimplicialComplex κ}

/-- Every simplicial map induces a cellular map for the canonical simplicial CW structures.
The universal-subset restriction is the map used by the cellular-chain functor. The common
universe is required by the existing `TauCeti.IsCellular` interface. -/
theorem isCellular_realizationMap
    (f : SimplicialMap K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex) :
    letI := realizationCWComplex K
    letI := realizationCWComplex L
    TauCeti.IsCellular (univ : Set (Realization K)) (univ : Set (Realization L))
      (TopCat.ofHom (f.realizationMap.restrictPreimage univ)) := by
  intro n x hx
  exact f.mapsTo_realizationMap_skeletonLT n hx

end PreAbstractSimplicialComplex.SimplicialMap
