/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.NDRPair
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Neighborhood

/-!
# Subcomplexes are NDR pairs

Let `P` be a subcomplex of an abstract simplicial complex `K`, or more generally any precomplex
of finite sets of vertices. Its polyhedron `{y | y.support ∈ P}` in the weak realization of `K` is
an NDR pair, and hence has the homotopy extension property: the inclusion of a subcomplex is a
closed cofibration.

The polyhedron of `P` need not be the polyhedron of a full subcomplex, but it becomes one after a
barycentric subdivision (`preimage_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem`).
The control function `openSimplicialNeighborhoodControl K P` is therefore the open star control
function of the subdivision, `openStarControl`, for the face-vertices that are faces of `P`,
transported along the subdivision homeomorphism. It vanishes exactly on the polyhedron of `P`, and
is less than one exactly on the open simplicial neighbourhood of `P`. Together with the
deformation `AbstractSimplicialComplex.openSimplicialNeighborhoodDeformation` of that
neighbourhood, `TauCeti.NDRPair.ofHomotopyRel` turns it into NDR data. No finiteness or local
finiteness is assumed.

## Main definitions

* `AbstractSimplicialComplex.openSimplicialNeighborhoodControl`: the control function of the open
  simplicial neighbourhood of `P`.
* `AbstractSimplicialComplex.subcomplexNDRPair`: NDR data for the polyhedron of `P`.

## Main results

* `AbstractSimplicialComplex.hasHomotopyExtensionProperty_setOf_support_mem`: the polyhedron of
  a subcomplex has the homotopy extension property in the realization.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3 (derived neighbourhoods; every subcomplex is full in a derived subdivision).
* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152 (NDR pairs).
-/

public section

noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι) (P : PreAbstractSimplicialComplex ι)

/-- The control function of the open simplicial neighbourhood of `P`: the open star control
function, in the barycentric subdivision, of the face-vertices that are faces of `P`, transported
along the subdivision homeomorphism. -/
def openSimplicialNeighborhoodControl : C(Realization K, unitInterval) :=
  ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
    K.toPreAbstractSimplicialComplex).openStarControl {σ : Face K | σ.1 ∈ P}).comp
      ((barycentricSubdivisionRealizationHomeomorph K).symm : C(_, _))

theorem openSimplicialNeighborhoodControl_apply (y : Realization K) :
    K.openSimplicialNeighborhoodControl P y =
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openStarControl {σ : Face K | σ.1 ∈ P}
          ((barycentricSubdivisionRealizationHomeomorph K).symm y) :=
  (rfl)

/-- The control function of the open simplicial neighbourhood of `P` vanishes exactly on the
polyhedron of `P`. -/
theorem openSimplicialNeighborhoodControl_eq_zero_iff {y : Realization K} :
    K.openSimplicialNeighborhoodControl P y = 0 ↔ y.1.support ∈ P := by
  have h := Set.ext_iff.1 (preimage_barycentricSubdivisionRealizationHomeomorph_setOf_support_mem
    K P) ((barycentricSubdivisionRealizationHomeomorph K).symm y)
  rw [mem_preimage, Homeomorph.apply_symm_apply] at h
  rw [openSimplicialNeighborhoodControl_apply, openStarControl_eq_zero_iff]
  exact h.symm

/-- The control function of the open simplicial neighbourhood of `P` is less than one exactly on
that neighbourhood. -/
theorem openSimplicialNeighborhoodControl_lt_one_iff {y : Realization K} :
    K.openSimplicialNeighborhoodControl P y < 1 ↔ y ∈ K.openSimplicialNeighborhood P := by
  have h := Set.ext_iff.1
    (preimage_barycentricSubdivisionRealizationHomeomorph_openSimplicialNeighborhood K P)
      ((barycentricSubdivisionRealizationHomeomorph K).symm y)
  rw [mem_preimage, Homeomorph.apply_symm_apply] at h
  rw [openSimplicialNeighborhoodControl_apply, openStarControl_lt_one_iff]
  exact h.symm

/-- **The polyhedron of a subcomplex is an NDR pair.** The NDR data is obtained from the
deformation of the open simplicial neighbourhood of `P` onto the polyhedron of `P`, cut off by the
control function `openSimplicialNeighborhoodControl K P`. -/
def subcomplexNDRPair : TauCeti.NDRPair {y : Realization K | y.1.support ∈ P} :=
  .ofHomotopyRel (K.setOf_support_mem_subset_openSimplicialNeighborhood P)
    (K.openSimplicialNeighborhoodDeformation P) (K.openSimplicialNeighborhoodControl P)
    (fun _ => K.openSimplicialNeighborhoodControl_eq_zero_iff P)
    fun _ => (K.openSimplicialNeighborhoodControl_lt_one_iff P).1

theorem subcomplexNDRPair_def :
    K.subcomplexNDRPair P =
      .ofHomotopyRel (K.setOf_support_mem_subset_openSimplicialNeighborhood P)
        (K.openSimplicialNeighborhoodDeformation P) (K.openSimplicialNeighborhoodControl P)
        (fun _ => K.openSimplicialNeighborhoodControl_eq_zero_iff P)
        fun _ => (K.openSimplicialNeighborhoodControl_lt_one_iff P).1 :=
  (rfl)

/-- **The polyhedron of a subcomplex has the homotopy extension property** in the weak
realization: the inclusion of a subcomplex is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_setOf_support_mem :
    TauCeti.HasHomotopyExtensionProperty {y : Realization K | y.1.support ∈ P} :=
  (K.subcomplexNDRPair P).hasHomotopyExtensionProperty

end AbstractSimplicialComplex
