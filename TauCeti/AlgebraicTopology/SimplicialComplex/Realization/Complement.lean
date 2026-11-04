/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Neighborhood
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.HomotopyEquiv
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.CWComplex.EulerCharacteristic

/-!
# Finite CW models for complements of subcomplexes

The complement of a subcomplex in a weak simplicial realization is homotopy equivalent to the
full subcomplex of the barycentric subdivision on the faces not belonging to the removed
subcomplex. Indeed, every subcomplex is full in the subdivision, and its complement is the open
star of the remaining face-vertices. The normalized open-star retraction supplies the equivalence.
No finiteness or local finiteness is needed for this construction.

When the original complex has finitely many faces, this gives a genuine Hausdorff finite CW
model for the complement, not merely finite domination. In particular it applies to deleting
marked vertices, by taking the removed subcomplex to consist of their singleton faces.
This is useful when passing from a triangulated compact manifold to its punctured complement.

We reuse `support_barycentricSubdivisionRealizationMap_mem_iff` to identify the removed
polyhedron and `openStarHomotopyEquiv` for its complement's retraction.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 3 (derived subdivisions and complements of subpolyhedra).
-/

public noncomputable section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*} (K : AbstractSimplicialComplex ι) (P : PreAbstractSimplicialComplex ι)

attribute [local instance] Classical.decEq

/-- In the barycentric subdivision, the complement of a subcomplex is the open star of the
face-vertices not belonging to that subcomplex. The precomplex need not contain every ambient
vertex or be contained in `K`: only its faces in `K` affect either side. -/
theorem preimage_barycentricSubdivisionRealizationHomeomorph_compl :
    barycentricSubdivisionRealizationHomeomorph K ⁻¹'
        {y : Realization K | y.1.support ∉ P} =
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∉ P} := by
  calc
    _ = {x | ¬ (x.1.support : Set (Face K)) ⊆ {σ | σ.1 ∈ P}} := by
      ext x
      simp only [mem_preimage, mem_ofPred_eq,
        barycentricSubdivisionRealizationHomeomorph_apply,
        support_barycentricSubdivisionRealizationMap_mem_iff]
    _ = _ := ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarRealizationSet_compl {σ : Face K | σ.1 ∈ P}).symm

/-- The subdivision homeomorphism restricts to a homeomorphism from the open star of the
remaining face-vertices onto the complement of the removed polyhedron. -/
def complementSubdivisionHomeomorph :
    (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∉ P} ≃ₜ
      {y : Realization K | y.1.support ∉ P} :=
  (barycentricSubdivisionRealizationHomeomorph K).sets
    (K.preimage_barycentricSubdivisionRealizationHomeomorph_compl P).symm

/-- The restricted homeomorphism is the canonical subdivision map on underlying points. -/
@[simp]
theorem coe_complementSubdivisionHomeomorph_apply
    (x : (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarRealizationSet {σ : Face K | σ.1 ∉ P}) :
    (K.complementSubdivisionHomeomorph P x : Realization K) =
      barycentricSubdivisionRealizationMap K x := by
  simp [complementSubdivisionHomeomorph]

/-- The inverse restricted homeomorphism is the inverse subdivision map on underlying points. -/
@[simp]
theorem coe_complementSubdivisionHomeomorph_symm_apply
    (y : {y : Realization K | y.1.support ∉ P}) :
    ((K.complementSubdivisionHomeomorph P).symm y :
      Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex)) =
      (barycentricSubdivisionRealizationHomeomorph K).symm y := by
  simp [complementSubdivisionHomeomorph]

/-- The complement of a subcomplex has the homotopy type of the full subcomplex of the
barycentric subdivision spanned by the faces not in the removed subcomplex. -/
def complementHomotopyEquiv :
    ContinuousMap.HomotopyEquiv {y : Realization K | y.1.support ∉ P}
      (Realization ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).restrict {σ : Face K | σ.1 ∉ P})) :=
  (K.complementSubdivisionHomeomorph P).symm.toHomotopyEquiv.trans
    ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).openStarHomotopyEquiv {σ : Face K | σ.1 ∉ P})

/-- The forward map first passes to subdivision coordinates and then retracts the open star. -/
@[simp]
theorem complementHomotopyEquiv_apply (y : {y : Realization K | y.1.support ∉ P}) :
    K.complementHomotopyEquiv P y =
      (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
        K.toPreAbstractSimplicialComplex).openStarHomotopyEquiv {σ : Face K | σ.1 ∉ P}
          ((K.complementSubdivisionHomeomorph P).symm y) :=
  (rfl)

/-- The inverse includes the retained subdivision into its open star and then applies the
restricted subdivision homeomorphism. -/
@[simp]
theorem complementHomotopyEquiv_symm_apply
    (x : Realization ((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex).restrict {σ : Face K | σ.1 ∉ P})) :
    (K.complementHomotopyEquiv P).symm x =
      K.complementSubdivisionHomeomorph P
        (((TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
          K.toPreAbstractSimplicialComplex).openStarHomotopyEquiv {σ : Face K | σ.1 ∉ P}).symm x) :=
  (rfl)

/-- The complement of a subcomplex of a finite complex has finite CW type. The model is the
full subcomplex on the remaining face-vertices in the barycentric subdivision. -/
instance instFiniteCWTypeComplement [Finite (Face K)] :
    TauCeti.FiniteCWType {y : Realization K | y.1.support ∉ P} :=
  (K.complementHomotopyEquiv P).finiteCWType

variable (s : Set ι)

/-- Deleting any collection of vertices from a finite simplicial realization leaves a space
of finite CW type. Edges between deleted vertices cause no difficulty: the CW model is taken
in the barycentric subdivision, rather than by deleting those vertices from `K` itself. -/
instance instFiniteCWTypeComplVertexImage [Finite (Face K)] :
    TauCeti.FiniteCWType {x : Realization K // x ∉ K.vertex '' s} := by
  let P := ((⊥ : AbstractSimplicialComplex ι).restrict s).toPreAbstractSimplicialComplex.map
    (Subtype.val : s → ι)
  have heq : {y : Realization K | y.1.support ∉ P} = (K.vertex '' s)ᶜ := by
    ext x
    have hmem : x.1.support ∈ P ↔ x ∈ K.vertex '' s := by
      rw [mem_map_restrict_iff, TauCeti.AbstractSimplicialComplex.mem_bot]
      constructor
      · rintro ⟨⟨v, hv⟩, hs⟩
        exact ⟨v, hs (by simp [hv]), (Realization.eq_vertex_of_support_eq K x hv).symm⟩
      · rintro ⟨v, hv, rfl⟩
        simp [hv]
    exact not_congr hmem
  exact (Homeomorph.setCongr heq.symm).finiteCWType

end AbstractSimplicialComplex
