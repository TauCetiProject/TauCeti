/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Reindex
public import TauCeti.KnotTheory.Khovanov.Resolution.Cube
public import TauCeti.KnotTheory.Khovanov.Transport

/-!
# Relabelling the Khovanov cube of resolutions

The cube of resolutions of a planar PD-code `D` (`TauCeti.PDCode.resolutionCube`) and its signed
totalization, the unnormalized Khovanov complex `TauCeti.PDCode.khovanovBracket`, are built from
the labels of the code: its crossings index the cube, their order fixes the signs of the
differential, and its half-edges name the circles of each resolution. This file shows that codes
whose smoothings are identified give isomorphic complexes.

An identification `E : D.ResolutionEquiv D'` of all smoothings of `D` with those of `D'`, along a
bijection of crossings `E.crossingEquiv`, carries the vertex `S` of the cube of `D` to the vertex
`S.map E.crossingEquiv` of the cube of `D'`, by reindexing the circle tensor along the induced
bijection of resolved circles (`TauCeti.PDCode.ResolutionEquiv.resolutionCubeIso`). These vertex
isomorphisms commute with the saddle maps on the edges, so the reordering isomorphism of cube
complexes (`CategoryTheory.Functor.cubeComplexReindexIso`) gives an isomorphism of unnormalized
Khovanov complexes `TauCeti.PDCode.ResolutionEquiv.khovanovBracketIso`, in every quantum degree.
On the vertex `S` it acts by the vertex isomorphism with the sign `(-1) ^ #(S.inversions e)` of the
permutation of `S` comparing the two crossing orders. It is the identity for the identity
identification and is compatible with composition.

This applies to relabelling the half-edges and crossings of a code (`TauCeti.PDCode.relabel`), in
particular to reordering its crossings, to reading a crossing from another slot
(`TauCeti.PDCode.rotateCrossing`) and to permuting the labels of its crossing-free circles.

## Main definitions

* `TauCeti.PDCode.ResolutionEquiv.resolutionCubeIso`: the vertex isomorphisms of the cubes of
  resolutions, characterized by `ResolutionEquiv.resolutionCubeIso_hom_comp_resolutionCubeι`.
* `TauCeti.PDCode.ResolutionEquiv.khovanovBracketIso`: the isomorphism of unnormalized Khovanov
  complexes, given in each quantum degree by `ResolutionEquiv.khovanovBracketIso_hom_apply`.

## Main results

* `TauCeti.PDCode.ResolutionEquiv.isCubeReindexCompatible`: the vertex isomorphisms commute with
  the saddle maps.
* `TauCeti.PDCode.ResolutionEquiv.refl_khovanovBracketIso`,
  `TauCeti.PDCode.ResolutionEquiv.trans_khovanovBracketIso`: the identity and composition laws.

## References

* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2 (independence of the complex from the crossing order).
-/

public section

noncomputable section

open CategoryTheory Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

variable {n m r : ℕ}

/-- The state of the vertex `S.map e` of a cube indexed by `Fin m`, read along a bijection
`e : Fin n ≃ Fin m`, is the state of the vertex `S`. -/
@[simp]
theorem cubeState_map_apply (e : Fin n ≃ Fin m) (S : Finset (Fin n)) (i : Fin n) :
    cubeState (S.map e.toEmbedding) (e i) = cubeState S i := by
  simp [cubeState_apply]

/-- Along an edge `S ⋖ T` of the cube, the cube of resolutions acts by the saddle map at the
crossing added along the edge. This restates
`resolutionCube_map_homOfLE_insert_comp_resolutionCubeι` for a target which is only
propositionally `insert a S`. -/
private theorem resolutionCube_map_homOfLE_comp_resolutionCubeι (D : PDCode n) (hD : D.IsPlanar)
    (R : Type u) [CommRing R] (j : ℤ) {S T : Finset (Fin n)} {a : Fin n} (ha : a ∉ S)
    (hT : insert a S = T) (hST : S ⊆ T) (hst : ∀ i, i ≠ a → cubeState S i = cubeState T i)
    (hc : cubeState S a ≠ cubeState T a)
    (h : #(D.circlesAt (cubeState S) a) = 2 ∨ #(D.circlesAt (cubeState T) a) = 2) :
    (D.resolutionCube hD R j).map (homOfLE hST) ≫ D.resolutionCubeι hD R j T =
      D.resolutionCubeι hD R j S ≫ ModuleCat.ofHom (D.resolutionEdgeMap hst hc h R) := by
  subst hT
  exact D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R j ha

namespace ResolutionEquiv

variable {D : PDCode n} {D' : PDCode m} {D'' : PDCode r} (E : D.ResolutionEquiv D')
  (hD : D.IsPlanar) (hD' : D'.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The vertex isomorphism as a linear equivalence: reindexing along the bijection of resolved
circles, restricted to the quantum pieces, which are the images of the vertex inclusions. -/
private def resolutionCubeLinearEquiv (S : Finset (Fin n)) :
    (D.resolutionCube hD R j).obj S ≃ₗ[R]
      (D'.resolutionCube hD' R j).obj (S.map E.crossingEquiv.toEmbedding) :=
  (LinearEquiv.ofInjective _ (D.resolutionCubeι_injective hD R j S)).trans <|
    (LinearEquiv.ofEq _ _ (D.range_resolutionCubeι hD R j S)).trans <|
      ((reindex R (fun _ ↦ R[ε])
        (E.smoothingEquiv (cubeState_map_apply E.crossingEquiv S)).resolvedCircleCongr).ofSubmodules
          _ _ (by rw [Khovanov.map_reindex_circleQuantumGrading_piece, card_map])).trans <|
        (LinearEquiv.ofEq _ _ (D'.range_resolutionCubeι hD' R j _).symm).trans <|
          (LinearEquiv.ofInjective _ (D'.resolutionCubeι_injective hD' R j _)).symm

/-- The vertex isomorphism from the vertex `S` of the degree-`j` cube of resolutions of `D` to the
vertex `S.map E.crossingEquiv` of that of `D'`: it reindexes the circle tensor of the resolution
of `S` along the bijection of resolved circles induced by `E`. -/
def resolutionCubeIso (S : Finset (Fin n)) :
    (D.resolutionCube hD R j).obj S ≅
      (D'.resolutionCube hD' R j).obj (S.map E.crossingEquiv.toEmbedding) :=
  (E.resolutionCubeLinearEquiv hD hD' R j S).toModuleIso

/-- The vertex isomorphism reindexes the circle tensor along the bijection of resolved circles
induced by `E`. -/
@[reassoc]
theorem resolutionCubeIso_hom_comp_resolutionCubeι (S : Finset (Fin n)) :
    (E.resolutionCubeIso hD hD' R j S).hom ≫
        D'.resolutionCubeι hD' R j (S.map E.crossingEquiv.toEmbedding) =
      D.resolutionCubeι hD R j S ≫ ModuleCat.ofHom (reindex R (fun _ ↦ R[ε])
        (E.smoothingEquiv (cubeState_map_apply E.crossingEquiv S)).resolvedCircleCongr).toLinearMap
    := by
  ext x
  simp [resolutionCubeIso, resolutionCubeLinearEquiv]

/-- The vertex isomorphism, followed by an identification of its target vertex with an equal
vertex `T`, reindexes the circle tensor along the bijection of resolved circles induced by `E`
between the resolutions of `S` and `T`. -/
private theorem resolutionCubeIso_hom_comp_eqToHom_comp_resolutionCubeι {S : Finset (Fin n)}
    {T : Finset (Fin m)} (hT : S.map E.crossingEquiv.toEmbedding = T)
    (h : ∀ i, cubeState T (E.crossingEquiv i) = cubeState S i) :
    (E.resolutionCubeIso hD hD' R j S).hom ≫
        eqToHom (congrArg (D'.resolutionCube hD' R j).obj hT) ≫ D'.resolutionCubeι hD' R j T =
      D.resolutionCubeι hD R j S ≫
        ModuleCat.ofHom (reindex R (fun _ ↦ R[ε]) (E.smoothingEquiv h).resolvedCircleCongr) := by
  subst hT
  rw [eqToHom_refl, Category.id_comp, resolutionCubeIso_hom_comp_resolutionCubeι]

/-- **The vertex isomorphisms commute with the saddle maps.** Along the edge from `S` to
`S ∪ {a}`, reindexing the circle tensors of the two resolutions commutes with the saddle map at
`a` of `D` and the saddle map at `E.crossingEquiv a` of `D'`, because the two reindexings use the
same bijections of half-edges and of crossing-free labels. -/
theorem isCubeReindexCompatible :
    Functor.IsCubeReindexCompatible (D.resolutionCube hD R j) (D'.resolutionCube hD' R j)
      E.crossingEquiv (E.resolutionCubeIso hD hD' R j) := by
  refine Functor.isCubeReindexCompatible_iff.2 fun S a ha ↦ ?_
  have ha' : E.crossingEquiv a ∉ S.map E.crossingEquiv.toEmbedding := by simpa using ha
  have hT : insert (E.crossingEquiv a) (S.map E.crossingEquiv.toEmbedding) =
      (insert a S).map E.crossingEquiv.toEmbedding := by simp [map_insert]
  have hcov : S.map E.crossingEquiv.toEmbedding ⋖ (insert a S).map E.crossingEquiv.toEmbedding :=
    hT ▸ covBy_insert ha'
  have hmem : E.crossingEquiv a ∈ (insert a S).map E.crossingEquiv.toEmbedding :=
    hT ▸ mem_insert_self _ _
  have hst' := cubeState_eq_of_covBy hcov ha' hmem
  have hc' := cubeState_ne_of_notMem_of_mem ha' hmem
  rw [← cancel_mono (D'.resolutionCubeι hD' R j ((insert a S).map E.crossingEquiv.toEmbedding)),
    Category.assoc, Category.assoc, resolutionCubeIso_hom_comp_resolutionCubeι,
    resolutionCube_map_homOfLE_comp_resolutionCubeι D' hD' R j ha' hT _ hst' hc'
      (hD'.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst' hc'),
    D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι_assoc hD R j ha,
    resolutionCubeIso_hom_comp_resolutionCubeι_assoc]
  obtain ⟨slots, hslots⟩ := E.exists_slots a
  ext x
  exact SmoothingEquiv.reindex_resolutionEdgeMap (E.smoothingEquiv _) (E.smoothingEquiv _)
    (by simp) (by simp) slots (by simpa using hslots) _ _ _ _ _ _ R _

/-- The vertex isomorphisms of the identity identification are the identifications
`S = S.map id` of vertices. -/
theorem refl_resolutionCubeIso (S : Finset (Fin n)) :
    (refl D).resolutionCubeIso hD hD R j S =
      eqToIso (congrArg (D.resolutionCube hD R j).obj (by simp)) := by
  ext : 1
  rw [← cancel_mono (eqToHom (congrArg (D.resolutionCube hD R j).obj (by simp)) ≫
    D.resolutionCubeι hD R j S), resolutionCubeIso_hom_comp_eqToHom_comp_resolutionCubeι _ _ _ _ _
      (by simp) (fun i ↦ by simp), eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  ext x
  simp

/-- The vertex isomorphisms of a composite identification are the composites of the vertex
isomorphisms, followed by the identification `(S.map e₁).map e₂ = S.map (e₁.trans e₂)`. -/
theorem trans_resolutionCubeIso (F : D'.ResolutionEquiv D'') (hD'' : D''.IsPlanar)
    (S : Finset (Fin n)) :
    (E.trans F).resolutionCubeIso hD hD'' R j S =
      E.resolutionCubeIso hD hD' R j S ≪≫
        F.resolutionCubeIso hD' hD'' R j (S.map E.crossingEquiv.toEmbedding) ≪≫
          eqToIso (congrArg (D''.resolutionCube hD'' R j).obj (by simp [map_map])) := by
  have h : ∀ i, cubeState (S.map (E.trans F).crossingEquiv.toEmbedding) (F.crossingEquiv i) =
      cubeState (S.map E.crossingEquiv.toEmbedding) i := fun i ↦ by
    rw [trans_crossingEquiv, Equiv.trans_toEmbedding, ← map_map, cubeState_map_apply]
  ext : 1
  rw [← cancel_mono (D''.resolutionCubeι hD'' R j _), resolutionCubeIso_hom_comp_resolutionCubeι,
    Iso.trans_hom, Iso.trans_hom, eqToIso.hom, Category.assoc, Category.assoc,
    resolutionCubeIso_hom_comp_eqToHom_comp_resolutionCubeι _ _ _ _ _ (by simp [map_map]) h,
    resolutionCubeIso_hom_comp_resolutionCubeι_assoc,
    ← smoothingEquiv_trans_smoothingEquiv E F (cubeState_map_apply E.crossingEquiv S) h,
    SmoothingEquiv.resolvedCircleCongr_trans, ← reindex_trans]
  rfl

/-- **Relabelling the unnormalized Khovanov complex.** An identification of all smoothings of
`D` with those of `D'` gives an isomorphism of their unnormalized Khovanov complexes, in every
quantum degree. In degree `j` it is the reordering isomorphism of the cube complexes along the
crossing bijection, with the vertex isomorphisms `E.resolutionCubeIso`
(`ResolutionEquiv.khovanovBracketIso_hom_apply`). -/
def khovanovBracketIso : D.khovanovBracket hD R ≅ D'.khovanovBracket hD' R :=
  GradedObject.isoMk _ _ fun j ↦ eqToIso (D.khovanovBracket_apply hD R j) ≪≫
    (D.resolutionCube hD R j).cubeComplexReindexIso E.crossingEquiv (E.resolutionCubeIso hD hD' R j)
      (E.isCubeReindexCompatible hD hD' R j) ≪≫ eqToIso (D'.khovanovBracket_apply hD' R j).symm

/-- In quantum degree `j`, the isomorphism of unnormalized Khovanov complexes is the reordering
isomorphism of the cube complexes with the vertex isomorphisms `E.resolutionCubeIso`. On the
vertex `S` it acts by `E.resolutionCubeIso` with the sign `(-1) ^ #(S.inversions e)`
(`CategoryTheory.Functor.ι_cubeComplexReindexIso_hom_f`). -/
theorem khovanovBracketIso_hom_apply :
    (E.khovanovBracketIso hD hD' R).hom j =
      eqToHom (D.khovanovBracket_apply hD R j) ≫
        ((D.resolutionCube hD R j).cubeComplexReindexIso E.crossingEquiv
          (E.resolutionCubeIso hD hD' R j) (E.isCubeReindexCompatible hD hD' R j)).hom ≫
          eqToHom (D'.khovanovBracket_apply hD' R j).symm := by
  simp [khovanovBracketIso]

/-- In quantum degree `j`, the inverse isomorphism of unnormalized Khovanov complexes is the
inverse of the reordering isomorphism of the cube complexes. -/
theorem khovanovBracketIso_inv_apply :
    (E.khovanovBracketIso hD hD' R).inv j =
      eqToHom (D'.khovanovBracket_apply hD' R j) ≫
        ((D.resolutionCube hD R j).cubeComplexReindexIso E.crossingEquiv
          (E.resolutionCubeIso hD hD' R j) (E.isCubeReindexCompatible hD hD' R j)).inv ≫
          eqToHom (D.khovanovBracket_apply hD R j).symm := by
  simp [khovanovBracketIso]

/-- The isomorphism of unnormalized Khovanov complexes of the identity identification is the
identity. -/
@[simp]
theorem refl_khovanovBracketIso : (refl D).khovanovBracketIso hD hD R = Iso.refl _ := by
  ext j : 2
  -- The vertex isomorphisms are the identifications of vertices, along a crossing bijection which
  -- is only propositionally the identity.
  have key : ∀ (e : Fin n ≃ Fin n) (he : e = Equiv.refl _)
      (hα : Functor.IsCubeReindexCompatible _ _ e
        fun S ↦ eqToIso (congrArg (D.resolutionCube hD R j).obj (by subst he; simp))),
      (D.resolutionCube hD R j).cubeComplexReindexIso e _ hα = Iso.refl _ := by
    rintro e rfl hα
    exact Functor.cubeComplexReindexIso_refl _
  have hα := funext (refl_resolutionCubeIso hD R j)
  rw [khovanovBracketIso_hom_apply]
  simp only [hα]
  rw [key _ (refl_crossingEquiv D)]
  simp

/-- The isomorphism of unnormalized Khovanov complexes of a composite identification is the
composite of the isomorphisms. -/
theorem trans_khovanovBracketIso (F : D'.ResolutionEquiv D'') (hD'' : D''.IsPlanar) :
    (E.trans F).khovanovBracketIso hD hD'' R =
      E.khovanovBracketIso hD hD' R ≪≫ F.khovanovBracketIso hD' hD'' R := by
  ext j : 2
  -- The vertex isomorphisms are the composites of vertex isomorphisms, along a crossing bijection
  -- which is only propositionally the composite.
  have key : ∀ (e : Fin n ≃ Fin r) (he : e = E.crossingEquiv.trans F.crossingEquiv)
      (hα : Functor.IsCubeReindexCompatible _ _ e fun S ↦ E.resolutionCubeIso hD hD' R j S ≪≫
        F.resolutionCubeIso hD' hD'' R j (S.map E.crossingEquiv.toEmbedding) ≪≫
          eqToIso (congrArg (D''.resolutionCube hD'' R j).obj (by subst he; simp [map_map]))),
      (D.resolutionCube hD R j).cubeComplexReindexIso e _ hα =
        (D.resolutionCube hD R j).cubeComplexReindexIso E.crossingEquiv
            (E.resolutionCubeIso hD hD' R j) (E.isCubeReindexCompatible hD hD' R j) ≪≫
          (D'.resolutionCube hD' R j).cubeComplexReindexIso F.crossingEquiv
            (F.resolutionCubeIso hD' hD'' R j) (F.isCubeReindexCompatible hD' hD'' R j) := by
    rintro e rfl hα
    exact Functor.cubeComplexReindexIso_trans (D.resolutionCube hD R j) E.crossingEquiv
      F.crossingEquiv _ _ (E.isCubeReindexCompatible hD hD' R j)
      (F.isCubeReindexCompatible hD' hD'' R j)
  have hα := funext (E.trans_resolutionCubeIso hD hD' R j F hD'')
  rw [Iso.trans_hom, GradedObject.categoryOfGradedObjects_comp, khovanovBracketIso_hom_apply,
    khovanovBracketIso_hom_apply, khovanovBracketIso_hom_apply]
  simp only [hα]
  rw [key _ (trans_crossingEquiv E F)]
  simp

end ResolutionEquiv

end TauCeti.PDCode
