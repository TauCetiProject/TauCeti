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
On the vertex `S` it acts by the vertex isomorphism with the sign
`(-1) ^ #(S.inversions E.crossingEquiv)` of the permutation of `S` comparing the two crossing
orders. It is the identity for the identity identification and is compatible with composition
and inversion.

When `E` keeps the crossings, the vertex isomorphisms form an isomorphism of the cubes of
resolutions themselves (`TauCeti.PDCode.ResolutionEquiv.resolutionCubeNatIso`), so that maps of
cubes can be transported along `E` before totalizing.

This applies to relabelling the half-edges and crossings of a code (`TauCeti.PDCode.relabel`), in
particular to reordering its crossings, to reading a crossing from another slot
(`TauCeti.PDCode.rotateCrossing`) and to permuting the labels of its crossing-free circles.

## Main definitions

* `TauCeti.PDCode.ResolutionEquiv.resolutionCubeIso`: the vertex isomorphisms of the cubes of
  resolutions, characterized by `ResolutionEquiv.resolutionCubeIso_hom_comp_resolutionCubeι`.
* `TauCeti.PDCode.ResolutionEquiv.khovanovBracketIso`: the isomorphism of unnormalized Khovanov
  complexes, given in each quantum degree by `ResolutionEquiv.khovanovBracketIso_hom_apply`.
* `TauCeti.PDCode.ResolutionEquiv.resolutionCubeNatIso`: for an identification keeping the
  crossings, the isomorphism of cubes of resolutions, characterized by
  `ResolutionEquiv.resolutionCubeNatIso_hom_app_comp_resolutionCubeι`.

## Main results

* `TauCeti.PDCode.ResolutionEquiv.isCubeReindexCompatible`: the vertex isomorphisms commute with
  the saddle maps.
* `TauCeti.PDCode.ResolutionEquiv.refl_khovanovBracketIso`,
  `TauCeti.PDCode.ResolutionEquiv.trans_khovanovBracketIso`,
  `TauCeti.PDCode.ResolutionEquiv.symm_khovanovBracketIso`: the identity, composition and
  inverse laws.

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

namespace ResolutionEquiv

variable {D : PDCode n} {D' : PDCode m} {D'' : PDCode r} (E : D.ResolutionEquiv D')
  (hD : D.IsPlanar) (hD' : D'.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The vertex isomorphism from the vertex `S` of the degree-`j` cube of resolutions of `D` to the
vertex `S.map E.crossingEquiv` of that of `D'`: it reindexes the circle tensor of the resolution
of `S` along the bijection of resolved circles induced by `E`. -/
def resolutionCubeIso (S : Finset (Fin n)) :
    (D.resolutionCube hD R j).obj S ≅
      (D'.resolutionCube hD' R j).obj (S.map E.crossingEquiv.toEmbedding) :=
  (D.resolutionCubeObjCongr hD R j hD'
    (E.smoothingEquiv (cubeState_map_apply E.crossingEquiv S)).resolvedCircleCongr
    (by rw [card_map])).toModuleIso

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
  exact D.resolutionCubeι_resolutionCubeObjCongr hD R j hD' _ _ x

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
  rw [← cancel_mono (D'.resolutionCubeι hD' R j ((insert a S).map E.crossingEquiv.toEmbedding))]
  simp only [Category.assoc]
  -- Both sides now reindex circle tensors and apply a saddle map, in the two orders.
  rw [resolutionCubeIso_hom_comp_resolutionCubeι,
    D'.resolutionCube_map_homOfLE_comp_resolutionCubeι hD' R j hT _ hst' hc'
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
    D.resolutionCubeι hD R j S)]
  simp only [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  -- The vertex isomorphism reindexes along the identity bijection of resolved circles.
  rw [resolutionCubeIso_hom_comp_eqToHom_comp_resolutionCubeι _ _ _ _ _ (by simp) fun i ↦ by simp]
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
  -- Reindexing along the composite identification is the composite of the reindexings.
  have hreindex : reindex R (fun _ ↦ R[ε]) ((E.trans F).smoothingEquiv
      (cubeState_map_apply (E.trans F).crossingEquiv S)).resolvedCircleCongr =
        (reindex R (fun _ ↦ R[ε])
          (E.smoothingEquiv (cubeState_map_apply E.crossingEquiv S)).resolvedCircleCongr).trans
          (reindex R (fun _ ↦ R[ε]) (F.smoothingEquiv h).resolvedCircleCongr) := by
    rw [← smoothingEquiv_trans_smoothingEquiv E F (cubeState_map_apply E.crossingEquiv S) h,
      SmoothingEquiv.resolvedCircleCongr_trans, reindex_trans]
  ext : 1
  rw [← cancel_mono (D''.resolutionCubeι hD'' R j _)]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [resolutionCubeIso_hom_comp_resolutionCubeι,
    resolutionCubeIso_hom_comp_eqToHom_comp_resolutionCubeι _ _ _ _ _ (by simp [map_map]) h,
    resolutionCubeIso_hom_comp_resolutionCubeι_assoc, hreindex]
  simp only [LinearEquiv.coe_trans, ModuleCat.ofHom_comp]

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
vertex `S` it acts by `E.resolutionCubeIso` with the sign
`(-1) ^ #(S.inversions E.crossingEquiv)`
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
  have hα := funext (refl_resolutionCubeIso hD R j)
  rw [khovanovBracketIso_hom_apply]
  simp only [hα]
  rw [Functor.cubeComplexReindexIso_refl_of_eq _ (refl_crossingEquiv D)]
  simp

/-- The isomorphism of unnormalized Khovanov complexes of a composite identification is the
composite of the isomorphisms. -/
theorem trans_khovanovBracketIso (F : D'.ResolutionEquiv D'') (hD'' : D''.IsPlanar) :
    (E.trans F).khovanovBracketIso hD hD'' R =
      E.khovanovBracketIso hD hD' R ≪≫ F.khovanovBracketIso hD' hD'' R := by
  ext j : 2
  -- The vertex isomorphisms are the composites of vertex isomorphisms, along a crossing bijection
  -- which is only propositionally the composite.
  have hα := funext (E.trans_resolutionCubeIso hD hD' R j F hD'')
  rw [Iso.trans_hom, GradedObject.categoryOfGradedObjects_comp, khovanovBracketIso_hom_apply,
    khovanovBracketIso_hom_apply, khovanovBracketIso_hom_apply]
  simp only [hα]
  rw [Functor.cubeComplexReindexIso_trans_of_eq _ E.crossingEquiv F.crossingEquiv
    (trans_crossingEquiv E F) _ _ (E.isCubeReindexCompatible hD hD' R j)
    (F.isCubeReindexCompatible hD' hD'' R j)]
  simp

/-- The isomorphism of unnormalized Khovanov complexes of the inverse identification is the
inverse of the isomorphism. -/
theorem symm_khovanovBracketIso :
    E.symm.khovanovBracketIso hD' hD R = (E.khovanovBracketIso hD hD' R).symm := by
  have h := E.trans_khovanovBracketIso hD hD' R E.symm hD
  rw [self_trans_symm, refl_khovanovBracketIso] at h
  exact Iso.ext (Iso.inv_ext' (congrArg Iso.hom h).symm)

end ResolutionEquiv

/-! ### Identifications fixing the crossings -/

namespace ResolutionEquiv

variable {D₁ D₂ : PDCode n} (E : D₁.ResolutionEquiv D₂) (hE : E.crossingEquiv = Equiv.refl _)
  (hD₁ : D₁.IsPlanar) (hD₂ : D₂.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

include hE in
private theorem apply_crossingEquiv_of_eq_refl (s : Fin n → Bool) (i : Fin n) :
    s (E.crossingEquiv i) = s i := by
  rw [hE, Equiv.refl_apply]

/-- The map of cubes of resolutions reindexing every circle tensor along `E`, when `E` keeps
the crossings. -/
private noncomputable def resolutionCubeHomOfEqRefl :
    D₁.resolutionCube hD₁ R j ⟶ D₂.resolutionCube hD₂ R j :=
  resolutionCubeHom hD₁ R j hD₂
    (fun s ↦ (reindex R (fun _ ↦ R[ε])
      (E.smoothingEquiv (E.apply_crossingEquiv_of_eq_refl hE s)).resolvedCircleCongr).toLinearMap)
    (fun s ↦ by simpa using Khovanov.isHomogeneous_reindex (R := R) _)
    (fun s t c hst hc h h' x ↦ by
      obtain ⟨slots, hslots⟩ := E.exists_slots c
      rw [hE, Equiv.refl_apply] at hslots
      have := SmoothingEquiv.reindex_resolutionEdgeMap
        (E.smoothingEquiv (E.apply_crossingEquiv_of_eq_refl hE s))
        (E.smoothingEquiv (E.apply_crossingEquiv_of_eq_refl hE t)) (by simp) (by simp) slots
        (by simpa using hslots) hst hc hst hc h h' R x
      rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe]
      exact this.symm)
    (add_zero j).symm

@[reassoc]
private theorem resolutionCubeHomOfEqRefl_app_comp_resolutionCubeι (S : Finset (Fin n)) :
    (E.resolutionCubeHomOfEqRefl hE hD₁ hD₂ R j).app S ≫ D₂.resolutionCubeι hD₂ R j S =
      D₁.resolutionCubeι hD₁ R j S ≫ ModuleCat.ofHom (reindex R (fun _ ↦ R[ε])
        (E.smoothingEquiv (E.apply_crossingEquiv_of_eq_refl hE (cubeState S))).resolvedCircleCongr
        ).toLinearMap :=
  resolutionCubeHom_app_comp_resolutionCubeι ..

include hE in
private theorem symm_crossingEquiv_eq_refl : E.symm.crossingEquiv = Equiv.refl _ := by
  rw [symm_crossingEquiv, hE, Equiv.refl_symm]

/-- The circle bijections of `E.symm` are the inverses of those of `E`. -/
private theorem resolvedCircleCongr_symm_smoothingEquiv (s : Fin n → Bool) :
    (E.symm.smoothingEquiv (E.symm.apply_crossingEquiv_of_eq_refl
      (E.symm_crossingEquiv_eq_refl hE) s)).resolvedCircleCongr =
      (E.smoothingEquiv (E.apply_crossingEquiv_of_eq_refl hE s)).resolvedCircleCongr.symm := by
  rw [← SmoothingEquiv.resolvedCircleCongr_symm, smoothingEquiv_symm]

private theorem resolutionCubeHomOfEqRefl_comp_symm :
    E.resolutionCubeHomOfEqRefl hE hD₁ hD₂ R j ≫
      E.symm.resolutionCubeHomOfEqRefl (E.symm_crossingEquiv_eq_refl hE) hD₂ hD₁ R j = 𝟙 _ := by
  ext S : 2
  rw [NatTrans.comp_app, NatTrans.id_app, ← cancel_mono (D₁.resolutionCubeι hD₁ R j S),
    Category.assoc, resolutionCubeHomOfEqRefl_app_comp_resolutionCubeι,
    resolutionCubeHomOfEqRefl_app_comp_resolutionCubeι_assoc, Category.id_comp,
    resolvedCircleCongr_symm_smoothingEquiv E hE]
  ext x
  simp

/-- **The cubes of resolutions of codes identified with the same crossings.** An identification
`E` of all smoothings of `D₁` with those of `D₂` which keeps the crossings gives an isomorphism of
their cubes of resolutions in every quantum degree, reindexing the circle tensor of each vertex
along the bijection of resolved circles induced by `E`
(`ResolutionEquiv.resolutionCubeNatIso_hom_app_comp_resolutionCubeι`). -/
noncomputable def resolutionCubeNatIso : D₁.resolutionCube hD₁ R j ≅ D₂.resolutionCube hD₂ R j where
  hom := E.resolutionCubeHomOfEqRefl hE hD₁ hD₂ R j
  inv := E.symm.resolutionCubeHomOfEqRefl (E.symm_crossingEquiv_eq_refl hE) hD₂ hD₁ R j
  hom_inv_id := E.resolutionCubeHomOfEqRefl_comp_symm hE hD₁ hD₂ R j
  inv_hom_id := by
    simpa using E.symm.resolutionCubeHomOfEqRefl_comp_symm (E.symm_crossingEquiv_eq_refl hE) hD₂
      hD₁ R j

/-- On the vertex `S`, `ResolutionEquiv.resolutionCubeNatIso` reindexes the circle tensor along
the bijection of resolved circles induced by `E`. -/
@[reassoc]
theorem resolutionCubeNatIso_hom_app_comp_resolutionCubeι (S : Finset (Fin n))
    (h : ∀ i, cubeState S (E.crossingEquiv i) = cubeState S i) :
    (E.resolutionCubeNatIso hE hD₁ hD₂ R j).hom.app S ≫ D₂.resolutionCubeι hD₂ R j S =
      D₁.resolutionCubeι hD₁ R j S ≫ ModuleCat.ofHom
        (reindex R (fun _ ↦ R[ε]) (E.smoothingEquiv h).resolvedCircleCongr).toLinearMap :=
  E.resolutionCubeHomOfEqRefl_app_comp_resolutionCubeι hE hD₁ hD₂ R j S

/-- On the vertex `S`, the inverse of `ResolutionEquiv.resolutionCubeNatIso` reindexes the circle
tensor along the inverse of the bijection of resolved circles induced by `E`. -/
@[reassoc]
theorem resolutionCubeNatIso_inv_app_comp_resolutionCubeι (S : Finset (Fin n))
    (h : ∀ i, cubeState S (E.crossingEquiv i) = cubeState S i) :
    (E.resolutionCubeNatIso hE hD₁ hD₂ R j).inv.app S ≫ D₁.resolutionCubeι hD₁ R j S =
      D₂.resolutionCubeι hD₂ R j S ≫ ModuleCat.ofHom
        (reindex R (fun _ ↦ R[ε]) (E.smoothingEquiv h).resolvedCircleCongr.symm).toLinearMap := by
  rw [resolutionCubeNatIso, resolutionCubeHomOfEqRefl_app_comp_resolutionCubeι,
    resolvedCircleCongr_symm_smoothingEquiv E hE]

end ResolutionEquiv

end TauCeti.PDCode
