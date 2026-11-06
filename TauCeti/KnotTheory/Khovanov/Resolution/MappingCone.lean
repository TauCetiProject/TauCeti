/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.MappingCone
public import TauCeti.KnotTheory.Khovanov.Resolution.ResolveCrossing

/-!
# The skein mapping cone of the Khovanov bracket

Let `D` be a planar PD-code with `n + 1` crossings and `c` one of its crossings. Write
`D_A = D.resolveCrossing c true` and `D_B = D.resolveCrossing c false` for its two resolutions
at `c`, planar codes with `n` crossings. The vertices of the cube of resolutions of `D` at which
`c` has the `A`-smoothing form the `0`-face of the cube in the direction of `c`, which is the cube
of resolutions of `D_A`; those at which `c` has the `B`-smoothing form the `1`-face, which is the
cube of resolutions of `D_B` with every height raised by one, so with the quantum degree lowered by
one (`TauCeti.PDCode.resolveCrossingCubeIso`). The edges of the cube of `D` in the direction of
`c`, the merges and splits at `c`, form the saddle map
`TauCeti.PDCode.resolveCrossingSaddleCubeMap` from the cube of `D_A` in quantum degree `j` to the
cube of `D_B` in quantum degree `j - 1`.

Totalizing, the saddle map is a cochain map `TauCeti.PDCode.khovanovBracketSaddleMap` from
`⟦D_A⟧ʲ` to `⟦D_B⟧ʲ⁻¹`, and its mapping cone is the bracket of `D` shifted by one:

`Cone(⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ⁻¹) ≅ ⟦D⟧ʲ[1]`

(`TauCeti.PDCode.khovanovBracketMappingConeIso`). On the summand of a state `S` of `D_A` it is
the identification of `S` with the vertex of `D` over it. On the summand of a state `S` of `D_B`
it carries the sign `-(-1) ^ #{i ∈ S | i.castSucc < c}`: the cone convention contributes `-1`,
and moving `c` to the front of the crossing order contributes the parity of the crossings of the
vertex preceding `c`. This is the cone description of the Khovanov bracket behind the skein long
exact sequence and the cancellation arguments for Reidemeister invariance.

## Main definitions

All in the namespace `TauCeti.PDCode`:

* `resolveCrossingSaddleCubeMap D c hD R hj`: the saddle map at `c` from the cube of resolutions
  of `D_A` in quantum degree `j` to that of `D_B` in quantum degree `j'`, where `j' + 1 = j`.
* `resolveCrossingMappingConeIso D c hD R hj`: the mapping cone of its totalization is the
  totalized cube of resolutions of `D` in quantum degree `j`, shifted by one.
* `khovanovBracketSaddleMap D c hD R hj`: the saddle map `⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ'` of Khovanov
  brackets.
* `khovanovBracketMappingConeIso D c hD R hj`: its mapping cone is `⟦D⟧ʲ[1]`.

## Main results

* `resolveCrossingSaddleCubeMap_app_comp`: the saddle map is the edge map of the cube of `D` in
  the direction of `c`, read through the identifications of the faces.
* `resolveCrossingSaddleCubeMap_app_comp_resolutionCubeι`: on circle tensors it is the merge or
  split at `c` of the vertices of `D`.
* `inl_v_resolveCrossingMappingConeIso_hom_f`, `inr_f_resolveCrossingMappingConeIso_hom_f`: the
  cone isomorphism on the vertices of the two resolutions.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.1.
-/

public section

noncomputable section

open CategoryTheory Limits Finset CochainComplex PiTensorProduct DualNumber

attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode (n + 1)) (c : Fin (n + 1)) (hD : D.IsPlanar) (R : Type u)
  [CommRing R] {j j' : ℤ} (hj : j' + 1 = j)

/-- On the `A`-face, taking the vertex over `S` is taking the image of `S`. -/
private lemma functor_resolveCrossingVertex_true :
    (monotone_resolveCrossingVertex (n := n) c true).functor =
      (show Monotone (Finset.map c.succAboveEmb) from fun _ _ ↦ map_subset_map.2).functor :=
  CategoryTheory.Functor.ext (resolveCrossingVertex_true c) fun _ _ _ ↦ Subsingleton.elim _ _

/-- On the `B`-face, taking the vertex over `S` is inserting `c` into the image of `S`. -/
private lemma functor_resolveCrossingVertex_false :
    (monotone_resolveCrossingVertex (n := n) c false).functor =
      (show Monotone fun S : Finset (Fin n) ↦ insert c (S.map c.succAboveEmb) from
        fun _ _ h ↦ insert_subset_insert c (map_subset_map.2 h)).functor :=
  CategoryTheory.Functor.ext (resolveCrossingVertex_false c) fun _ _ _ ↦ Subsingleton.elim _ _

/-- The cube of resolutions of the `A`-resolution of `D` at `c` is the `0`-face at `c` of the
cube of resolutions of `D`, in the same quantum degree. -/
private def resolveCrossingFaceZeroIso (j : ℤ) :
    (D.resolveCrossing c true).resolutionCube (IsPlanar.resolveCrossing D c true hD) R j ≅
      (D.resolutionCube hD R j).cubeFaceZeroAt c :=
  D.resolveCrossingCubeIso c true hD _ R (j' := j) (by simp) ≪≫
    Functor.isoWhiskerRight (eqToIso (functor_resolveCrossingVertex_true c)) _

/-- The cube of resolutions of the `B`-resolution of `D` at `c` in quantum degree `j'` is the
`1`-face at `c` of the cube of resolutions of `D` in quantum degree `j' + 1`. -/
private def resolveCrossingFaceOneIso :
    (D.resolveCrossing c false).resolutionCube (IsPlanar.resolveCrossing D c false hD) R j' ≅
      (D.resolutionCube hD R j).cubeFaceOneAt c :=
  D.resolveCrossingCubeIso c false hD _ R (by simpa using hj) ≪≫
    Functor.isoWhiskerRight (eqToIso (functor_resolveCrossingVertex_false c)) _

/-- **The saddle map at a crossing.** The map of cubes of resolutions from the `A`-resolution
`D.resolveCrossing c true` in quantum degree `j` to the `B`-resolution `D.resolveCrossing c false`
in quantum degree `j' = j - 1` given by the edges of the cube of `D` in the direction of `c`:
the merge or split at `c`, read through the identifications of the two resolutions with the two
faces of the cube of `D` at `c`. -/
def resolveCrossingSaddleCubeMap :
    (D.resolveCrossing c true).resolutionCube (IsPlanar.resolveCrossing D c true hD) R j ⟶
      (D.resolveCrossing c false).resolutionCube (IsPlanar.resolveCrossing D c false hD) R j' :=
  (D.resolveCrossingFaceZeroIso c hD R j).hom ≫ (D.resolutionCube hD R j).cubeFaceMapAt c ≫
    (D.resolveCrossingFaceOneIso c hD R hj).inv

/-- The saddle map is the edge map of the cube of resolutions of `D` from the vertex over `S` on
the `A`-face to the vertex over `S` on the `B`-face, read through the identifications of the
faces. -/
theorem resolveCrossingSaddleCubeMap_app_comp (S : Finset (Fin n)) :
    (D.resolveCrossingSaddleCubeMap c hD R hj).app S ≫
        (D.resolveCrossingCubeIso c false hD _ R (by simpa using hj)).hom.app S =
      (D.resolveCrossingCubeIso c true hD _ R (j' := j) (by simp)).hom.app S ≫
        (D.resolutionCube hD R j).map
          (homOfLE (by simp [subset_insert] : resolveCrossingVertex c true S ⊆
            resolveCrossingVertex c false S)) := by
  simp only [resolveCrossingSaddleCubeMap, resolveCrossingFaceZeroIso, resolveCrossingFaceOneIso,
    NatTrans.comp_app, Iso.trans_hom, Iso.trans_inv, Category.assoc, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    Functor.cubeFaceMapAt_app, Iso.inv_hom_id_app, Category.comp_id]
  rw [cancel_epi, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (Subsingleton.elim _ _)

/-- On circle tensors, the saddle map at `c` is the merge or split at `c` of the vertices of `D`
over `S`, read through the identifications of the circles of the two resolutions with those of
`D` (`TauCeti.PDCode.resolveCrossingCubeCircleEquiv`). -/
theorem resolveCrossingSaddleCubeMap_app_comp_resolutionCubeι (S : Finset (Fin n))
    (hst : ∀ i, i ≠ c → cubeState (resolveCrossingVertex c true S) i =
      cubeState (resolveCrossingVertex c false S) i)
    (hc : cubeState (resolveCrossingVertex c true S) c ≠
      cubeState (resolveCrossingVertex c false S) c)
    (h : #(D.circlesAt (cubeState (resolveCrossingVertex c true S)) c) = 2 ∨
      #(D.circlesAt (cubeState (resolveCrossingVertex c false S)) c) = 2) :
    (D.resolveCrossingSaddleCubeMap c hD R hj).app S ≫
        (D.resolveCrossing c false).resolutionCubeι (IsPlanar.resolveCrossing D c false hD) R j'
          S ≫ ModuleCat.ofHom
            (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingCubeCircleEquiv c false S)).toLinearMap =
      (D.resolveCrossing c true).resolutionCubeι (IsPlanar.resolveCrossing D c true hD) R j S ≫
        ModuleCat.ofHom
          (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingCubeCircleEquiv c true S)).toLinearMap ≫
          ModuleCat.ofHom (D.resolutionEdgeMap hst hc h R) := by
  rw [← D.resolveCrossingCubeIso_hom_app_comp_resolutionCubeι c false hD _ R (by simpa using hj),
    reassoc_of% (D.resolveCrossingSaddleCubeMap_app_comp c hD R hj S),
    D.resolutionCube_map_homOfLE_comp_resolutionCubeι hD R j (a := c) (by simp) (by simp) _ hst hc
      h, D.resolveCrossingCubeIso_hom_app_comp_resolutionCubeι_assoc c true hD _ R (by simp)]

/-- The totalization of `resolveCrossingFaceZeroIso`. -/
private def resolveCrossingFaceZeroComplexIso :
    ((D.resolveCrossing c true).resolutionCube (IsPlanar.resolveCrossing D c true hD) R
      j).cubeComplex ≅ ((D.resolutionCube hD R j).cubeFaceZeroAt c).cubeComplex :=
  (cubeComplexFunctor (ModuleCat.{u} R) (Fin n)).mapIso (D.resolveCrossingFaceZeroIso c hD R j)

/-- The totalization of `resolveCrossingFaceOneIso`. -/
private def resolveCrossingFaceOneComplexIso :
    ((D.resolveCrossing c false).resolutionCube (IsPlanar.resolveCrossing D c false hD) R
      j').cubeComplex ≅ ((D.resolutionCube hD R j).cubeFaceOneAt c).cubeComplex :=
  (cubeComplexFunctor (ModuleCat.{u} R) (Fin n)).mapIso (D.resolveCrossingFaceOneIso c hD R hj)

/-- The face identifications carry the saddle map to the edges of the cube of `D` in the
direction of `c`. -/
private lemma resolveCrossingFace_comm :
    NatTrans.cubeComplexMap (D.resolveCrossingSaddleCubeMap c hD R hj) ≫
        (D.resolveCrossingFaceOneComplexIso c hD R hj).hom =
      (D.resolveCrossingFaceZeroComplexIso c hD R).hom ≫
        NatTrans.cubeComplexMap ((D.resolutionCube hD R j).cubeFaceMapAt c) := by
  simp only [resolveCrossingFaceZeroComplexIso, resolveCrossingFaceOneComplexIso,
    Functor.mapIso_hom, cubeComplexFunctor_map]
  rw [← NatTrans.cubeComplexMap_comp, ← NatTrans.cubeComplexMap_comp]
  simp [resolveCrossingSaddleCubeMap]

/-- **The skein mapping cone of the cube of resolutions.** The mapping cone of the saddle map at
the crossing `c`, from the totalized cube of resolutions of the `A`-resolution in quantum degree
`j` to that of the `B`-resolution in quantum degree `j' = j - 1`, is isomorphic to the totalized
cube of resolutions of `D` in quantum degree `j`, shifted by one. A vertex of the `A`-resolution
goes to the vertex over it (`TauCeti.PDCode.inl_v_resolveCrossingMappingConeIso_hom_f`), and a
vertex `S` of the `B`-resolution to the vertex over it with the sign
`-(-1) ^ #{i ∈ S | i.castSucc < c}` (`TauCeti.PDCode.inr_f_resolveCrossingMappingConeIso_hom_f`). -/
def resolveCrossingMappingConeIso :
    mappingCone (NatTrans.cubeComplexMap (D.resolveCrossingSaddleCubeMap c hD R hj)) ≅
      (D.resolutionCube hD R j).cubeComplex⟦(1 : ℤ)⟧ :=
  mappingCone.mapIso _ _ (D.resolveCrossingFace_comm c hD R hj) ≪≫
    (D.resolutionCube hD R j).cubeComplexMappingConeIsoAt c

/-- The isomorphism `TauCeti.PDCode.resolveCrossingMappingConeIso` sends a vertex `S` of the cube of
the `A`-resolution, placed in the mapping cone by `mappingCone.inl`, to the vertex
`resolveCrossingVertex c true S` of the cube of `D`. -/
@[reassoc (attr := simp)]
theorem inl_v_resolveCrossingMappingConeIso_hom_f (p : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = p + 1}) :
    ((D.resolveCrossing c true).resolutionCube (IsPlanar.resolveCrossing D c true hD) R
        j).cubeComplexι S ≫
        (mappingCone.inl (NatTrans.cubeComplexMap
          (D.resolveCrossingSaddleCubeMap c hD R hj))).v (p + 1) p (by omega) ≫
          (D.resolveCrossingMappingConeIso c hD R hj).hom.f p =
      (D.resolveCrossingCubeIso c true hD _ R (j' := j) (by simp)).hom.app S.1 ≫
        (D.resolutionCube hD R j).cubeComplexι
          ⟨resolveCrossingVertex c true S.1, by simp [S.2]⟩ := by
  simp only [resolveCrossingMappingConeIso, Iso.trans_hom, HomologicalComplex.comp_f,
    mappingCone.mapIso_hom, mappingCone.inl_v_map_f_assoc]
  simp only [resolveCrossingFaceZeroComplexIso, Functor.mapIso_hom, cubeComplexFunctor_map]
  rw [resolveCrossingFaceZeroIso, Iso.trans_hom, NatTrans.cubeComplexMap_comp,
    HomologicalComplex.comp_f]
  simp only [NatTrans.ι_cubeComplexMap_f_assoc, Category.assoc, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map,
    Functor.inl_v_cubeComplexMappingConeIsoAt_hom_f]
  rw [Functor.eqToHom_comp_cubeComplexι _ (resolveCrossingVertex_true c S.1)]

/-- The isomorphism `TauCeti.PDCode.resolveCrossingMappingConeIso` sends a vertex `S` of the cube of
the `B`-resolution, placed in the mapping cone by `mappingCone.inr`, to the vertex
`resolveCrossingVertex c false S` of the cube of `D`, with the sign
`-(-1) ^ #{i ∈ S | i.castSucc < c}`. -/
@[reassoc (attr := simp)]
theorem inr_f_resolveCrossingMappingConeIso_hom_f (p : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = p}) :
    ((D.resolveCrossing c false).resolutionCube (IsPlanar.resolveCrossing D c false hD) R
        j').cubeComplexι S ≫
        (mappingCone.inr (NatTrans.cubeComplexMap
          (D.resolveCrossingSaddleCubeMap c hD R hj))).f p ≫
          (D.resolveCrossingMappingConeIso c hD R hj).hom.f p =
      -((-1 : ℤ) ^ #{i ∈ S.1 | i.castSucc < c} •
        (D.resolveCrossingCubeIso c false hD _ R (by simpa using hj)).hom.app S.1 ≫
          (D.resolutionCube hD R j).cubeComplexι
            ⟨resolveCrossingVertex c false S.1, by
              simp [card_insert_of_notMem, Fin.succAbove_ne, S.2]⟩) := by
  simp only [resolveCrossingMappingConeIso, Iso.trans_hom, HomologicalComplex.comp_f,
    mappingCone.mapIso_hom, mappingCone.inr_f_map_f_assoc]
  simp only [resolveCrossingFaceOneComplexIso, Functor.mapIso_hom, cubeComplexFunctor_map]
  rw [resolveCrossingFaceOneIso, Iso.trans_hom, NatTrans.cubeComplexMap_comp,
    HomologicalComplex.comp_f]
  simp only [NatTrans.ι_cubeComplexMap_f_assoc, Category.assoc, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map,
    Functor.inr_f_cubeComplexMappingConeIsoAt_hom_f,
    Preadditive.comp_neg, Preadditive.comp_zsmul]
  rw [Functor.eqToHom_comp_cubeComplexι _ (resolveCrossingVertex_false c S.1)]

/-- **The saddle map of unnormalized Khovanov complexes at a crossing.** The cochain map from the
Khovanov bracket of the `A`-resolution `D.resolveCrossing c true` in quantum degree `j` to that of
the `B`-resolution `D.resolveCrossing c false` in quantum degree `j' = j - 1`, the totalization of
`TauCeti.PDCode.resolveCrossingSaddleCubeMap`. -/
def khovanovBracketSaddleMap :
    (D.resolveCrossing c true).khovanovBracket (IsPlanar.resolveCrossing D c true hD) R j ⟶
      (D.resolveCrossing c false).khovanovBracket (IsPlanar.resolveCrossing D c false hD) R j' :=
  eqToHom ((D.resolveCrossing c true).khovanovBracket_apply _ R j) ≫
    NatTrans.cubeComplexMap (D.resolveCrossingSaddleCubeMap c hD R hj) ≫
      eqToHom ((D.resolveCrossing c false).khovanovBracket_apply _ R j').symm

/-- The saddle map of Khovanov brackets is the totalization of the saddle map of cubes of
resolutions. -/
theorem khovanovBracketSaddleMap_def :
    D.khovanovBracketSaddleMap c hD R hj =
      eqToHom ((D.resolveCrossing c true).khovanovBracket_apply _ R j) ≫
        NatTrans.cubeComplexMap (D.resolveCrossingSaddleCubeMap c hD R hj) ≫
          eqToHom ((D.resolveCrossing c false).khovanovBracket_apply _ R j').symm :=
  (rfl)

/-- The identifications of the Khovanov brackets of the two resolutions with the totalized cubes
carry the saddle map of brackets to the saddle map of cubes. -/
private lemma khovanovBracketSaddleMap_comm :
    D.khovanovBracketSaddleMap c hD R hj ≫
        (eqToIso ((D.resolveCrossing c false).khovanovBracket_apply _ R j')).hom =
      (eqToIso ((D.resolveCrossing c true).khovanovBracket_apply _ R j)).hom ≫
        NatTrans.cubeComplexMap (D.resolveCrossingSaddleCubeMap c hD R hj) := by
  simp [khovanovBracketSaddleMap_def]

/-- **The skein mapping cone of the unnormalized Khovanov complex.** For a crossing `c` of a planar
code `D`, the mapping cone of the saddle map from the Khovanov bracket of the `A`-resolution in
quantum degree `j` to that of the `B`-resolution in quantum degree `j' = j - 1` is isomorphic to
the Khovanov bracket of `D` in quantum degree `j`, shifted by one. It is
`TauCeti.PDCode.resolveCrossingMappingConeIso` read through the identifications of the brackets
with the totalized cubes of resolutions (`TauCeti.PDCode.khovanovBracketMappingConeIso_hom`). -/
def khovanovBracketMappingConeIso :
    mappingCone (D.khovanovBracketSaddleMap c hD R hj) ≅ (D.khovanovBracket hD R j)⟦(1 : ℤ)⟧ :=
  mappingCone.mapIso _ _ (D.khovanovBracketSaddleMap_comm c hD R hj) ≪≫
    D.resolveCrossingMappingConeIso c hD R hj ≪≫
      (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ)).mapIso
        (eqToIso (D.khovanovBracket_apply hD R j).symm)

/-- The skein mapping cone isomorphism of Khovanov brackets is that of the totalized cubes of
resolutions, read through the identifications of the brackets with the totalized cubes. -/
theorem khovanovBracketMappingConeIso_hom :
    (D.khovanovBracketMappingConeIso c hD R hj).hom =
      mappingCone.map _ _ (eqToHom ((D.resolveCrossing c true).khovanovBracket_apply _ R j))
          (eqToHom ((D.resolveCrossing c false).khovanovBracket_apply _ R j'))
          (by simp [khovanovBracketSaddleMap_def]) ≫
        (D.resolveCrossingMappingConeIso c hD R hj).hom ≫
          (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (1 : ℤ)).map
            (eqToHom (D.khovanovBracket_apply hD R j).symm) :=
  (rfl)

end TauCeti.PDCode
