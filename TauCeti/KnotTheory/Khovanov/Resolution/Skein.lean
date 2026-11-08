/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.MappingCone
public import TauCeti.KnotTheory.Khovanov.Resolution.ResolveCrossing

/-!
# The skein mapping cone of the unnormalized Khovanov complex

Let `D` be a planar PD-code with `n + 1` crossings and `c` one of its crossings, with resolutions
`D_A = D.resolveCrossing c true` and `D_B = D.resolveCrossing c false`. The cube of resolutions of
`D` splits into the face where `c` carries the `A`-smoothing, which is the cube of `D_A`, and the
face where `c` carries the `B`-smoothing, which is the cube of `D_B` with every height raised by
one, so in quantum degree `j` it is the cube of `D_B` in quantum degree `j - 1`
(`TauCeti.PDCode.resolveCrossingCubeIso`). The edges of the cube of `D` in the direction of `c` are
the saddle maps at `c`, and they form a map of cubes between the two faces,
`TauCeti.PDCode.resolveCrossingSaddle`. It acts on the circle tensors as the saddle map of `D` at
`c`, merging the two circles through `c` or splitting the circle through `c`
(`TauCeti.PDCode.resolveCrossingSaddle_app_comp_resolutionCubeι`).

Totalizing, the unnormalized Khovanov complex of `D` is, up to a shift by one, the mapping cone
of the induced cochain map `⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ⁻¹`, `TauCeti.PDCode.khovanovBracketMappingConeIso`.
Hence the skein triangle `⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ⁻¹ ⟶ ⟦D⟧ʲ⟦1⟧ ⟶ ⟦D_A⟧ʲ⟦1⟧` is distinguished in the
homotopy category (`TauCeti.PDCode.khovanovBracketSkeinTriangle_distinguished`). Rotated, it is
the degreewise split sequence `⟦D_B⟧ʲ⁻¹⟦-1⟧ ⟶ ⟦D⟧ʲ ⟶ ⟦D_A⟧ʲ` with connecting map the saddle map;
in terms of the quantum shift, the `B`-term is `⟦D_B⟧⟨1⟩[-1]`. Any homological functor, such as
cohomology, turns it into a long exact sequence.

The crossing `c` need not be the first one: the identification moves `c` to the front of the
crossing order, and the vertex `S` of the `B`-face then carries the sign
`-(-1) ^ #{a ∈ S | a.castSucc < c}` (`TauCeti.PDCode.inr_f_khovanovBracketMappingConeIso_hom_f`),
while the vertices of the `A`-face carry no sign
(`TauCeti.PDCode.inl_v_khovanovBracketMappingConeIso_hom_f`).

## Main definitions

All in the namespace `TauCeti.PDCode`:

* `resolveCrossingSaddle D c hD R j`: the map of cubes from the cube of resolutions of `D_A` in
  quantum degree `j` to that of `D_B` in quantum degree `j - 1`, given by the saddle maps of `D`
  at `c`.
* `khovanovBracketMappingConeIso D c hD R j`: the mapping cone of the cochain map induced by
  `resolveCrossingSaddle D c hD R j` is the degree-`j` component of `⟦D⟧` shifted by one.
* `khovanovBracketSkeinTriangle D c hD R j`: the skein triangle
  `⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ⁻¹ ⟶ ⟦D⟧ʲ⟦1⟧ ⟶ ⟦D_A⟧ʲ⟦1⟧`.

## Main results

* `resolveCrossingSaddle_app`: the component of the saddle map at a vertex is the edge map of the
  cube of `D` in the direction of `c`, through the identifications of the two faces.
* `resolveCrossingSaddle_app_comp_resolutionCubeι`: the saddle map acts on circle tensors as the
  merge or split of `D` at `c`.
* `inl_v_khovanovBracketMappingConeIso_hom_f`, `inr_f_khovanovBracketMappingConeIso_hom_f`: the
  mapping cone identification on the vertices of the two faces.
* `khovanovBracketSkeinTriangle_distinguished`: the skein triangle is distinguished in the
  homotopy category.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.4.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.1.
-/

public section

noncomputable section

open CategoryTheory Finset CochainComplex PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode (n + 1)) (c : Fin (n + 1)) (hD : D.IsPlanar) (R : Type u)
  [CommRing R] (j : ℤ)

/-! ### The faces at a crossing -/

/-- The cube of resolutions of `D_A` in quantum degree `j`, as the `0`-face at `c` of the cube of
resolutions of `D` in quantum degree `j`. -/
private def resolveCrossingFaceZeroIso :
    (D.resolveCrossing c true).resolutionCube (hD.resolveCrossing _ c true) R j ≅
      (D.resolutionCube hD R j).cubeFaceZeroAt c :=
  D.resolveCrossingCubeIso c true hD (hD.resolveCrossing _ c true) R (j := j) (j' := j) (by simp) ≪≫
    NatIso.ofComponents
      (fun S ↦ (D.resolutionCube hD R j).mapIso (eqToIso (resolveCrossingVertex_true c S)))
      fun _ ↦ by
        simp only [Functor.comp_map, Functor.mapIso_hom, ← Functor.map_comp]
        exact congrArg _ (Subsingleton.elim _ _)

/-- The cube of resolutions of `D_B` in quantum degree `j - 1`, as the `1`-face at `c` of the
cube of resolutions of `D` in quantum degree `j`. -/
private def resolveCrossingFaceOneIso :
    (D.resolveCrossing c false).resolutionCube (hD.resolveCrossing _ c false) R (j - 1) ≅
      (D.resolutionCube hD R j).cubeFaceOneAt c :=
  D.resolveCrossingCubeIso c false hD (hD.resolveCrossing _ c false) R (j := j) (j' := j - 1)
      (by simp) ≪≫
    NatIso.ofComponents
      (fun S ↦ (D.resolutionCube hD R j).mapIso (eqToIso (resolveCrossingVertex_false c S)))
      fun _ ↦ by
        simp only [Functor.comp_map, Functor.mapIso_hom, ← Functor.map_comp]
        exact congrArg _ (Subsingleton.elim _ _)

/-! ### The saddle map at a crossing -/

/-- **The saddle map at a crossing**, as a map of cubes from the cube of resolutions of
`D.resolveCrossing c true` in quantum degree `j` to the cube of resolutions of
`D.resolveCrossing c false` in quantum degree `j - 1`. Under the identifications of these cubes
with the two faces of the cube of resolutions of `D` at `c`, it is given by the edges of the cube
of `D` in the direction of `c`, which are the saddle maps of `D` at `c`
(`TauCeti.PDCode.resolveCrossingSaddle_app_comp_resolutionCubeι`). -/
def resolveCrossingSaddle :
    (D.resolveCrossing c true).resolutionCube (hD.resolveCrossing _ c true) R j ⟶
      (D.resolveCrossing c false).resolutionCube (hD.resolveCrossing _ c false) R (j - 1) :=
  (D.resolveCrossingFaceZeroIso c hD R j).hom ≫ (D.resolutionCube hD R j).cubeFaceMapAt c ≫
    (D.resolveCrossingFaceOneIso c hD R j).inv

/-- The component of the saddle map at the vertex `S`, read through the identifications of the
two cubes with the faces of the cube of `D`, is the edge map of the cube of `D` from the vertex
over `S` on the `A`-face to the vertex over `S` on the `B`-face. -/
@[reassoc]
theorem resolveCrossingSaddle_app (S : Finset (Fin n)) :
    (D.resolveCrossingSaddle c hD R j).app S =
      (D.resolveCrossingCubeIso c true hD (hD.resolveCrossing _ c true) R (j := j) (j' := j)
          (by simp)).hom.app S ≫
        (D.resolutionCube hD R j).map (homOfLE (resolveCrossingVertex_true_subset_false c S)) ≫
          (D.resolveCrossingCubeIso c false hD (hD.resolveCrossing _ c false) R (j := j)
            (j' := j - 1) (by simp)).inv.app S := by
  simp only [resolveCrossingSaddle, resolveCrossingFaceZeroIso, resolveCrossingFaceOneIso,
    NatTrans.comp_app, Iso.trans_hom, Iso.trans_inv, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.cubeFaceMapAt_app, Category.assoc, ← Functor.map_comp_assoc]
  -- The two composites of morphisms of the preorder category of subsets agree.
  congr 3

/-- **The saddle map at a crossing is the saddle map of `D`.** Reindexing the circle tensors of
the two resolutions at the vertex `S` along `TauCeti.PDCode.resolveCrossingCubeCircleEquiv`, the
component of `TauCeti.PDCode.resolveCrossingSaddle` at `S` is the saddle map
`TauCeti.PDCode.resolutionEdgeMap` of `D` at `c`, between the states of the vertices over `S`
on the two faces: it merges the two circles through `c` or splits the circle through `c`. -/
theorem resolveCrossingSaddle_app_comp_resolutionCubeι (S : Finset (Fin n))
    (hst : ∀ i, i ≠ c → cubeState (resolveCrossingVertex c true S) i =
      cubeState (resolveCrossingVertex c false S) i)
    (hc : cubeState (resolveCrossingVertex c true S) c ≠
      cubeState (resolveCrossingVertex c false S) c)
    (h : #(D.circlesAt (cubeState (resolveCrossingVertex c true S)) c) = 2 ∨
      #(D.circlesAt (cubeState (resolveCrossingVertex c false S)) c) = 2) :
    (D.resolveCrossingSaddle c hD R j).app S ≫
        (D.resolveCrossing c false).resolutionCubeι (hD.resolveCrossing _ c false) R (j - 1) S ≫
          ModuleCat.ofHom
            (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingCubeCircleEquiv c false S)).toLinearMap =
      (D.resolveCrossing c true).resolutionCubeι (hD.resolveCrossing _ c true) R j S ≫
        ModuleCat.ofHom
          (reindex R (fun _ ↦ R[ε]) (D.resolveCrossingCubeCircleEquiv c true S)).toLinearMap ≫
          ModuleCat.ofHom (D.resolutionEdgeMap hst hc h R) := by
  rw [resolveCrossingSaddle_app, Category.assoc, Category.assoc,
    ← D.resolveCrossingCubeIso_hom_app_comp_resolutionCubeι c false hD
      (hD.resolveCrossing _ c false) R (j := j) (j' := j - 1) (by simp) S,
    Iso.inv_hom_id_app_assoc,
    D.resolutionCube_map_homOfLE_comp_resolutionCubeι hD R j (a := c) (by simp) (by simp) _ hst hc
      h,
    D.resolveCrossingCubeIso_hom_app_comp_resolutionCubeι_assoc c true hD
      (hD.resolveCrossing _ c true) R (j := j) (j' := j) (by simp) S]

/-! ### The mapping cone -/

/-- **The skein mapping cone of the unnormalized Khovanov complex.** For a crossing `c` of a
planar code `D`, the mapping cone of the cochain map `⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ⁻¹` induced by the saddle
map `TauCeti.PDCode.resolveCrossingSaddle` is the degree-`j` component of the unnormalized
Khovanov complex `⟦D⟧` shifted by one, where `D_A` and `D_B` are the resolutions of `D` at `c`.
A vertex of `⟦D_A⟧` is sent to the vertex over it in `⟦D⟧`
(`TauCeti.PDCode.inl_v_khovanovBracketMappingConeIso_hom_f`), and a vertex `S` of `⟦D_B⟧` to the
vertex over it with the sign `-(-1) ^ #{a ∈ S | a.castSucc < c}`
(`TauCeti.PDCode.inr_f_khovanovBracketMappingConeIso_hom_f`). -/
def khovanovBracketMappingConeIso :
    mappingCone (NatTrans.cubeComplexMap (D.resolveCrossingSaddle c hD R j)) ≅
      (D.khovanovBracket hD R j)⟦(1 : ℤ)⟧ :=
  mappingCone.mapIso (φ₂ := NatTrans.cubeComplexMap ((D.resolutionCube hD R j).cubeFaceMapAt c))
      ((cubeComplexFunctor _ _).mapIso (D.resolveCrossingFaceZeroIso c hD R j))
      ((cubeComplexFunctor _ _).mapIso (D.resolveCrossingFaceOneIso c hD R j))
      (by simp [resolveCrossingSaddle, ← NatTrans.cubeComplexMap_comp]) ≪≫
    (D.resolutionCube hD R j).cubeComplexMappingConeIsoAt c ≪≫
    (CategoryTheory.shiftFunctor _ (1 : ℤ)).mapIso (eqToIso (D.khovanovBracket_apply hD R j).symm)

/-- The isomorphism `TauCeti.PDCode.khovanovBracketMappingConeIso` sends a vertex `S` of `⟦D_A⟧`,
placed in the mapping cone by `mappingCone.inl`, to the vertex over `S` in `⟦D⟧`, by the
identification `TauCeti.PDCode.resolveCrossingCubeIso` of the cube of `D_A` with the `A`-face of
the cube of `D`. -/
@[reassoc]
theorem inl_v_khovanovBracketMappingConeIso_hom_f (p : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = p + 1}) :
    ((D.resolveCrossing c true).resolutionCube (hD.resolveCrossing _ c true) R j).cubeComplexι S ≫
        (mappingCone.inl (NatTrans.cubeComplexMap (D.resolveCrossingSaddle c hD R j))).v (p + 1) p
          (by omega) ≫
          (D.khovanovBracketMappingConeIso c hD R j).hom.f p =
      (D.resolveCrossingCubeIso c true hD (hD.resolveCrossing _ c true) R (j := j) (j' := j)
          (by simp)).hom.app S.1 ≫
        (D.resolutionCube hD R j).cubeComplexι (r := p + 1)
          ⟨resolveCrossingVertex c true S.1, by simp [S.2]⟩ ≫
          eqToHom (by rw [CochainComplex.shiftFunctor_obj_X', khovanovBracket_apply]) := by
  dsimp only [khovanovBracketMappingConeIso, cubeComplexFunctor, Functor.mapIso]
  simp [resolveCrossingFaceZeroIso, eqToHom_map, Functor.eqToHom_comp_cubeComplexι_assoc]

/-- The isomorphism `TauCeti.PDCode.khovanovBracketMappingConeIso` sends a vertex `S` of `⟦D_B⟧`,
placed in the mapping cone by `mappingCone.inr`, to the vertex over `S` in `⟦D⟧`, by the
identification `TauCeti.PDCode.resolveCrossingCubeIso` of the cube of `D_B` with the `B`-face of
the cube of `D`, with the sign `-(-1) ^ #{a ∈ S | a.castSucc < c}`. -/
@[reassoc]
theorem inr_f_khovanovBracketMappingConeIso_hom_f (p : ℤ)
    (S : {S : Finset (Fin n) // (#S : ℤ) = p}) :
    ((D.resolveCrossing c false).resolutionCube (hD.resolveCrossing _ c false) R
        (j - 1)).cubeComplexι S ≫
        (mappingCone.inr (NatTrans.cubeComplexMap (D.resolveCrossingSaddle c hD R j))).f p ≫
          (D.khovanovBracketMappingConeIso c hD R j).hom.f p =
      -((-1 : ℤ) ^ #{a ∈ S.1 | a.castSucc < c} •
        (D.resolveCrossingCubeIso c false hD (hD.resolveCrossing _ c false) R (j := j)
            (j' := j - 1) (by simp)).hom.app S.1 ≫
          (D.resolutionCube hD R j).cubeComplexι (r := p + 1)
            ⟨resolveCrossingVertex c false S.1, by simp [S.2]⟩ ≫
            eqToHom (by rw [CochainComplex.shiftFunctor_obj_X', khovanovBracket_apply])) := by
  dsimp only [khovanovBracketMappingConeIso, cubeComplexFunctor, Functor.mapIso]
  simp [resolveCrossingFaceOneIso, eqToHom_map, Functor.eqToHom_comp_cubeComplexι_assoc]

/-! ### The skein triangle -/

/-- **The skein triangle** `⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ⁻¹ ⟶ ⟦D⟧ʲ⟦1⟧ ⟶ ⟦D_A⟧ʲ⟦1⟧` of a crossing `c` of a
planar code `D`, whose first map is the saddle map at `c`. It is the standard triangle of the
mapping cone of the saddle map, with the mapping cone replaced by `⟦D⟧ʲ⟦1⟧` along
`TauCeti.PDCode.khovanovBracketMappingConeIso`; its image in the homotopy category is
distinguished (`TauCeti.PDCode.khovanovBracketSkeinTriangle_distinguished`). -/
@[expose, simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
def khovanovBracketSkeinTriangle : Pretriangulated.Triangle (CochainComplex (ModuleCat.{u} R) ℤ) :=
  Pretriangulated.Triangle.mk (NatTrans.cubeComplexMap (D.resolveCrossingSaddle c hD R j))
    (mappingCone.inr _ ≫ (D.khovanovBracketMappingConeIso c hD R j).hom)
    ((D.khovanovBracketMappingConeIso c hD R j).inv ≫ (mappingCone.triangle _).mor₃)

/-- The skein triangle is isomorphic to the standard triangle of the mapping cone of the saddle
map. -/
def khovanovBracketSkeinTriangleIso :
    D.khovanovBracketSkeinTriangle c hD R j ≅
      mappingCone.triangle (NatTrans.cubeComplexMap (D.resolveCrossingSaddle c hD R j)) :=
  Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (D.khovanovBracketMappingConeIso c hD R j).symm (by simp [khovanovBracketSkeinTriangle])
    (by simp [khovanovBracketSkeinTriangle]) (by simp [khovanovBracketSkeinTriangle])

/-- **The skein triangle is distinguished.** In the homotopy category, the triangle
`⟦D_A⟧ʲ ⟶ ⟦D_B⟧ʲ⁻¹ ⟶ ⟦D⟧ʲ⟦1⟧ ⟶ ⟦D_A⟧ʲ⟦1⟧` formed by the saddle map at a crossing `c` of a planar
code `D` is distinguished. Applying a homological functor such as homology gives the skein long
exact sequence of the unnormalized Khovanov complex. -/
theorem khovanovBracketSkeinTriangle_distinguished :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).mapTriangle.obj
        (D.khovanovBracketSkeinTriangle c hD R j) ∈ distTriang _ :=
  Pretriangulated.isomorphic_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished _) _
    ((HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (D.khovanovBracketSkeinTriangleIso c hD R j))

end TauCeti.PDCode
