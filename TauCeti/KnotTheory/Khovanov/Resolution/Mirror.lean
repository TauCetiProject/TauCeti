/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.Dual
public import TauCeti.KnotTheory.Khovanov.Resolution.Cube

/-!
# The cube of resolutions of the mirror diagram

Mirroring a PD-code `D` with `n` crossings exchanges the over- and under-strands, hence the `A`-
and `B`-smoothings at every crossing: the vertex `S` of the cube of resolutions of `D.mirror` has
the same resolved circles as the complementary vertex `Sᶜ` of the cube of `D`, and an edge
`S ⟶ S ∪ {a}` of the mirror cube runs backwards along the edge `Sᶜ \ {a} ⟶ Sᶜ` of the cube of
`D`, so a merge of `D` becomes a split of `D.mirror` and conversely.

The Frobenius pairing of circle tensors identifies these reversed cubes. It is perfect between
the quantum pieces of degrees `p` and `-p` (`TauCeti.Khovanov.circlePieceDuality`), and a merge
is adjoint to the split in the opposite direction
(`TauCeti.PDCode.circleDuality_resolutionEdgeMap`). Since the vertex `S` of the degree-`j` cube
of `D.mirror` is the degree `j - |S|` piece of the circle tensor, and the vertex `Sᶜ` of the
degree-`(n - j)` cube of `D` is the degree `(n - j) - (n - |S|) = -(j - |S|)` piece, the pairing
is a natural isomorphism from the degree-`j` cube of resolutions of `D.mirror` to the dual cube
(`CategoryTheory.Functor.dualCube`) of the degree-`(n - j)` cube of resolutions of `D`,
`TauCeti.PDCode.mirrorResolutionCubeIso`. Totalizing, the unnormalized Khovanov complex of the
mirror in quantum degree `j` is the signed totalization of this dual cube
(`TauCeti.PDCode.mirrorKhovanovBracketIso`). This is the cube-level form of the duality between
the Khovanov homology of a link and that of its mirror image.

## Main definitions

All in the namespace `TauCeti.PDCode`:

* `mirrorResolutionCubeIso D hD R j`: the isomorphism from the degree-`j` cube of resolutions of
  `D.mirror` to the dual cube of the degree-`(n - j)` cube of resolutions of `D`, characterized by
  `mirrorResolutionCubeIso_hom_app_apply`.
* `mirrorKhovanovBracketIso D hD R j`: the induced isomorphism from the degree-`j` component of
  the unnormalized Khovanov complex of `D.mirror` to the totalization of that dual cube.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.
-/

public section

noncomputable section

open CategoryTheory Finset PiTensorProduct DualNumber

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n) (hD : D.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The vertex `S` of the degree-`j` mirror cube, carried to the degree `j - |S|` piece of the
circle tensor of the resolution of `D` at `Sᶜ`. -/
private def mirrorVertexEquiv (S : Finset (Fin n)) :
    (D.mirror.resolutionCube ((isPlanar_mirror D).2 hD) R j).obj S ≃ₗ[R]
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState Sᶜ))).piece (j - #S) :=
  (LinearEquiv.ofInjective _ (D.mirror.resolutionCubeι_injective _ R j S)).trans <|
    (LinearEquiv.ofEq _ _ (D.mirror.range_resolutionCubeι _ R j S)).trans <|
      (reindex R (fun _ ↦ R[ε])
        (SmoothingEquiv.mirror D (cubeState_compl S)).symm.resolvedCircleCongr).ofSubmodules _ _
        (Khovanov.map_reindex_circleQuantumGrading_piece _ _)

/-- The vertex `Sᶜ` of the degree-`(n - j)` cube of `D`, as the degree `-(j - |S|)` piece of
the circle tensor of its resolution. -/
private def complVertexEquiv (S : Finset (Fin n)) :
    (D.resolutionCube hD R (n - j)).obj Sᶜ ≃ₗ[R]
      (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState Sᶜ))).piece (-(j - #S)) :=
  (LinearEquiv.ofInjective _ (D.resolutionCubeι_injective hD R _ Sᶜ)).trans <|
    LinearEquiv.ofEq _ _ (by
      -- The quantum degree `(n - j) - |Sᶜ|` of the vertex `Sᶜ` is opposite to `j - |S|`.
      rw [range_resolutionCubeι]
      congr 1
      have h := card_compl_add_card S
      rw [Fintype.card_fin] at h
      omega)

/-- The vertex isomorphism of `mirrorResolutionCubeIso`: the Frobenius pairing of the vertex `S`
of the mirror cube with the complementary vertex `Sᶜ` of the cube of `D`. -/
private def mirrorResolutionCubeLinearEquiv (S : Finset (Fin n)) :
    (D.mirror.resolutionCube ((isPlanar_mirror D).2 hD) R j).obj S ≃ₗ[R]
      Module.Dual R ((D.resolutionCube hD R (n - j)).obj Sᶜ) :=
  (mirrorVertexEquiv D hD R j S).trans <|
    (Khovanov.circlePieceDuality R _ (j - #S)).trans (complVertexEquiv D hD R j S).dualMap

private theorem mirrorResolutionCubeLinearEquiv_apply (S : Finset (Fin n))
    (x : (D.mirror.resolutionCube ((isPlanar_mirror D).2 hD) R j).obj S)
    (y : (D.resolutionCube hD R (n - j)).obj Sᶜ) :
    mirrorResolutionCubeLinearEquiv D hD R j S x y =
      Khovanov.circleDuality R _ (reindex R (fun _ ↦ R[ε])
        (SmoothingEquiv.mirror D (cubeState_compl S)).symm.resolvedCircleCongr
          ((D.mirror.resolutionCubeι _ R j S).hom x))
        ((D.resolutionCubeι hD R (n - j) Sᶜ).hom y) := by
  simp [mirrorResolutionCubeLinearEquiv, mirrorVertexEquiv, complVertexEquiv,
    LinearEquiv.dualMap_apply]

/-- The vertex isomorphisms commute with the edge maps: along an edge `S ⋖ T` of the mirror cube,
the saddle map of `D.mirror` is the transpose of the saddle map of `D` along `Tᶜ ⋖ Sᶜ`. -/
private theorem mirrorResolutionCubeLinearEquiv_naturality {S T : Finset (Fin n)} (h : S ⋖ T) :
    (D.mirror.resolutionCube ((isPlanar_mirror D).2 hD) R j).map (homOfLE h.le) ≫
        (mirrorResolutionCubeLinearEquiv D hD R j T).toModuleIso.hom =
      (mirrorResolutionCubeLinearEquiv D hD R j S).toModuleIso.hom ≫
        (D.resolutionCube hD R (n - j)).dualCube.map (homOfLE h.le) := by
  obtain ⟨a, haS, rfl⟩ := h.exists_finset_insert
  have hD' := (isPlanar_mirror D).2 hD
  -- The edge `S ⋖ insert a S` of the mirror cube, at the crossing `a`.
  have hst := cubeState_eq_of_covBy (covBy_insert haS) haS (mem_insert_self a S)
  have hc := cubeState_ne_of_notMem_of_mem haS (mem_insert_self a S)
  have hsad := hD'.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst hc
  -- The edge `(insert a S)ᶜ ⋖ Sᶜ` of the cube of `D`, at the same crossing.
  have hst' : ∀ i, i ≠ a → cubeState (insert a S)ᶜ i = cubeState Sᶜ i := fun i hi ↦ by
    rw [cubeState_compl, cubeState_compl, hst i hi]
  have hc' : cubeState (insert a S)ᶜ a ≠ cubeState Sᶜ a := by
    rw [cubeState_compl, cubeState_compl]
    exact fun h ↦ hc (Bool.not_inj h).symm
  have hsad' := hD.card_circlesAt_eq_two_or_card_circlesAt_eq_two hst' hc'
  -- The edge maps of the two cubes, on the underlying circle tensors.
  have hx (x) := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (D.mirror.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD' R j haS)) x
  have hy (y) := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (D.resolutionCube_map_homOfLE_comp_resolutionCubeι hD R (n - j)
      (by simp : a ∉ (insert a S)ᶜ) (insert_compl_insert haS)
      (compl_subset_compl.2 (subset_insert a S)) hst' hc' hsad')) y
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply] at hx hy
  -- Transport the saddle map of the mirror to the reversed saddle map of `D`.
  have hreindex := SmoothingEquiv.reindex_resolutionEdgeMap
    (SmoothingEquiv.mirror D (cubeState_compl S)).symm
    (SmoothingEquiv.mirror D (cubeState_compl (insert a S))).symm (by simp) (by simp)
    (Equiv.refl _) (fun _ ↦ by simp) hst hc (fun i hi ↦ (hst' i hi).symm) hc'.symm hsad
    hsad'.symm R
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
    LinearMap.dualMap_apply, mirrorResolutionCubeLinearEquiv_apply]
  rw [hx, hreindex, circleDuality_resolutionEdgeMap, hy]

/-- **The cube of resolutions of the mirror is the dual cube.** For a planar code `D` with `n`
crossings, the Frobenius pairing of circle tensors is a natural isomorphism from the degree-`j`
cube of resolutions of `D.mirror` to the dual cube of the degree-`(n - j)` cube of resolutions of
`D`: the vertex `S` of the mirror cube is paired with the complementary vertex `Sᶜ` of the cube
of `D`, whose resolution has the same circles. -/
def mirrorResolutionCubeIso :
    D.mirror.resolutionCube ((isPlanar_mirror D).2 hD) R j ≅
      (D.resolutionCube hD R (n - j)).dualCube :=
  NatIso.ofComponents (fun S ↦ (mirrorResolutionCubeLinearEquiv D hD R j S).toModuleIso)
    fun f ↦ by
      -- Naturality along every inclusion follows from naturality along the edges.
      simpa only [NatTrans.ofCubeEdges_app] using (NatTrans.ofCubeEdges
        (F := D.mirror.resolutionCube _ R j) (G := (D.resolutionCube hD R (n - j)).dualCube)
        (fun S ↦ (mirrorResolutionCubeLinearEquiv D hD R j S).toModuleIso.hom)
        fun _ _ h ↦ mirrorResolutionCubeLinearEquiv_naturality D hD R j h).naturality f

/-- The isomorphism from the mirror cube to the dual cube pairs an element `x` of the vertex `S`
of the mirror cube with an element `y` of the vertex `Sᶜ` of the cube of `D` by the Frobenius
pairing of circle tensors, after identifying the circles of the two resolutions. -/
@[simp]
theorem mirrorResolutionCubeIso_hom_app_apply (S : Finset (Fin n))
    (x : (D.mirror.resolutionCube ((isPlanar_mirror D).2 hD) R j).obj S)
    (y : (D.resolutionCube hD R (n - j)).obj Sᶜ) :
    ((D.mirrorResolutionCubeIso hD R j).hom.app S).hom x y =
      Khovanov.circleDuality R _ (reindex R (fun _ ↦ R[ε])
        (SmoothingEquiv.mirror D (cubeState_compl S)).symm.resolvedCircleCongr
          ((D.mirror.resolutionCubeι _ R j S).hom x))
        ((D.resolutionCubeι hD R (n - j) Sᶜ).hom y) := by
  simp [mirrorResolutionCubeIso, mirrorResolutionCubeLinearEquiv_apply]

/-- **The unnormalized Khovanov complex of the mirror** of a planar code `D` with `n` crossings,
in quantum degree `j`, is the signed totalization of the dual cube of the degree-`(n - j)` cube of
resolutions of `D`. -/
def mirrorKhovanovBracketIso :
    D.mirror.khovanovBracket ((isPlanar_mirror D).2 hD) R j ≅
      (D.resolutionCube hD R (n - j)).dualCube.cubeComplex :=
  eqToIso (D.mirror.khovanovBracket_apply _ R j) ≪≫
    (cubeComplexFunctor (ModuleCat.{u} R) (Fin n)).mapIso (D.mirrorResolutionCubeIso hD R j)

/-- The isomorphism of unnormalized complexes is induced by the isomorphism of cubes. -/
theorem mirrorKhovanovBracketIso_hom :
    (D.mirrorKhovanovBracketIso hD R j).hom =
      eqToHom (D.mirror.khovanovBracket_apply _ R j) ≫
        NatTrans.cubeComplexMap (D.mirrorResolutionCubeIso hD R j).hom :=
  (rfl)

/-- The inverse isomorphism of unnormalized complexes is induced by the inverse isomorphism of
cubes. -/
theorem mirrorKhovanovBracketIso_inv :
    (D.mirrorKhovanovBracketIso hD R j).inv =
      NatTrans.cubeComplexMap (D.mirrorResolutionCubeIso hD R j).inv ≫
        eqToHom (D.mirror.khovanovBracket_apply _ R j).symm :=
  (rfl)

end TauCeti.PDCode
