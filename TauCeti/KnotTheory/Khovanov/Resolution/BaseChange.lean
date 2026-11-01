/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.KnotTheory.Khovanov.BaseChange
public import TauCeti.KnotTheory.Khovanov.Resolution.Cube

/-!
# Coefficient change for the Khovanov cube of resolutions

Let `f : R →+* S` be a map of commutative rings in a common universe and `D` a planar PD-code.
Extending scalars along `f` in the degree-`j` cube of resolutions of `D` over `R` gives the
degree-`j` cube of resolutions over `S`: `TauCeti.PDCode.resolutionCubeBaseChangeIso` is a
natural isomorphism of cubes `Finset (Fin n) ⥤ ModuleCat S`. Its component at a vertex is the
comparison of quantum pieces `TauCeti.Khovanov.circlePieceBaseChange`, which preserves the
enhanced-state basis, and its naturality is the compatibility of every saddle edge map with
scalar extension, `TauCeti.PDCode.circleBaseChange_resolutionEdgeMap`. The comparison involves
no sign and no choice. Since the Khovanov bracket is the signed totalization of these cubes, this
is the cube-level input for identifying the bracket over `S` with the scalar extension of the
bracket over `R`, for instance over `ℤ`.

## Main results

* `TauCeti.PDCode.circleBaseChange_resolutionEdgeMap`: scalar extension commutes with the
  merge or split map along a saddle edge.
* `TauCeti.PDCode.resolutionCubeBaseChangeIso`: the cube of resolutions over `R` with scalars
  extended to `S` is isomorphic to the cube of resolutions over `S`.
* `TauCeti.PDCode.resolutionCubeι_resolutionCubeBaseChangeIso_hom_app_tmul`: on each vertex,
  the isomorphism is scalar extension of the underlying circle tensor.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Finset TensorProduct

namespace TauCeti.PDCode

universe u v w

section Edge

variable {n : ℕ} (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (h : #(D.circlesAt s c) = 2 ∨ #(D.circlesAt t c) = 2)
  {R : Type v} {S : Type w} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Scalar extension commutes with the saddle map along an edge of the cube of resolutions,
both when it merges two circles and when it splits one. -/
theorem circleBaseChange_resolutionEdgeMap
    (x : S ⊗[R] Khovanov.CircleTensor R (D.ResolvedCircle s)) :
    Khovanov.circleBaseChange R S _ ((D.resolutionEdgeMap hst hc h R).baseChange S x) =
      D.resolutionEdgeMap hst hc h S (Khovanov.circleBaseChange R S _ x) := by
  by_cases hs : #(D.circlesAt s c) = 2
  · rw [D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h R hs,
      D.resolutionEdgeMap_eq_resolutionMergeMap hst hc h S hs, resolutionMergeMap_def,
      resolutionMergeMap_def, AlgHom.toLinearMap_apply]
    exact Khovanov.circleBaseChange_fiberwiseMul _ x
  · have ht := h.resolve_left hs
    rw [D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h R ht,
      D.resolutionEdgeMap_eq_resolutionSplitMap hst hc h S ht, resolutionSplitMap_def,
      resolutionSplitMap_def]
    exact Khovanov.circleBaseChange_fiberwiseSplit _ x

end Edge

section Cube

variable {n : ℕ} (D : PDCode n) (hD : D.IsPlanar) {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (j : ℤ)

/-- The component at the vertex `T` of the comparison of cubes of resolutions: scalar
extension of the degree `j - |T|` piece of the circle tensor of the resolution of `T`. -/
private def resolutionCubeBaseChangeApp (T : Finset (Fin n)) :
    (D.resolutionCube hD R j ⋙ ModuleCat.extendScalars f).obj T ≅
      (D.resolutionCube hD S j).obj T :=
  letI := f.toAlgebra
  ((D.resolutionCubeVertexEquiv hD R j T).baseChange R S ≪≫ₗ
    Khovanov.circlePieceBaseChange R S (D.ResolvedCircle (cubeState T)) (j - #T) ≪≫ₗ
      (D.resolutionCubeVertexEquiv hD S j T).symm).toModuleIso

private theorem resolutionCubeι_resolutionCubeBaseChangeApp_tmul (T : Finset (Fin n)) (a : S)
    (x : (D.resolutionCube hD R j).obj T) :
    letI := f.toAlgebra
    D.resolutionCubeι hD S j T ((resolutionCubeBaseChangeApp D hD f j T).hom (a ⊗ₜ[R] x)) =
      Khovanov.circleBaseChange R S _ (a ⊗ₜ[R] D.resolutionCubeι hD R j T x) := by
  let := f.toAlgebra
  -- The component is, by definition, scalar extension of the vertex identified with its piece.
  calc _ = D.resolutionCubeι hD S j T ((D.resolutionCubeVertexEquiv hD S j T).symm
        (Khovanov.circlePieceBaseChange R S _ _
          (a ⊗ₜ[R] D.resolutionCubeVertexEquiv hD R j T x))) := (rfl)
    _ = _ := by
      rw [← coe_resolutionCubeVertexEquiv, LinearEquiv.apply_symm_apply,
        Khovanov.subtype_circlePieceBaseChange, LinearMap.baseChange_tmul,
        Submodule.subtype_apply, coe_resolutionCubeVertexEquiv]

/-- The vertex comparisons are natural along each edge `T ⋖ U` of the cube, because scalar
extension commutes with the saddle map along that edge. -/
private theorem resolutionCubeBaseChangeApp_naturality {T U : Finset (Fin n)} (h : T ⋖ U) :
    (D.resolutionCube hD R j ⋙ ModuleCat.extendScalars f).map (homOfLE h.le) ≫
        (resolutionCubeBaseChangeApp D hD f j U).hom =
      (resolutionCubeBaseChangeApp D hD f j T).hom ≫
        (D.resolutionCube hD S j).map (homOfLE h.le) := by
  let := f.toAlgebra
  obtain ⟨a, ha, rfl⟩ := Finset.covBy_iff_exists_insert.mp h
  rw [← cancel_mono (D.resolutionCubeι hD S j (insert a T))]
  refine ModuleCat.ExtendScalars.hom_ext fun x ↦ ?_
  -- Along the edge, both routes send `1 ⊗ x` to the scalar extension of the saddle map at `a`
  -- applied to `x`.
  have hR := congr($(D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD R j ha) x)
  have hS := congr($(D.resolutionCube_map_homOfLE_insert_comp_resolutionCubeι hD S j ha)
    ((resolutionCubeBaseChangeApp D hD f j T).hom ((1 : S) ⊗ₜ[R] x)))
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.ofHom_apply] at hR hS
  -- `ModuleCat.ExtendScalars.hom_ext` states the goal on `1 ⊗ₜ[R] x` with `S` as the left
  -- factor, not `(ModuleCat.restrictScalars f).obj S`, so `ModuleCat.comp_apply` and
  -- `ModuleCat.ExtendScalars.map_tmul` do not rewrite it: the goal is not type-correct at
  -- instance transparency. The outer calc steps unfold the composites, and the functor
  -- `(D.resolutionCube hD R j ⋙ ModuleCat.extendScalars f).map g`, which sends `1 ⊗ x` to
  -- `1 ⊗ (D.resolutionCube hD R j).map g x`, by `rfl`.
  calc _ = D.resolutionCubeι hD S j (insert a T)
        ((resolutionCubeBaseChangeApp D hD f j (insert a T)).hom
          ((1 : S) ⊗ₜ[R] (D.resolutionCube hD R j).map (homOfLE h.le) x)) := (rfl)
    _ = D.resolutionCubeι hD S j (insert a T) ((D.resolutionCube hD S j).map (homOfLE h.le)
          ((resolutionCubeBaseChangeApp D hD f j T).hom ((1 : S) ⊗ₜ[R] x))) := by
      rw [resolutionCubeι_resolutionCubeBaseChangeApp_tmul, hR, hS,
        resolutionCubeι_resolutionCubeBaseChangeApp_tmul, ← circleBaseChange_resolutionEdgeMap,
        LinearMap.baseChange_tmul]
    _ = _ := (rfl)

/-- **Coefficient change for the cube of resolutions.** Extending scalars along `f : R →+* S`
in the degree-`j` cube of resolutions of a planar code over `R` gives the degree-`j` cube of
resolutions over `S`. At each vertex this is the scalar extension of the quantum piece of the
circle tensor, preserving the enhanced-state basis. -/
def resolutionCubeBaseChangeIso :
    D.resolutionCube hD R j ⋙ ModuleCat.extendScalars f ≅ D.resolutionCube hD S j :=
  NatIso.ofComponents (resolutionCubeBaseChangeApp D hD f j)
    fun g ↦ by
      simpa only [NatTrans.ofCubeEdges_app] using
        (NatTrans.ofCubeEdges (fun T ↦ (resolutionCubeBaseChangeApp D hD f j T).hom)
          fun _ _ h ↦ resolutionCubeBaseChangeApp_naturality D hD f j h).naturality g

/-- On the vertex `T`, the comparison of cubes of resolutions sends `a ⊗ x` to the scalar
extension of `a ⊗ x` in the circle tensor of the resolution of `T` over `S`. This determines the
comparison, since the inclusion of the vertex into the circle tensor is injective. -/
theorem resolutionCubeι_resolutionCubeBaseChangeIso_hom_app_tmul (T : Finset (Fin n)) (a : S)
    (x : (D.resolutionCube hD R j).obj T) :
    letI := f.toAlgebra
    D.resolutionCubeι hD S j T ((D.resolutionCubeBaseChangeIso hD f j).hom.app T (a ⊗ₜ[R] x)) =
      Khovanov.circleBaseChange R S _ (a ⊗ₜ[R] D.resolutionCubeι hD R j T x) :=
  D.resolutionCubeι_resolutionCubeBaseChangeApp_tmul hD f j T a x

end Cube

end TauCeti.PDCode
