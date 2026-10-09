/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction

/-!
# The action on an affine toric scheme

The grading coaction on the coordinate ring of an affine toric chart induces a morphism from
the product of the dense torus and the chart to the chart. We construct this morphism using the
standard comparison between a fibre product of affine schemes and the spectrum of a tensor
product, then package it as a morphism of schemes over `Spec ℂ`.

On the zero cone, the action morphism agrees with multiplication on the dense torus. The counit
and coassociativity identities for the underlying coordinate-ring coaction are proved in
`TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction`.
The action is equivariant under maps of lattice cones, in particular under face inclusions.

## Main declarations

* `TauCeti.Toric.affineToricSchemeAction`: the action morphism on an affine toric chart.
* `TauCeti.Toric.affineToricSchemeActionOver`: the action as a morphism over `Spec ℂ`.
* `TauCeti.Toric.affineToricSchemeAction_bot`: on the zero cone, the action is torus
  multiplication.
* `TauCeti.Toric.affineToricSchemeActionOver_comp_map` and `_comp_face`: equivariance
  under toric maps and face inclusions over `Spec ℂ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonObj MonoidalCategory TensorProduct

namespace TauCeti.Toric

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The action of the dense torus on the affine toric scheme of a cone. Its source is the
fibre product over `Spec ℂ`, identified with the spectrum of the tensor product of coordinate
rings, and its comorphism is `affineCoordinateRingCoaction`. -/
noncomputable def affineToricSchemeAction (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) ⟶
      affineToricScheme hi σ :=
  (pullbackSpecIso ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
      (affineCoordinateRing hi σ)).hom ≫
    Spec.map (CommRingCat.ofHom (affineCoordinateRingCoaction hi σ).toRingHom)

/-- The affine toric action is `Spec` of the coordinate-ring coaction after the canonical
comparison of the fibre product with the spectrum of the tensor product. -/
theorem affineToricSchemeAction_def (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    affineToricSchemeAction hi σ =
      (pullbackSpecIso ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
          (affineCoordinateRing hi σ)).hom ≫
        Spec.map (CommRingCat.ofHom (affineCoordinateRingCoaction hi σ).toRingHom) :=
  (rfl)

/-- The affine toric action, packaged as a morphism of schemes over `Spec ℂ`. -/
noncomputable def affineToricSchemeActionOver (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    (denseTorusScheme hi).asOver (Spec (.of ℂ)) ⊗
        (affineToricScheme hi σ).asOver (Spec (.of ℂ)) ⟶
      (affineToricScheme hi σ).asOver (Spec (.of ℂ)) := by
  refine Over.homMk (affineToricSchemeAction hi σ) ?_
  -- The tensor product in `Over` is the chosen pullback, so unfold its structure maps to state
  -- compatibility of the underlying action morphism with the maps to `Spec ℂ`.
  change affineToricSchemeAction hi σ ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ))) =
    pullback.fst
        (Spec.map (CommRingCat.ofHom
          (algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing hi σ)))) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V))))
  rw [affineToricSchemeAction_def, Category.assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (affineCoordinateRingCoaction hi σ).toRingHom.comp
      (algebraMap ℂ (affineCoordinateRing hi σ)) =
    algebraMap ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V) ⊗[ℂ]
      affineCoordinateRing hi σ) := by
    ext z
    simp
  rw [h]
  exact pullbackSpecIso_hom_base ℂ
    (affineCoordinateRing hi (⊥ : PointedCone ℝ V)) (affineCoordinateRing hi σ)

/-- The underlying scheme morphism of the bundled affine toric action is
`affineToricSchemeAction`. -/
@[simp]
theorem affineToricSchemeActionOver_left (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    (affineToricSchemeActionOver hi σ).left = affineToricSchemeAction hi σ := by
  rw [affineToricSchemeActionOver]
  exact Over.homMk_left _ _

/-- On the zero cone, the affine toric action is multiplication on the dense torus. -/
@[simp]
theorem affineToricSchemeAction_bot (hi : IsIntegralLattice i) :
    affineToricSchemeAction hi (⊥ : PointedCone ℝ V) =
      μ[((denseTorusScheme hi).asOver (Spec (.of ℂ)))].left := by
  rw [affineToricSchemeAction_def, mul_spec_asOver_spec_left]
  congr 1
  exact congrArg Spec.map <| congrArg CommRingCat.ofHom <|
    congrArg AlgHom.toRingHom <| affineCoordinateRingCoaction_bot hi

/-- On the zero cone, the bundled affine toric action is the multiplication morphism. -/
@[simp]
theorem affineToricSchemeActionOver_bot (hi : IsIntegralLattice i) :
    affineToricSchemeActionOver hi (⊥ : PointedCone ℝ V) =
      μ[((denseTorusScheme hi).asOver (Spec (.of ℂ)))] := by
  ext
  simp

/-- Affine toric maps respect the complex base of the action. -/
instance affineToricSchemeMap_isOver
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    (affineToricSchemeMap hi hi' f g hfg hστ).IsOver (Spec (.of ℂ)) := by
  rw [affineToricSchemeMap_def]
  infer_instance

/-- Face inclusions respect the complex base of the action. -/
instance faceAffineToricSchemeMap_isOver (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ) :
    (faceAffineToricSchemeMap hi hτσ).IsOver (Spec (.of ℂ)) := by
  rw [faceAffineToricSchemeMap_def]
  infer_instance

/-- A map of lattice cones intertwines the affine torus actions, with its induced map on
dense tori in the first factor. The square is an equality of morphisms over `Spec ℂ`. -/
@[reassoc]
theorem affineToricSchemeActionOver_comp_map
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    affineToricSchemeActionOver hi σ ≫
        (affineToricSchemeMap hi hi' f g hfg hστ).asOver (Spec (.of ℂ)) =
      ((affineToricSchemeMap hi hi' f g hfg
          (σ := ⊥) (τ := ⊥) (by simp [Set.MapsTo])).asOver (Spec (.of ℂ)) ⊗ₘ
        (affineToricSchemeMap hi hi' f g hfg hστ).asOver (Spec (.of ℂ))) ≫
          affineToricSchemeActionOver hi' τ := by
  let R : CommRingCat := .of ℂ
  let F := algSpec R
  let : F.LaxMonoidal := (braidedAlgSpec (R := R)).toLaxBraided.toLaxMonoidal
  let a := (CommAlgCat.ofHom (R := R) (affineCoordinateRingCoaction hi σ)).op
  let b := (CommAlgCat.ofHom (R := R) (affineCoordinateRingCoaction hi' τ)).op
  let t := (CommAlgCat.ofHom (R := R) (affineCoordinateRingMap hi hi' f g hfg
    (σ := ⊥) (τ := ⊥) (by simp [Set.MapsTo]))).op
  let m := (CommAlgCat.ofHom (R := R) (affineCoordinateRingMap hi hi' f g hfg hστ)).op
  have h : (Functor.LaxMonoidal.μ F _ _ ≫ F.map a) ≫ F.map m =
      (F.map t ⊗ₘ F.map m) ≫ Functor.LaxMonoidal.μ F _ _ ≫ F.map b := by
    rw [Functor.LaxMonoidal.μ_natural_assoc, Category.assoc, ← F.map_comp, ← F.map_comp]
    congr 2
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    exact affineCoordinateRingCoaction_comp_map hi hi' f g hfg hστ
  have hl := congrArg (fun k ↦ k.left) h
  dsimp only [F] at hl
  simp only [Over.comp_left] at hl
  rw [μ_algSpec_left, μ_algSpec_left] at hl
  apply Over.OverMorphism.ext
  -- The comparison lemmas identify the monoidal structure map with `pullbackSpecIso`.
  -- The remaining projections forget the `Over` and algebra-to-`Under` packaging.
  simp only [Over.tensorObj_left, algSpec_obj_hom, algSpec_map_left, unop_tensorObj,
    Quiver.Hom.unop_op, commAlgCatEquivUnder_functor_map, AlgHom.toUnder,
    CommAlgCat.coe_tensorObj, ConcreteCategory.hom_ofHom, AlgHom.toRingHom_eq_coe,
    Under.homMk_right, Over.tensorHom_left, denseTorusScheme, affineToricScheme,
    Scheme.Hom.asOver, affineToricSchemeMap_def, Over.comp_left,
    affineToricSchemeActionOver_left, affineToricSchemeAction_def, OverClass.asOverHom_left,
    R, a, m, t, b] at hl ⊢
  convert hl using 1 <;> rfl

/-- Face inclusions are equivariant for the affine torus action over `Spec ℂ`. -/
@[reassoc]
theorem affineToricSchemeActionOver_comp_face (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ) :
    affineToricSchemeActionOver hi τ ≫
        (faceAffineToricSchemeMap hi hτσ).asOver (Spec (.of ℂ)) =
      (𝟙 ((denseTorusScheme hi).asOver (Spec (.of ℂ))) ⊗ₘ
        (faceAffineToricSchemeMap hi hτσ).asOver (Spec (.of ℂ))) ≫
          affineToricSchemeActionOver hi σ := by
  simpa only [faceAffineToricSchemeMap_eq_affineToricSchemeMap,
    affineToricSchemeMap_id, Scheme.Hom.asOver, OverClass.asOverHom_id] using
      affineToricSchemeActionOver_comp_map hi hi (AddMonoidHom.id N) LinearMap.id
        (fun _ ↦ rfl) (fun _ hx ↦ hτσ.le hx)

end TauCeti.Toric
