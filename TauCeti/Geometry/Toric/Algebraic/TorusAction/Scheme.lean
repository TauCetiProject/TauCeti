/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction

/-!
# The action on an affine toric scheme

The grading coaction on the coordinate ring of an affine toric chart induces a morphism from
the product of the dense torus and the chart to the chart. We construct this morphism using the
standard comparison between a fibre product of affine schemes and the spectrum of a tensor
product, then package it as a morphism of schemes over `Spec ℂ`.

On the zero cone, the action morphism agrees with multiplication on the dense torus. Its unit
and associativity laws follow from the counit and coassociativity identities in
`TauCeti.Geometry.Toric.Algebraic.TorusAction.Coaction`, transported by Mathlib's monoidal
`AlgebraicGeometry.algSpec` functor.
The action is equivariant under maps of lattice cones, in particular under face inclusions.

## Main declarations

* `TauCeti.Toric.affineToricSchemeAction`: the action morphism on an affine toric chart.
* `TauCeti.Toric.affineToricSchemeActionOver`: the action as a morphism over `Spec ℂ`.
* `TauCeti.Toric.affineToricSchemeModObj`: the dense-torus action as a module object, with
  unit and associativity laws supplied by `CategoryTheory.ModObj`.
* `TauCeti.Toric.affineToricSchemeAction_bot`: on the zero cone, the action is torus
  multiplication.
* `TauCeti.Toric.affineToricSchemeActionOver_comp_map`: equivariance under toric maps.
* `TauCeti.Toric.faceAffineToricSchemeMap_isModHom`: equivariance under face inclusions.

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

private theorem affineToricSchemeActionOver_left (hi : IsIntegralLattice i)
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

private theorem affineToricSchemeActionOver_eq_algSpec (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    letI : (algSpec (.of ℂ)).LaxMonoidal :=
      (braidedAlgSpec (R := .of ℂ)).toLaxBraided.toLaxMonoidal
    affineToricSchemeActionOver hi σ =
      Functor.LaxMonoidal.μ (algSpec (.of ℂ))
        (.op <| CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))
        (.op <| CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi σ)) ≫
      (algSpec (.of ℂ)).map (CommAlgCat.ofHom (R := CommRingCat.of ℂ)
          (affineCoordinateRingCoaction hi σ)).op := by
  dsimp only
  apply Over.OverMorphism.ext
  rw [affineToricSchemeActionOver_left, affineToricSchemeAction_def, Over.comp_left,
    μ_algSpec_left, algSpec_map_left]
  -- The remaining equality forgets the algebra-to-`Under` packaging of the same ring map.
  rfl

private theorem affineCoordinateRingCoaction_op_one (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
  let T := Opposite.op <| CommAlgCat.of (CommRingCat.of ℂ)
      (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
  let X := Opposite.op <| CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi σ)
  let a : T ⊗ X ⟶ X := (CommAlgCat.ofHom (R := CommRingCat.of ℂ)
      (affineCoordinateRingCoaction hi σ)).op
  η[T] ▷ X ≫ a = (λ_ X).hom := by
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, unop_whiskerRight,
    unop_hom_leftUnitor, Quiver.Hom.unop_op, Opposite.unop_op]
  apply (cancel_mono (λ_ (CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi σ))).hom).mp
  simp only [Iso.inv_hom_id]
  apply CommAlgCat.hom_ext
  -- `CommAlgCat` chooses the tensor-product left-unit equivalence as its unitor.
  have hunit : (λ_ (CommAlgCat.of (CommRingCat.of ℂ)
      (affineCoordinateRing hi σ))).hom.hom =
      (Algebra.TensorProduct.lid ℂ (affineCoordinateRing hi σ)).toAlgHom := rfl
  simpa only [CommAlgCat.hom_comp, CommAlgCat.whiskerRight_hom,
    CommAlgCat.one_op_of_unop_hom, CommAlgCat.hom_ofHom, CommAlgCat.hom_id,
    hunit, AlgHom.comp_assoc]
    using affineCoordinateRingCoaction_counit hi σ

private theorem affineCoordinateRingCoaction_op_mul (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
  let T := Opposite.op <| CommAlgCat.of (CommRingCat.of ℂ)
      (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
  let X := Opposite.op <| CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi σ)
  let a : T ⊗ X ⟶ X := (CommAlgCat.ofHom (R := CommRingCat.of ℂ)
      (affineCoordinateRingCoaction hi σ)).op
  μ[T] ▷ X ≫ a = (α_ T T X).hom ≫ T ◁ a ≫ a := by
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, unop_whiskerRight,
    unop_whiskerLeft, unop_hom_associator,
    Quiver.Hom.unop_op, Opposite.unop_op]
  apply (cancel_mono (α_ (CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi ⊥))
    (CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi ⊥))
    (CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi σ))).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply CommAlgCat.hom_ext
  simpa only [CommAlgCat.hom_comp, CommAlgCat.whiskerRight_hom,
    CommAlgCat.whiskerLeft_hom, CommAlgCat.mul_op_of_unop_hom,
    CommAlgCat.hom_ofHom, CommAlgCat.associator_hom_hom]
    using affineCoordinateRingCoaction_coassoc hi σ

private theorem denseTorus_one_eq_algSpec (hi : IsIntegralLattice i) :
    letI : (algSpec (.of ℂ)).LaxMonoidal :=
      (braidedAlgSpec (R := .of ℂ)).toLaxBraided.toLaxMonoidal
    η[(denseTorusScheme hi).asOver (Spec (.of ℂ))] =
      Functor.LaxMonoidal.ε (algSpec (.of ℂ)) ≫
        (algSpec (.of ℂ)).map
          η[Opposite.op <| CommAlgCat.of (CommRingCat.of ℂ)
              (affineCoordinateRing hi (⊥ : PointedCone ℝ V))] := by
  dsimp only
  apply Over.OverMorphism.ext
  simp only [one_spec_asOver_spec_left, Over.comp_left, algSpec_map_left]
  -- `braidedAlgSpec` chooses the identity for its unit comparison, and the
  -- algebra-to-`Under` packaging retains the same counit ring map.
  rfl

private theorem denseTorus_mul_eq_algSpec (hi : IsIntegralLattice i) :
    letI : (algSpec (.of ℂ)).LaxMonoidal :=
      (braidedAlgSpec (R := .of ℂ)).toLaxBraided.toLaxMonoidal
    μ[(denseTorusScheme hi).asOver (Spec (.of ℂ))] =
      Functor.LaxMonoidal.μ (algSpec (.of ℂ))
        (.op <| CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))
        (.op <| CommAlgCat.of (CommRingCat.of ℂ) (affineCoordinateRing hi (⊥ : PointedCone ℝ V))) ≫
      (algSpec (.of ℂ)).map
        μ[Opposite.op <| CommAlgCat.of (CommRingCat.of ℂ)
            (affineCoordinateRing hi (⊥ : PointedCone ℝ V))] := by
  dsimp only
  apply Over.OverMorphism.ext
  simp only [mul_spec_asOver_spec_left, Over.comp_left, algSpec_map_left]
  -- `braidedAlgSpec` chooses `pullbackSpecIso.hom` for its tensor comparison, and the
  -- algebra-to-`Under` packaging retains the same comultiplication ring map.
  rfl

/-- Each affine toric chart is a module object for its dense torus over `Spec ℂ`. -/
noncomputable instance affineToricSchemeModObj (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    ModObj ((denseTorusScheme hi).asOver (Spec (.of ℂ)))
      ((affineToricScheme hi σ).asOver (Spec (.of ℂ))) := by
  let R : CommRingCat := .of ℂ
  let F := algSpec R
  let : F.LaxMonoidal := (braidedAlgSpec (R := R)).toLaxBraided.toLaxMonoidal
  let T := Opposite.op <| CommAlgCat.of R (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
  let X := Opposite.op <| CommAlgCat.of R (affineCoordinateRing hi σ)
  let a : T ⊗ X ⟶ X := (CommAlgCat.ofHom (R := R) (affineCoordinateRingCoaction hi σ)).op
  exact {
    smul := affineToricSchemeActionOver hi σ
    one_smul := by
      have h : (Functor.LaxMonoidal.ε F ≫ F.map η[T]) ▷ F.obj X ≫
          Functor.LaxMonoidal.μ F T X ≫ F.map a = (λ_ (F.obj X)).hom := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
          Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
          affineCoordinateRingCoaction_op_one, ← Functor.LaxMonoidal.left_unitality]
      simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
        MonoidalCategory.selfLeftAction_actionUnitIso]
      rw [affineToricSchemeActionOver_eq_algSpec, denseTorus_one_eq_algSpec]
      exact h
    mul_smul := by
      have h : (Functor.LaxMonoidal.μ F T T ≫ F.map μ[T]) ▷ F.obj X ≫
          Functor.LaxMonoidal.μ F T X ≫ F.map a =
        (α_ (F.obj T) (F.obj T) (F.obj X)).hom ≫
          F.obj T ◁ (Functor.LaxMonoidal.μ F T X ≫ F.map a) ≫
            Functor.LaxMonoidal.μ F T X ≫ F.map a := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc,
          Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp,
          affineCoordinateRingCoaction_op_mul, F.map_comp, F.map_comp,
          Functor.LaxMonoidal.associativity_assoc,
          ← Functor.LaxMonoidal.μ_natural_right_assoc]
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc, a, X]
      simp only [MonoidalCategory.selfLeftAction_actionHomLeft,
        MonoidalCategory.selfLeftAction_actionHomRight,
        MonoidalCategory.selfLeftAction_actionAssocIso]
      rw [affineToricSchemeActionOver_eq_algSpec, denseTorus_mul_eq_algSpec]
      exact h
  }

/-- The affine toric action over `Spec ℂ` is the action map of its module object. -/
@[simp]
theorem affineToricSchemeActionOver_eq_smul (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    affineToricSchemeActionOver hi σ =
      γ[(denseTorusScheme hi).asOver (Spec (.of ℂ)),
        (affineToricScheme hi σ).asOver (Spec (.of ℂ))] := (rfl)

/-- The underlying scheme morphism of the dense-torus module-object action is
`affineToricSchemeAction`. -/
@[simp]
theorem affineToricScheme_smul_left (hi : IsIntegralLattice i) (σ : PointedCone ℝ V) :
    (γ[(denseTorusScheme hi).asOver (Spec (.of ℂ)),
      (affineToricScheme hi σ).asOver (Spec (.of ℂ))]).left =
        affineToricSchemeAction hi σ := by
  rw [← affineToricSchemeActionOver_eq_smul, affineToricSchemeActionOver_left]

/-- On the zero cone, the module-object action is multiplication on the dense torus. -/
@[simp]
theorem affineToricSchemeActionOver_bot (hi : IsIntegralLattice i) :
    γ[(denseTorusScheme hi).asOver (Spec (.of ℂ)),
      (affineToricScheme hi (⊥ : PointedCone ℝ V)).asOver (Spec (.of ℂ))] =
        μ[(denseTorusScheme hi).asOver (Spec (.of ℂ))] := by
  rw [← affineToricSchemeActionOver_eq_smul]
  apply Over.OverMorphism.ext
  rw [affineToricSchemeActionOver_left, affineToricSchemeAction_bot]

private theorem affineToricSchemeMap_asOver_eq_algSpec
    {N' : Type} {V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    (affineToricSchemeMap hi hi' f g hfg hστ).asOver (Spec (.of ℂ)) =
      (algSpec (.of ℂ)).map
        (CommAlgCat.ofHom (R := CommRingCat.of ℂ)
            (affineCoordinateRingMap hi hi' f g hfg hστ)).op := by
  apply Over.OverMorphism.ext
  simp only [Scheme.Hom.asOver, OverClass.asOverHom_left, affineToricSchemeMap_def,
    algSpec_map_left]
  -- The algebra-to-`Under` packaging retains the same coordinate-ring map.
  rfl

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
  rw [affineToricSchemeActionOver_eq_algSpec, affineToricSchemeActionOver_eq_algSpec,
    affineToricSchemeMap_asOver_eq_algSpec, affineToricSchemeMap_asOver_eq_algSpec]
  exact h

/-- Face inclusions are morphisms of dense-torus module objects over `Spec ℂ`. -/
instance faceAffineToricSchemeMap_isModHom (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ) :
    IsModHom ((denseTorusScheme hi).asOver (Spec (.of ℂ)))
      ((faceAffineToricSchemeMap hi hτσ).asOver (Spec (.of ℂ))) where
  smul_hom := by
    simp only [faceAffineToricSchemeMap_eq_affineToricSchemeMap]
    have h := affineToricSchemeActionOver_comp_map hi hi (AddMonoidHom.id N) LinearMap.id
      (fun _ ↦ rfl) (fun _ hx ↦ hτσ.le hx)
    simp only [affineToricSchemeMap_id, OverClass.asOverHom_id,
      MonoidalCategory.id_tensorHom] at h
    simpa only [affineToricSchemeActionOver_eq_smul,
      MonoidalCategory.selfLeftAction_actionHomRight] using h

end TauCeti.Toric
