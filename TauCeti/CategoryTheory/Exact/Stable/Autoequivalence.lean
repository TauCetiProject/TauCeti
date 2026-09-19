/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Connecting
public import TauCeti.CategoryTheory.Exact.Stable.Loop

/-!
# Suspension and loops are inverse autoequivalences of a Frobenius stable category

Let `E` be a Frobenius exact structure, with chosen conflations `X ⟶ I(X) ⟶ ΣX` and
`ΩX ⟶ P(X) ⟶ X` whose middle terms are projective-injective. This file proves that the stable
suspension and stable loop functors are quasi-inverse, and packages them as an additive
autoequivalence of the projective stable category.

The comparisons are the classical ones. Since `P(X)` is injective, the loop inflation
`ΩX ⟶ P(X)` extends along `ΩX ⟶ I(ΩX)`, which induces `ΣΩX ⟶ X` on cokernels; its inverse in the
stable category is the connecting map `X ⟶ ΣΩX` of the loop conflation. Dually, since `I(X)` is
projective, the suspension deflation `I(X) ⟶ ΣX` lifts along `P(ΣX) ⟶ ΣX`, which induces
`X ⟶ ΩΣX` on kernels, and `P(ΣX)` lifts along `I(X) ⟶ ΣX` to give the inverse `ΩΣX ⟶ X`.
All the required identities in the stable category follow from
`ExactStructure.projectiveStableFunctor_map_τ₃_eq_of_τ₁_eq` and its dual: maps of conflations
agreeing at one end agree at the other end modulo a projective middle term.

## Main definitions

* `TauCeti.ExactStructure.IsFrobenius.fromSuspensionLoop`: the comparison `ΣΩX ⟶ X`.
* `TauCeti.ExactStructure.IsFrobenius.toLoopSuspension`: the comparison `X ⟶ ΩΣX`.
* `TauCeti.ExactStructure.IsFrobenius.fromLoopSuspension`: its inverse `ΩΣX ⟶ X` in the stable
  category.
* `TauCeti.ExactStructure.IsFrobenius.stableLoopCompStableSuspensionIso`: `Ω ⋙ Σ ≅ 𝟭`.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspensionCompStableLoopIso`: `Σ ⋙ Ω ≅ 𝟭`.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspensionEquivalence`: suspension as an
  autoequivalence of the stable category, with inverse the loop functor.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

/-- The middle term of a chosen loop presentation is relatively injective. -/
theorem isInjective_loopProjective (X : C) :
    E.isInjective (hE.enoughProjectives.loopProjective X) :=
  (hE.projective_iff_injective _).mp (hE.enoughProjectives.isProjective_loopProjective X)

/-! ### The comparison `ΣΩX ≅ X` -/

/-- A chosen extension `I(ΩX) ⟶ P(X)` of the loop inflation `ΩX ⟶ P(X)` along the suspension
inflation `ΩX ⟶ I(ΩX)`. -/
private noncomputable abbrev suspensionLoopMiddleMap (X : C) :
    hE.suspensionInjective (hE.enoughProjectives.loopObj X) ⟶
      hE.enoughProjectives.loopProjective X :=
  (hE.isInjective_loopProjective X).factorThru
    (E.isInflation_f (hE.suspensionPresentation _).conflation)
    (hE.enoughProjectives.loopInflation X)

/-- The chosen middle map extends the loop inflation along the suspension inflation. -/
@[reassoc (attr := simp)]
private theorem suspensionInflation_comp_suspensionLoopMiddleMap (X : C) :
    hE.suspensionInflation (hE.enoughProjectives.loopObj X) ≫ suspensionLoopMiddleMap hE X =
      hE.enoughProjectives.loopInflation X :=
  (hE.isInjective_loopProjective X).comp_factorThru
    (E.isInflation_f (hE.suspensionPresentation _).conflation)
    (hE.enoughProjectives.loopInflation X)

/-- The comparison map `ΣΩX ⟶ X`, induced on cokernels by the chosen middle map. It is an
isomorphism in the stable category. -/
noncomputable def fromSuspensionLoop (X : C) :
    hE.suspensionObj (hE.enoughProjectives.loopObj X) ⟶ X :=
  (E.isKernelCokernelPair _ (hE.suspensionPresentation _).conflation).desc
    (suspensionLoopMiddleMap hE X ≫ hE.enoughProjectives.loopDeflation X) (by
      rw [suspensionInflation_comp_suspensionLoopMiddleMap_assoc hE,
        hE.enoughProjectives.loopInflation_comp_loopDeflation])

/-- The comparison `ΣΩX ⟶ X` makes the square on the two deflations commute. -/
@[reassoc (attr := simp)]
private theorem suspensionDeflation_comp_fromSuspensionLoop (X : C) :
    hE.suspensionDeflation (hE.enoughProjectives.loopObj X) ≫ hE.fromSuspensionLoop X =
      suspensionLoopMiddleMap hE X ≫ hE.enoughProjectives.loopDeflation X :=
  (E.isKernelCokernelPair _ (hE.suspensionPresentation _).conflation).g_desc _ _

/-- In the stable category, the connecting map `X ⟶ ΣΩX` of the loop conflation is a right
inverse of `fromSuspensionLoop`. -/
theorem projectiveStableFunctor_map_connectingMap_comp_fromSuspensionLoop (X : C) :
    E.projectiveStableFunctor.map
        (hE.connectingMap (hE.enoughProjectives.conflation_loopInflation_loopDeflation X) ≫
          hE.fromSuspensionLoop X) = 𝟙 _ := by
  let hS := hE.enoughProjectives.conflation_loopInflation_loopDeflation X
  let φ : ShortComplex.mk _ _ (hE.enoughProjectives.loopInflation_comp_loopDeflation X) ⟶
      ShortComplex.mk _ _ (hE.enoughProjectives.loopInflation_comp_loopDeflation X) :=
    { τ₁ := 𝟙 _
      τ₂ := hE.connectingMiddleMap hS ≫ suspensionLoopMiddleMap hE X
      τ₃ := hE.connectingMap hS ≫ hE.fromSuspensionLoop X
      comm₁₂ := by simp [hE.f_comp_connectingMiddleMap_assoc hS]
      comm₂₃ := by simp [hE.g_comp_connectingMap_assoc hS] }
  simpa [φ] using E.projectiveStableFunctor_map_τ₃_eq_of_τ₁_eq hS
    (hE.enoughProjectives.isProjective_loopProjective X) (φ := φ) (ψ := 𝟙 _) rfl

/-- In the stable category, the connecting map `X ⟶ ΣΩX` of the loop conflation is a left
inverse of `fromSuspensionLoop`. -/
theorem projectiveStableFunctor_map_fromSuspensionLoop_comp_connectingMap (X : C) :
    E.projectiveStableFunctor.map (hE.fromSuspensionLoop X ≫
        hE.connectingMap (hE.enoughProjectives.conflation_loopInflation_loopDeflation X)) =
      𝟙 _ := by
  let hS := hE.enoughProjectives.conflation_loopInflation_loopDeflation X
  let S := ShortComplex.mk _ _ (hE.suspensionPresentation (hE.enoughProjectives.loopObj X)).zero
  let φ : S ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := suspensionLoopMiddleMap hE X ≫ hE.connectingMiddleMap hS
      τ₃ := hE.fromSuspensionLoop X ≫ hE.connectingMap hS
      comm₁₂ := by simp [S, hE.f_comp_connectingMiddleMap hS]
      comm₂₃ := by simp [S, hE.g_comp_connectingMap hS] }
  simpa [φ] using E.projectiveStableFunctor_map_τ₃_eq_of_τ₁_eq
    (hE.suspensionPresentation _).conflation (hE.isProjective_suspensionInjective _)
    (φ := φ) (ψ := 𝟙 _) rfl

/-- The comparison `ΣΩX ≅ X` in the stable category. -/
noncomputable def suspensionLoopIso (X : C) :
    E.projectiveStableFunctor.obj (hE.suspensionObj (hE.enoughProjectives.loopObj X)) ≅
      E.projectiveStableFunctor.obj X where
  hom := E.projectiveStableFunctor.map (hE.fromSuspensionLoop X)
  inv := E.projectiveStableFunctor.map
    (hE.connectingMap (hE.enoughProjectives.conflation_loopInflation_loopDeflation X))
  hom_inv_id := by
    rw [← Functor.map_comp, hE.projectiveStableFunctor_map_fromSuspensionLoop_comp_connectingMap]
  inv_hom_id := by
    rw [← Functor.map_comp, hE.projectiveStableFunctor_map_connectingMap_comp_fromSuspensionLoop]

/-- The comparison `ΣΩX ⟶ X` is natural in the stable category. -/
theorem projectiveStableFunctor_map_fromSuspensionLoop_naturality {X Y : C} (f : X ⟶ Y) :
    E.projectiveStableFunctor.map
        (hE.suspensionMap (hE.enoughProjectives.loopMap f) ≫ hE.fromSuspensionLoop Y) =
      E.projectiveStableFunctor.map (hE.fromSuspensionLoop X ≫ f) := by
  let S := ShortComplex.mk _ _ (hE.suspensionPresentation (hE.enoughProjectives.loopObj X)).zero
  let T := ShortComplex.mk _ _ (hE.enoughProjectives.loopInflation_comp_loopDeflation Y)
  let φ : S ⟶ T :=
    { τ₁ := hE.enoughProjectives.loopMap f
      τ₂ := hE.suspensionMiddleMap (hE.enoughProjectives.loopMap f) ≫
        suspensionLoopMiddleMap hE Y
      τ₃ := hE.suspensionMap (hE.enoughProjectives.loopMap f) ≫ hE.fromSuspensionLoop Y
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T] }
  let ψ : S ⟶ T :=
    { τ₁ := hE.enoughProjectives.loopMap f
      τ₂ := suspensionLoopMiddleMap hE X ≫ hE.enoughProjectives.loopMiddleMap f
      τ₃ := hE.fromSuspensionLoop X ≫ f
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T] }
  exact E.projectiveStableFunctor_map_τ₃_eq_of_τ₁_eq (hE.suspensionPresentation _).conflation
    (hE.enoughProjectives.isProjective_loopProjective Y) (φ := φ) (ψ := ψ) rfl

/-! ### The comparison `X ≅ ΩΣX` -/

/-- A chosen lift `I(X) ⟶ P(ΣX)` of the suspension deflation `I(X) ⟶ ΣX` along the loop
deflation `P(ΣX) ⟶ ΣX`. -/
private noncomputable abbrev loopSuspensionMiddleMap (X : C) :
    hE.suspensionInjective X ⟶ hE.enoughProjectives.loopProjective (hE.suspensionObj X) :=
  (hE.isProjective_suspensionInjective X).factorThru
    (E.isDeflation_g (hE.enoughProjectives.conflation_loopInflation_loopDeflation _))
    (hE.suspensionDeflation X)

/-- The chosen middle map lifts the suspension deflation along the loop deflation. -/
@[reassoc (attr := simp)]
private theorem loopSuspensionMiddleMap_comp_loopDeflation (X : C) :
    loopSuspensionMiddleMap hE X ≫ hE.enoughProjectives.loopDeflation (hE.suspensionObj X) =
      hE.suspensionDeflation X :=
  (hE.isProjective_suspensionInjective X).factorThru_comp
    (E.isDeflation_g (hE.enoughProjectives.conflation_loopInflation_loopDeflation _))
    (hE.suspensionDeflation X)

/-- The comparison map `X ⟶ ΩΣX`, induced on kernels by the chosen middle map. It is an
isomorphism in the stable category. -/
noncomputable def toLoopSuspension (X : C) :
    X ⟶ hE.enoughProjectives.loopObj (hE.suspensionObj X) :=
  (E.isKernelCokernelPair _
    (hE.enoughProjectives.conflation_loopInflation_loopDeflation _)).lift
      (hE.suspensionInflation X ≫ loopSuspensionMiddleMap hE X) (by
        rw [Category.assoc, loopSuspensionMiddleMap_comp_loopDeflation hE,
          (hE.suspensionPresentation X).zero])

/-- The comparison `X ⟶ ΩΣX` makes the square on the two inflations commute. -/
@[reassoc (attr := simp)]
private theorem toLoopSuspension_comp_loopInflation (X : C) :
    hE.toLoopSuspension X ≫ hE.enoughProjectives.loopInflation (hE.suspensionObj X) =
      hE.suspensionInflation X ≫ loopSuspensionMiddleMap hE X :=
  (E.isKernelCokernelPair _
    (hE.enoughProjectives.conflation_loopInflation_loopDeflation _)).lift_f _ _

/-- A chosen lift `P(ΣX) ⟶ I(X)` of the loop deflation `P(ΣX) ⟶ ΣX` along the suspension
deflation `I(X) ⟶ ΣX`. -/
private noncomputable abbrev loopSuspensionInvMiddleMap (X : C) :
    hE.enoughProjectives.loopProjective (hE.suspensionObj X) ⟶ hE.suspensionInjective X :=
  (hE.enoughProjectives.isProjective_loopProjective _).factorThru
    (E.isDeflation_g (hE.suspensionPresentation X).conflation)
    (hE.enoughProjectives.loopDeflation (hE.suspensionObj X))

/-- The chosen middle map lifts the loop deflation along the suspension deflation. -/
@[reassoc (attr := simp)]
private theorem loopSuspensionInvMiddleMap_comp_suspensionDeflation (X : C) :
    loopSuspensionInvMiddleMap hE X ≫ hE.suspensionDeflation X =
      hE.enoughProjectives.loopDeflation (hE.suspensionObj X) :=
  (hE.enoughProjectives.isProjective_loopProjective _).factorThru_comp
    (E.isDeflation_g (hE.suspensionPresentation X).conflation)
    (hE.enoughProjectives.loopDeflation (hE.suspensionObj X))

/-- The comparison map `ΩΣX ⟶ X`, induced on kernels by the chosen middle map. It is the
inverse of `toLoopSuspension` in the stable category. -/
noncomputable def fromLoopSuspension (X : C) :
    hE.enoughProjectives.loopObj (hE.suspensionObj X) ⟶ X :=
  (E.isKernelCokernelPair _ (hE.suspensionPresentation X).conflation).lift
    (hE.enoughProjectives.loopInflation _ ≫ loopSuspensionInvMiddleMap hE X) (by
      rw [Category.assoc, loopSuspensionInvMiddleMap_comp_suspensionDeflation hE,
        hE.enoughProjectives.loopInflation_comp_loopDeflation])

/-- The comparison `ΩΣX ⟶ X` makes the square on the two inflations commute. -/
@[reassoc (attr := simp)]
private theorem fromLoopSuspension_comp_suspensionInflation (X : C) :
    hE.fromLoopSuspension X ≫ hE.suspensionInflation X =
      hE.enoughProjectives.loopInflation (hE.suspensionObj X) ≫
        loopSuspensionInvMiddleMap hE X :=
  (E.isKernelCokernelPair _ (hE.suspensionPresentation X).conflation).lift_f _ _

/-- In the stable category, `fromLoopSuspension` is a left inverse of `toLoopSuspension`. -/
theorem projectiveStableFunctor_map_toLoopSuspension_comp_fromLoopSuspension (X : C) :
    E.projectiveStableFunctor.map (hE.toLoopSuspension X ≫ hE.fromLoopSuspension X) = 𝟙 _ := by
  let S := ShortComplex.mk _ _ (hE.suspensionPresentation X).zero
  let φ : S ⟶ S :=
    { τ₁ := hE.toLoopSuspension X ≫ hE.fromLoopSuspension X
      τ₂ := loopSuspensionMiddleMap hE X ≫ loopSuspensionInvMiddleMap hE X
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S] }
  simpa [φ] using E.projectiveStableFunctor_map_τ₁_eq_of_τ₃_eq
    (hE.suspensionPresentation X).conflation
    (hE.isProjective_suspensionInjective X) (φ := φ) (ψ := 𝟙 _) rfl

/-- In the stable category, `fromLoopSuspension` is a right inverse of `toLoopSuspension`. -/
theorem projectiveStableFunctor_map_fromLoopSuspension_comp_toLoopSuspension (X : C) :
    E.projectiveStableFunctor.map (hE.fromLoopSuspension X ≫ hE.toLoopSuspension X) = 𝟙 _ := by
  let hS := hE.enoughProjectives.conflation_loopInflation_loopDeflation (hE.suspensionObj X)
  let φ : ShortComplex.mk _ _
        (hE.enoughProjectives.loopInflation_comp_loopDeflation (hE.suspensionObj X)) ⟶
      ShortComplex.mk _ _
        (hE.enoughProjectives.loopInflation_comp_loopDeflation (hE.suspensionObj X)) :=
    { τ₁ := hE.fromLoopSuspension X ≫ hE.toLoopSuspension X
      τ₂ := loopSuspensionInvMiddleMap hE X ≫ loopSuspensionMiddleMap hE X
      τ₃ := 𝟙 _
      comm₁₂ := by simp
      comm₂₃ := by simp }
  simpa [φ] using E.projectiveStableFunctor_map_τ₁_eq_of_τ₃_eq hS
    (hE.enoughProjectives.isProjective_loopProjective _) (φ := φ) (ψ := 𝟙 _) rfl

/-- The comparison `X ≅ ΩΣX` in the stable category. -/
noncomputable def loopSuspensionIso (X : C) :
    E.projectiveStableFunctor.obj X ≅
      E.projectiveStableFunctor.obj (hE.enoughProjectives.loopObj (hE.suspensionObj X)) where
  hom := E.projectiveStableFunctor.map (hE.toLoopSuspension X)
  inv := E.projectiveStableFunctor.map (hE.fromLoopSuspension X)
  hom_inv_id := by
    rw [← Functor.map_comp,
      hE.projectiveStableFunctor_map_toLoopSuspension_comp_fromLoopSuspension]
  inv_hom_id := by
    rw [← Functor.map_comp,
      hE.projectiveStableFunctor_map_fromLoopSuspension_comp_toLoopSuspension]

/-- The comparison `X ⟶ ΩΣX` is natural in the stable category. -/
theorem projectiveStableFunctor_map_toLoopSuspension_naturality {X Y : C} (f : X ⟶ Y) :
    E.projectiveStableFunctor.map (f ≫ hE.toLoopSuspension Y) =
      E.projectiveStableFunctor.map
        (hE.toLoopSuspension X ≫ hE.enoughProjectives.loopMap (hE.suspensionMap f)) := by
  let S := ShortComplex.mk _ _ (hE.suspensionPresentation X).zero
  let hT := hE.enoughProjectives.conflation_loopInflation_loopDeflation (hE.suspensionObj Y)
  let T := ShortComplex.mk _ _
    (hE.enoughProjectives.loopInflation_comp_loopDeflation (hE.suspensionObj Y))
  let φ : S ⟶ T :=
    { τ₁ := f ≫ hE.toLoopSuspension Y
      τ₂ := hE.suspensionMiddleMap f ≫ loopSuspensionMiddleMap hE Y
      τ₃ := hE.suspensionMap f
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T] }
  let ψ : S ⟶ T :=
    { τ₁ := hE.toLoopSuspension X ≫ hE.enoughProjectives.loopMap (hE.suspensionMap f)
      τ₂ := loopSuspensionMiddleMap hE X ≫
        hE.enoughProjectives.loopMiddleMap (hE.suspensionMap f)
      τ₃ := hE.suspensionMap f
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T] }
  exact E.projectiveStableFunctor_map_τ₁_eq_of_τ₃_eq hT
    (hE.isProjective_suspensionInjective X) (φ := φ) (ψ := ψ) rfl

/-! ### The autoequivalence -/

/-- Loops followed by suspension is isomorphic to the identity of the stable category. -/
noncomputable def stableLoopCompStableSuspensionIso :
    hE.enoughProjectives.stableLoop ⋙ hE.stableSuspension ≅ 𝟭 E.ProjectiveStableCategory :=
  CategoryTheory.Quotient.natIsoLift _ (NatIso.ofComponents
    (fun X ↦ eqToIso (by simp) ≪≫ hE.suspensionLoopIso X) (fun {X Y} f ↦ by
      simp only [Functor.comp_map, Functor.id_map, Iso.trans_hom, eqToIso.hom,
        EnoughProjectives.stableLoop_map_projectiveStableFunctor_map, Functor.map_comp,
        eqToHom_map, stableSuspension_map_projectiveStableFunctor_map, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, suspensionLoopIso]
      rw [← Functor.map_comp, hE.projectiveStableFunctor_map_fromSuspensionLoop_naturality,
        Functor.map_comp]))

/-- Suspension followed by loops is isomorphic to the identity of the stable category. -/
noncomputable def stableSuspensionCompStableLoopIso :
    hE.stableSuspension ⋙ hE.enoughProjectives.stableLoop ≅ 𝟭 E.ProjectiveStableCategory :=
  (CategoryTheory.Quotient.natIsoLift (F := 𝟭 E.ProjectiveStableCategory)
    (G := hE.stableSuspension ⋙ hE.enoughProjectives.stableLoop) _ (NatIso.ofComponents
    (fun X ↦ hE.loopSuspensionIso X ≪≫ eqToIso (by simp)) (fun {X Y} f ↦ by
      simp only [Functor.comp_map, Functor.id_map, Iso.trans_hom, eqToIso.hom,
        EnoughProjectives.stableLoop_map_projectiveStableFunctor_map, Functor.map_comp,
        eqToHom_map, stableSuspension_map_projectiveStableFunctor_map, Category.assoc,
        eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, loopSuspensionIso]
      rw [← Functor.map_comp_assoc, hE.projectiveStableFunctor_map_toLoopSuspension_naturality,
        Functor.map_comp, Category.assoc]))).symm

/-- On a represented object, the isomorphism `ΣΩX ≅ X` is `fromSuspensionLoop`. -/
@[simp]
theorem stableLoopCompStableSuspensionIso_hom_app (X : C) :
    hE.stableLoopCompStableSuspensionIso.hom.app (E.projectiveStableFunctor.obj X) =
      eqToHom (by simp) ≫ E.projectiveStableFunctor.map (hE.fromSuspensionLoop X) := by
  simp [stableLoopCompStableSuspensionIso, suspensionLoopIso]

/-- On a represented object, the inverse isomorphism `X ≅ ΣΩX` is the connecting map of the
chosen loop conflation. -/
@[simp]
theorem stableLoopCompStableSuspensionIso_inv_app (X : C) :
    hE.stableLoopCompStableSuspensionIso.inv.app (E.projectiveStableFunctor.obj X) =
      E.projectiveStableFunctor.map
        (hE.connectingMap (hE.enoughProjectives.conflation_loopInflation_loopDeflation X)) ≫
          eqToHom (by simp) := by
  simp [stableLoopCompStableSuspensionIso, suspensionLoopIso]

/-- On a represented object, the isomorphism `ΩΣX ≅ X` is `fromLoopSuspension`. -/
@[simp]
theorem stableSuspensionCompStableLoopIso_hom_app (X : C) :
    hE.stableSuspensionCompStableLoopIso.hom.app (E.projectiveStableFunctor.obj X) =
      eqToHom (by simp) ≫ E.projectiveStableFunctor.map (hE.fromLoopSuspension X) := by
  simp [stableSuspensionCompStableLoopIso, loopSuspensionIso]

/-- On a represented object, the inverse isomorphism `X ≅ ΩΣX` is `toLoopSuspension`. -/
@[simp]
theorem stableSuspensionCompStableLoopIso_inv_app (X : C) :
    hE.stableSuspensionCompStableLoopIso.inv.app (E.projectiveStableFunctor.obj X) =
      E.projectiveStableFunctor.map (hE.toLoopSuspension X) ≫ eqToHom (by simp) := by
  simp [stableSuspensionCompStableLoopIso, loopSuspensionIso]

/-- Suspension is an autoequivalence of the stable category of a Frobenius exact structure, with
quasi-inverse the loop functor. -/
noncomputable def stableSuspensionEquivalence :
    E.ProjectiveStableCategory ≌ E.ProjectiveStableCategory :=
  CategoryTheory.Equivalence.mk hE.stableSuspension hE.enoughProjectives.stableLoop
    hE.stableSuspensionCompStableLoopIso.symm hE.stableLoopCompStableSuspensionIso

/-- The functor of `stableSuspensionEquivalence` is stable suspension. -/
@[simp]
theorem stableSuspensionEquivalence_functor :
    hE.stableSuspensionEquivalence.functor = hE.stableSuspension :=
  (rfl)

/-- The inverse of `stableSuspensionEquivalence` is the stable loop functor. -/
@[simp]
theorem stableSuspensionEquivalence_inverse :
    hE.stableSuspensionEquivalence.inverse = hE.enoughProjectives.stableLoop :=
  (rfl)

/-- Stable suspension is an equivalence of categories. -/
instance isEquivalence_stableSuspension : hE.stableSuspension.IsEquivalence :=
  hE.stableSuspensionEquivalence.isEquivalence_functor

/-- The stable loop functor of a Frobenius exact structure is an equivalence of categories. -/
instance isEquivalence_stableLoop : hE.enoughProjectives.stableLoop.IsEquivalence :=
  hE.stableSuspensionEquivalence.isEquivalence_inverse

end ExactStructure.IsFrobenius

end TauCeti
