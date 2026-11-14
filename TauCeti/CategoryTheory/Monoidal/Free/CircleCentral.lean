/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Free.SelfDuality
public import TauCeti.CategoryTheory.Monoidal.Scalar

/-!
# The free self-duality with a central circle

`TauCeti.CircleCentralSelfDualityCat` is the quotient of the free monoidal category on a
self-dual object by the equation equating the left and right actions of its closed circle
on the generator. The equation is imposed at the generator only, with its monoidal closure;
no circle value is prescribed. This is the presentation appropriate for diagrams recording
the number of closed circles, rather than their positions among the strands.

Every self-duality whose circle is central at its underlying object gives a strong monoidal
functor from this quotient, unique up to a monoidal natural isomorphism compatible with the
chosen identification of the generator. The target is an arbitrary monoidal category: it
need not be braided, linear, or strict, and centrality at its other objects is not required.

The construction uses `TauCeti.FreeSelfDualityCat` and the monoidal quotient machinery;
it does not identify the presented category with a combinatorial model of planar diagrams.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1.
* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845.
-/

public section

universe u v

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

namespace CircleCentralSelfDualityCat

open FreeSelfDualityCat in
/-- The single additional relation: a closed circle can pass across the generating strand. -/
inductive Rel : HomRel FreeSelfDualityCat
  | circle : Rel
      ((ρ_ generator).inv ≫ generator ◁ (η_ generator generator ≫ ε_ generator generator) ≫
        (ρ_ generator).hom)
      ((λ_ generator).inv ≫ (η_ generator generator ≫ ε_ generator generator) ▷ generator ≫
        (λ_ generator).hom)

end CircleCentralSelfDualityCat

/-- The free monoidal category on a self-duality whose closed circle acts centrally on the
generating object. Only the two snakes and this one extra equation are imposed. -/
abbrev CircleCentralSelfDualityCat : Type :=
  CategoryTheory.Quotient (HomRel.MonoidalClosure CircleCentralSelfDualityCat.Rel)

namespace CircleCentralSelfDualityCat

/-- The strong monoidal quotient functor imposing circle centrality. -/
abbrev quotientFunctor : FreeSelfDualityCat ⥤ CircleCentralSelfDualityCat :=
  CategoryTheory.Quotient.functor (HomRel.MonoidalClosure Rel)

/-- The self-dual generating object. -/
abbrev generator : CircleCentralSelfDualityCat :=
  quotientFunctor.obj FreeSelfDualityCat.generator

/-- The self-duality descends along the strong monoidal quotient functor. -/
instance : ExactPairing generator generator where
  coevaluation' :=
    quotientFunctor.map (η_ FreeSelfDualityCat.generator FreeSelfDualityCat.generator)
  evaluation' :=
    quotientFunctor.map (ε_ FreeSelfDualityCat.generator FreeSelfDualityCat.generator)
  coevaluation_evaluation' := by
    rw [CategoryTheory.Quotient.associator_inv_obj,
      CategoryTheory.Quotient.rightUnitor_hom_obj,
      CategoryTheory.Quotient.leftUnitor_inv_obj,
      CategoryTheory.Quotient.whiskerLeft_map, CategoryTheory.Quotient.map_whiskerRight,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg quotientFunctor.map
      (ExactPairing.coevaluation_evaluation
        FreeSelfDualityCat.generator FreeSelfDualityCat.generator)
  evaluation_coevaluation' := by
    rw [CategoryTheory.Quotient.associator_hom_obj,
      CategoryTheory.Quotient.leftUnitor_hom_obj,
      CategoryTheory.Quotient.rightUnitor_inv_obj,
      CategoryTheory.Quotient.whiskerLeft_map, CategoryTheory.Quotient.map_whiskerRight,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg quotientFunctor.map
      (ExactPairing.evaluation_coevaluation
        FreeSelfDualityCat.generator FreeSelfDualityCat.generator)

/-- The generating cup is the class of the free cup. -/
theorem coevaluation_generator :
    η_ generator generator =
      quotientFunctor.map (η_ FreeSelfDualityCat.generator FreeSelfDualityCat.generator) := (rfl)

/-- The generating cap is the class of the free cap. -/
theorem evaluation_generator :
    ε_ generator generator =
      quotientFunctor.map (ε_ FreeSelfDualityCat.generator FreeSelfDualityCat.generator) := (rfl)

/-- The quotient functor preserves the generating self-duality. -/
theorem quotientFunctor_sendsSelfDuality :
    SendsSelfDuality quotientFunctor generator (Iso.refl generator) where
  coevaluation := by simp [coevaluation_generator, quotientFunctor]
  evaluation := by simp [evaluation_generator, quotientFunctor]

/-- The closed circle acts centrally on the generator of the quotient. -/
@[simp]
theorem circlesCommuteAt_generator :
    CirclesCommuteAt (η_ generator generator ≫ ε_ generator generator) generator := by
  rw [circlesCommuteAt_iff, coevaluation_generator, evaluation_generator,
    CategoryTheory.Quotient.rightUnitor_inv_obj, CategoryTheory.Quotient.rightUnitor_hom_obj,
    CategoryTheory.Quotient.leftUnitor_inv_obj, CategoryTheory.Quotient.leftUnitor_hom_obj]
  simp only [← Functor.map_comp, CategoryTheory.Quotient.whiskerLeft_map,
    CategoryTheory.Quotient.map_whiskerRight]
  exact CategoryTheory.Quotient.sound _ (.of Rel.circle)

/-- A monoidal natural transformation out of the quotient is determined by its component
at the generator. -/
theorem natTrans_ext {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {F G : CircleCentralSelfDualityCat ⥤ C} [F.Monoidal] [G.LaxMonoidal] {α β : F ⟶ G}
    [NatTrans.IsMonoidal α] [NatTrans.IsMonoidal β]
    (h : α.app generator = β.app generator) : α = β :=
  CategoryTheory.Quotient.natTrans_ext _ _
    (TensorSignature.Presented.natTrans_ext (fun _ ↦ h))

section Lift

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (V : C) [ExactPairing V V]
  (hc : CirclesCommuteAt (η_ V V ≫ ε_ V V) V)

include hc in
/-- The free interpretation identifies the extra circle relation. -/
theorem map_eq_of_rel ⦃X Y : FreeSelfDualityCat⦄ ⦃f g : X ⟶ Y⦄ (h : Rel f g) :
    (FreeSelfDualityCat.lift V).map f = (FreeSelfDualityCat.lift V).map g := by
  cases h
  have hd : ε (FreeSelfDualityCat.lift V) ≫
      (FreeSelfDualityCat.lift V).map
        (η_ FreeSelfDualityCat.generator FreeSelfDualityCat.generator ≫
          ε_ FreeSelfDualityCat.generator FreeSelfDualityCat.generator) ≫
      η (FreeSelfDualityCat.lift V) = η_ V V ≫ ε_ V V := by
    rw [Functor.map_comp, FreeSelfDualityCat.lift_map_coevaluation,
      FreeSelfDualityCat.lift_map_evaluation, TensorSignature.Presented.lift_ε,
      TensorSignature.Presented.lift_η]
    exact (by simp : 𝟙 (𝟙_ C) ≫ (η_ V V ≫ ε_ V V) ≫ 𝟙 (𝟙_ C) = η_ V V ≫ ε_ V V)
  have hcentral := ObjectProperty.prop_of_iso (CirclesCommuteAt (η_ V V ≫ ε_ V V))
    (FreeSelfDualityCat.liftObjIso V).symm hc
  rw [circlesCommuteAt_iff, ← hd] at hcentral
  simpa only [Functor.map_comp, Functor.Monoidal.map_rightUnitor_inv,
    Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_rightUnitor,
    Functor.Monoidal.map_leftUnitor_inv, Functor.Monoidal.map_whiskerRight,
    Functor.Monoidal.map_leftUnitor, whiskerLeft_comp, comp_whiskerRight,
    Category.assoc, Functor.Monoidal.μ_δ_assoc] using hcentral

/-- Interpret the presented self-duality in any monoidal category, provided its circle is
central at the chosen object `V`. -/
abbrev lift : CircleCentralSelfDualityCat ⥤ C :=
  CategoryTheory.Quotient.lift _ (FreeSelfDualityCat.lift V) fun _ _ _ _ h =>
    HomRel.MonoidalClosure.map_eq (map_eq_of_rel V hc) h

/-- The interpretation on an object represented in the free self-duality category. -/
@[simp]
theorem lift_obj (X : FreeSelfDualityCat) :
    (lift V hc).obj (quotientFunctor.obj X) = (FreeSelfDualityCat.lift V).obj X := (rfl)

/-- The interpretation on a morphism represented in the free self-duality category. -/
@[simp]
theorem lift_map {X Y : FreeSelfDualityCat} (f : X ⟶ Y) :
    (lift V hc).map (quotientFunctor.map f) = (FreeSelfDualityCat.lift V).map f := (rfl)

/-- The tensor comparison of the interpretation is the identity. -/
@[simp]
theorem lift_μ (X Y : CircleCentralSelfDualityCat) : μ (lift V hc) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_μ _ _ X.as Y.as).trans
    (TensorSignature.Presented.lift_μ _ _ _ X.as Y.as)

/-- The inverse tensor comparison of the interpretation is the identity. -/
@[simp]
theorem lift_δ (X Y : CircleCentralSelfDualityCat) : δ (lift V hc) X Y = 𝟙 _ :=
  (CategoryTheory.Quotient.lift_δ _ _ X.as Y.as).trans
    (TensorSignature.Presented.lift_δ _ _ _ X.as Y.as)

/-- The image of the generating object is identified with `V`. -/
def liftObjIso : (lift V hc).obj generator ≅ V :=
  FreeSelfDualityCat.liftObjIso V

/-- The generator identification has identity forward map. -/
@[simp]
theorem liftObjIso_hom : (liftObjIso V hc).hom = 𝟙 V :=
  FreeSelfDualityCat.liftObjIso_hom V

/-- The generator identification has identity inverse map. -/
@[simp]
theorem liftObjIso_inv : (liftObjIso V hc).inv = 𝟙 V :=
  FreeSelfDualityCat.liftObjIso_inv V

/-- The interpretation sends the generating cup to the chosen coevaluation. -/
@[simp]
theorem lift_map_coevaluation : (lift V hc).map (η_ generator generator) = η_ V V := by
  rw [coevaluation_generator, CategoryTheory.Quotient.lift_map_functor_map,
    FreeSelfDualityCat.lift_map_coevaluation]

/-- The interpretation sends the generating cap to the chosen evaluation. -/
@[simp]
theorem lift_map_evaluation : (lift V hc).map (ε_ generator generator) = ε_ V V := by
  rw [evaluation_generator, CategoryTheory.Quotient.lift_map_functor_map,
    FreeSelfDualityCat.lift_map_evaluation]

/-- The interpretation preserves the specified self-duality. -/
theorem lift_sendsSelfDuality : SendsSelfDuality (lift V hc) V (liftObjIso V hc) where
  -- Computing the comparison morphisms leaves identities on tensor words; give their
  -- concrete types so simplification does not need to unfold the interpretation on objects.
  coevaluation := by
    simp only [lift_map_coevaluation, liftObjIso_inv, CategoryTheory.Quotient.lift_ε,
      CategoryTheory.Quotient.lift_μ, TensorSignature.Presented.lift_ε,
      TensorSignature.Presented.lift_μ]
    exact (by simp : 𝟙 (𝟙_ C) ≫ η_ V V = η_ V V ≫ (𝟙 V ⊗ₘ 𝟙 V) ≫ 𝟙 (V ⊗ V))
  evaluation := by
    simp only [lift_map_evaluation, liftObjIso_inv, CategoryTheory.Quotient.lift_η,
      CategoryTheory.Quotient.lift_μ, TensorSignature.Presented.lift_η,
      TensorSignature.Presented.lift_μ]
    exact (by simp : (𝟙 V ⊗ₘ 𝟙 V) ≫ 𝟙 (V ⊗ V) ≫ ε_ V V ≫ 𝟙 (𝟙_ C) = ε_ V V)

/-- A strong monoidal functor sending the generating self-duality to that of `V` is
monoidally naturally isomorphic to its interpretation, compatibly with the identification
of the generator. -/
theorem lift_unique (G : CircleCentralSelfDualityCat ⥤ C) [G.Monoidal]
    (e : G.obj generator ≅ V) (he : SendsSelfDuality G V e) :
    ∃ i : G ≅ lift V hc, NatTrans.IsMonoidal i.hom ∧
      i.hom.app generator = e.hom ≫ (liftObjIso V hc).inv := by
  obtain ⟨i, hi, heq⟩ := FreeSelfDualityCat.lift_unique V (quotientFunctor ⋙ G) e
    (by simpa using quotientFunctor_sendsSelfDuality.comp he)
  have := hi
  let j : quotientFunctor ⋙ G ≅ quotientFunctor ⋙ lift V hc :=
    i ≪≫ (CategoryTheory.Quotient.lift.isLift _ _ _).symm
  have : NatTrans.IsMonoidal j.hom := by dsimp [j]; infer_instance
  refine ⟨CategoryTheory.Quotient.natIsoLift _ j, ?_, ?_⟩
  · rw [CategoryTheory.Quotient.natIsoLift_hom]
    infer_instance
  · simpa [j, generator, liftObjIso] using heq

end Lift

end CircleCentralSelfDualityCat

end TauCeti
