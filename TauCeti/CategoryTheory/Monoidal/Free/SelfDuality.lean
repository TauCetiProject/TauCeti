/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Presentation
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# The free monoidal category on a self-dual object

The monoidal category `TauCeti.FreeSelfDualityCat` is presented by one generating object `X`,
two generating morphisms `cup : 𝟙_ ⟶ X ⊗ X` and `cap : X ⊗ X ⟶ 𝟙_`, and exactly the two zigzag
(snake) equations saying that `cup` and `cap` are the coevaluation and evaluation of an exact
pairing `ExactPairing X X`. No value is assigned to the closed circle `cup ≫ cap`, an
endomorphism of the unit.

Its universal property says that every self-duality in an arbitrary monoidal category `C`, that
is, every object `V` with an exact pairing `ExactPairing V V`, is the image of the generating one
under a strong monoidal functor out of `FreeSelfDualityCat`, unique up to monoidal natural
isomorphism:

* `TauCeti.FreeSelfDualityCat.lift V` is a strong monoidal functor sending the generator to `V`
  along `TauCeti.FreeSelfDualityCat.liftObjIso V`, and the generating self-duality to the given
  one (`TauCeti.FreeSelfDualityCat.lift_sendsSelfDuality`);
* `TauCeti.FreeSelfDualityCat.lift_unique`: any strong monoidal functor sending the generating
  self-duality to that of `V` along an isomorphism `e` is monoidally isomorphic to `lift V`, by an
  isomorphism whose component at the generator is `e` followed by the inverse of `liftObjIso V`.

The condition that a strong monoidal functor `F` sends a self-duality of `g` to one of `V` along
`e : F.obj g ≅ V` is `TauCeti.SendsSelfDuality F V e`, from
`TauCeti.CategoryTheory.Monoidal.Rigid.Functor`: the coevaluation and evaluation of `V`
are the images under `F` of those of `g`, transported along `e` and the comparison morphisms of
`F`.

Only the zigzag equations are imposed. In particular, no equation identifies the left and right
actions of the circle on `X` (its whiskerings with `X`, conjugated by the unitors), whereas they
agree in the Temperley–Lieb diagram category, which records only the number of circles.

## References

* A. Joyal and R. Street, *The geometry of tensor calculus I*, Adv. Math. 88 (1991), §1
  (presentations of monoidal categories by tensor schemes and relations).
* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845
  (cups, caps and the zigzag relations).
-/

public section

universe u v

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

namespace FreeSelfDualityCat

/-- The two generating morphisms of the free self-duality: the cup `𝟙_ ⟶ X ⊗ X` and the cap
`X ⊗ X ⟶ 𝟙_`. -/
inductive Coupon : Type
  | /-- The cup, the coevaluation `𝟙_ ⟶ X ⊗ X`. -/
    cup
  | /-- The cap, the evaluation `X ⊗ X ⟶ 𝟙_`. -/
    cap

/-- The tensor signature of a self-dual object: one generating object, and the cup and cap
coupons between the empty word and the word of length two. -/
abbrev signature : TensorSignature.{0, 0} where
  Obj := Unit
  Coupon := Coupon
  src
    | .cup => .unit
    | .cap => .tensor (.of ()) (.of ())
  tgt
    | .cup => .tensor (.of ()) (.of ())
    | .cap => .unit

/-- The generating object of the free monoidal category on `FreeSelfDualityCat.signature`. -/
abbrev freeGenerator : signature.FreeMonoidal :=
  .of ()

/-- The cup in the free monoidal category on `FreeSelfDualityCat.signature`. -/
abbrev freeCup : 𝟙_ signature.FreeMonoidal ⟶ freeGenerator ⊗ freeGenerator :=
  TensorSignature.FreeMonoidal.coupon (S := signature) Coupon.cup

/-- The cap in the free monoidal category on `FreeSelfDualityCat.signature`. -/
abbrev freeCap : freeGenerator ⊗ freeGenerator ⟶ 𝟙_ signature.FreeMonoidal :=
  TensorSignature.FreeMonoidal.coupon (S := signature) Coupon.cap

/-- The two zigzag equations between the cup and the cap, in the form of the axioms of
`ExactPairing`. -/
inductive Rel : HomRel signature.FreeMonoidal
  | coevaluation_evaluation :
      Rel (freeGenerator ◁ freeCup ≫ (α_ _ _ _).inv ≫ freeCap ▷ freeGenerator)
        ((ρ_ _).hom ≫ (λ_ _).inv)
  | evaluation_coevaluation :
      Rel (freeCup ▷ freeGenerator ≫ (α_ _ _ _).hom ≫ freeGenerator ◁ freeCap)
        ((λ_ _).hom ≫ (ρ_ _).inv)

end FreeSelfDualityCat

/-- The free monoidal category on a self-dual object: the monoidal category presented by one
generating object `X`, a cup `𝟙_ ⟶ X ⊗ X` and a cap `X ⊗ X ⟶ 𝟙_`, subject only to the two zigzag
equations. -/
abbrev FreeSelfDualityCat : Type :=
  FreeSelfDualityCat.signature.Presented FreeSelfDualityCat.Rel

namespace FreeSelfDualityCat

open TensorSignature

/-- The generating object of `FreeSelfDualityCat`. -/
abbrev generator : FreeSelfDualityCat :=
  (Presented.quotientFunctor Rel).obj freeGenerator

/-- The generating object of `FreeSelfDualityCat` is self-dual, with the cup as coevaluation and
the cap as evaluation. -/
instance : ExactPairing generator generator where
  coevaluation' := (Presented.quotientFunctor Rel).map freeCup
  evaluation' := (Presented.quotientFunctor Rel).map freeCap
  coevaluation_evaluation' := Presented.sound Rel.coevaluation_evaluation
  evaluation_coevaluation' := Presented.sound Rel.evaluation_coevaluation

/-- The coevaluation of the generator is the class of the cup. -/
theorem coevaluation_generator :
    η_ generator generator = (Presented.quotientFunctor Rel).map freeCup :=
  (rfl)

/-- The evaluation of the generator is the class of the cap. -/
theorem evaluation_generator :
    ε_ generator generator = (Presented.quotientFunctor Rel).map freeCap :=
  (rfl)

section Lift

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (V : C) [ExactPairing V V]

/-- The images of the cup and the cap determined by a self-duality of `V`: the coevaluation and
the evaluation of `V`. -/
def liftCoupon :
    ∀ c : signature.Coupon,
      FreeMonoidalCategory.projectObj (fun _ ↦ V) (signature.src c) ⟶
        FreeMonoidalCategory.projectObj (fun _ ↦ V) (signature.tgt c)
  | .cup => η_ V V
  | .cap => ε_ V V

private theorem freeLift_map_freeCup :
    (FreeMonoidal.lift (fun _ ↦ V) (liftCoupon V)).map freeCup = η_ V V :=
  FreeMonoidal.lift_map_coupon (S := signature) (fun _ ↦ V) (liftCoupon V) Coupon.cup

private theorem freeLift_map_freeCap :
    (FreeMonoidal.lift (fun _ ↦ V) (liftCoupon V)).map freeCap = ε_ V V :=
  FreeMonoidal.lift_map_coupon (S := signature) (fun _ ↦ V) (liftCoupon V) Coupon.cap

/-- The interpretation of the free monoidal category on `FreeSelfDualityCat.signature` determined
by a self-duality satisfies the zigzag equations. -/
theorem map_eq_map_of_rel ⦃X Y : signature.FreeMonoidal⦄ ⦃f g : X ⟶ Y⦄ (h : Rel f g) :
    (FreeMonoidal.lift (fun _ ↦ V) (liftCoupon V)).map f =
      (FreeMonoidal.lift (fun _ ↦ V) (liftCoupon V)).map g := by
  cases h with
  | coevaluation_evaluation =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
      FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_associator_inv,
      FreeMonoidal.lift_map_rightUnitor_hom, FreeMonoidal.lift_map_leftUnitor_inv,
      freeLift_map_freeCup, freeLift_map_freeCap]
    exact ExactPairing.coevaluation_evaluation V V
  | evaluation_coevaluation =>
    simp only [Functor.map_comp, FreeMonoidal.lift_map_whiskerLeft,
      FreeMonoidal.lift_map_whiskerRight, FreeMonoidal.lift_map_associator_hom,
      FreeMonoidal.lift_map_leftUnitor_hom, FreeMonoidal.lift_map_rightUnitor_inv,
      freeLift_map_freeCup, freeLift_map_freeCap]
    exact ExactPairing.evaluation_coevaluation V V

/-- The strong monoidal functor out of the free monoidal category on a self-dual object determined
by a self-duality `ExactPairing V V`: it sends the generator to `V` (along `liftObjIso V`) and the
generating self-duality to that of `V` (`lift_sendsSelfDuality`). -/
abbrev lift : FreeSelfDualityCat ⥤ C :=
  Presented.lift (fun _ ↦ V) (liftCoupon V) (map_eq_map_of_rel V)

/-- The image of the generator under `lift V` is `V`. -/
def liftObjIso : (lift V).obj generator ≅ V :=
  Iso.refl V

/-- The identification of the image of the generator under `lift V` with `V` is the identity. -/
@[simp]
theorem liftObjIso_hom : (liftObjIso V).hom = 𝟙 V :=
  (rfl)

/-- The identification of the image of the generator under `lift V` with `V` is the identity. -/
@[simp]
theorem liftObjIso_inv : (liftObjIso V).inv = 𝟙 V :=
  (rfl)

/-- `lift V` sends the cup to the coevaluation of `V`. -/
@[simp]
theorem lift_map_coevaluation : (lift V).map (η_ generator generator) = η_ V V := by
  rw [coevaluation_generator, Presented.lift_map, freeLift_map_freeCup]

/-- `lift V` sends the cap to the evaluation of `V`. -/
@[simp]
theorem lift_map_evaluation : (lift V).map (ε_ generator generator) = ε_ V V := by
  rw [evaluation_generator, Presented.lift_map, freeLift_map_freeCap]

/-- `lift V` sends the generating self-duality to the self-duality of `V`. -/
theorem lift_sendsSelfDuality : SendsSelfDuality (lift V) V (liftObjIso V) where
  -- After computing the comparisons of `lift V`, the objects `(lift V).obj _` in the implicit
  -- arguments agree with the corresponding words in `V` only up to unfolding `lift`, so the
  -- remaining identities are cancelled in `C` and the result is matched by unification.
  coevaluation := by
    rw [lift_map_coevaluation, Presented.lift_ε, Presented.lift_μ, liftObjIso_inv]
    exact (by simp : 𝟙 (𝟙_ C) ≫ η_ V V = η_ V V ≫ (𝟙 V ⊗ₘ 𝟙 V) ≫ 𝟙 (V ⊗ V))
  evaluation := by
    rw [lift_map_evaluation, Presented.lift_η, Presented.lift_μ, liftObjIso_inv]
    exact (by simp : (𝟙 V ⊗ₘ 𝟙 V) ≫ 𝟙 (V ⊗ V) ≫ ε_ V V ≫ 𝟙 (𝟙_ C) = ε_ V V)

/-- Two strong monoidal functors sending the generating self-duality to the self-duality of `V`
are compatible with the cup and the cap, along the isomorphisms of words induced by their
identifications with `V`. -/
private theorem map_coupon_comp_wordIso_hom {G H : FreeSelfDualityCat ⥤ C} [G.Monoidal]
    [H.Monoidal] {eG : G.obj generator ≅ V} {eH : H.obj generator ≅ V}
    (hG : SendsSelfDuality G V eG) (hH : SendsSelfDuality H V eH) (c : signature.Coupon) :
    G.map ((Presented.quotientFunctor Rel).map (FreeMonoidal.coupon c)) ≫
        (FreeMonoidal.wordIso (Presented.quotientFunctor Rel ⋙ G)
          (Presented.quotientFunctor Rel ⋙ H) (fun _ ↦ eG ≪≫ eH.symm) (signature.tgt c)).hom =
      (FreeMonoidal.wordIso (Presented.quotientFunctor Rel ⋙ G)
          (Presented.quotientFunctor Rel ⋙ H) (fun _ ↦ eG ≪≫ eH.symm) (signature.src c)).hom ≫
        H.map ((Presented.quotientFunctor Rel).map (FreeMonoidal.coupon c)) := by
  cases c with
  | cup =>
    -- Solve the first equation of `SendsSelfDuality` for the image of the cup.
    have hG' : G.map (η_ generator generator) =
        η G ≫ η_ V V ≫ (eG.inv ⊗ₘ eG.inv) ≫ μ G generator generator := by
      rw [← hG.coevaluation, Functor.Monoidal.η_ε_assoc]
    have hH' : H.map (η_ generator generator) =
        η H ≫ η_ V V ≫ (eH.inv ⊗ₘ eH.inv) ≫ μ H generator generator := by
      rw [← hH.coevaluation, Functor.Monoidal.η_ε_assoc]
    -- By definition of `signature`, the cup goes from the empty word to `X ⊗ X`; restate the goal
    -- with these words so that the computation rules of `wordIso` apply.
    change G.map (η_ generator generator) ≫
        (FreeMonoidal.wordIso (Presented.quotientFunctor Rel ⋙ G)
          (Presented.quotientFunctor Rel ⋙ H) (fun _ ↦ eG ≪≫ eH.symm)
          (freeGenerator ⊗ freeGenerator).as).hom =
      (FreeMonoidal.wordIso (Presented.quotientFunctor Rel ⋙ G)
          (Presented.quotientFunctor Rel ⋙ H) (fun _ ↦ eG ≪≫ eH.symm)
          (𝟙_ signature.FreeMonoidal).as).hom ≫ H.map (η_ generator generator)
    simp [hG', hH']
  | cap =>
    -- Solve the second equation of `SendsSelfDuality` for the image of the cap.
    have hG' : G.map (ε_ generator generator) =
        δ G generator generator ≫ (eG.hom ⊗ₘ eG.hom) ≫ ε_ V V ≫ ε G := by
      rw [← hG.evaluation]
      simp
    have hH' : H.map (ε_ generator generator) =
        δ H generator generator ≫ (eH.hom ⊗ₘ eH.hom) ≫ ε_ V V ≫ ε H := by
      rw [← hH.evaluation]
      simp
    -- By definition of `signature`, the cap goes from `X ⊗ X` to the empty word; restate the goal
    -- with these words so that the computation rules of `wordIso` apply.
    change G.map (ε_ generator generator) ≫
        (FreeMonoidal.wordIso (Presented.quotientFunctor Rel ⋙ G)
          (Presented.quotientFunctor Rel ⋙ H) (fun _ ↦ eG ≪≫ eH.symm)
          (𝟙_ signature.FreeMonoidal).as).hom =
      (FreeMonoidal.wordIso (Presented.quotientFunctor Rel ⋙ G)
          (Presented.quotientFunctor Rel ⋙ H) (fun _ ↦ eG ≪≫ eH.symm)
          (freeGenerator ⊗ freeGenerator).as).hom ≫ H.map (ε_ generator generator)
    simp [hG', hH']

/-- **Uniqueness of the lift.** A strong monoidal functor `G` out of the free monoidal category on
a self-dual object which sends the generating self-duality to the self-duality of `V` along
`e : G.obj generator ≅ V` is isomorphic to `lift V` by a monoidal natural isomorphism whose
component at the generator is `e` followed by the inverse of `liftObjIso V`. -/
theorem lift_unique (G : FreeSelfDualityCat ⥤ C) [G.Monoidal] (e : G.obj generator ≅ V)
    (he : SendsSelfDuality G V e) :
    ∃ i : G ≅ lift V, NatTrans.IsMonoidal i.hom ∧
      i.hom.app generator = e.hom ≫ (liftObjIso V).inv :=
  ⟨Presented.monoidalNatIso G (lift V) (fun _ ↦ e ≪≫ (liftObjIso V).symm)
      (map_coupon_comp_wordIso_hom V he (lift_sendsSelfDuality V)),
    inferInstance, by rw [Presented.monoidalNatIso_hom_app_of, Iso.trans_hom, Iso.symm_hom]⟩

end Lift

end FreeSelfDualityCat

end TauCeti
