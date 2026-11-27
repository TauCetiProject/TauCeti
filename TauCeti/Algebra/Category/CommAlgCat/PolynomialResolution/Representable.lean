/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Augmentation

/-!
# Evaluating a simplicial polynomial resolution on a polynomial algebra

For an augmented simplicial algebra over `B`, evaluation of the degreewise representable
presheaves at `T → B` gives the simplicial set of algebra maps from `T` over `B`. If `T` is
polynomial and the underlying augmentation is a trivial Kan fibration, each polynomial
variable lifts independently across any monomorphism of simplicial sets. The resulting
augmentation to a singleton is a trivial Kan fibration. On free abelian groups it gives a
quasi-isomorphism to the free abelian group on one generator in degree zero.

## References

* The Stacks Project, the polynomial test-object argument in the proof of Lemma 92.4.1
  (Tag 08PS) and Remark 92.5.5 (Tag 08QI).
-/

public noncomputable section

universe u v

open CategoryTheory CommAlgCat Limits MorphismProperty Opposite

namespace CategoryTheory.SimplicialObject.Augmented

variable {A : Type u} [CommRing A] {ι : Type v}
  (P : SimplicialObject.Augmented (CommAlgCat.{max u v} A))
  (t : of A (MvPolynomial ι A) ⟶ P.right)

/-- The simplicial set of lifts of a polynomial algebra map through an augmented simplicial
algebra. Its simplices are morphisms in the slice over the base, via
`polynomialLifts.objEquiv`. -/
def polynomialLifts : SSet.{max u v} :=
  Over.lift P.left P.hom ⋙ coyoneda.obj (op (Over.mk t))

namespace polynomialLifts

/-- In degree `n`, a simplex is an algebra map from the polynomial algebra to `P.left.obj n`
over the base of the augmentation. -/
def objEquiv {n : SimplexCategoryᵒᵖ} :
    (P.polynomialLifts t).obj n ≃ (Over.mk t ⟶ Over.mk (P.hom.app n)) :=
  Equiv.refl _

end polynomialLifts

/-- A simplicial operator acts on a lift by postcomposition with the algebra map. -/
@[simp] lemma polynomialLifts_map_left {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (P.polynomialLifts t).obj n) :
    (polynomialLifts.objEquiv P t ((P.polynomialLifts t).map f x)).left =
      (polynomialLifts.objEquiv P t x).left ≫ P.left.map f := (rfl)

namespace polynomialLifts

/-- Read the image of a polynomial variable in each simplicial degree. -/
def evalVar (a : ι) : P.polynomialLifts t ⟶ P.left ⋙ forget (CommAlgCat.{max u v} A) where
  app _ := ↾fun x ↦ (objEquiv P t x).left.hom (MvPolynomial.X a)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    simp only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply, polynomialLifts_map_left,
      CommAlgCat.hom_comp, AlgHom.comp_apply]
    -- The forgetful functor acts by the underlying algebra homomorphism.
    rfl

/-- Evaluation at a variable sends every lift to its prescribed image under the augmentation. -/
@[simp] lemma evalVar_comp_augmentation (a : ι) :
    evalVar P t a ≫ Functor.whiskerRight P.hom (forget (CommAlgCat.{max u v} A)) =
      SSet.const (t.hom (MvPolynomial.X a)) := by
  ext n f
  exact congrArg (fun g ↦ g.hom (MvPolynomial.X a)) (Over.w (objEquiv P t f))

private lemma obj_ext {n : SimplexCategoryᵒᵖ} {x y : (P.polynomialLifts t).obj n}
    (h : ∀ a, (objEquiv P t x).left.hom (MvPolynomial.X a) =
      (objEquiv P t y).left.hom (MvPolynomial.X a)) : x = y := by
  apply (objEquiv P t).injective
  exact Over.OverMorphism.ext (CommAlgCat.hom_ext (MvPolynomial.algHom_ext h))

/-- A family of simplicial maps giving the images of the variables over the prescribed base
elements determines a map into the simplicial set of polynomial lifts. -/
def lift {K : SSet.{max u v}} (s : ι → (K ⟶ P.left ⋙ forget (CommAlgCat.{max u v} A)))
    (hs : ∀ a, s a ≫ Functor.whiskerRight P.hom (forget (CommAlgCat.{max u v} A)) =
      SSet.const (t.hom (MvPolynomial.X a))) :
    K ⟶ P.polynomialLifts t where
  app n := ↾fun x ↦ (objEquiv P t).symm
    (Over.homMk (ofHom (MvPolynomial.aeval (S₁ := P.left.obj n) (fun a ↦ (s a).app n x))) (by
      apply CommAlgCat.hom_ext
      apply MvPolynomial.algHom_ext
      intro a
      -- Expose the two algebra maps in the slice triangle to evaluate on a generator.
      change (P.hom.app n).hom (MvPolynomial.aeval _ (MvPolynomial.X a)) = _
      simpa using ConcreteCategory.congr_hom (NatTrans.congr_app (hs a) n) x))
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply obj_ext P t
    intro a
    simp only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply, polynomialLifts_map_left,
      Equiv.apply_symm_apply, Over.homMk_left, CommAlgCat.hom_comp, AlgHom.comp_apply,
      CommAlgCat.hom_ofHom]
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact NatTrans.naturality_apply (s a) f x

/-- Evaluation at a variable of a simplex reads the corresponding slice map on that generator. -/
@[simp↓]
lemma evalVar_app {n : SimplexCategoryᵒᵖ} (a : ι) (x : (P.polynomialLifts t).obj n) :
    (evalVar P t a).app n x = (objEquiv P t x).left.hom (MvPolynomial.X a) := (rfl)

/-- The map constructed from variable images recovers those images upon evaluation. -/
@[simp] lemma lift_comp_evalVar {K : SSet.{max u v}}
    (s : ι → (K ⟶ P.left ⋙ forget (CommAlgCat.{max u v} A)))
    (hs : ∀ a, s a ≫ Functor.whiskerRight P.hom (forget (CommAlgCat.{max u v} A)) =
      SSet.const (t.hom (MvPolynomial.X a))) (a : ι) :
    lift P t s hs ≫ evalVar P t a = s a := by
  ext n x
  exact MvPolynomial.aeval_X (S₁ := P.left.obj n) (fun b ↦ (s b).app n x) a

/-- Maps into the simplicial set of polynomial lifts agree if they agree on every variable. -/
@[ext] lemma hom_ext {K : SSet.{max u v}} {f g : K ⟶ P.polynomialLifts t}
    (h : ∀ a, f ≫ evalVar P t a = g ≫ evalVar P t a) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply obj_ext P t
  intro a
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h a) n) x

end polynomialLifts

/-- Evaluating a resolution with a trivial Kan augmentation at a polynomial algebra over its
base gives a simplicial set whose map to the point is a trivial Kan fibration. -/
theorem rlp_monomorphisms_polynomialLifts
    (hP : (monomorphisms SSet).rlp (Functor.whiskerRight P.hom (forget _))) :
    (monomorphisms SSet).rlp (P.polynomialLifts t).toAugmented.hom := by
  intro K L i (hi : Mono i)
  have := hP i (monomorphisms.infer_property i)
  refine ⟨fun {f b} _ ↦ ?_⟩
  have sq (a : ι) : CommSq (f ≫ polynomialLifts.evalVar P t a) i
      (Functor.whiskerRight P.hom (forget _)) (SSet.const (t.hom (MvPolynomial.X a))) :=
    ⟨by simp only [Category.assoc, polynomialLifts.evalVar_comp_augmentation, SSet.comp_const]⟩
  refine ⟨⟨{ l := polynomialLifts.lift P t (fun a ↦ (sq a).lift) (fun a ↦ (sq a).fac_right),
              fac_right := (Functor.isTerminalConst _ Types.isTerminalPUnit).hom_ext _ _,
              fac_left := ?_ }⟩⟩
  apply polynomialLifts.hom_ext
  intro a
  rw [Category.assoc, polynomialLifts.lift_comp_evalVar, (sq a).fac_left]

/-- Objectwise exactness of the augmented complex of free abelian representables: evaluating
at a polynomial algebra over the base resolves the free abelian group on one generator. -/
theorem quasiIso_free_polynomialLifts
    (hP : (monomorphisms SSet).rlp (Functor.whiskerRight P.hom (forget _))) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((SimplicialObject.Augmented.whiskering _ _).obj AddCommGrpCat.free).obj
        (P.polynomialLifts t).toAugmented)) :=
  homotopyEquivalences_le_quasiIso _ _ _
    (SSet.Augmented.homotopyEquivalences_ε_of_rlp_monomorphisms _
      (rlp_monomorphisms_polynomialLifts P t hP) AddCommGrpCat.free)

end CategoryTheory.SimplicialObject.Augmented
