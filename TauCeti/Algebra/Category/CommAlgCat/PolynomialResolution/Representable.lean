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
algebra. Its body is exposed so callers can use its simplices directly as morphisms in
the slice over the base. -/
@[expose] def polynomialLifts : SSet.{max u v} :=
  Over.lift P.left P.hom ⋙ coyoneda.obj (op (Over.mk t))

/-- A simplicial operator acts on a lift by postcomposition with the algebra map. -/
@[simp] lemma polynomialLifts_map_left {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (P.polynomialLifts t).obj n) :
    (((P.polynomialLifts t).map f) x).left = x.left ≫ P.left.map f := (rfl)

private abbrev underlying := P.left ⋙ forget (CommAlgCat.{max u v} A)

private abbrev augmentation := Functor.whiskerRight P.hom (forget (CommAlgCat.{max u v} A))

/-- Read the image of a polynomial variable in each simplicial degree. -/
private def evalVar (a : ι) : P.polynomialLifts t ⟶ underlying P where
  app _ := ↾fun f ↦ f.left.hom (MvPolynomial.X a)
  naturality _ _ _ := rfl

private lemma evalVar_comp (a : ι) :
    evalVar P t a ≫ augmentation P = SSet.const (t.hom (MvPolynomial.X a)) := by
  ext n f
  exact congrArg (fun g ↦ g.hom (MvPolynomial.X a)) (Over.w f)

private def ofVariables {K : SSet.{max u v}} (s : ι → (K ⟶ underlying P))
    (hs : ∀ a, s a ≫ augmentation P = SSet.const (t.hom (MvPolynomial.X a))) :
    K ⟶ P.polynomialLifts t where
  app n := ↾fun x ↦ Over.homMk (ofHom (MvPolynomial.aeval (fun a ↦ (s a).app n x))) (by
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro a
    -- Expose the two algebra maps in the slice triangle to evaluate on a generator.
    change (P.hom.app n).hom (MvPolynomial.aeval _ (MvPolynomial.X a)) = _
    simpa using ConcreteCategory.congr_hom (NatTrans.congr_app (hs a) n) x)
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    intro a
    -- At a generator the two induced polynomial maps reduce to naturality of its image.
    change MvPolynomial.aeval _ (MvPolynomial.X a) =
      (P.left.map f).hom (MvPolynomial.aeval _ (MvPolynomial.X a))
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact NatTrans.naturality_apply (s a) f x

private lemma hom_ext_variables {K : SSet.{max u v}} {f g : K ⟶ P.polynomialLifts t}
    (h : ∀ a, f ≫ evalVar P t a = g ≫ evalVar P t a) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Over.OverMorphism.ext
  apply CommAlgCat.hom_ext
  apply MvPolynomial.algHom_ext
  intro a
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h a) n) x

/-- Evaluating a resolution with a trivial Kan augmentation at a polynomial algebra over its
base gives a simplicial set whose map to the point is a trivial Kan fibration. -/
theorem rlp_monomorphisms_polynomialLifts
    (hP : (monomorphisms SSet).rlp (Functor.whiskerRight P.hom (forget _))) :
    (monomorphisms SSet).rlp (P.polynomialLifts t).toAugmented.hom := by
  intro K L i (hi : Mono i)
  have := hP i (monomorphisms.infer_property i)
  refine ⟨fun {f b} _ ↦ ?_⟩
  have sq (a : ι) : CommSq (f ≫ evalVar P t a) i (augmentation P)
      (SSet.const (t.hom (MvPolynomial.X a))) :=
    ⟨by rw [Category.assoc, evalVar_comp]; rfl⟩
  let l := ofVariables P t (fun a ↦ (sq a).lift) (fun a ↦ (sq a).fac_right)
  refine ⟨⟨{ l := l,
              fac_right := (Functor.isTerminalConst _ Types.isTerminalPUnit).hom_ext _ _,
              fac_left := ?_ }⟩⟩
  apply hom_ext_variables
  intro a
  ext n x
  -- Specify the algebra carrier behind the underlying-set functor for polynomial evaluation.
  change MvPolynomial.aeval (S₁ := P.left.obj n) _ (MvPolynomial.X a) = _
  rw [MvPolynomial.aeval_X]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (sq a).fac_left n) x

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
