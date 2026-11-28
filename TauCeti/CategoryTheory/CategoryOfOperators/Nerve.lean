/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.CategoryOfOperators.SymmetricMonoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Pi

/-!
# Fibers of the symmetric operator nerve

The strict fiber over `⟨n⟩` of the nerve of the category of operators of `C` is the nerve
of the category of `n`-tuples in `C`. Coordinate evaluation therefore identifies it with
the product of `n` copies of `nerve C`. In particular, the fiber over `⟨1⟩` is strictly
isomorphic to `nerve C`, and the fiber over `⟨0⟩` is terminal.

The comparisons are degreewise comparisons of composable strings. This keeps the natural
universe `max u v` for a category with objects in `Type u` and morphisms in `Type v`:
the operator base `FinPointed` is taken in that universe.

## References

* J. Lurie, *Higher Algebra*, Construction 2.0.0.1.
-/

public section

universe v u

open CategoryTheory Limits MonoidalCategory Simplicial SSet

namespace TauCeti.CategoryOfOperators

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- Strings of families correspond to simplices in the strict fiber of the operator nerve. -/
noncomputable def nerveFiberSimplexEquiv (b : FinPointed.{max u v})
    (n : SimplexCategoryᵒᵖ) :
    (nerve (Fin b.len → C)).obj n ≃
      (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet).obj n :=
  Equiv.trans (β := (nerve ((toFinPointed C).Fiber b)).obj n)
   { toFun s := s ⋙ toFiber C b
     invFun s := s ⋙ (toFiber C b).strictInv
     left_inv s := (Functor.assoc s _ _).trans
       ((congrArg (s ⋙ ·) (toFiber C b).asIsomorphism.unit_eq.symm).trans (Functor.comp_id s))
     right_inv s := (Functor.assoc s _ _).trans
       ((congrArg (s ⋙ ·) (toFiber C b).asIsomorphism.counit_eq).trans (Functor.comp_id s)) }
    (nerve.fiberSimplexEquiv (toFinPointed C) b n)

/-- The underlying string of the comparison is the inclusion of the family in the
category of operators. -/
-- Normalize the subfunctor simplex type, also in implicit arguments, for simp matching.
@[simp]
lemma nerveFiberSimplexEquiv_apply_coe (b : FinPointed.{max u v})
    (n : SimplexCategoryᵒᵖ) (s : (nerve (Fin b.len → C)).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj] (nerveFiberSimplexEquiv C b n s).val) =
      s ⋙ ι C b :=
  (nerve.fiberSimplexEquiv_apply_coe (toFinPointed C) b n (s ⋙ toFiber C b)).trans
    ((Functor.assoc s _ _).trans (congrArg (s ⋙ ·) (toFiber_comp_fiberInclusion b)))

/-- The family comparison commutes with every simplicial operator. -/
lemma nerveFiberSimplexEquiv_naturality (b : FinPointed.{max u v})
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (s : (nerve (Fin b.len → C)).obj m) :
    nerveFiberSimplexEquiv C b n ((nerve (Fin b.len → C)).map f s) =
      (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet).map f
        (nerveFiberSimplexEquiv C b m s) := by
  apply Subtype.ext
  exact (nerveFiberSimplexEquiv_apply_coe C b n _).trans
    ((Functor.assoc (SimplexCategory.toCat.map f.unop).toFunctor s (ι C b)).trans
      (congrArg ((nerve (CategoryOfOperators C)).map f)
        (nerveFiberSimplexEquiv_apply_coe C b m s)).symm)

/-- The nerve of the category of families is the strict fiber of the operator nerve. -/
noncomputable def nerveFiberIso (b : FinPointed.{max u v}) :
    nerve (Fin b.len → C) ≅ fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) :=
  NatIso.ofComponents (fun n ↦ (nerveFiberSimplexEquiv C b n).toIso) fun f ↦ by
    ext s
    exact nerveFiberSimplexEquiv_naturality C b f s

/-- The forward comparison sends a string to its inclusion in the category of operators. -/
@[simp]
lemma nerveFiberIso_hom_app_coe (b : FinPointed.{max u v}) (n : SimplexCategoryᵒᵖ)
    (s : (nerve (Fin b.len → C)).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj] ((nerveFiberIso C b).hom.app n s).val) =
      s ⋙ ι C b :=
  nerveFiberSimplexEquiv_apply_coe C b n s

/-- The inverse comparison reconstructs the family string whose inclusion is the given
string in the fiber. -/
@[simp]
lemma nerveFiberIso_inv_app_comp (b : FinPointed.{max u v}) (n : SimplexCategoryᵒᵖ)
    (s : (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj]
      (nerveFiberIso C b).inv.app n s ⋙ ι C b) = s.val :=
  (nerveFiberIso_hom_app_coe C b n _).symm.trans
    (congrArg Subtype.val (ConcreteCategory.congr_hom
      (Iso.inv_hom_id_app (nerveFiberIso C b) n) s))

/-- Coordinate evaluation on the strict fiber of the operator nerve. -/
noncomputable def nerveFiberEval (b : FinPointed.{max u v}) (i : Fin b.len) :
    (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet) ⟶ nerve C :=
  (nerveFiberIso C b).inv ≫ nerveMap (CategoryTheory.Pi.eval (fun _ : Fin b.len ↦ C) i)

/-- Evaluation is the inverse family comparison followed by coordinate evaluation. -/
lemma nerveFiberEval_eq (b : FinPointed.{max u v}) (i : Fin b.len) :
    nerveFiberEval C b i =
      (nerveFiberIso C b).inv ≫ nerveMap (CategoryTheory.Pi.eval (fun _ : Fin b.len ↦ C) i) :=
  (rfl)

/-- Evaluation of a fiber simplex is its reconstructed string at the given coordinate. -/
-- Normalize the subfunctor simplex type in implicit arguments for simp matching.
@[simp]
lemma nerveFiberEval_app (b : FinPointed.{max u v}) (i : Fin b.len)
    (n : SimplexCategoryᵒᵖ)
    (s : (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet).obj n) :
    (dsimp% only [Subfunctor.toFunctor_obj] (nerveFiberEval C b i).app n s) =
      (nerveFiberIso C b).inv.app n s ⋙ CategoryTheory.Pi.eval (fun _ : Fin b.len ↦ C) i :=
  (rfl)

/-- Under the family comparison, evaluation is ordinary coordinate evaluation on strings. -/
@[reassoc (attr := simp)]
lemma nerveFiberIso_hom_eval (b : FinPointed.{max u v}) (i : Fin b.len) :
    (nerveFiberIso C b).hom ≫ nerveFiberEval C b i =
      nerveMap (CategoryTheory.Pi.eval (fun _ : Fin b.len ↦ C) i) := by
  simp [nerveFiberEval]

/-- The coordinate comparison from the strict fiber to the product of copies of `nerve C`. -/
noncomputable def nerveFiberPiIso (b : FinPointed.{max u v}) :
    (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm b) : SSet) ≅
      ∏ᶜ (fun _ : Fin b.len ↦ nerve C) :=
  (nerveFiberIso C b).symm ≪≫ asIso (nerve.piComparison C (Fin b.len))

/-- The coordinate projections of the product comparison are evaluation. -/
@[reassoc (attr := simp)]
lemma nerveFiberPiIso_hom_π (b : FinPointed.{max u v}) (i : Fin b.len) :
    (nerveFiberPiIso C b).hom ≫ Pi.π (fun _ : Fin b.len ↦ nerve C) i =
      nerveFiberEval C b i := by
  simp [nerveFiberPiIso, nerveFiberEval]

/-- Evaluating the inverse product comparison recovers the corresponding projection. -/
@[reassoc (attr := simp)]
lemma nerveFiberPiIso_inv_eval (b : FinPointed.{max u v}) (i : Fin b.len) :
    (nerveFiberPiIso C b).inv ≫ nerveFiberEval C b i =
      Pi.π (fun _ : Fin b.len ↦ nerve C) i := by
  rw [← nerveFiberPiIso_hom_π, Iso.inv_hom_id_assoc]

/-- The fiber over `⟨1⟩` is strictly isomorphic to the nerve of the original category. -/
noncomputable def nerveFiberOneIso :
    (fiber (nerveMap (toFinPointed C)) (nerveEquiv.symm (FinPointed.mk 1)) : SSet) ≅ nerve C :=
  nerveFiberPiIso C (FinPointed.mk 1) ≪≫
    productUniqueIso (fun _ : Fin 1 ↦ nerve C)

/-- The singleton-fiber comparison is evaluation at its unique coordinate. -/
@[simp]
lemma nerveFiberOneIso_hom :
    (nerveFiberOneIso C).hom = nerveFiberEval C (FinPointed.mk 1) 0 := by
  simp only [nerveFiberOneIso, Iso.trans_hom, productUniqueIso_hom]
  exact nerveFiberPiIso_hom_π C (FinPointed.mk 1) 0

/-- The empty-family fiber of the operator nerve is terminal. -/
noncomputable def isTerminalNerveFiberZero :
    IsTerminal (fiber (nerveMap (toFinPointed.{max u v} C))
      (nerveEquiv.symm (FinPointed.mk 0)) : SSet) :=
  IsTerminal.ofIso
    ((isLimitEquivIsTerminalOfIsEmpty (SSet.{max u v})
      (limit.cone (Discrete.functor (fun _ : Fin 0 ↦ nerve C)))).toFun (limit.isLimit _))
    (nerveFiberPiIso C (FinPointed.mk 0)).symm

/-- The operator nerve of a monoidal category with one object and one morphism is the
nerve of `FinPointed`, with its given projection as the forward map. -/
noncomputable def nerveIsoOfSubsingleton [Subsingleton C] [Quiver.IsThin C] :
    nerve (CategoryOfOperators.{max u v} C) ≅ nerve FinPointed.{max u v} :=
  let e := (toFinPointed.{max u v} C).asIsomorphism
  nerveFunctor.mapIso
    { hom := e.functor.toCatHom
      inv := e.inverse.toCatHom
      hom_inv_id := congrArg Functor.toCatHom e.unit_eq.symm
      inv_hom_id := congrArg Functor.toCatHom e.counit_eq }

/-- The terminal operator-nerve comparison is an isomorphism over the original base. -/
@[simp]
lemma nerveIsoOfSubsingleton_hom [Subsingleton C] [Quiver.IsThin C] :
    (nerveIsoOfSubsingleton C).hom = nerveMap (toFinPointed.{max u v} C) :=
  (rfl)

/-- The inverse terminal operator-nerve comparison is the nerve of the strict inverse. -/
@[simp]
lemma nerveIsoOfSubsingleton_inv [Subsingleton C] [Quiver.IsThin C] :
    (nerveIsoOfSubsingleton C).inv = nerveMap (toFinPointed.{max u v} C).strictInv :=
  (rfl)

end TauCeti.CategoryOfOperators
