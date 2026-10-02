/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Full
public import TauCeti.Algebra.Module.AuslanderReiten.Faithful
public import TauCeti.Algebra.Module.AuslanderReiten.EssSurj

/-!
# The Auslander–Bridger stable equivalence

Transposition gives an additive equivalence between finitely presented stable left modules
and the opposite category of finitely presented stable right modules over an arbitrary ring.
Its inverse takes the cokernel of the `A`-valued dual of a right projective presentation.
The inverse's maps are uniquely characterized by transposing them back, using the canonical
double-transpose recovery. Both composites are naturally isomorphic to the identity.

`stableTransposeEquivalence` accepts independent choices of left and right presentations.
Its forward functor is `stableTransposeFunctor`; its inverse has the explicit right-transpose
objects, rather than objects chosen by abstract essential surjectivity. The morphisms remain
those of the existing stable quotient, modulo maps through arbitrary projectives.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Section 2.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

variable {A : Type u} [Ring A]

variable (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
  FiniteProjectivePresentation M.obj.as)

/-- Transposition is an equivalence for every family of finite projective presentations. -/
instance : (stableTransposeFunctor P).IsEquivalence where

/-- The transpose using chosen finite projective presentations is an equivalence. -/
instance : (stableTranspose.{u, v} A).IsEquivalence where

namespace FiniteProjectivePresentation

variable {N : FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ}

/-- The cokernel of the dual right presentation, as a finitely presented stable left module. -/
noncomputable abbrev stableRightTransposeObj (Q : FiniteProjectivePresentation N.obj.as) :
    FinitelyPresentedStableModule.{u, max u v} A :=
  ⟨(ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))).obj
      Q.rightTranspose, inferInstanceAs (Module.FinitePresentation A Q.rightTranspose)⟩

/-- Transposition of the dual right presentation recovers the original stable right module.
The comparison also accounts for the left presentation chosen by the forward functor. -/
noncomputable def stableTransposeRightIso (Q : FiniteProjectivePresentation N.obj.as) :
    (stableTransposeFunctor P).obj Q.stableRightTransposeObj ≅ Opposite.op N := by
  let T := ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))
  let i : Q.rightTransposePresentation.stableTransposeObj ≅ N :=
    ObjectProperty.isoMk _ (T.mapIso
      (rightDoubleTransposePresentationEquiv A Q.p Q.π Q.exact Q.surjective).toModuleIso)
  exact eqToIso (stableTransposeFunctor_obj P Q.stableRightTransposeObj) ≪≫
    ((P Q.stableRightTransposeObj).stableTransposeIso Q.rightTransposePresentation ≪≫ i).symm.op

/-- The stable recovery compares the chosen left presentation with the dual right presentation,
then applies the existing double-transpose recovery. -/
theorem stableTransposeRightIso_def (Q : FiniteProjectivePresentation N.obj.as) :
    Q.stableTransposeRightIso P =
      eqToIso (stableTransposeFunctor_obj P Q.stableRightTransposeObj) ≪≫
        ((P Q.stableRightTransposeObj).stableTransposeIso Q.rightTransposePresentation ≪≫
          ObjectProperty.isoMk _
            ((ExactStructure.projectiveStableFunctor
              (ExactStructure.abelian (ModuleCat Aᵐᵒᵖ))).mapIso
                (rightDoubleTransposePresentationEquiv A Q.p Q.π Q.exact Q.surjective).toModuleIso)
          ).symm.op := (rfl)

end FiniteProjectivePresentation

variable (Q : ∀ N : FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ,
  FiniteProjectivePresentation N.obj.as)

/-- The inverse transpose, with the cokernels of dual right presentations as its objects.
Fullness and faithfulness uniquely determine its maps from double-transpose recovery. -/
noncomputable def stableTransposeInverse :
    (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ ⥤
      FinitelyPresentedStableModule.{u, max u v} A where
  obj N := (Q N.unop).stableRightTransposeObj
  map {N L} f := (stableTransposeFunctor P).preimage
    (((Q N.unop).stableTransposeRightIso P).hom ≫ f ≫
      ((Q L.unop).stableTransposeRightIso P).inv)
  map_id N := by
    apply (stableTransposeFunctor P).map_injective
    simp
  map_comp f g := by
    apply (stableTransposeFunctor P).map_injective
    simp only [Functor.map_comp, Functor.map_preimage, Category.assoc,
      Iso.inv_hom_id_assoc]

/-- Inverse transposition takes the cokernel of the chosen dual right presentation. -/
@[simp]
theorem stableTransposeInverse_obj
    (N : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ) :
    (stableTransposeInverse P Q).obj N = (Q N.unop).stableRightTransposeObj := (rfl)

/-- Transposing an inverse-transpose object recovers the original stable right module. -/
noncomputable def stableTransposeInverseRecovery
    (N : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ) :
    (stableTransposeFunctor P).obj ((stableTransposeInverse P Q).obj N) ≅ N := by
  rw [stableTransposeInverse_obj]
  exact (Q N.unop).stableTransposeRightIso P

/-- Inverse recovery is the dual-presentation comparison after the inverse's object equation. -/
theorem stableTransposeInverseRecovery_def
    (N : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ) :
    stableTransposeInverseRecovery P Q N =
      eqToIso (congrArg (stableTransposeFunctor P).obj (stableTransposeInverse_obj P Q N)) ≪≫
        (Q N.unop).stableTransposeRightIso P := by
  exact (Iso.refl_trans _).symm

/-- Transposing an inverse-transpose map gives the original map conjugated by recovery. -/
-- Use recovery before the general simp rule expanding a stable transpose map.
@[simp high]
theorem stableTransposeFunctor_map_inverse {N L}
    (f : N ⟶ L) :
    (stableTransposeFunctor P).map ((stableTransposeInverse P Q).map f) =
      (stableTransposeInverseRecovery P Q N).hom ≫ f ≫
        (stableTransposeInverseRecovery P Q L).inv := by
  unfold stableTransposeInverseRecovery stableTransposeInverse
  exact (stableTransposeFunctor P).map_preimage _

/-- Inverse transposition preserves addition of stable morphisms. -/
instance : (stableTransposeInverse P Q).Additive where
  map_add := by
    intro N L f g
    apply (stableTransposeFunctor P).map_injective
    simp only [Functor.map_add, stableTransposeFunctor_map_inverse,
      Preadditive.comp_add, Preadditive.add_comp]

/-- Double-transpose recovery is a natural isomorphism on stable right modules. -/
noncomputable def stableTransposeCounitIso :
    stableTransposeInverse P Q ⋙ stableTransposeFunctor P ≅ 𝟭 _ :=
  NatIso.ofComponents (stableTransposeInverseRecovery P Q) fun f ↦ by
    simp only [Functor.comp_map, Functor.id_map, stableTransposeFunctor_map_inverse,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The counit is the comparison induced by the dual right presentation and its recovery. -/
@[simp]
theorem stableTransposeCounitIso_app
    (N : (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ) :
    (stableTransposeCounitIso P Q).app N = stableTransposeInverseRecovery P Q N := (rfl)

/-- Double transposition is naturally the identity on stable left modules. -/
noncomputable def stableTransposeUnitIso :
    𝟭 _ ≅ stableTransposeFunctor P ⋙ stableTransposeInverse P Q :=
  NatIso.ofComponents
    (fun M ↦ (stableTransposeFunctor P).preimageIso
      (stableTransposeInverseRecovery P Q ((stableTransposeFunctor P).obj M)).symm)
    fun f ↦ by
      apply (stableTransposeFunctor P).map_injective
      simp only [Functor.map_comp, Functor.comp_map, Functor.id_map,
        Functor.preimageIso_hom, Functor.map_preimage, Iso.symm_hom,
        stableTransposeFunctor_map_inverse, Iso.inv_hom_id_assoc]

/-- The unit lifts inverse recovery through the fully faithful transpose functor. -/
@[simp]
theorem stableTransposeUnitIso_app (M : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTransposeUnitIso P Q).app M =
      (stableTransposeFunctor P).preimageIso
        (stableTransposeInverseRecovery P Q ((stableTransposeFunctor P).obj M)).symm := (rfl)

/-- The Auslander–Bridger equivalence, with left and right transpose functors and their
canonical double-transpose comparisons. It holds over any ring. -/
noncomputable def stableTransposeEquivalence :
    FinitelyPresentedStableModule.{u, max u v} A ≌
      (FinitelyPresentedStableModule.{u, max u v} Aᵐᵒᵖ)ᵒᵖ where
  functor := stableTransposeFunctor P
  inverse := stableTransposeInverse P Q
  unitIso := stableTransposeUnitIso P Q
  counitIso := stableTransposeCounitIso P Q
  functor_unitIso_comp M := by
    rw [← Iso.app_hom, stableTransposeUnitIso_app, ← Iso.app_hom,
      stableTransposeCounitIso_app, Functor.preimageIso_hom, Functor.map_preimage]
    exact Iso.inv_hom_id _

/-- The forward functor of the stable equivalence is transposition. -/
@[simp]
theorem stableTransposeEquivalence_functor :
    (stableTransposeEquivalence P Q).functor = stableTransposeFunctor P := (rfl)

/-- The inverse functor has the explicit dual right-presentation cokernels as objects. -/
@[simp]
theorem stableTransposeEquivalence_inverse :
    (stableTransposeEquivalence P Q).inverse = stableTransposeInverse P Q := (rfl)

/-- The unit of the stable equivalence is the lifted inverse recovery. -/
@[simp]
theorem stableTransposeEquivalence_unitIso :
    (stableTransposeEquivalence P Q).unitIso =
      stableTransposeUnitIso P Q ≪≫ eqToIso (by
        rw [stableTransposeEquivalence_functor, stableTransposeEquivalence_inverse]) := by
  exact (Iso.trans_refl _).symm

/-- The counit of the stable equivalence is the natural double-transpose recovery. -/
@[simp]
theorem stableTransposeEquivalence_counitIso :
    (stableTransposeEquivalence P Q).counitIso =
      eqToIso (by rw [stableTransposeEquivalence_functor, stableTransposeEquivalence_inverse]) ≪≫
        stableTransposeCounitIso P Q := by
  exact (Iso.refl_trans _).symm

end TauCeti
