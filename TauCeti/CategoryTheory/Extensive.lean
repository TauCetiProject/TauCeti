/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Over
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Base change of finite coproducts in finitary pre-extensive categories

In a finitary pre-extensive category finite coproducts are universal: they are stable under
pullback. Phrased in over categories, base change `Over.pullback f : Over S ⥤ Over T` along any
morphism `f : T ⟶ S` preserves finite coproducts. This applies for instance to schemes, where
it says that the fibre product of a finite disjoint union with `T` over `S` is the disjoint
union of the fibre products.

## Main results

* `CategoryTheory.Over.preservesColimitsOfShape_discrete_pullback`: in a finitary pre-extensive
  category, `Over.pullback f` preserves finite coproducts.
* `CategoryTheory.FinitaryPreExtensive.isPullback_sigmaMap_sigmaDesc_id`: in a finitary
  pre-extensive category, the base change of the fold map `∐_j Y ⟶ Y` along `f : S ⟶ Y` is the
  fold map `∐_j S ⟶ S`.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {S T : C} (f : T ⟶ S) [HasPullbacksAlong f]

/-- In a finitary pre-extensive category, base change of objects over `S` along any `f : T ⟶ S`
preserves finite coproducts. -/
instance preservesColimitsOfShape_discrete_pullback [FinitaryPreExtensive C] (J : Type*)
    [Finite J] : PreservesColimitsOfShape (Discrete J) (Over.pullback f) where
  preservesColimit {K} := ⟨fun {c} hc ↦ ⟨by
    -- The forgetful functors create colimits, and the image under `Over.forget S` of the
    -- coproduct `c` is universal, so it suffices that the base change of each coproduct
    -- inclusion is a pullback of it.
    apply isColimitOfReflects (Over.forget T)
    refine (FinitaryPreExtensive.isUniversal_finiteCoproducts
      (isColimitOfPreserves (Over.forget S) hc) _
      (Discrete.natTrans fun j ↦ pullback.fst (K.obj j).hom f) (pullback.fst c.pt.hom f) ?_
      (NatTrans.Equifibered.of_discrete _) fun j ↦ ?_).some
    · ext j
      simp
    · exact isPullback_pullback_map_left f (c.ι.app j)⟩⟩

/-- In a finitary pre-extensive category, base change of objects over `S` preserves finite
coproducts. -/
instance [FinitaryPreExtensive C] : PreservesFiniteCoproducts (Over.pullback f) :=
  ⟨fun _ ↦ inferInstance⟩

end CategoryTheory.Over

namespace CategoryTheory.FinitaryPreExtensive

variable {C : Type u} [Category.{v} C] [FinitaryPreExtensive C]

/-- In a finitary pre-extensive category, the base change of the fold map `∐_j Y ⟶ Y` along any
morphism `f : S ⟶ Y` is the fold map `∐_j S ⟶ S`, with first projection `∐_j f`. -/
lemma isPullback_sigmaMap_sigmaDesc_id {J : Type*} [Finite J] {S Y : C} (f : S ⟶ Y)
    [HasPullback (Sigma.desc fun _ : J ↦ 𝟙 Y) f] :
    IsPullback (Limits.Sigma.map fun _ : J ↦ f) (Sigma.desc fun _ : J ↦ 𝟙 S)
      (Sigma.desc fun _ : J ↦ 𝟙 Y) f := by
  have hS := coproductIsCoproduct fun _ : J ↦ S
  have h₁ : Cofan.IsColimit.desc hS (fun j ↦ f ≫ (Cofan.mk _ (Sigma.ι fun _ : J ↦ Y)).inj j) =
      Limits.Sigma.map fun _ : J ↦ f :=
    Cofan.IsColimit.hom_ext hS _ _ fun j ↦ by rw [Cofan.IsColimit.fac]; simp
  have h₂ : Cofan.IsColimit.desc hS (fun _ ↦ 𝟙 S) = Sigma.desc fun _ : J ↦ 𝟙 S :=
    Cofan.IsColimit.hom_ext hS _ _ fun j ↦ by rw [Cofan.IsColimit.fac]; simp
  rw [← h₁, ← h₂]
  exact IsUniversalColimit.isPullback_of_isColimit_right
    (isUniversal_finiteCoproducts (coproductIsCoproduct fun _ : J ↦ Y)) (fun _ ↦ 𝟙 _)
    (Sigma.desc fun _ ↦ 𝟙 Y) f (fun _ ↦ f) (fun _ ↦ 𝟙 _) (fun _ ↦ IsPullback.id_vert f) hS

end CategoryTheory.FinitaryPreExtensive
