/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward

/-!
# Pushforward along a left adjoint of sites is strong monoidal

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, both continuous, and let `φ` and `ψ` be
compatible morphisms of sheaves of rings along `F` and `G`. Mathlib's
`SheafOfModules.pushforwardPushforwardAdj` makes the pushforward of sheaves of modules along `φ`
left adjoint to the pushforward along `ψ`. For the inclusion of an open subset `U` of a
topological space, `F` is the inclusion of the opens of `U` into the opens of the space and the
pushforward along `φ` is restriction to `U`.

Both pushforwards carry their canonical lax monoidal structures
(`TauCeti.SheafOfModules.pushforwardLaxMonoidal`), whose tensor maps send `m ⊗ n` to `m ⊗ n` on
sections. This file shows that the unit and the counit of the adjunction are compatible with
these tensor maps (`SheafOfModules.pushforwardPushforwardAdj_unit_app_tensor` and
`SheafOfModules.pushforwardPushforwardAdj_counit_app_tensor`); on sections both are restriction
maps. By doctrinal adjunction (`CategoryTheory.Adjunction.isIso_μ_of_unit_of_counit`) the tensor
map of the left adjoint is then invertible: pushforward along `φ` commutes with tensor products
(`SheafOfModules.isIso_pushforward_μ_of_adjunction`). The inverse is the mate of the tensor map
of the right adjoint, which is the tensor comparison of the left adjoint as an oplax monoidal
functor. This identification of the canonical tensor map, rather than the construction of some
isomorphism `φ_* (M ⊗ N) ≅ φ_* M ⊗ φ_* N` as in `SheafOfModules.pushforwardTensorProductIso`,
is what lets it be compared, through mates, with the tensor comparison of a pullback.

## Main declarations

* `TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_tensor` and
  `TauCeti.SheafOfModules.pushforwardPushforwardAdj_counit_app_tensor`: the unit and counit of the
  adjunction are compatible with the tensor maps;
* `TauCeti.SheafOfModules.isIso_pushforward_μ_of_adjunction`: the tensor map of the pushforward
  along the left adjoint is invertible, with inverse computed by
  `TauCeti.SheafOfModules.inv_pushforward_μ_of_adjunction`.

## References

* G. M. Kelly, *Doctrinal adjunction*, Lecture Notes in Mathematics 420 (1974).
* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

section Adjunction

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J] (adj : F ⊣ G)
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj (ringCatSheaf S))
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) (ringCatSheaf R).obj =
    ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) (ringCatSheaf S).obj = 𝟙 (ringCatSheaf S).obj)

/-- The unit `M ⟶ ψ_* φ_* M` of the adjunction between pushforwards is compatible with the tensor
maps of the two pushforwards. On sections both sides send `m ⊗ n` to its restriction. -/
theorem pushforwardPushforwardAdj_unit_app_tensor
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app (M ⊗ N) =
      ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M ⊗ₘ
          (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app N) ≫
        μ (_root_.SheafOfModules.pushforward ψ) _ _ ≫
          (_root_.SheafOfModules.pushforward ψ).map
            (μ (_root_.SheafOfModules.pushforward φ) M N) := by
  apply tensor_hom_ext
  ext V : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  set η := (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit
  have hnat := congrArg (fun f ↦ f.app V (m ⊗ₜ[R.obj.obj V] n))
    (μ_natural (_root_.SheafOfModules.forget (ringCatSheaf R)) (η.app M) (η.app N))
  have hψ := pushforward_μ_app_tmul ψ ((_root_.SheafOfModules.pushforward φ).obj M)
    ((_root_.SheafOfModules.pushforward φ).obj N) V ((η.app M).val.app V m)
      ((η.app N).val.app V n)
  have hφ := pushforward_μ_app_tmul φ M N (G.op.obj V)
    ((η.app M).val.app V m) ((η.app N).val.app V n)
  -- On sections over `V`, the unit is restriction along the counit `F (G V) ⟶ V`; move it past
  -- the tensor map of `forget`, then compute the right side through the two tensor maps.
  refine (PresheafOfModules.naturality_apply
    (μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N) (adj.counit.app V.unop).op
      (m ⊗ₜ[R.obj.obj V] n)).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ ((_root_.SheafOfModules.forget (ringCatSheaf R)).map
    (μ (_root_.SheafOfModules.pushforward ψ) ((_root_.SheafOfModules.pushforward φ).obj M)
      ((_root_.SheafOfModules.pushforward φ).obj N) ≫
        (_root_.SheafOfModules.pushforward ψ).map
          (μ (_root_.SheafOfModules.pushforward φ) M N))).app V z) hnat)
  exact hφ.symm.trans (congrArg (((_root_.SheafOfModules.forget (ringCatSheaf S)).map
    (μ (_root_.SheafOfModules.pushforward φ) M N)).app (G.op.obj V)) hψ.symm)

/-- The counit `φ_* ψ_* A ⟶ A` of the adjunction between pushforwards is compatible with the
tensor maps of the two pushforwards. On sections both sides send `a ⊗ b` to its restriction. -/
theorem pushforwardPushforwardAdj_counit_app_tensor
    (A B : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    μ (_root_.SheafOfModules.pushforward φ) ((_root_.SheafOfModules.pushforward ψ).obj A)
        ((_root_.SheafOfModules.pushforward ψ).obj B) ≫
      (_root_.SheafOfModules.pushforward φ).map (μ (_root_.SheafOfModules.pushforward ψ) A B) ≫
        (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app (A ⊗ B) =
      ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app A ⊗ₘ
        (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app B) := by
  apply tensor_hom_ext
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  set ε := (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit
  have hnat := congrArg (fun f ↦ f.app U (a ⊗ₜ[S.obj.obj U] b))
    (μ_natural (_root_.SheafOfModules.forget (ringCatSheaf S)) (ε.app A) (ε.app B))
  have hφ := pushforward_μ_app_tmul φ ((_root_.SheafOfModules.pushforward ψ).obj A)
    ((_root_.SheafOfModules.pushforward ψ).obj B) U a b
  have hψ := pushforward_μ_app_tmul ψ A B (F.op.obj U) a b
  -- Compute the left side through the two tensor maps; on sections over `U`, the counit is
  -- restriction along the unit `U ⟶ G (F U)`, which then moves past the tensor map of `forget`.
  refine Eq.trans (congrArg (((_root_.SheafOfModules.forget (ringCatSheaf S)).map
    ((_root_.SheafOfModules.pushforward φ).map (μ (_root_.SheafOfModules.pushforward ψ) A B) ≫
      ε.app (A ⊗ B))).app U) hφ) ?_
  refine Eq.trans (congrArg (((_root_.SheafOfModules.forget (ringCatSheaf S)).map
      (ε.app (A ⊗ B))).app U) hψ) ?_
  refine Eq.trans ?_ hnat
  exact (PresheafOfModules.naturality_apply
    (μ (_root_.SheafOfModules.forget (ringCatSheaf S)) A B) (adj.unit.app U.unop).op
      (a ⊗ₜ[S.obj.obj (G.op.obj (F.op.obj U))] b)).symm

include adj ψ H₁ H₂ in
/-- **Pushforward along a left adjoint of sites commutes with tensor products**: the tensor map
`φ_* M ⊗ φ_* N ⟶ φ_* (M ⊗ N)` of the pushforward along `φ` is an isomorphism. -/
theorem isIso_pushforward_μ_of_adjunction (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    IsIso (μ (_root_.SheafOfModules.pushforward φ) M N) :=
  (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).isIso_μ_of_unit_of_counit
    (pushforwardPushforwardAdj_unit_app_tensor adj φ ψ H₁ H₂)
    (pushforwardPushforwardAdj_counit_app_tensor adj φ ψ H₁ H₂) M N

/-- The inverse of the tensor map of the pushforward along a left adjoint is the mate, under the
adjunction between pushforwards, of the tensor map of the right adjoint. -/
theorem inv_pushforward_μ_of_adjunction (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    letI := isIso_pushforward_μ_of_adjunction adj φ ψ H₁ H₂ M N
    inv (μ (_root_.SheafOfModules.pushforward φ) M N) =
      ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).homEquiv _ _).symm
        (((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M ⊗ₘ
          (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app N) ≫
            μ (_root_.SheafOfModules.pushforward ψ) _ _) :=
  letI := isIso_pushforward_μ_of_adjunction adj φ ψ H₁ H₂ M N
  (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).inv_μ_eq_homEquiv_symm
    (pushforwardPushforwardAdj_counit_app_tensor adj φ ψ H₁ H₂) M N

end Adjunction

end SheafOfModules

end

end TauCeti
