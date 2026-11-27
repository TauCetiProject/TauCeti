/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Adjunction
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Tensor products under restriction along open immersions

Restriction along an open immersion `j : U ⟶ Y` is lax monoidal with invertible tensor map
(`Scheme.Modules.restrictFunctorLaxMonoidal`, `Scheme.Modules.isIso_restrictFunctor_μ`).
The restriction--pullback isomorphism identifies this tensor map with the inverse of the
canonical pullback comparison (`Scheme.Modules.restrictFunctorIsoPullback_inv_app_tensor`).

## References

* G. M. Kelly, *Doctrinal adjunction*, Lecture Notes in Mathematics 420 (1974).
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

section OpenImmersion

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- Restriction of modules along an open immersion `j` is lax monoidal, as the pushforward of
sheaves of modules along the functor of opens `j.opensFunctor`
(`SheafOfModules.pushforwardLaxMonoidal`). -/
instance restrictFunctorLaxMonoidal : (restrictFunctor j).LaxMonoidal :=
  SheafOfModules.pushforwardLaxMonoidal (restrictRingCatSheafHom j)

/-- The unit `M ⟶ j_* (M|_U)` of the restriction--pushforward adjunction along an open immersion
is compatible with the tensor maps of restriction and pushforward. -/
lemma restrictAdjunction_unit_app_tensor (M N : Y.Modules) :
    (restrictAdjunction j).unit.app (M ⊗ N) =
      ((restrictAdjunction j).unit.app M ⊗ₘ (restrictAdjunction j).unit.app N) ≫
        μ (pushforward j) _ _ ≫ (pushforward j).map (μ (restrictFunctor j) M N) :=
  -- The adjunction of opens is stated for `IsOpenMap.functor`, which is `j.opensFunctor`; `show`
  -- restates it in the form the sheaf-level lemma unifies with `restrictAdjunction j`.
  TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_tensor
    (show j.opensFunctor ⊣ TopologicalSpace.Opens.map j.base from
      j.isOpenEmbedding.isOpenMap.adjunction) (restrictRingCatSheafHom j) j.toRingCatSheafHom _ _
    M N

/-- The counit `(j_* A)|_U ⟶ A` of the restriction--pushforward adjunction along an open
immersion is compatible with the tensor maps of restriction and pushforward. -/
lemma restrictAdjunction_counit_app_tensor (A B : U.Modules) :
    μ (restrictFunctor j) ((pushforward j).obj A) ((pushforward j).obj B) ≫
      (restrictFunctor j).map (μ (pushforward j) A B) ≫
        (restrictAdjunction j).counit.app (A ⊗ B) =
      ((restrictAdjunction j).counit.app A ⊗ₘ (restrictAdjunction j).counit.app B) :=
  -- As in `restrictAdjunction_unit_app_tensor`, the adjunction of opens is restated with `show`.
  TauCeti.SheafOfModules.pushforwardPushforwardAdj_counit_app_tensor
    (show j.opensFunctor ⊣ TopologicalSpace.Opens.map j.base from
      j.isOpenEmbedding.isOpenMap.adjunction) (restrictRingCatSheafHom j) j.toRingCatSheafHom _ _
    A B

/-- Restriction of modules along an open immersion commutes with tensor products: its tensor
map `M|_U ⊗ N|_U ⟶ (M ⊗ N)|_U` is an isomorphism. -/
instance isIso_restrictFunctor_μ (M N : Y.Modules) : IsIso (μ (restrictFunctor j) M N) :=
  (restrictAdjunction j).isIso_μ_of_unit_of_counit (restrictAdjunction_unit_app_tensor j)
    (restrictAdjunction_counit_app_tensor j) M N

/-- The restriction--pullback isomorphism identifies the oplax tensor comparison of pullback
with the inverse tensor map of restriction. -/
lemma restrictFunctorIsoPullback_inv_app_tensor (M N : Y.Modules) :
    (restrictFunctorIsoPullback j).inv.app (M ⊗ N) ≫
        inv (μ (restrictFunctor j) M N) =
      δ (pullback j) M N ≫
        ((restrictFunctorIsoPullback j).inv.app M ⊗ₘ
          (restrictFunctorIsoPullback j).inv.app N) := by
  let := (restrictAdjunction j).leftAdjointOplaxMonoidal
  let σ := (restrictFunctorIsoPullback j).inv
  have hσ : conjugateEquiv (restrictAdjunction j) (pullbackPushforwardAdjunction j) σ = 𝟙 _ := by
    simp [σ, restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]
  have h := Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _ hσ M N
  have hd : δ (restrictFunctor j) M N = inv (μ (restrictFunctor j) M N) := by
    rw [Adjunction.leftAdjointOplaxMonoidal_δ]
    exact ((restrictAdjunction j).inv_μ_eq_homEquiv_symm
      (restrictAdjunction_counit_app_tensor j) M N).symm
  rw [hd] at h
  exact h

end OpenImmersion

end

end AlgebraicGeometry.Scheme.Modules
