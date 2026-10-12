/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Adjunction
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Affine

/-!
# Pullback of tensor products with a quasicoherent factor

For a morphism of schemes `f : X ⟶ Y`, the canonical comparison `f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N`,
the tensor map of the oplax monoidal pullback, is an isomorphism whenever either factor is
quasicoherent (`Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent` and
`Scheme.Modules.isIso_pullback_δ_of_isQuasicoherent_right`). The target `Y` is arbitrary and the
other factor is an arbitrary sheaf of modules; no flatness or finiteness is assumed.

Pullback along an open immersion `j : U ⟶ Y` is strong monoidal for all sheaves of modules
(`Scheme.Modules.isIso_pullback_δ_of_isOpenImmersion`), and restriction along `j` is lax monoidal
with invertible tensor map (`Scheme.Modules.restrictFunctorLaxMonoidal`,
`Scheme.Modules.isIso_restrictFunctor_μ`).

These isomorphisms say that pulling back along `f` turns tensor products into tensor products as
long as one factor is quasicoherent; in particular they apply to line bundles. This is what makes
pullback of line-bundle classes multiplicative (`LineBundleClass.pullback_mul`), so that every
morphism of schemes induces a homomorphism of Picard groups `Pic(Y) →* Pic(X)`
(`LineBundleClass.pullbackHom`), as the Picard functor `T ↦ Pic(X_T)` requires.

## References

* The Stacks Project, *Sheaves of Modules*, Lemma 03EL (pullback of tensor products).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
* G. M. Kelly, *Doctrinal adjunction*, Lecture Notes in Mathematics 420 (1974).
-/

public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

section OpenImmersion

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- The morphism of sheaves of rings along `j.opensFunctor`, given on sections by the inverses of
the isomorphisms `Scheme.Hom.appIso`, along which `Scheme.Modules.restrictFunctor j` is the
pushforward of sheaves of modules. -/
-- Exposed because the exported instance `restrictFunctorLaxMonoidal` is checked by unfolding
-- `restrictFunctor j` to the pushforward along this morphism.
@[expose]
def restrictRingCatSheafHom :
    U.ringCatSheaf ⟶ (j.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
  letI α : U.presheaf ⟶ j.opensFunctor.op ⋙ Y.presheaf := { app W := (j.appIso W.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

/-- Restriction of modules along an open immersion `j` is lax monoidal, as the pushforward of
sheaves of modules along the functor of opens `j.opensFunctor`
(`TauCeti.SheafOfModules.pushforwardLaxMonoidal`). -/
instance restrictFunctorLaxMonoidal : (restrictFunctor j).LaxMonoidal :=
  TauCeti.SheafOfModules.pushforwardLaxMonoidal (restrictRingCatSheafHom j)

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

/-- **Pullback along an open immersion is strong monoidal**: the tensor comparison
`j^*(M ⊗ N) ⟶ j^*M ⊗ j^*N` is an isomorphism for all sheaves of modules `M` and `N`. -/
instance isIso_pullback_δ_of_isOpenImmersion (M N : Y.Modules) :
    IsIso (δ (pullback j) M N) := by
  -- Compare with restriction, carrying the oplax structure of a left adjoint of `pushforward j`.
  let := (restrictAdjunction j).leftAdjointOplaxMonoidal
  let σ := (Adjunction.leftAdjointUniq (restrictAdjunction j) (pullbackPushforwardAdjunction j)).inv
  have hσ : conjugateEquiv (restrictAdjunction j) (pullbackPushforwardAdjunction j) σ = 𝟙 _ := by
    simp [σ, Adjunction.leftAdjointUniq]
  have h := Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _ hσ M N
  have : IsIso (δ (restrictFunctor j) M N) := by
    rw [Adjunction.leftAdjointOplaxMonoidal_δ]
    exact (restrictAdjunction j).inv_μ_eq_homEquiv_symm (restrictAdjunction_counit_app_tensor j)
      M N ▸ IsIso.inv_isIso (f := μ (restrictFunctor j) M N)
  have : IsIso (δ (pullback j) M N ≫ (σ.app M ⊗ₘ σ.app N)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (σ.app M ⊗ₘ σ.app N)

end OpenImmersion

variable {X Y : Scheme.{u}}

/-- **Pullback preserves tensor products with a quasicoherent left factor**: for every morphism
of schemes `f : X ⟶ Y`, the tensor comparison `f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` is an isomorphism when
`M` is quasicoherent. The right factor need not be quasicoherent. -/
instance isIso_pullback_δ_of_isQuasicoherent (f : X ⟶ Y) (M N : Y.Modules)
    [M.IsQuasicoherent] : IsIso (δ (pullback f) M N) := by
  -- The claim is local on `Y` (`isIso_iff_of_isOpenCover`). Over an affine open `V ⊆ Y` the
  -- comparison for `f ∣_ V` is invertible (`isIso_pullback_δ_of_isAffine`), and so is the
  -- comparison for the open immersion `V.ι`. Writing `(f⁻¹ V).ι ≫ f = f ∣_ V ≫ V.ι` and using
  -- `pullback_comp_δ`, the pullback of the comparison for `f` to `f⁻¹ V` is invertible.
  refine (isIso_iff_of_isOpenCover
    (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.hom) _).mpr fun V ↦ ?_
  have : IsAffine V.1 := V.2
  -- Over the affine open `V`, the comparison for `f ∣_ V ≫ V.ι = (f⁻¹ V).ι ≫ f` is invertible.
  have hg : IsIso (δ (pullback (f ∣_ V.1 ≫ V.1.ι)) M N) := by
    rw [pullback_comp_δ]
    have := isIso_pullback_δ_of_isAffine (f ∣_ V.1) ((pullback V.1.ι).obj M)
      ((pullback V.1.ι).obj N)
    infer_instance
  rw [morphismRestrict_ι, pullback_comp_δ, isIso_comp_left_iff, isIso_comp_right_iff] at hg
  exact hg

/-- **Pullback preserves tensor products with a quasicoherent right factor**: for every morphism
of schemes `f : X ⟶ Y`, the tensor comparison `f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` is an isomorphism when
`N` is quasicoherent. The left factor need not be quasicoherent. -/
instance isIso_pullback_δ_of_isQuasicoherent_right (f : X ⟶ Y) (M N : Y.Modules)
    [N.IsQuasicoherent] : IsIso (δ (pullback f) M N) := by
  -- The comparison with the factors exchanged is invertible, and the braidings carry one to the
  -- other.
  have h := pullback_map_braiding_hom_comp_δ f M N
  have : IsIso (δ (pullback f) M N ≫ (β_ _ _).hom) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (β_ _ _).hom

end

end AlgebraicGeometry.Scheme.Modules
