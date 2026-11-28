/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Algebra.Category.CommAlgCat.BaseChange

/-!
# Semilinear natural transformations between base-changed algebra functors

Let `F : C ⥤ CommAlgCat A` and `G : C ⥤ CommAlgCat A'` be functors into categories of commutative
algebras, let `τ : A →+* A'` and `σ : S →+* S'` be ring homomorphisms compatible with the algebra
structures `A → S` and `A' → S'` (with `S` and `S'` in independent universes), and let
`s : F ⋙ forget₂ (CommAlgCat A) CommRingCat ⟶ G ⋙ forget₂ (CommAlgCat A') CommRingCat` be a natural
transformation whose components lie over `τ`. Then `σ ⊗ s` defines a natural transformation
`CommAlgCat.extendScalarsSemilinearNatTrans` between the universe-lifted base-changed ring functors,
acting on pure tensors by `ULift.up (a ⊗ₜ x) ↦ ULift.up (σ a ⊗ₜ s.app c x)`.

## Main definitions and results

* `CommAlgCat.extendScalarsSemilinearNatTrans`: the natural transformation `σ ⊗ s` on base-changed
  functors of commutative algebras, with independent universes for `S` and `S'`.
* `CommAlgCat.extendScalarsSemilinearNatTrans_app_tmul`: evaluation on pure tensors.

## Provenance

Generalized from `grh-lean` (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/PadicComparison/CrystallineFrobenius.lean` (`exists_tensor_twist`).
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

namespace CommAlgCat

universe u v u₁ u₂ w₁ w₁' w₂

/-- Universe-lifting functor `CommRingCat.{u} ⥤ CommRingCat.{max u v}` via `ULift`. -/
abbrev commRingULiftFunctor : CommRingCat.{u} ⥤ CommRingCat.{max u v} where
  obj R := CommRingCat.of (ULift.{v} R)
  map f := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp (f.hom.comp ULift.ringEquiv.toRingHom))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- Given compatible ring homomorphisms `τ : A →+* A'` and `σ : S →+* S'` (with `S` and `S'` in
independent universes) and a natural transformation `s` from
`F ⋙ forget₂ (CommAlgCat A) CommRingCat` to `G ⋙ forget₂ (CommAlgCat A') CommRingCat` whose
components lie over `τ`, the tensor product `σ ⊗ s` defines a natural transformation between the
universe-lifted base-changed ring functors. -/
noncomputable def extendScalarsSemilinearNatTrans
    {C : Type u} [Category.{v} C]
    {A : Type u₁} {A' : Type u₂} {S : Type w₁} {S' : Type w₁'}
    [CommRing A] [CommRing A'] [CommRing S] [CommRing S'] [Algebra A S] [Algebra A' S']
    {F : C ⥤ CommAlgCat.{w₂} A} {G : C ⥤ CommAlgCat.{w₂} A'}
    (τ : A →+* A') (σ : S →+* S')
    (hσ : σ.comp (algebraMap A S) = (algebraMap A' S').comp τ)
    (s : F ⋙ forget₂ (CommAlgCat.{w₂} A) CommRingCat.{w₂} ⟶
      G ⋙ forget₂ (CommAlgCat.{w₂} A') CommRingCat.{w₂})
    (hs : ∀ c : C, (s.app c).hom.comp (algebraMap A (F.obj c)) =
      (algebraMap A' (G.obj c)).comp τ) :
    (F ⋙ extendScalars A S) ⋙ forget₂ (CommAlgCat.{max w₁ w₂} S) CommRingCat.{max w₁ w₂} ⋙
        commRingULiftFunctor.{max w₁ w₂, max w₁ w₁' w₂} ⟶
      (G ⋙ extendScalars A' S') ⋙ forget₂ (CommAlgCat.{max w₁' w₂} S') CommRingCat.{max w₁' w₂} ⋙
        commRingULiftFunctor.{max w₁' w₂, max w₁ w₁' w₂} where
  app c := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Algebra.TensorProduct.mapRingHom (T := F.obj c) (T' := G.obj c) τ σ (s.app c).hom hσ
        (hs c)).comp ULift.ringEquiv.toRingHom))
  naturality c d f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    rintro ⟨z⟩
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      apply ULift.ext
      change Algebra.TensorProduct.mapRingHom (T := F.obj d) (T' := G.obj d) τ σ (s.app d).hom hσ
          (hs d) (a ⊗ₜ[A] (F.map f).hom x) =
        Algebra.TensorProduct.map (AlgHom.id S' S') (G.map f).hom
          (Algebra.TensorProduct.mapRingHom (T := F.obj c) (T' := G.obj c) τ σ (s.app c).hom hσ
            (hs c) (a ⊗ₜ[A] x))
      rw [Algebra.TensorProduct.mapRingHom_tmul, Algebra.TensorProduct.mapRingHom_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (σ a ⊗ₜ[A'] ·) (ConcreteCategory.congr_hom (s.naturality f) x)
    | add x y hx hy =>
      have hxy : ULift.up (x + y) = ULift.up x + ULift.up y := rfl
      rw [hxy, map_add, map_add, hx, hy]

/-- Evaluation of `CommAlgCat.extendScalarsSemilinearNatTrans` on a pure tensor
`ULift.up (a ⊗ₜ[A] x)`. -/
@[simp]
theorem extendScalarsSemilinearNatTrans_app_tmul
    {C : Type u} [Category.{v} C]
    {A : Type u₁} {A' : Type u₂} {S : Type w₁} {S' : Type w₁'}
    [CommRing A] [CommRing A'] [CommRing S] [CommRing S'] [Algebra A S] [Algebra A' S']
    {F : C ⥤ CommAlgCat.{w₂} A} {G : C ⥤ CommAlgCat.{w₂} A'}
    (τ : A →+* A') (σ : S →+* S')
    (hσ : σ.comp (algebraMap A S) = (algebraMap A' S').comp τ)
    (s : F ⋙ forget₂ (CommAlgCat.{w₂} A) CommRingCat.{w₂} ⟶
      G ⋙ forget₂ (CommAlgCat.{w₂} A') CommRingCat.{w₂})
    (hs : ∀ c : C, (s.app c).hom.comp (algebraMap A (F.obj c)) =
      (algebraMap A' (G.obj c)).comp τ)
    (c : C) (a : S) (x : F.obj c) :
    (extendScalarsSemilinearNatTrans τ σ hσ s hs).app c (ULift.up (a ⊗ₜ[A] x)) =
      ULift.up (σ a ⊗ₜ[A'] show G.obj c from s.app c x) :=
  congrArg ULift.up (Algebra.TensorProduct.mapRingHom_tmul (T := F.obj c) (T' := G.obj c) τ σ
    (s.app c).hom hσ (hs c) a x)

end CommAlgCat
