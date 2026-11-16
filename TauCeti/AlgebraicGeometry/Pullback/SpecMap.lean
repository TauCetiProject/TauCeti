/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Pullback of schemes along `Spec.map`

Mathlib's `CategoryTheory.Over.pullbackId` and `CategoryTheory.Over.pullbackComp` compare the
pullback functors on `Over` categories along an identity morphism and along a composite. This
file reads those comparisons through `Spec`: `Spec.map` takes an identity ring map to an
identity morphism of schemes and a composite `f ≫ g` to `Spec.map g ≫ Spec.map f`, so pullback
along `Spec.map (𝟙 R)` is the identity functor on schemes over `Spec R`, and pullback along
`Spec.map (f ≫ g)` is the composite of pullback along `Spec.map f` with pullback along
`Spec.map g`.

These two comparisons mention neither affineness nor group objects: they are statements about
arbitrary schemes over an affine base, and they are the underlying comparisons of the base-change
functors on affine group schemes in
`TauCeti/AlgebraicGeometry/AffineGroupScheme/BaseChange/Basic.lean`.

The same pullback along `Spec.map` of a ring map `k → K` carries affine charts: if `Spec A` is an
open subscheme of `X` over `Spec k`, then `Spec (A ⊗[k] K)` is an open subscheme of the base
change `X ×_k Spec K`, over `Spec K`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapId`: pullback along `Spec.map (𝟙 R)` is the
  identity functor.
* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapComp`: pullback along `Spec.map (f ≫ g)` is a
  composite of pullbacks.
* `TauCeti.AlgebraicGeometry.exists_isOpenImmersion_tensorProduct_of_isPullback`: the base change
  of an affine chart is an affine chart of the base change.
* `TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv`: an algebra equivalence
  identifies an affine base change over its new base;
  `TauCeti.AlgebraicGeometry.exists_pullbackSpecIso_of_isPushout` packages the resulting
  isomorphism with an affine `Spec T`-scheme whose global sections form an `Algebra.IsPushout`.
* `AlgebraicGeometry.Scheme.Hom.toSpecΓ_SpecMap_ΓSpecIso_inv_comp_appTop`: any morphism
  `p : X ⟶ Spec R` factors through `X.toSpecΓ` followed by `Spec.map` of
  `(ΓSpecIso R).inv ≫ p.appTop`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- Any morphism `p : X ⟶ Spec R` factors through `X.toSpecΓ` followed by `Spec.map` of the
induced ring map `R ⟶ Γ(X, ⊤)`. -/
@[reassoc]
theorem Scheme.Hom.toSpecΓ_SpecMap_ΓSpecIso_inv_comp_appTop {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ p.appTop) = p := by
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

end AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {R S T : CommRingCat.{u}}

/-- Pullback along `Spec.map (𝟙 R)` is the identity functor on schemes over `Spec R`. -/
noncomputable def Over.pullbackSpecMapId :
    Over.pullback (Spec.map (𝟙 R)) ≅ 𝟭 (Over (Spec R)) :=
  eqToIso (by simp only [Spec.map_id]) ≪≫ Over.pullbackId

/-- Pullback along `Spec.map (f ≫ g)` is pullback along `Spec.map f` followed by pullback along
`Spec.map g`. -/
noncomputable def Over.pullbackSpecMapComp (f : R ⟶ S) (g : S ⟶ T) :
    Over.pullback (Spec.map (f ≫ g)) ≅
      Over.pullback (Spec.map f) ⋙ Over.pullback (Spec.map g) :=
  eqToIso (by simp only [Spec.map_comp]) ≪≫ Over.pullbackComp (Spec.map g) (Spec.map f)

/-- **The base change of an affine chart is an affine chart of the base change.** Let
`φ : Spec A ⟶ X` be an open immersion of schemes over `Spec k`, and let `Y = X ×_k Spec K` be a
base change of `X`. Then `Spec (A ⊗[k] K)` is an open subscheme of `Y`, over `Spec K`. -/
theorem exists_isOpenImmersion_tensorProduct_of_isPullback {k A K : Type u} [CommRing k]
    [CommRing A] [CommRing K] [Algebra k A] [Algebra k K] {X Y : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {φ : Spec (.of A) ⟶ X} [IsOpenImmersion φ]
    (hφ : φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A))) {g : Y ⟶ X}
    {q : Y ⟶ Spec (.of K)} (H : IsPullback g q f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ∃ ι : Spec (.of (A ⊗[k] K)) ⟶ Y, IsOpenImmersion ι ∧
      ι ≫ q = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : K →ₐ[k] A ⊗[k] K).toRingHom) := by
  refine ⟨(pullbackSpecIso k A K).inv ≫ (pullback.congrHom hφ.symm rfl).hom ≫
    (pullbackRightPullbackFstIso _ _ _).inv ≫ pullback.snd _ _ ≫ H.isoPullback.inv,
    inferInstance, ?_⟩
  simp

/-- An algebraic identification of a base-changed algebra induces an isomorphism over the
new affine base. No finiteness or étaleness assumptions are needed for this transport. -/
noncomputable def pullbackSpecIsoOfAlgEquiv (R B T C : Type u)
    [CommRing R] [CommRing B] [CommRing T] [CommRing C]
    [Algebra R B] [Algebra R T] [Algebra T C]
    (e : T ⊗[R] B ≃ₐ[T] C) :
    Over.mk (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ≅
      Over.mk (Spec.algebraMap T C) := by
  let e₁ : Over.mk (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ≅
      Over.mk (Spec.algebraMap T (T ⊗[R] B)) :=
    Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R T B) (by
      simp [Spec.algebraMap, pullbackSpecIso_hom_fst'])
  refine e₁ ≪≫ Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.symm.op) ?_
  simp only [Over.mk_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
    Spec.algebraMap, ← Spec.map_comp]
  congr 1
  ext r
  exact e.symm.commutes r

/-- The underlying map of the affine base-change isomorphism is the standard pullback
comparison followed by the spectrum map of the inverse algebra equivalence. -/
@[simp]
theorem pullbackSpecIsoOfAlgEquiv_hom_left (R B T C : Type u)
    [CommRing R] [CommRing B] [CommRing T] [CommRing C]
    [Algebra R B] [Algebra R T] [Algebra T C]
    (e : T ⊗[R] B ≃ₐ[T] C) :
    (pullbackSpecIsoOfAlgEquiv R B T C e).hom.left =
      (pullbackSymmetry (Spec.algebraMap R B) (Spec.algebraMap R T)).hom ≫
        (pullbackSpecIso R T B).hom ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) :=
  (rfl)

/-- The inverse underlying map of the affine base-change isomorphism is the spectrum map of the
algebra equivalence followed by the inverse pullback comparison. -/
@[simp]
theorem pullbackSpecIsoOfAlgEquiv_inv_left (R B T C : Type u)
    [CommRing R] [CommRing B] [CommRing T] [CommRing C]
    [Algebra R B] [Algebra R T] [Algebra T C]
    (e : T ⊗[R] B ≃ₐ[T] C) :
    (pullbackSpecIsoOfAlgEquiv R B T C e).inv.left =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        (pullbackSpecIso R T B).inv ≫
          (pullbackSymmetry (Spec.algebraMap R B) (Spec.algebraMap R T)).inv :=
  (rfl)

/-- If the global sections of an affine `Spec T`-scheme `Y'` form a pushout `T ⊗[R] B`, then
`Spec B ×_{Spec R} Spec T` is isomorphic to `Y'` over `Spec T`, with inverse first projection
induced by `algebraMap B Γ(Y'.left, ⊤)`. -/
theorem exists_pullbackSpecIso_of_isPushout (R B T : Type u)
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T]
    (Y' : Over (Spec (.of T))) [IsAffine Y'.left]
    [Algebra R Γ(Y'.left, ⊤)] [Algebra B Γ(Y'.left, ⊤)] [Algebra T Γ(Y'.left, ⊤)]
    [IsScalarTower R B Γ(Y'.left, ⊤)] [IsScalarTower R T Γ(Y'.left, ⊤)]
    [Algebra.IsPushout R T B Γ(Y'.left, ⊤)]
    (hY' : algebraMap T Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of T)).inv ≫ Y'.hom.appTop).hom) :
    ∃ eSpec : Over.mk (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ≅ Y',
      eSpec.inv.left ≫ pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R T) =
        Y'.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(Y'.left, ⊤))) := by
  have hY'_isoSpec : Y'.left.isoSpec.hom ≫ Spec.algebraMap T Γ(Y'.left, ⊤) = Y'.hom := by
    rw [Scheme.isoSpec_hom, Spec.algebraMap, hY', CommRingCat.ofHom_hom]
    exact Y'.hom.toSpecΓ_SpecMap_ΓSpecIso_inv_comp_appTop
  let eSpec : Over.mk (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ≅ Y' :=
    pullbackSpecIsoOfAlgEquiv R B T Γ(Y'.left, ⊤)
      (Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤)) ≪≫
      Over.isoMk Y'.left.isoSpec.symm (by
        rw [Iso.symm_hom, ← cancel_epi Y'.left.isoSpec.hom, Iso.hom_inv_id_assoc]
        exact hY'_isoSpec.symm)
  refine ⟨eSpec, ?_⟩
  have hval : (Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤)).toRingHom.comp
      ↑(Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B) =
      algebraMap B Γ(Y'.left, ⊤) := by
    ext b
    exact (Algebra.IsPushout.equiv_tmul R T B Γ(Y'.left, ⊤) 1 b).trans (by simp)
  have hproj :
      (pullbackSpecIsoOfAlgEquiv R B T Γ(Y'.left, ⊤)
          (Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤))).inv.left ≫
        pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R T) =
        Spec.map (CommRingCat.ofHom (algebraMap B Γ(Y'.left, ⊤))) := by
    rw [pullbackSpecIsoOfAlgEquiv_inv_left, Category.assoc, Category.assoc,
      pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, hval]
  dsimp only [eSpec, Iso.trans_inv, Over.comp_left]
  rw [Category.assoc]
  exact congrArg (Y'.left.toSpecΓ ≫ ·) hproj

end AlgebraicGeometry

end TauCeti
