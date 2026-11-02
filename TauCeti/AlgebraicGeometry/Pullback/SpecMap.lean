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
* `TauCeti.AlgebraicGeometry.Over.pullbackSndSpecIsoOfAlgEquiv`: an isomorphism
  `T ⊗[R] A ≃ₐ[T] B` identifies the base change of `Spec A` along `Spec T ⟶ Spec R` with `Spec B`
  over `Spec T`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

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

section AlgEquiv

variable {R A T B : Type u} [CommRing R] [CommRing A] [CommRing T] [CommRing B] [Algebra R A]
  [Algebra R T] [Algebra T B]

/-- An isomorphism `a : T ⊗[R] A ≃ₐ[T] B` identifies the base change of `Spec A ⟶ Spec R` along
`Spec T ⟶ Spec R` with `Spec B ⟶ Spec T`, as schemes over `Spec T`. The underlying isomorphism
of schemes is Mathlib's `pullbackSpecIso` followed by `Spec.map` of `a.symm`. -/
noncomputable def Over.pullbackSndSpecIsoOfAlgEquiv (a : T ⊗[R] A ≃ₐ[T] B) :
    Over.mk (pullback.snd (Spec.algebraMap R A) (Spec.algebraMap R T)) ≅
      Over.mk (Spec.algebraMap T B) :=
  Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R T A ≪≫
    Scheme.Spec.mapIso a.symm.toRingEquiv.toCommRingCatIso.op) <| by
    have ha : CommRingCat.ofHom (algebraMap T B) ≫ a.symm.toRingEquiv.toCommRingCatIso.hom =
        CommRingCat.ofHom (algebraMap T (T ⊗[R] A)) := by
      ext t
      exact a.symm.commutes t
    simp only [Over.mk_hom, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map,
      Quiver.Hom.unop_op, Category.assoc, ← Spec.map_comp, ha]
    simp [pullbackSpecIso_hom_fst']

/-- The underlying morphism of `Over.pullbackSndSpecIsoOfAlgEquiv a` is `pullbackSymmetry`,
then `pullbackSpecIso`, then `Spec.map` of `a.symm`. -/
theorem Over.pullbackSndSpecIsoOfAlgEquiv_hom_left (a : T ⊗[R] A ≃ₐ[T] B) :
    (Over.pullbackSndSpecIsoOfAlgEquiv a).hom.left =
      (pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R T A).hom ≫
        Spec.map (CommRingCat.ofHom (a.symm : B →+* T ⊗[R] A)) := by
  rfl

/-- The inverse of `Over.pullbackSndSpecIsoOfAlgEquiv a`, followed by the projection to `Spec A`,
is `Spec.map` of `A → T ⊗[R] A → B`. -/
@[reassoc (attr := simp)]
theorem Over.pullbackSndSpecIsoOfAlgEquiv_inv_left_fst (a : T ⊗[R] A ≃ₐ[T] B) :
    (Over.pullbackSndSpecIsoOfAlgEquiv a).inv.left ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom ((a : T ⊗[R] A →+* B).comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom)) := by
  simp only [Over.pullbackSndSpecIsoOfAlgEquiv, Over.isoMk_inv_left, Iso.trans_inv,
    Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc,
    pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd, ← Spec.map_comp,
    RingEquiv.toCommRingCatIso_inv]
  rfl

end AlgEquiv

end AlgebraicGeometry

end TauCeti
