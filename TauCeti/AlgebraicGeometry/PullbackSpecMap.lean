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

end AlgebraicGeometry

end TauCeti
