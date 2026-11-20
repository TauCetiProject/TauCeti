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
  identifies an affine base change over its new base.
* `TauCeti.AlgebraicGeometry.tensorProductChart`: affine charts `Spec A ⟶ X` and `Spec B ⟶ Y`
  over an affine chart `Spec C ⟶ Z` give an affine chart `Spec (A ⊗[C] B)` of a fibre product of
  `X ⟶ Z ⟵ Y`.
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

section TensorProductChart

variable {X Y Z P : Scheme.{u}} {g₁ : X ⟶ Z} {g₂ : Y ⟶ Z} {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
  (hP : IsPullback p₁ p₂ g₁ g₂) {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra C A] [Algebra C B] {iA : Spec (.of A) ⟶ X} {iB : Spec (.of B) ⟶ Y}
  {iC : Spec (.of C) ⟶ Z}
  (hA : Spec.map (CommRingCat.ofHom (algebraMap C A)) ≫ iC = iA ≫ g₁)
  (hB : Spec.map (CommRingCat.ofHom (algebraMap C B)) ≫ iC = iB ≫ g₂)

/-- The affine chart `Spec (A ⊗[C] B) ⟶ P` of a fibre product `P` of `X ⟶ Z ⟵ Y`, built from
affine charts `Spec A ⟶ X` and `Spec B ⟶ Y` lying over an affine chart `Spec C ⟶ Z`. -/
noncomputable def tensorProductChart : Spec (.of (A ⊗[C] B)) ⟶ P :=
  (pullbackSpecIso C A B).inv ≫ pullback.map _ _ _ _ iA iB iC hA hB ≫ hP.isoPullback.inv

/-- The tensor-product chart of a fibre product of open charts is an open chart. -/
instance [IsOpenImmersion iA] [IsOpenImmersion iB] [IsOpenImmersion iC] :
    IsOpenImmersion (tensorProductChart hP hA hB) := by
  unfold tensorProductChart
  infer_instance

/-- The first projection of the tensor-product chart is the chart of `X` on the left factor. -/
@[reassoc (attr := simp)]
theorem tensorProductChart_fst : tensorProductChart hP hA hB ≫ p₁ =
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ iA := by
  simp [tensorProductChart]

/-- The second projection of the tensor-product chart is the chart of `Y` on the right factor. -/
@[reassoc (attr := simp)]
theorem tensorProductChart_snd : tensorProductChart hP hA hB ≫ p₂ = Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := C) (A := A) (B := B)).toRingHom) ≫ iB := by
  simp [tensorProductChart]

end TensorProductChart

end AlgebraicGeometry

end TauCeti
