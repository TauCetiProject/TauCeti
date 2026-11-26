/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Pi
import TauCeti.AlgebraicGeometry.AffineScheme.Basic

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

A split scheme `Spec (ι → L)` stays split after base change to a commutative `L`-algebra `F`,
with model `Spec (ι → F)` and compatibility with both pullback projections.

## Main declarations

* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapId`: pullback along `Spec.map (𝟙 R)` is the
  identity functor.
* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapComp`: pullback along `Spec.map (f ≫ g)` is a
  composite of pullbacks.
* `TauCeti.AlgebraicGeometry.exists_isOpenImmersion_tensorProduct_of_isPullback`: the base change
  of an affine chart is an affine chart of the base change.
* `TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv`: an algebra equivalence
  identifies an affine base change over its new base;
  `TauCeti.AlgebraicGeometry.pullbackSpecIsoOfIsPushout` is the resulting isomorphism with an
  affine `Spec T`-scheme whose global sections form an `Algebra.IsPushout`.
* `CategoryTheory.IsPullback.exists_split`: a scheme split over a commutative ring stays split
  after affine base change, with the same finite index type.
* `TauCeti.AlgebraicGeometry.tensorProductChart`: affine charts `Spec A ⟶ X` and `Spec B ⟶ Y`
  over an affine chart `Spec C ⟶ Z` give an affine chart `Spec (A ⊗[C] B)` of a fibre product of
  `X ⟶ Z ⟵ Y`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

namespace AlgebraicGeometry

universe u v

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

/-- Compatibility of `Y'.left.isoSpec.symm` with `Spec.algebraMap T Γ(Y'.left, ⊤)` when the
`T`-algebra structure on `Γ(Y'.left, ⊤)` is induced by `Y'.hom`. -/
private theorem isoSpec_symm_hom_comp_eq_algebraMap {T : Type u} [CommRing T]
    (Y' : Over (Spec (.of T))) [IsAffine Y'.left] [Algebra T Γ(Y'.left, ⊤)]
    (hY' : algebraMap T Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of T)).inv ≫ Y'.hom.appTop).hom) :
    Y'.left.isoSpec.symm.hom ≫ Y'.hom = (Over.mk (Spec.algebraMap T Γ(Y'.left, ⊤))).hom := by
  rw [Iso.symm_hom, ← cancel_epi Y'.left.isoSpec.hom, Iso.hom_inv_id_assoc,
    Scheme.isoSpec_hom, Spec.algebraMap, hY', CommRingCat.ofHom_hom]
  exact Y'.hom.toSpecΓ_SpecMap_ΓSpecIso_inv_comp_appTop.symm

/-- When the global sections of an affine `Spec T`-scheme `Y'` form a pushout `T ⊗[R] B`, the
base change `Spec B ×_{Spec R} Spec T` is isomorphic to `Y'` over `Spec T` via
`pullbackSpecIsoOfAlgEquiv` followed by `Y'.left.isoSpec.symm`. -/
noncomputable def pullbackSpecIsoOfIsPushout (R B T : Type u)
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T]
    (Y' : Over (Spec (.of T))) [IsAffine Y'.left]
    [Algebra R Γ(Y'.left, ⊤)] [Algebra B Γ(Y'.left, ⊤)] [Algebra T Γ(Y'.left, ⊤)]
    [IsScalarTower R B Γ(Y'.left, ⊤)] [IsScalarTower R T Γ(Y'.left, ⊤)]
    [Algebra.IsPushout R T B Γ(Y'.left, ⊤)]
    (hY' : algebraMap T Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of T)).inv ≫ Y'.hom.appTop).hom) :
    Over.mk (pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T)) ≅ Y' :=
  pullbackSpecIsoOfAlgEquiv R B T Γ(Y'.left, ⊤)
    (Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤)) ≪≫
    Over.isoMk Y'.left.isoSpec.symm (by exact isoSpec_symm_hom_comp_eq_algebraMap Y' hY')

/-- `pullbackSpecIsoOfIsPushout` factors as `pullbackSpecIsoOfAlgEquiv` of `Algebra.IsPushout.equiv`
followed by `Y'.left.isoSpec.symm` over `Spec T`. -/
theorem pullbackSpecIsoOfIsPushout_def (R B T : Type u)
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T]
    (Y' : Over (Spec (.of T))) [IsAffine Y'.left]
    [Algebra R Γ(Y'.left, ⊤)] [Algebra B Γ(Y'.left, ⊤)] [Algebra T Γ(Y'.left, ⊤)]
    [IsScalarTower R B Γ(Y'.left, ⊤)] [IsScalarTower R T Γ(Y'.left, ⊤)]
    [Algebra.IsPushout R T B Γ(Y'.left, ⊤)]
    (hY' : algebraMap T Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of T)).inv ≫ Y'.hom.appTop).hom) :
    pullbackSpecIsoOfIsPushout R B T Y' hY' =
      pullbackSpecIsoOfAlgEquiv R B T Γ(Y'.left, ⊤)
        (Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤)) ≪≫
        Over.isoMk Y'.left.isoSpec.symm (by exact isoSpec_symm_hom_comp_eq_algebraMap Y' hY') :=
  (rfl)

/-- The forward underlying map of `pullbackSpecIsoOfIsPushout` is the affine pullback comparison
followed by `Spec.map` of `(Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤)).symm` and
`Y'.left.isoSpec.inv`. -/
@[simp, reassoc]
theorem pullbackSpecIsoOfIsPushout_hom_left (R B T : Type u)
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T]
    (Y' : Over (Spec (.of T))) [IsAffine Y'.left]
    [Algebra R Γ(Y'.left, ⊤)] [Algebra B Γ(Y'.left, ⊤)] [Algebra T Γ(Y'.left, ⊤)]
    [IsScalarTower R B Γ(Y'.left, ⊤)] [IsScalarTower R T Γ(Y'.left, ⊤)]
    [Algebra.IsPushout R T B Γ(Y'.left, ⊤)]
    (hY' : algebraMap T Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of T)).inv ≫ Y'.hom.appTop).hom) :
    (pullbackSpecIsoOfIsPushout R B T Y' hY').hom.left =
      (pullbackSymmetry (Spec.algebraMap R B) (Spec.algebraMap R T)).hom ≫
        (pullbackSpecIso R T B).hom ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤)).symm.toRingHom) ≫
            Y'.left.isoSpec.inv := by
  simp [pullbackSpecIsoOfIsPushout_def]

/-- The inverse of `pullbackSpecIsoOfIsPushout` followed by the first projection to `Spec B` is
`Y'.left.toSpecΓ` followed by `Spec.map` of `algebraMap B Γ(Y'.left, ⊤)`. -/
@[reassoc (attr := simp)]
theorem pullbackSpecIsoOfIsPushout_inv_left_fst (R B T : Type u)
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T]
    (Y' : Over (Spec (.of T))) [IsAffine Y'.left]
    [Algebra R Γ(Y'.left, ⊤)] [Algebra B Γ(Y'.left, ⊤)] [Algebra T Γ(Y'.left, ⊤)]
    [IsScalarTower R B Γ(Y'.left, ⊤)] [IsScalarTower R T Γ(Y'.left, ⊤)]
    [Algebra.IsPushout R T B Γ(Y'.left, ⊤)]
    (hY' : algebraMap T Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of T)).inv ≫ Y'.hom.appTop).hom) :
    (pullbackSpecIsoOfIsPushout R B T Y' hY').inv.left ≫
        pullback.fst (Spec.algebraMap R B) (Spec.algebraMap R T) =
      Y'.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(Y'.left, ⊤))) := by
  have hval :
      (↑(Algebra.IsPushout.equiv R T B Γ(Y'.left, ⊤)) : T ⊗[R] B →+* Γ(Y'.left, ⊤)).comp
        ↑(Algebra.TensorProduct.includeRight : B →ₐ[R] T ⊗[R] B) =
        algebraMap B Γ(Y'.left, ⊤) := by
    ext b
    exact (Algebra.IsPushout.equiv_tmul R T B Γ(Y'.left, ⊤) 1 b).trans (by simp)
  simp [pullbackSpecIsoOfIsPushout_def, Scheme.isoSpec_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hval]

/-- The inverse of `pullbackSpecIsoOfIsPushout` followed by the second projection to `Spec T` is
the structure morphism `Y'.hom`. -/
@[reassoc (attr := simp)]
theorem pullbackSpecIsoOfIsPushout_inv_left_snd (R B T : Type u)
    [CommRing R] [CommRing B] [CommRing T] [Algebra R B] [Algebra R T]
    (Y' : Over (Spec (.of T))) [IsAffine Y'.left]
    [Algebra R Γ(Y'.left, ⊤)] [Algebra B Γ(Y'.left, ⊤)] [Algebra T Γ(Y'.left, ⊤)]
    [IsScalarTower R B Γ(Y'.left, ⊤)] [IsScalarTower R T Γ(Y'.left, ⊤)]
    [Algebra.IsPushout R T B Γ(Y'.left, ⊤)]
    (hY' : algebraMap T Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of T)).inv ≫ Y'.hom.appTop).hom) :
    (pullbackSpecIsoOfIsPushout R B T Y' hY').inv.left ≫
        pullback.snd (Spec.algebraMap R B) (Spec.algebraMap R T) =
      Y'.hom :=
  Over.w (pullbackSpecIsoOfIsPushout R B T Y' hY').inv

/-- **A split scheme stays split after base change.** If `s : S ⟶ Spec L` is identified with
`Spec (ι → L) ⟶ Spec L`, then every base change `s' : S' ⟶ Spec F` of `s` along
`Spec F ⟶ Spec L` is identified with `Spec (ι → F) ⟶ Spec F`, compatibly with the projection
to `S`. -/
theorem _root_.CategoryTheory.IsPullback.exists_split {L F : Type (max u v)}
    [CommRing L] [CommRing F] [Algebra L F] {ι : Type v} [Finite ι]
    {S S' : Scheme.{max u v}} {s : S ⟶ Spec (.of L)} {s' : S' ⟶ Spec (.of F)} {p : S' ⟶ S}
    (H : IsPullback p s' s (Spec.algebraMap L F)) (e : S ≅ Spec (.of (ι → L)))
    (he : e.hom ≫ Spec.algebraMap L (ι → L) = s) :
    ∃ e' : S' ≅ Spec (.of (ι → F)), e'.hom ≫ Spec.algebraMap F (ι → F) = s' ∧
      e'.hom ≫ Spec.algebraMap (ι → L) (ι → F) = p ≫ e.hom := by
  classical
  let _ := Fintype.ofFinite ι
  have H' : IsPullback (p ≫ e.hom) s' (Spec.algebraMap L (ι → L)) (Spec.algebraMap L F) := by
    simpa using H.paste_horiz (IsPullback.of_horiz_isIso (snd := s)
      (f := Spec.algebraMap L (ι → L)) (g := 𝟙 _) ⟨by rw [he, Category.comp_id]⟩)
  let eP := TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv L (ι → L) F (ι → F)
    (Algebra.TensorProduct.piScalarRight L F F ι)
  refine ⟨H'.isoPullback ≪≫ (Over.forget _).mapIso eP, ?_, ?_⟩
  · have := Over.w eP.hom
    simp only [Over.mk_hom] at this
    simp [this]
  · have hpi : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.piScalarRight L F F ι).symm.toRingHom) ≫
        Spec.algebraMap (ι → L) (ι → F) =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
      rw [← Spec.map_comp]
      refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
      apply (Algebra.TensorProduct.piScalarRight L F F ι).injective
      ext i
      simp [Algebra.smul_def]
      rfl
    simp only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, eP,
      TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv_hom_left, Category.assoc]
    rw [hpi]
    simp

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

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A pullback of schemes with affine coordinates is the spectrum of the tensor product,
compatibly with both projections. -/
theorem exists_pullback_isoSpec_tensorProduct
    {H Q M : Scheme.{u}} (q : Q ⟶ H) (s : M ⟶ H)
    (R A B : CommRingCat.{u}) [Algebra R A] [Algebra R B]
    (e0 : H ≅ Spec R) (eB : Q ≅ Spec B) (eA : M ≅ Spec A)
    (hB : q ≫ e0.hom = eB.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hA : s ≫ e0.hom = eA.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ i : pullback q s ≅ Spec (.of (A ⊗[R] B)),
      i.inv ≫ pullback.fst q s = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) ≫ eB.inv ∧
      i.inv ≫ pullback.snd q s = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) ≫ eA.inv := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let j : pullback q s ≅ pullback b a :=
    asIso (pullback.map q s b a eB.hom eA.hom e0.hom hB hA)
  let i := j ≪≫ pullbackSymmetry b a ≪≫ pullbackSpecIso R A B
  refine ⟨i, ?_, ?_⟩
  · apply (cancel_epi i.hom).mp
    simp [i, j, a, b]
  · apply (cancel_epi i.hom).mp
    simp [i, j, a, b]

/-- In affine coordinates, base change of a morphism is the spectrum of its tensor product map. -/
theorem nonempty_pullbackMap_arrowIso_specMap_tensorProduct
    {H P Q M : Scheme.{u}} (g : P ⟶ Q) (q : Q ⟶ H) (s : M ⟶ H)
    (R A B C : CommRingCat.{u}) [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : B →ₐ[R] C) (e0 : H ≅ Spec R) (eB : Q ≅ Spec B)
    (eC : P ≅ Spec C) (eA : M ≅ Spec A)
    (hB : q ≫ e0.hom = eB.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hC : g ≫ eB.hom = eC.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hA : s ≫ e0.hom = eA.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Nonempty (Arrow.mk (pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _)
      (by simp) (by simp)) ≅ Arrow.mk (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
  have hc : (g ≫ q) ≫ e0.hom =
      eC.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [Category.assoc, hB, ← Category.assoc, hC, Category.assoc]
    rw [← Spec.map_comp]
    congr 1
    exact congrArg (fun k : R →+* C ↦ Spec.map (CommRingCat.ofHom k)) φ.comp_algebraMap
  obtain ⟨iB, hb₁, hb₂⟩ := exists_pullback_isoSpec_tensorProduct q s R A B e0 eB eA hB hA
  obtain ⟨iC, hc₁, hc₂⟩ := exists_pullback_isoSpec_tensorProduct (g ≫ q) s R A C e0 eC eA hc hA
  let ψ := Algebra.TensorProduct.map (AlgHom.id R A) φ
  let sψ := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hRight : sψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    dsimp [sψ]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hLeft : sψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] C)) := by
    dsimp [sψ]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [ψ]
  have hh : sψ ≫ iB.inv = iC.inv ≫
      pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [hb₁, reassoc_of% hRight, reassoc_of% hc₁]
      rw [← cancel_mono eB.hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hC, Iso.inv_hom_id_assoc]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [hb₂, ← Category.assoc, hLeft, hc₂]
  refine ⟨Arrow.isoMk' _ sψ iC iB ?_⟩
  rw [← cancel_epi iC.inv, ← cancel_mono iB.inv]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh


end AlgebraicGeometry.Scheme.Hom
