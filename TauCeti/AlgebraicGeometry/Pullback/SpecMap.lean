/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.TensorProduct.Pi

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

Compatible affine charts on any pullback square give an affine tensor-product chart on the fibre
product (`exists_isOpenImmersion_spec_tensorProduct_of_isPullback`) and pointwise lifts of primes
with contracted-prime identification (`exists_isOpenImmersion_spec_tensorProduct_at_of_isPullback`).

A split scheme `Spec (ι → L)` stays split after base change to a commutative `L`-algebra `F`,
with model `Spec (ι → F)` and compatibility with both pullback projections.

## Main declarations

* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapId`: pullback along `Spec.map (𝟙 R)` is the
  identity functor.
* `TauCeti.AlgebraicGeometry.Over.pullbackSpecMapComp`: pullback along `Spec.map (f ≫ g)` is a
  composite of pullbacks.
* `TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_of_isPullback`: compatible
  affine charts on any pullback square give an affine tensor-product chart on the fibre product
  with explicit projections and range.
* `TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_at_of_isPullback`: pointwise
  affine chart extraction on a pullback square with projected prime identification.
* `TauCeti.AlgebraicGeometry.isDominant_of_isPullback_spec` and
  `TauCeti.AlgebraicGeometry.isDominant_of_baseChange`: dominance of base-change projections and
  base-changed dominant morphisms along field extensions.
* `TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv`: an algebra equivalence
  identifies an affine base change over its new base.
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

/-- **Affine charts on a pullback square.** Given a pullback square `H : IsPullback gX f' f gY` of
schemes, a monomorphism `iY : Spec R ⟶ Y`, and open immersions `iY' : Spec S ⟶ Y'` and
`iX : Spec A ⟶ X` compatible with `gY` and `f`, the tensor product `Spec (S ⊗[R] A)` embeds as an
open subscheme of `X'` with range `(f' ⁻¹' Set.range iY') ∩ (gX ⁻¹' Set.range iX)`, compatible with
both `f'` and `gX`. -/
theorem exists_isOpenImmersion_spec_tensorProduct_of_isPullback
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    {X Y X' Y' : Scheme.{u}} {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    (H : IsPullback gX f' f gY)
    {iY : Spec (.of R) ⟶ Y} {iY' : Spec (.of S) ⟶ Y'} {iX : Spec (.of A) ⟶ X}
    [Mono iY] [IsOpenImmersion iY'] [IsOpenImmersion iX]
    (eY' : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ iY = iY' ≫ gY)
    (eX : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iY = iX ≫ f) :
    ∃ ι : Spec (.of (S ⊗[R] A)) ⟶ X', IsOpenImmersion ι ∧
      ι ≫ f' = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ iY' ∧
      ι ≫ gX = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ iX ∧
      Set.range ι = f' ⁻¹' Set.range iY' ∩ gX ⁻¹' Set.range iX := by
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A))) gY f iY' iX iY eY' eX
  have : IsOpenImmersion m := Scheme.pullback_map_isOpenImmersion ..
  let ι : Spec (.of (S ⊗[R] A)) ⟶ X' := (pullbackSpecIso R S A).inv ≫ m ≫ H.flip.isoPullback.inv
  have h₁ : ι ≫ f' =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ iY' := by simp [ι, m]
  have h₂ : ι ≫ gX = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ iX := by simp [ι, m]
  refine ⟨ι, inferInstance, h₁, h₂, Set.ext fun z ↦ ⟨?_, fun ⟨hy', hx⟩ ↦ ?_⟩⟩
  · rintro ⟨q, rfl⟩
    exact ⟨by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h₁]; exact ⟨_, rfl⟩,
      by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h₂]; exact ⟨_, rfl⟩⟩
  · have hw : H.flip.isoPullback.hom z ∈
        pullback.fst gY f ⁻¹' Set.range iY' ∩ pullback.snd gY f ⁻¹' Set.range iX :=
      ⟨by simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_fst]
        using hy',
       by simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_snd]
        using hx⟩
    rw [← Scheme.Pullback.range_map (f := Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R A))) gY f iY' iX iY eY' eX] at hw
    obtain ⟨p, hp⟩ := hw
    exact ⟨(pullbackSpecIso R S A).hom p, by simp [ι, m, hp]⟩

/-- **Pointwise affine chart on a pullback square.** Under the hypotheses of
`exists_isOpenImmersion_spec_tensorProduct_of_isPullback`, any point `x' : X'` whose images under
`f'` and `gX` lie in the ranges of `iY'` and `iX` lifts to a prime `q` of `S ⊗[R] A` along an
open immersion `ι : Spec (S ⊗[R] A) ⟶ X'`, whose right projection `p : Spec A` has prime equal
to `q.asIdeal.under A` and satisfies `gX (ι q) = iX p`. -/
theorem exists_isOpenImmersion_spec_tensorProduct_at_of_isPullback
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    {X Y X' Y' : Scheme.{u}} {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}
    (H : IsPullback gX f' f gY)
    {iY : Spec (.of R) ⟶ Y} {iY' : Spec (.of S) ⟶ Y'} {iX : Spec (.of A) ⟶ X}
    [Mono iY] [IsOpenImmersion iY'] [IsOpenImmersion iX]
    (eY' : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ iY = iY' ≫ gY)
    (eX : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iY = iX ≫ f)
    {x' : X'} (hy' : f' x' ∈ Set.range iY') (hx : gX x' ∈ Set.range iX) :
    ∃ (ι : Spec (.of (S ⊗[R] A)) ⟶ X') (_ : IsOpenImmersion ι)
      (q : Spec (.of (S ⊗[R] A))) (p : Spec (.of A)),
      letI : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
      ι q = x' ∧
      ι ≫ f' = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ iY' ∧
      ι ≫ gX = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) ≫ iX ∧
      gX (ι q) = iX p ∧
      p.asIdeal = q.asIdeal.under A := by
  obtain ⟨ι, hι, h₁, h₂, hrange⟩ :=
    exists_isOpenImmersion_spec_tensorProduct_of_isPullback H eY' eX
  obtain ⟨q, rfl⟩ : x' ∈ Set.range ι := hrange.symm ▸ ⟨hy', hx⟩
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let φR := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
  refine ⟨ι, hι, q, Spec.map φR q, rfl, h₁, h₂,
    by simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : _ ⟶ X ↦ k q) h₂,
    (congrArg PrimeSpectrum.asIdeal (Spec.map_apply φR q)).trans (PrimeSpectrum.comap_asIdeal _ q)⟩

/-- The projection from the base change along any field extension `K / k` is dominant. -/
theorem isDominant_of_isPullback_spec {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of K))] {g : Y ⟶ X}
    (H : IsPullback g (Y ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    IsDominant g :=
  have : Surjective g := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  inferInstance

/-- The base change of a dominant `k`-morphism between integral `k`-schemes along any field
extension `K / k` is dominant. -/
theorem isDominant_of_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X₁ X₂ X₁' X₂' : Scheme.{u}} [X₁.Over (Spec (.of k))] [X₂.Over (Spec (.of k))]
    [X₁'.Over (Spec (.of K))] [X₂'.Over (Spec (.of K))] [IsIntegral X₁] [IsIntegral X₂]
    {f : X₁ ⟶ X₂} [f.IsOver (Spec (.of k))] [IsDominant f]
    {g₁ : X₁' ⟶ X₁} {g₂ : X₂' ⟶ X₂} {f' : X₁' ⟶ X₂'} [f'.IsOver (Spec (.of K))]
    (H₁ : IsPullback g₁ (X₁' ↘ Spec (.of K)) (X₁ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (H₂ : IsPullback g₂ (X₂' ↘ Spec (.of K)) (X₂ ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hf' : f' ≫ g₂ = g₁ ≫ f) :
    IsDominant f' :=
  have : Flat g₂ := MorphismProperty.of_isPullback (P := @Flat) H₂.flip inferInstance
  IsDominant.of_isPullback_of_flat (IsPullback.of_bot (by simpa [comp_over] using H₁) hf'.symm H₂)

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
