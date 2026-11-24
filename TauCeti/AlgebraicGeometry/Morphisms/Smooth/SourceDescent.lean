/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.Algebra.Colimit.DirectLimit
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Regular.Descent
import TauCeti.RingTheory.Flat.FaithfullyFlat.DirectLimit
import TauCeti.RingTheory.RingHom.Etale
import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# Smoothness along flat and étale surjections on the source

Smoothness can be checked after a flat surjective presentation of the source. This supports
smooth quotient constructions and complements descent after base change on the target.

The resulting morphism must be locally of finite presentation; over a field, local finite
type suffices. These finiteness hypotheses do not descend along arbitrary flat surjections
without additional covering hypotheses. The covering morphism itself need not be locally
finitely presented or quasi-compact.

When the covering morphism `p : X' ⟶ X` is étale and surjective, local finite presentation
descends from `p ≫ f` to `f` as well, so `f` is smooth of relative dimension `n` if and only if
`p ≫ f` is
(`AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_comp_iff_of_etale_of_surjective`),
with no prior smoothness or finite-presentation assumption on `f`.

## Main results

* `AlgebraicGeometry.Smooth.of_comp_surjective`: smoothness descends along a flat surjection
  on the source when the resulting morphism is locally of finite presentation.
* `AlgebraicGeometry.SmoothOfRelativeDimension.of_comp_of_etale_of_surjective`: if
  `p : X' ⟶ X` is étale and surjective and `p ≫ f` is smooth of relative dimension `n`, then `f`
  is smooth of relative dimension `n`.
* `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_comp_iff_of_etale_of_surjective`: for
  `p : X' ⟶ X` étale and surjective and `f : X ⟶ Y`, `p ≫ f` is smooth of relative dimension `n`
  if and only if `f` is.

## References

* The Stacks Project, Tags 05AX, 05B5, 04N7, 036N, and 00ON.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

private theorem smooth_pullback_snd_comp {X' X S T : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) (g : T ⟶ S) [Smooth (u ≫ f)] :
    Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g) := by
  rw [← pullbackRightPullbackFstIso_hom_snd]
  infer_instance

/-- Smoothness over a field descends through any flat surjection on the source, provided
that the target morphism is locally of finite type. -/
private theorem Smooth.of_comp_surjective_of_field {K : Type u} [Field K] {X' X : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Flat u] [Surjective u]
    [LocallyOfFiniteType f] [Smooth (u ≫ f)] : Smooth f := by
  -- Keep the induction hypothesis from becoming a local Smooth instance.
  change id (Smooth f)
  wlog hK : IsAlgClosed K generalizing K X X' with H
  · let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    have := smooth_pullback_snd_comp u f g
    have hsnd := H (pullback.snd u (pullback.fst f g)) (pullback.snd f g)
      (AlgebraicClosure.isAlgClosed K)
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsnd
  -- Over an algebraically closed field, regular stalks characterize smoothness.
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x ↦ by
    obtain ⟨x', rfl⟩ := u.surjective x
    have : IsRegularLocalRing (X'.presheaf.stalk x') :=
      TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth (u ≫ f) x'
    exact u.isRegularLocalRing_stalk_of_flat x'
  exact f.smooth_of_isRegularLocalRing_stalk

/-- Smoothness of a locally finitely presented morphism descends through any flat surjection
on its source. The covering morphism need not be quasi-compact or locally finitely presented. -/
theorem Smooth.of_comp_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation f] [Smooth (u ≫ f)] : Smooth f := by
  have : Flat f := Flat.of_comp_surjective u f
  refine Smooth.of_smooth_fiberToSpecResidueField f fun s ↦ ?_
  -- Unfold the named fibre so pullback instances can see its projection maps.
  dsimp only [Scheme.Hom.fiber, Scheme.Hom.fiberToSpecResidueField]
  let g := S.fromSpecResidueField s
  have := smooth_pullback_snd_comp u f g
  exact Smooth.of_comp_surjective_of_field (K := S.residueField s)
    (pullback.snd u (pullback.fst f g)) (pullback.snd f g)

section SmoothOfRelativeDimension

open MorphismProperty TauCeti.AlgebraicGeometry

open scoped TensorProduct in
-- Transfer faithful flatness of a base change from an algebra isomorphic to a direct limit
-- down to a finite stage above a prescribed index.
private theorem exists_faithfullyFlat_baseChange_of_algEquiv
    {A ι : Type*} [CommRing A] [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {B : ι → Type*} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
    {T : Type*} [CommRing T] [Algebra A T] (e : DirectLimit B f ≃ₐ[A] T)
    (S : Type*) [CommRing S] [Algebra A S] [Module.Flat A S]
    [Algebra.FinitePresentation A S] [Module.FaithfullyFlat T (T ⊗[A] S)] (i : ι) :
    ∃ j, i ≤ j ∧ Module.FaithfullyFlat (B j) (B j ⊗[A] S) := by
  have : Module.FaithfullyFlat (DirectLimit B f) ((DirectLimit B f) ⊗[A] S) := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    let φ : (DirectLimit B f) ⊗[A] S ≃ₐ[A] T ⊗[A] S := Algebra.TensorProduct.congr e .refl
    have hcomp :
        algebraMap (DirectLimit B f) ((DirectLimit B f) ⊗[A] S) =
          φ.symm.toRingHom.comp ((algebraMap T (T ⊗[A] S)).comp e.toRingHom) := by
      ext x
      simp [φ, Algebra.TensorProduct.algebraMap_apply]
    rw [hcomp]
    exact RingHom.FaithfullyFlat.comp
      (RingHom.FaithfullyFlat.comp (RingHom.FaithfullyFlat.of_bijective e.bijective)
        (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance))
      (RingHom.FaithfullyFlat.of_bijective φ.symm.bijective)
  exact TauCeti.DirectLimit.Algebra.exists_faithfullyFlat_baseChange (f := f) S i

open scoped TensorProduct in
-- Finite type descends along an étale faithfully flat algebra map.
private theorem finiteType_of_comp_etale_faithfullyFlat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.Etale A B] [Module.FaithfullyFlat A B] [Algebra.FinitePresentation R B] :
    Algebra.FiniteType R A := by
  classical
  obtain ⟨A₀, B₀, _, _, hA₀, _, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg R A B
  obtain ⟨G₀, hG₀⟩ := hA₀
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := B)
  have hrep (x : s) := TensorProduct.exists_sum_tmul_eq (e x.val)
  choose k a y hxy using hrep
  let S₁ : Finset A := s.attach.biUnion fun x ↦ Finset.univ.image (a x)
  let stage (t : Finset A) : Subalgebra R A := Algebra.adjoin R (↑(G₀ ∪ t) : Set A)
  have hA₀_le (t : Finset A) : A₀ ≤ stage t := by
    rw [← hG₀]
    exact Algebra.adjoin_mono (by intro z hz; simp [hz])
  let Bstage (t : Finset A) : Type u := stage t
  let : ∀ t, CommRing (Bstage t) := fun _ ↦ inferInstance
  let : ∀ t, Algebra A₀ (Bstage t) := fun t ↦ (Subalgebra.inclusion (hA₀_le t)).toAlgebra
  let fstage (t₁ t₂ : Finset A) (ht : t₁ ≤ t₂) : Bstage t₁ →ₐ[A₀] Bstage t₂ :=
    { Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.mpr (Finset.union_subset_union Finset.Subset.rfl ht))) with
      commutes' := fun _ ↦ rfl }
  have : DirectedSystem Bstage (fstage · · ·) :=
    { map_self := fun _ _ ↦ rfl
      map_map := fun _ _ _ _ _ _ ↦ rfl }
  let eColim : DirectLimit Bstage fstage ≃ₐ[A₀] A :=
    AlgEquiv.ofBijective
      (DirectLimit.Algebra.lift Bstage fstage A
        (fun t ↦ { (stage t).val with commutes' := fun _ ↦ rfl }) (fun _ _ _ _ ↦ rfl))
      ⟨fun x y hxy ↦ by
        obtain ⟨t₁, x₁, rfl⟩ := DirectLimit.exists_eq_mk _ x
        obtain ⟨t₂, x₂, rfl⟩ := DirectLimit.exists_eq_mk _ y
        exact Quotient.sound ⟨t₁ ∪ t₂, Finset.subset_union_left, Finset.subset_union_right,
          Subtype.val_injective hxy⟩,
       fun x ↦ ⟨DirectLimit.Algebra.of Bstage fstage {x}
         ⟨x, Algebra.subset_adjoin (by simp)⟩, rfl⟩⟩
  have : Module.FaithfullyFlat A (A ⊗[A₀] B₀) :=
    .of_linearEquiv A B e.symm.toLinearEquiv
  obtain ⟨S₂, hS₁S₂, _⟩ := exists_faithfullyFlat_baseChange_of_algEquiv eColim B₀ S₁
  let A₁ := stage S₂
  let B₁ := A₁ ⊗[A₀] B₀
  have : IsScalarTower A₀ A₁ A := .of_algebraMap_eq fun _ ↦ rfl
  let gAlg : B₁ →ₐ[R] B :=
    ((e.symm.restrictScalars R).toAlgHom).comp
      ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom A₀ A₁ A) (.id A₀ B₀)).restrictScalars R)
  have hg_surj : Function.Surjective gAlg := by
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    intro b hb
    let x : s := ⟨b, hb⟩
    have ha_mem : ∀ j : Fin (k x), a x j ∈ (↑(G₀ ∪ S₂) : Set A) := fun j ↦ by
      refine Finset.mem_coe.mpr (Finset.mem_union_right _ (hS₁S₂ ?_))
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_attach _ _,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    have ha₁ (j : Fin (k x)) : a x j ∈ A₁ := Algebra.subset_adjoin (ha_mem j)
    refine ⟨∑ j : Fin (k x), (⟨a x j, ha₁ j⟩ : A₁) ⊗ₜ[A₀] y x j, ?_⟩
    calc gAlg (∑ j : Fin (k x), (⟨a x j, ha₁ j⟩ : A₁) ⊗ₜ[A₀] y x j)
        = ∑ j : Fin (k x), e.symm (a x j ⊗ₜ[A₀] y x j) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ ↦ congrArg e.symm rfl
      _ = e.symm (∑ j : Fin (k x), a x j ⊗ₜ[A₀] y x j) := (map_sum e.symm _ _).symm
      _ = b := by rw [← hxy x, AlgEquiv.symm_apply_apply]
  let Φ : B₁ ⊗[A₁] A ≃+* B :=
    (Algebra.TensorProduct.comm A₁ B₁ A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange A₀ A₁ A₁ A B₀).toRingEquiv.trans
        e.symm.toRingEquiv)
  have hΦ_eq : ∀ b₁ : B₁, Φ (b₁ ⊗ₜ[A₁] 1) = gAlg b₁ := fun b₁ ↦ by
    induction b₁ using TensorProduct.inductionOn with
    | add _ _ ih₁ ih₂ => simp only [TensorProduct.add_tmul, map_add, ih₁, ih₂]
    | tmul a₁ b₀ =>
      simp only [Φ, gAlg, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
        AlgHom.coe_comp, AlgHom.coe_restrictScalars', AlgEquiv.coe_toAlgHom,
        Function.comp_apply, Algebra.TensorProduct.comm_tmul]
      have hcan :
          Algebra.TensorProduct.cancelBaseChange A₀ A₁ A₁ A B₀ (1 ⊗ₜ[A₁] (a₁ ⊗ₜ[A₀] b₀)) =
            (a₁ • (1 : A)) ⊗ₜ[A₀] b₀ :=
        Algebra.TensorProduct.cancelBaseChange_tmul A₀ A₁ A₁ A B₀ (1 : A) a₁ b₀
      rw [hcan, Algebra.smul_def, mul_one]
      rfl
  have hlTensor_surj : Function.Surjective (LinearMap.lTensor B₁ (Algebra.linearMap A₁ A)) := by
    intro w
    obtain ⟨b₁, hb₁⟩ := hg_surj (Φ w)
    refine ⟨b₁ ⊗ₜ[A₁] (1 : A₁), Φ.injective ?_⟩
    simpa [hΦ_eq] using hb₁
  have hA₁_surj : Function.Surjective (Algebra.linearMap A₁ A) :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A₁ B₁
      (Algebra.linearMap A₁ A)).mp hlTensor_surj
  have htop_sub : A₁ = ⊤ := eq_top_iff.mpr fun a _ ↦ by
    obtain ⟨a₁, rfl⟩ := hA₁_surj a
    exact a₁.property
  exact ⟨⟨G₀ ∪ S₂, by simpa [A₁, stage] using htop_sub⟩⟩

section QuotientSystem

private def SubidealFG {A₀ : Type u} [CommRing A₀] (J : Ideal A₀) :=
  { J' : Ideal A₀ // J' ≤ J ∧ J'.FG }

private instance {A₀ : Type u} [CommRing A₀] (J : Ideal A₀) : Preorder (SubidealFG J) :=
  Preorder.lift Subtype.val

private instance {A₀ : Type u} [CommRing A₀] (J : Ideal A₀) : Nonempty (SubidealFG J) :=
  ⟨⟨⊥, bot_le, Submodule.fg_bot⟩⟩

private instance {A₀ : Type u} [CommRing A₀] (J : Ideal A₀) : IsDirectedOrder (SubidealFG J) :=
  ⟨fun J₁ J₂ ↦
    ⟨⟨J₁.val ⊔ J₂.val, sup_le J₁.property.1 J₂.property.1,
      Submodule.FG.sup J₁.property.2 J₂.property.2⟩,
      (le_sup_left : J₁.val ≤ J₁.val ⊔ J₂.val),
      (le_sup_right : J₂.val ≤ J₁.val ⊔ J₂.val)⟩⟩

private def quotientFunctor {A₀ : Type u} [CommRing A₀] (J : Ideal A₀) :
    SubidealFG J ⥤ CommRingCat.{u} where
  obj J' := CommRingCat.of (A₀ ⧸ J'.val)
  map h := CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom h))

private def quotientCocone {A₀ : Type u} [CommRing A₀] (J : Ideal A₀) :
    Cocone (quotientFunctor J) where
  pt := CommRingCat.of (A₀ ⧸ J)
  ι :=
    { app J' := CommRingCat.ofHom (Ideal.Quotient.factor J'.property.1)
      naturality _ J₂ h := CommRingCat.hom_ext
        (Ideal.Quotient.factor_comp (leOfHom h) J₂.property.1) }

private noncomputable def quotientIsColimit {A₀ : Type u} [CommRing A₀] (J : Ideal A₀) :
    IsColimit (quotientCocone J) :=
  isColimitOfReflects (forget CommRingCat.{u}) <|
    Types.FilteredColimit.isColimitOf' _ _
      (fun x ↦ by
        obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨⟨⊥, bot_le, Submodule.fg_bot⟩, Ideal.Quotient.mk ⊥ x₀, rfl⟩)
      (fun J₁ x y hxy ↦ by
        obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
        let J₂ : SubidealFG J := ⟨J₁.val ⊔ Ideal.span {x₀ - y₀},
          sup_le J₁.property.1
            (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.Quotient.eq.mp hxy))),
          Submodule.FG.sup J₁.property.2 (Submodule.fg_span (Set.finite_singleton _))⟩
        refine ⟨J₂, homOfLE (le_sup_left : J₁.val ≤ J₂.val), ?_⟩
        exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_right (Ideal.subset_span rfl)))

end QuotientSystem

open scoped TensorProduct in
private theorem fg_ker_of_etale_faithfullyFlat {R A' A'' Q B' B : Type u} [CommRing R] [CommRing A']
    [CommRing A''] [CommRing Q] [CommRing B'] [CommRing B] [Algebra R A'] [Algebra R A'']
    [Algebra R B] [Algebra A' A''] [Algebra A' Q] [Algebra A'' Q]
    [Algebra A' B'] [Algebra Q B] [Algebra A' B] [IsScalarTower R A' A'']
    [IsScalarTower A' A'' Q] [IsScalarTower A' Q B] [IsScalarTower R A' B]
    (ePush : Q ⊗[A'] B' ≃ₐ[Q] B)
    (hsurj : Function.Surjective (algebraMap A'' Q)) [Algebra.Etale A' B']
    [Module.FaithfullyFlat A'' (A'' ⊗[A'] B')] [Algebra.FinitePresentation R A'']
    [Algebra.FinitePresentation R B] : (RingHom.ker (algebraMap A'' Q)).FG := by
  let B'' := A'' ⊗[A'] B'
  have : Algebra.Etale A'' B'' := inferInstance
  have : Algebra.FinitePresentation R B'' := .trans R A'' B''
  let f : A'' →ₐ[A''] Q := Algebra.ofId A'' Q
  let K : Ideal A'' := RingHom.ker f.toRingHom
  let eK : (A'' ⧸ K) ≃ₐ[A''] Q := Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj
  let e : (B'' ⧸ K.map (algebraMap A'' B'')) ≃ₐ[A'] B :=
    ((Algebra.TensorProduct.quotientTensorEquiv (R := A') A' B' A'' K).symm.trans
      (Algebra.TensorProduct.congr (eK.restrictScalars A') .refl)).trans
      (ePush.restrictScalars A')
  let ψ : B'' →ₐ[R] B :=
    (e.restrictScalars R).toAlgHom.comp (Ideal.Quotient.mkₐ R (K.map (algebraMap A'' B'')))
  have hψ_surj : Function.Surjective ψ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hkerFG : (RingHom.ker ψ.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective ψ hψ_surj
  have hker_eq : RingHom.ker ψ.toRingHom = K.map (algebraMap A'' B'') := by
    ext b
    change e (Ideal.Quotient.mk (K.map (algebraMap A'' B'')) b) = 0 ↔
      b ∈ K.map (algebraMap A'' B'')
    rw [map_eq_zero_iff e e.injective, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.FG.of_FG_map_of_faithfullyFlat (hker_eq ▸ hkerFG)

open scoped TensorProduct in
-- Finite presentation descends along an étale faithfully flat algebra map.
private theorem finitePresentation_of_comp_etale_faithfullyFlat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.Etale A B] [Module.FaithfullyFlat A B] [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A := by
  have : Algebra.FiniteType R A :=
    finiteType_of_comp_etale_faithfullyFlat (R := R) (A := A) (B := B)
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType R A›
  let A₀ := MvPolynomial (Fin n) R
  let J : Ideal A₀ := RingHom.ker π.toRingHom
  let eA : (A₀ ⧸ J) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hπ
  let ψJ : (A₀ ⧸ J) →+* B := (algebraMap A B).comp eA.toRingHom
  have hψJ : ψJ.Etale :=
    RingHom.Etale.comp (RingHom.etale_algebraMap.mpr inferInstance)
      (RingHom.Etale.of_bijective eA.bijective)
  obtain ⟨J', T', f', g', hpush, hf'⟩ :=
    RingHom.Etale.preIndSpreads.exists_isPushout (quotientIsColimit J) (CommRingCat.ofHom ψJ) hψJ
  let A' := A₀ ⧸ J'.val
  let B' : Type u := T'
  let : Algebra A' B' := f'.hom.toAlgebra
  let : Algebra A' (A₀ ⧸ J) := (Ideal.Quotient.factor J'.property.1).toAlgebra
  let : Algebra (A₀ ⧸ J) B := ψJ.toAlgebra
  let : Algebra B' B := g'.hom.toAlgebra
  let : Algebra A' B := (ψJ.comp (Ideal.Quotient.factor J'.property.1)).toAlgebra
  have : IsScalarTower A' (A₀ ⧸ J) B := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A' B' B := .of_algebraMap_eq fun x ↦ congr($hpush.w x)
  have : IsScalarTower R (A₀ ⧸ J) B :=
    .of_algebraMap_eq (R := R) (S := A₀ ⧸ J) (A := B) fun r ↦ by
      change algebraMap R B r = algebraMap A B (eA (algebraMap R (A₀ ⧸ J) r))
      rw [eA.commutes, ← IsScalarTower.algebraMap_apply R A B]
  have : Algebra.Etale A' B' := hf'
  have : Module.FaithfullyFlat (A₀ ⧸ J) B := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    change ((algebraMap A B).comp eA.toRingHom).FaithfullyFlat
    exact RingHom.FaithfullyFlat.comp
      (RingHom.FaithfullyFlat.of_bijective eA.bijective)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Algebra.IsPushout A' (A₀ ⧸ J) B' B := CommRingCat.isPushout_iff_isPushout.mp hpush
  let ePush : (A₀ ⧸ J) ⊗[A'] B' ≃ₐ[A₀ ⧸ J] B := Algebra.IsPushout.equiv A' (A₀ ⧸ J) B' B
  let D := quotientFunctor J
  have : Nonempty { i : SubidealFG J // J' ≤ i } := ⟨⟨J', le_rfl⟩⟩
  have : IsDirectedOrder { i : SubidealFG J // J' ≤ i } := ⟨fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
    exact ⟨⟨k, i.property.trans hik⟩, hik, hjk⟩⟩
  let : ∀ j : { i : SubidealFG J // J' ≤ i }, Algebra (D.obj J') (D.obj j.val) :=
    fun j ↦ (D.map (homOfLE j.property)).hom.toAlgebra
  obtain ⟨fTail, hfTail, ⟨eTail⟩⟩ :=
    CategoryTheory.Functor.exists_directLimit_tail_algEquiv_colimit D J'
  let : DirectedSystem (fun j : { i : SubidealFG J // J' ≤ i } ↦ D.obj j.val) (fTail · · ·) :=
    hfTail
  let : Algebra (D.obj J') (colimit D : CommRingCat.{u}) := (colimit.ι D J').hom.toAlgebra
  let : Algebra (D.obj J') (A₀ ⧸ J) := (Ideal.Quotient.factor J'.property.1).toAlgebra
  let : Algebra (D.obj J') B' := f'.hom.toAlgebra
  have : Algebra.Etale (D.obj J') B' := hf'
  have : Module.FaithfullyFlat (A₀ ⧸ J) ((A₀ ⧸ J) ⊗[D.obj J'] B') :=
    .of_linearEquiv (A₀ ⧸ J) B ePush.toLinearEquiv
  let iso : (colimit D : CommRingCat.{u}) ≅ CommRingCat.of (A₀ ⧸ J) :=
    (colimit.isColimit D).coconePointUniqueUpToIso (quotientIsColimit J)
  let eIso : (colimit D : CommRingCat.{u}) ≃ₐ[D.obj J'] (A₀ ⧸ J) :=
    { iso.hom.hom with
      invFun := iso.inv.hom
      left_inv x := ConcreteCategory.congr_hom iso.hom_inv_id x
      right_inv x := ConcreteCategory.congr_hom iso.inv_hom_id x
      commutes' x := ConcreteCategory.congr_hom
        ((colimit.isColimit D).comp_coconePointUniqueUpToIso_hom (quotientIsColimit J) J') x }
  obtain ⟨J'', _, hFF''⟩ :=
    exists_faithfullyFlat_baseChange_of_algEquiv (A := D.obj J') (f := fTail)
      (eTail.trans eIso) B' ⟨J', le_rfl⟩
  let J₂ : Ideal A₀ := J''.val.val
  have hJ'J₂ : J'.val ≤ J₂ := J''.property
  have hJ₂J : J₂ ≤ J := J''.val.property.1
  have hJ₂FG : J₂.FG := J''.val.property.2
  let A'' := A₀ ⧸ J₂
  let : Algebra A' A'' := (Ideal.Quotient.factor hJ'J₂).toAlgebra
  let : Algebra A'' (A₀ ⧸ J) := (Ideal.Quotient.factor hJ₂J).toAlgebra
  have : Module.FaithfullyFlat A'' (A'' ⊗[A'] B') := hFF''
  let : Algebra R B' := Algebra.compHom B' (algebraMap R A')
  have : IsScalarTower A' A'' (A₀ ⧸ J) := .of_algebraMap_eq fun x ↦ by
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have : IsScalarTower R A' B' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R A' A'' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R A'' (A₀ ⧸ J) :=
    .of_algebraMap_eq (R := R) (S := A'') (A := A₀ ⧸ J) fun _ ↦ rfl
  have : IsScalarTower R A' (A₀ ⧸ J) :=
    .of_algebraMap_eq (R := R) (S := A') (A := A₀ ⧸ J) fun _ ↦ rfl
  have : IsScalarTower R A' B := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R (A₀ ⧸ J) B,
      IsScalarTower.algebraMap_apply R A' (A₀ ⧸ J),
      IsScalarTower.algebraMap_apply A' (A₀ ⧸ J) B]
  have : Algebra.FinitePresentation R A₀ := inferInstance
  have : Algebra.FinitePresentation R A'' := .quotient hJ₂FG
  let K : Ideal A'' := RingHom.ker (Ideal.Quotient.factor hJ₂J)
  have hKFG : K.FG :=
    fg_ker_of_etale_faithfullyFlat (R := R) ePush (Ideal.Quotient.factor_surjective hJ₂J)
  have hJFG : J.FG := by
    have hcomp := Ideal.fg_ker_comp (Ideal.Quotient.mk J₂) (Ideal.Quotient.factor hJ₂J)
      (by simpa [Ideal.mk_ker] using hJ₂FG) hKFG Ideal.Quotient.mk_surjective
    simpa [Ideal.Quotient.factor_comp_mk, Ideal.mk_ker] using hcomp
  have : Algebra.FinitePresentation R (A₀ ⧸ J) := .quotient hJFG
  exact .equiv eA

-- Local finite presentation descends along étale surjections on the source.
private theorem locallyOfFinitePresentation_of_comp_of_etale_of_surjective {X' X Y : Scheme.{u}}
    (p : X' ⟶ X) (f : X ⟶ Y) [Etale p] [Surjective p]
    [LocallyOfFinitePresentation (p ≫ f)] : LocallyOfFinitePresentation f := by
  refine (HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)).mpr ?_
  intro U W hWU
  let pW : (p ⁻¹ᵁ W.val).toScheme ⟶ W.val.toScheme := p ∣_ W.val
  have : Etale pW := inferInstanceAs (Etale (p ∣_ W.val))
  have : Surjective pW :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict p W.val).flip
      inferInstance
  obtain ⟨V : (p ⁻¹ᵁ W.val).toScheme.Opens, hV, hVim⟩ :=
    pW.isOpenMap.exists_opens_image_eq_of_prespectralSpace
      pW.continuous (by simp) isOpen_univ isCompact_univ
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have hVpW_surj : Surjective (V.ι ≫ pW) := ⟨fun w ↦ by
    obtain ⟨v, hvV, hvw⟩ := hVim.ge (Set.mem_univ w)
    exact ⟨⟨v, hvV⟩, hvw⟩⟩
  have : IsZariskiLocalAtSource @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  have : MorphismProperty.ContainsIdentities (@Etale.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  obtain ⟨Z, s, hs_surj, hs_et, hZ_aff⟩ :=
    Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource @Etale.{u} V.toScheme
  let q : Z ⟶ W.val.toScheme := s ≫ V.ι ≫ pW
  have : Etale q := by
    have : Etale (V.ι ≫ pW) := IsZariskiLocalAtSource.comp (P := @Etale.{u}) inferInstance _
    exact inferInstance
  have : Surjective q := ⟨fun w ↦ by
    obtain ⟨v, hv⟩ := hVpW_surj.surj w
    obtain ⟨z, hz⟩ := hs_surj.surj v
    refine ⟨z, ?_⟩
    change (V.ι ≫ pW) (s z) = w
    rw [hz, hv]⟩
  have hqcomp : q ≫ f.resLE U.val W.val hWU ≫ U.val.ι =
      (s ≫ V.ι ≫ (p ⁻¹ᵁ W.val).ι) ≫ (p ≫ f) := by
    simp only [q, pW, Category.assoc, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι_assoc]
  have : LocallyOfFinitePresentation (q ≫ f.resLE U.val W.val hWU) := by
    refine locallyOfFinitePresentation_of_comp (q ≫ f.resLE U.val W.val hWU) U.val.ι (hfg := ?_)
    rw [Category.assoc, hqcomp]
    have : LocallyOfFinitePresentation (s ≫ V.ι ≫ (p ⁻¹ᵁ W.val).ι) := inferInstance
    exact MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ this inferInstance
  algebraize [(f.resLE U.val W.val hWU).appTop.hom, q.appTop.hom,
    q.appTop.hom.comp (f.resLE U.val W.val hWU).appTop.hom]
  have : Algebra.Etale Γ(W.val.toScheme, ⊤) Γ(Z, ⊤) := by
    change q.appTop.hom.Etale
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  have : Module.FaithfullyFlat Γ(W.val.toScheme, ⊤) Γ(Z, ⊤) :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨inferInstance, inferInstance⟩
  have : Algebra.FinitePresentation Γ(U.val.toScheme, ⊤) Γ(Z, ⊤) := by
    change (q.appTop.hom.comp (f.resLE U.val W.val hWU).appTop.hom).FinitePresentation
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    exact Scheme.Hom.finitePresentation_appTop (q ≫ f.resLE U.val W.val hWU)
  have hFP : (f.resLE U.val W.val hWU).appTop.hom.FinitePresentation :=
    finitePresentation_of_comp_etale_faithfullyFlat
      (R := Γ(U.val.toScheme, ⊤)) (A := Γ(W.val.toScheme, ⊤)) (B := Γ(Z, ⊤))
  exact (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U.val W.val hWU)).mp hFP

-- Over a field, if `f : X ⟶ Spec k` is smooth, `p : X' ⟶ X` is étale and surjective, and
-- `p ≫ f` is smooth of relative dimension `n`, then `f` is smooth of relative dimension `n`.
private theorem SmoothOfRelativeDimension.of_comp_of_etale_of_surjective_field {k : Type u}
    [Field k] {X X' : Scheme.{u}} {n : ℕ} (p : X' ⟶ X) (f : X ⟶ Spec (.of k))
    [Etale p] [Surjective p] [Smooth f] [SmoothOfRelativeDimension n (p ≫ f)] :
    SmoothOfRelativeDimension n f := by
  have := SmoothOfRelativeDimension.smooth n (p ≫ f)
  have : JacobsonSpace X' := LocallyOfFiniteType.jacobsonSpace (p ≫ f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim' :=
    ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (p ≫ f) n).mp inferInstance).2
  refine (smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f n).mpr ⟨‹_›, fun x hx ↦ ?_⟩
  -- The closed fibre `p ⁻¹' {x}` is nonempty in the Jacobson space `X'`, so it contains a closed
  -- point `x'` of `X'`, at which `p` preserves the local Krull dimension.
  obtain ⟨z, hz⟩ := p.surjective x
  obtain ⟨x', hx', hx'c⟩ := nonempty_inter_closedPoints (⟨z, hz⟩ : (p ⁻¹' {x}).Nonempty)
    (hx.preimage p.continuous).isLocallyClosed
  have hpx' : p x' = x := hx'
  rw [← hpx', p.ringKrullDim_stalk_eq_of_etale x']
  exact hdim' x' hx'c

/-- **Smooth relative dimension descends along étale surjective morphisms on the source.** If
`p : X' ⟶ X` is étale and surjective and `p ≫ f` is smooth of relative dimension `n`, then `f` is
smooth of relative dimension `n`. -/
theorem SmoothOfRelativeDimension.of_comp_of_etale_of_surjective {X X' Y : Scheme.{u}} {n : ℕ}
    (p : X' ⟶ X) (f : X ⟶ Y) [Etale p] [Surjective p]
    [SmoothOfRelativeDimension n (p ≫ f)] :
    SmoothOfRelativeDimension n f := by
  have : Smooth (p ≫ f) := SmoothOfRelativeDimension.smooth n (p ≫ f)
  have : LocallyOfFinitePresentation f :=
    locallyOfFinitePresentation_of_comp_of_etale_of_surjective p f
  have : Smooth f := Smooth.of_comp_surjective p f
  refine (smoothOfRelativeDimension_iff_smooth_and_pureRelativeDimension f).mpr ⟨‹_›, ?_⟩
  -- Check pure relative dimension fibrewise over `Y` by reducing to the field case.
  have hfib (y : Y) : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) := by
    let g := Y.fromSpecResidueField y
    let q : pullback p (pullback.fst f g) ⟶ pullback f g := pullback.snd p (pullback.fst f g)
    have : Etale q :=
      MorphismProperty.of_isPullback (P := @Etale) (IsPullback.of_hasPullback _ _) ‹_›
    have : Surjective q :=
      MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback _ _) ‹_›
    have : Smooth (pullback.snd f g) :=
      MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f g) ‹_›
    have : SmoothOfRelativeDimension n (pullback.snd (p ≫ f) g) :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n)
        (IsPullback.of_hasPullback (p ≫ f) g) ‹_›
    have hcomp : q ≫ pullback.snd f g =
        (pullbackRightPullbackFstIso f g p).hom ≫ pullback.snd (p ≫ f) g :=
      (pullbackRightPullbackFstIso f g p).inv_comp_eq.mp (by simp [q])
    have : SmoothOfRelativeDimension n (q ≫ pullback.snd f g) := by
      have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension.{u} n) :=
        MorphismProperty.IsStableUnderBaseChange.respectsIso
      rw [hcomp]
      exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n)
        (pullbackRightPullbackFstIso f g p).hom _).mpr inferInstance
    exact of_comp_of_etale_of_surjective_field (k := Y.residueField y) q (pullback.snd f g)
  have hpure (y : Y) : PureRelativeDimension n (f.fiberToSpecResidueField y) :=
    let := hfib y
    inferInstance
  refine (pureRelativeDimension_iff_relativeDimensionLE_and_isPureDimensional_fiber f).mpr
    ⟨⟨fun y ↦ ?_⟩, fun y ↦ ((pureRelativeDimension_iff_of_field _).mp (hpure y)).2⟩
  exact (relativeDimensionLE_iff_of_field _).mp (hpure y).toRelativeDimensionLE

/-- For an étale surjective morphism `p : X' ⟶ X` and any morphism `f : X ⟶ Y`, the composite
`p ≫ f` is smooth of relative dimension `n` if and only if `f` is. -/
theorem Scheme.Hom.smoothOfRelativeDimension_comp_iff_of_etale_of_surjective {X X' Y : Scheme.{u}}
    {n : ℕ} (p : X' ⟶ X) [Etale p] [Surjective p] (f : X ⟶ Y) :
    SmoothOfRelativeDimension n (p ≫ f) ↔ SmoothOfRelativeDimension n f :=
  ⟨fun _ ↦ SmoothOfRelativeDimension.of_comp_of_etale_of_surjective p f,
    fun h ↦ by
      have := SmoothOfRelativeDimension.smooth n f
      exact Nat.zero_add n ▸ (inferInstance : SmoothOfRelativeDimension (0 + n) (p ≫ f))⟩

end SmoothOfRelativeDimension

end AlgebraicGeometry
