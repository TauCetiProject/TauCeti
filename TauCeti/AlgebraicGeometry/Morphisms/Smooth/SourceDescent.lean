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
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Stalk
import TauCeti.AlgebraicGeometry.Morphisms.FinitePresentation
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Regular.Descent
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
  obtain ⟨I₀, hI₀⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    (Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)))ᶜ).mp
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := A₀) (S := B₀)).isOpen_range.isClosed_compl
  have : Module.FaithfullyFlat A (A ⊗[A₀] B₀) :=
    .of_linearEquiv A B e.symm.toLinearEquiv
  have htop : I₀.map (algebraMap A₀ A) = ⊤ :=
    (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I₀ hI₀).mp inferInstance
  have h1 : (1 : A) ∈ Ideal.span (algebraMap A₀ A '' (I₀ : Set A₀)) := by
    change (1 : A) ∈ I₀.map (algebraMap A₀ A)
    simp [htop]
  rw [Submodule.mem_span_set] at h1
  obtain ⟨c, hc_supp, hc_sum⟩ := h1
  let S₂ : Finset A := c.support.image c
  let A₁ : Subalgebra R A := Algebra.adjoin R (↑(G₀ ∪ S₁ ∪ S₂) : Set A)
  have hA₀A₁ : A₀ ≤ A₁ := by
    rw [← hG₀]
    exact Algebra.adjoin_mono (by intro z hz; simp [hz])
  let : Algebra A₀ A₁ := (Subalgebra.inclusion hA₀A₁).toAlgebra
  have : IsScalarTower A₀ A₁ A := .of_algebraMap_eq fun _ ↦ rfl
  have htop₁ : I₀.map (algebraMap A₀ A₁) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hmem : ∀ z ∈ c.support, ∃ i ∈ I₀, algebraMap A₀ A i = z := fun z hz ↦ by
      simpa using hc_supp hz
    choose i hi_mem hi_eq using hmem
    let sum₁ : A₁ := ∑ z ∈ c.support.attach,
      ⟨c z.val, Algebra.subset_adjoin (Finset.mem_coe.mpr
        (Finset.mem_union_right _ (Finset.mem_image_of_mem c z.property)))⟩ *
        algebraMap A₀ A₁ (i z.val z.property)
    have hsum₁_mem : sum₁ ∈ I₀.map (algebraMap A₀ A₁) :=
      Ideal.sum_mem _ fun z _ ↦
        Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hi_mem z.val z.property))
    have hsum₁_val : (sum₁ : A) = 1 := by
      change A₁.val sum₁ = 1
      simp only [sum₁, map_sum, map_mul]
      rw [← hc_sum, Finsupp.sum]
      refine (Finset.sum_congr rfl fun z _ ↦ ?_).trans
        (Finset.sum_attach c.support (fun z ↦ c z • z))
      change c z.val * (algebraMap A₀ A (i z.val z.property)) = c z.val • z.val
      simp [hi_eq z.val z.property, smul_eq_mul]
    have : sum₁ = 1 := Subtype.val_injective hsum₁_val
    exact this ▸ hsum₁_mem
  have : Module.FaithfullyFlat A₁ (A₁ ⊗[A₀] B₀) :=
    (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I₀ hI₀).mpr htop₁
  let B₁ := A₁ ⊗[A₀] B₀
  let gAlg : B₁ →ₐ[R] B :=
    ((e.symm.restrictScalars R).toAlgHom).comp
      ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom A₀ A₁ A) (.id A₀ B₀)).restrictScalars R)
  have hg_surj : Function.Surjective gAlg := by
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    intro b hb
    let x : s := ⟨b, hb⟩
    have ha_mem : ∀ j : Fin (k x), a x j ∈ (↑(G₀ ∪ S₁ ∪ S₂) : Set A) := fun j ↦ by
      refine Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
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
  exact ⟨⟨G₀ ∪ S₁ ∪ S₂, by simpa [A₁] using htop_sub⟩⟩

private theorem exists_etale_pushout_quotient {A₀ B : Type u} [CommRing A₀] [CommRing B]
    (J : Ideal A₀) (ψ : (A₀ ⧸ J) →+* B) (hψ : ψ.Etale) :
    ∃ (J' : { J' : Ideal A₀ // J' ≤ J ∧ J'.FG }) (T' : CommRingCat.{u})
      (f' : CommRingCat.of (A₀ ⧸ J'.val) ⟶ T') (g' : T' ⟶ CommRingCat.of B),
      IsPushout (CommRingCat.ofHom (Ideal.Quotient.factor J'.property.1)) f'
        (CommRingCat.ofHom ψ) g' ∧ f'.hom.Etale := by
  let ι := { J' : Ideal A₀ // J' ≤ J ∧ J'.FG }
  let : Preorder ι := Preorder.lift Subtype.val
  have : Nonempty ι := ⟨⟨⊥, bot_le, Submodule.fg_bot⟩⟩
  have : IsDirectedOrder ι := ⟨fun J₁ J₂ ↦
    ⟨⟨J₁.val ⊔ J₂.val, sup_le J₁.property.1 J₂.property.1,
      Submodule.FG.sup J₁.property.2 J₂.property.2⟩,
      (le_sup_left : J₁.val ≤ J₁.val ⊔ J₂.val),
      (le_sup_right : J₂.val ≤ J₁.val ⊔ J₂.val)⟩⟩
  let D : ι ⥤ CommRingCat.{u} :=
    { obj J' := CommRingCat.of (A₀ ⧸ J'.val)
      map h := CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom h)) }
  let c : Cocone D :=
    { pt := CommRingCat.of (A₀ ⧸ J)
      ι :=
        { app J' := CommRingCat.ofHom (Ideal.Quotient.factor J'.property.1)
          naturality _ J₂ h := CommRingCat.hom_ext
            (Ideal.Quotient.factor_comp (leOfHom h) J₂.property.1) } }
  let botι : ι := ⟨⊥, bot_le, Submodule.fg_bot⟩
  let hc : IsColimit c :=
    { desc s :=
        let base : A₀ →+* s.pt := (s.ι.app botι).hom.comp (Ideal.Quotient.mk ⊥)
        CommRingCat.ofHom <| Ideal.Quotient.lift J base fun x hx ↦ by
          let Jx : ι := ⟨Ideal.span {x}, Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx),
            Submodule.fg_span (Set.finite_singleton x)⟩
          have hle : botι ≤ Jx := (bot_le : (⊥ : Ideal A₀) ≤ Jx.val)
          have hw := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (s.w (homOfLE hle)))
            (Ideal.Quotient.mk ⊥ x)
          change (s.ι.app Jx).hom (Ideal.Quotient.factor hle (Ideal.Quotient.mk ⊥ x)) = base x
            at hw
          rw [Ideal.Quotient.factor_mk,
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl), map_zero] at hw
          exact hw.symm
      fac s J' := by
        refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
        have hle : botι ≤ J' := (bot_le : (⊥ : Ideal A₀) ≤ J'.val)
        have hw := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (s.w (homOfLE hle)))
          (Ideal.Quotient.mk ⊥ x)
        change (s.ι.app J').hom (Ideal.Quotient.factor hle (Ideal.Quotient.mk ⊥ x)) =
          (s.ι.app botι).hom (Ideal.Quotient.mk ⊥ x) at hw
        rw [Ideal.Quotient.factor_mk] at hw
        exact hw.symm
      uniq s m hm := by
        refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_))
        have hw := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hm botι))
          (Ideal.Quotient.mk ⊥ x)
        change m.hom (Ideal.Quotient.factor botι.property.1 (Ideal.Quotient.mk ⊥ x)) =
          (s.ι.app botι).hom (Ideal.Quotient.mk ⊥ x) at hw
        rw [Ideal.Quotient.factor_mk] at hw
        exact hw }
  obtain ⟨J', T', f', g', hpush, hf'⟩ :=
    RingHom.Etale.preIndSpreads.exists_isPushout hc (CommRingCat.ofHom ψ) hψ
  exact ⟨J', T', f', g', hpush, hf'⟩

open scoped TensorProduct in
private theorem fg_ker_of_etale_faithfullyFlat {R A' A'' Q B' B : Type u} [CommRing R] [CommRing A']
    [CommRing A''] [CommRing Q] [CommRing B'] [CommRing B] [Algebra R A'] [Algebra R A'']
    [Algebra R Q] [Algebra R B] [Algebra A' A''] [Algebra A' Q] [Algebra A'' Q]
    [Algebra A' B'] [Algebra Q B] [IsScalarTower R A' A'']
    [IsScalarTower R A'' Q] [IsScalarTower A' A'' Q]
    [IsScalarTower R Q B] (ePush : Q ⊗[A'] B' ≃ₐ[Q] B)
    (hsurj : Function.Surjective (algebraMap A'' Q)) [Algebra.Etale A' B']
    [Module.FaithfullyFlat A'' (A'' ⊗[A'] B')] [Algebra.FinitePresentation R A'']
    [Algebra.FinitePresentation R B] : (RingHom.ker (algebraMap A'' Q)).FG := by
  let B'' := A'' ⊗[A'] B'
  have : Algebra.Etale A'' B'' := inferInstance
  have : Algebra.FinitePresentation R B'' := .trans R A'' B''
  let f : A'' →ₐ[A''] Q := Algebra.ofId A'' Q
  let K : Ideal A'' := RingHom.ker f.toRingHom
  let eK : (A'' ⧸ K) ≃ₐ[A''] Q := Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj
  let eB''KAlg : (B'' ⧸ K.map (algebraMap A'' B'')) ≃ₐ[B''] B'' ⊗[A''] Q :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B'' K).trans
      (Algebra.TensorProduct.congr .refl eK)
  let eB''K : (B'' ⧸ K.map (algebraMap A'' B'')) ≃+* B'' ⊗[A''] Q := eB''KAlg.toRingEquiv
  let eB''J : B'' ⊗[A''] Q ≃+* B :=
    (Algebra.TensorProduct.comm A'' B'' Q).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange A' A'' Q Q B').toRingEquiv.trans ePush.toRingEquiv)
  let ψHom : B'' →+* B :=
    (eB''J.toRingHom.comp eB''K.toRingHom).comp (Ideal.Quotient.mk (K.map (algebraMap A'' B'')))
  let ψ : B'' →ₐ[R] B :=
    { __ := ψHom
      commutes' r := by
        change eB''J (eB''KAlg (algebraMap B'' _ (algebraMap R B'' r))) = algebraMap R B r
        rw [eB''KAlg.commutes]
        have hr : algebraMap B'' (B'' ⊗[A''] Q) (algebraMap R B'' r) =
            ((algebraMap R A'' r) ⊗ₜ[A'] (1 : B')) ⊗ₜ[A''] (1 : Q) := rfl
        rw [hr]
        simp only [eB''J, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
          Algebra.TensorProduct.comm_tmul]
        have hcan :
            Algebra.TensorProduct.cancelBaseChange A' A'' Q Q B'
                ((1 : Q) ⊗ₜ[A''] ((algebraMap R A'' r) ⊗ₜ[A'] (1 : B'))) =
              ((algebraMap R A'' r) • (1 : Q)) ⊗ₜ[A'] (1 : B') :=
          Algebra.TensorProduct.cancelBaseChange_tmul A' A'' Q Q B' (1 : Q) (algebraMap R A'' r) 1
        rw [hcan, Algebra.smul_def, mul_one]
        change ePush ((algebraMap A'' Q (algebraMap R A'' r)) ⊗ₜ[A'] (1 : B')) = algebraMap R B r
        rw [← IsScalarTower.algebraMap_apply R A'' Q]
        change ePush (algebraMap Q (Q ⊗[A'] B') (algebraMap R Q r)) = algebraMap R B r
        rw [ePush.commutes, ← IsScalarTower.algebraMap_apply R Q B] }
  have hψ_surj : Function.Surjective ψ :=
    eB''J.surjective.comp (eB''K.surjective.comp Ideal.Quotient.mk_surjective)
  have hkerFG : (RingHom.ker ψ.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective ψ hψ_surj
  have hker_eq : RingHom.ker ψ.toRingHom = K.map (algebraMap A'' B'') := by
    ext b
    change eB''J (eB''K (Ideal.Quotient.mk (K.map (algebraMap A'' B'')) b)) = 0 ↔
      b ∈ K.map (algebraMap A'' B'')
    rw [eB''J.map_eq_zero_iff, eB''K.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
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
  obtain ⟨J', T', f', g', hpush, hf'⟩ := exists_etale_pushout_quotient J ψJ hψJ
  let A' := A₀ ⧸ J'.val
  let B' : Type u := T'
  let : Algebra A' B' := f'.hom.toAlgebra
  let : Algebra A' (A₀ ⧸ J) := (Ideal.Quotient.factor J'.property.1).toAlgebra
  let : Algebra (A₀ ⧸ J) B := ψJ.toAlgebra
  let : Algebra A' B := (ψJ.comp (Ideal.Quotient.factor J'.property.1)).toAlgebra
  have : IsScalarTower A' (A₀ ⧸ J) B := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (A₀ ⧸ J) B := ⟨fun r x y ↦ by
    rw [Algebra.smul_def r x, Algebra.smul_def _ y, Algebra.smul_def r (x • y),
      Algebra.smul_def x y]
    change ψJ (algebraMap R (A₀ ⧸ J) r * x) * y = algebraMap R B r * (ψJ x * y)
    rw [map_mul, ← mul_assoc]
    congr 2
    change algebraMap A B (eA (algebraMap R (A₀ ⧸ J) r)) = algebraMap R B r
    rw [eA.commutes, ← IsScalarTower.algebraMap_apply R A B]⟩
  have : Algebra.Etale A' B' := hf'
  have : Module.FaithfullyFlat (A₀ ⧸ J) B := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    change ((algebraMap A B).comp eA.toRingHom).FaithfullyFlat
    exact RingHom.FaithfullyFlat.comp
      (RingHom.FaithfullyFlat.of_bijective eA.bijective)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let eIso := (CommRingCat.isPushout_tensorProduct A' (A₀ ⧸ J) B').isoPushout ≪≫
    hpush.isoPushout.symm
  let ePush : (A₀ ⧸ J) ⊗[A'] B' ≃ₐ[A₀ ⧸ J] B :=
    { __ := eIso.commRingCatIsoToRingEquiv
      commutes' x := by
        have h1 : (CommRingCat.isPushout_tensorProduct A' (A₀ ⧸ J) B').isoPushout.hom
            (x ⊗ₜ 1) = (pushout.inl (CommRingCat.ofHom (algebraMap A' (A₀ ⧸ J)))
              (CommRingCat.ofHom (algebraMap A' B'))) x :=
          congr($((CommRingCat.isPushout_tensorProduct A' (A₀ ⧸ J) B').inl_isoPushout_hom).hom x)
        have h2 (y : A₀ ⧸ J) := congr($hpush.inl_isoPushout_inv y)
        dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          CommRingCat.hom_ofHom] at h2
        change hpush.isoPushout.inv.hom
          (((CommRingCat.isPushout_tensorProduct A' (A₀ ⧸ J) B').isoPushout.hom).hom
            (x ⊗ₜ[A'] 1)) = ψJ x
        rw [h1]
        exact h2 x }
  obtain ⟨I₀, hI₀⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    (Set.range (PrimeSpectrum.comap (algebraMap A' B')))ᶜ).mp
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := A') (S := B')).isOpen_range.isClosed_compl
  have : Module.FaithfullyFlat (A₀ ⧸ J) ((A₀ ⧸ J) ⊗[A'] B') :=
    .of_linearEquiv (A₀ ⧸ J) B ePush.toLinearEquiv
  have htop : I₀.map (algebraMap A' (A₀ ⧸ J)) = ⊤ :=
    (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I₀ hI₀).mp inferInstance
  have h1 : (1 : A₀ ⧸ J) ∈ I₀.map (algebraMap A' (A₀ ⧸ J)) := by simp [htop]
  obtain ⟨x, hxI₀, hx1⟩ :=
    (Ideal.mem_map_iff_of_surjective (algebraMap A' (A₀ ⧸ J))
      (Ideal.Quotient.factor_surjective J'.property.1)).mp h1
  obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1x₀ : 1 - x₀ ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    have hmk : Ideal.Quotient.mk J x₀ =
        algebraMap A' (A₀ ⧸ J) (Ideal.Quotient.mk J'.val x₀) := rfl
    rw [hmk, hx1, sub_self]
  let J'' : Ideal A₀ := J'.val ⊔ Ideal.span {1 - x₀}
  have hJ'J'' : J'.val ≤ J'' := le_sup_left
  have hJ''J : J'' ≤ J :=
    sup_le J'.property.1 (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h1x₀))
  have hJ''FG : J''.FG :=
    Submodule.FG.sup J'.property.2 (Submodule.fg_span (Set.finite_singleton _))
  let A'' := A₀ ⧸ J''
  let : Algebra A' A'' := (Ideal.Quotient.factor hJ'J'').toAlgebra
  let : Algebra A'' (A₀ ⧸ J) := (Ideal.Quotient.factor hJ''J).toAlgebra
  let : Algebra R B' := Algebra.compHom B' (algebraMap R A')
  have : IsScalarTower A' A'' (A₀ ⧸ J) := ⟨fun x y z ↦ by
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      mul_assoc]
    rfl⟩
  have : IsScalarTower R A' B' := ⟨fun r x y ↦ by
    rw [Algebra.smul_def r x, Algebra.smul_def _ y, Algebra.smul_def r (x • y),
      Algebra.smul_def x y, map_mul, mul_assoc]
    rfl⟩
  have : IsScalarTower R A' A'' := ⟨fun r x y ↦ by
    rw [Algebra.smul_def r x, Algebra.smul_def _ y, Algebra.smul_def r (x • y),
      Algebra.smul_def x y, map_mul, mul_assoc]
    rfl⟩
  have : IsScalarTower R A'' (A₀ ⧸ J) := ⟨fun r x y ↦ by
    rw [Algebra.smul_def r x, Algebra.smul_def _ y, Algebra.smul_def r (x • y),
      Algebra.smul_def x y, map_mul, mul_assoc]
    rfl⟩
  have : IsScalarTower R A' (A₀ ⧸ J) := ⟨fun r x y ↦ by
    rw [Algebra.smul_def r x, Algebra.smul_def _ y, Algebra.smul_def r (x • y),
      Algebra.smul_def x y, map_mul, mul_assoc]
    rfl⟩
  have htop'' : I₀.map (algebraMap A' A'') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have hmem : algebraMap A' A'' (Ideal.Quotient.mk J'.val x₀) = 1 := by
      have hsub : Ideal.Quotient.mk J'' (1 - x₀) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span rfl))
      rw [map_sub, map_one, sub_eq_zero] at hsub
      exact hsub.symm
    exact hmem ▸ Ideal.mem_map_of_mem _ hxI₀
  have : Module.FaithfullyFlat A'' (A'' ⊗[A'] B') :=
    (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I₀ hI₀).mpr htop''
  have : Algebra.FinitePresentation R A₀ := inferInstance
  have : Algebra.FinitePresentation R A'' := .quotient hJ''FG
  let K : Ideal A'' := RingHom.ker (Ideal.Quotient.factor hJ''J)
  have hKFG : K.FG :=
    fg_ker_of_etale_faithfullyFlat (R := R) ePush (Ideal.Quotient.factor_surjective hJ''J)
  have hJFG : J.FG := by
    have hcomp := Ideal.fg_ker_comp (Ideal.Quotient.mk J'') (Ideal.Quotient.factor hJ''J)
      (by simpa [Ideal.mk_ker] using hJ''FG) hKFG Ideal.Quotient.mk_surjective
    simpa [Ideal.Quotient.factor_comp_mk, Ideal.mk_ker] using hcomp
  have : Algebra.FinitePresentation R (A₀ ⧸ J) := .quotient hJFG
  exact .equiv eA

-- Local finite presentation descends along étale surjections on the source.
private theorem locallyOfFinitePresentation_of_comp_of_etale_of_surjective {X' X Y : Scheme.{u}}
    (p : X' ⟶ X) (f : X ⟶ Y) [Etale p] [Surjective p]
    [LocallyOfFinitePresentation (p ≫ f)] : LocallyOfFinitePresentation f := by
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have hloc (x : X) :
      ∃ (W : X.Opens), x ∈ W ∧ LocallyOfFinitePresentation (W.ι ≫ f) := by
    obtain ⟨(U : Y.Opens), hU, hxU, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top (f x))
    obtain ⟨(W : X.Opens), hW, hxW, hWU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := f ⁻¹ᵁ U) hxU
    have : IsAffine U.toScheme := hU
    have : IsAffine W.toScheme := hW
    let pW : (p ⁻¹ᵁ W).toScheme ⟶ W.toScheme := p ∣_ W
    have : Etale pW := inferInstanceAs (Etale (p ∣_ W))
    have : Surjective pW :=
      MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict p W).flip
        inferInstance
    obtain ⟨V : (p ⁻¹ᵁ W).toScheme.Opens, hV, hVim⟩ :=
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
    let q : Z ⟶ W.toScheme := s ≫ V.ι ≫ pW
    have : Etale q := by
      have : Etale (V.ι ≫ pW) := IsZariskiLocalAtSource.comp (P := @Etale.{u}) inferInstance _
      exact inferInstance
    have : Surjective q := ⟨fun w ↦ by
      obtain ⟨v, hv⟩ := hVpW_surj.surj w
      obtain ⟨z, hz⟩ := hs_surj.surj v
      refine ⟨z, ?_⟩
      change (V.ι ≫ pW) (s z) = w
      rw [hz, hv]⟩
    have hqcomp : q ≫ f.resLE U W hWU ≫ U.ι = (s ≫ V.ι ≫ (p ⁻¹ᵁ W).ι) ≫ (p ≫ f) := by
      simp only [q, pW, Category.assoc, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι_assoc]
    have : LocallyOfFinitePresentation (q ≫ f.resLE U W hWU) := by
      refine locallyOfFinitePresentation_of_comp (q ≫ f.resLE U W hWU) U.ι (hfg := ?_)
      rw [Category.assoc, hqcomp]
      have : LocallyOfFinitePresentation (s ≫ V.ι ≫ (p ⁻¹ᵁ W).ι) := inferInstance
      exact MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ this inferInstance
    algebraize [(f.resLE U W hWU).appTop.hom, q.appTop.hom,
      q.appTop.hom.comp (f.resLE U W hWU).appTop.hom]
    have : Algebra.Etale Γ(W.toScheme, ⊤) Γ(Z, ⊤) := by
      change q.appTop.hom.Etale
      exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
    have : Module.FaithfullyFlat Γ(W.toScheme, ⊤) Γ(Z, ⊤) :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨inferInstance, inferInstance⟩
    have : Algebra.FinitePresentation Γ(U.toScheme, ⊤) Γ(Z, ⊤) := by
      change (q.appTop.hom.comp (f.resLE U W hWU).appTop.hom).FinitePresentation
      rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
      exact Scheme.Hom.finitePresentation_appTop (q ≫ f.resLE U W hWU)
    have hFP : (f.resLE U W hWU).appTop.hom.FinitePresentation :=
      finitePresentation_of_comp_etale_faithfullyFlat
        (R := Γ(U.toScheme, ⊤)) (A := Γ(W.toScheme, ⊤)) (B := Γ(Z, ⊤))
    have : LocallyOfFinitePresentation (f.resLE U W hWU) :=
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr hFP
    refine ⟨W, hxW, ?_⟩
    rw [← f.resLE_comp_ι (e := hWU)]
    exact MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ this inferInstance
  choose W hxW hW using hloc
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top W (P := @LocallyOfFinitePresentation)]
  · exact hW
  · rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩

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
      rw [hcomp]
      exact Nat.zero_add n ▸
        (inferInstance : SmoothOfRelativeDimension (0 + n)
          ((pullbackRightPullbackFstIso f g p).hom ≫ pullback.snd (p ≫ f) g))
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
