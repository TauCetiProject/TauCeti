/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import TauCeti.RingTheory.LocalRing.Quotient
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.Scheme.SectionsBaseChange
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Comma.Over.Pullback
import TauCeti.RingTheory.FormalGlueing.Reconstruction

/-!
# Extending finite morphisms from the completion across the closed point

Let `A → A'` be a flat homomorphism of local rings, with `𝔪_A` finitely generated, that induces a
bijection `A ⧸ 𝔪_A → A' ⧸ 𝔪_A A'` (for instance, the `𝔪_A`-adic completion `Â` of a Noetherian
local ring `A`). Then `𝔪_A A' = 𝔪_{A'}`
(`TauCeti.IsLocalRing.map_maximalIdeal_of_bijective_quotientMap`), so `A → A'` is faithfully flat
and the punctured spectrum `U'` of `A'` is the preimage of the punctured spectrum `U` of `A`.

Suppose `V ⟶ U` is a finite morphism whose base change `V' = V ×_U U'` to `U'` extends to a finite
morphism `Y' ⟶ Spec A'`. This file proves that `V` extends to a finite morphism `Y ⟶ Spec A` whose
base change to `Spec A'` is `Y'` and whose restriction to `U` is `V`, compatibly with the given
identification over `U'`.

The proof passes to global sections and applies subalgebra formal gluing
(`TauCeti.exists_subalgebra_isPushout_of_formalGlueing`) along `A → A'` and a finite generating set
`G` of `𝔪_A`:

* Flat base change (`TauCeti.IsLocalRing.isPushout_appTop_pullback_puncturedSpectrum_of_flat`)
  identifies `Γ(V', ⊤)` with `A' ⊗[A] Γ(V, ⊤)`.
* Because `Y' ⟶ Spec A'` is finite over an affine base, `Y'` is affine, and for every `x ∈ G` the
  basic open `D(x)` on `Spec A'` lies in `U'`. Restricting the open immersion `V' ⟶ Y'` over the
  corresponding basic open of `Y'` gives an isomorphism of principal localizations, so
  `Γ(Y', ⊤) → Γ(V', ⊤)` becomes bijective after inverting the image of each `x ∈ G`.
* Formal gluing produces an `A`-subalgebra `B ≤ Γ(Y', ⊤)` with `A' ⊗[A] B ≃ₐ[A'] Γ(Y', ⊤)` and an
  `A`-algebra map `B →ₐ[A] Γ(V, ⊤)` compatible with `Γ(Y', ⊤) → Γ(V', ⊤)`.
* Faithfully flat descent gives finiteness of `B` over `A`, so `Y = Spec B` is finite over `Spec A`,
  and fpqc descent of isomorphisms along `U' ⟶ U` shows that the induced comparison `V ⟶ Y ×_X U`
  is an isomorphism over `U`.

## Main declarations

* `TauCeti.IsLocalRing.overRestrictPuncturedCompPullbackIso`: restriction of schemes over `Spec A`
  to the punctured spectrum commutes with pullback along `Spec A' ⟶ Spec A`.
* `TauCeti.IsLocalRing.isPushout_appTop_pullback_puncturedSpectrum_of_flat`: flat base change for
  global sections of a qcqs morphism over the punctured spectrum.
* `TauCeti.IsLocalRing.finite_extend_of_bijective_quotientMap`: extending a finite morphism over
  the punctured spectrum of `A` from a finite extension over `Spec A'`, for any flat `A → A'`
  with `𝔪_A` finitely generated inducing `A ⧸ 𝔪_A ≅ A' ⧸ 𝔪_A A'`.
* `TauCeti.IsLocalRing.finite_extend_of_completion`: the case of the `𝔪_A`-adic completion `Â` of
  a Noetherian local ring `A` (Stacks, Lemma 58.19.3 (0BLH)).

## References

* [The Stacks Project, Lemma 58.19.3](https://stacks.math.columbia.edu/tag/0BLH).
* [The Stacks Project, Proposition 15.91.16](https://stacks.math.columbia.edu/tag/05ER).
* [The Stacks Project, Remark 15.91.20](https://stacks.math.columbia.edu/tag/05EU).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite IsLocalRing
open scoped TensorProduct

universe u

namespace TauCeti.IsLocalRing

section PullbackIso

variable {A A' : Type u} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A'] [Algebra A A']

/-- Restriction of schemes over `Spec A` to the punctured spectrum commutes with pullback along
`Spec A' ⟶ Spec A` whenever the closed point is the only point of `Spec A'` over the closed point
of `Spec A`. -/
def overRestrictPuncturedCompPullbackIso
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A') :
    Over.pullback (puncturedSpectrum A).ι ⋙
        Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
          (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≅
      Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⋙
        Over.pullback (puncturedSpectrum A').ι :=
  Over.pullbackCompIsoOfEq (Scheme.Hom.resLE_comp_ι _ (preimage_puncturedSpectrum h).ge)

/-- First-projection compatibility for the forward direction of
`overRestrictPuncturedCompPullbackIso`. -/
@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_hom_app_left_fst_fst
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).hom.app Y).left ≫
        pullback.fst (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (puncturedSpectrum A').ι ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
      pullback.fst (pullback.snd Y.hom (puncturedSpectrum A).ι)
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≫
        pullback.fst Y.hom (puncturedSpectrum A).ι :=
  Over.pullbackCompIsoOfEq_hom_app_left_fst_fst _ Y

/-- Second-projection compatibility for the forward direction of
`overRestrictPuncturedCompPullbackIso`. -/
@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_hom_app_left_snd
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).hom.app Y).left ≫
        pullback.snd (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (puncturedSpectrum A').ι =
      pullback.snd (pullback.snd Y.hom (puncturedSpectrum A).ι)
        ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
          (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) :=
  Over.pullbackCompIsoOfEq_hom_app_left_snd _ Y

/-- First-projection compatibility for the inverse direction of
`overRestrictPuncturedCompPullbackIso`. -/
@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_inv_app_left_fst_fst
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).inv.app Y).left ≫
        pullback.fst (pullback.snd Y.hom (puncturedSpectrum A).ι)
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≫
        pullback.fst Y.hom (puncturedSpectrum A).ι =
      pullback.fst (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (puncturedSpectrum A').ι ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
  Over.pullbackCompIsoOfEq_inv_app_left_fst_fst _ Y

/-- Second-projection compatibility for the inverse direction of
`overRestrictPuncturedCompPullbackIso`. -/
@[reassoc (attr := simp)]
theorem overRestrictPuncturedCompPullbackIso_inv_app_left_snd
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (Y : Over (Spec (.of A))) :
    ((overRestrictPuncturedCompPullbackIso h).inv.app Y).left ≫
        pullback.snd (pullback.snd Y.hom (puncturedSpectrum A).ι)
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) =
      pullback.snd (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
        (puncturedSpectrum A').ι :=
  Over.pullbackCompIsoOfEq_inv_app_left_snd _ Y

end PullbackIso

section Extend

variable {A A' : Type u} [CommRing A] [IsLocalRing A]
  [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A']

/-- **Flat base change for the global sections of a quasi-compact quasi-separated morphism over the
punctured spectrum.** Let `A → A'` be a flat homomorphism of local rings, with `𝔪_A` finitely
generated, such that the closed point is the only point of `Spec A'` over the closed point of
`Spec A`. For a quasi-compact quasi-separated morphism `V ⟶ U` over the punctured spectrum `U` of
`A`, with base change `V'` to the punctured spectrum `U'` of `A'`, the square of global sections
exhibits `Γ(V', ⊤)` as `A' ⊗[A] Γ(V, ⊤)`. -/
theorem isPushout_appTop_pullback_puncturedSpectrum_of_flat
    (hfg : (maximalIdeal A).FG)
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (V : Over (puncturedSpectrum A).toScheme) [QuasiCompact V.hom] [QuasiSeparated V.hom] :
    IsPushout ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.hom ≫ (puncturedSpectrum A).ι).appTop)
      (CommRingCat.ofHom (algebraMap A A'))
      (pullback.fst V.hom ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge)).appTop
      ((Scheme.ΓSpecIso (.of A')).inv ≫ (pullback.snd V.hom
        ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE (puncturedSpectrum A)
          (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≫
        (puncturedSpectrum A').ι).appTop) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let U := puncturedSpectrum A
  let U' := puncturedSpectrum A'
  let r := f.resLE U U' (preimage_puncturedSpectrum h).ge
  have hU : IsPullback r U'.ι U.ι f :=
    f.isPullback_resLE_of_eq U (preimage_puncturedSpectrum h).symm
  let : V.left.Over (Spec (.of A)) := ⟨V.hom ≫ U.ι⟩
  let : (pullback V.hom r).Over (Spec (.of A')) := ⟨pullback.snd V.hom r ≫ U'.ι⟩
  have H : IsPullback (pullback.fst V.hom r) (pullback V.hom r ↘ Spec (.of A'))
      (V.left ↘ Spec (.of A)) f :=
    (IsPullback.of_hasPullback V.hom r).paste_vert hU
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    (isCompact_puncturedSpectrum_of_fg_maximalIdeal A hfg)
  have : CompactSpace V.left := QuasiCompact.compactSpace_of_compactSpace V.hom
  have : QuasiSeparatedSpace V.left := quasiSeparatedSpace_of_quasiSeparated (V.hom ≫ U.ι)
  have hpush := TauCeti.AlgebraicGeometry.isPushout_baseRingToStructurePresheaf_app_of_flat H
    (W := ⊤) isCompact_univ isQuasiSeparated_univ (W' := ⊤) rfl
  rwa [Scheme.baseRingToStructurePresheaf_app_eq_appLE,
    Scheme.baseRingToStructurePresheaf_app_eq_appLE,
    Scheme.Hom.appLE_top_top, Scheme.Hom.appLE_top_top, Scheme.Hom.appLE_top_top] at hpush

omit [Module.Flat A A'] in
/-- Away from any element `s ∈ 𝔪_{A'}`, the open immersion `V' ⟶ Y'` induced by an identification
`e'` of `Y' ×_{Spec A'} U'` with `V ×_U U'` contains `Y'.basicOpen s` in its range, so the induced
`A'`-algebra map on global sections becomes bijective after inverting `s`. -/
private theorem bijective_localizedModuleMap_pullback_puncturedSpectrum
    (hfg : (maximalIdeal A).FG)
    (hmap : (maximalIdeal A).map (algebraMap A A') = maximalIdeal A')
    (hrad : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (V : Over (puncturedSpectrum A).toScheme) [QuasiCompact V.hom] [QuasiSeparated V.hom]
    (Y' : Over (Spec (.of A'))) [CompactSpace Y'.left] [QuasiSeparatedSpace Y'.left]
    (e' : (Over.pullback (puncturedSpectrum A').ι).obj Y' ≅
      (Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A')
        (preimage_puncturedSpectrum hrad).ge)).obj V)
    [Algebra A' Γ(Y'.left, ⊤)]
    (hY' : algebraMap A' Γ(Y'.left, ⊤) = ((Scheme.ΓSpecIso (.of A')).inv ≫ Y'.hom.appTop).hom)
    [Algebra A' Γ(pullback V.hom ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
      (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum hrad).ge), ⊤)]
    (g_alg : Γ(Y'.left, ⊤) →ₐ[A'] Γ(pullback V.hom
      ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum hrad).ge), ⊤))
    (hg : g_alg.toRingHom =
      (e'.inv.left ≫ pullback.fst Y'.hom (puncturedSpectrum A').ι).appTop.hom)
    {s : A'} (hs : s ∈ maximalIdeal A') :
    Function.Bijective (LocalizedModule.map (.powers s) g_alg.toLinearMap) := by
  let U' := puncturedSpectrum A'
  let r := (Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
    (puncturedSpectrum A) U' (preimage_puncturedSpectrum hrad).ge
  let V' : Scheme.{u} := pullback V.hom r
  let π' : V' ⟶ U'.toScheme := pullback.snd V.hom r
  have : CompactSpace U'.toScheme := isCompact_iff_compactSpace.mp
    (isCompact_puncturedSpectrum_of_fg_maximalIdeal A' (hmap ▸ hfg.map (algebraMap A A')))
  have : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace π'
  have : QuasiSeparatedSpace V' := quasiSeparatedSpace_of_quasiSeparated (π' ≫ U'.ι)
  let j' : V' ⟶ Y'.left := e'.inv.left ≫ pullback.fst Y'.hom U'.ι
  have : IsOpenImmersion j' := inferInstance
  have hrange : Y'.left.basicOpen (algebraMap A' Γ(Y'.left, ⊤) s) ≤ j'.opensRange := by
    let D : (Spec (.of A')).Opens := PrimeSpectrum.basicOpen s
    have h1 : Y'.left.basicOpen (algebraMap A' Γ(Y'.left, ⊤) s) = Y'.hom ⁻¹ᵁ D := by
      rw [hY', CommRingCat.hom_comp, RingHom.comp_apply, ← Scheme.preimage_basicOpen_top,
        basicOpen_eq_of_affine]
    rw [h1]
    intro y hy
    have hyD : Y'.hom y ∈ PrimeSpectrum.basicOpen s :=
      (Scheme.Hom.mem_preimage (f := Y'.hom) (U := D) (x := y)).mp hy
    have hyU' : Y'.hom y ∈ U' :=
      (mem_puncturedSpectrum_iff A' _).mpr fun hclosed ↦ hyD (hclosed ▸ hs)
    obtain ⟨w, hw1, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y'.hom) (g := U'.ι) y
      ⟨Y'.hom y, hyU'⟩ rfl
    refine ⟨e'.hom.left w, ?_⟩
    dsimp only [j']
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e'.hom.left e'.inv.left,
      ← Over.comp_left, e'.hom_inv_id, Over.id_left]
    simpa using hw1
  exact j'.bijective_localizedModuleMap_of_basicOpen_le_opensRange g_alg hg s hrange

/-- Global-sections reconstruction step for `finite_extend_of_bijective_quotientMap`: produces a
module-finite `A`-algebra `B`, ring homomorphisms `b'Hom : B →+* Γ(Y'.left, ⊤)` and
`ψ : B →+* Γ(V.left, ⊤)`, and a base-change isomorphism `Spec B ×_{Spec A} Spec A' ≅ Y'` over
`Spec A'` compatible with `b'Hom` and `ψ`. -/
private theorem exists_finite_algebra_of_bijective_quotientMap
    (hfg : (maximalIdeal A).FG)
    (hquot : Function.Bijective (Ideal.quotientMap ((maximalIdeal A).map (algebraMap A A'))
      (algebraMap A A') Ideal.le_comap_map))
    (V : Over (puncturedSpectrum A).toScheme) [IsFinite V.hom]
    (Y' : Over (Spec (.of A'))) [IsFinite Y'.hom]
    (e' : (Over.pullback (puncturedSpectrum A').ι).obj Y' ≅
      (Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A')
        (preimage_puncturedSpectrum
          (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).obj V) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
      (b'Hom : B →+* Γ(Y'.left, ⊤)) (ψ : B →+* Γ(V.left, ⊤))
      (eSpec : Over.mk (pullback.snd (Spec.algebraMap A B)
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ≅ Y'),
      ψ.comp (algebraMap A B) =
          ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.hom ≫ (puncturedSpectrum A).ι).appTop).hom ∧
        ((pullback.fst V.hom
          ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
            (puncturedSpectrum A) (puncturedSpectrum A')
            (preimage_puncturedSpectrum
              (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).appTop.hom).comp ψ =
          ((e'.inv.left ≫ pullback.fst Y'.hom (puncturedSpectrum A').ι).appTop.hom).comp b'Hom ∧
        eSpec.inv.left ≫ pullback.fst (Spec.algebraMap A B)
            (Spec.map (CommRingCat.ofHom (algebraMap A A'))) =
          Y'.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b'Hom) := by
  classical
  have hmap : (maximalIdeal A).map (algebraMap A A') = maximalIdeal A' :=
    map_maximalIdeal_of_bijective_quotientMap hquot
  have hrad : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A' :=
    radical_map_maximalIdeal_of_bijective_quotientMap hquot
  have : IsLocalHom (algebraMap A A') := isLocalHom_of_bijective_quotientMap hquot
  have : Module.FaithfullyFlat A A' := .of_flat_of_isLocalHom
  let U := puncturedSpectrum A
  let U' := puncturedSpectrum A'
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let r := f.resLE U U' (preimage_puncturedSpectrum hrad).ge
  let V' := pullback V.hom r
  let π' : V' ⟶ U'.toScheme := pullback.snd V.hom r
  have : IsAffine Y'.left := isAffine_of_isAffineHom Y'.hom
  -- Equip `Γ(V, ⊤)`, `Γ(V', ⊤)`, and `Γ(Y', ⊤)` with their canonical base-ring algebra structures.
  let aMapM : A →+* Γ(V.left, ⊤) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.hom ≫ U.ι).appTop).hom
  let aMapP : A' →+* Γ(V', ⊤) :=
    ((Scheme.ΓSpecIso (.of A')).inv ≫ (π' ≫ U'.ι).appTop).hom
  let aMapB' : A' →+* Γ(Y'.left, ⊤) :=
    ((Scheme.ΓSpecIso (.of A')).inv ≫ Y'.hom.appTop).hom
  algebraize [aMapM, aMapP, aMapP.comp (algebraMap A A'), aMapB', aMapB'.comp (algebraMap A A')]
  have : IsScalarTower A A' Γ(V', ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A A' Γ(Y'.left, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  -- Flat base change identifies `Γ(V', ⊤)` with `A' ⊗[A] Γ(V, ⊤)`.
  have hpush_V := isPushout_appTop_pullback_puncturedSpectrum_of_flat hfg hrad V
  let f_alg : Γ(V.left, ⊤) →ₐ[A] Γ(V', ⊤) :=
    { toRingHom := (pullback.fst V.hom r).appTop.hom
      commutes' a := by
        have hw := congrArg (fun φ ↦ φ.hom a) hpush_V.w
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hw
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact hw }
  have hf_bc : IsBaseChange A' f_alg.toLinearMap := by
    let : Algebra Γ(V.left, ⊤) Γ(V', ⊤) := f_alg.toRingHom.toAlgebra
    have : IsScalarTower A Γ(V.left, ⊤) Γ(V', ⊤) :=
      .of_algebraMap_eq fun a ↦ (f_alg.commutes a).symm
    have hpush_alg : Algebra.IsPushout A Γ(V.left, ⊤) A' Γ(V', ⊤) :=
      (CommRingCat.isPushout_iff_isPushout (R := A) (R' := Γ(V.left, ⊤))
        (S := A') (S' := Γ(V', ⊤))).mp hpush_V
    have htoAlg : IsScalarTower.toAlgHom A Γ(V.left, ⊤) Γ(V', ⊤) = f_alg := by
      ext x
      rw [IsScalarTower.toAlgHom_apply, RingHom.algebraMap_toAlgebra, AlgHom.coe_mk]
    exact htoAlg ▸ hpush_alg.symm.out
  -- Construct `g_alg : Γ(Y'.left, ⊤) →ₐ[A'] Γ(V', ⊤)` from the open immersion `j' : V' ⟶ Y'`.
  let j' : V' ⟶ Y'.left := e'.inv.left ≫ pullback.fst Y'.hom U'.ι
  have hj'_comm : j' ≫ Y'.hom = π' ≫ U'.ι := by
    have hw := Over.w e'.inv
    dsimp only [Over.pullback_obj_hom, Over.mk_hom] at hw
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw]
  have hcomm_app : ((Scheme.ΓSpecIso (.of A')).inv ≫ Y'.hom.appTop) ≫ j'.appTop =
      (Scheme.ΓSpecIso (.of A')).inv ≫ (π' ≫ U'.ι).appTop := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, hj'_comm]
  let g_alg : Γ(Y'.left, ⊤) →ₐ[A'] Γ(V', ⊤) :=
    { toRingHom := j'.appTop.hom
      commutes' a' := by
        have hw := congrArg (fun φ ↦ φ.hom a') hcomm_app
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hw
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact hw }
  have ⟨G, hG_span⟩ := hfg
  have hG_quot : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (G : Set A)).map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map) :=
    hG_span ▸ hquot
  have hg_loc (x : A) (hx : x ∈ G) :
      Function.Bijective (LocalizedModule.map (.powers (algebraMap A A' x)) g_alg.toLinearMap) :=
    bijective_localizedModuleMap_pullback_puncturedSpectrum hfg hmap hrad V Y' e' rfl g_alg rfl
      (hmap ▸ Ideal.mem_map_of_mem _ (hG_span ▸ Ideal.subset_span hx))
  -- Reconstruct the `A`-subalgebra `B ≤ Γ(Y', ⊤)` and descend finiteness from `Γ(Y', ⊤)` over `A'`.
  obtain ⟨B, ψ, hpush, hcomp, _⟩ :=
    TauCeti.exists_subalgebra_isPushout_of_formalGlueing hG_quot f_alg hf_bc g_alg hg_loc
  have : Module.Finite A' Γ(Y'.left, ⊤) := Y'.hom.moduleFinite_appTop rfl
  have : Module.Finite A' (A' ⊗[A] B) :=
    Module.Finite.equiv (Algebra.IsPushout.equiv A A' B Γ(Y'.left, ⊤)).symm.toLinearEquiv
  have hB_fin : Module.Finite A B := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A'
  obtain ⟨eSpec, heSpec_fst⟩ :=
    TauCeti.AlgebraicGeometry.exists_pullbackSpecIso_of_isPushout A B A' Y' rfl
  have hb' : algebraMap B Γ(Y'.left, ⊤) = B.val.toRingHom := by
    rw [B.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, AlgHom.toRingHom_eq_coe]
  have hcomp_ring : (pullback.fst V.hom r).appTop.hom.comp ψ.toRingHom =
      j'.appTop.hom.comp (algebraMap B Γ(Y'.left, ⊤)) := by
    rw [hb']
    exact congrArg AlgHom.toRingHom hcomp
  exact ⟨B, inferInstance, inferInstance, hB_fin, algebraMap B Γ(Y'.left, ⊤), ψ.toRingHom, eSpec,
    RingHom.ext ψ.commutes, hcomp_ring, heSpec_fst⟩

omit [Module.Flat A A'] in
/-- Over the punctured spectrum `U'` of `A'`, the base change of the comparison morphism
`Φ : V ⟶ (Spec B) ×_{Spec A} U` agrees with the inverse of the given identification `e'`,
transported along `eY'` and `overRestrictPuncturedCompPullbackIso`. -/
private theorem overPullback_map_homMk_lift_eq
    (hrad : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    {B : Type u} [CommRing B] [Algebra A B]
    (V : Over (puncturedSpectrum A).toScheme)
    (Y' : Over (Spec (.of A')))
    (b'Hom : B →+* Γ(Y'.left, ⊤)) (ψ : B →+* Γ(V.left, ⊤)) :
    let U := puncturedSpectrum A
    let U' := puncturedSpectrum A'
    let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
    let r := f.resLE U U' (preimage_puncturedSpectrum hrad).ge
    let q := Spec.algebraMap A B
    let Y : Over (Spec (.of A)) := Over.mk q
    let jV : V.left ⟶ Spec (.of B) := V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
    ∀ (e' : (Over.pullback U'.ι).obj Y' ≅ (Over.pullback r).obj V)
      (eY' : (Over.pullback f).obj Y ≅ Y')
      (hjV : jV ≫ q = V.hom ≫ U.ι),
      (pullback.fst V.hom r).appTop.hom.comp ψ =
        (e'.inv.left ≫ pullback.fst Y'.hom U'.ι).appTop.hom.comp b'Hom →
      eY'.inv.left ≫ pullback.fst q f = Y'.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b'Hom) →
      (Over.pullback r).map (Over.homMk (pullback.lift jV V.hom hjV) (pullback.lift_snd _ _ _) :
        V ⟶ (Over.pullback U.ι).obj Y) =
        e'.inv ≫ (Over.pullback U'.ι).map eY'.inv ≫
          (overRestrictPuncturedCompPullbackIso hrad).inv.app Y := by
  intro U U' f r q Y jV e' eY' hjV hcomp_ring heY'_fst
  set Φ : V ⟶ (Over.pullback U.ι).obj Y :=
    Over.homMk (pullback.lift jV V.hom hjV) (pullback.lift_snd _ _ _)
  have hw1 := Over.w ((Over.pullback r).map Φ)
  have hw2 := Over.w (e'.inv ≫ (Over.pullback U'.ι).map eY'.inv ≫
    (overRestrictPuncturedCompPullbackIso hrad).inv.app Y)
  dsimp only [Functor.comp_obj, Over.pullback_obj_hom, Over.mk_hom, Y] at hw1 hw2
  ext1
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · dsimp only [Over.pullback_obj_hom, Over.mk_hom, Y]
      simp only [Category.assoc]
      have hL : ((Over.pullback r).map Φ).left ≫
          pullback.fst (pullback.snd q U.ι) r ≫ pullback.fst q U.ι =
          (pullback V.hom r).toSpecΓ ≫
            Spec.map (CommRingCat.ofHom ((pullback.fst V.hom r).appTop.hom.comp ψ)) := by
        have hΦ_left : Φ.left = pullback.lift jV V.hom hjV := rfl
        simp only [Over.pullback_map_left]
        dsimp only [Over.pullback_obj_left, Over.pullback_obj_hom, Over.mk_hom, Y]
        rw [pullback.lift_fst_assoc, Category.assoc, hΦ_left, pullback.lift_fst]
        dsimp only [jV]
        rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp, CommRingCat.ofHom_comp,
          CommRingCat.ofHom_hom]
      have hR_step : ((overRestrictPuncturedCompPullbackIso hrad).inv.app Y).left ≫
          pullback.fst (pullback.snd q U.ι) r ≫ pullback.fst q U.ι =
          pullback.fst (pullback.snd q f) U'.ι ≫ pullback.fst q f :=
        overRestrictPuncturedCompPullbackIso_inv_app_left_fst_fst hrad Y
      have hR : (e'.inv ≫ (Over.pullback U'.ι).map eY'.inv ≫
          (overRestrictPuncturedCompPullbackIso hrad).inv.app Y).left ≫
          pullback.fst (pullback.snd q U.ι) r ≫ pullback.fst q U.ι =
          (pullback V.hom r).toSpecΓ ≫
            Spec.map (CommRingCat.ofHom
              ((e'.inv.left ≫ pullback.fst Y'.hom U'.ι).appTop.hom.comp b'Hom)) := by
        simp only [Over.comp_left, Category.assoc, hR_step, Over.pullback_map_left]
        dsimp only [Over.pullback_obj_hom, Over.mk_hom, Y, q, f]
        rw [pullback.lift_fst_assoc, Category.assoc, heY'_fst, ← Category.assoc e'.inv.left,
          Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp, CommRingCat.ofHom_comp,
          CommRingCat.ofHom_hom]
        dsimp only [Over.pullback_obj_left]
      rw [hL, hR, hcomp_ring]
    · dsimp only [Over.pullback_obj_hom, Over.mk_hom, Y]
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw1,
        Category.assoc, pullback.condition, ← Category.assoc, hw2]
  · exact hw1.trans hw2.symm

/-- **Extending a finite morphism across the closed point along a flat homomorphism inducing
`A ⧸ 𝔪_A ≅ A' ⧸ 𝔪_A A'`.** Let `A → A'` be a flat homomorphism of local rings, with `𝔪_A` finitely
generated, that induces a bijection `A ⧸ 𝔪_A → A' ⧸ 𝔪_A A'`. If `V ⟶ U` is a finite morphism over
the punctured spectrum `U` of `A` whose base change to the punctured spectrum `U'` of `A'` is
isomorphic to the restriction of a finite morphism `Y' ⟶ Spec A'`, then there exist a finite
morphism `Y ⟶ Spec A`, an isomorphism `Y ×_{Spec A} Spec A' ≅ Y'` over `Spec A'`, and an
isomorphism `Y ×_{Spec A} U ≅ V` over `U` compatible with the given isomorphism over `U'`. -/
theorem finite_extend_of_bijective_quotientMap
    (hfg : (maximalIdeal A).FG)
    (hquot : Function.Bijective (Ideal.quotientMap ((maximalIdeal A).map (algebraMap A A'))
      (algebraMap A A') Ideal.le_comap_map))
    (V : Over (puncturedSpectrum A).toScheme) [IsFinite V.hom]
    (Y' : Over (Spec (.of A'))) [IsFinite Y'.hom]
    (e' : (Over.pullback (puncturedSpectrum A').ι).obj Y' ≅
      (Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A')
        (preimage_puncturedSpectrum
          (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).obj V) :
    ∃ (Y : Over (Spec (.of A))) (_ : IsFinite Y.hom)
      (eY' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap A A')))).obj Y ≅ Y')
      (eV : (Over.pullback (puncturedSpectrum A).ι).obj Y ≅ V),
      (overRestrictPuncturedCompPullbackIso
        (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).hom.app Y ≫
        (Over.pullback (puncturedSpectrum A').ι).map eY'.hom ≫ e'.hom =
      (Over.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A')
        (preimage_puncturedSpectrum
          (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).ge)).map eV.hom := by
  have hrad : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A' :=
    radical_map_maximalIdeal_of_bijective_quotientMap hquot
  have : IsLocalHom (algebraMap A A') := isLocalHom_of_bijective_quotientMap hquot
  have : Module.FaithfullyFlat A A' := .of_flat_of_isLocalHom
  let U := puncturedSpectrum A
  let U' := puncturedSpectrum A'
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let r := f.resLE U U' (preimage_puncturedSpectrum hrad).ge
  have hU : IsPullback r U'.ι U.ι f :=
    f.isPullback_resLE_of_eq U (preimage_puncturedSpectrum hrad).symm
  obtain ⟨B, _, _, _, b'Hom, ψ, eY', hψA, hcomp_ring, heY'_fst⟩ :=
    exists_finite_algebra_of_bijective_quotientMap hfg hquot V Y' e'
  let q : Spec (.of B) ⟶ Spec (.of A) := Spec.algebraMap A B
  have : IsFinite q := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let Y : Over (Spec (.of A)) := Over.mk q
  -- Build the comparison morphism `Φ : V ⟶ Y ×_{Spec A} U` over `U`.
  let jV : V.left ⟶ Spec (.of B) := V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have hjV : jV ≫ q = V.hom ≫ U.ι := by
    dsimp only [jV, q, Spec.algebraMap]
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψA, CommRingCat.ofHom_hom]
    exact (V.hom ≫ U.ι).toSpecΓ_SpecMap_ΓSpecIso_inv_comp_appTop
  let Φ : V ⟶ (Over.pullback U.ι).obj Y :=
    Over.homMk (pullback.lift jV V.hom hjV) (pullback.lift_snd _ _ _)
  have hΦ_pull := overPullback_map_homMk_lift_eq hrad V Y' b'Hom ψ e' eY' hjV hcomp_ring heY'_fst
  -- Descend `IsIso` from `(Over.pullback r).map Φ` along the fpqc morphism `r`.
  have : Flat f := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A A'›)
  have : Surjective f := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : Surjective r := MorphismProperty.of_isPullback hU.flip ‹Surjective f›
  have : Flat r := MorphismProperty.of_isPullback hU.flip ‹Flat f›
  have : QuasiCompact r := MorphismProperty.of_isPullback hU.flip inferInstance
  have : IsIso ((Over.pullback r).map Φ) := by
    rw [hΦ_pull]
    infer_instance
  have : IsIso Φ.left :=
    (MorphismProperty.isomorphisms Scheme.{u}).of_isPullback_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (Over.isPullback_pullback_map_left r Φ)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let eV : (Over.pullback U.ι).obj Y ≅ V :=
    (Over.isoMk (asIso Φ.left) (Over.w Φ)).symm
  have heV_inv : eV.inv = Φ := by
    ext1
    rfl
  refine ⟨Y, ‹IsFinite q›, eY', eV, ?_⟩
  rw [← cancel_mono ((Over.pullback r).map eV.inv), ← Functor.map_comp, eV.hom_inv_id,
    CategoryTheory.Functor.map_id, heV_inv, hΦ_pull]
  simp [Y, q, U, ← Functor.map_comp_assoc]

omit [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A'] in
/-- **Extending a finite morphism from the completion across the closed point** (Stacks, Lemma
58.19.3 (0BLH)). Let `A` be a Noetherian local ring with `𝔪`-adic completion `Â`, punctured spectrum
`U`, and punctured spectrum `U'` of `Â`. If `V ⟶ U` is a finite morphism whose base change to
`U'` is isomorphic to the restriction of a finite morphism `Y' ⟶ Spec Â`, then there exist a finite
morphism `Y ⟶ Spec A`, an isomorphism `Y ×_{Spec A} Spec Â ≅ Y'` over `Spec Â`, and an isomorphism
`Y ×_{Spec A} U ≅ V` over `U` compatible with the given isomorphism over `U'`. -/
@[stacks 0BLH]
theorem finite_extend_of_completion [IsNoetherianRing A]
    (V : Over (puncturedSpectrum A).toScheme) [IsFinite V.hom]
    (Y' : Over (Spec (.of (AdicCompletion (maximalIdeal A) A)))) [IsFinite Y'.hom]
    (e' : (Over.pullback (puncturedSpectrum (AdicCompletion (maximalIdeal A) A)).ι).obj Y' ≅
      (Over.pullback
        ((Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))).resLE
          (puncturedSpectrum A) (puncturedSpectrum (AdicCompletion (maximalIdeal A) A))
          (preimage_puncturedSpectrum (by
            rw [← AdicCompletion.maximalIdeal_eq_map]
            exact (maximalIdeal.isMaximal _).isPrime.radical)).ge)).obj V) :
    ∃ (Y : Over (Spec (.of A))) (_ : IsFinite Y.hom)
      (eY' : (Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A))))).obj Y ≅
          Y')
      (eV : (Over.pullback (puncturedSpectrum A).ι).obj Y ≅ V),
      (overRestrictPuncturedCompPullbackIso (A' := AdicCompletion (maximalIdeal A) A) (by
        rw [← AdicCompletion.maximalIdeal_eq_map]
        exact (maximalIdeal.isMaximal _).isPrime.radical)).hom.app Y ≫
        (Over.pullback (puncturedSpectrum (AdicCompletion (maximalIdeal A) A)).ι).map eY'.hom ≫
          e'.hom =
      (Over.pullback
        ((Spec.map (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))).resLE
          (puncturedSpectrum A) (puncturedSpectrum (AdicCompletion (maximalIdeal A) A))
          (preimage_puncturedSpectrum (by
            rw [← AdicCompletion.maximalIdeal_eq_map]
            exact (maximalIdeal.isMaximal _).isPrime.radical)).ge)).map eV.hom :=
  finite_extend_of_bijective_quotientMap (maximalIdeal A).fg_of_isNoetherianRing
    ((bijective_quotientMap_iff_map_maximalIdeal_eq_and_bijective_residueFieldMap
      (algebraMap A _)).mpr
      ⟨AdicCompletion.maximalIdeal_eq_map.symm, AdicCompletion.residueField_map_bijective A⟩)
    V Y' e'

end Extend

end TauCeti.IsLocalRing
