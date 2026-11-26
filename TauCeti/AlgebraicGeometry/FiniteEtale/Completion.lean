/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Extension
public import TauCeti.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.Depth.Flat
public import TauCeti.RingTheory.LocalRing.Quotient
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Completion
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.RingTheory.Etale.FiniteDescent

/-!
# Extending finite étale covers after a flat base change

Let `A → A'` be a flat homomorphism of local rings such that the closed point is the only point of
`Spec A'` over the closed point of `Spec A`, for instance the completion of a Noetherian local ring
`A` at its maximal ideal. Then `A → A'` is local and the punctured spectrum `U'` of `A'` is the
preimage of the punctured spectrum `U` of `A` (`TauCeti.IsLocalRing.preimage_puncturedSpectrum`).

This file establishes two criteria under which extension of a finite étale cover `V` of `U` across
the closed point of `Spec A` is equivalent to extension of its base change over `U'` across the
closed point of `Spec A'`:

1. When `A` and `A'` are Noetherian and `A` has depth at least two
   (`TauCeti.IsLocalRing.extends_iff_extends_pullback_of_flat`), the criterion
   `TauCeti.IsLocalRing.extends_iff_sections_finiteEtale` (Stacks 0BLK) reduces extension on both
   sides to global sections being finite étale, and flat base change
   (`TauCeti.IsLocalRing.isPushout_appTop_pullback_puncturedSpectrum_of_flat`) identifies global
   sections of the pullback with `A' ⊗[A] Γ(V, 𝒪_V)`.
2. When `𝔪_A` is finitely generated and `A → A'` induces a bijection `A ⧸ 𝔪_A → A' ⧸ 𝔪_A A'`,
   without any depth hypothesis on `A` or Noetherian hypothesis on `A` or `A'`
   (`TauCeti.IsLocalRing.extends_iff_extends_pullback_of_bijective_quotientMap`), formal gluing of
   finite morphisms (`TauCeti.IsLocalRing.finite_extend_of_bijective_quotientMap`, Stacks 0BLH)
   produces a finite extension `Y ⟶ Spec A` whose base change to `Spec A'` is isomorphic to the
   given finite étale extension over `Spec A'`, and étaleness descends along the fpqc morphism
   `Spec A' ⟶ Spec A`.

Specialising the second criterion to the `𝔪_A`-adic completion `Â` of a Noetherian local ring `A`
gives Stacks, Lemma 58.20.4 (0BLL) in full generality
(`TauCeti.IsLocalRing.extends_iff_completion_extends`), and implies that purity descends from `Â`
to `A` (`TauCeti.IsLocalRing.purityHolds_of_purityHolds_completion`).

## Main results

* `TauCeti.IsLocalRing.extends_iff_extends_pullback_of_flat`: for `A` and `A'` Noetherian and `A`
  of depth at least two, a finite étale cover of `U` extends to `Spec A` if and only if its base
  change to `U'` extends to `Spec A'`.
* `TauCeti.IsLocalRing.extends_iff_extends_pullback_of_bijective_quotientMap`: for any flat `A → A'`
  with `𝔪_A` finitely generated inducing `A ⧸ 𝔪_A ≅ A' ⧸ 𝔪_A A'`, a finite étale cover of `U`
  extends to `Spec A` if and only if its base change to `U'` extends to `Spec A'`, so purity
  descends from `A'` to `A`
  (`TauCeti.IsLocalRing.purityHolds_of_purityHolds_of_bijective_quotientMap`).
* `TauCeti.IsLocalRing.extends_iff_completion_extends`: for a Noetherian local ring `A`, the case
  of its `𝔪_A`-adic completion, which is Stacks, Lemma 58.20.4 (0BLL).
* `TauCeti.IsLocalRing.purityHolds_of_purityHolds_completion`: for a Noetherian local ring `A`, if
  purity holds for the `𝔪_A`-adic completion of `A`, then purity holds for `A`.

## References

* [The Stacks Project, Lemma 58.20.4](https://stacks.math.columbia.edu/tag/0BLL).
* [The Stacks Project, Lemma 58.19.3](https://stacks.math.columbia.edu/tag/0BLH).
* [The Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK).
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

variable {A A' : Type u} [CommRing A] [IsLocalRing A]
  [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A']

/-- Let `A → A'` be a flat homomorphism of Noetherian local rings such that the closed point is
the only point of `Spec A'` over the closed point of `Spec A`. If `A` has depth at least two, a
finite étale cover of the punctured spectrum of `A` extends across the closed point if and only if
its base change to the punctured spectrum of `A'` extends across the closed point. -/
theorem extends_iff_extends_pullback_of_flat [IsNoetherianRing A] [IsNoetherianRing A']
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y : FiniteEtaleScheme (Spec (.of A')),
        Nonempty ((restrictPunctured A').obj Y ≅ (pullbackPunctured h).obj V) := by
  have : IsLocalHom (algebraMap A A') :=
    ((local_hom_tfae (algebraMap A A')).out 1 3).mpr (h ▸ Ideal.le_radical)
  have : Module.FaithfullyFlat A A' := .of_flat_of_isLocalHom
  have hdepth' : 2 ≤ depth (ModuleCat.of A' A') := by
    rw [depth_eq_add_of_flat (R := A)]
    exact hdepth.trans le_self_add
  rw [extends_iff_sections_finiteEtale A hdepth, extends_iff_sections_finiteEtale A' hdepth']
  -- The criterion uses the algebra structures given by the ring maps of
  -- `isPushout_appTop_pullback_puncturedSpectrum_of_flat`, and `RingHom.Finite` and
  -- `RingHom.Etale` unfold to `Module.Finite` and `Algebra.Etale` for those structures.
  exact CommRingCat.finite_and_etale_iff_of_isPushout_of_faithfullyFlat
    (isPushout_appTop_pullback_puncturedSpectrum_of_flat (maximalIdeal A).fg_of_isNoetherianRing h
      V.obj)
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

/-- Let `A → A'` be a flat homomorphism of local rings, with `𝔪_A` finitely generated, that induces
a bijection `A ⧸ 𝔪_A → A' ⧸ 𝔪_A A'`. Then a finite étale cover of the punctured spectrum of `A`
extends across the closed point if and only if its base change to the punctured spectrum of `A'`
extends across the closed point. Unlike `extends_iff_extends_pullback_of_flat`, this requires no
depth assumption on `A` and no Noetherian hypothesis on `A` or `A'`. -/
theorem extends_iff_extends_pullback_of_bijective_quotientMap
    (hfg : (maximalIdeal A).FG)
    (hquot : Function.Bijective (Ideal.quotientMap ((maximalIdeal A).map (algebraMap A A'))
      (algebraMap A A') Ideal.le_comap_map))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y : FiniteEtaleScheme (Spec (.of A')),
        Nonempty ((restrictPunctured A').obj Y ≅
          (pullbackPunctured
            (radical_map_maximalIdeal_of_bijective_quotientMap hquot)).obj V) := by
  refine ⟨extends_pullbackPunctured_of_extends
    (radical_map_maximalIdeal_of_bijective_quotientMap hquot), ?_⟩
  rintro ⟨Y', ⟨e'⟩⟩
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  obtain ⟨Y₀, hY₀_fin, eY', eV, _⟩ :=
    finite_extend_of_bijective_quotientMap hfg hquot V.obj Y'.obj
      ((finiteEtaleSchemeProperty (puncturedSpectrum A').toScheme).ι.mapIso e')
  obtain ⟨_, _⟩ := flat_and_surjective_SpecMap_of_bijective_quotientMap hquot
  have hw : eY'.hom.left ≫ Y'.obj.hom = pullback.snd Y₀.hom f := Over.w eY'.hom
  have het_snd : Etale (pullback.snd Y₀.hom f) := by
    rw [← hw]
    infer_instance
  have het_Y₀ : Etale Y₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (IsPullback.of_hasPullback Y₀.hom f).flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ het_snd
  exact ⟨⟨Y₀, (finiteEtaleSchemeProperty_iff Y₀).mpr ⟨hY₀_fin, het_Y₀⟩⟩,
    ⟨ObjectProperty.isoMk _ eV⟩⟩

/-- Let `A → A'` be a flat homomorphism of local rings, with `𝔪_A` finitely generated, that induces
a bijection `A ⧸ 𝔪_A → A' ⧸ 𝔪_A A'`. If purity holds for `A'`, then purity holds for `A`. -/
theorem purityHolds_of_purityHolds_of_bijective_quotientMap
    (hfg : (maximalIdeal A).FG)
    (hquot : Function.Bijective (Ideal.quotientMap ((maximalIdeal A).map (algebraMap A A'))
      (algebraMap A A') Ideal.le_comap_map))
    (hA' : PurityHolds A') : PurityHolds A :=
  (purityHolds_iff A).mpr fun V ↦
    (extends_iff_extends_pullback_of_bijective_quotientMap hfg hquot V).mpr
      ((purityHolds_iff A').mp hA' _)

omit [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A'] in
/-- **Extension across the closed point is detected on the completion** (Stacks, Lemma 58.20.4
(0BLL)). For a Noetherian local ring `A`, a finite étale cover of the punctured spectrum of `A`
extends across the closed point if and only if its base change to the punctured spectrum of the
`𝔪`-adic completion `Â` extends across the closed point of `Spec Â`. -/
@[stacks 0BLL]
theorem extends_iff_completion_extends [IsNoetherianRing A]
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y : FiniteEtaleScheme (Spec (.of (AdicCompletion (maximalIdeal A) A))),
        Nonempty ((restrictPunctured (AdicCompletion (maximalIdeal A) A)).obj Y ≅
          (pullbackPunctured TauCeti.AdicCompletion.radical_map_maximalIdeal).obj V) :=
  extends_iff_extends_pullback_of_bijective_quotientMap (maximalIdeal A).fg_of_isNoetherianRing
    TauCeti.AdicCompletion.bijective_quotientMap_maximalIdeal V

omit [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A'] in
/-- **Purity descends from the completion.** For a Noetherian local ring `A`, if purity holds for
its `𝔪`-adic completion `Â`, then purity holds for `A`. -/
theorem purityHolds_of_purityHolds_completion [IsNoetherianRing A]
    (h : PurityHolds (AdicCompletion (maximalIdeal A) A)) : PurityHolds A :=
  (purityHolds_iff A).mpr fun V ↦
    (extends_iff_completion_extends V).mpr ((purityHolds_iff _).mp h _)

end TauCeti.IsLocalRing
