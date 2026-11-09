/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Extension
public import TauCeti.AlgebraicGeometry.Scheme.SectionsBaseChange
public import TauCeti.RingTheory.Depth.Flat
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Etale.FiniteDescent

/-!
# Extending finite étale covers after a flat local base change

Let `A → A'` be a flat local homomorphism of Noetherian local rings such that the closed point is
the only point of `Spec A'` over the closed point of `Spec A`, for instance the completion of `A`
at its maximal ideal. Then the punctured spectrum `U'` of `A'` is the preimage of the punctured
spectrum `U` of `A` (`TauCeti.IsLocalRing.preimage_puncturedSpectrum`). If `A` has depth at
least two, a finite étale cover `V` of `U` extends to a finite étale cover of `Spec A` if and only
if its base change to `U'` extends to a finite étale cover of `Spec A'`.

By the criterion `TauCeti.IsLocalRing.extends_iff_sections_finiteEtale` (Stacks 0BLK), applied to
`A` and to `A'` (whose depth is at least that of `A`, by the depth formula for flat local
homomorphisms), both conditions say that the ring of global sections is finite étale. Flat base
change for sections of the structure sheaf identifies the global sections of the base change of `V`
with `A' ⊗[A] Γ(V, 𝒪_V)`, and finite étale algebras are stable under base change and descend along
the faithfully flat map `A → A'`
(`CommRingCat.finite_and_etale_iff_of_isPushout_of_faithfullyFlat`).

## Main results

* `TauCeti.IsLocalRing.isPushout_appTop_pullback_of_flat`: the global sections of the base change
  of a finite étale cover `V` of `U` to `U'` are `A' ⊗[A] Γ(V, 𝒪_V)`.
* `TauCeti.IsLocalRing.extends_iff_extends_pullback_of_flat`: for `A` of depth at least two, a
  finite étale cover of `U` extends to `Spec A` if and only if its base change to `U'` extends to
  `Spec A'`.
* `TauCeti.IsLocalRing.extends_iff_completion_extends_of_two_le_depth`: the case of the completion
  of `A`, which is Stacks, Lemma 58.20.4 (0BLL) for local rings of depth at least two.

## References

* [The Stacks Project, Lemma 58.20.4](https://stacks.math.columbia.edu/tag/0BLL).
* [The Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK).
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base change.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

universe u

namespace TauCeti.IsLocalRing

variable {A A' : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A']

/-- **Flat base change for the sections of a finite étale cover of the punctured spectrum.** Let
`A → A'` be a flat homomorphism of local rings, with `A` Noetherian, such that the closed point is
the only point of `Spec A'` over the closed point of `Spec A`. For a finite étale cover `V` of the
punctured spectrum of `A`, with base change `V'` to the punctured spectrum of `A'`, the square of
global sections exhibits `Γ(V', 𝒪)` as `A' ⊗[A] Γ(V, 𝒪)`. -/
theorem isPushout_appTop_pullback_of_flat
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    IsPushout ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ (puncturedSpectrum A).ι).appTop)
      (CommRingCat.ofHom (algebraMap A A'))
      (pullback.fst V.obj.hom ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
        (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge)).appTop
      ((Scheme.ΓSpecIso (.of A')).inv ≫ (pullback.snd V.obj.hom
        ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE (puncturedSpectrum A)
          (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge) ≫
        (puncturedSpectrum A').ι).appTop) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A A'))
  let U := puncturedSpectrum A
  let U' := puncturedSpectrum A'
  let r := f.resLE U U' (preimage_puncturedSpectrum h).ge
  -- The base change of `V` to `U'` is its base change to `Spec A'`.
  have hU : IsPullback r U'.ι U.ι f := IsOpenImmersion.isPullback _ _ _ _
    (Scheme.Hom.resLE_comp_ι _ _).symm (by simpa using preimage_puncturedSpectrum h)
  let : V.obj.left.Over (Spec (.of A)) := ⟨V.obj.hom ≫ U.ι⟩
  let : (pullback V.obj.hom r).Over (Spec (.of A')) := ⟨pullback.snd V.obj.hom r ≫ U'.ι⟩
  have H : IsPullback (pullback.fst V.obj.hom r) (pullback V.obj.hom r ↘ Spec (.of A'))
      (V.obj.left ↘ Spec (.of A)) f :=
    (IsPullback.of_hasPullback V.obj.hom r).paste_vert hU
  -- `V` is quasi-compact, as it is finite over the quasi-compact `U`, and quasi-separated.
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    (isCompact_puncturedSpectrum_of_fg_maximalIdeal A (maximalIdeal A).fg_of_isNoetherianRing)
  have : CompactSpace V.obj.left := QuasiCompact.compactSpace_of_compactSpace V.obj.hom
  have : QuasiSeparatedSpace V.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated (V.obj.hom ≫ U.ι)
  have hpush := TauCeti.AlgebraicGeometry.isPushout_baseRingToStructurePresheaf_app_of_flat H
    (W := ⊤) isCompact_univ isQuasiSeparated_univ (W' := ⊤) rfl
  -- `Scheme.Hom.app_eq_appLE` states this with the open `g ⁻¹ᵁ ⊤`, which is `⊤` up to defeq.
  have happ {X Y : Scheme.{u}} (g : X ⟶ Y) : g.appLE ⊤ ⊤ le_top = g.appTop :=
    (Scheme.Hom.app_eq_appLE g).symm
  rwa [Scheme.baseRingToStructurePresheaf_app_eq_appLE,
    Scheme.baseRingToStructurePresheaf_app_eq_appLE, happ, happ, happ] at hpush

/-- Let `A → A'` be a flat homomorphism of Noetherian local rings such that the closed point is
the only point of `Spec A'` over the closed point of `Spec A`. If `A` has depth at least two, a
finite étale cover of the punctured spectrum of `A` extends across the closed point if and only if
its base change to the punctured spectrum of `A'` extends across the closed point. -/
theorem extends_iff_extends_pullback_of_flat [IsNoetherianRing A']
    (h : ((maximalIdeal A).map (algebraMap A A')).radical = maximalIdeal A')
    (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y : FiniteEtaleScheme (Spec (.of A')), Nonempty ((restrictPunctured A').obj Y ≅
        (FiniteEtaleScheme.pullback ((Spec.map (CommRingCat.ofHom (algebraMap A A'))).resLE
          (puncturedSpectrum A) (puncturedSpectrum A') (preimage_puncturedSpectrum h).ge)).obj
          V) := by
  have : IsLocalHom (algebraMap A A') :=
    ((local_hom_tfae (algebraMap A A')).out 1 3).mpr (h ▸ Ideal.le_radical)
  have : Module.FaithfullyFlat A A' := .of_flat_of_isLocalHom
  have hdepth' : 2 ≤ depth (ModuleCat.of A' A') := by
    rw [depth_eq_add_of_flat (R := A)]
    exact hdepth.trans le_self_add
  rw [extends_iff_sections_finiteEtale A hdepth, extends_iff_sections_finiteEtale A' hdepth']
  -- The criterion uses the algebra structures given by the ring maps of
  -- `isPushout_appTop_pullback_of_flat`, and `RingHom.Finite` and `RingHom.Etale` unfold to
  -- `Module.Finite` and `Algebra.Etale` for those structures.
  exact CommRingCat.finite_and_etale_iff_of_isPushout_of_faithfullyFlat
    (isPushout_appTop_pullback_of_flat h V)
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

omit [CommRing A'] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A'] in
/-- **Extension across the closed point is detected on the completion**, for a Noetherian local
ring `A` of depth at least two: a finite étale cover of the punctured spectrum of `A` extends
across the closed point if and only if its base change to the punctured spectrum of the
`𝔪`-adic completion `Â` extends across the closed point of `Spec Â`. -/
@[stacks 0BLL "for local rings of depth at least two"]
theorem extends_iff_completion_extends_of_two_le_depth (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme) :
    (∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V)) ↔
      ∃ Y : FiniteEtaleScheme (Spec (.of (AdicCompletion (maximalIdeal A) A))),
        Nonempty ((restrictPunctured (AdicCompletion (maximalIdeal A) A)).obj Y ≅
          (FiniteEtaleScheme.pullback ((Spec.map (CommRingCat.ofHom
            (algebraMap A (AdicCompletion (maximalIdeal A) A)))).resLE (puncturedSpectrum A)
            (puncturedSpectrum (AdicCompletion (maximalIdeal A) A))
            (preimage_puncturedSpectrum (by
              rw [← AdicCompletion.maximalIdeal_eq_map]
              exact (maximalIdeal.isMaximal _).isPrime.radical)).ge)).obj V) :=
  extends_iff_extends_pullback_of_flat (by
    rw [← AdicCompletion.maximalIdeal_eq_map]
    exact (maximalIdeal.isMaximal _).isPrime.radical) hdepth V

end TauCeti.IsLocalRing
