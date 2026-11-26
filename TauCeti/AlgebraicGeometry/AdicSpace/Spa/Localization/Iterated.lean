/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.CompletedRationalSubset
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.UniversalProperty
import TauCeti.RingTheory.Huber.LocalizationTopology.Iterated
import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# Transitivity of completed rational localisations

`TauCeti.Huber.PairOfDefinition.iteratedLocalizationRingEquiv` identifies `A⟨T''/s''⟩` with
`B⟨ρ(T'')/ρ(s'')⟩` for `B = A⟨T/s⟩` when `(T'', s'')` refines `(T, s)` syntactically and `B`
carries `P.completionLocalization`. Combining this with Wedhorn's Proposition 8.2(1)–(2)
(`exists_mem_spaRationalOpens_locOpensComap_eq`), common refinements, and the geometric universal
property (`existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset`) removes both the
syntactic refinement hypothesis and the choice of pair of definition on `B`.

## Main results

* `TauCeti.Huber.exists_ratLoc_ringEquiv_ratLoc`: an iterated completed rational localisation with
  open numerator ideals is topologically `A`-isomorphic to a single completed rational localisation
  with open numerator ideal.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 8.2 and Remark 8.4.
-/

public section

namespace TauCeti.Huber

open TauCeti.ValuationSpectrum

/-- **Transitivity of completed rational localisations with open numerator ideals** (Wedhorn,
Proposition 8.2 and Remark 8.4). Let `B = A⟨T/s⟩` with `T` generating an open ideal of `A`, and let
`C = B⟨T_B/s_B⟩` with `T_B` generating an open ideal of `B`. Then there exist a finite set `T''` of
`A` generating an open ideal, a denominator `s'' : A`, a proof `hden''` of `HasDenominatorPower`,
and a homeomorphic ring equivalence `e : A⟨T''/s''⟩ ≃+* C` commuting with the canonical maps from
`A`. -/
theorem exists_ratLoc_ringEquiv_ratLoc {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hden : P.HasDenominatorPower T s (Localization.Away s))
    (hT : IsOpen ((Ideal.span (T : Set A) : Ideal A) : Set A))
    (P_B : PairOfDefinition (ratLoc P T s hden)) (T_B : Finset (ratLoc P T s hden))
    (s_B : ratLoc P T s hden)
    (hden_B : P_B.HasDenominatorPower T_B s_B (Localization.Away s_B))
    (hT_B : IsOpen ((Ideal.span (T_B : Set (ratLoc P T s hden)) : Ideal (ratLoc P T s hden)) :
      Set (ratLoc P T s hden))) :
    ∃ (T'' : Finset A) (s'' : A) (hden'' : P.HasDenominatorPower T'' s'' (Localization.Away s'')),
      IsOpen ((Ideal.span (T'' : Set A) : Ideal A) : Set A) ∧
      ∃ e : ratLoc P T'' s'' hden'' ≃+* ratLoc P_B T_B s_B hden_B,
        Continuous e ∧ Continuous e.symm ∧
        ∀ a : A, e (algebraMap A (ratLoc P T'' s'' hden'') a) =
          algebraMap (ratLoc P T s hden) (ratLoc P_B T_B s_B hden_B)
            (algebraMap A (ratLoc P T s hden) a) := by
  classical
  have : IsHuberRing A := ⟨⟨P⟩⟩
  let B := ratLoc P T s hden; let C := ratLoc P_B T_B s_B hden_B
  let Aplus : Subring A := powerBoundedSubring A
  let Bplus : Subring B := P.completedPlusSubring Aplus T s (Localization.Away s) hden
  have hBplus : ∀ ⦃b : B⦄, b ∈ Bplus → IsPowerBounded b :=
    P.isPowerBounded_of_mem_completedPlusSubring Aplus (fun _ ↦ mem_powerBoundedSubring.mp) T s
      (Localization.Away s) hden
  obtain ⟨V, hV, hVle, hVeq⟩ := exists_mem_spaRationalOpens_locOpensComap_eq P Aplus T s
    (Localization.Away s) hden hT (spaBasicOpen Bplus T_B s_B)
    (spaBasicOpen_mem_spaRationalOpens hT_B)
  obtain ⟨T', s', hT', rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hV
  let p₀ : P.Presentation := ⟨T, s, hden⟩
  let q₀ : P.Presentation := ⟨T', s', P.hasDenominatorPower_of_isOpen_span T' s' _ hT'⟩
  let p : P.Presentation := p₀.commonRefinement q₀
  have hp_open : IsOpen ((Ideal.span (p.num : Set A) : Ideal A) : Set A) :=
    PairOfDefinition.Presentation.commonRefinement_num p₀ q₀ ▸
      P.isOpen_span_insert_mul_insert hT hT'
  have hp_basic : spaBasicOpen Aplus p.num p.den = spaBasicOpen Aplus T' s' :=
    (spaBasicOpen_commonRefinement Aplus p₀ q₀).trans (inf_eq_right.mpr hVle)
  obtain ⟨r, hr, hTr⟩ := PairOfDefinition.Presentation.le_def.mp (p₀.le_commonRefinement_left q₀)
  let Q : PairOfDefinition B := P.completionLocalization T s (Localization.Away s) hden
  let ρ : A →+* B := P.toCompletionLoc T s (Localization.Away s) hden
  let TB : Finset B := p.num.image ρ; let sB' : B := ρ p.den
  have hden_Q : Q.HasDenominatorPower TB sB' (Localization.Away sB') :=
    PairOfDefinition.hasDenominatorPower_completionLocalization_of_coe_eq_image P T s _ hden
      p.num p.den _ p.hasDenominatorPower _ TB Finset.coe_image
  let D := ratLoc Q TB sB' hden_Q
  let e₁ : ratLoc P p.num p.den p.hasDenominatorPower ≃+* D :=
    P.iteratedLocalizationRingEquiv T s _ hden p.num p.den _ p.hasDenominatorPower _ TB
      Finset.coe_image r hr hTr
  have he₁_alg := P.iteratedLocalizationRingEquiv_coe_comp_toCompletionLoc T s _ hden
    p.num p.den _ p.hasDenominatorPower (Localization.Away sB') TB Finset.coe_image r hr hTr
  have hrat_eq : rationalSubset Bplus TB sB' = rationalSubset Bplus T_B s_B :=
    rationalSubset_eq_of_spaBasicOpen_eq <|
      (locOpensComap_spaBasicOpen P Aplus T s _ hden p.num p.den).symm.trans
        ((congrArg _ hp_basic).trans hVeq)
  obtain ⟨f, ⟨hfc, hfe⟩, -⟩ :=
    existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset Q Bplus TB sB' _ hden_Q
      (powerBoundedSubring C) ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
      (P_B.continuous_toCompletionLoc T_B s_B _ hden_B).continuousAt fun w hw ↦ hrat_eq.ge <| by
        simpa only [spaComapLoc_val] using spaComapLoc_mem_rationalSubset P_B Bplus T_B s_B _ hden_B
          ⟨w, spa_antitone (P_B.completedPlusSubring_le_powerBoundedSubring Bplus hBplus T_B s_B _
            hden_B) hw⟩
  obtain ⟨g, ⟨hgc, hge⟩, -⟩ :=
    existsUnique_continuous_ringHom_of_forall_comap_mem_rationalSubset P_B Bplus T_B s_B _ hden_B
      (powerBoundedSubring D) ⟨isOpen_powerBoundedSubring _, inferInstance, le_rfl⟩
      (Q.continuous_toCompletionLoc TB sB' _ hden_Q).continuousAt fun w hw ↦ hrat_eq.le <| by
        simpa only [spaComapLoc_val] using spaComapLoc_mem_rationalSubset Q Bplus TB sB' _ hden_Q
          ⟨w, spa_antitone (Q.completedPlusSubring_le_powerBoundedSubring Bplus hBplus TB sB' _
            hden_Q) hw⟩
  have hgf : g.comp f = RingHom.id D := Q.eq_id_of_comp_toCompletionLoc_eq_self TB sB' _ hden_Q
    (g.comp f) (hgc.comp hfc) (by rw [RingHom.comp_assoc, hfe, hge])
  have hfg : f.comp g = RingHom.id C := P_B.eq_id_of_comp_toCompletionLoc_eq_self T_B s_B _ hden_B
    (f.comp g) (hfc.comp hgc) (by rw [RingHom.comp_assoc, hge, hfe])
  refine ⟨p.num, p.den, p.hasDenominatorPower, hp_open, e₁.trans (.ofRingHom f g hfg hgf),
    hfc.comp (P.continuous_iteratedLocalizationRingEquiv T s _ hden p.num p.den _
      p.hasDenominatorPower _ TB Finset.coe_image r hr hTr),
    (P.continuous_iteratedLocalizationRingEquiv_symm T s _ hden p.num p.den _
      p.hasDenominatorPower _ TB Finset.coe_image r hr hTr).comp hgc, fun a ↦ ?_⟩
  rw [algebraMap_ratLoc, algebraMap_ratLoc, algebraMap_ratLoc]
  exact (congrArg f congr($he₁_alg a)).trans congr($hfe (ρ a))

end TauCeti.Huber
