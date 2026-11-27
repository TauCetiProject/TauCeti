/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.CohenMacaulay.Flat
public import TauCeti.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.LocalRing.Quotient
public import TauCeti.RingTheory.RegularLocalRing.Flat

import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.AdicCompletion.Localization

/-!
# Completions of local rings and their invariants

Let `R` be a Noetherian local ring with maximal ideal `𝔪`, let `I ⊆ 𝔪` be an ideal and let `R̂` be
the `I`-adic completion of `R`. Then `R̂` is a Noetherian local ring, flat over `R`, with maximal
ideal `𝔪 R̂` and the same residue field. This file shows that `R̂` has the same Krull dimension as
`R`, that `R̂` is regular if and only if `R` is, and that `R̂` is Cohen–Macaulay if and only if `R`
is. For `I = 𝔪` these, together with Mathlib's `AdicCompletion.spanFinrank_maximalIdeal_eq`, are
among the invariants of a local ring that are unchanged by completion.

Descent of regularity from `R̂` to `R` lets regularity be tested on complete local rings, where the
Cohen structure theorem presents them as quotients of power series rings over a field or, in mixed
characteristic, over a complete discrete valuation ring. Completions along smaller ideals occur as
the completed localisations `lim_n (A ⧸ Iⁿ)_𝔭` of an adic ring `A` with ideal of definition `I` at
an open prime `𝔭`, which have the dimension, regularity, and Cohen–Macaulay property of `A_𝔭`.

More generally, for any local ring `R` and ideal `I ≤ 𝔪`, `AdicCompletion I R → R ⧸ I` and
`R → AdicCompletion I R` are local homomorphisms, and `AdicCompletion I R` is a local ring.
Finally, if `f : S →+* S'` is a homomorphism of local rings and `J ≤ 𝔪_S` is an ideal such that
`S ⧸ J ^ n → S' ⧸ (J S') ^ n` is bijective for every `n ≥ 1`, then `f` induces an isomorphism
between the maximal-ideal-adic completions of `S` and `S'`.

## Main results

* `TauCeti.AdicCompletion.isLocalHom_evalOneₐ_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.isLocalHom_algebraMap_of_le_maximalIdeal`: local homomorphisms into and
  out of `AdicCompletion I R` for any ideal `I ≤ 𝔪`.
* `TauCeti.AdicCompletion.isLocalRing_of_le`: the completion of a local ring along an ideal
  `I ⊆ 𝔪` is a local ring.
* `TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le`: its maximal ideal is `𝔪 R̂`.
* `TauCeti.AdicCompletion.ringKrullDim_eq`: `R̂` and `R` have the same Krull dimension.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff`: `R̂` is regular if and only if `R` is.
* `TauCeti.AdicCompletion.isCohenMacaulay_self_iff`: `R̂` is Cohen–Macaulay if and only if `R` is.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff_of_isMaximal`: completing a Noetherian ring `R` at
  a maximal ideal `p` is regular if and only if any localization `Rₚ` of `R` at `p` is regular.
* `AdicCompletion.mapₐ_maximalIdeal_bijective_of_quotientMap_pow_bijective`,
  `RingHom.adicCompletionMaximalIdealRingEquivOfQuotientMap`: the induced isomorphism between
  maximal-ideal completions.

## References

* [Stacks Project, Lemma 15.44.1](https://stacks.math.columbia.edu/tag/07NV), the dimension of
  the completion.
* [Stacks Project, Lemma 15.44.2](https://stacks.math.columbia.edu/tag/07NX), the Cohen–Macaulay
  property of the completion.
* [Stacks Project, Lemma 15.44.4](https://stacks.math.columbia.edu/tag/07NY), regularity of the
  completion.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

section

variable {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}

/-- For a local ring `R` and an ideal `I ≤ 𝔪_R`, the canonical projection
`AdicCompletion I R → R ⧸ I` is a local homomorphism. -/
theorem isLocalHom_evalOneₐ_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalHom (evalOneₐ I).toRingHom := by
  have hI_ne : I ≠ ⊤ := (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  refine ⟨fun x hx ↦ x.isUnit_of_forall_isUnit_evalₐ fun n ↦ ?_⟩
  rcases n with _ | k
  · have : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact isUnit_of_subsingleton _
  · have : IsLocalHom (Ideal.Quotient.factor (Ideal.pow_le_self k.succ_ne_zero)) :=
      Ideal.Quotient.isLocalHom_factor _ hI_ne
    refine isUnit_of_map_unit (Ideal.Quotient.factor (Ideal.pow_le_self k.succ_ne_zero))
      (evalₐ I (k + 1) x) ?_
    rwa [← Ideal.Quotient.factor_comp_apply
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le k))) (by simp : I ^ 1 ≤ I),
      factor_evalₐ (Nat.succ_le_succ (Nat.zero_le k)), factorₐ_evalₐ_one]

/-- For a local ring `R` and an ideal `I ≤ 𝔪_R`, the canonical map `R → AdicCompletion I R` is a
local homomorphism. -/
theorem isLocalHom_algebraMap_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalHom (algebraMap R (AdicCompletion I R)) := by
  have : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  have : IsLocalHom ((evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R))) := by
    rw [evalOneₐ_comp_algebraMap_eq_mk]
    exact .of_surjective _ Ideal.Quotient.mk_surjective
  exact isLocalHom_of_comp (algebraMap R (AdicCompletion I R)) (evalOneₐ I).toRingHom

/-- The completion of a local ring along an ideal contained in the maximal ideal is a local ring:
the projection `AdicCompletion I R → R ⧸ I` is a local homomorphism onto the local ring `R ⧸ I`. -/
theorem isLocalRing_of_le (hI : I ≤ maximalIdeal R) :
    IsLocalRing (AdicCompletion I R) := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := isLocalHom_evalOneₐ_of_le_maximalIdeal hI
  exact (AdicCompletion.evalOneₐ I).toRingHom.domain_isLocalRing

/-- The maximal ideal of the completion of a local ring along a finitely generated ideal `I ⊆ 𝔪`
is generated by the maximal ideal `𝔪` of the ring. -/
theorem maximalIdeal_eq_map_of_le (hI : I ≤ maximalIdeal R) (fg : I.FG) :
    haveI := isLocalRing_of_le hI
    maximalIdeal (AdicCompletion I R) = (maximalIdeal R).map (algebraMap R (AdicCompletion I R)) :=
  haveI := isLocalRing_of_le hI
  (eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I _ hI fg)).symm

variable [IsNoetherianRing R]

/-- The completion of a Noetherian local ring along an ideal contained in the maximal ideal has
the same Krull dimension as the ring. -/
@[stacks 07NV]
theorem ringKrullDim_eq (hI : I ≤ maximalIdeal R) :
    ringKrullDim (AdicCompletion I R) = ringKrullDim R :=
  haveI := isLocalRing_of_le hI
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map_of_le hI (IsNoetherian.noetherian I)).symm

/-- The completion of a Noetherian local ring along an ideal contained in the maximal ideal is
regular if and only if the ring is. -/
@[stacks 07NY]
theorem isRegularLocalRing_iff (hI : I ≤ maximalIdeal R) :
    IsRegularLocalRing (AdicCompletion I R) ↔ IsRegularLocalRing R :=
  haveI := isLocalRing_of_le hI
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map_of_le hI (IsNoetherian.noetherian I)).symm

/-- The completion of a Noetherian local ring along an ideal contained in the maximal ideal is
Cohen–Macaulay if and only if the ring is. -/
@[stacks 07NX]
theorem isCohenMacaulay_self_iff (hI : I ≤ maximalIdeal R) :
    haveI := isLocalRing_of_le hI
    Module.IsCohenMacaulay (AdicCompletion I R) (AdicCompletion I R) ↔
      Module.IsCohenMacaulay R R :=
  haveI := isLocalRing_of_le hI
  Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map_of_le hI (IsNoetherian.noetherian I)).symm

end

/-- The completion of a regular local ring at its maximal ideal is regular. -/
instance {R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
  (isRegularLocalRing_iff le_rfl).mpr ‹_›

/-- Completing a Noetherian ring `R` at a maximal ideal `p` yields a regular local ring if and only
if any localization `Rₚ` of `R` at `p` is a regular local ring. -/
theorem isRegularLocalRing_iff_of_isMaximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    IsRegularLocalRing (AdicCompletion p R) ↔ IsRegularLocalRing Rₚ := by
  have : IsNoetherianRing Rₚ := IsLocalization.isNoetherianRing p.primeCompl Rₚ ‹_›
  let e := (_root_.AdicCompletion.equivMaximalIdealOfAtPrime p Rₚ).toRingEquiv
  exact ⟨fun _ ↦ (isRegularLocalRing_iff le_rfl).mp (.of_ringEquiv e),
    fun _ ↦ .of_ringEquiv (R := AdicCompletion (maximalIdeal Rₚ) Rₚ) e.symm⟩

end TauCeti.AdicCompletion

section MaximalIdealComparison

open AdicCompletion IsLocalRing

namespace AdicCompletion

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [IsLocalRing S] [IsLocalRing S']

/-- If an `R`-algebra homomorphism `f : S →ₐ[R] S'` of local rings induces bijections
`S ⧸ J ^ n → S' ⧸ (J S') ^ n` for an ideal `J ≤ 𝔪_S` and every `n ≥ 1`, then `f` induces a
bijection between the maximal-ideal-adic completions of `S` and `S'`. -/
theorem mapₐ_maximalIdeal_bijective_of_quotientMap_pow_bijective (f : S →ₐ[R] S')
    (hf : maximalIdeal S ≤ (maximalIdeal S').comap f) {J : Ideal S} (hJ : J ≤ maximalIdeal S)
    (hbij : f.toRingHom.QuotientMapPowBijective J) :
    Function.Bijective (mapₐ f hf) := by
  refine mapₐ_bijective f hf fun n ↦ ?_
  rcases n with _ | n
  · exact f.toRingHom.quotientMap_maximalIdeal_pow_bijective
      (K := J ^ 1) (by simp) (f.toRingHom.quotientMap_bijective_congr rfl rfl
        (Ideal.map_pow f.toRingHom J 1).symm (hbij 1 le_rfl) (H₂ := Ideal.le_comap_map))
  · exact f.toRingHom.quotientMap_maximalIdeal_pow_bijective
      (Ideal.pow_right_mono hJ (n + 1))
      (f.toRingHom.quotientMap_bijective_congr rfl rfl (Ideal.map_pow f.toRingHom J (n + 1)).symm
        (hbij (n + 1) (Nat.succ_pos n)) (H₂ := Ideal.le_comap_map))

end AdicCompletion

namespace RingHom

variable {T T' : Type*} [CommRing T] [CommRing T'] [IsLocalRing T] [IsLocalRing T']
  (f : T →+* T') {J : Ideal T} (hJ : J ≤ maximalIdeal T) (hbij : f.QuotientMapPowBijective J)

omit [IsLocalRing T] [IsLocalRing T'] in
private theorem toRingHom_ofId_toAlgebra :
    letI : Algebra T T' := f.toAlgebra
    (Algebra.ofId T T').toRingHom = f :=
  RingHom.ext fun x ↦ by simp [RingHom.algebraMap_toAlgebra]

/-- The canonical ring isomorphism between the maximal-ideal-adic completions of local rings `T`
and `T'` induced by a ring homomorphism `f : T →+* T'` that is an isomorphism modulo `J ^ n`
for an ideal `J ≤ 𝔪_T` and every `n ≥ 1`. -/
noncomputable def adicCompletionMaximalIdealRingEquivOfQuotientMap :
    AdicCompletion (maximalIdeal T) T ≃+* AdicCompletion (maximalIdeal T') T' :=
  letI : Algebra T T' := f.toAlgebra
  have hle : maximalIdeal T ≤ (maximalIdeal T').comap (Algebra.ofId T T') := fun x hx ↦ by
    rw [Ideal.mem_comap, Algebra.ofId_apply, RingHom.algebraMap_toAlgebra]
    exact f.maximalIdeal_le_comap_of_quotientMap_pow_bijective hJ hbij hx
  (AlgEquiv.ofBijective
    (mapₐ (Algebra.ofId T T') hle)
    (AdicCompletion.mapₐ_maximalIdeal_bijective_of_quotientMap_pow_bijective
      (Algebra.ofId T T') hle hJ
      (fun n hn ↦ f.quotientMap_bijective_congr (toRingHom_ofId_toAlgebra f).symm rfl rfl
        (hbij n hn)))).toRingEquiv

/-- Modulo `𝔪_{T'} ^ n`, `adicCompletionMaximalIdealRingEquivOfQuotientMap f` is the quotient map
induced by `f`. -/
@[simp]
theorem evalₐ_adicCompletionMaximalIdealRingEquivOfQuotientMap (n : ℕ)
    (x : AdicCompletion (maximalIdeal T) T) :
    evalₐ (maximalIdeal T') n (f.adicCompletionMaximalIdealRingEquivOfQuotientMap hJ hbij x) =
      Ideal.quotientMap (maximalIdeal T' ^ n) f
        (Ideal.pow_le_comap_pow_of_le_comap f
          (f.maximalIdeal_le_comap_of_quotientMap_pow_bijective hJ hbij) n)
        (evalₐ (maximalIdeal T) n x) := by
  let : Algebra T T' := f.toAlgebra
  rw [adicCompletionMaximalIdealRingEquivOfQuotientMap, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.ofBijective_apply, evalₐ_mapₐ]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal T) n x)
  rw [← ht, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun (toRingHom_ofId_toAlgebra f) t)

/-- On elements of `T`, `adicCompletionMaximalIdealRingEquivOfQuotientMap f` applies `f`. -/
@[simp]
theorem adicCompletionMaximalIdealRingEquivOfQuotientMap_of (x : T) :
    f.adicCompletionMaximalIdealRingEquivOfQuotientMap hJ hbij (of (maximalIdeal T) T x) =
      of (maximalIdeal T') T' (f x) := by
  let : Algebra T T' := f.toAlgebra
  rw [adicCompletionMaximalIdealRingEquivOfQuotientMap, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.ofBijective_apply, mapₐ_of]
  exact congrArg (of (maximalIdeal T') T') (RingHom.congr_fun (toRingHom_ofId_toAlgebra f) x)

/-- Composing two maximal-ideal completion ring isomorphisms induced by `f` and `g` yields the
isomorphism induced by `h = g.comp f`. -/
theorem adicCompletionMaximalIdealRingEquivOfQuotientMap_trans {T'' : Type*} [CommRing T'']
    [IsLocalRing T''] (f : T →+* T') {J : Ideal T} (hJ : J ≤ maximalIdeal T)
    (hbijf : f.QuotientMapPowBijective J)
    (g : T' →+* T'') {J' : Ideal T'} (hJ' : J' ≤ maximalIdeal T')
    (hbijg : g.QuotientMapPowBijective J')
    {h : T →+* T''} (hfg : g.comp f = h) {K : Ideal T} (hK : K ≤ maximalIdeal T)
    (hbijh : h.QuotientMapPowBijective K) :
    (f.adicCompletionMaximalIdealRingEquivOfQuotientMap hJ hbijf).trans
        (g.adicCompletionMaximalIdealRingEquivOfQuotientMap hJ' hbijg) =
      h.adicCompletionMaximalIdealRingEquivOfQuotientMap hK hbijh := by
  subst hfg
  refine RingEquiv.ext fun x ↦ ext_evalₐ fun n ↦ ?_
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal T) n x)
  simp only [RingEquiv.trans_apply,
    RingHom.evalₐ_adicCompletionMaximalIdealRingEquivOfQuotientMap, ← hs, Ideal.quotientMap_mk,
    RingHom.comp_apply]

end RingHom

end MaximalIdealComparison
