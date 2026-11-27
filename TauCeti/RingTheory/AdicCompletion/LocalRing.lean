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
`R → AdicCompletion I R` are local homomorphisms. Finally, if `f : S →ₐ[R] S'` is an `R`-algebra
homomorphism of local rings and `J ≤ 𝔪_S` is an ideal such that `S ⧸ J ^ n → S' ⧸ (J S') ^ n` is
bijective for every `n ≥ 1`, then `f` induces an isomorphism between the maximal-ideal-adic
completions of `S` and `S'`.

## Main results

* `TauCeti.AdicCompletion.isLocalRing_of_le`: the completion of a local ring along a finitely
  generated ideal `I ⊆ 𝔪` is a local ring.
* `TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le`: its maximal ideal is `𝔪 R̂`.
* `TauCeti.AdicCompletion.ringKrullDim_eq`: `R̂` and `R` have the same Krull dimension.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff`: `R̂` is regular if and only if `R` is.
* `TauCeti.AdicCompletion.isCohenMacaulay_self_iff`: `R̂` is Cohen–Macaulay if and only if `R` is.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff_of_isMaximal`: completing a Noetherian ring `R` at
  a maximal ideal `p` is regular if and only if any localization `Rₚ` of `R` at `p` is regular.
* `TauCeti.AdicCompletion.isLocalHom_evalOneₐ_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.isLocalHom_algebraMap_of_le_maximalIdeal`: local homomorphisms into and
  out of `AdicCompletion I R` for any ideal `I ≤ 𝔪`.
* `AdicCompletion.mapₐ_maximalIdeal_bijective_of_quotientMap_pow_bijective`,
  `AlgHom.adicCompletionMaximalIdealEquivOfQuotientMap`,
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

/-- The completion of a local ring along a finitely generated ideal contained in the maximal ideal
is a local ring: it is complete along `I R̂`, which therefore lies in its Jacobson radical, and its
quotient by `I R̂` is the local ring `R ⧸ I`. -/
theorem isLocalRing_of_le (hI : I ≤ maximalIdeal R) (fg : I.FG) :
    IsLocalRing (AdicCompletion I R) := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := AdicCompletion.isAdicComplete_self I fg
  have : IsLocalHom (AdicCompletion.evalOneₐ I).toRingHom := by
    rw [RingHom.isLocalHom_iff_ker_le_jacobson (AdicCompletion.evalOneₐ_surjective I),
      AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact IsAdicComplete.le_jacobson _
  exact (AdicCompletion.evalOneₐ I).toRingHom.domain_isLocalRing

/-- The maximal ideal of the completion of a local ring along a finitely generated ideal `I ⊆ 𝔪`
is generated by the maximal ideal `𝔪` of the ring. -/
theorem maximalIdeal_eq_map_of_le (hI : I ≤ maximalIdeal R) (fg : I.FG) :
    haveI := isLocalRing_of_le hI fg
    maximalIdeal (AdicCompletion I R) = (maximalIdeal R).map (algebraMap R (AdicCompletion I R)) :=
  haveI := isLocalRing_of_le hI fg
  (eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I _ hI fg)).symm

variable [IsNoetherianRing R]

/-- The completion of a Noetherian local ring along an ideal contained in the maximal ideal has
the same Krull dimension as the ring. -/
@[stacks 07NV]
theorem ringKrullDim_eq (hI : I ≤ maximalIdeal R) :
    ringKrullDim (AdicCompletion I R) = ringKrullDim R :=
  haveI := isLocalRing_of_le hI (IsNoetherian.noetherian I)
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map_of_le hI (IsNoetherian.noetherian I)).symm

/-- The completion of a Noetherian local ring along an ideal contained in the maximal ideal is
regular if and only if the ring is. -/
@[stacks 07NY]
theorem isRegularLocalRing_iff (hI : I ≤ maximalIdeal R) :
    IsRegularLocalRing (AdicCompletion I R) ↔ IsRegularLocalRing R :=
  haveI := isLocalRing_of_le hI (IsNoetherian.noetherian I)
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map_of_le hI (IsNoetherian.noetherian I)).symm

/-- The completion of a Noetherian local ring along an ideal contained in the maximal ideal is
Cohen–Macaulay if and only if the ring is. -/
@[stacks 07NX]
theorem isCohenMacaulay_self_iff (hI : I ≤ maximalIdeal R) :
    haveI := isLocalRing_of_le hI (IsNoetherian.noetherian I)
    Module.IsCohenMacaulay (AdicCompletion I R) (AdicCompletion I R) ↔
      Module.IsCohenMacaulay R R :=
  haveI := isLocalRing_of_le hI (IsNoetherian.noetherian I)
  Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map_of_le hI (IsNoetherian.noetherian I)).symm

end

/-- The completion of a regular local ring at its maximal ideal is regular. -/
instance {R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
  (isRegularLocalRing_iff le_rfl).mpr ‹_›

section LeMaximalIdeal

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

end LeMaximalIdeal

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
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
    Function.Bijective (mapₐ f hf) := by
  refine mapₐ_bijective f hf fun n ↦ ?_
  rcases n with _ | n
  · exact f.toRingHom.quotientMap_maximalIdeal_pow_bijective
      (K := J ^ 1) (by simp) (f.toRingHom.quotientMap_bijective_congr rfl
        (Ideal.map_pow f.toRingHom J 1).symm (hbij 1 le_rfl) (H₂ := Ideal.le_comap_map))
  · exact f.toRingHom.quotientMap_maximalIdeal_pow_bijective
      (Ideal.pow_right_mono hJ (n + 1))
      (f.toRingHom.quotientMap_bijective_congr rfl (Ideal.map_pow f.toRingHom J (n + 1)).symm
        (hbij (n + 1) (Nat.succ_pos n)) (H₂ := Ideal.le_comap_map))

end AdicCompletion

namespace AlgHom

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [IsLocalRing S] [IsLocalRing S']

section Equiv

variable (f : S →ₐ[R] S') {J : Ideal S} (hJ : J ≤ maximalIdeal S)
  (hbij : ∀ n : ℕ, 1 ≤ n →
    Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))

include hJ hbij

/-- The canonical isomorphism between the maximal-ideal-adic completions of local rings `S` and
`S'` induced by an `R`-algebra homomorphism `f : S →ₐ[R] S'` that is an isomorphism modulo `J ^ n`
for an ideal `J ≤ 𝔪_S` and every `n ≥ 1`. -/
noncomputable def adicCompletionMaximalIdealEquivOfQuotientMap :
    AdicCompletion (maximalIdeal S) S ≃ₐ[R] AdicCompletion (maximalIdeal S') S' :=
  AlgEquiv.ofBijective
    (mapₐ f (f.toRingHom.maximalIdeal_le_comap_of_quotientMap_pow_bijective hJ hbij))
    (AdicCompletion.mapₐ_maximalIdeal_bijective_of_quotientMap_pow_bijective f _ hJ hbij)

/-- As an algebra homomorphism, `adicCompletionMaximalIdealEquivOfQuotientMap f` is
`AdicCompletion.mapₐ f`. -/
@[simp]
theorem toAlgHom_adicCompletionMaximalIdealEquivOfQuotientMap :
    (f.adicCompletionMaximalIdealEquivOfQuotientMap hJ hbij :
        AdicCompletion (maximalIdeal S) S →ₐ[R] AdicCompletion (maximalIdeal S') S') =
      mapₐ f (f.toRingHom.maximalIdeal_le_comap_of_quotientMap_pow_bijective hJ hbij) := by
  ext; rfl

/-- Modulo `𝔪_{S'} ^ n`, `adicCompletionMaximalIdealEquivOfQuotientMap f` is the quotient map
induced by `f`. -/
@[simp]
theorem evalₐ_adicCompletionMaximalIdealEquivOfQuotientMap (n : ℕ)
    (x : AdicCompletion (maximalIdeal S) S) :
    evalₐ (maximalIdeal S') n (f.adicCompletionMaximalIdealEquivOfQuotientMap hJ hbij x) =
      Ideal.quotientMap (maximalIdeal S' ^ n) (f : S →+* S')
        ((Ideal.pow_right_mono
          (f.toRingHom.maximalIdeal_le_comap_of_quotientMap_pow_bijective hJ hbij) n).trans
          (Ideal.le_comap_pow _ n))
        (evalₐ (maximalIdeal S) n x) := by
  exact evalₐ_mapₐ f _ n x

/-- On elements of `S`, `adicCompletionMaximalIdealEquivOfQuotientMap f` applies `f`. -/
@[simp]
theorem adicCompletionMaximalIdealEquivOfQuotientMap_of (x : S) :
    f.adicCompletionMaximalIdealEquivOfQuotientMap hJ hbij (of (maximalIdeal S) S x) =
      of (maximalIdeal S') S' (f x) := by
  exact mapₐ_of f _ x

/-- The underlying map of `adicCompletionMaximalIdealEquivOfQuotientMap f` is
`AdicCompletion.mapₐ f`. -/
theorem adicCompletionMaximalIdealEquivOfQuotientMap_apply
    (x : AdicCompletion (maximalIdeal S) S) :
    f.adicCompletionMaximalIdealEquivOfQuotientMap hJ hbij x =
      mapₐ f (f.toRingHom.maximalIdeal_le_comap_of_quotientMap_pow_bijective hJ hbij) x := by
  rfl

end Equiv

/-- Composing two maximal-ideal completion isomorphisms induced by `f` and `g` yields the
isomorphism induced by `h = g.comp f`. -/
theorem adicCompletionMaximalIdealEquivOfQuotientMap_trans {S'' : Type*} [CommRing S'']
    [Algebra R S''] [IsLocalRing S''] (f : S →ₐ[R] S') {J : Ideal S} (hJ : J ≤ maximalIdeal S)
    (hbijf : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (g : S' →ₐ[R] S'') {J' : Ideal S'} (hJ' : J' ≤ maximalIdeal S')
    (hbijg : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J'.map g.toRingHom) ^ n) g.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    {h : S →ₐ[R] S''} (hfg : g.comp f = h) {K : Ideal S} (hK : K ≤ maximalIdeal S)
    (hbijh : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((K.map h.toRingHom) ^ n) h.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
    (f.adicCompletionMaximalIdealEquivOfQuotientMap hJ hbijf).trans
        (g.adicCompletionMaximalIdealEquivOfQuotientMap hJ' hbijg) =
      h.adicCompletionMaximalIdealEquivOfQuotientMap hK hbijh := by
  subst hfg
  exact AlgEquiv.ext fun x ↦ by
    rw [AlgEquiv.trans_apply, AlgHom.adicCompletionMaximalIdealEquivOfQuotientMap_apply,
      AlgHom.adicCompletionMaximalIdealEquivOfQuotientMap_apply,
      AlgHom.adicCompletionMaximalIdealEquivOfQuotientMap_apply]
    exact mapₐ_mapₐ _ _ _ _ x

end AlgHom

namespace RingHom

variable {T T' : Type*} [CommRing T] [CommRing T'] [IsLocalRing T] [IsLocalRing T']
  (f : T →+* T') {J : Ideal T} (hJ : J ≤ maximalIdeal T)
  (hbij : ∀ n : ℕ, 1 ≤ n →
    Function.Bijective (Ideal.quotientMap ((J.map f) ^ n) f
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))

/-- The canonical ring isomorphism between the maximal-ideal-adic completions of local rings `T`
and `T'` induced by a ring homomorphism `f : T →+* T'` that is an isomorphism modulo `J ^ n`
for an ideal `J ≤ 𝔪_T` and every `n ≥ 1`. -/
noncomputable def adicCompletionMaximalIdealRingEquivOfQuotientMap :
    AdicCompletion (maximalIdeal T) T ≃+* AdicCompletion (maximalIdeal T') T' :=
  letI : Algebra T T' := f.toAlgebra
  ((Algebra.ofId T T').adicCompletionMaximalIdealEquivOfQuotientMap hJ hbij).toRingEquiv

/-- Modulo `𝔪_{T'} ^ n`, `adicCompletionMaximalIdealRingEquivOfQuotientMap f` is the quotient map
induced by `f`. -/
@[simp]
theorem evalₐ_adicCompletionMaximalIdealRingEquivOfQuotientMap (n : ℕ)
    (x : AdicCompletion (maximalIdeal T) T) :
    evalₐ (maximalIdeal T') n (f.adicCompletionMaximalIdealRingEquivOfQuotientMap hJ hbij x) =
      Ideal.quotientMap (maximalIdeal T' ^ n) f
        ((Ideal.pow_right_mono
          (f.maximalIdeal_le_comap_of_quotientMap_pow_bijective hJ hbij) n).trans
          (Ideal.le_comap_pow _ n))
        (evalₐ (maximalIdeal T) n x) := by
  let : Algebra T T' := f.toAlgebra
  exact (Algebra.ofId T T').evalₐ_adicCompletionMaximalIdealEquivOfQuotientMap hJ hbij n x

/-- On elements of `T`, `adicCompletionMaximalIdealRingEquivOfQuotientMap f` applies `f`. -/
@[simp]
theorem adicCompletionMaximalIdealRingEquivOfQuotientMap_of (x : T) :
    f.adicCompletionMaximalIdealRingEquivOfQuotientMap hJ hbij (of (maximalIdeal T) T x) =
      of (maximalIdeal T') T' (f x) := by
  let : Algebra T T' := f.toAlgebra
  exact (Algebra.ofId T T').adicCompletionMaximalIdealEquivOfQuotientMap_of hJ hbij x

/-- Composing two maximal-ideal completion ring isomorphisms induced by `f` and `g` yields the
isomorphism induced by `h = g.comp f`. -/
theorem adicCompletionMaximalIdealRingEquivOfQuotientMap_trans {T'' : Type*} [CommRing T'']
    [IsLocalRing T''] (f : T →+* T') {J : Ideal T} (hJ : J ≤ maximalIdeal T)
    (hbijf : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f) ^ n) f
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (g : T' →+* T'') {J' : Ideal T'} (hJ' : J' ≤ maximalIdeal T')
    (hbijg : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J'.map g) ^ n) g
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    {h : T →+* T''} (hfg : g.comp f = h) {K : Ideal T} (hK : K ≤ maximalIdeal T)
    (hbijh : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((K.map h) ^ n) h
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
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
