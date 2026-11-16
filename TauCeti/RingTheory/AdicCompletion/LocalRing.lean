/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.AdicCompletion.AlgHom
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.CohenMacaulay.Flat
public import TauCeti.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Completions of local rings and their invariants

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and let `R̂` be its `𝔪`-adic completion.
Then `R̂` is a Noetherian local ring, flat over `R`, with maximal ideal `𝔪 R̂` and the same residue
field. This file shows that `R̂` has the same Krull dimension as `R`, that `R̂` is regular if and
only if `R` is, and that `R̂` is Cohen–Macaulay if and only if `R` is. Together with Mathlib's
`AdicCompletion.spanFinrank_maximalIdeal_eq`, these are among the invariants of a local ring that
are unchanged by completion.

More generally, for any local ring `R` and finitely generated ideal `I ≤ 𝔪`, the `I`-adic
completion `AdicCompletion I R` is again a local ring, with maximal ideal `𝔪 · AdicCompletion I R`,
and `R → AdicCompletion I R` is a local homomorphism.

Finally, if `f : R → S` is a homomorphism of local rings and `J ≤ 𝔪_R` is an ideal such that
`R ⧸ J → S ⧸ J S` is bijective, then `f` is a local homomorphism with `𝔪_R S = 𝔪_S`; if moreover
`R ⧸ J ^ n → S ⧸ (J S) ^ n` is bijective for every `n ≥ 1`, then `f` induces bijections
`R ⧸ 𝔪_R ^ n → S ⧸ 𝔪_S ^ n` for all `n` and hence an isomorphism between the maximal-ideal-adic
completions of `R` and `S`.

## Main results

* `TauCeti.AdicCompletion.ringKrullDim_eq`: `R̂` and `R` have the same Krull dimension.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff`: `R̂` is regular if and only if `R` is.
* `TauCeti.AdicCompletion.isCohenMacaulay_self_iff`: `R̂` is Cohen–Macaulay if and only if `R` is.
* `AdicCompletion.isLocalRing_of_le_maximalIdeal`,
  `AdicCompletion.maximalIdeal_eq_map_of_le_maximalIdeal`,
  `AdicCompletion.algebraMap_isLocalHom_of_le_maximalIdeal`: completing a local ring along a
  finitely generated proper ideal produces a local ring with extended maximal ideal.
* `IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective`,
  `IsLocalRing.isLocalHom_of_quotientMap_bijective`,
  `IsLocalRing.quotientMap_maximalIdeal_pow_bijective`: mod-`J ^ n` isomorphisms for `J ≤ 𝔪_R`
  force `𝔪_R S = 𝔪_S`, locality of `f`, and mod-`𝔪 ^ n` isomorphisms.
* `AdicCompletion.mapₐ_maximalIdeal_bijective`,
  `AdicCompletion.maximalIdealEquivOfQuotientMap`: the induced isomorphism between maximal-ideal
  completions.

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

section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The completion of a Noetherian local ring at its maximal ideal has the same Krull dimension as
the ring. -/
@[stacks 07NV]
theorem ringKrullDim_eq : ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R :=
  ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq AdicCompletion.maximalIdeal_eq_map.symm

/-- The completion of a Noetherian local ring at its maximal ideal is regular if and only if the
ring is. -/
@[stacks 07NY]
theorem isRegularLocalRing_iff :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) ↔ IsRegularLocalRing R :=
  isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq AdicCompletion.maximalIdeal_eq_map.symm

/-- The completion of a Noetherian local ring at its maximal ideal is Cohen–Macaulay if and only if
the ring is. -/
@[stacks 07NX]
theorem isCohenMacaulay_self_iff :
    Module.IsCohenMacaulay (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R) ↔ Module.IsCohenMacaulay R R :=
  Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    AdicCompletion.maximalIdeal_eq_map.symm

end

/-- The completion of a regular local ring at its maximal ideal is regular. -/
instance {R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
  isRegularLocalRing_iff.mpr ‹_›

end TauCeti.AdicCompletion

namespace IsLocalRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

private theorem quotientMap_bijective_congr {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ = I₂) (hJ : J₁ = J₂)
    {H₁ : I₁ ≤ J₁.comap f} {H₂ : I₂ ≤ J₂.comap f}
    (h : Function.Bijective (Ideal.quotientMap J₁ f H₁)) :
    Function.Bijective (Ideal.quotientMap J₂ f H₂) := by
  subst hI hJ
  exact h

/-- If `f : R →+* S` is a homomorphism of local rings and `J ≤ 𝔪_R` is an ideal such that
`R ⧸ J → S ⧸ J S` is bijective, then `𝔪_R` generates `𝔪_S`. -/
theorem map_maximalIdeal_eq_of_quotientMap_bijective (f : R →+* S) {J : Ideal R}
    (hJ : J ≤ maximalIdeal R) {H : J ≤ (J.map f).comap f}
    (hbij : Function.Bijective (Ideal.quotientMap (J.map f) f H)) :
    (maximalIdeal R).map f = maximalIdeal S := by
  let e : R ⧸ J ≃+* S ⧸ J.map f := RingEquiv.ofBijective _ hbij
  have hJne : J ≠ ⊤ := (lt_of_le_of_lt hJ (maximalIdeal.isMaximal R).lt_top).ne
  have : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
  have : Nontrivial (S ⧸ J.map f) := e.injective.nontrivial
  have hJS : J.map f ≤ maximalIdeal S := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  have : IsLocalRing (S ⧸ J.map f) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmaxR : ((maximalIdeal R).map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hJ)
  have hmaxS : (((maximalIdeal R).map (Ideal.Quotient.mk J)).map e.toRingHom).IsMaximal :=
    Ideal.map_isMaximal_of_equiv e
  have heq : ((maximalIdeal R).map (Ideal.Quotient.mk J)).map e.toRingHom =
      (maximalIdeal S).map (Ideal.Quotient.mk (J.map f)) := by
    rw [eq_maximalIdeal hmaxS, map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  have hcomp : ((maximalIdeal R).map (Ideal.Quotient.mk J)).map e.toRingHom =
      ((maximalIdeal R).map f).map (Ideal.Quotient.mk (J.map f)) := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg ((maximalIdeal R).map ·) (Ideal.quotientMap_comp_mk H)
  rw [hcomp] at heq
  have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk (J.map f))) heq
  rwa [Ideal.comap_map_mk (Ideal.map_mono hJ), Ideal.comap_map_mk hJS] at hcomap

/-- If `f : R →+* S` is a homomorphism of local rings and `J ≤ 𝔪_R` is an ideal such that
`R ⧸ J → S ⧸ J S` is bijective, then `f` is a local homomorphism. -/
theorem isLocalHom_of_quotientMap_bijective (f : R →+* S) {J : Ideal R}
    (hJ : J ≤ maximalIdeal R) {H : J ≤ (J.map f).comap f}
    (hbij : Function.Bijective (Ideal.quotientMap (J.map f) f H)) :
    IsLocalHom f :=
  ((local_hom_tfae f).out 1 3).mpr (map_maximalIdeal_eq_of_quotientMap_bijective f hJ hbij).le

/-- If `f : R →+* S` is a homomorphism of local rings with `𝔪_R S = 𝔪_S` and `J ≤ 𝔪_R`, and
`R ⧸ J ^ n → S ⧸ (J S) ^ n` is bijective, then `R ⧸ 𝔪_R ^ n → S ⧸ 𝔪_S ^ n` is bijective. -/
theorem quotientMap_maximalIdeal_pow_bijective (f : R →+* S) {J : Ideal R}
    (hJ : J ≤ maximalIdeal R) (hm : (maximalIdeal R).map f = maximalIdeal S) (n : ℕ)
    {HJ : J ^ n ≤ ((J.map f) ^ n).comap f}
    (hbij : Function.Bijective (Ideal.quotientMap ((J.map f) ^ n) f HJ))
    {Hm : maximalIdeal R ^ n ≤ (maximalIdeal S ^ n).comap f} :
    Function.Bijective (Ideal.quotientMap (maximalIdeal S ^ n) f Hm) :=
  have hbij' := quotientMap_bijective_congr f rfl (Ideal.map_pow f J n).symm hbij
    (H₂ := Ideal.le_comap_map)
  quotientMap_bijective_congr f rfl (by rw [Ideal.map_pow, hm])
    (Ideal.quotientMap_bijective_of_le f (Ideal.pow_right_mono hJ n) hbij'
      (HJ := Ideal.le_comap_map))

end IsLocalRing

namespace AdicCompletion

section LeMaximalIdeal

variable {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}

/-- Completing a local ring `R` along any finitely generated ideal `I ≤ 𝔪_R` yields a local ring:
every maximal ideal of `AdicCompletion I R` contains `I · AdicCompletion I R`, so it corresponds to
the unique maximal ideal of `R ⧸ I`. -/
theorem isLocalRing_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) (hIfg : I.FG) :
    IsLocalRing (AdicCompletion I R) := by
  have hmax : ((maximalIdeal R).map (algebraMap R (AdicCompletion I R))).IsMaximal :=
    isMaximal_map_of_le I (maximalIdeal R) hI hIfg
  have hcomp : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    isAdicComplete_self I hIfg
  have hIne : I ≠ ⊤ := (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  refine IsLocalRing.of_unique_max_ideal ⟨_, hmax, fun q hq ↦ ?_⟩
  -- Every maximal ideal `q` of `AdicCompletion I R` contains `I · AdicCompletion I R`.
  have hIq : I.map (algebraMap R (AdicCompletion I R)) ≤ q :=
    (IsAdicComplete.le_jacobson _).trans (Ring.jacobson_le_of_isMaximal q)
  have hIm : I.map (algebraMap R (AdicCompletion I R)) ≤
      (maximalIdeal R).map (algebraMap R (AdicCompletion I R)) := Ideal.map_mono hI
  have hker : RingHom.ker (evalOneₐ I).toRingHom = I.map (algebraMap R (AdicCompletion I R)) :=
    ker_evalOneₐ_eq_map I hIfg
  have hqmax : (q.map (evalOneₐ I).toRingHom).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le (evalOneₐ_surjective I) (hker ▸ hIq)
  have hmmax : (((maximalIdeal R).map (algebraMap R (AdicCompletion I R))).map
      (evalOneₐ I).toRingHom).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le (evalOneₐ_surjective I) (hker ▸ hIm)
  have heq : q.map (evalOneₐ I).toRingHom =
      ((maximalIdeal R).map (algebraMap R (AdicCompletion I R))).map (evalOneₐ I).toRingHom :=
    (eq_maximalIdeal hqmax).trans (eq_maximalIdeal hmmax).symm
  have hcomap := congrArg (Ideal.comap (evalOneₐ I).toRingHom) heq
  rw [Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I),
    Ideal.comap_map_of_surjective' (evalOneₐ I).toRingHom (evalOneₐ_surjective I), hker,
    sup_eq_left.mpr hIq, sup_eq_left.mpr hIm] at hcomap
  exact hcomap

/-- For a local ring `R` and a finitely generated ideal `I ≤ 𝔪_R`, the maximal ideal of
`AdicCompletion I R` is the extension of `𝔪_R`. -/
theorem maximalIdeal_eq_map_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) (hIfg : I.FG)
    [IsLocalRing (AdicCompletion I R)] :
    maximalIdeal (AdicCompletion I R) =
      (maximalIdeal R).map (algebraMap R (AdicCompletion I R)) :=
  (eq_maximalIdeal (isMaximal_map_of_le I (maximalIdeal R) hI hIfg)).symm

/-- For a local ring `R` and a finitely generated ideal `I ≤ 𝔪_R`, the canonical map
`R → AdicCompletion I R` is a local homomorphism. -/
theorem algebraMap_isLocalHom_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) (hIfg : I.FG) :
    IsLocalHom (algebraMap R (AdicCompletion I R)) := by
  have := isLocalRing_of_le_maximalIdeal hI hIfg
  exact ((local_hom_tfae (algebraMap R (AdicCompletion I R))).out 1 3).mpr
    (maximalIdeal_eq_map_of_le_maximalIdeal hI hIfg).ge

end LeMaximalIdeal

section MaximalIdealComparison

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']
  [IsLocalRing S] [IsLocalRing S']

private theorem map_maximalIdeal_of_pow_bijective (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
    (maximalIdeal S).map f.toRingHom = maximalIdeal S' :=
  map_maximalIdeal_eq_of_quotientMap_bijective f.toRingHom hJ
    (quotientMap_bijective_congr f.toRingHom (pow_one J) (pow_one _) (hbij 1 le_rfl)
      (H₂ := Ideal.le_comap_map))

/-- If an `R`-algebra homomorphism `f : S →ₐ[R] S'` of local rings induces bijections
`S ⧸ J ^ n → S' ⧸ (J S') ^ n` for an ideal `J ≤ 𝔪_S` and every `n ≥ 1`, then `f` induces a
bijection between the maximal-ideal-adic completions of `S` and `S'`. -/
theorem mapₐ_maximalIdeal_bijective (f : S →ₐ[R] S') {J : Ideal S} (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (hf : maximalIdeal S ≤ (maximalIdeal S').comap f) :
    Function.Bijective (mapₐ f hf) := by
  have hm := map_maximalIdeal_of_pow_bijective f hJ hbij
  refine mapₐ_bijective f hf fun n ↦ ?_
  rcases n with _ | n
  · have : Subsingleton (S ⧸ maximalIdeal S ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    have : Subsingleton (S' ⧸ maximalIdeal S' ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · exact quotientMap_maximalIdeal_pow_bijective f.toRingHom hJ hm (n + 1)
      (hbij (n + 1) (Nat.succ_pos n))

/-- The canonical isomorphism between the maximal-ideal-adic completions of local rings `S` and
`S'` induced by an `R`-algebra homomorphism `f : S →ₐ[R] S'` that is an isomorphism modulo `J ^ n`
for an ideal `J ≤ 𝔪_S` and every `n ≥ 1`. -/
noncomputable def maximalIdealEquivOfQuotientMap (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
    AdicCompletion (maximalIdeal S) S ≃ₐ[R] AdicCompletion (maximalIdeal S') S' :=
  AlgEquiv.ofBijective
    (mapₐ f ((map_maximalIdeal_of_pow_bijective f hJ hbij) ▸ Ideal.le_comap_map))
    (mapₐ_maximalIdeal_bijective f hJ hbij _)

/-- On elements of `S`, `maximalIdealEquivOfQuotientMap f` applies `f`. -/
@[simp]
theorem maximalIdealEquivOfQuotientMap_of (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) (x : S) :
    maximalIdealEquivOfQuotientMap f hJ hbij (of (maximalIdeal S) S x) =
      of (maximalIdeal S') S' (f x) :=
  mapₐ_of f _ x

/-- The underlying map of `maximalIdealEquivOfQuotientMap f` is `AdicCompletion.mapₐ f`. -/
theorem maximalIdealEquivOfQuotientMap_apply (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (h : maximalIdeal S ≤ (maximalIdeal S').comap f.toRingHom)
    (x : AdicCompletion (maximalIdeal S) S) :
    maximalIdealEquivOfQuotientMap f hJ hbij x = mapₐ f h x := by
  simp [maximalIdealEquivOfQuotientMap]

end MaximalIdealComparison

end AdicCompletion
