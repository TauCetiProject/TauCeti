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
public import TauCeti.RingTheory.RegularLocalRing.Flat

import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Dimension, regularity, Cohen–Macaulay property, and comparison of local-ring completions

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and let `R̂` be its `𝔪`-adic completion.
Then `R̂` is a Noetherian local ring, flat over `R`, with maximal ideal `𝔪 R̂` and the same residue
field. This file shows that `R̂` has the same Krull dimension as `R`, that `R̂` is regular if and
only if `R` is, and that `R̂` is Cohen–Macaulay if and only if `R` is. Together with Mathlib's
`AdicCompletion.spanFinrank_maximalIdeal_eq`, these are among the invariants of a local ring that
are unchanged by completion, and therefore coincide for any two Noetherian local rings with
isomorphic maximal-ideal-adic completions.

For any commutative ring `R` and any ideal `I`, the projection `AdicCompletion I R → R ⧸ I` is a
local homomorphism (with no finite-generation assumption on `I`). Consequently, for any local ring
`R` and any ideal `I ≤ 𝔪`, the `I`-adic completion of `R` is again a local ring, the canonical map
`R → R̂` is local (more generally whenever `I ≤ Ring.jacobson R`), and when `I` is finitely
generated the maximal ideal of `R̂` is `𝔪 R̂`. Moreover, if a ring homomorphism `f : R →+* S`
between local rings induces surjections `R ⧸ K → S ⧸ L` with `L ≤ 𝔪_S`, then `f` is local and
`𝔪_R S ⊔ L = 𝔪_S`; if `f` induces bijections `R ⧸ I ^ n → S ⧸ J ^ n` for all `n ≥ 1` (with
`J ≤ 𝔪_S` and `I ≤ f⁻¹ J`), then `f` induces an isomorphism of maximal-ideal-adic completions.

## Main results

* `TauCeti.AdicCompletion.ringKrullDim_eq`: `R̂` and `R` have the same Krull dimension.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff`: `R̂` is regular if and only if `R` is.
* `TauCeti.AdicCompletion.isCohenMacaulay_self_iff`: `R̂` is Cohen–Macaulay if and only if `R` is.
* `TauCeti.AdicCompletion.isLocalHom_evalOneₐ`,
  `TauCeti.AdicCompletion.isLocalRing_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.algebraMap_isLocalHom_of_le_jacobson`,
  `TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le_maximalIdeal`: completion of a local ring
  along any ideal `I ≤ 𝔪` is local, the canonical map `R → R̂` is local whenever
  `I ≤ Ring.jacobson R`, and the maximal ideal of `R̂` is `𝔪 R̂` when `I` is finitely generated.
* `TauCeti.AdicCompletion.maximalIdealCompletionEquiv`: a ring homomorphism between local rings
  inducing bijections modulo `I ^ n` and `J ^ n` for all `n ≥ 1` induces an isomorphism of
  maximal-ideal-adic completions.
* `TauCeti.AdicCompletion.ringKrullDim_eq_of_maximalIdealCompletionEquiv`,
  `TauCeti.AdicCompletion.isRegularLocalRing_iff_of_maximalIdealCompletionEquiv`,
  `TauCeti.AdicCompletion.isCohenMacaulay_self_iff_of_maximalIdealCompletionEquiv`: Noetherian local
  rings with isomorphic maximal-ideal-adic completions share Krull dimension, regularity, and the
  Cohen–Macaulay property.

## References

* [Stacks Project, Lemma 15.44.1](https://stacks.math.columbia.edu/tag/07NV), the dimension of
  the completion.
* [Stacks Project, Lemma 15.44.3](https://stacks.math.columbia.edu/tag/07NX), the Cohen–Macaulay
  property of the completion.
* [Stacks Project, Lemma 15.44.4](https://stacks.math.columbia.edu/tag/07NY), regularity of the
  completion.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

section CompletionInvariance

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
        (AdicCompletion (maximalIdeal R) R) ↔
      Module.IsCohenMacaulay R R :=
  Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    AdicCompletion.maximalIdeal_eq_map.symm

end CompletionInvariance

/-- The completion of a regular local ring at its maximal ideal is regular. -/
instance {R : Type*} [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
  isRegularLocalRing_iff.mpr ‹_›

section CompletionOfSubideal

/-- If the reduction of `x ∈ AdicCompletion I R` modulo `I` is a unit, then its reduction modulo
`I ^ n` is a unit for every `n`. -/
private theorem isUnit_evalₐ_of_isUnit_evalOneₐ {R : Type*} [CommRing R] {I : Ideal R}
    {x : AdicCompletion I R} (hx : IsUnit (AdicCompletion.evalOneₐ I x)) (n : ℕ) :
    IsUnit (AdicCompletion.evalₐ I n x) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (R ⧸ I ^ 0) := by
      rw [pow_zero]; exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    exact isUnit_of_subsingleton _
  · let f : R ⧸ I ^ n →+* R ⧸ I := Ideal.Quotient.factor (Ideal.pow_le_self hn)
    have hfx : f (AdicCompletion.evalₐ I n x) = AdicCompletion.evalOneₐ I x := by
      rw [← AdicCompletion.factorₐ_evalₐ_one,
        ← AdicCompletion.factor_evalₐ (Nat.one_le_iff_ne_zero.mpr hn) x]
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
      simp [f, ← hr]
    obtain ⟨b, hb⟩ :=
      Ideal.Quotient.factor_surjective (Ideal.pow_le_self hn) (↑hx.unit⁻¹ : R ⧸ I)
    have hnil : IsNilpotent (1 - AdicCompletion.evalₐ I n x * b) := by
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (1 - AdicCompletion.evalₐ I n x * b)
      have hrI : r ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change f (Ideal.Quotient.mk (I ^ n) r) = 0
        rw [hr, map_sub, map_one, map_mul, hfx, hb, IsUnit.mul_val_inv, sub_self]
      refine ⟨n, ?_⟩
      rw [← hr, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hrI n
    have hab : IsUnit (AdicCompletion.evalₐ I n x * b) := by
      simpa only [sub_sub_cancel] using hnil.isUnit_one_sub
    exact isUnit_of_mul_isUnit_left hab

/-- The canonical projection `AdicCompletion I R →+* R ⧸ I` is a local homomorphism: an element of
the completion is a unit whenever its reduction modulo `I` is a unit, with no finite-generation
hypothesis on `I`. -/
instance isLocalHom_evalOneₐ {R : Type*} [CommRing R] (I : Ideal R) :
    IsLocalHom (AdicCompletion.evalOneₐ I).toRingHom := by
  refine ⟨fun x hx ↦ ?_⟩
  have hunit := isUnit_evalₐ_of_isUnit_evalOneₐ hx
  choose y hy using fun n ↦ Ideal.Quotient.mk_surjective (↑(hunit n).unit⁻¹ : R ⧸ I ^ n)
  let c : AdicCompletion.AdicCauchySequence I R :=
    AdicCompletion.AdicCauchySequence.mk I R y fun n ↦ by
    have hmn := Nat.le_succ n
    have hmul : AdicCompletion.evalₐ I n x * Ideal.Quotient.mk (I ^ n) (y (n + 1)) = 1 := by
      have h1 : Ideal.Quotient.mk (I ^ n) (y (n + 1)) =
          Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
            (Ideal.Quotient.mk (I ^ (n + 1)) (y (n + 1))) := rfl
      rw [← AdicCompletion.factor_evalₐ hmn x, h1, ← map_mul, hy (n + 1), IsUnit.mul_val_inv,
        map_one]
    have heq : Ideal.Quotient.mk (I ^ n) (y n) = Ideal.Quotient.mk (I ^ n) (y (n + 1)) := by
      calc Ideal.Quotient.mk (I ^ n) (y n)
          = Ideal.Quotient.mk (I ^ n) (y n) *
              (AdicCompletion.evalₐ I n x * Ideal.Quotient.mk (I ^ n) (y (n + 1))) := by
            rw [hmul, mul_one]
        _ = (Ideal.Quotient.mk (I ^ n) (y n) * AdicCompletion.evalₐ I n x) *
              Ideal.Quotient.mk (I ^ n) (y (n + 1)) := (mul_assoc _ _ _).symm
        _ = Ideal.Quotient.mk (I ^ n) (y (n + 1)) := by
            rw [hy n, IsUnit.val_inv_mul, one_mul]
    rw [SModEq.sub_mem]
    simpa only [smul_eq_mul, Ideal.mul_top] using Ideal.Quotient.eq.mp heq
  refine isUnit_iff_exists_inv.mpr ⟨AdicCompletion.mk I R c, AdicCompletion.ext_evalₐ fun n ↦ ?_⟩
  rw [map_mul, map_one, AdicCompletion.evalₐ_mk]
  change AdicCompletion.evalₐ I n x * Ideal.Quotient.mk (I ^ n) (y n) = 1
  rw [hy n, IsUnit.mul_val_inv]

/-- For any ideal `I` contained in the Jacobson radical of `R`, the canonical map from `R` to its
`I`-adic completion is a local homomorphism. -/
theorem algebraMap_isLocalHom_of_le_jacobson {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I ≤ Ring.jacobson R) : IsLocalHom (algebraMap R (AdicCompletion I R)) := by
  have : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson hI
  refine ⟨fun x hx ↦ isUnit_of_map_unit (Ideal.Quotient.mk I) x ?_⟩
  rw [← AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk]
  exact hx.map (AdicCompletion.evalOneₐ I).toRingHom

variable {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}

/-- The completion of a local ring along any ideal contained in its maximal ideal is a local
ring. -/
theorem isLocalRing_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalRing (AdicCompletion I R) := by
  have : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI)
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  exact (AdicCompletion.evalOneₐ I).toRingHom.domain_isLocalRing

/-- For a local ring `R` and a finitely generated ideal `I ≤ 𝔪_R`, the maximal ideal of the
`I`-adic completion of `R` is the extension of `𝔪_R`. -/
theorem maximalIdeal_eq_map_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) (fg : I.FG) :
    haveI := isLocalRing_of_le_maximalIdeal hI
    maximalIdeal (AdicCompletion I R) = (maximalIdeal R).map (algebraMap R (AdicCompletion I R)) :=
  haveI := isLocalRing_of_le_maximalIdeal hI
  (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I (maximalIdeal R) hI fg)).symm

/-- For a local ring `R` and any ideal `I ≤ 𝔪_R`, the canonical map from `R` to its `I`-adic
completion is a local homomorphism. -/
theorem algebraMap_isLocalHom_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalHom (algebraMap R (AdicCompletion I R)) :=
  algebraMap_isLocalHom_of_le_jacobson
    (hI.trans (Ideal.jacobson_bot.symm.trans (jacobson_eq_maximalIdeal ⊥ bot_ne_top)).ge)

end CompletionOfSubideal

section MaximalIdealComparison

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (f : R →+* S)

/-- If a ring homomorphism `f : R →+* S` between local rings induces a surjection `R ⧸ K → S ⧸ L`
with `L ≤ 𝔪_S`, then `𝔪_R S ⊔ L = 𝔪_S`. -/
theorem map_maximalIdeal_sup_eq_of_quotientMap_surjective {K : Ideal R} {L : Ideal S}
    (hL : L ≤ maximalIdeal S) (hKL : K ≤ L.comap f)
    (hsurj : Function.Surjective (Ideal.quotientMap L f hKL)) :
    (maximalIdeal R).map f ⊔ L = maximalIdeal S := by
  have : Nontrivial (S ⧸ L) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hL)
  have : Nontrivial (R ⧸ K) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (S ⧸ L)
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    exact ⟨⟨x, y, fun h ↦ hab (congrArg _ h)⟩⟩
  have : IsLocalRing (R ⧸ K) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (S ⧸ L) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hcomp : (Ideal.quotientMap L f hKL).comp (Ideal.Quotient.mk K) =
      (Ideal.Quotient.mk L).comp f :=
    RingHom.ext fun _ ↦ rfl
  have hmap : ((maximalIdeal R).map f).map (Ideal.Quotient.mk L) =
      (maximalIdeal S).map (Ideal.Quotient.mk L) := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map,
      map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
      map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
      map_maximalIdeal_of_surjective _ hsurj]
  have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk L)) hmap
  simp only [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker] at hcomap
  exact hcomap.trans (sup_eq_left.mpr hL)

/-- If a ring homomorphism `f : R →+* S` between local rings induces a surjection `R ⧸ K → S ⧸ L`
with `L ≤ 𝔪_S`, then `f` is a local homomorphism. -/
theorem isLocalHom_of_quotientMap_surjective {K : Ideal R} {L : Ideal S}
    (hL : L ≤ maximalIdeal S) (hKL : K ≤ L.comap f)
    (hsurj : Function.Surjective (Ideal.quotientMap L f hKL)) :
    IsLocalHom f :=
  ((local_hom_tfae f).out 1 3).mpr
    (le_sup_left.trans_eq (map_maximalIdeal_sup_eq_of_quotientMap_surjective f hL hKL hsurj))

/-- If a ring homomorphism `f : R →+* S` between local rings induces a surjection `R ⧸ K → S ⧸ K S`
with `K S ≤ 𝔪_S`, then `𝔪_R S = 𝔪_S`. -/
theorem map_maximalIdeal_eq_of_quotientMap_surjective {K : Ideal R}
    (hK : K.map f ≤ maximalIdeal S)
    (hsurj : Function.Surjective (Ideal.quotientMap (K.map f) f Ideal.le_comap_map)) :
    (maximalIdeal R).map f = maximalIdeal S := by
  have : Nontrivial (S ⧸ K.map f) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hK)
  have : Nontrivial (R ⧸ K) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (S ⧸ K.map f)
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨y, rfl⟩ := hsurj b
    exact ⟨⟨x, y, fun h ↦ hab (congrArg _ h)⟩⟩
  have hKR : K ≤ maximalIdeal R := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp ‹_›)
  exact (sup_eq_left.mpr (Ideal.map_mono hKR)).symm.trans
    (map_maximalIdeal_sup_eq_of_quotientMap_surjective f hK Ideal.le_comap_map hsurj)

/-- If `f : R →+* S` between local rings induces a bijection `R ⧸ K → S ⧸ L` with `K ≤ 𝔪_R ^ m`
and `L ≤ 𝔪_S ^ m`, then `f` induces a bijection `R ⧸ 𝔪_R ^ m → S ⧸ 𝔪_S ^ m`. -/
theorem quotientMap_maximalIdeal_pow_bijective_of_quotientMap_bijective {K : Ideal R} {L : Ideal S}
    (hKL : K ≤ L.comap f) (hbij : Function.Bijective (Ideal.quotientMap L f hKL))
    {m : ℕ} (hKm : K ≤ maximalIdeal R ^ m) (hLm : L ≤ maximalIdeal S ^ m)
    {H : maximalIdeal R ^ m ≤ (maximalIdeal S ^ m).comap f} :
    Function.Bijective (Ideal.quotientMap (maximalIdeal S ^ m) f H) := by
  rcases eq_or_ne m 0 with rfl | hm
  · have : Subsingleton (R ⧸ maximalIdeal R ^ 0) := by
      rw [pow_zero]; exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    have : Subsingleton (S ⧸ maximalIdeal S ^ 0) := by
      rw [pow_zero]; exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩
  · have hL : L ≤ maximalIdeal S := hLm.trans (Ideal.pow_le_self hm)
    have : Nontrivial (S ⧸ L) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hL)
    let e : R ⧸ K ≃+* S ⧸ L := RingEquiv.ofBijective _ hbij
    have : Nontrivial (R ⧸ K) := e.symm.injective.nontrivial
    have : IsLocalRing (R ⧸ K) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalRing (S ⧸ L) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hpow : (maximalIdeal S ^ m).map (Ideal.Quotient.mk L) =
        ((maximalIdeal R ^ m).map (Ideal.Quotient.mk K)).map e.toRingHom := by
      rw [Ideal.map_pow, Ideal.map_pow, Ideal.map_pow,
        map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
        map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
        map_maximalIdeal_of_surjective e.toRingHom e.surjective]
    let eqTotal : R ⧸ maximalIdeal R ^ m ≃+* S ⧸ maximalIdeal S ^ m :=
      (DoubleQuot.quotQuotEquivQuotOfLE hKm).symm.trans
        ((Ideal.quotientEquiv _ _ e hpow).trans (DoubleQuot.quotQuotEquivQuotOfLE hLm))
    have heq : Ideal.quotientMap (maximalIdeal S ^ m) f H = eqTotal.toRingHom := by
      ext r
      rfl
    exact heq ▸ eqTotal.bijective

/-- If a ring homomorphism `f : R →+* S` between local rings induces bijections
`R ⧸ I ^ n → S ⧸ J ^ n` for all `n ≥ 1` (with `J ≤ 𝔪_S` and `I ≤ f⁻¹ J`), then `f` induces a ring
isomorphism between the maximal-ideal-adic completions of `R` and `S`. -/
noncomputable def maximalIdealCompletionEquiv {I : Ideal R} {J : Ideal S}
    (hJ : J ≤ maximalIdeal S) (hIJ : I ≤ J.comap f)
    (hbij : ∀ n ≥ 1, Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono hIJ n).trans (Ideal.le_comap_pow _ n)))) :
    AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal S) S := by
  have h1 := hbij 1 le_rfl
  have hL1 : J ^ 1 ≤ maximalIdeal S := (pow_one J).le.trans hJ
  have hloc : IsLocalHom f := isLocalHom_of_quotientMap_surjective f hL1 _ h1.2
  have hle : maximalIdeal R ≤ (maximalIdeal S).comap f :=
    Ideal.map_le_iff_le_comap.mp (map_maximalIdeal_le f)
  have hIR : I ≤ maximalIdeal R := by
    have : Nontrivial (S ⧸ J ^ 1) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hL1)
    have : Nontrivial (R ⧸ I ^ 1) := (RingEquiv.ofBijective _ h1).symm.injective.nontrivial
    have hne : I ^ 1 ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp ‹_›
    rw [pow_one] at hne
    exact le_maximalIdeal hne
  refine RingEquiv.ofBijective (AdicCompletion.mapₐ f.toIntAlgHom hle).toRingHom
    (AdicCompletion.mapₐ_bijective f.toIntAlgHom hle fun n ↦ ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · have : Subsingleton (R ⧸ maximalIdeal R ^ 0) := by
      rw [pow_zero]; exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    have : Subsingleton (S ⧸ maximalIdeal S ^ 0) := by
      rw [pow_zero]; exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩
  · exact quotientMap_maximalIdeal_pow_bijective_of_quotientMap_bijective f
      _ (hbij n (Nat.pos_of_ne_zero hn))
      (Ideal.pow_right_mono hIR n) (Ideal.pow_right_mono hJ n)

/-- The isomorphism of maximal-ideal-adic completions extends `f` along the canonical maps into the
completions. -/
@[simp]
theorem maximalIdealCompletionEquiv_of {I : Ideal R} {J : Ideal S}
    (hJ : J ≤ maximalIdeal S) (hIJ : I ≤ J.comap f)
    (hbij : ∀ n ≥ 1, Function.Bijective (Ideal.quotientMap (J ^ n) f
      ((Ideal.pow_right_mono hIJ n).trans (Ideal.le_comap_pow _ n)))) (x : R) :
    maximalIdealCompletionEquiv f hJ hIJ hbij (AdicCompletion.of (maximalIdeal R) R x) =
      AdicCompletion.of (maximalIdeal S) S (f x) :=
  AdicCompletion.mapₐ_of f.toIntAlgHom _ x

end MaximalIdealComparison

section SharedCompletion

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [IsNoetherianRing R] [IsNoetherianRing S]

/-- Two Noetherian local rings with isomorphic maximal-ideal-adic completions have the same Krull
dimension. -/
theorem ringKrullDim_eq_of_maximalIdealCompletionEquiv
    (e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal S) S) :
    ringKrullDim R = ringKrullDim S := by
  rw [← ringKrullDim_eq (R := R), ← ringKrullDim_eq (R := S), ringKrullDim_eq_of_ringEquiv e]

/-- Two Noetherian local rings with isomorphic maximal-ideal-adic completions are either both
regular or neither is. -/
theorem isRegularLocalRing_iff_of_maximalIdealCompletionEquiv
    (e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal S) S) :
    IsRegularLocalRing R ↔ IsRegularLocalRing S := by
  rw [← isRegularLocalRing_iff (R := R), ← isRegularLocalRing_iff (R := S)]
  exact ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩

/-- Two Noetherian local rings with isomorphic maximal-ideal-adic completions are either both
Cohen–Macaulay or neither is. -/
theorem isCohenMacaulay_self_iff_of_maximalIdealCompletionEquiv
    (e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal S) S) :
    Module.IsCohenMacaulay R R ↔ Module.IsCohenMacaulay S S := by
  rw [← isCohenMacaulay_self_iff (R := R), ← isCohenMacaulay_self_iff (R := S)]
  exact e.isCohenMacaulay_self_iff

end SharedCompletion

end TauCeti.AdicCompletion
