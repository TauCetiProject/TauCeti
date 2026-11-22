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

import TauCeti.RingTheory.AdicCompletion.Localization

/-!
# Completions of local rings and their invariants

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and let `R̂` be its `𝔪`-adic completion.
Then `R̂` is a Noetherian local ring, flat over `R`, with maximal ideal `𝔪 R̂` and the same residue
field. This file shows that `R̂` has the same Krull dimension as `R`, that `R̂` is regular if and
only if `R` is, and that `R̂` is Cohen–Macaulay if and only if `R` is. Together with Mathlib's
`AdicCompletion.spanFinrank_maximalIdeal_eq`, these are among the invariants of a local ring that
are unchanged by completion.

More generally, for any local ring `R` and ideal `I ≤ 𝔪`, the `I`-adic completion
`AdicCompletion I R` is again a local ring, and `R → AdicCompletion I R` and
`AdicCompletion I R → R ⧸ I` are local homomorphisms; when `I` is finitely generated, the maximal
ideal of `AdicCompletion I R` is `𝔪 · AdicCompletion I R`.

Finally, if `f : S →ₐ[R] S'` is an `R`-algebra homomorphism of local rings and `J ≤ 𝔪_S` is an
ideal such that `S ⧸ J ^ n → S' ⧸ (J S') ^ n` is bijective for every `n ≥ 1`, then `f` induces an
isomorphism between the maximal-ideal-adic completions of `S` and `S'`.

## Main results

* `TauCeti.AdicCompletion.ringKrullDim_eq`: `R̂` and `R` have the same Krull dimension.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff`: `R̂` is regular if and only if `R` is.
* `TauCeti.AdicCompletion.isCohenMacaulay_self_iff`: `R̂` is Cohen–Macaulay if and only if `R` is.
* `TauCeti.AdicCompletion.isRegularLocalRing_iff_of_isMaximal`: completing a Noetherian ring `R` at
  a maximal ideal `p` is regular if and only if any localization `Rₚ` of `R` at `p` is regular.
* `TauCeti.AdicCompletion.isLocalHom_evalOneₐ_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.isLocalRing_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.isLocalHom_algebraMap_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le_maximalIdeal`: completing a local ring along an
  ideal `I ≤ 𝔪` produces a local ring (with extended maximal ideal when `I` is finitely generated).
* `TauCeti.AdicCompletion.mapₐ_maximalIdeal_bijective`,
  `TauCeti.AdicCompletion.maximalIdealEquivOfQuotientMap`,
  `TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap`: the induced isomorphism between
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

section LeMaximalIdeal

variable {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}

/-- For a local ring `R` and an ideal `I ≤ 𝔪_R`, the canonical projection
`AdicCompletion I R → R ⧸ I` is a local homomorphism. -/
theorem isLocalHom_evalOneₐ_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalHom (evalOneₐ I).toRingHom := by
  have : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  refine ⟨fun x hx ↦ ?_⟩
  have htr {m n : ℕ} (hmn : m ≤ n) : transitionMap I R hmn (eval I R n x) = eval I R m x :=
    x.property hmn
  have hunit (n : ℕ) : IsUnit (eval I R n x) := by
    rcases n with _ | k
    · have : Subsingleton (R ⧸ (I ^ 0 • ⊤ : Ideal R)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact isUnit_of_subsingleton _
    · have hle : (I ^ (k + 1) • ⊤ : Ideal R) ≤ I := by
        simpa using Ideal.pow_le_self (Nat.succ_ne_zero k)
      have : Nontrivial (R ⧸ (I ^ (k + 1) • ⊤ : Ideal R)) := Ideal.Quotient.nontrivial_iff.mpr
        (lt_of_le_of_lt (hle.trans hI) (maximalIdeal.isMaximal R).lt_top).ne
      have : IsLocalRing (R ⧸ (I ^ (k + 1) • ⊤ : Ideal R)) :=
        .of_surjective' _ Ideal.Quotient.mk_surjective
      have : IsLocalHom (Ideal.Quotient.factor hle) :=
        .of_surjective _ (Ideal.Quotient.factor_surjective hle)
      refine isUnit_of_map_unit (Ideal.Quotient.factor hle) (eval I R (k + 1) x) ?_
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (eval I R (k + 1) x)
      have hx1 : eval I R 1 x = Ideal.Quotient.mk (I ^ 1 • ⊤ : Ideal R) r := by
        rw [← htr (Nat.succ_le_succ (Nat.zero_le k)), ← hr]; exact Submodule.factor_mk _ _
      have heval : evalₐ I 1 x = Ideal.Quotient.mk (I ^ 1) r := by
        rw [← factor_eval_eq_evalₐ I x (by simp : (I ^ 1 • ⊤ : Ideal R) ≤ I ^ 1), hx1]
        exact Submodule.factor_mk _ _
      have h1 : evalOneₐ I x = Ideal.Quotient.mk I r := by
        rw [← factorₐ_evalₐ_one, heval, Ideal.Quotient.factor_mk]
      rwa [← hr, Ideal.Quotient.factor_mk, ← h1]
  refine isUnit_iff_exists_inv.mpr ⟨⟨fun n ↦ ↑(hunit n).unit⁻¹, fun {m n} hmn ↦ ?_⟩,
    ext fun n ↦ (hunit n).mul_val_inv⟩
  have hmul : transitionMap I R hmn (↑(hunit n).unit⁻¹) * eval I R m x = 1 := by
    rw [← htr hmn, ← transitionMap_map_mul I hmn, (hunit n).val_inv_mul, transitionMap_map_one]
  rw [← mul_one (transitionMap I R hmn _), ← (hunit m).mul_val_inv, ← mul_assoc, hmul, one_mul]

/-- Completing a local ring `R` along any ideal `I ≤ 𝔪_R` yields a local ring. -/
theorem isLocalRing_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalRing (AdicCompletion I R) := by
  have : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := isLocalHom_evalOneₐ_of_le_maximalIdeal hI
  exact (evalOneₐ I).toRingHom.domain_isLocalRing

/-- For a local ring `R` and a finitely generated ideal `I ≤ 𝔪_R`, the maximal ideal of
`AdicCompletion I R` is the extension of `𝔪_R`. -/
theorem maximalIdeal_eq_map_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) (hIfg : I.FG)
    [IsLocalRing (AdicCompletion I R)] :
    maximalIdeal (AdicCompletion I R) =
      (maximalIdeal R).map (algebraMap R (AdicCompletion I R)) :=
  (eq_maximalIdeal (isMaximal_map_of_le I (maximalIdeal R) hI hIfg)).symm

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

section MaximalIdealComparison

section RingHomBase

variable {S S' : Type*} [CommRing S] [CommRing S'] [IsLocalRing S] [IsLocalRing S']

/-- If `f : S →+* S'` induces bijections modulo `J ^ n` for an ideal `J ≤ 𝔪_S` and every
`n ≥ 1`, then `𝔪_S` maps into `𝔪_{S'}`. -/
theorem maximalIdeal_le_comap_of_quotientMap_pow_bijective (f : S →+* S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f) ^ n) f
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
    maximalIdeal S ≤ (maximalIdeal S').comap f :=
  (TauCeti.IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective f hJ
    (Ideal.quotientMap_bijective_congr f (pow_one J) (pow_one _) (hbij 1 le_rfl)
      (H₂ := Ideal.le_comap_map))) ▸ Ideal.le_comap_map

end RingHomBase

variable {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [IsLocalRing S] [IsLocalRing S']

section Equiv

variable (f : S →ₐ[R] S') {J : Ideal S} (hJ : J ≤ maximalIdeal S)
  (hbij : ∀ n : ℕ, 1 ≤ n →
    Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))

include hJ hbij

/-- If an `R`-algebra homomorphism `f : S →ₐ[R] S'` of local rings induces bijections
`S ⧸ J ^ n → S' ⧸ (J S') ^ n` for an ideal `J ≤ 𝔪_S` and every `n ≥ 1`, then `f` induces a
bijection between the maximal-ideal-adic completions of `S` and `S'`. -/
theorem mapₐ_maximalIdeal_bijective (hf : maximalIdeal S ≤ (maximalIdeal S').comap f) :
    Function.Bijective (mapₐ f hf) := by
  refine mapₐ_bijective f hf fun n ↦ ?_
  rcases n with _ | n
  · exact TauCeti.IsLocalRing.quotientMap_maximalIdeal_pow_bijective f.toRingHom
      (K := J ^ 1) (by simp) (Ideal.quotientMap_bijective_congr f.toRingHom rfl
        (Ideal.map_pow f.toRingHom J 1).symm (hbij 1 le_rfl) (H₂ := Ideal.le_comap_map))
  · exact TauCeti.IsLocalRing.quotientMap_maximalIdeal_pow_bijective f.toRingHom
      (Ideal.pow_right_mono hJ (n + 1))
      (Ideal.quotientMap_bijective_congr f.toRingHom rfl (Ideal.map_pow f.toRingHom J (n + 1)).symm
        (hbij (n + 1) (Nat.succ_pos n)) (H₂ := Ideal.le_comap_map))

/-- The canonical isomorphism between the maximal-ideal-adic completions of local rings `S` and
`S'` induced by an `R`-algebra homomorphism `f : S →ₐ[R] S'` that is an isomorphism modulo `J ^ n`
for an ideal `J ≤ 𝔪_S` and every `n ≥ 1`. -/
noncomputable def maximalIdealEquivOfQuotientMap :
    AdicCompletion (maximalIdeal S) S ≃ₐ[R] AdicCompletion (maximalIdeal S') S' :=
  AlgEquiv.ofBijective
    (mapₐ f (maximalIdeal_le_comap_of_quotientMap_pow_bijective f.toRingHom hJ hbij))
    (mapₐ_maximalIdeal_bijective f hJ hbij _)

/-- As an algebra homomorphism, `maximalIdealEquivOfQuotientMap f` is `AdicCompletion.mapₐ f`. -/
@[simp]
theorem toAlgHom_maximalIdealEquivOfQuotientMap :
    (maximalIdealEquivOfQuotientMap f hJ hbij :
        AdicCompletion (maximalIdeal S) S →ₐ[R] AdicCompletion (maximalIdeal S') S') =
      mapₐ f (maximalIdeal_le_comap_of_quotientMap_pow_bijective f.toRingHom hJ hbij) := by
  ext; rfl

/-- Modulo `𝔪_{S'} ^ n`, `maximalIdealEquivOfQuotientMap f` is the quotient map induced by `f`. -/
@[simp]
theorem evalₐ_maximalIdealEquivOfQuotientMap (n : ℕ) (x : AdicCompletion (maximalIdeal S) S) :
    evalₐ (maximalIdeal S') n (maximalIdealEquivOfQuotientMap f hJ hbij x) =
      Ideal.quotientMap (maximalIdeal S' ^ n) (f : S →+* S')
        ((Ideal.pow_right_mono
          (maximalIdeal_le_comap_of_quotientMap_pow_bijective f.toRingHom hJ hbij) n).trans
          (Ideal.le_comap_pow _ n))
        (evalₐ (maximalIdeal S) n x) := by
  exact evalₐ_mapₐ f _ n x

/-- On elements of `S`, `maximalIdealEquivOfQuotientMap f` applies `f`. -/
@[simp]
theorem maximalIdealEquivOfQuotientMap_of (x : S) :
    maximalIdealEquivOfQuotientMap f hJ hbij (of (maximalIdeal S) S x) =
      of (maximalIdeal S') S' (f x) := by
  exact mapₐ_of f _ x

/-- The underlying map of `maximalIdealEquivOfQuotientMap f` is `AdicCompletion.mapₐ f`. -/
theorem maximalIdealEquivOfQuotientMap_apply (x : AdicCompletion (maximalIdeal S) S) :
    maximalIdealEquivOfQuotientMap f hJ hbij x =
      mapₐ f (maximalIdeal_le_comap_of_quotientMap_pow_bijective f.toRingHom hJ hbij) x := by
  rfl

end Equiv

/-- Composing two maximal-ideal completion isomorphisms induced by `f` and `g` yields the
isomorphism induced by `h = g.comp f`. -/
theorem maximalIdealEquivOfQuotientMap_trans {S'' : Type*} [CommRing S''] [Algebra R S'']
    [IsLocalRing S''] (f : S →ₐ[R] S') {J : Ideal S} (hJ : J ≤ maximalIdeal S)
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
    (maximalIdealEquivOfQuotientMap f hJ hbijf).trans
        (maximalIdealEquivOfQuotientMap g hJ' hbijg) =
      maximalIdealEquivOfQuotientMap h hK hbijh := by
  subst hfg
  exact AlgEquiv.ext fun x ↦ by
    rw [AlgEquiv.trans_apply, maximalIdealEquivOfQuotientMap_apply,
      maximalIdealEquivOfQuotientMap_apply, maximalIdealEquivOfQuotientMap_apply]
    exact mapₐ_mapₐ _ _ _ _ x

section RingEquiv

variable {T T' : Type*} [CommRing T] [CommRing T'] [IsLocalRing T] [IsLocalRing T']
  (f : T →+* T') {J : Ideal T} (hJ : J ≤ maximalIdeal T)
  (hbij : ∀ n : ℕ, 1 ≤ n →
    Function.Bijective (Ideal.quotientMap ((J.map f) ^ n) f
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))

/-- The canonical ring isomorphism between the maximal-ideal-adic completions of local rings `T`
and `T'` induced by a ring homomorphism `f : T →+* T'` that is an isomorphism modulo `J ^ n`
for an ideal `J ≤ 𝔪_T` and every `n ≥ 1`. -/
noncomputable def maximalIdealRingEquivOfQuotientMap :
    AdicCompletion (maximalIdeal T) T ≃+* AdicCompletion (maximalIdeal T') T' :=
  letI : Algebra T T' := f.toAlgebra
  (maximalIdealEquivOfQuotientMap (Algebra.ofId T T') hJ hbij).toRingEquiv

/-- Modulo `𝔪_{T'} ^ n`, `maximalIdealRingEquivOfQuotientMap f` is the quotient map induced by
`f`. -/
@[simp]
theorem evalₐ_maximalIdealRingEquivOfQuotientMap (n : ℕ)
    (x : AdicCompletion (maximalIdeal T) T) :
    evalₐ (maximalIdeal T') n (maximalIdealRingEquivOfQuotientMap f hJ hbij x) =
      Ideal.quotientMap (maximalIdeal T' ^ n) f
        ((Ideal.pow_right_mono
          (maximalIdeal_le_comap_of_quotientMap_pow_bijective f hJ hbij) n).trans
          (Ideal.le_comap_pow _ n))
        (evalₐ (maximalIdeal T) n x) := by
  let : Algebra T T' := f.toAlgebra
  exact evalₐ_maximalIdealEquivOfQuotientMap (Algebra.ofId T T') hJ hbij n x

/-- On elements of `T`, `maximalIdealRingEquivOfQuotientMap f` applies `f`. -/
@[simp]
theorem maximalIdealRingEquivOfQuotientMap_of (x : T) :
    maximalIdealRingEquivOfQuotientMap f hJ hbij (of (maximalIdeal T) T x) =
      of (maximalIdeal T') T' (f x) := by
  let : Algebra T T' := f.toAlgebra
  exact maximalIdealEquivOfQuotientMap_of (Algebra.ofId T T') hJ hbij x

/-- Composing two maximal-ideal completion ring isomorphisms induced by `f` and `g` yields the
isomorphism induced by `h = g.comp f`. -/
theorem maximalIdealRingEquivOfQuotientMap_trans {T'' : Type*} [CommRing T''] [IsLocalRing T'']
    (f : T →+* T') {J : Ideal T} (hJ : J ≤ maximalIdeal T)
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
    (maximalIdealRingEquivOfQuotientMap f hJ hbijf).trans
        (maximalIdealRingEquivOfQuotientMap g hJ' hbijg) =
      maximalIdealRingEquivOfQuotientMap h hK hbijh := by
  subst hfg
  refine RingEquiv.ext fun x ↦ ext_evalₐ fun n ↦ ?_
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal T) n x)
  simp only [RingEquiv.trans_apply, evalₐ_maximalIdealRingEquivOfQuotientMap, ← hs,
    Ideal.quotientMap_mk, RingHom.comp_apply]

end RingEquiv

end MaximalIdealComparison

/-- Completing a Noetherian ring `R` at a maximal ideal `p` yields a regular local ring if and only
if any localization `Rₚ` of `R` at `p` is a regular local ring. -/
theorem isRegularLocalRing_iff_of_isMaximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    IsRegularLocalRing (AdicCompletion p R) ↔ IsRegularLocalRing Rₚ := by
  have : IsNoetherianRing Rₚ := IsLocalization.isNoetherianRing p.primeCompl Rₚ ‹_›
  let e := (_root_.AdicCompletion.equivMaximalIdealOfAtPrime p Rₚ).toRingEquiv
  exact ⟨fun _ ↦ isRegularLocalRing_iff.mp (.of_ringEquiv e),
    fun _ ↦ .of_ringEquiv (R := AdicCompletion (maximalIdeal Rₚ) Rₚ) e.symm⟩

end TauCeti.AdicCompletion
