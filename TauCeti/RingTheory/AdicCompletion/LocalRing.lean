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
public import TauCeti.RingTheory.LocalRing.Quotient
public import TauCeti.RingTheory.RegularLocalRing.Flat

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
* `TauCeti.AdicCompletion.evalOneₐ_isLocalHom_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.isLocalRing_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.algebraMap_isLocalHom_of_le_maximalIdeal`,
  `TauCeti.AdicCompletion.maximalIdeal_eq_map_of_le_maximalIdeal`: completing a local ring along an
  ideal `I ≤ 𝔪` produces a local ring (with extended maximal ideal when `I` is finitely generated).
* `TauCeti.AdicCompletion.mapₐ_maximalIdeal_bijective`,
  `TauCeti.AdicCompletion.maximalIdealEquivOfQuotientMap`: the induced isomorphism between
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
theorem evalOneₐ_isLocalHom_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalHom (evalOneₐ I).toRingHom := by
  have hIne : I ≠ ⊤ := (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  refine ⟨fun x hx ↦ ?_⟩
  have htr {m n : ℕ} (hmn : m ≤ n) :
      transitionMap I R hmn (eval I R n x) = eval I R m x :=
    x.property hmn
  have hunit (n : ℕ) : IsUnit (eval I R n x) := by
    rcases n with _ | k
    · have : Subsingleton (R ⧸ (I ^ 0 • ⊤ : Ideal R)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact isUnit_of_subsingleton _
    · have hle : (I ^ (k + 1) • ⊤ : Ideal R) ≤ I := by
        simpa using Ideal.pow_le_self (Nat.succ_ne_zero k)
      have hne : (I ^ (k + 1) • ⊤ : Ideal R) ≠ ⊤ :=
        (lt_of_le_of_lt (hle.trans hI) (maximalIdeal.isMaximal R).lt_top).ne
      have : Nontrivial (R ⧸ (I ^ (k + 1) • ⊤ : Ideal R)) :=
        Ideal.Quotient.nontrivial_iff.mpr hne
      have : IsLocalRing (R ⧸ (I ^ (k + 1) • ⊤ : Ideal R)) :=
        .of_surjective' _ Ideal.Quotient.mk_surjective
      have : IsLocalHom (Ideal.Quotient.factor hle) :=
        IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective hle)
      refine isUnit_of_map_unit (Ideal.Quotient.factor hle) (eval I R (k + 1) x) ?_
      have hfac : Ideal.Quotient.factor hle (eval I R (k + 1) x) = evalOneₐ I x := by
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (eval I R (k + 1) x)
        have hx1 : eval I R 1 x = Ideal.Quotient.mk (I ^ 1 • ⊤ : Ideal R) r := by
          rw [← htr (Nat.succ_le_succ (Nat.zero_le k)), ← hr]
          rfl
        have heval : evalₐ I 1 x = Ideal.Quotient.mk (I ^ 1) r := by
          rw [← factor_eval_eq_evalₐ I x (by simp : (I ^ 1 • ⊤ : Ideal R) ≤ I ^ 1), hx1]
          rfl
        rw [← factorₐ_evalₐ_one, heval, ← hr, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
      rwa [hfac]
  have hmul_inv (n : ℕ) : eval I R n x * ↑(hunit n).unit⁻¹ = 1 := by simp
  have hinv_mul (n : ℕ) : ↑(hunit n).unit⁻¹ * eval I R n x = 1 := by simp
  let y : AdicCompletion I R := ⟨fun n ↦ ↑(hunit n).unit⁻¹, fun {m n} hmn ↦ by
    have hmul : transitionMap I R hmn (↑(hunit n).unit⁻¹) * eval I R m x = 1 := by
      rw [← htr hmn, ← transitionMap_map_mul I hmn, hinv_mul n, transitionMap_map_one]
    calc transitionMap I R hmn (↑(hunit n).unit⁻¹)
        = transitionMap I R hmn (↑(hunit n).unit⁻¹) * (eval I R m x * ↑(hunit m).unit⁻¹) := by
          rw [hmul_inv m, mul_one]
      _ = (transitionMap I R hmn (↑(hunit n).unit⁻¹) * eval I R m x) * ↑(hunit m).unit⁻¹ :=
          (mul_assoc _ _ _).symm
      _ = ↑(hunit m).unit⁻¹ := by rw [hmul, one_mul]⟩
  exact isUnit_iff_exists_inv.mpr ⟨y, ext fun n ↦ hmul_inv n⟩

/-- Completing a local ring `R` along any ideal `I ≤ 𝔪_R` yields a local ring. -/
theorem isLocalRing_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalRing (AdicCompletion I R) := by
  have hIne : I ≠ ⊤ := (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have := evalOneₐ_isLocalHom_of_le_maximalIdeal hI
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
theorem algebraMap_isLocalHom_of_le_maximalIdeal (hI : I ≤ maximalIdeal R) :
    IsLocalHom (algebraMap R (AdicCompletion I R)) := by
  have hIne : I ≠ ⊤ := (lt_of_le_of_lt hI (maximalIdeal.isMaximal R).lt_top).ne
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalHom ((evalOneₐ I).toRingHom.comp (algebraMap R (AdicCompletion I R))) := by
    rw [evalOneₐ_comp_algebraMap_eq_mk]
    exact IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact isLocalHom_of_comp (algebraMap R (AdicCompletion I R)) (evalOneₐ I).toRingHom

end LeMaximalIdeal

section MaximalIdealComparison

variable {R S S' S'' : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing S'']
  [Algebra R S] [Algebra R S'] [Algebra R S'']
  [IsLocalRing S] [IsLocalRing S'] [IsLocalRing S'']

/-- If an `R`-algebra homomorphism `f : S →ₐ[R] S'` of local rings induces bijections
`S ⧸ J ^ n → S' ⧸ (J S') ^ n` for an ideal `J ≤ 𝔪_S` and every `n ≥ 1`, then `f` induces a
bijection between the maximal-ideal-adic completions of `S` and `S'`. -/
theorem mapₐ_maximalIdeal_bijective (f : S →ₐ[R] S') {J : Ideal S} (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (hf : maximalIdeal S ≤ (maximalIdeal S').comap f) :
    Function.Bijective (mapₐ f hf) := by
  refine mapₐ_bijective f hf fun n ↦ ?_
  rcases n with _ | n
  · have : Subsingleton (S ⧸ maximalIdeal S ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    have : Subsingleton (S' ⧸ maximalIdeal S' ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]; exact Ideal.Quotient.subsingleton_iff.mpr rfl
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · exact TauCeti.IsLocalRing.quotientMap_maximalIdeal_pow_bijective f.toRingHom
      (Ideal.pow_right_mono hJ (n + 1))
      (Ideal.quotientMap_bijective_congr f.toRingHom rfl (Ideal.map_pow f.toRingHom J (n + 1)).symm
        (hbij (n + 1) (Nat.succ_pos n)) (H₂ := Ideal.le_comap_map))

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
    (mapₐ f ((TauCeti.IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective f.toRingHom hJ
      (Ideal.quotientMap_bijective_congr f.toRingHom (pow_one J) (pow_one _) (hbij 1 le_rfl)
        (H₂ := Ideal.le_comap_map))) ▸ Ideal.le_comap_map))
    (mapₐ_maximalIdeal_bijective f hJ hbij _)

/-- As an algebra homomorphism, `maximalIdealEquivOfQuotientMap f` is `AdicCompletion.mapₐ f`. -/
@[simp]
theorem toAlgHom_maximalIdealEquivOfQuotientMap (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
    (maximalIdealEquivOfQuotientMap f hJ hbij :
        AdicCompletion (maximalIdeal S) S →ₐ[R] AdicCompletion (maximalIdeal S') S') =
      mapₐ f ((TauCeti.IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective f.toRingHom hJ
        (Ideal.quotientMap_bijective_congr f.toRingHom (pow_one J) (pow_one _) (hbij 1 le_rfl)
          (H₂ := Ideal.le_comap_map))) ▸ Ideal.le_comap_map) := by
  ext; rfl

/-- Modulo `𝔪_{S'} ^ n`, `maximalIdealEquivOfQuotientMap f` is the quotient map induced by `f`. -/
@[simp]
theorem evalₐ_maximalIdealEquivOfQuotientMap (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (n : ℕ) (x : AdicCompletion (maximalIdeal S) S) :
    evalₐ (maximalIdeal S') n (maximalIdealEquivOfQuotientMap f hJ hbij x) =
      Ideal.quotientMap (maximalIdeal S' ^ n) (f : S →+* S')
        ((Ideal.pow_right_mono
          ((TauCeti.IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective f.toRingHom hJ
            (Ideal.quotientMap_bijective_congr f.toRingHom (pow_one J) (pow_one _) (hbij 1 le_rfl)
              (H₂ := Ideal.le_comap_map))) ▸ Ideal.le_comap_map) n).trans (Ideal.le_comap_pow _ n))
        (evalₐ (maximalIdeal S) n x) := by
  exact evalₐ_mapₐ f _ n x

/-- On elements of `S`, `maximalIdealEquivOfQuotientMap f` applies `f`. -/
@[simp]
theorem maximalIdealEquivOfQuotientMap_of (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) (x : S) :
    maximalIdealEquivOfQuotientMap f hJ hbij (of (maximalIdeal S) S x) =
      of (maximalIdeal S') S' (f x) := by
  exact mapₐ_of f _ x

/-- The underlying map of `maximalIdealEquivOfQuotientMap f` is `AdicCompletion.mapₐ f`. -/
theorem maximalIdealEquivOfQuotientMap_apply (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbij : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (x : AdicCompletion (maximalIdeal S) S) :
    maximalIdealEquivOfQuotientMap f hJ hbij x =
      mapₐ f ((TauCeti.IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective f.toRingHom hJ
        (Ideal.quotientMap_bijective_congr f.toRingHom (pow_one J) (pow_one _) (hbij 1 le_rfl)
          (H₂ := Ideal.le_comap_map))) ▸ Ideal.le_comap_map) x := by
  rfl

/-- Composing two maximal-ideal completion isomorphisms induced by `f` and `g` yields the
isomorphism induced by `g.comp f`. -/
theorem maximalIdealEquivOfQuotientMap_trans (f : S →ₐ[R] S') {J : Ideal S}
    (hJ : J ≤ maximalIdeal S)
    (hbijf : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J.map f.toRingHom) ^ n) f.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    (g : S' →ₐ[R] S'') {J' : Ideal S'} (hJ' : J' ≤ maximalIdeal S')
    (hbijg : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((J'.map g.toRingHom) ^ n) g.toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))))
    {K : Ideal S} (hK : K ≤ maximalIdeal S)
    (hbijgf : ∀ n : ℕ, 1 ≤ n →
      Function.Bijective (Ideal.quotientMap ((K.map (g.comp f).toRingHom) ^ n) (g.comp f).toRingHom
        ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n)))) :
    (maximalIdealEquivOfQuotientMap f hJ hbijf).trans
        (maximalIdealEquivOfQuotientMap g hJ' hbijg) =
      maximalIdealEquivOfQuotientMap (g.comp f) hK hbijgf := by
  ext x
  simp only [AlgEquiv.trans_apply, maximalIdealEquivOfQuotientMap_apply, mapₐ_mapₐ]

end MaximalIdealComparison

end TauCeti.AdicCompletion
