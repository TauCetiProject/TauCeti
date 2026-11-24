/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Tactic.LinearCombination
public import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.RingTheory.AdicCompletion.Regular
public import TauCeti.RingTheory.Patching.ExactSquare

/-!
# Glueing pairs

Let `R → R'` be a map of commutative rings and `f ∈ R`. Write `f'` for the image of `f` in `R'`,
`M[f^∞]` for the `f`-power torsion of a module `M`, `R_f` for a localization of `R` away from `f`
and `R'_f` for a localization of `R'` away from `f'`. The pair `(R → R', f)` is a *glueing pair*
when `R → R'` induces isomorphisms `R ⧸ fⁿ ≃ R' ⧸ f'ⁿ` for every `n` and a bijection
`R[f^∞] → R'[f^∞]`. Equivalently, given the isomorphisms modulo powers of `f`, the square

```
R   ⟶ R'
↓      ↓
R_f ⟶ R'_f
```

is exact in the sense of `TauCeti.ExactSquare`: the sequence `0 → R → R' × R_f → R'_f → 0` is
exact. This is the setting of the Beauville–Laszlo theorem, which glues modules over `R'` and
`R_f` along `R'_f` without any flatness of `R → R'`. The main example is the `f`-adic completion
`R → R̂` of a ring in which `f` is a nonzerodivisor; no noetherian hypothesis is needed.

Given the isomorphisms modulo powers of `f`, the sequence is always exact on the right. It is
exact on the left exactly when `R[f^∞] → R'[f^∞]` is injective, since the kernel of `R → R_f` is
`R[f^∞]`, and exact in the middle exactly when `R[f^∞] → R'[f^∞]` is surjective.

## Main definitions

* `TauCeti.GlueingPair R' f`: the pair `(R → R', f)` is a glueing pair.

## Main results

* `TauCeti.GlueingPair.quotientMap_bijective`: a glueing pair induces isomorphisms
  `R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)`.
* `TauCeti.GlueingPair.exactSquare`: the square `R → R'`, `R_f → R'_f` of a glueing pair is
  exact.
* `TauCeti.glueingPair_iff_exactSquare`: the torsion criterion. When `R → R'` induces
  isomorphisms modulo every power of `f`, the pair is a glueing pair if and only if the square is
  exact.
* `TauCeti.exists_isPrime_comap_eq_of_bijective_quotientMap`,
  `TauCeti.GlueingPair.exists_isPrime_comap_eq`: if `R ⧸ (f) ≃ R' ⧸ (f')`, in particular for a
  glueing pair, every prime of `R` comes from a prime of `R'` or of `R_f`.
* `TauCeti.glueingPair_self`: the identity `R → R` is a glueing pair for every `f`.
* `IsRegular.glueingPair_adicCompletion`: if `f` is a nonzerodivisor, then `R` and its
  `(f)`-adic completion form a glueing pair.

## References

* [The Stacks Project, Section 15.92](https://stacks.math.columbia.edu/tag/0BNI), glueing pairs:
  Lemma 15.92.3 for the primes, Lemma 15.92.6 (Tag 0BNR) for the torsion criterion and
  Remark 15.92.7 (Tag 0BNS) for the completion at a nonzerodivisor.
* A. Beauville, Y. Laszlo, *Un lemme de descente*, C. R. Acad. Sci. Paris Sér. I Math. 320
  (1995), 335–340.
-/

public section

namespace TauCeti

variable {R R' : Type*} [CommRing R] [CommRing R']

section Definition

variable [Algebra R R']

variable (R') in
/-- The pair `(R → R', f)` is a *glueing pair* when `R → R'` induces isomorphisms
`R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)` for every `n`, where `f'` is the image of `f`, and a bijection between
the `f`-power torsion of `R` and the `f'`-power torsion of `R'`. When the first condition holds,
the second is equivalent to exactness of `0 → R → R' × R_f → R'_f → 0`
(`TauCeti.glueingPair_iff_exactSquare`). -/
structure GlueingPair (f : R) : Prop where
  /-- Every element of `R'` is congruent modulo `f'ⁿ` to the image of an element of `R`. -/
  quotient_surjective : ∀ (n : ℕ) (y : R'), ∃ x : R,
    y - algebraMap R R' x ∈ Ideal.span {algebraMap R R' f ^ n}
  /-- An element of `R` whose image is divisible by `f'ⁿ` is divisible by `fⁿ`. -/
  quotient_injective : ∀ n : ℕ,
    (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') = Ideal.span {f ^ n}
  /-- The map `R → R'` restricts to a bijection between the power torsion submodules. -/
  torsion_bijOn : Set.BijOn (algebraMap R R')
    (Submodule.torsion' R R (Submonoid.powers f))
    (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f)))

/-- A glueing pair induces isomorphisms `R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)` for every `n`. -/
theorem GlueingPair.quotientMap_bijective {f : R} (h : GlueingPair R' f) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (Ideal.span {algebraMap R R' f ^ n})
      (algebraMap R R') (h.quotient_injective n).ge) := by
  refine ⟨Ideal.quotientMap_injective' (h.quotient_injective n).le, fun y ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := h.quotient_surjective n y
  exact ⟨Ideal.Quotient.mk _ x, (Ideal.Quotient.eq.mpr hx).symm⟩

end Definition

variable (R) in
/-- The identity map of a ring is a glueing pair for every element. -/
theorem glueingPair_self (f : R) : GlueingPair R f where
  quotient_surjective _ y := ⟨y, by simp⟩
  quotient_injective _ := by simp
  torsion_bijOn := by simpa using Set.bijOn_id _

section ExactSquare

variable {R₂ L : Type*} [CommRing R₂] [CommRing L] [Algebra R R'] [Algebra R R₂] [Algebra R L]
  [Algebra R' L] [Algebra R₂ L] [IsScalarTower R R' L] [IsScalarTower R R₂ L] {f : R}

/-- An element dies in a localization at a submonoid exactly when it is torsion for that
submonoid. -/
private theorem algebraMap_eq_zero_iff_mem_torsion' {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (S : Submonoid A) [IsLocalization S B] (a : A) :
    algebraMap A B a = 0 ↔ a ∈ Submodule.torsion' A A S := by
  simp [IsLocalization.map_eq_zero_iff S, Submodule.mem_torsion'_iff]

/-- The image of an `f`-power torsion element of `R` is `f'`-power torsion in `R'`. -/
private theorem mapsTo_torsion' :
    Set.MapsTo (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f))
      (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f))) := by
  rintro x ⟨⟨_, k, rfl⟩, hk⟩
  refine ⟨⟨_, k, rfl⟩, ?_⟩
  simpa [Submonoid.smul_def] using congr(algebraMap R R' $hk)

variable (R' R₂) in
/-- The diagonal `R → R' × R_f` is injective exactly when `R[f^∞] → R'[f^∞]` is injective
(Stacks, Lemma 15.92.6). -/
private theorem injective_iff_injOn_torsion' [IsLocalization.Away f R₂] :
    Function.Injective (fun r : R ↦ (algebraMap R R' r, algebraMap R R₂ r)) ↔
      Set.InjOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f)) := by
  have hz := algebraMap_eq_zero_iff_mem_torsion' (B := R₂) (Submonoid.powers f)
  refine ⟨fun hi x hx y hy hxy ↦ hi ?_, fun hi x y hxy ↦ ?_⟩
  · simp [hxy, (hz x).mpr hx, (hz y).mpr hy]
  · simp only [Prod.mk.injEq] at hxy
    rw [← sub_eq_zero]
    refine hi ((hz _).mp ?_) (zero_mem _) (by simp [hxy.1])
    simp [hxy.2]

/-- If every element of `R'` is congruent modulo every power of `f'` to the image of an element
of `R`, then the difference map `R' × R_f → R'_f` is surjective: the patching sequence is exact on
the right (Stacks, Lemma 15.92.6). -/
private theorem surjective_sub_of_quotient_surjective [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (hs : ∀ (n : ℕ) (y : R'), ∃ x : R, y - algebraMap R R' x ∈ Ideal.span {algebraMap R R' f ^ n}) :
    Function.Surjective fun x : R' × R₂ ↦ algebraMap R' L x.1 - algebraMap R₂ L x.2 := by
  intro z
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj (algebraMap R R' f) z
  obtain ⟨a, ha⟩ := hs n r
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
  -- `z = r / f'ⁿ = b + a / fⁿ`, and `a / fⁿ` comes from `R_f`.
  refine ⟨(b, -(IsLocalization.Away.invSelf f ^ n * algebraMap R R₂ a)), ?_⟩
  have hu : IsUnit (algebraMap R L f) := by
    rw [IsScalarTower.algebraMap_apply R R' L]
    exact IsLocalization.Away.algebraMap_isUnit _
  have hinv : algebraMap R₂ L (IsLocalization.Away.invSelf f) ^ n * algebraMap R L f ^ n = 1 := by
    rw [← mul_pow, IsScalarTower.algebraMap_apply R R₂ L f, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one, one_pow]
  have hz : z * algebraMap R L f ^ n = algebraMap R' L r := by
    rwa [IsScalarTower.algebraMap_apply R R' L f]
  have hb' : algebraMap R' L b * algebraMap R L f ^ n = algebraMap R' L r - algebraMap R L a := by
    rw [IsScalarTower.algebraMap_apply R R' L f, IsScalarTower.algebraMap_apply R R' L a,
      ← map_pow, ← map_mul, hb, map_sub]
  refine (hu.pow n).mul_left_inj.mp ?_
  simp only [map_neg, map_mul, map_pow, ← IsScalarTower.algebraMap_apply, sub_neg_eq_add]
  linear_combination hb' - hz + algebraMap R L a * hinv

/-- If every element of `R` whose image is divisible by `f'ⁿ` is divisible by `fⁿ` and
`R[f^∞] → R'[f^∞]` is surjective, then a pair `(r', s) ∈ R' × R_f` with the same image in `R'_f`
comes from `R`. Writing `s = a / fⁿ`, the element `a` is corrected by a torsion element to become
divisible by `fⁿ`, and the quotient is then corrected by a second torsion element. -/
private theorem exists_algebraMap_eq_of_surjOn_torsion' [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (hi : ∀ n : ℕ,
      (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') ≤ Ideal.span {f ^ n})
    (hsurj : Set.SurjOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f))
      (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f))))
    {r' : R'} {s : R₂} (hrs : algebraMap R' L r' = algebraMap R₂ L s) :
    ∃ r : R, algebraMap R R' r = r' ∧ algebraMap R R₂ r = s := by
  -- Write `s = a / fⁿ`; then `f'ⁿ r' - a` is torsion in `R'`.
  obtain ⟨n, a, hs⟩ := IsLocalization.Away.surj f s
  have ht : algebraMap R R' f ^ n * r' - algebraMap R R' a ∈
      Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f)) := by
    refine (algebraMap_eq_zero_iff_mem_torsion' (B := L) _ _).mp ?_
    simp only [map_sub, map_mul, map_pow, hrs, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply R R₂ L f, IsScalarTower.algebraMap_apply R R₂ L a, ← hs,
      map_mul, map_pow]
    ring
  -- Correct `a` by a torsion element `t` to make it divisible by `fⁿ`: `a + t = fⁿ c`.
  obtain ⟨t, ht, htr⟩ := hsurj ht
  have hat : a + t ∈ (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') :=
    Ideal.mem_comap.mpr <| Ideal.mem_span_singleton'.mpr ⟨r', by rw [map_add, htr]; ring⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hi n hat)
  -- Then `r' - c` is torsion in `R'`; lift it to a torsion element `u` of `R`.
  have hv : r' - algebraMap R R' c ∈
      Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f)) := by
    have h0 : algebraMap R R' f ^ n * (r' - algebraMap R R' c) = 0 := by
      rw [mul_sub, ← map_pow, ← map_mul, mul_comm (f ^ n) c, hc, map_add, htr, map_pow]
      ring
    exact ⟨⟨_, pow_mem (Submonoid.mem_powers _) n⟩, h0⟩
  obtain ⟨u, hu, hur⟩ := hsurj hv
  refine ⟨c + u, by rw [map_add, hur, add_sub_cancel], ?_⟩
  refine ((IsLocalization.Away.algebraMap_isUnit f).pow n).mul_left_inj.mp ?_
  rw [hs, ← map_pow, ← map_mul, add_mul, hc, ← sub_eq_zero, ← map_sub]
  refine (algebraMap_eq_zero_iff_mem_torsion' (B := R₂) (Submonoid.powers f) _).mpr ?_
  convert add_mem ht (Submodule.smul_mem _ (f ^ n) hu) using 1
  rw [smul_eq_mul]
  ring

/-- If every element of `R` whose image is divisible by `f'ⁿ` is divisible by `fⁿ`, then the
patching sequence `R → R' × R_f → R'_f` is exact in the middle exactly when `R[f^∞] → R'[f^∞]` is
surjective (Stacks, Lemma 15.92.6). -/
private theorem exact_iff_surjOn_torsion' [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (hi : ∀ n : ℕ,
      (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') ≤ Ideal.span {f ^ n}) :
    Function.Exact (fun r : R ↦ (algebraMap R R' r, algebraMap R R₂ r))
        (fun x : R' × R₂ ↦ algebraMap R' L x.1 - algebraMap R₂ L x.2) ↔
      Set.SurjOn (algebraMap R R') (Submodule.torsion' R R (Submonoid.powers f))
        (Submodule.torsion' R' R' (Submonoid.powers (algebraMap R R' f))) := by
  refine ⟨fun he t ht ↦ ?_, fun hsurj x ↦ ⟨fun hrs ↦ ?_, ?_⟩⟩
  · -- A torsion element `t` of `R'` gives the compatible pair `(t, 0)`.
    obtain ⟨r, hr⟩ := (he (t, 0)).mp
      (by simp [(algebraMap_eq_zero_iff_mem_torsion' (B := L) _ t).mpr ht])
    simp only [Prod.mk.injEq] at hr
    exact ⟨r, (algebraMap_eq_zero_iff_mem_torsion' (B := R₂) _ r).mp hr.2, hr.1⟩
  · obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_surjOn_torsion' hi hsurj (sub_eq_zero.mp hrs)
    exact ⟨r, Prod.ext hr.1 hr.2⟩
  · rintro ⟨r, rfl⟩
    simp [← IsScalarTower.algebraMap_apply]

variable (R₂ L) in
/-- The square `R → R'`, `R_f → R'_f` of a glueing pair is exact: the sequence
`0 → R → R' × R_f → R'_f → 0` is exact (Stacks, Lemma 15.92.6). -/
theorem GlueingPair.exactSquare (h : GlueingPair R' f) [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L] : ExactSquare R R' R₂ L where
  injective := (injective_iff_injOn_torsion' R' R₂).mpr h.torsion_bijOn.injOn
  exact := (exact_iff_surjOn_torsion' fun n ↦ (h.quotient_injective n).le).mpr
    h.torsion_bijOn.surjOn
  surjective := surjective_sub_of_quotient_surjective h.quotient_surjective

/-- The torsion criterion for glueing pairs (Stacks, Lemma 15.92.6). Suppose that `R → R'` induces
isomorphisms `R ⧸ (fⁿ) ≃ R' ⧸ (f'ⁿ)` for every `n`. Then `(R → R', f)` is a glueing pair, that is,
`R[f^∞] → R'[f^∞]` is bijective, if and only if the square `R → R'`, `R_f → R'_f` is exact. -/
theorem glueingPair_iff_exactSquare [IsLocalization.Away f R₂]
    [IsLocalization.Away (algebraMap R R' f) L]
    (hs : ∀ (n : ℕ) (y : R'), ∃ x : R, y - algebraMap R R' x ∈ Ideal.span {algebraMap R R' f ^ n})
    (hi : ∀ n : ℕ,
      (Ideal.span {algebraMap R R' f ^ n}).comap (algebraMap R R') = Ideal.span {f ^ n}) :
    GlueingPair R' f ↔ ExactSquare R R' R₂ L :=
  ⟨fun h ↦ h.exactSquare R₂ L, fun h ↦
    { quotient_surjective := hs
      quotient_injective := hi
      torsion_bijOn := ⟨mapsTo_torsion', (injective_iff_injOn_torsion' R' R₂).mp h.injective,
        (exact_iff_surjOn_torsion' fun n ↦ (hi n).le).mp h.exact⟩ }⟩

omit [Algebra R L] [Algebra R' L] [Algebra R₂ L] [IsScalarTower R R' L] [IsScalarTower R R₂ L] in
/-- If `R → R'` induces an isomorphism `R ⧸ (f) ≃ R' ⧸ (f')`, then every prime ideal of `R` is the
contraction of a prime ideal of `R'` or of `R_f`: the maps `Spec R' → Spec R` and
`Spec R_f → Spec R` are jointly surjective (Stacks, Lemma 15.92.3). A prime containing `f` comes
from `R'` through the isomorphism, and a prime avoiding `f` comes from `R_f`. -/
theorem exists_isPrime_comap_eq_of_bijective_quotientMap [IsLocalization.Away f R₂]
    {H : Ideal.span {f} ≤ (Ideal.span {algebraMap R R' f}).comap (algebraMap R R')}
    (hg : Function.Bijective (Ideal.quotientMap _ (algebraMap R R') H)) (p : Ideal R) [p.IsPrime] :
    (∃ P : Ideal R', P.IsPrime ∧ P.comap (algebraMap R R') = p) ∨
      ∃ P : Ideal R₂, P.IsPrime ∧ P.comap (algebraMap R R₂) = p := by
  by_cases hf : f ∈ p
  · left
    have hle : Ideal.span {f} ≤ p := by simpa [Ideal.span_le] using hf
    set g := Ideal.quotientMap _ (algebraMap R R') H
    have : (p.map (Ideal.Quotient.mk (Ideal.span {f}))).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hle
    have : ((p.map (Ideal.Quotient.mk _)).map g).IsPrime :=
      Ideal.map_isPrime_of_surjective hg.2 (by simp [(RingHom.injective_iff_ker_eq_bot g).mp hg.1])
    refine ⟨((p.map (Ideal.Quotient.mk _)).map g).comap (Ideal.Quotient.mk _), inferInstance, ?_⟩
    rw [Ideal.comap_comap, ← Ideal.quotientMap_comp_mk H, ← Ideal.comap_comap,
      Ideal.comap_map_of_bijective g hg, Ideal.comap_map_mk hle]
  · right
    have hd : Disjoint (Submonoid.powers f : Set R) p :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
    exact ⟨_, IsLocalization.isPrime_of_isPrime_disjoint _ R₂ p ‹_› hd,
      IsLocalization.under_map_of_isPrime_disjoint _ R₂ ‹_› hd⟩

omit [Algebra R L] [Algebra R' L] [Algebra R₂ L] [IsScalarTower R R' L] [IsScalarTower R R₂ L] in
/-- Every prime ideal of `R` is the contraction of a prime ideal of `R'` or of `R_f` for a glueing
pair `(R → R', f)`. -/
theorem GlueingPair.exists_isPrime_comap_eq (h : GlueingPair R' f) [IsLocalization.Away f R₂]
    (p : Ideal R) [p.IsPrime] :
    (∃ P : Ideal R', P.IsPrime ∧ P.comap (algebraMap R R') = p) ∨
      ∃ P : Ideal R₂, P.IsPrime ∧ P.comap (algebraMap R R₂) = p := by
  have hi := h.quotient_injective 1
  simp only [pow_one] at hi
  exact exists_isPrime_comap_eq_of_bijective_quotientMap (H := hi.ge)
    (by convert h.quotientMap_bijective 1 <;> simp) p

end ExactSquare

end TauCeti

namespace IsRegular

universe u

variable {R : Type u} [CommRing R] {f : R}

/-- If `f` is a nonzerodivisor of `R`, then `R` and its `(f)`-adic completion form a glueing pair
(Stacks, Remark 15.92.7). No noetherian hypothesis is needed: the completion has the same
quotients by the powers of `f`, and `f` stays a nonzerodivisor in it, so neither ring has
`f`-power torsion. -/
theorem glueingPair_adicCompletion (hf : IsRegular f) :
    TauCeti.GlueingPair (AdicCompletion (Ideal.span {f}) R) f := by
  have hI (n : ℕ) : (Ideal.span {f} ^ n).map (algebraMap R (AdicCompletion (Ideal.span {f}) R)) =
      Ideal.span {algebraMap R (AdicCompletion (Ideal.span {f}) R) f ^ n} := by
    simp [Ideal.span_singleton_pow, Ideal.map_span]
  have htors {A : Type u} [CommRing A] {a : A} (ha : IsRegular a) :
      Submodule.torsion' A A (Submonoid.powers a) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr ?_
    rintro x ⟨⟨_, k, rfl⟩, hk⟩
    exact (ha.pow k).left (hk.trans (mul_zero _).symm)
  refine ⟨fun n y ↦ ?_, fun n ↦ ?_, ?_⟩
  · simpa [hI] using AdicCompletion.exists_sub_algebraMap_mem_map_pow
      (Submodule.fg_span_singleton f) n y
  · ext x
    rw [Ideal.mem_comap, ← hI, AdicCompletion.algebraMap_mem_map_pow_iff, Ideal.span_singleton_pow]
  · rw [htors hf, htors hf.adicCompletion, Submodule.bot_coe, Submodule.bot_coe]
    exact Set.bijOn_singleton.mpr (map_zero _)

end IsRegular
