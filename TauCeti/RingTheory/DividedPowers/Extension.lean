/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import TauCeti.RingTheory.DividedPowers.Generators

import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Ideal
import TauCeti.Algebra.Group.Pow
import TauCeti.RingTheory.Ideal.Maps
import TauCeti.RingTheory.RingHom.Flat

/-!
# Extension of divided powers along principal ideals, flat maps, and localizations

Let `f : A →+* B` be a homomorphism of commutative rings (or semirings where subtraction is not
needed), and let `hI : DividedPowers I` be a divided power structure on an ideal `I` of `A`.
An extension of `hI` to `I.map f` is a divided power structure `hJ : DividedPowers (I.map f)`
making `f` a divided power morphism (`DividedPowers.IsDPMorphism hI hJ f`).

We prove Stacks Project Lemma 23.4.2 (Tag 07H1):

* **Uniqueness** (`DividedPowers.eq_of_isDPMorphism_map`): an extension to `I.map f` is unique
  whenever it exists, with no flatness or injectivity assumption on `f`.
* **Principal ideals** (`DividedPowers.ofPrincipal`): when `I = Ideal.span {x}`, the unique
  extension exists along an arbitrary semiring homomorphism `f : A →+* B`, given by
  `dpow n (b * f x) = b ^ n * f (hI.dpow n x)`.
* **Flat homomorphisms** (`DividedPowers.ofFlat`): when `f.Flat`, the unique extension exists and
  evaluates on a finite sum `∑ i ∈ s, b i * f (x i)` (`x i ∈ I`) to the scalar-extension
  coefficient formula `DividedPowers.extCoeff hI f n s b x`. Well-definedness is proved by
  expressing `extCoeff` as the coefficients of a product of scaled exponential power series
  (yielding invariance under finite scalar substitutions without flatness) and applying the
  equational criterion for flatness (`RingHom.Flat.exists_eq_sum_mul_of_sum_mul_eq`).
* **Localizations** (`DividedPowers.ofLocalization`): for any localization `B` of a commutative
  semiring `A` at a submonoid `S`, direct evaluation on fractions gives the unique extension to
  `I.map (algebraMap A B)`, satisfying
  `dpow n (IsLocalization.mk' B x s) = IsLocalization.mk' B (hI.dpow n x) (s ^ n)`, and agreeing
  with `ofFlat` over commutative rings (`DividedPowers.ofLocalization_eq_ofFlat`).

## Main definitions

* `DividedPowers.ofPrincipal`: extension of `DividedPowers I` along any `f : A →+* B` when `I` is
  principal.
* `DividedPowers.extCoeff`: the scalar-extension coefficient formula
  `∑ e ∈ piAntidiag s n, ∏ i ∈ s, b i ^ e i * f (hI.dpow (e i) (x i))`.
* `DividedPowers.flatCandidate`: the `TauCeti.AdditivePowers (I.map f)` candidate for flat `f`.
* `DividedPowers.ofFlat`: the unique extension of `DividedPowers I` along a flat `f : A →+* B`.
* `DividedPowers.ofLocalization`: the unique extension of `DividedPowers I` to a localization.

## Main results

* `DividedPowers.eq_of_isDPMorphism_map`: uniqueness of an extension to `I.map f`.
* `DividedPowers.extCoeff_substitution`: invariance of `extCoeff` under finite scalar
  substitutions, without flatness.
* `DividedPowers.extCoeff_eq_of_sum_eq`: presentation-independence of `extCoeff` for flat `f`.
* `DividedPowers.isDPMorphism_ofFlat_iff`: universal property of `ofFlat`.
* `DividedPowers.ofFlat_comp_dpow`: functoriality of `ofFlat` under composition of flat maps.
* `DividedPowers.ofLocalization_dpow_mk'`: formula for divided powers of fractions `x / s`.
* `DividedPowers.ofLocalization_eq_ofFlat`: agreement of `ofLocalization` with `ofFlat`.

## References

* [Stacks: Divided Power Algebra, Lemma 07H1](https://stacks.math.columbia.edu/tag/07H1).
* P. Berthelot, *Cohomologie cristalline des schémas de caractéristique $p > 0$*,
  Lecture Notes in Math. 407, Springer (1974), I §2.7.
* Mathlib's `DividedPowers`, from the formalization of A. Chambert-Loir and
  M. I. de Frutos-Fernández.
-/

public section

open Finset

namespace DividedPowers

section UniquenessAndPrincipal

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}

/-- Any two divided power structures on `I.map f` making `f` a divided power morphism from `hI`
are equal (Stacks Project Lemma 23.4.2, Tag 07H1). -/
theorem eq_of_isDPMorphism_map (hI : DividedPowers I) {f : A →+* B}
    {hJ hJ' : DividedPowers (I.map f)}
    (h1 : IsDPMorphism hI hJ f) (h2 : IsDPMorphism hI hJ' f) :
    hJ = hJ' :=
  DividedPowers.ext hJ hJ' fun n _ hy ↦
    ((mem_dpEqualizer_iff hJ hJ').mp
      (le_equalizer_of_isDPMorphism hI f le_rfl hJ hJ' h1 h2 hy)).2 n

/-- Well-definedness of the principal-ideal extension formula: if `I = Ideal.span {x}` and
`b * f x = c * f x`, then `b ^ n * f (hI.dpow n x) = c ^ n * f (hI.dpow n x)` for every `n`. -/
theorem pow_mul_map_dpow_eq_of_mul_eq (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) {b c : B} (hbc : b * f x = c * f x) (n : ℕ) :
    b ^ n * f (hI.dpow n x) = c ^ n * f (hI.dpow n x) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hmem : hI.dpow n x ∈ Ideal.span {x} := hx ▸ hI.dpow_mem hn (hx ▸ Ideal.subset_span rfl)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [← ha, map_mul]
    calc
      b ^ n * (f a * f x) = f a * (b ^ n * f x) := by ring
      _ = f a * (c ^ n * f x) := by rw [TauCeti.pow_mul_eq_pow_mul_of_mul_eq hbc n]
      _ = c ^ n * (f a * f x) := by ring

private noncomputable def principalDpow (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) (n : ℕ) (y : B) : B :=
  open scoped Classical in
  if hy : y ∈ I.map f then
    have hy' : y ∈ Ideal.span {f x} := by
      rwa [hx, Ideal.map_span, Set.image_singleton] at hy
    (Ideal.mem_span_singleton'.mp hy').choose ^ n * f (hI.dpow n x)
  else 0

private theorem principalDpow_mul (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) (n : ℕ) (b : B) :
    principalDpow hI hx f n (b * f x) = b ^ n * f (hI.dpow n x) := by
  classical
  have hy : b * f x ∈ I.map f := by
    rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨b, rfl⟩
  simp only [principalDpow, dite_eq_left hy]
  have hy' : b * f x ∈ Ideal.span {f x} := by
    rwa [hx, Ideal.map_span, Set.image_singleton] at hy
  exact hI.pow_mul_map_dpow_eq_of_mul_eq hx f (Ideal.mem_span_singleton'.mp hy').choose_spec n

private theorem add_pow_mul_map_dpow (hI : DividedPowers I) {x : A} (hx : x ∈ I) (f : A →+* B)
    (b c : B) (n : ℕ) :
    (b + c) ^ n * f (hI.dpow n x) =
      ∑ k ∈ antidiagonal n, (b ^ k.1 * f (hI.dpow k.1 x)) * (c ^ k.2 * f (hI.dpow k.2 x)) := by
  rw [add_pow, sum_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hsum : k + (n - k) = n := Nat.add_sub_of_le hkn
  have hmul : hI.dpow k x * hI.dpow (n - k) x = (n.choose k : A) * hI.dpow n x := by
    have h := hI.mul_dpow (m := k) (n := n - k) hx
    rwa [hsum] at h
  calc
    b ^ k * c ^ (n - k) * (n.choose k : B) * f (hI.dpow n x)
      = b ^ k * c ^ (n - k) * f ((n.choose k : A) * hI.dpow n x) := by
        rw [map_mul, map_natCast]; ring
    _ = b ^ k * c ^ (n - k) * f (hI.dpow k x * hI.dpow (n - k) x) := by rw [hmul]
    _ = (b ^ k * f (hI.dpow k x)) * (c ^ (n - k) * f (hI.dpow (n - k) x)) := by
        rw [map_mul]; ring

private theorem principalDpow_mul_dpow (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) {m n : ℕ} {y : B} (hy : y ∈ I.map f) :
    principalDpow hI hx f m y * principalDpow hI hx f n y =
      ((m + n).choose m : B) * principalDpow hI hx f (m + n) y := by
  rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy
  obtain ⟨b, rfl⟩ := hy
  rw [principalDpow_mul, principalDpow_mul, principalDpow_mul]
  calc
    b ^ m * f (hI.dpow m x) * (b ^ n * f (hI.dpow n x))
      = b ^ (m + n) * f (hI.dpow m x * hI.dpow n x) := by rw [pow_add, map_mul]; ring
    _ = b ^ (m + n) * f (((m + n).choose m : A) * hI.dpow (m + n) x) := by
        rw [hI.mul_dpow (hx ▸ Ideal.subset_span rfl)]
    _ = ((m + n).choose m : B) * (b ^ (m + n) * f (hI.dpow (m + n) x)) := by
        rw [map_mul, map_natCast]; ring

private theorem principalDpow_dpow_comp (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) {m n : ℕ} (hn : n ≠ 0) {y : B} (hy : y ∈ I.map f) :
    principalDpow hI hx f m (principalDpow hI hx f n y) =
      (Nat.uniformBell m n : B) * principalDpow hI hx f (m * n) y := by
  rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy
  obtain ⟨b, rfl⟩ := hy
  have hxI : x ∈ I := hx ▸ Ideal.subset_span rfl
  have hmem : hI.dpow n x ∈ Ideal.span {x} := hx ▸ hI.dpow_mem hn hxI
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [principalDpow_mul, principalDpow_mul, ← ha, map_mul, ← mul_assoc, principalDpow_mul,
    mul_pow, ← pow_mul, mul_comm n m, mul_assoc, ← map_pow, ← map_mul, ← hI.dpow_mul hxI, ha,
    hI.dpow_comp hn hxI, map_mul, map_natCast]
  ring

/-- Extension of divided powers on a principal ideal `I = Ideal.span {x}` along an arbitrary
homomorphism `f : A →+* B`, without any flatness hypothesis (Stacks Project Lemma 23.4.2,
Tag 07H1). -/
noncomputable def ofPrincipal (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) : DividedPowers (I.map f) where
  dpow := principalDpow hI hx f
  dpow_null {n y} hy := by classical simp [principalDpow, hy]
  dpow_zero {y} hy := by
    rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy
    obtain ⟨b, rfl⟩ := hy
    rw [principalDpow_mul, pow_zero, one_mul, hI.dpow_zero (hx ▸ Ideal.subset_span rfl), map_one]
  dpow_one {y} hy := by
    rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy
    obtain ⟨b, rfl⟩ := hy
    rw [principalDpow_mul, pow_one, hI.dpow_one (hx ▸ Ideal.subset_span rfl)]
  dpow_mem {n y} hn hy := by
    rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy
    obtain ⟨b, rfl⟩ := hy
    rw [principalDpow_mul]
    exact Ideal.mul_mem_left _ _
      (Ideal.mem_map_of_mem f (hI.dpow_mem hn (hx ▸ Ideal.subset_span rfl)))
  dpow_add {n y z} hy hz := by
    rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy hz
    obtain ⟨b, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hz
    rw [← add_mul, principalDpow_mul, add_pow_mul_map_dpow hI (hx ▸ Ideal.subset_span rfl)]
    exact sum_congr rfl fun k _ ↦ by rw [principalDpow_mul, principalDpow_mul]
  dpow_mul {n r y} hy := by
    rw [hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy
    obtain ⟨b, rfl⟩ := hy
    rw [← mul_assoc, principalDpow_mul, principalDpow_mul, mul_pow, mul_assoc]
  mul_dpow hy := principalDpow_mul_dpow hI hx f hy
  dpow_comp hn hy := principalDpow_dpow_comp hI hx f hn hy

/-- Evaluation of the principal extension on `b * f x`. -/
@[simp]
theorem ofPrincipal_dpow_mul (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) (n : ℕ) (b : B) :
    (hI.ofPrincipal hx f).dpow n (b * f x) = b ^ n * f (hI.dpow n x) :=
  principalDpow_mul hI hx f n b

/-- Evaluation of the principal extension on the generator image `f x`. -/
@[simp]
theorem ofPrincipal_dpow_apply (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) (n : ℕ) :
    (hI.ofPrincipal hx f).dpow n (f x) = f (hI.dpow n x) := by
  simpa using hI.ofPrincipal_dpow_mul hx f n 1

/-- The ring homomorphism `f` is a divided power morphism into `hI.ofPrincipal hx f`. -/
theorem isDPMorphism_ofPrincipal (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) :
    IsDPMorphism hI (hI.ofPrincipal hx f) f := by
  refine ⟨le_rfl, fun a ha ↦ ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp (hx ▸ ha)
  rw [map_mul, ofPrincipal_dpow_mul, hI.dpow_mul (hx ▸ Ideal.subset_span rfl), map_mul, map_pow]

/-- Uniqueness of the principal-ideal extension: any `DividedPowers (I.map f)` making `f` a
divided power morphism equals `hI.ofPrincipal hx f`. -/
theorem eq_ofPrincipal_of_isDPMorphism (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    {f : A →+* B} {hJ : DividedPowers (I.map f)} (h : IsDPMorphism hI hJ f) :
    hJ = hI.ofPrincipal hx f :=
  hI.eq_of_isDPMorphism_map h (hI.isDPMorphism_ofPrincipal hx f)

/-- Universal property of `ofPrincipal`: a homomorphism `g : B →+* C` is a PD morphism out of
`hI.ofPrincipal hx f` if and only if `g.comp f` is a PD morphism out of `hI`. -/
theorem isDPMorphism_ofPrincipal_iff (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (f : A →+* B) {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (hI.ofPrincipal hx f) hK g ↔ IsDPMorphism hI hK (g.comp f) :=
  ⟨fun hg ↦ hg.comp hK (hI.isDPMorphism_ofPrincipal hx f),
    fun hgf ↦ IsDPMorphism.of_comp hI (hI.ofPrincipal hx f) hK f g rfl
      (hI.isDPMorphism_ofPrincipal hx f) hgf⟩

/-- The principal extension does not depend on the choice of generator of `I`. -/
theorem ofPrincipal_congr (hI : DividedPowers I) {x y : A}
    (hx : I = Ideal.span {x}) (hy : I = Ideal.span {y}) (f : A →+* B) :
    hI.ofPrincipal hx f = hI.ofPrincipal hy f :=
  hI.eq_of_isDPMorphism_map (hI.isDPMorphism_ofPrincipal hx f) (hI.isDPMorphism_ofPrincipal hy f)

/-- Along the identity map, the principal extension recovers `hI`. -/
theorem ofPrincipal_id_dpow (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    (n : ℕ) (z : A) :
    (hI.ofPrincipal hx (RingHom.id A)).dpow n z = hI.dpow n z := by
  by_cases hz : z ∈ I
  · have h := (hI.isDPMorphism_ofPrincipal hx (RingHom.id A)).2 (n := n) z hz
    simpa using h
  · rw [DividedPowers.dpow_null _ (by rwa [Ideal.map_id]), hI.dpow_null hz]

end UniquenessAndPrincipal

section ExtCoeff

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}

/-- The scalar-extension coefficient formula
`∑_{∑_{i ∈ s} e i = n} ∏_{i ∈ s} b i ^ (e i) * f (hI.dpow (e i) (x i))`. -/
def extCoeff (hI : DividedPowers I) (f : A →+* B) (n : ℕ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b : ι → B) (x : ι → A) : B :=
  ∑ e ∈ piAntidiag s n, ∏ i ∈ s, b i ^ e i * f (hI.dpow (e i) (x i))

/-- The defining equation of `DividedPowers.extCoeff`. -/
theorem extCoeff_def (hI : DividedPowers I) (f : A →+* B) (n : ℕ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b : ι → B) (x : ι → A) :
    hI.extCoeff f n s b x =
      ∑ e ∈ piAntidiag s n, ∏ i ∈ s, b i ^ e i * f (hI.dpow (e i) (x i)) := (rfl)

/-- Multiset-indexed form of `DividedPowers.extCoeff`. -/
theorem extCoeff_eq_sum_sym (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → B) (x : ι → A) :
    hI.extCoeff f n s b x =
      ∑ k ∈ s.sym n,
        ∏ i ∈ s, b i ^ Multiset.count i k * f (hI.dpow (Multiset.count i k) (x i)) := by
  rw [extCoeff_def, ← map_sym_eq_piAntidiag, sum_map]
  rfl

/-- `extCoeff` depends only on the values of `b` and `x` on `s`. -/
theorem extCoeff_congr (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {b b' : ι → B} {x x' : ι → A}
    (hb : ∀ i ∈ s, b i = b' i) (hx : ∀ i ∈ s, x i = x' i) :
    hI.extCoeff f n s b x = hI.extCoeff f n s b' x' := by
  rw [extCoeff_def, extCoeff_def]
  exact sum_congr rfl fun _ _ ↦ prod_congr rfl fun i hi ↦ by rw [hb i hi, hx i hi]

private def scaledExp (hI : DividedPowers I) (f : A →+* B) (b : B) (x : A) : PowerSeries B :=
  PowerSeries.mk fun n ↦ b ^ n * f (hI.dpow n x)

private theorem coeff_scaledExp (hI : DividedPowers I) (f : A →+* B) (b : B) (x : A) (n : ℕ) :
    PowerSeries.coeff n (scaledExp hI f b x) = b ^ n * f (hI.dpow n x) :=
  PowerSeries.coeff_mk n _

private theorem scaledExp_zero_left (hI : DividedPowers I) (f : A →+* B) {x : A} (hx : x ∈ I) :
    scaledExp hI f 0 x = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_scaledExp, hI.dpow_zero hx]
  · simp [coeff_scaledExp, zero_pow hn, PowerSeries.coeff_one, hn]

private theorem scaledExp_zero_right (hI : DividedPowers I) (f : A →+* B) (b : B) :
    scaledExp hI f b 0 = 1 := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_scaledExp, hI.dpow_zero I.zero_mem]
  · simp [coeff_scaledExp, hI.dpow_eval_zero hn, PowerSeries.coeff_one, hn]

private theorem scaledExp_add_left (hI : DividedPowers I) (f : A →+* B) (b c : B)
    {x : A} (hx : x ∈ I) :
    scaledExp hI f (b + c) x = scaledExp hI f b x * scaledExp hI f c x := by
  ext n
  rw [coeff_scaledExp, PowerSeries.coeff_mul, add_pow_mul_map_dpow hI hx f b c n]
  exact sum_congr rfl fun k _ ↦ by rw [coeff_scaledExp, coeff_scaledExp]

private theorem scaledExp_add_right (hI : DividedPowers I) (f : A →+* B) (b : B)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    scaledExp hI f b (x + y) = scaledExp hI f b x * scaledExp hI f b y := by
  ext n
  rw [coeff_scaledExp, PowerSeries.coeff_mul, hI.dpow_add hx hy, map_sum, mul_sum]
  refine sum_congr rfl fun ⟨i, j⟩ hk ↦ ?_
  have hij : i + j = n := mem_antidiagonal.mp hk
  rw [coeff_scaledExp, coeff_scaledExp, ← hij, pow_add, map_mul]
  ring

private theorem scaledExp_mul (hI : DividedPowers I) (f : A →+* B) (b : B) (a : A)
    {x : A} (hx : x ∈ I) :
    scaledExp hI f (b * f a) x = scaledExp hI f b (a * x) := by
  ext n
  rw [coeff_scaledExp, coeff_scaledExp, hI.dpow_mul hx, mul_pow, map_mul, map_pow]
  ring

private theorem scaledExp_sum_left (hI : DividedPowers I) (f : A →+* B)
    {κ : Type*} {t : Finset κ} (u : κ → B) {x : A} (hx : x ∈ I) :
    scaledExp hI f (∑ j ∈ t, u j) x = ∏ j ∈ t, scaledExp hI f (u j) x := by
  classical
  induction t using Finset.induction with
  | empty => simp [scaledExp_zero_left hI f hx]
  | insert a t ha ih =>
    rw [sum_insert ha, prod_insert ha, scaledExp_add_left hI f _ _ hx, ih]

private theorem scaledExp_sum_right (hI : DividedPowers I) (f : A →+* B)
    {ι : Type*} {s : Finset ι} (c : B) {y : ι → A} (hy : ∀ i ∈ s, y i ∈ I) :
    scaledExp hI f c (∑ i ∈ s, y i) = ∏ i ∈ s, scaledExp hI f c (y i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [scaledExp_zero_right]
  | insert a s ha ih =>
    have hy' : ∀ i ∈ s, y i ∈ I := fun i hi ↦ hy i (mem_insert_of_mem hi)
    rw [sum_insert ha, prod_insert ha,
      scaledExp_add_right hI f c (hy a (mem_insert_self a s)) (Submodule.sum_mem I hy'), ih hy']

private theorem extCoeff_eq_coeff_prod_scaledExp (hI : DividedPowers I) (f : A →+* B)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → B) (x : ι → A) (n : ℕ) :
    hI.extCoeff f n s b x = PowerSeries.coeff n (∏ i ∈ s, scaledExp hI f (b i) (x i)) := by
  induction s using Finset.cons_induction generalizing n with
  | empty =>
    rw [extCoeff_def, piAntidiag_empty, prod_empty, PowerSeries.coeff_one]
    split_ifs <;> simp
  | cons a s ha ih =>
    rw [extCoeff_def, piAntidiag_cons ha, sum_disjiUnion, prod_cons, PowerSeries.coeff_mul]
    refine sum_congr rfl fun ⟨k₁, k₂⟩ _ ↦ ?_
    rw [sum_map, coeff_scaledExp, ← ih k₂, extCoeff_def, mul_sum]
    refine sum_congr rfl fun e he ↦ ?_
    have hea : e a = 0 := by
      by_contra h
      exact ha ((mem_piAntidiag.mp he).2 a h)
    rw [prod_cons]
    simp only [addRightEmbedding_apply, Pi.add_apply, hea, zero_add, ↓reduceIte]
    congr 1
    refine prod_congr rfl fun i hi ↦ ?_
    have hne : i ≠ a := fun h ↦ ha (h ▸ hi)
    simp [hne]

/-- On the empty finset, `extCoeff` is `1` in degree `0` and `0` in positive degrees. -/
@[simp]
theorem extCoeff_empty (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [DecidableEq ι] (b : ι → B) (x : ι → A) :
    hI.extCoeff f n ∅ b x = if n = 0 then 1 else 0 := by
  rw [extCoeff_eq_coeff_prod_scaledExp, prod_empty, PowerSeries.coeff_one]

/-- In degree `0`, `extCoeff` equals `1` when all `x i ∈ I`. -/
@[simp]
theorem extCoeff_zero (hI : DividedPowers I) (f : A →+* B)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (b : ι → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    hI.extCoeff f 0 s b x = 1 := by
  rw [extCoeff_def, piAntidiag_zero, sum_singleton]
  exact prod_eq_one fun i hi ↦ by simp [hI.dpow_zero (hx i hi)]

/-- On a singleton `{i}`, `extCoeff` equals `b i ^ n * f (hI.dpow n (x i))`. -/
@[simp]
theorem extCoeff_singleton (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [DecidableEq ι] (i : ι) (b : ι → B) (x : ι → A) :
    hI.extCoeff f n {i} b x = b i ^ n * f (hI.dpow n (x i)) := by
  rw [extCoeff_eq_coeff_prod_scaledExp, prod_singleton, coeff_scaledExp]

/-- Insertion law for `extCoeff`. -/
theorem extCoeff_cons (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [DecidableEq ι] {a : ι} {s : Finset ι} (ha : a ∉ s) (b : ι → B) (x : ι → A) :
    hI.extCoeff f n (cons a s ha) b x =
      ∑ k ∈ antidiagonal n, (b a ^ k.1 * f (hI.dpow k.1 (x a))) * hI.extCoeff f k.2 s b x := by
  rw [extCoeff_eq_coeff_prod_scaledExp, prod_cons, PowerSeries.coeff_mul]
  exact sum_congr rfl fun k _ ↦ by rw [coeff_scaledExp, extCoeff_eq_coeff_prod_scaledExp]

/-- Disjoint union law for `extCoeff`: splitting a finite presentation corresponds to antidiagonal
convolution. -/
theorem extCoeff_disjUnion (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι : Type*} [DecidableEq ι] {s t : Finset ι} (hst : Disjoint s t) (b : ι → B) (x : ι → A) :
    hI.extCoeff f n (s.disjUnion t hst) b x =
      ∑ k ∈ antidiagonal n, hI.extCoeff f k.1 s b x * hI.extCoeff f k.2 t b x := by
  rw [extCoeff_eq_coeff_prod_scaledExp, prod_disjUnion, PowerSeries.coeff_mul]
  exact sum_congr rfl fun k _ ↦ by
    rw [extCoeff_eq_coeff_prod_scaledExp, extCoeff_eq_coeff_prod_scaledExp]

/-- In degree `1`, `extCoeff` equals the linear combination `∑ i ∈ s, b i * f (x i)`. -/
@[simp]
theorem extCoeff_one (hI : DividedPowers I) (f : A →+* B)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (b : ι → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    hI.extCoeff f 1 s b x = ∑ i ∈ s, b i * f (x i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hx' : ∀ i ∈ s, x i ∈ I := fun i hi ↦ hx i (mem_cons_of_mem hi)
    have hxa : x a ∈ I := hx a (mem_cons_self a s)
    rw [extCoeff_cons, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ, sum_range_one,
      sum_cons]
    simp [hI.dpow_zero hxa, hI.dpow_one hxa, extCoeff_zero hI f b hx', ih hx', add_comm]

/-- In degree `2` on a two-element set `{i, j}` (`i ≠ j`), `extCoeff` expands to the quadratic
divided-power formula. -/
theorem extCoeff_pair_two (hI : DividedPowers I) (f : A →+* B)
    {ι : Type*} [DecidableEq ι] {i j : ι} (hij : i ≠ j) (b : ι → B) {x : ι → A}
    (hi : x i ∈ I) (hj : x j ∈ I) :
    hI.extCoeff f 2 {i, j} b x =
      b i ^ 2 * f (hI.dpow 2 (x i)) + b i * b j * f (x i * x j) +
        b j ^ 2 * f (hI.dpow 2 (x j)) := by
  have hcons : ({i, j} : Finset ι) = cons i {j} (by simp [hij]) := by simp
  rw [hcons, extCoeff_cons, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ,
    sum_range_succ, sum_range_one]
  simp only [Nat.sub_zero, Nat.reduceSub, Nat.sub_self, extCoeff_singleton, pow_zero, pow_one,
    hI.dpow_zero hi, hI.dpow_one hi, hI.dpow_zero hj, hI.dpow_one hj, map_one, map_mul]
  ring

/-- In positive degree, `extCoeff` always lies in `I.map f`. -/
theorem extCoeff_mem (hI : DividedPowers I) (f : A →+* B) {n : ℕ} (hn : n ≠ 0)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → B) (x : ι → A) :
    hI.extCoeff f n s b x ∈ I.map f := by
  rw [extCoeff_def]
  refine Submodule.sum_mem _ fun e he ↦ ?_
  have hsum : ∑ i ∈ s, e i = n := (mem_piAntidiag.mp he).1
  obtain ⟨j, hj, hej⟩ : ∃ j ∈ s, e j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hn (hsum ▸ sum_eq_zero hall)
  rw [← mul_prod_erase s _ hj]
  by_cases hxj : x j ∈ I
  · exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem f (hI.dpow_mem hej hxj)))
  · rw [hI.dpow_null hxj, map_zero, mul_zero, zero_mul]
    exact Submodule.zero_mem _

/-- Scaling every coefficient `b i` by `r` scales `extCoeff` by `r ^ n`. -/
theorem extCoeff_smul (hI : DividedPowers I) (f : A →+* B) (n : ℕ) (r : B)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → B) (x : ι → A) :
    hI.extCoeff f n s (fun i ↦ r * b i) x = r ^ n * hI.extCoeff f n s b x := by
  rw [extCoeff_def, extCoeff_def, mul_sum]
  refine sum_congr rfl fun e he ↦ ?_
  have hsum : ∑ i ∈ s, e i = n := (mem_piAntidiag.mp he).1
  have hprod : ∏ i ∈ s, (r * b i) ^ e i * f (hI.dpow (e i) (x i)) =
      (∏ i ∈ s, r ^ e i) * ∏ i ∈ s, b i ^ e i * f (hI.dpow (e i) (x i)) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ ↦ by rw [mul_pow, mul_assoc]
  rw [hprod, prod_pow_eq_pow_sum, hsum]

/-- If `f` is a divided power morphism from `(I, hI)` to `(J, hJ)`, then `hJ.dpow n` on any finite
combination `∑ i ∈ s, b i * f (x i)` (`x i ∈ I`) is given by `extCoeff`. -/
theorem dpow_sum_of_isDPMorphism (hI : DividedPowers I) {J : Ideal B} (hJ : DividedPowers J)
    {f : A →+* B} (hf : IsDPMorphism hI hJ f) (n : ℕ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (b : ι → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    hJ.dpow n (∑ i ∈ s, b i * f (x i)) = hI.extCoeff f n s b x := by
  rw [hJ.dpow_sum fun i hi ↦ J.mul_mem_left _ (hf.1 (Ideal.mem_map_of_mem f (hx i hi))),
    hI.extCoeff_eq_sum_sym]
  refine sum_congr rfl fun k _ ↦ prod_congr rfl fun i hi ↦ ?_
  rw [hJ.dpow_mul (hf.1 (Ideal.mem_map_of_mem f (hx i hi))), hf.2 _ (hx i hi)]

/-- **Invariance under finite scalar substitution**: for `x i ∈ I`, `a i j ∈ A`, and `c j ∈ B`,
setting `b i = ∑ j ∈ t, f (a i j) * c j` and `y j = ∑ i ∈ s, a i j * x i` gives
`extCoeff hI f n s b x = extCoeff hI f n t c y`, with no flatness hypothesis. -/
theorem extCoeff_substitution (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (a : ι → κ → A) (c : κ → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    hI.extCoeff f n s (fun i ↦ ∑ j ∈ t, f (a i j) * c j) x =
      hI.extCoeff f n t c (fun j ↦ ∑ i ∈ s, a i j * x i) := by
  rw [extCoeff_eq_coeff_prod_scaledExp, extCoeff_eq_coeff_prod_scaledExp]
  congr 1
  calc
    ∏ i ∈ s, scaledExp hI f (∑ j ∈ t, f (a i j) * c j) (x i)
      = ∏ i ∈ s, ∏ j ∈ t, scaledExp hI f (f (a i j) * c j) (x i) :=
        prod_congr rfl fun i hi ↦ scaledExp_sum_left hI f _ (hx i hi)
    _ = ∏ j ∈ t, ∏ i ∈ s, scaledExp hI f (c j) (a i j * x i) := by
        rw [prod_comm]
        refine prod_congr rfl fun j _ ↦ prod_congr rfl fun i hi ↦ ?_
        rw [mul_comm (f (a i j)), scaledExp_mul hI f _ _ (hx i hi)]
    _ = ∏ j ∈ t, scaledExp hI f (c j) (∑ i ∈ s, a i j * x i) :=
        prod_congr rfl fun j _ ↦
          (scaledExp_sum_right hI f (c j) fun i hi ↦ I.mul_mem_left _ (hx i hi)).symm

private theorem extCoeff_finAddCases (hI : DividedPowers I) (f : A →+* B) (n : ℕ)
    {r₁ r₂ : ℕ} (b₁ : Fin r₁ → B) (b₂ : Fin r₂ → B) (x₁ : Fin r₁ → A) (x₂ : Fin r₂ → A) :
    hI.extCoeff f n univ (Fin.addCases b₁ b₂) (Fin.addCases x₁ x₂) =
      ∑ k ∈ antidiagonal n, hI.extCoeff f k.1 univ b₁ x₁ * hI.extCoeff f k.2 univ b₂ x₂ := by
  rw [extCoeff_eq_coeff_prod_scaledExp, Fin.prod_univ_add, PowerSeries.coeff_mul]
  have h1 : ∏ i : Fin r₁, scaledExp hI f (Fin.addCases b₁ b₂ (Fin.castAdd r₂ i))
      (Fin.addCases x₁ x₂ (Fin.castAdd r₂ i)) = ∏ i : Fin r₁, scaledExp hI f (b₁ i) (x₁ i) :=
    prod_congr rfl fun i _ ↦ by simp
  have h2 : ∏ j : Fin r₂, scaledExp hI f (Fin.addCases b₁ b₂ (Fin.natAdd r₁ j))
      (Fin.addCases x₁ x₂ (Fin.natAdd r₁ j)) = ∏ j : Fin r₂, scaledExp hI f (b₂ j) (x₂ j) :=
    prod_congr rfl fun j _ ↦ by simp
  rw [h1, h2]
  exact sum_congr rfl fun k _ ↦ by
    rw [extCoeff_eq_coeff_prod_scaledExp, extCoeff_eq_coeff_prod_scaledExp]

end ExtCoeff

section FlatExtension

variable {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A}

/-- Over a flat ring homomorphism `f : A →+* B`, the scalar-extension coefficient formula depends
only on the represented element `∑ i ∈ s, b i * f (x i)` of `I.map f`. -/
theorem extCoeff_eq_of_sum_eq (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {s : Finset ι} {t : Finset κ} {b : ι → B} {b' : κ → B} {x : ι → A} {x' : κ → A}
    (hx : ∀ i ∈ s, x i ∈ I) (hx' : ∀ j ∈ t, x' j ∈ I)
    (hsum : ∑ i ∈ s, b i * f (x i) = ∑ j ∈ t, b' j * f (x' j)) (n : ℕ) :
    hI.extCoeff f n s b x = hI.extCoeff f n t b' x' := by
  obtain ⟨k, aL, aR, c, hbL, hbR, hy_eq⟩ := hf.exists_eq_sum_mul_of_sum_mul_eq hsum
  calc
    hI.extCoeff f n s b x
      = hI.extCoeff f n s (fun i ↦ ∑ l : Fin k, f (aL i l) * c l) x :=
        hI.extCoeff_congr f n hbL fun _ _ ↦ rfl
    _ = hI.extCoeff f n univ c (fun l ↦ ∑ i ∈ s, aL i l * x i) :=
        hI.extCoeff_substitution f n s univ aL c hx
    _ = hI.extCoeff f n univ c (fun l ↦ ∑ j ∈ t, aR j l * x' j) :=
        hI.extCoeff_congr f n (fun _ _ ↦ rfl) fun l _ ↦ hy_eq l
    _ = hI.extCoeff f n t (fun j ↦ ∑ l : Fin k, f (aR j l) * c l) x' :=
        (hI.extCoeff_substitution f n t univ aR c hx').symm
    _ = hI.extCoeff f n t b' x' :=
        hI.extCoeff_congr f n (fun j hj ↦ (hbR j hj).symm) fun _ _ ↦ rfl

private noncomputable def flatDpow (hI : DividedPowers I) (f : A →+* B) (n : ℕ) (z : B) : B :=
  open scoped Classical in
  if hz : z ∈ I.map f then
    have h := Ideal.mem_map_iff_exists_fin_sum.mp hz
    hI.extCoeff f n univ h.choose_spec.choose h.choose_spec.choose_spec.choose
  else 0

private theorem flatDpow_sum_eq (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat) (n : ℕ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (b : ι → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    flatDpow hI f n (∑ i ∈ s, b i * f (x i)) = hI.extCoeff f n s b x := by
  classical
  have hz : ∑ i ∈ s, b i * f (x i) ∈ I.map f :=
    Submodule.sum_mem _ fun i hi ↦ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem f (hx i hi))
  simp only [flatDpow, dite_eq_left hz]
  set h := Ideal.mem_map_iff_exists_fin_sum.mp hz
  exact hI.extCoeff_eq_of_sum_eq hf (fun i _ ↦ h.choose_spec.choose_spec.choose_spec.1 i) hx
    h.choose_spec.choose_spec.choose_spec.2 n

private theorem flatDpow_add (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat)
    {n : ℕ} {z₁ z₂ : B} (hz₁ : z₁ ∈ I.map f) (hz₂ : z₂ ∈ I.map f) :
    flatDpow hI f n (z₁ + z₂) =
      ∑ k ∈ antidiagonal n, flatDpow hI f k.1 z₁ * flatDpow hI f k.2 z₂ := by
  obtain ⟨r₁, b₁, x₁, hx₁, rfl⟩ := Ideal.mem_map_iff_exists_fin_sum.mp hz₁
  obtain ⟨r₂, b₂, x₂, hx₂, rfl⟩ := Ideal.mem_map_iff_exists_fin_sum.mp hz₂
  have hsum : (∑ i : Fin r₁, b₁ i * f (x₁ i)) + ∑ j : Fin r₂, b₂ j * f (x₂ j) =
      ∑ k : Fin (r₁ + r₂), Fin.addCases b₁ b₂ k * f (Fin.addCases x₁ x₂ k) := by
    rw [Fin.sum_univ_add]; simp
  have hmem : ∀ k ∈ (univ : Finset (Fin (r₁ + r₂))), Fin.addCases x₁ x₂ k ∈ I := fun k _ ↦ by
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp [hx₁, hx₂]
  rw [hsum, flatDpow_sum_eq hI hf n _ hmem, extCoeff_finAddCases]
  exact sum_congr rfl fun k _ ↦ by
    rw [flatDpow_sum_eq hI hf k.1 b₁ fun i _ ↦ hx₁ i,
      flatDpow_sum_eq hI hf k.2 b₂ fun j _ ↦ hx₂ j]

private theorem flatDpow_mul (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat)
    {n : ℕ} {a z : B} (hz : z ∈ I.map f) :
    flatDpow hI f n (a * z) = a ^ n * flatDpow hI f n z := by
  obtain ⟨r, b, x, hx, rfl⟩ := Ideal.mem_map_iff_exists_fin_sum.mp hz
  have hmul : a * ∑ i : Fin r, b i * f (x i) = ∑ i : Fin r, (a * b i) * f (x i) := by
    rw [mul_sum]; exact sum_congr rfl fun i _ ↦ by ring
  rw [hmul, flatDpow_sum_eq hI hf n _ fun i _ ↦ hx i,
    flatDpow_sum_eq hI hf n b fun i _ ↦ hx i, extCoeff_smul]

/-- The additive divided-power candidate on `I.map f` for a flat ring homomorphism `f : A →+* B`. -/
noncomputable def flatCandidate (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat) :
    TauCeti.AdditivePowers (I.map f) where
  dpow := flatDpow hI f
  dpow_null {n z} hz := by classical simp [flatDpow, hz]
  dpow_zero {z} hz := by
    obtain ⟨r, b, x, hx, rfl⟩ := Ideal.mem_map_iff_exists_fin_sum.mp hz
    rw [flatDpow_sum_eq hI hf 0 b fun i _ ↦ hx i, extCoeff_zero hI f b fun i _ ↦ hx i]
  dpow_one {z} hz := by
    obtain ⟨r, b, x, hx, rfl⟩ := Ideal.mem_map_iff_exists_fin_sum.mp hz
    rw [flatDpow_sum_eq hI hf 1 b fun i _ ↦ hx i, extCoeff_one hI f b fun i _ ↦ hx i]
  dpow_mem {n z} hn hz := by
    obtain ⟨r, b, x, hx, rfl⟩ := Ideal.mem_map_iff_exists_fin_sum.mp hz
    rw [flatDpow_sum_eq hI hf n b fun i _ ↦ hx i]
    exact hI.extCoeff_mem f hn univ b x
  dpow_add hz₁ hz₂ := flatDpow_add hI hf hz₁ hz₂
  dpow_mul hz := flatDpow_mul hI hf hz

/-- Evaluation of `flatCandidate` on any finite presentation `∑ i ∈ s, b i * f (x i)`. -/
theorem flatCandidate_dpow_sum (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat) (n : ℕ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (b : ι → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    (hI.flatCandidate hf).dpow n (∑ i ∈ s, b i * f (x i)) = hI.extCoeff f n s b x :=
  flatDpow_sum_eq hI hf n b hx

/-- `flatCandidate` preserves the base divided power operations on `I`. -/
theorem flatCandidate_dpow_map (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.flatCandidate hf).dpow n (f x) = f (hI.dpow n x) := by
  have h := hI.flatCandidate_dpow_sum hf n (s := ({()} : Finset Unit))
    (b := fun _ ↦ 1) (x := fun _ ↦ x) (fun _ _ ↦ hx)
  simpa using h

/-- The unique extension of `hI : DividedPowers I` along a flat ring homomorphism `f : A →+* B`
(Stacks Project Lemma 23.4.2, Tag 07H1). -/
noncomputable def ofFlat (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat) :
    DividedPowers (I.map f) :=
  (hI.flatCandidate hf).toDividedPowers (S := f '' (I : Set A)) (by rw [Ideal.map])
    (fun m n _ hs ↦ by
      rcases hs with ⟨x, hx, rfl⟩
      simp only [hI.flatCandidate_dpow_map hf _ hx]
      rw [← map_mul, hI.mul_dpow hx, map_mul, map_natCast])
    (fun m n hn _ hs ↦ by
      rcases hs with ⟨x, hx, rfl⟩
      rw [hI.flatCandidate_dpow_map hf n hx,
        hI.flatCandidate_dpow_map hf m (hI.dpow_mem hn hx),
        hI.flatCandidate_dpow_map hf (m * n) hx,
        hI.dpow_comp hn hx, map_mul, map_natCast])

/-- Evaluation of `ofFlat` on any finite presentation `∑ i ∈ s, b i * f (x i)` (`x i ∈ I`). -/
theorem ofFlat_dpow_sum (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat) (n : ℕ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (b : ι → B) {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) :
    (hI.ofFlat hf).dpow n (∑ i ∈ s, b i * f (x i)) = hI.extCoeff f n s b x := by
  rw [ofFlat, TauCeti.AdditivePowers.toDividedPowers_dpow]
  exact hI.flatCandidate_dpow_sum hf n b hx

/-- Evaluation of `ofFlat` on the image of an element of `I`. -/
@[simp]
theorem ofFlat_dpow_map (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat)
    (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.ofFlat hf).dpow n (f x) = f (hI.dpow n x) := by
  rw [ofFlat, TauCeti.AdditivePowers.toDividedPowers_dpow]
  exact hI.flatCandidate_dpow_map hf n hx

/-- The flat ring homomorphism `f` is a divided power morphism into `hI.ofFlat hf`. -/
theorem isDPMorphism_ofFlat (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat) :
    IsDPMorphism hI (hI.ofFlat hf) f :=
  ⟨le_rfl, fun _ ha ↦ hI.ofFlat_dpow_map hf _ ha⟩

/-- Uniqueness of the flat extension: any `DividedPowers (I.map f)` making `f` a divided power
morphism equals `hI.ofFlat hf`. -/
theorem eq_ofFlat_of_isDPMorphism (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat)
    {hJ : DividedPowers (I.map f)} (h : IsDPMorphism hI hJ f) :
    hJ = hI.ofFlat hf :=
  hI.eq_of_isDPMorphism_map h (hI.isDPMorphism_ofFlat hf)

/-- Universal property of `ofFlat`: a ring map `g : B →+* C` is a PD morphism out of `hI.ofFlat hf`
if and only if `g.comp f` is a PD morphism out of `hI`. -/
theorem isDPMorphism_ofFlat_iff (hI : DividedPowers I) {f : A →+* B} (hf : f.Flat)
    {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (hI.ofFlat hf) hK g ↔ IsDPMorphism hI hK (g.comp f) :=
  ⟨fun hg ↦ hg.comp hK (hI.isDPMorphism_ofFlat hf),
    fun hgf ↦ IsDPMorphism.of_comp hI (hI.ofFlat hf) hK f g rfl (hI.isDPMorphism_ofFlat hf) hgf⟩

/-- Functoriality of `ofFlat` under composition of flat ring homomorphisms. -/
theorem ofFlat_comp_dpow (hI : DividedPowers I) {C : Type*} [CommRing C]
    {f : A →+* B} {g : B →+* C} (hf : f.Flat) (hg : g.Flat) (n : ℕ) (z : C) :
    ((hI.ofFlat hf).ofFlat hg).dpow n z = (hI.ofFlat (hf.comp hg)).dpow n z := by
  let h₁ : DividedPowers (I.map (g.comp f)) :=
    ((hI.ofFlat hf).ofFlat hg).ofRingEquiv (e := RingEquiv.refl C)
      (by rw [Ideal.map_map]; exact Ideal.map_id _)
  have hm : IsDPMorphism hI h₁ (g.comp f) := by
    have hcomp := (isDPMorphism_ofFlat (hI.ofFlat hf) hg).comp
      ((hI.ofFlat hf).ofFlat hg) (hI.isDPMorphism_ofFlat hf)
    exact ⟨le_rfl, fun a ha ↦ by simpa [h₁] using hcomp.2 a ha⟩
  have heq : h₁ = hI.ofFlat (hf.comp hg) := hI.eq_ofFlat_of_isDPMorphism (hf.comp hg) hm
  simpa [h₁] using congrArg (fun h : DividedPowers (I.map (g.comp f)) ↦ h.dpow n z) heq

/-- Along the identity map, `ofFlat` recovers `hI`. -/
theorem ofFlat_id_dpow (hI : DividedPowers I) (n : ℕ) (x : A) :
    (hI.ofFlat (RingHom.Flat.id A)).dpow n x = hI.dpow n x := by
  by_cases hx : x ∈ I
  · simpa using hI.ofFlat_dpow_map (RingHom.Flat.id A) n hx
  · rw [DividedPowers.dpow_null _ (by rwa [Ideal.map_id]), hI.dpow_null hx]

/-- On a principal ideal, the flat extension agrees with the principal extension. -/
theorem ofFlat_eq_ofPrincipal (hI : DividedPowers I) {x : A} (hx : I = Ideal.span {x})
    {f : A →+* B} (hf : f.Flat) :
    hI.ofFlat hf = hI.ofPrincipal hx f :=
  hI.eq_of_isDPMorphism_map (hI.isDPMorphism_ofFlat hf) (hI.isDPMorphism_ofPrincipal hx f)

/-- Along a ring isomorphism `e : A ≃+* B`, `ofFlat` agrees with `DividedPowers.ofRingEquiv`. -/
theorem ofFlat_eq_ofRingEquiv (hI : DividedPowers I) (e : A ≃+* B) :
    hI.ofFlat (f := (e : A →+* B)) (RingHom.Flat.of_bijective e.bijective) =
      hI.ofRingEquiv (e := e) rfl := by
  refine hI.eq_of_isDPMorphism_map (hI.isDPMorphism_ofFlat _) ⟨le_rfl, fun a _ ↦ ?_⟩
  simp

end FlatExtension

section Localization

variable {A : Type*} [CommSemiring A] {I : Ideal A}

private theorem mk'_dpow_eq_of_mk'_eq (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    {s t : S} (hxy : IsLocalization.mk' B x s = IsLocalization.mk' B y t) (n : ℕ) :
    IsLocalization.mk' B (hI.dpow n x) (s ^ n) = IsLocalization.mk' B (hI.dpow n y) (t ^ n) := by
  obtain ⟨c, hc⟩ := IsLocalization.eq.mp hxy
  have hdp := congrArg (hI.dpow n) hc
  rw [← mul_assoc, ← mul_assoc, hI.dpow_mul hx, hI.dpow_mul hy, mul_pow, mul_pow] at hdp
  refine IsLocalization.eq.mpr ⟨c ^ n, ?_⟩
  simpa [SubmonoidClass.coe_pow, mul_assoc] using hdp

private noncomputable def locDpow (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] (n : ℕ) (z : B) : B :=
  open scoped Classical in
  if hz : z ∈ I.map (algebraMap A B) then
    have h := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
    IsLocalization.mk' B (hI.dpow n h.choose.1.1) (h.choose.2 ^ n)
  else 0

private theorem locDpow_mk' (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] (n : ℕ) {x : A} (hx : x ∈ I) (s : S) :
    locDpow hI S B n (IsLocalization.mk' B x s) = IsLocalization.mk' B (hI.dpow n x) (s ^ n) := by
  classical
  have hz : IsLocalization.mk' B x s ∈ I.map (algebraMap A B) :=
    (IsLocalization.mem_map_algebraMap_iff S B).mpr
      ⟨⟨⟨x, hx⟩, s⟩, IsLocalization.mk'_spec B x s⟩
  simp only [locDpow, dite_eq_left hz]
  set h := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
  exact mk'_dpow_eq_of_mk'_eq hI S B h.choose.1.2 hx
    (IsLocalization.mk'_eq_iff_eq_mul.mpr h.choose_spec.symm) n

private theorem locDpow_add (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] {n : ℕ} {z₁ z₂ : B}
    (hz₁ : z₁ ∈ I.map (algebraMap A B)) (hz₂ : z₂ ∈ I.map (algebraMap A B)) :
    locDpow hI S B n (z₁ + z₂) =
      ∑ k ∈ antidiagonal n, locDpow hI S B k.1 z₁ * locDpow hI S B k.2 z₂ := by
  obtain ⟨⟨⟨x, hx⟩, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz₁
  obtain ⟨⟨⟨y, hy⟩, t⟩, hzt⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz₂
  rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hzs, IsLocalization.eq_mk'_iff_mul_eq.mpr hzt]
  have hxt : x * (t : A) ∈ I := I.mul_mem_right _ hx
  have hys : y * (s : A) ∈ I := I.mul_mem_right _ hy
  rw [← IsLocalization.mk'_add, locDpow_mk' hI S B n (I.add_mem hxt hys)]
  refine (IsLocalization.mk'_eq_iff_eq_mul).mpr ?_
  rw [hI.dpow_add hxt hys, map_sum, sum_mul]
  refine sum_congr rfl fun ⟨i, j⟩ hk ↦ ?_
  have hij : i + j = n := mem_antidiagonal.mp hk
  rw [locDpow_mk' hI S B i hx s, locDpow_mk' hI S B j hy t, mul_comm x (t : A), mul_comm y (s : A),
    hI.dpow_mul hx, hI.dpow_mul hy, SubmonoidClass.coe_pow, Submonoid.coe_mul, mul_pow, ← hij,
    pow_add, pow_add, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
  have hs := IsLocalization.mk'_spec B (hI.dpow i x) (s ^ i)
  have ht := IsLocalization.mk'_spec B (hI.dpow j y) (t ^ j)
  rw [SubmonoidClass.coe_pow] at hs ht
  calc
    algebraMap A B ((t : A) ^ i) * algebraMap A B (hI.dpow i x) *
        (algebraMap A B ((s : A) ^ j) * algebraMap A B (hI.dpow j y))
      = algebraMap A B ((t : A) ^ i) * algebraMap A B ((s : A) ^ j) *
          (IsLocalization.mk' B (hI.dpow i x) (s ^ i) * algebraMap A B ((s : A) ^ i)) *
          (IsLocalization.mk' B (hI.dpow j y) (t ^ j) * algebraMap A B ((t : A) ^ j)) := by
        rw [hs, ht]; ring
    _ = IsLocalization.mk' B (hI.dpow i x) (s ^ i) * IsLocalization.mk' B (hI.dpow j y) (t ^ j) *
        (algebraMap A B ((s : A) ^ i) * algebraMap A B ((s : A) ^ j) *
          (algebraMap A B ((t : A) ^ i) * algebraMap A B ((t : A) ^ j))) := by ring

private theorem locDpow_mul (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] {n : ℕ} {b z : B}
    (hz : z ∈ I.map (algebraMap A B)) :
    locDpow hI S B n (b * z) = b ^ n * locDpow hI S B n z := by
  obtain ⟨⟨⟨x, hx⟩, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
  rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hzs]
  obtain ⟨a, r, rfl⟩ := IsLocalization.exists_mk'_eq S b
  rw [← IsLocalization.mk'_mul, locDpow_mk' hI S B n (I.mul_mem_left a hx),
    locDpow_mk' hI S B n hx, hI.dpow_mul hx, mul_pow, IsLocalization.mk'_mul,
    IsLocalization.mk'_pow]

/-- The unique extension of `hI : DividedPowers I` to a localization `B` of a commutative semiring
`A` at a submonoid `S` (Stacks Project Lemma 23.4.2, Tag 07H1). -/
noncomputable def ofLocalization (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] :
    DividedPowers (I.map (algebraMap A B)) where
  dpow := locDpow hI S B
  dpow_null {n z} hz := by classical simp [locDpow, hz]
  dpow_zero {z} hz := by
    obtain ⟨⟨⟨x, hx⟩, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
    rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hzs, locDpow_mk' hI S B 0 hx s, hI.dpow_zero hx,
      pow_zero, IsLocalization.mk'_one, map_one]
  dpow_one {z} hz := by
    obtain ⟨⟨⟨x, hx⟩, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
    rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hzs, locDpow_mk' hI S B 1 hx s, hI.dpow_one hx,
      pow_one]
  dpow_mem {n z} hn hz := by
    obtain ⟨⟨⟨x, hx⟩, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
    rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hzs, locDpow_mk' hI S B n hx s,
      IsLocalization.mk'_mem_iff]
    exact Ideal.mem_map_of_mem _ (hI.dpow_mem hn hx)
  dpow_add hz₁ hz₂ := locDpow_add hI S B hz₁ hz₂
  dpow_mul hz := locDpow_mul hI S B hz
  mul_dpow {m n z} hz := by
    obtain ⟨⟨⟨x, hx⟩, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
    rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hzs, locDpow_mk' hI S B m hx s,
      locDpow_mk' hI S B n hx s, locDpow_mk' hI S B (m + n) hx s, ← IsLocalization.mk'_mul,
      hI.mul_dpow hx, ← pow_add, ← IsLocalization.mul_mk'_eq_mk'_of_mul, map_natCast]
  dpow_comp {m n z} hn hz := by
    obtain ⟨⟨⟨x, hx⟩, s⟩, hzs⟩ := (IsLocalization.mem_map_algebraMap_iff S B).mp hz
    rw [IsLocalization.eq_mk'_iff_mul_eq.mpr hzs, locDpow_mk' hI S B n hx s,
      locDpow_mk' hI S B m (hI.dpow_mem hn hx) (s ^ n), locDpow_mk' hI S B (m * n) hx s,
      hI.dpow_comp hn hx, ← pow_mul, mul_comm n m, ← IsLocalization.mul_mk'_eq_mk'_of_mul,
      map_natCast]

/-- Divided powers of a fraction `x / s` in a localization are given by `hI.dpow n x / s ^ n`. -/
@[simp]
theorem ofLocalization_dpow_mk' (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] (n : ℕ) {x : A} (hx : x ∈ I) (s : S) :
    (hI.ofLocalization S B).dpow n (IsLocalization.mk' B x s) =
      IsLocalization.mk' B (hI.dpow n x) (s ^ n) :=
  locDpow_mk' hI S B n hx s

/-- Evaluation of `ofLocalization` on `algebraMap A B x` for `x ∈ I`. -/
@[simp]
theorem ofLocalization_dpow_algebraMap (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] (n : ℕ) {x : A} (hx : x ∈ I) :
    (hI.ofLocalization S B).dpow n (algebraMap A B x) = algebraMap A B (hI.dpow n x) := by
  have h := hI.ofLocalization_dpow_mk' S B n hx 1
  simpa [IsLocalization.mk'_one] using h

/-- The localization map `algebraMap A B` is a divided power morphism into `ofLocalization`. -/
theorem isDPMorphism_ofLocalization (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B] :
    IsDPMorphism hI (hI.ofLocalization S B) (algebraMap A B) :=
  ⟨le_rfl, fun _ ha ↦ hI.ofLocalization_dpow_algebraMap S B _ ha⟩

/-- Uniqueness of the divided power extension to a localization. -/
theorem eq_ofLocalization_of_isDPMorphism (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B]
    {hJ : DividedPowers (I.map (algebraMap A B))} (h : IsDPMorphism hI hJ (algebraMap A B)) :
    hJ = hI.ofLocalization S B :=
  hI.eq_of_isDPMorphism_map h (hI.isDPMorphism_ofLocalization S B)

/-- Universal property of `ofLocalization`: a homomorphism `g : B →+* C` is a PD morphism out of
`hI.ofLocalization S B` if and only if `g.comp (algebraMap A B)` is a PD morphism out of `hI`. -/
theorem isDPMorphism_ofLocalization_iff (hI : DividedPowers I) (S : Submonoid A) (B : Type*)
    [CommSemiring B] [Algebra A B] [IsLocalization S B]
    {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K) (g : B →+* C) :
    IsDPMorphism (hI.ofLocalization S B) hK g ↔ IsDPMorphism hI hK (g.comp (algebraMap A B)) :=
  ⟨fun hg ↦ hg.comp hK (hI.isDPMorphism_ofLocalization S B),
    fun hgf ↦ IsDPMorphism.of_comp hI (hI.ofLocalization S B) hK (algebraMap A B) g rfl
      (hI.isDPMorphism_ofLocalization S B) hgf⟩

end Localization

/-- Over commutative rings, `ofLocalization` agrees with the flat extension along
`algebraMap A B`. -/
theorem ofLocalization_eq_ofFlat {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B] :
    hI.ofLocalization S B =
      hI.ofFlat (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S)) :=
  hI.eq_ofFlat_of_isDPMorphism _ (hI.isDPMorphism_ofLocalization S B)

end DividedPowers
