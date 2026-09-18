/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
public import TauCeti.RingTheory.DedekindDomain.Different.Basic

/-!
# The complementary module of a place, by valuations

Let `F' / k'` be an extension of the algebraic function field `F / k` with `F' / F` finite and
separable, let `P` be a place of `F / k`, and let `𝒪'_P` be the integral closure of its valuation
ring `𝒪_P` in `F'`.  The **complementary module**

`C_P = {z ∈ F' | Tr_{F'/F} (z · 𝒪'_P) ⊆ 𝒪_P}`

is Mathlib's trace dual `Submodule.traceDual 𝒪_P F 1` of the local model.  Stichtenoth describes
it as `t · 𝒪'_P` for an element `t` with `v_{P'}(t) = -d(P' ∣ P)` at every place `P'` above `P`
(Proposition 3.4.2 and Definition 3.4.3); this file proves the description in the form in which
it is used, as a valuation criterion:

`z ∈ C_P ↔ ∀ P' ∣ P, v_{P'}(z) ≤ exp d(P' ∣ P)`.

Its consequence `TauCeti.Place.valuation_trace_le_exp` is the local estimate behind the trace of
repartitions, and so behind the divisor of the cotrace of a Weil differential: if
`ord_{P'}(z) ≥ -(e(P' ∣ P) · n + d(P' ∣ P))` at every `P'` above `P`, then
`ord_P (Tr_{F'/F} z) ≥ -n`.  The estimate is sharp: relaxing the bound by one at a single place
`P'` over `P` makes every `x ∈ F` with `ord_P x ≥ -(n + 1)` a trace, which is what pins the divisor
of the cotrace down exactly.

The criterion is read off the different ideal `𝔡` of the local model, which is the inverse of
`C_P` as a fractional ideal: `z ∈ C_P` exactly when `z · 𝔡 ⊆ 𝒪'_P`
(`TauCeti.mem_traceDual_one_iff_forall_mem_differentIdeal`).  The order at `P'` of an
element of `𝔡` is at least `d(P' ∣ P)`, with equality for an element of `𝔡` outside the
`(d + 1)`-st power of the centre of `P'`; and `𝒪'_P` is the intersection of the valuation rings
of the places above `P` (`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`), which
is where the constant field `k'` has to be integral over `k`.

## Main results

* `TauCeti.Place.differentExponent_le_ord_of_mem_differentIdeal` and
  `TauCeti.Place.exists_mem_differentIdeal_ord_eq`: the smallest order at `P'` of a nonzero element
  of the different ideal of the local model is `d(P' ∣ P)`.
* `TauCeti.Place.valuation_le_exp_differentExponent_of_mem_traceDual`: an element of the
  complementary module has order at least `-d(P' ∣ P)` at `P'`.
* `TauCeti.Place.mem_traceDual_iff_forall_valuation_le`: **the valuation criterion for the
  complementary module** (Stichtenoth, Proposition 3.4.2 and Definition 3.4.3).
* `TauCeti.Place.valuation_trace_le_exp`: the trace estimate at a place.
* `TauCeti.Place.exists_forall_valuation_le_and_trace_eq`: the trace estimate is sharp.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.4.1, Proposition 3.4.2, Definition 3.4.3 and the proof of Theorem 3.4.6.
-/

public section

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (k F)

section OnePlace

variable (P' : Place k' F')

private theorem finiteMultiplicity_span {y : integralClosure (P'.restrict k F).integers F'}
    (hy0 : y ≠ 0) :
    FiniteMultiplicity (centerIntegralClosure k F P').asIdeal (Ideal.span {y}) :=
  .of_prime_left (Ideal.prime_of_isPrime (centerIntegralClosure k F P').ne_bot
    (centerIntegralClosure k F P').isPrime) (by simpa using hy0)

/-- **Elements of the different ideal vanish to order at least `d(P' ∣ P)` at `P'`**: the
different ideal of the local model is divisible by the `d(P' ∣ P)`-th power of the centre of
`P'`. -/
theorem differentExponent_le_ord_of_mem_differentIdeal
    {y : integralClosure (P'.restrict k F).integers F'}
    (hy : y ∈ differentIdeal (P'.restrict k F).integers
      (integralClosure (P'.restrict k F).integers F'))
    (hy0 : y ≠ 0) :
    (differentExponent k F P' : ℤ) ≤ P'.ord (algebraMap _ F' y) := by
  rw [P'.ord_algebraMap_eq_multiplicity_center
    (algebraMap_mem_integers_of_mem_integralClosure k F P') hy0, Nat.cast_le,
    ← centerIntegralClosure_def,
    ← (finiteMultiplicity_span k F P' hy0).pow_dvd_iff_le_multiplicity]
  exact dvd_trans ((pow_dvd_differentIdeal_iff_le_differentExponent k F P').mpr le_rfl)
    (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hy))

/-- **Some element of the different ideal vanishes to order exactly `d(P' ∣ P)` at `P'`**: the
`(d + 1)`-st power of the centre of `P'` does not divide the different ideal, so the different
ideal has an element outside it. -/
theorem exists_mem_differentIdeal_ord_eq :
    ∃ y ∈ differentIdeal (P'.restrict k F).integers
        (integralClosure (P'.restrict k F).integers F'),
      y ≠ 0 ∧ P'.ord (algebraMap _ F' y) = differentExponent k F P' := by
  have hnot : ¬ (centerIntegralClosure k F P').asIdeal ^ (differentExponent k F P' + 1) ∣
      differentIdeal (P'.restrict k F).integers (integralClosure (P'.restrict k F).integers F') :=
    fun h ↦ by simpa using (pow_dvd_differentIdeal_iff_le_differentExponent k F P').mp h
  obtain ⟨y, hy, hyP⟩ := SetLike.not_le_iff_exists.mp (mt Ideal.dvd_iff_le.mpr hnot)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hyP (zero_mem _)
  refine ⟨y, hy, hy0, le_antisymm ?_ (differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0)⟩
  rw [P'.ord_algebraMap_eq_multiplicity_center
    (algebraMap_mem_integers_of_mem_integralClosure k F P') hy0, ← centerIntegralClosure_def,
    Nat.cast_le]
  by_contra hlt
  exact hyP ((Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp
    ((finiteMultiplicity_span k F P' hy0).pow_dvd_iff_le_multiplicity.mpr (by omega))))

/-- **An element of the complementary module has order at least `-d(P' ∣ P)` at `P'`**: it
multiplies an element of the different ideal of order exactly `d(P' ∣ P)` into `𝒪'_P`, whose
functions are regular at `P'`. -/
theorem valuation_le_exp_differentExponent_of_mem_traceDual {z : F'}
    (hz : z ∈ Submodule.traceDual (P'.restrict k F).integers F
      (1 : Submodule (integralClosure (P'.restrict k F).integers F') F')) :
    P'.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
  obtain ⟨b, hb⟩ :=
    Submodule.mem_one.mp (mem_traceDual_one_iff_forall_mem_differentIdeal.mp hz y hy)
  have hle : P'.valuation (z * algebraMap _ F' y) ≤ 1 :=
    hb ▸ P'.mem_integers_iff.mp (algebraMap_mem_integers_of_mem_integralClosure k F P' b)
  have hy0' : algebraMap (integralClosure (P'.restrict k F).integers F') F' y ≠ 0 := by
    simpa using hy0
  rw [map_mul, P'.valuation_eq_exp_neg_ord hy0', hord] at hle
  calc P'.valuation z
      = P'.valuation z * WithZero.exp (-(differentExponent k F P' : ℤ)) *
          WithZero.exp (differentExponent k F P' : ℤ) := by
        rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
    _ ≤ 1 * WithZero.exp (differentExponent k F P' : ℤ) := by gcongr
    _ = WithZero.exp (differentExponent k F P' : ℤ) := one_mul _

end OnePlace

variable [Algebra.IsIntegral k k']

/-- **The valuation criterion for the complementary module** (Stichtenoth, Proposition 3.4.2 and
Definition 3.4.3): an element `z` of `F'` satisfies `Tr_{F'/F} (z · 𝒪'_P) ⊆ 𝒪_P` exactly when
`v_{P'}(z) ≤ exp d(P' ∣ P)`, that is `ord_{P'} z ≥ -d(P' ∣ P)` for `z ≠ 0`, at every place `P'` of
`F' / k'` lying over `P`. -/
theorem mem_traceDual_iff_forall_valuation_le (hF' : IsFunctionField k' F') (P : Place k F)
    {z : F'} :
    z ∈ Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers F') F') ↔
      ∀ P' : Place k' F', P'.restrict k F = P →
        P'.valuation z ≤ WithZero.exp (differentExponent k F P' : ℤ) := by
  refine ⟨fun hz P' hP' ↦ ?_, fun h ↦ ?_⟩
  · subst hP'
    exact valuation_le_exp_differentExponent_of_mem_traceDual k F P' hz
  refine mem_traceDual_one_iff_forall_mem_differentIdeal.mpr fun y hy ↦
    Submodule.mem_one.mpr ⟨⟨z * algebraMap (integralClosure P.integers F') F' y, ?_⟩, rfl⟩
  refine (isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mpr fun P' hP' ↦ ?_
  subst hP'
  rw [mem_integers_iff, map_mul]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  have hy0' : algebraMap (integralClosure (P'.restrict k F).integers F') F' y ≠ 0 := by
    simpa using hy0
  have hord := differentExponent_le_ord_of_mem_differentIdeal k F P' hy hy0
  rw [P'.valuation_eq_exp_neg_ord hy0']
  calc P'.valuation z * WithZero.exp (-P'.ord (algebraMap _ F' y))
      ≤ WithZero.exp (differentExponent k F P' : ℤ) *
          WithZero.exp (-(differentExponent k F P' : ℤ)) := by
        gcongr
        · exact h P' rfl
        · exact WithZero.exp_le_exp.mpr (neg_le_neg hord)
    _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

/-- **The trace estimate at a place**: if `z ∈ F'` has order at least
`-(e(P' ∣ P) · n + d(P' ∣ P))` at every place `P'` of `F' / k'` over `P`, then its trace to `F` has
order at least `-n` at `P`.  Multiplying `z` by a function of order `n` at `P` moves it into the
complementary module `C_P`, whose traces are regular at `P`. -/
theorem valuation_trace_le_exp (hF' : IsFunctionField k' F') (P : Place k F) (n : ℤ) {z : F'}
    (hz : ∀ P' : Place k' F', P'.restrict k F = P → P'.valuation z ≤
      WithZero.exp (ramificationIdx F P' * n + differentExponent k F P')) :
    P.valuation (Algebra.trace F F' z) ≤ WithZero.exp n := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have ht0 : t ≠ 0 := ht.ne_zero
  have hs0 : t ^ n ≠ 0 := zpow_ne_zero n ht0
  have hords : P.ord (t ^ n) = n := by
    rw [ord_zpow, P.isUniformizer_iff_ord_eq_one.mp ht, mul_one]
  -- `t ^ n • z` lies in the complementary module
  have hmem : algebraMap F F' (t ^ n) * z ∈ Submodule.traceDual P.integers F
      (1 : Submodule (integralClosure P.integers F') F') := by
    refine (mem_traceDual_iff_forall_valuation_le k F hF' P).mpr fun P' hP' ↦ ?_
    have hs0' : algebraMap F F' (t ^ n) ≠ 0 := (map_ne_zero _).mpr hs0
    rw [map_mul, P'.valuation_eq_exp_neg_ord hs0', ord_algebraMap_restrict k F P', hP', hords]
    calc WithZero.exp (-(ramificationIdx F P' * n)) * P'.valuation z
        ≤ WithZero.exp (-(ramificationIdx F P' * n)) *
            WithZero.exp (ramificationIdx F P' * n + differentExponent k F P') := by
          gcongr
          exact hz P' hP'
      _ = WithZero.exp (differentExponent k F P' : ℤ) := by
          rw [← WithZero.exp_add, neg_add_cancel_left]
  -- so its trace is regular at `P`
  obtain ⟨a, ha⟩ := (Submodule.mem_traceDual.mp hmem) 1 (Submodule.one_le.mp le_rfl)
  have htr : P.valuation (t ^ n * Algebra.trace F F' z) ≤ 1 := by
    have h1 : t ^ n * Algebra.trace F F' z = algebraMap P.integers F a := by
      rw [ha, Algebra.traceForm_apply, mul_one, ← Algebra.smul_def, LinearMap.map_smul,
        smul_eq_mul]
    rw [h1]
    exact P.mem_integers_iff.mp a.2
  rw [map_mul, P.valuation_eq_exp_neg_ord hs0, hords] at htr
  calc P.valuation (Algebra.trace F F' z)
      = WithZero.exp n * (WithZero.exp (-n) * P.valuation (Algebra.trace F F' z)) := by
        rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
    _ ≤ WithZero.exp n * 1 := by gcongr
    _ = WithZero.exp n := mul_one _

/-- **The trace estimate is sharp** (Stichtenoth, proof of Theorem 3.4.6): relaxing the bound of
`TauCeti.Place.valuation_trace_le_exp` by one at a single place `P'` over `P` relaxes the bound on
the traces by one.  Every `x ∈ F` with `ord_P x ≥ -(n + 1)` is the trace of some `z ∈ F'` with
`ord_{Q'} z ≥ -(e(Q' ∣ P) · n + d(Q' ∣ P))` at the places `Q' ≠ P'` over `P` and
`ord_{P'} z ≥ -(e(P' ∣ P) · n + d(P' ∣ P) + 1)`. -/
theorem exists_forall_valuation_le_and_trace_eq (hF' : IsFunctionField k' F')
    (P' : Place k' F') (n : ℤ) {x : F}
    (hx : (P'.restrict k F).valuation x ≤ WithZero.exp (n + 1)) :
    ∃ z : F', (∀ Q' : Place k' F', Q'.restrict k F = P'.restrict k F → Q' ≠ P' →
        Q'.valuation z ≤ WithZero.exp (ramificationIdx F Q' * n + differentExponent k F Q')) ∧
      P'.valuation z ≤ WithZero.exp (ramificationIdx F P' * n + differentExponent k F P' + 1) ∧
      Algebra.trace F F' z = x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, fun _ _ _ ↦ by simp, by simp, by simp⟩
  set P := P'.restrict k F with hP
  -- By the valuation criterion for `C_P`, a function `z₀` of `F'` with order exactly
  -- `-(d(P' ∣ P) + 1)` at `P'` and at least `-d(Q' ∣ P)` at the other places over `P` lies outside
  -- `C_P`; then some `z₀ * b` with `b ∈ 𝒪'_P` has a trace `y ∉ 𝒪_P`, and `(x / y) * z₀ * b` works.
  obtain ⟨z₀, hz₀0, hz₀⟩ := exists_ne_zero_forall_mem_ord_eq
    (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset
    fun Q' ↦ -((differentExponent k F Q' : ℤ) + if Q' = P' then 1 else 0)
  have hval (Q' : Place k' F') (hQ' : Q'.restrict k F = P) :
      Q'.valuation z₀ =
        WithZero.exp ((differentExponent k F Q' : ℤ) + if Q' = P' then 1 else 0) := by
    rw [Q'.valuation_eq_exp_neg_ord hz₀0, hz₀ Q' (by simpa using hQ'), neg_neg]
  have hnot : z₀ ∉ Submodule.traceDual P.integers F
      (1 : Submodule (integralClosure P.integers F') F') := by
    rw [mem_traceDual_iff_forall_valuation_le k F hF' P]
    intro h
    have h' := h P' rfl
    rw [hval P' rfl] at h'
    simp only [↓reduceIte, WithZero.exp_le_exp] at h'
    omega
  -- so some multiple of it by an element `a` of `𝒪'_P` has a trace `y` outside `𝒪_P`
  obtain ⟨a, ha, hy⟩ : ∃ a ∈ (1 : Submodule (integralClosure P.integers F') F'),
      Algebra.trace F F' (z₀ * a) ∉ (algebraMap P.integers F).range := by
    simpa [Submodule.mem_traceDual, Algebra.traceForm_apply] using hnot
  obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
  set y := Algebra.trace F F' (z₀ * algebraMap _ F' b) with hydef
  have hy1 : 1 < P.valuation y := by
    refine lt_of_not_ge fun h ↦ hy ⟨⟨y, P.mem_integers_iff.mpr h⟩, rfl⟩
  have hy0 : y ≠ 0 := by
    rintro h
    simp [h] at hy1
  have hordy : P.ord y < 0 := by
    rw [P.valuation_eq_exp_neg_ord hy0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hy1
    omega
  have hordx : -(n + 1) ≤ P.ord x := by
    rw [P.valuation_eq_exp_neg_ord hx0, WithZero.exp_le_exp] at hx
    omega
  -- the multiplier `x / y` has order at least `-n` at `P`
  have hc0 : x / y ≠ 0 := div_ne_zero hx0 hy0
  have hc : ∀ Q' : Place k' F', Q'.restrict k F = P →
      Q'.valuation (algebraMap F F' (x / y)) ≤ WithZero.exp (ramificationIdx F Q' * n) := by
    intro Q' hQ'
    rw [Q'.valuation_eq_exp_neg_ord ((map_ne_zero _).mpr hc0), ord_algebraMap_restrict k F Q', hQ',
      P.ord_div hx0 hy0, WithZero.exp_le_exp]
    have he : (0 : ℤ) ≤ ramificationIdx F Q' := by positivity
    nlinarith
  have hb (Q' : Place k' F') (hQ' : Q'.restrict k F = P) :
      Q'.valuation (algebraMap (integralClosure P.integers F') F' b) ≤ 1 :=
    Q'.mem_integers_iff.mp
      ((isIntegral_iff_forall_restrict_eq_mem_integers hF' P).mp b.2 Q' hQ')
  have hbound (Q' : Place k' F') (hQ' : Q'.restrict k F = P) :
      Q'.valuation (algebraMap F F' (x / y) * (z₀ * algebraMap _ F' b)) ≤
        WithZero.exp (ramificationIdx F Q' * n + differentExponent k F Q' +
          if Q' = P' then 1 else 0) := by
    calc Q'.valuation (algebraMap F F' (x / y) * (z₀ * algebraMap _ F' b))
        = Q'.valuation (algebraMap F F' (x / y)) * Q'.valuation z₀ *
            Q'.valuation (algebraMap _ F' b) := by rw [map_mul, map_mul, mul_assoc]
      _ ≤ WithZero.exp (ramificationIdx F Q' * n) * Q'.valuation z₀ * 1 := by
          gcongr
          · exact hc Q' hQ'
          · exact hb Q' hQ'
      _ = _ := by rw [mul_one, hval Q' hQ', ← WithZero.exp_add, add_assoc]
  refine ⟨algebraMap F F' (x / y) * (z₀ * algebraMap _ F' b), fun Q' hQ' hne ↦ ?_, ?_, ?_⟩
  · simpa [hne] using hbound Q' hQ'
  · simpa using hbound P' rfl
  · rw [← Algebra.smul_def, LinearMap.map_smul, ← hydef, smul_eq_mul, div_mul_cancel₀ x hy0]

end Place

end TauCeti

end
