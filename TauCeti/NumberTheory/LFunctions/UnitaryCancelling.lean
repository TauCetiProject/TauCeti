/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing

/-!
# Intrinsic nonvanishing packages for unitary ideal weights

To prove zero-freeness of an `L`-function on the boundary line `Re s = 1` via the `3-4-1`
inequality, one needs partial-sum cancellation (`TauCeti.HasCancellation`) along vertical shifts
together with control of the companion series `L(χ ^ 2, ·)` at `1 + 2 i t`, while avoiding two
pitfalls:

* requiring `χ ^ 2` always to cancel excludes quadratic characters such as `χ₄`, whose square is
  trivial away from its bad primes and therefore has a pole at `s = 1`;
* requiring every member of a character group to have cancelling twists makes the package
  uninhabitable, since the trivial member's L-series is a Dedekind zeta function with finitely many
  Euler factors deleted (whose identity law holds only on good ideals, not at bad primes).

This file introduces the real-parametrized boundary twist and the two corresponding hypothesis
packages on `TauCeti.UnitaryIdealWeight K`:

* `TauCeti.LFunctions.imaginaryNormTwist`: the boundary twist `I ↦ χ(I) N(I) ^ (t * I)`.
* `TauCeti.LFunctions.UnitaryCancelling`: single-weight package for a possibly infinite-order
  unitary weight `χ`, excluding pure norm twists on the good ideals and allowing the square of each
  imaginary twist either to be a norm twist on its good ideals or to cancel.
  `TauCeti.LFunctions.UnitaryCancelling.continuedLFunctionOfWeight_ne_zero` proves nonvanishing on
  `Re s ≥ 1` away from boundary points `Re s = 1` where
  `(χ ^ 2).val.IsNormTwistOnGood (2 * s.im)`.
* `TauCeti.LFunctions.IsUnitaryCharacterFamily`: family package for a group-indexed family
  `w : G → UnitaryIdealWeight K` whose identity member is trivial on its good ideals, which is
  multiplicative and conjugation-compatible, and whose nontrivial members have cancelling imaginary
  norm twists. Every nontrivial member satisfies `UnitaryCancelling`
  (`TauCeti.LFunctions.IsUnitaryCharacterFamily.unitaryCancelling`), and
  `TauCeti.LFunctions.IsUnitaryCharacterFamily.continuedLFunctionOfWeight_ne_zero` proves
  nonvanishing on `Re s ≥ 1` away from `s = 1` when `g ^ 2 = 1`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The square-twist case split follows Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`
  (Michael Stoll and David Loeffler) via
  `TauCeti/NumberTheory/ArithmeticDirichletSeries/Cancellation/Nonvanishing.lean`.
-/

public section
noncomputable section

open Complex IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.LFunctions

section ImaginaryNormTwist

variable {K : Type*} [Field K] [NumberField K]

/-- **The purely imaginary norm twist** `I ↦ χ(I) N(I) ^ (t * I)` of a unitary ideal weight,
realized as `TauCeti.UnitaryIdealWeight.normTwist (-((t : ℂ) * Complex.I))` since `normTwist z`
multiplies by `N(I) ^ (-z)`. -/
def imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ) : UnitaryIdealWeight K :=
  UnitaryIdealWeight.normTwist (-((t : ℂ) * Complex.I)) (by simp) χ

/-- Defining equation of `TauCeti.LFunctions.imaginaryNormTwist`. -/
theorem imaginaryNormTwist_def (χ : UnitaryIdealWeight K) (t : ℝ) :
    imaginaryNormTwist χ t =
      UnitaryIdealWeight.normTwist (-((t : ℂ) * Complex.I)) (by simp) χ := (rfl)

/-- Underlying `MultiplicativeIdealWeight` of `imaginaryNormTwist χ t`. -/
-- Not `@[simp]`: rewriting `(imaginaryNormTwist χ t).val` to
-- `MultiplicativeIdealWeight.normTwist` would take `imaginaryNormTwist_apply`,
-- `badPrimes_imaginaryNormTwist`, and `isNormTwistOnGood_imaginaryNormTwist_iff` out of simp
-- normal form (`simpNF`).
theorem val_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ) :
    (imaginaryNormTwist χ t).val =
      MultiplicativeIdealWeight.normTwist (-((t : ℂ) * Complex.I)) χ.val := by
  rw [imaginaryNormTwist_def, UnitaryIdealWeight.val_normTwist]

@[simp]
theorem imaginaryNormTwist_apply (χ : UnitaryIdealWeight K) (t : ℝ) (I : Ideal (𝓞 K)) :
    (imaginaryNormTwist χ t).val I = χ.val I * (Ideal.absNorm I : ℂ) ^ ((t : ℂ) * Complex.I) := by
  simp [imaginaryNormTwist_def]

@[simp]
theorem badPrimes_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ) :
    (imaginaryNormTwist χ t).val.badPrimes = χ.val.badPrimes := by
  simp [imaginaryNormTwist_def]

@[simp]
theorem imaginaryNormTwist_zero (χ : UnitaryIdealWeight K) : imaginaryNormTwist χ 0 = χ := by
  simp [imaginaryNormTwist_def]

@[simp]
theorem imaginaryNormTwist_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t u : ℝ) :
    imaginaryNormTwist (imaginaryNormTwist χ t) u = imaginaryNormTwist χ (t + u) := by
  have hz : -((u : ℂ) * Complex.I) + -((t : ℂ) * Complex.I) =
      -(((t + u : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  simp only [imaginaryNormTwist_def, UnitaryIdealWeight.normTwist_normTwist, hz]

@[simp]
theorem imaginaryNormTwist_mul_imaginaryNormTwist (χ ψ : UnitaryIdealWeight K) (t u : ℝ) :
    imaginaryNormTwist χ t * imaginaryNormTwist ψ u = imaginaryNormTwist (χ * ψ) (t + u) := by
  have hz : -((t : ℂ) * Complex.I) + -((u : ℂ) * Complex.I) =
      -(((t + u : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  simp only [imaginaryNormTwist_def, UnitaryIdealWeight.normTwist_mul_normTwist, hz]

@[simp]
theorem imaginaryNormTwist_pow (χ : UnitaryIdealWeight K) (t : ℝ) (n : ℕ) :
    imaginaryNormTwist χ t ^ n = imaginaryNormTwist (χ ^ n) (n * t) := by
  have hz : (n : ℂ) * -((t : ℂ) * Complex.I) = -((((n : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  simp only [imaginaryNormTwist_def, UnitaryIdealWeight.normTwist_pow, hz]

@[simp]
theorem conj_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ) :
    (imaginaryNormTwist χ t).conj = imaginaryNormTwist χ.conj (-t) := by
  apply Subtype.ext
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · have hN : 0 < Ideal.absNorm I :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hnorm : ‖((Ideal.absNorm I : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hN]
      simp
    rw [UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply,
      imaginaryNormTwist_apply, imaginaryNormTwist_apply, UnitaryIdealWeight.val_conj,
      MultiplicativeIdealWeight.conj_apply, map_mul, ← Complex.inv_eq_conj hnorm,
      ← Complex.cpow_neg]
    congr 2
    push_cast
    ring

/-- Restriction of a unitary weight away from `S` commutes with `imaginaryNormTwist`. -/
@[simp]
theorem restrictAway_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    (imaginaryNormTwist χ t).restrictAway S hS = imaginaryNormTwist (χ.restrictAway S hS) t := by
  simp [imaginaryNormTwist_def]

/-- Regrouping by norm absorbs `imaginaryNormTwist`: the `n`-th norm coefficient is multiplied by
`n ^ (t * I)`. -/
@[simp]
theorem normCoeff_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ) (n : ℕ) :
    normCoeff K (imaginaryNormTwist χ t).toIdealArithmeticFunction n =
      normCoeff K χ.toIdealArithmeticFunction n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  simp [imaginaryNormTwist_def]

/-- Twisting `χ` by `N(I) ^ (t * I)` shifts a norm-twist parameter on the good ideals by `t`. -/
@[simp]
theorem isNormTwistOnGood_imaginaryNormTwist_iff {χ : UnitaryIdealWeight K} {t u : ℝ} :
    (imaginaryNormTwist χ t).val.IsNormTwistOnGood u ↔ χ.val.IsNormTwistOnGood (u - t) := by
  constructor
  · intro h
    have h' := h.normTwist (-t)
    rw [← val_imaginaryNormTwist, imaginaryNormTwist_imaginaryNormTwist, add_neg_cancel,
      imaginaryNormTwist_zero, ← sub_eq_add_neg] at h'
    exact h'
  · intro h
    simpa [val_imaginaryNormTwist, sub_add_cancel] using h.normTwist t

/-- Twisting `χ` by `N(I) ^ (t * I)` translates its continued L-function from `s` to `s - t * I` on
`Re s > 1`. -/
@[simp]
theorem continuedLFunctionOfWeight_imaginaryNormTwist_of_one_lt_re (χ : UnitaryIdealWeight K)
    (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    continuedLFunctionOfWeight (imaginaryNormTwist χ t) s =
      continuedLFunctionOfWeight χ (s - (t : ℂ) * Complex.I) := by
  rw [imaginaryNormTwist_def, continuedLFunctionOfWeight_normTwist_of_one_lt_re χ (by simp) hs,
    sub_eq_add_neg]

/-- When both `χ` and `imaginaryNormTwist χ t` have cancellation, twisting translates the continued
L-function across `Re s = 1` throughout `Re s > 1 - 1 / [K : ℚ]`. -/
theorem continuedLFunctionOfWeight_imaginaryNormTwist {χ : UnitaryIdealWeight K} (t : ℝ)
    (hχ : HasCancellation χ) (hχt : HasCancellation (imaginaryNormTwist χ t)) {s : ℂ}
    (hs : 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re) :
    continuedLFunctionOfWeight (imaginaryNormTwist χ t) s =
      continuedLFunctionOfWeight χ (s - (t : ℂ) * Complex.I) := by
  rw [imaginaryNormTwist_def, continuedLFunctionOfWeight_normTwist (by simp) hχ hχt hs,
    sub_eq_add_neg]

/-- No imaginary norm twist of the trivial unitary weight has cancellation. -/
theorem not_hasCancellation_imaginaryNormTwist_one (t : ℝ) :
    ¬ HasCancellation (imaginaryNormTwist (1 : UnitaryIdealWeight K) t) := by
  rw [imaginaryNormTwist_def]
  exact not_hasCancellation_normTwist_one (by simp)

end ImaginaryNormTwist

section UnitaryCancelling

variable {K : Type*} [Field K] [NumberField K]

/-- **Single-character cancellation package** for a possibly infinite-order unitary ideal weight.
It excludes weights that are pure imaginary norm twists on their good ideals, requires cancellation
for `χ`, its conjugate, and all its imaginary norm twists, and requires the pointwise square of
every imaginary norm twist either to be a norm twist on its good ideals (covering quadratic
characters and their twists) or to have cancellation. -/
structure UnitaryCancelling (χ : UnitaryIdealWeight K) : Prop where
  /-- `χ` is not a pure imaginary norm twist `N(I) ^ (u * I)` on its good ideals. -/
  not_normTwist : ∀ u : ℝ, ¬ χ.val.IsNormTwistOnGood u
  /-- `χ` has ideal partial-sum cancellation. -/
  cancellation : HasCancellation χ
  /-- The conjugate weight `χ.conj` has ideal partial-sum cancellation. -/
  cancellation_conj : HasCancellation χ.conj
  /-- Every imaginary norm twist `χ * N ^ (t * I)` has cancellation. -/
  cancellation_normTwist : ∀ t : ℝ, HasCancellation (imaginaryNormTwist χ t)
  /-- For every `t`, the square of `imaginaryNormTwist χ t` is either a norm twist on its good
  ideals or itself has cancellation. -/
  square_twist : ∀ t : ℝ,
    (∃ u : ℝ, (imaginaryNormTwist χ t ^ 2).val.IsNormTwistOnGood u) ∨
      HasCancellation (imaginaryNormTwist χ t ^ 2)

/-- Smart constructor for `UnitaryCancelling`: `cancellation`, `cancellation_conj`, and
`not_normTwist` all follow from `cancellation_normTwist` at `t = 0`. -/
theorem UnitaryCancelling.of_cancellation_normTwist {χ : UnitaryIdealWeight K}
    (hcanc : ∀ t : ℝ, HasCancellation (imaginaryNormTwist χ t))
    (hsq : ∀ t : ℝ,
      (∃ u : ℝ, (imaginaryNormTwist χ t ^ 2).val.IsNormTwistOnGood u) ∨
        HasCancellation (imaginaryNormTwist χ t ^ 2)) :
    UnitaryCancelling χ := by
  have h0 : HasCancellation χ := by simpa using hcanc 0
  exact ⟨fun u hu ↦ not_hasCancellation_of_isNormTwistOnGood hu h0, h0,
    hasCancellation_conj_iff.mpr h0, hcanc, hsq⟩

/-- `UnitaryCancelling` is closed under imaginary norm twists. -/
theorem UnitaryCancelling.imaginaryNormTwist {χ : UnitaryIdealWeight K} (hχ : UnitaryCancelling χ)
    (t : ℝ) : UnitaryCancelling (LFunctions.imaginaryNormTwist χ t) := by
  refine UnitaryCancelling.of_cancellation_normTwist
    (fun u ↦ by simpa [imaginaryNormTwist_imaginaryNormTwist] using
      hχ.cancellation_normTwist (t + u))
    (fun u ↦ by simpa [imaginaryNormTwist_imaginaryNormTwist] using hχ.square_twist (t + u))

@[simp]
theorem unitaryCancelling_imaginaryNormTwist_iff {χ : UnitaryIdealWeight K} (t : ℝ) :
    UnitaryCancelling (imaginaryNormTwist χ t) ↔ UnitaryCancelling χ :=
  ⟨fun h ↦ by simpa using h.imaginaryNormTwist (-t), fun h ↦ h.imaginaryNormTwist t⟩

/-- `UnitaryCancelling` is closed under complex conjugation. -/
theorem UnitaryCancelling.conj {χ : UnitaryIdealWeight K} (hχ : UnitaryCancelling χ) :
    UnitaryCancelling χ.conj := by
  refine UnitaryCancelling.of_cancellation_normTwist
    (fun t ↦ by
      rw [← neg_neg t, ← conj_imaginaryNormTwist, hasCancellation_conj_iff]
      exact hχ.cancellation_normTwist (-t))
    (fun t ↦ ?_)
  have hconj : (LFunctions.imaginaryNormTwist χ (-t) ^ 2).conj =
      LFunctions.imaginaryNormTwist χ.conj t ^ 2 := by
    rw [← UnitaryIdealWeight.star_eq_conj, star_pow, UnitaryIdealWeight.star_eq_conj,
      conj_imaginaryNormTwist, neg_neg]
  rcases hχ.square_twist (-t) with ⟨u, hu⟩ | hcanc
  · refine Or.inl ⟨-u, ?_⟩
    rw [← hconj, UnitaryIdealWeight.val_conj]
    exact hu.conj
  · refine Or.inr ?_
    rw [← hconj, hasCancellation_conj_iff]
    exact hcanc

@[simp]
theorem unitaryCancelling_conj_iff {χ : UnitaryIdealWeight K} :
    UnitaryCancelling χ.conj ↔ UnitaryCancelling χ :=
  ⟨fun h ↦ by simpa using h.conj, UnitaryCancelling.conj⟩

/-- `UnitaryCancelling` survives restriction away from a finite set of height-one primes. -/
theorem UnitaryCancelling.restrictAway {χ : UnitaryIdealWeight K} (hχ : UnitaryCancelling χ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    UnitaryCancelling (χ.restrictAway S hS) := by
  refine UnitaryCancelling.of_cancellation_normTwist
    (fun t ↦ by
      rw [← restrictAway_imaginaryNormTwist]
      exact (hχ.cancellation_normTwist t).restrictAway S hS)
    (fun t ↦ ?_)
  rw [← restrictAway_imaginaryNormTwist, ← UnitaryIdealWeight.restrictAway_pow _ hS two_ne_zero]
  rcases hχ.square_twist t with ⟨u, hu⟩ | hcanc
  · refine Or.inl ⟨u, ?_⟩
    rw [UnitaryIdealWeight.val_restrictAway]
    exact hu.restrictAway hS
  · exact Or.inr (hcanc.restrictAway S hS)

/-- A weight that is a pure norm twist on its good ideals never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_of_isNormTwistOnGood {χ : UnitaryIdealWeight K} {u : ℝ}
    (hχ : χ.val.IsNormTwistOnGood u) : ¬ UnitaryCancelling χ :=
  fun h ↦ h.not_normTwist u hχ

/-- A weight trivial on its good ideals never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_of_isTrivialOnGood {χ : UnitaryIdealWeight K}
    (hχ : χ.val.IsTrivialOnGood) : ¬ UnitaryCancelling χ :=
  not_unitaryCancelling_of_isNormTwistOnGood
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr hχ)

/-- The trivial unitary weight does not satisfy `UnitaryCancelling`. -/
theorem not_unitaryCancelling_one : ¬ UnitaryCancelling (1 : UnitaryIdealWeight K) :=
  fun h ↦ not_hasCancellation_one h.cancellation

/-- No imaginary norm twist `N ^ (t * I)` of the trivial weight satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_imaginaryNormTwist_one (t : ℝ) :
    ¬ UnitaryCancelling (imaginaryNormTwist (1 : UnitaryIdealWeight K) t) :=
  fun h ↦ not_hasCancellation_imaginaryNormTwist_one t h.cancellation

/-- **Boundary nonvanishing from `UnitaryCancelling`.** For `Re s ≥ 1`, `continuedLFunctionOfWeight`
of a `UnitaryCancelling` weight `χ` does not vanish at `s`, except possibly on `Re s = 1` when
`χ ^ 2` is the norm twist `N(I) ^ ((2 * Im s) * I)` on its good ideals (where the companion series
`L(χ ^ 2, ·)` has a pole at `2 s - 1 = 1 + 2 i Im s`). -/
theorem UnitaryCancelling.continuedLFunctionOfWeight_ne_zero {χ : UnitaryIdealWeight K}
    (hχ : UnitaryCancelling χ) {s : ℂ} (hs : 1 ≤ s.re)
    (hsq : s.re = 1 → ¬ (χ ^ 2).val.IsNormTwistOnGood (2 * s.im)) :
    continuedLFunctionOfWeight χ s ≠ 0 := by
  rcases hs.lt_or_eq with hs_lt | hs_eq
  · exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re χ hs_lt
  · have h0 := hχ.square_twist 0
    rw [imaginaryNormTwist_zero] at h0
    rcases h0 with ⟨u, hu⟩ | hcanc2
    · refine continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq hχ.cancellation hu hs
        fun hsu ↦ ?_
      have hu_eq : u = 2 * s.im := by
        have him := congrArg Complex.im hsu
        simp at him
        linarith
      exact hsq hs_eq.symm (hu_eq ▸ hu)
    · exact continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq hχ.cancellation hcanc2 hs

/-- If `χ` satisfies `UnitaryCancelling` and `χ ^ 2` is not a norm twist on its good ideals, then
`continuedLFunctionOfWeight χ` has no zeros anywhere on `Re s ≥ 1`. -/
theorem UnitaryCancelling.continuedLFunctionOfWeight_ne_zero_of_not_isNormTwistOnGood_sq
    {χ : UnitaryIdealWeight K} (hχ : UnitaryCancelling χ)
    (hsq : ∀ u : ℝ, ¬ (χ ^ 2).val.IsNormTwistOnGood u) {s : ℂ} (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ s ≠ 0 :=
  hχ.continuedLFunctionOfWeight_ne_zero hs fun _ ↦ hsq (2 * s.im)

/-- If `χ` satisfies `UnitaryCancelling` and `χ ^ 2` is trivial on its good ideals (the quadratic
case), then `continuedLFunctionOfWeight χ` has no zeros on `Re s ≥ 1` away from `s = 1`. -/
theorem UnitaryCancelling.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq
    {χ : UnitaryIdealWeight K} (hχ : UnitaryCancelling χ) (hsq : (χ ^ 2).val.IsTrivialOnGood)
    {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    continuedLFunctionOfWeight χ s ≠ 0 :=
  TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq hχ.cancellation hsq hs hs1

end UnitaryCancelling

section CharacterFamily

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [Group G]

/-- **Character-family cancellation package** for a group-indexed family
`w : G → UnitaryIdealWeight K`. The identity member `w 1` takes the value `1` on its good ideals
(where goodness includes `I ≠ ⊥`, while `w 1` may still vanish at bad primes), the family preserves
products and sends inverses to conjugates, and every imaginary norm twist of every **nontrivial**
member has cancellation. -/
structure IsUnitaryCharacterFamily (w : G → UnitaryIdealWeight K) : Prop where
  /-- The identity member `w 1` equals `1` on every good ideal (and vanishes off them). -/
  isTrivialOnGood_one : (w 1).val.IsTrivialOnGood
  /-- Pointwise multiplication of weights represents group multiplication. -/
  map_mul : ∀ g h : G, w (g * h) = w g * w h
  /-- Complex conjugation of weights represents group inversion. -/
  conj_eq_map_inv : ∀ g : G, (w g).conj = w g⁻¹
  /-- Every imaginary norm twist of every nontrivial member has cancellation. -/
  cancellation_normTwist : ∀ {g : G}, g ≠ 1 → ∀ t : ℝ, HasCancellation (imaginaryNormTwist (w g) t)

namespace IsUnitaryCharacterFamily

/-- The identity member `w 1` of a unitary character family takes the value `1` on every good
ideal. -/
theorem one_apply_eq_one_of_isGood {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w)
    {I : Ideal (𝓞 K)} (hI : (w 1).val.IsGood I) : (w 1).val I = 1 :=
  hw.isTrivialOnGood_one.apply_eq_one hI

private theorem badPrimes_eq_of_mul {w : G → UnitaryIdealWeight K}
    (hmul : ∀ g h : G, w (g * h) = w g * w h) (g : G) :
    (w g).val.badPrimes = (w 1).val.badPrimes := by
  apply Set.Subset.antisymm
  · have h1 : (w 1).val.badPrimes = (w g).val.badPrimes ∪ (w g⁻¹).val.badPrimes := by
      rw [← MultiplicativeIdealWeight.badPrimes_mul, ← UnitaryIdealWeight.val_mul, ← hmul,
        mul_inv_cancel]
    exact h1 ▸ Set.subset_union_left
  · have hg : (w g).val.badPrimes = (w g).val.badPrimes ∪ (w 1).val.badPrimes := by
      rw [← MultiplicativeIdealWeight.badPrimes_mul, ← UnitaryIdealWeight.val_mul, ← hmul,
        mul_one]
    exact hg ▸ Set.subset_union_right

/-- All members of a unitary character family share the same set of bad primes. -/
theorem badPrimes_eq {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w) (g : G) :
    (w g).val.badPrimes = (w 1).val.badPrimes :=
  badPrimes_eq_of_mul hw.map_mul g

/-- Smart constructor for `IsUnitaryCharacterFamily`: conjugation compatibility `(w g).conj = w g⁻¹`
follows automatically from unitarity, `isTrivialOnGood_one`, and `map_mul`. -/
theorem of_mul {w : G → UnitaryIdealWeight K} (hone : (w 1).val.IsTrivialOnGood)
    (hmul : ∀ g h : G, w (g * h) = w g * w h)
    (hcanc : ∀ {g : G}, g ≠ 1 → ∀ t : ℝ, HasCancellation (imaginaryNormTwist (w g) t)) :
    IsUnitaryCharacterFamily w := by
  refine ⟨hone, hmul,
    fun g ↦ Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun 𝔭 ↦ ?_), hcanc⟩
  have hbad_g := badPrimes_eq_of_mul hmul g
  have hbad_inv := badPrimes_eq_of_mul hmul g⁻¹
  by_cases h𝔭 : 𝔭 ∈ (w 1).val.badPrimes
  · have hg0 : (w g).val 𝔭.asIdeal = 0 :=
      MultiplicativeIdealWeight.mem_badPrimes.mp (hbad_g ▸ h𝔭)
    have hginv0 : (w g⁻¹).val 𝔭.asIdeal = 0 :=
      MultiplicativeIdealWeight.mem_badPrimes.mp (hbad_inv ▸ h𝔭)
    simp [hg0, hginv0]
  · have hgood1 : (w 1).val.IsGood 𝔭.asIdeal := Ideal.isPrimeTo_asIdeal_iff.mpr h𝔭
    have h𝔭g : 𝔭 ∉ (w g).val.badPrimes := hbad_g ▸ h𝔭
    have hprod : (w g).val 𝔭.asIdeal * (w g⁻¹).val 𝔭.asIdeal = 1 := by
      rw [← MultiplicativeIdealWeight.mul_apply, ← UnitaryIdealWeight.val_mul, ← hmul,
        mul_inv_cancel, hone.apply_eq_one hgood1]
    rw [UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply,
      ← Complex.inv_eq_conj ((w g).property 𝔭 h𝔭g), inv_eq_of_mul_eq_one_right hprod]

/-- Positive powers in `G` map to pointwise powers of unitary weights (excluding exponent `0`, where
`w 1` vanishes at bad primes while `(w g) ^ 0 = 1` does not). -/
theorem map_pow_of_ne_zero {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w)
    (g : G) {n : ℕ} (hn : n ≠ 0) : w (g ^ n) = w g ^ n := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | h0
    · simp
    · rw [pow_succ, pow_succ, hw.map_mul, ih h0]

/-- Squaring in `G` maps to the pointwise square of unitary weights. -/
theorem map_sq {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w) (g : G) :
    w (g ^ 2) = w g ^ 2 :=
  hw.map_pow_of_ne_zero g two_ne_zero

/-- Only the identity member of a unitary character family can be trivial on its good ideals. -/
theorem eq_one_of_isTrivialOnGood {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w)
    {g : G} (hg : (w g).val.IsTrivialOnGood) : g = 1 := by
  by_contra hne
  exact not_hasCancellation_of_isTrivialOnGood hg (by simpa using hw.cancellation_normTwist hne 0)

/-- A unitary character family is injective on `G`, hence forces `G` to be commutative. -/
theorem injective {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w) :
    Function.Injective w := by
  intro g h hgh
  refine mul_inv_eq_one.mp
    (hw.eq_one_of_isTrivialOnGood (MultiplicativeIdealWeight.isTrivialOnGood_iff.mpr fun I hI ↦ ?_))
  have hIh : (w h).val.IsGood I := by
    rwa [MultiplicativeIdealWeight.IsGood, hw.badPrimes_eq h, ← hw.badPrimes_eq (g * h⁻¹)]
  rw [hw.map_mul, ← hw.conj_eq_map_inv, hgh, UnitaryIdealWeight.val_mul,
    MultiplicativeIdealWeight.mul_apply, UnitaryIdealWeight.val_conj,
    MultiplicativeIdealWeight.conj_apply, Complex.mul_conj', (w h).norm_eq_one hIh,
    Complex.ofReal_one, one_pow]

/-- Any group indexing a unitary character family is commutative. -/
theorem mul_comm {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w) (g h : G) :
    g * h = h * g :=
  hw.injective (by rw [hw.map_mul, hw.map_mul, _root_.mul_comm])

/-- No imaginary norm twist of the identity member `w 1` has cancellation. -/
theorem not_hasCancellation_imaginaryNormTwist_one {w : G → UnitaryIdealWeight K}
    (hw : IsUnitaryCharacterFamily w) (t : ℝ) :
    ¬ HasCancellation (imaginaryNormTwist (w 1) t) := by
  refine not_hasCancellation_of_isNormTwistOnGood (u := t) ?_
  rw [isNormTwistOnGood_imaginaryNormTwist_iff, sub_self,
    MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff]
  exact hw.isTrivialOnGood_one

/-- In a unitary character family, an imaginary norm twist of `w g` has cancellation if and only if
`g ≠ 1`. -/
theorem hasCancellation_imaginaryNormTwist_iff {w : G → UnitaryIdealWeight K}
    (hw : IsUnitaryCharacterFamily w) {g : G} (t : ℝ) :
    HasCancellation (imaginaryNormTwist (w g) t) ↔ g ≠ 1 :=
  ⟨fun h ↦ by rintro rfl; exact hw.not_hasCancellation_imaginaryNormTwist_one t h,
    fun hg ↦ hw.cancellation_normTwist hg t⟩

/-- In a unitary character family, `w g` has cancellation if and only if `g ≠ 1`. -/
theorem hasCancellation_iff {w : G → UnitaryIdealWeight K}
    (hw : IsUnitaryCharacterFamily w) {g : G} :
    HasCancellation (w g) ↔ g ≠ 1 := by
  simpa using hw.hasCancellation_imaginaryNormTwist_iff (g := g) 0

/-- Every nontrivial member of a unitary character family satisfies `UnitaryCancelling`. -/
theorem unitaryCancelling {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w)
    {g : G} (hg : g ≠ 1) : UnitaryCancelling (w g) := by
  refine UnitaryCancelling.of_cancellation_normTwist (hw.cancellation_normTwist hg) fun t ↦ ?_
  rw [imaginaryNormTwist_pow, ← hw.map_sq]
  rcases eq_or_ne (g ^ 2) 1 with hg2 | hg2
  · refine Or.inl ⟨2 * t, ?_⟩
    have hzero : 2 * t - (2 : ℕ) * t = 0 := by norm_num
    rw [hg2, isNormTwistOnGood_imaginaryNormTwist_iff, hzero,
      MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff]
    exact hw.isTrivialOnGood_one
  · exact Or.inr (hw.cancellation_normTwist hg2 ((2 : ℕ) * t))

/-- The identity member `w 1` of a unitary character family never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_one {w : G → UnitaryIdealWeight K}
    (hw : IsUnitaryCharacterFamily w) : ¬ UnitaryCancelling (w 1) :=
  not_unitaryCancelling_of_isTrivialOnGood hw.isTrivialOnGood_one

/-- A member `w g` of a unitary character family satisfies `UnitaryCancelling` if and only if
`g ≠ 1`. -/
theorem unitaryCancelling_iff {w : G → UnitaryIdealWeight K}
    (hw : IsUnitaryCharacterFamily w) {g : G} :
    UnitaryCancelling (w g) ↔ g ≠ 1 :=
  ⟨fun h ↦ by rintro rfl; exact hw.not_unitaryCancelling_one h, hw.unitaryCancelling⟩

/-- **Boundary nonvanishing for a unitary character family.** For any nontrivial member `g ≠ 1` and
`Re s ≥ 1`, `continuedLFunctionOfWeight (w g) s ≠ 0` whenever `g ^ 2 ≠ 1` or `s ≠ 1`. -/
theorem continuedLFunctionOfWeight_ne_zero {w : G → UnitaryIdealWeight K}
    (hw : IsUnitaryCharacterFamily w) {g : G} (hg : g ≠ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (hquad : g ^ 2 ≠ 1 ∨ s ≠ 1) :
    continuedLFunctionOfWeight (w g) s ≠ 0 := by
  rcases eq_or_ne (g ^ 2) 1 with hg2 | hg2
  · have hs1 : s ≠ 1 := hquad.resolve_left (not_not.mpr hg2)
    have htriv : (w g ^ 2).val.IsTrivialOnGood := by
      rw [← hw.map_sq, hg2]
      exact hw.isTrivialOnGood_one
    exact (hw.unitaryCancelling hg).continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq
      htriv hs hs1
  · have hcanc2 : HasCancellation (w g ^ 2) := by
      rw [← hw.map_sq]
      simpa using hw.cancellation_normTwist hg2 0
    exact continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq
      (hw.unitaryCancelling hg).cancellation hcanc2 hs

end IsUnitaryCharacterFamily

end CharacterFamily

end TauCeti.LFunctions
