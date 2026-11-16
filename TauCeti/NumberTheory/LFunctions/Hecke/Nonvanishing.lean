/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.NumberField.Ideal.DegreeOne

/-!
# Intrinsic nonvanishing packages for unitary weights and ray class L-functions

To prove zero-freeness of an `L`-function on the boundary line `Re s = 1` via the `3-4-1`
inequality, one needs partial-sum cancellation (`TauCeti.HasCancellation`) along vertical shifts
together with control of the companion series `L(χ ^ 2, ·)` at `1 + 2 i t`, while avoiding two
pitfalls:

* requiring `χ ^ 2` always to cancel excludes quadratic characters such as `χ₄`, whose square is
  trivial away from its bad primes and therefore has a pole at `s = 1`;
* requiring every member of a finite character group to have cancelling twists makes the package
  uninhabitable, since the trivial member's L-series is a Dedekind zeta function with finitely many
  Euler factors deleted (whose identity law holds only on good ideals, not at bad primes).

This file introduces the two corresponding hypothesis packages and instantiates both for ray class
characters over an arbitrary number field `K`:

* `TauCeti.LFunctions.imaginaryNormTwist`: the real-parametrized boundary twist
  `I ↦ χ(I) N(I) ^ (t * I)`.
* `TauCeti.LFunctions.UnitaryCancelling`: single-character package for a possibly infinite-order
  unitary weight `χ`, excluding pure norm twists on the good ideals and allowing the square of each
  imaginary twist either to be a norm twist on its good ideals or to cancel.
* `TauCeti.LFunctions.IsUnitaryCharacterFamily`: family package for a group-indexed family
  `w : G → UnitaryIdealWeight K` whose identity member is trivial on its good ideals, which is
  multiplicative and conjugation-compatible, and whose nontrivial members have cancelling imaginary
  norm twists. Every nontrivial member of such a family satisfies `UnitaryCancelling`
  (`TauCeti.LFunctions.IsUnitaryCharacterFamily.unitaryCancelling`).
* `TauCeti.GlobalNumberFields.RayClassCharacter.isUnitaryCharacterFamily` and
  `TauCeti.GlobalNumberFields.RayClassCharacter.unitaryCancelling_toUnitaryIdealWeight_iff`:
  ray class characters of any modulus `𝔪` form a unitary character family, and
  `UnitaryCancelling χ.toUnitaryIdealWeight ↔ χ ≠ 1`.
* `TauCeti.LFunctions.UnitaryCancelling.continuedLFunctionOfWeight_ne_zero` and
  `TauCeti.GlobalNumberFields.RayClassCharacter.continuedLFunctionOfWeight_ne_zero`: nonvanishing
  on `Re s ≥ 1` away from the exceptional quadratic point (`χ ^ 2 = 1` at `s = 1`), together with
  holomorphic continuation across `Re s = 1`
  (`TauCeti.LFunctions.analyticOnNhd_heckeLFunctionC_of_eqOn`) and boundary nonvanishing
  (`TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_eqOn`) for `TauCeti.LFunctions.heckeLFunctionC`
  once whole-plane meromorphic continuation is supplied.
* `TauCeti.LFunctions.ratModFourChar`: the quadratic character modulo `(4)·∞` over `ℚ` induced by
  `ZMod.χ₄`, witnessing that `UnitaryCancelling` holds through the square-twist branch even though
  `ratModFourChar ^ 2 = 1` does not cancel, and that the trivial member of the mod-`4` family
  vanishes at `(2 : 𝓞 ℚ)`.

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

open GlobalNumberFields

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
-- Not `@[simp]`: rewriting `(imaginaryNormTwist χ t).1` to `MultiplicativeIdealWeight.normTwist`
-- would take `imaginaryNormTwist_apply`, `badPrimes_imaginaryNormTwist`, and
-- `isNormTwistOnGood_imaginaryNormTwist_iff` out of simp normal form (`simpNF`).
theorem val_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ) :
    (imaginaryNormTwist χ t).1 =
      MultiplicativeIdealWeight.normTwist (-((t : ℂ) * Complex.I)) χ.1 := by
  rw [imaginaryNormTwist_def, UnitaryIdealWeight.val_normTwist]

@[simp]
theorem imaginaryNormTwist_apply (χ : UnitaryIdealWeight K) (t : ℝ) (I : Ideal (𝓞 K)) :
    (imaginaryNormTwist χ t).1 I = χ.1 I * (Ideal.absNorm I : ℂ) ^ ((t : ℂ) * Complex.I) := by
  simp [imaginaryNormTwist_def]

@[simp]
theorem badPrimes_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t : ℝ) :
    (imaginaryNormTwist χ t).1.badPrimes = χ.1.badPrimes := by
  simp [imaginaryNormTwist_def]

@[simp]
theorem imaginaryNormTwist_zero (χ : UnitaryIdealWeight K) : imaginaryNormTwist χ 0 = χ := by
  simp [imaginaryNormTwist_def]

@[simp]
theorem imaginaryNormTwist_imaginaryNormTwist (χ : UnitaryIdealWeight K) (t u : ℝ) :
    imaginaryNormTwist (imaginaryNormTwist χ t) u = imaginaryNormTwist χ (t + u) := by
  apply Subtype.ext
  rw [val_imaginaryNormTwist, val_imaginaryNormTwist, val_imaginaryNormTwist,
    MultiplicativeIdealWeight.normTwist_normTwist]
  congr 1
  push_cast
  ring

@[simp]
theorem imaginaryNormTwist_mul (χ ψ : UnitaryIdealWeight K) (t u : ℝ) :
    imaginaryNormTwist χ t * imaginaryNormTwist ψ u = imaginaryNormTwist (χ * ψ) (t + u) := by
  apply Subtype.ext
  rw [UnitaryIdealWeight.val_mul, val_imaginaryNormTwist, val_imaginaryNormTwist,
    val_imaginaryNormTwist, UnitaryIdealWeight.val_mul,
    MultiplicativeIdealWeight.normTwist_mul_normTwist]
  congr 1
  push_cast
  ring

@[simp]
theorem imaginaryNormTwist_pow (χ : UnitaryIdealWeight K) (t : ℝ) (n : ℕ) :
    imaginaryNormTwist χ t ^ n = imaginaryNormTwist (χ ^ n) (n * t) := by
  apply Subtype.ext
  rw [UnitaryIdealWeight.val_pow, val_imaginaryNormTwist, val_imaginaryNormTwist,
    UnitaryIdealWeight.val_pow, MultiplicativeIdealWeight.normTwist_pow]
  congr 1
  push_cast
  ring

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

/-- Twisting `χ` by `N(I) ^ (t * I)` shifts a norm-twist parameter on the good ideals by `t`. -/
@[simp]
theorem isNormTwistOnGood_imaginaryNormTwist_iff {χ : UnitaryIdealWeight K} {t u : ℝ} :
    (imaginaryNormTwist χ t).1.IsNormTwistOnGood u ↔ χ.1.IsNormTwistOnGood (u - t) := by
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
  not_normTwist : ∀ u : ℝ, ¬ χ.1.IsNormTwistOnGood u
  /-- `χ` has ideal partial-sum cancellation. -/
  cancellation : HasCancellation χ
  /-- The conjugate weight `χ.conj` has ideal partial-sum cancellation. -/
  cancellation_conj : HasCancellation χ.conj
  /-- Every imaginary norm twist `χ * N ^ (t * I)` has cancellation. -/
  cancellation_normTwist : ∀ t : ℝ, HasCancellation (imaginaryNormTwist χ t)
  /-- For every `t`, the square of `imaginaryNormTwist χ t` is either a norm twist on its good
  ideals or itself has cancellation. -/
  square_twist : ∀ t : ℝ,
    (∃ u : ℝ, (imaginaryNormTwist χ t ^ 2).1.IsNormTwistOnGood u) ∨
      HasCancellation (imaginaryNormTwist χ t ^ 2)

/-- Smart constructor for `UnitaryCancelling`: `cancellation`, `cancellation_conj`, and
`not_normTwist` all follow from `cancellation_normTwist` at `t = 0`. -/
theorem UnitaryCancelling.of_cancellation_normTwist {χ : UnitaryIdealWeight K}
    (hcanc : ∀ t : ℝ, HasCancellation (imaginaryNormTwist χ t))
    (hsq : ∀ t : ℝ,
      (∃ u : ℝ, (imaginaryNormTwist χ t ^ 2).1.IsNormTwistOnGood u) ∨
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

/-- A weight that is a pure norm twist on its good ideals never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_of_isNormTwistOnGood {χ : UnitaryIdealWeight K} {u : ℝ}
    (hχ : χ.1.IsNormTwistOnGood u) : ¬ UnitaryCancelling χ :=
  fun h ↦ h.not_normTwist u hχ

/-- A weight trivial on its good ideals never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_of_isTrivialOnGood {χ : UnitaryIdealWeight K}
    (hχ : χ.1.IsTrivialOnGood) : ¬ UnitaryCancelling χ :=
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
    (hsq : s.re = 1 → ¬ (χ ^ 2).1.IsNormTwistOnGood (2 * s.im)) :
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
    (hsq : ∀ u : ℝ, ¬ (χ ^ 2).1.IsNormTwistOnGood u) {s : ℂ} (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ s ≠ 0 :=
  hχ.continuedLFunctionOfWeight_ne_zero hs fun _ ↦ hsq (2 * s.im)

/-- If `χ` satisfies `UnitaryCancelling` and `χ ^ 2` is trivial on its good ideals (the quadratic
case), then `continuedLFunctionOfWeight χ` has no zeros on `Re s ≥ 1` away from `s = 1`. -/
theorem UnitaryCancelling.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq
    {χ : UnitaryIdealWeight K} (hχ : UnitaryCancelling χ) (hsq : (χ ^ 2).1.IsTrivialOnGood)
    {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    continuedLFunctionOfWeight χ s ≠ 0 :=
  TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq hχ.cancellation hsq hs hs1

end UnitaryCancelling

section CharacterFamily

variable {K : Type*} [Field K] [NumberField K] {G : Type*} [Group G]

private theorem isTrivialOnGood_of_forall_isGood {χ : MultiplicativeIdealWeight K}
    (h : ∀ I : Ideal (𝓞 K), χ.IsGood I → χ I = 1) : χ.IsTrivialOnGood := by
  have heq : χ = MultiplicativeIdealWeight.ofBadPrimes χ.badPrimes χ.finite_badPrimes := by
    ext I
    rw [MultiplicativeIdealWeight.ofBadPrimes_apply]
    by_cases hI : χ.IsGood I
    · simp [hI, h I hI]
    · rw [(χ.apply_eq_zero_iff_not_isGood I).mpr hI]
      simp [hI]
  rw [heq]
  exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes _

/-- **Character-family cancellation package** for a group-indexed family
`w : G → UnitaryIdealWeight K`. The identity member `w 1` takes the value `1` on its good ideals
(where goodness includes `I ≠ ⊥`, while `w 1` may still vanish at bad primes), the family preserves
products and sends inverses to conjugates, and every imaginary norm twist of every **nontrivial**
member has cancellation. -/
structure IsUnitaryCharacterFamily (w : G → UnitaryIdealWeight K) : Prop where
  /-- The identity member `w 1` equals `1` on every good ideal (and vanishes off them). -/
  isTrivialOnGood_one : (w 1).1.IsTrivialOnGood
  /-- Pointwise multiplication of weights represents group multiplication. -/
  map_mul : ∀ g h : G, w (g * h) = w g * w h
  /-- Complex conjugation of weights represents group inversion. -/
  conj_eq_map_inv : ∀ g : G, (w g).conj = w g⁻¹
  /-- Every imaginary norm twist of every nontrivial member has cancellation. -/
  cancellation_normTwist : ∀ {g : G}, g ≠ 1 → ∀ t : ℝ, HasCancellation (imaginaryNormTwist (w g) t)

namespace IsUnitaryCharacterFamily

/-- Every ideal good for the identity member of a family is nonzero (`I ≠ ⊥`) and has weight `1`. -/
theorem one_apply_of_isGood {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w)
    {I : Ideal (𝓞 K)} (hI : (w 1).1.IsGood I) : I ≠ ⊥ ∧ (w 1).1 I = 1 :=
  ⟨hI.ne_bot, hw.isTrivialOnGood_one.apply_eq_one hI⟩

private theorem badPrimes_eq_of_mul {w : G → UnitaryIdealWeight K}
    (hmul : ∀ g h : G, w (g * h) = w g * w h) (g : G) :
    (w g).1.badPrimes = (w 1).1.badPrimes := by
  apply Set.Subset.antisymm
  · have h1 : (w 1).1 = (w g).1 * (w g⁻¹).1 := by
      rw [← UnitaryIdealWeight.val_mul, ← hmul, mul_inv_cancel]
    intro 𝔭 h𝔭
    rw [MultiplicativeIdealWeight.mem_badPrimes, h1, MultiplicativeIdealWeight.mul_apply,
      MultiplicativeIdealWeight.mem_badPrimes.mp h𝔭, zero_mul]
  · have hg : (w g).1 = (w g).1 * (w 1).1 := by
      rw [← UnitaryIdealWeight.val_mul, ← hmul, mul_one]
    intro 𝔭 h𝔭
    rw [MultiplicativeIdealWeight.mem_badPrimes, hg, MultiplicativeIdealWeight.mul_apply,
      MultiplicativeIdealWeight.mem_badPrimes.mp h𝔭, mul_zero]

/-- All members of a unitary character family share the same set of bad primes. -/
theorem badPrimes_eq {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w) (g : G) :
    (w g).1.badPrimes = (w 1).1.badPrimes :=
  badPrimes_eq_of_mul hw.map_mul g

/-- Smart constructor for `IsUnitaryCharacterFamily`: conjugation compatibility `(w g).conj = w g⁻¹`
follows automatically from unitarity, `isTrivialOnGood_one`, and `map_mul`. -/
theorem of_mul {w : G → UnitaryIdealWeight K} (hone : (w 1).1.IsTrivialOnGood)
    (hmul : ∀ g h : G, w (g * h) = w g * w h)
    (hcanc : ∀ {g : G}, g ≠ 1 → ∀ t : ℝ, HasCancellation (imaginaryNormTwist (w g) t)) :
    IsUnitaryCharacterFamily w := by
  refine ⟨hone, hmul,
    fun g ↦ Subtype.ext (MultiplicativeIdealWeight.ext_heightOneSpectrum fun 𝔭 ↦ ?_), hcanc⟩
  have hbad_g := badPrimes_eq_of_mul hmul g
  have hbad_inv := badPrimes_eq_of_mul hmul g⁻¹
  by_cases h𝔭 : 𝔭 ∈ (w 1).1.badPrimes
  · have hg0 : (w g).1 𝔭.asIdeal = 0 := MultiplicativeIdealWeight.mem_badPrimes.mp (hbad_g ▸ h𝔭)
    have hginv0 : (w g⁻¹).1 𝔭.asIdeal = 0 :=
      MultiplicativeIdealWeight.mem_badPrimes.mp (hbad_inv ▸ h𝔭)
    simp [hg0, hginv0]
  · have hgood1 : (w 1).1.IsGood 𝔭.asIdeal := Ideal.isPrimeTo_asIdeal_iff.mpr h𝔭
    have h𝔭g : 𝔭 ∉ (w g).1.badPrimes := hbad_g ▸ h𝔭
    have hprod : (w g).1 𝔭.asIdeal * (w g⁻¹).1 𝔭.asIdeal = 1 := by
      rw [← MultiplicativeIdealWeight.mul_apply, ← UnitaryIdealWeight.val_mul, ← hmul,
        mul_inv_cancel, hone.apply_eq_one hgood1]
    rw [UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply,
      ← Complex.inv_eq_conj ((w g).2 𝔭 h𝔭g), inv_eq_of_mul_eq_one_right hprod]

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

theorem map_sq {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w) (g : G) :
    w (g ^ 2) = w g ^ 2 :=
  hw.map_pow_of_ne_zero g two_ne_zero

/-- Only the identity member of a unitary character family can be trivial on its good ideals. -/
theorem eq_one_of_isTrivialOnGood {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w)
    {g : G} (hg : (w g).1.IsTrivialOnGood) : g = 1 := by
  by_contra hne
  exact not_hasCancellation_of_isTrivialOnGood hg (by simpa using hw.cancellation_normTwist hne 0)

/-- A unitary character family is injective on `G`, hence forces `G` to be commutative. -/
theorem injective {w : G → UnitaryIdealWeight K} (hw : IsUnitaryCharacterFamily w) :
    Function.Injective w := by
  intro g h hgh
  refine mul_inv_eq_one.mp
    (hw.eq_one_of_isTrivialOnGood (isTrivialOnGood_of_forall_isGood fun I hI ↦ ?_))
  have hIh : (w h).1.IsGood I := by
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

/-- **Every nontrivial member of a unitary character family satisfies `UnitaryCancelling`.**
When `g ^ 2 = 1`, the square of `imaginaryNormTwist (w g) t` is `imaginaryNormTwist (w 1) (2 * t)`,
which is a norm twist on its good ideals; when `g ^ 2 ≠ 1`, it is a twist of the nontrivial member
`w (g ^ 2)` and therefore cancels. -/
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

/-- **Boundary nonvanishing for a unitary character family.** For any nontrivial member `g ≠ 1` and
`Re s ≥ 1`, `continuedLFunctionOfWeight (w g) s ≠ 0` whenever `g ^ 2 ≠ 1` or `s ≠ 1`. -/
theorem continuedLFunctionOfWeight_ne_zero {w : G → UnitaryIdealWeight K}
    (hw : IsUnitaryCharacterFamily w) {g : G} (hg : g ≠ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (hquad : g ^ 2 ≠ 1 ∨ s ≠ 1) :
    continuedLFunctionOfWeight (w g) s ≠ 0 := by
  rcases eq_or_ne (g ^ 2) 1 with hg2 | hg2
  · have hs1 : s ≠ 1 := hquad.resolve_left (not_not.mpr hg2)
    have htriv : (w g ^ 2).1.IsTrivialOnGood := by
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

namespace TauCeti.GlobalNumberFields.RayClassCharacter

open TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Ray class characters of any modulus `𝔪` form a unitary character family.** -/
theorem isUnitaryCharacterFamily (𝔪 : Modulus K) :
    IsUnitaryCharacterFamily (toUnitaryIdealWeight (𝔪 := 𝔪)) :=
  IsUnitaryCharacterFamily.of_mul
    (by
      rw [val_toUnitaryIdealWeight, toMultiplicativeIdealWeight_one]
      exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes 𝔪.support.finite_toSet)
    toUnitaryIdealWeight_mul
    (fun hχ t ↦ by
      rw [imaginaryNormTwist_def]
      exact hasCancellation_normTwist_toUnitaryIdealWeight hχ _ (by simp))

/-- Every nontrivial ray class character's unitary weight satisfies `UnitaryCancelling`. -/
theorem unitaryCancelling {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) :
    UnitaryCancelling χ.toUnitaryIdealWeight :=
  (isUnitaryCharacterFamily 𝔪).unitaryCancelling hχ

/-- The unitary weight of the trivial ray class character never satisfies `UnitaryCancelling`. -/
theorem not_unitaryCancelling_one :
    ¬ UnitaryCancelling (1 : RayClassCharacter 𝔪).toUnitaryIdealWeight :=
  fun h ↦ not_hasCancellation_one_toUnitaryIdealWeight h.cancellation

/-- A ray class character's unitary weight satisfies `UnitaryCancelling` if and only if `χ ≠ 1`. -/
@[simp]
theorem unitaryCancelling_toUnitaryIdealWeight_iff {χ : RayClassCharacter 𝔪} :
    UnitaryCancelling χ.toUnitaryIdealWeight ↔ χ ≠ 1 :=
  ⟨fun h ↦ by rintro rfl; exact not_unitaryCancelling_one h, unitaryCancelling⟩

/-- **Boundary nonvanishing for the continued L-function of a nontrivial ray class character** on
`Re s ≥ 1`, away from `s = 1` in the quadratic case `χ ^ 2 = 1`. -/
theorem continuedLFunctionOfWeight_ne_zero {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) (hquad : χ ^ 2 ≠ 1 ∨ s ≠ 1) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 :=
  (isUnitaryCharacterFamily 𝔪).continuedLFunctionOfWeight_ne_zero hχ hs hquad

end TauCeti.GlobalNumberFields.RayClassCharacter

namespace TauCeti.LFunctions

open GlobalNumberFields

section HeckeTransfer

open Filter Set
open scoped Topology

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- Once `heckeLFunctionC χ` (`χ ≠ 1`) agrees with its defining L-series on `Re s > 1` (for example
via `TauCeti.meromorphicContinuation_eqOn` from any whole-plane meromorphic continuation),
meromorphic normal form automatically identifies it with
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` throughout `Re s > 1 - 1 / [K : ℚ]` — without
assuming regularity across `Re s = 1` in advance. -/
theorem heckeLFunctionC_eq_continuedLFunctionOfWeight {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (heq : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re) :
    heckeLFunctionC χ s = continuedLFunctionOfWeight χ.toUnitaryIdealWeight s := by
  let U : Set ℂ := {z | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U :=
    ((convex_Ioi (1 - 1 / (Module.finrank ℚ K : ℝ))).linear_preimage Complex.reLm).isPreconnected
  have hF_anal : AnalyticOnNhd ℂ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight) U :=
    (differentiableOn_continuedLFunctionOfWeight
      (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ)).analyticOnNhd hU_open
  have h2U : (2 : ℂ) ∈ U :=
    (cancellationExponent_lt_one (K := K)).trans (by norm_num : (1 : ℝ) < (2 : ℂ).re)
  have hgerm : heckeLFunctionC χ =ᶠ[𝓝[≠] (2 : ℂ)]
      continuedLFunctionOfWeight χ.toUnitaryIdealWeight := by
    have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := hopen1.mem_nhds (by norm_num)
    exact (Filter.eventually_of_mem hmem fun z hz ↦
      (heq hz).trans (continuedLFunctionOfWeight_eq_LSeries _ hz).symm).filter_mono
      nhdsWithin_le_nhds
  have hnf : MeromorphicNFOn (heckeLFunctionC χ) U :=
    fun z _ ↦ meromorphicNFOn_heckeLFunctionC χ (mem_univ z)
  exact hnf.eqOn_of_isPreconnected hF_anal.meromorphicNFOn hU_conn h2U hgerm hs

/-- Once `heckeLFunctionC χ` (`χ ≠ 1`) agrees with its defining L-series on `Re s > 1`, cancellation
automatically makes `heckeLFunctionC χ` holomorphic across `Re s = 1` throughout
`Re s > 1 - 1 / [K : ℚ]` (ruling out any pole on that half-plane, in particular at `s = 1`). -/
theorem analyticOnNhd_heckeLFunctionC_of_eqOn {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (heq : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re}) :
    AnalyticOnNhd ℂ (heckeLFunctionC χ) {z | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} := by
  have hU_open : IsOpen {z : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hF_anal : AnalyticOnNhd ℂ (continuedLFunctionOfWeight χ.toUnitaryIdealWeight)
      {z | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} :=
    (differentiableOn_continuedLFunctionOfWeight
      (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ)).analyticOnNhd hU_open
  refine fun s hs ↦ (hF_anal s hs).congr ?_
  filter_upwards [hU_open.mem_nhds hs] with z hz using
    (heckeLFunctionC_eq_continuedLFunctionOfWeight hχ heq hz).symm

/-- Boundary nonvanishing for `heckeLFunctionC χ` on `Re s ≥ 1` away from the quadratic point
`(χ ^ 2 = 1, s = 1)`, requiring only half-plane agreement on `Re s > 1`. -/
theorem heckeLFunctionC_ne_zero_of_eqOn {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    (heq : EqOn (heckeLFunctionC χ)
      (LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction)) {z | 1 < z.re})
    {s : ℂ} (hs : 1 ≤ s.re) (hquad : χ ^ 2 ≠ 1 ∨ s ≠ 1) :
    heckeLFunctionC χ s ≠ 0 := by
  rw [heckeLFunctionC_eq_continuedLFunctionOfWeight hχ heq
    ((cancellationExponent_lt_one (K := K)).trans_le hs)]
  exact RayClassCharacter.continuedLFunctionOfWeight_ne_zero hχ hs hquad

end HeckeTransfer

section ModFourChecks

/-- **The nontrivial ray class character modulo `(4)·∞` over `ℚ`**, corresponding to Mathlib's
quadratic character `ZMod.χ₄` under `ratDirichletEquiv`. -/
def ratModFourChar : RayClassCharacter (ratModulus 4 four_ne_zero) :=
  (ratDirichletEquiv 4 four_ne_zero).symm (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))

/-- Defining equation of `TauCeti.LFunctions.ratModFourChar`. -/
theorem ratModFourChar_def :
    ratModFourChar =
      (ratDirichletEquiv 4 four_ne_zero).symm (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) := (rfl)

/-- `ratModFourChar` is nontrivial (`χ₄(-1) = -1 ≠ 1`). -/
theorem ratModFourChar_ne_one : ratModFourChar ≠ 1 := by
  intro h
  have h1 := congrArg (fun η ↦ ratDirichletEquiv 4 four_ne_zero η (-1 : ZMod 4)) h
  rw [ratModFourChar_def, MulEquiv.apply_symm_apply, map_one,
    MulChar.ringHomComp_apply] at h1
  have hχ : ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1 := ZMod.χ₄_int_three_mod_four (by decide)
  rw [Int.cast_neg, Int.cast_one] at hχ
  have hone : (1 : DirichletCharacter ℂ 4) (-1 : ZMod 4) = 1 :=
    MulChar.one_apply (Units.isUnit (-1 : (ZMod 4)ˣ))
  rw [hχ, hone] at h1
  norm_num at h1

/-- `ratModFourChar` has order two (`ratModFourChar ^ 2 = 1`). -/
@[simp]
theorem ratModFourChar_sq : ratModFourChar ^ 2 = 1 := by
  apply (ratDirichletEquiv 4 four_ne_zero).injective
  rw [map_pow, map_one, ratModFourChar_def, MulEquiv.apply_symm_apply]
  exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

/-- **Quadratic check for `UnitaryCancelling`**: the weight of `χ₄` over `ℚ` satisfies
`UnitaryCancelling`, its square is trivial on its good ideals, and its square does **not** have
cancellation (so requiring `χ ^ 2` to cancel would reject `χ₄`). -/
theorem unitaryCancelling_ratModFourChar :
    UnitaryCancelling ratModFourChar.toUnitaryIdealWeight ∧
      (ratModFourChar.toUnitaryIdealWeight ^ 2).1.IsTrivialOnGood ∧
      ¬ HasCancellation (ratModFourChar.toUnitaryIdealWeight ^ 2) := by
  have hmul : ratModFourChar * ratModFourChar = 1 := by
    simpa [_root_.pow_two] using ratModFourChar_sq
  have hsq_eq : ratModFourChar.toUnitaryIdealWeight ^ 2 =
      (1 : RayClassCharacter (ratModulus 4 four_ne_zero)).toUnitaryIdealWeight := by
    rw [pow_two, ← RayClassCharacter.toUnitaryIdealWeight_mul, hmul]
  refine ⟨RayClassCharacter.unitaryCancelling ratModFourChar_ne_one, ?_, ?_⟩
  · rw [hsq_eq, RayClassCharacter.val_toUnitaryIdealWeight,
      RayClassCharacter.toMultiplicativeIdealWeight_one]
    exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes _
  · rw [hsq_eq]
    exact RayClassCharacter.not_hasCancellation_one_toUnitaryIdealWeight

/-- **Bad-prime check for `IsUnitaryCharacterFamily` modulo `4`**: the ray class characters modulo
`(4)·∞` over `ℚ` form a unitary character family whose identity member vanishes at `(2 : 𝓞 ℚ)`
(so the family identity law holds only on good ideals, not at ideals meeting `(4)`). -/
theorem isUnitaryCharacterFamily_ratModFour_and_apply_two_eq_zero :
    IsUnitaryCharacterFamily
        (RayClassCharacter.toUnitaryIdealWeight (𝔪 := ratModulus 4 four_ne_zero)) ∧
      (1 : RayClassCharacter (ratModulus 4 four_ne_zero)).toUnitaryIdealWeight.1
          (Ideal.span {(2 : 𝓞 ℚ)}) = 0 := by
  refine ⟨RayClassCharacter.isUnitaryCharacterFamily _, ?_⟩
  rw [RayClassCharacter.val_toUnitaryIdealWeight]
  refine RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ fun hprime ↦ ?_
  have htop : Ideal.span {(2 : 𝓞 ℚ)} ≠ ⊤ := by
    intro htop
    have hnorm :=
      RingOfIntegers.absNorm_span_natCast_of_finrank_eq_one (Module.finrank_self ℚ) 2
    rw [Nat.cast_two, htop, Ideal.absNorm_top] at hnorm
    omega
  obtain ⟨𝔪₂, hmax, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 ℚ)}) htop
  have hbot : 𝔪₂ ≠ ⊥ := fun h ↦ by
    have h2 : (2 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := h ▸ hle (Ideal.mem_span_singleton_self _)
    exact two_ne_zero ((Submodule.mem_bot (R := 𝓞 ℚ)).mp h2)
  let 𝔭 : HeightOneSpectrum (𝓞 ℚ) := ⟨𝔪₂, hmax.isPrime, hbot⟩
  have h2mem : (2 : 𝓞 ℚ) ∈ 𝔭.asIdeal := hle (Ideal.mem_span_singleton_self _)
  have h4mem : ((4 : ℕ) : 𝓞 ℚ) ∈ 𝔭.asIdeal := by
    have h4 : ((4 : ℕ) : 𝓞 ℚ) = (2 : 𝓞 ℚ) * (2 : 𝓞 ℚ) := by norm_num
    exact h4 ▸ 𝔭.asIdeal.mul_mem_left _ h2mem
  exact (Ideal.isPrimeTo_iff.mp hprime).2 𝔭 (mem_ratModulus_support_iff.mpr h4mem)
    (Ideal.dvd_iff_le.mpr hle)

end ModFourChecks

end TauCeti.LFunctions
