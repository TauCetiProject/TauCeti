/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse.RealClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Clifford
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Signature
import Mathlib.FieldTheory.IsRealClosed.Real
import TauCeti.Data.Nat.Choose.Lucas

/-!
# The Clifford invariant over ordered real closed fields and `ℝ`

Over an ordered real closed field `K`, every Witt class equals the integer cast of its signature
`σ = signature x ∈ ℤ` (`WittRing.intCast_signature`). Combined with eightfold periodicity of the
Clifford invariant along multiples of `⟨1⟩` (`8 ∈ I(K)³`), the Clifford invariant of any Witt class
or regular quadratic form depends only on `σ mod 8`:

* `c(x) = [(-1, -1)]` when `σ % 8 ∈ {3, 4, 5, 6}`, and
* `c(x) = 1` when `σ % 8 ∈ {0, 1, 2, 7}`.

On `⟨1, …, 1⟩` of rank `n` (`σ = n`), this generalizes the sum-of-squares computation in
`TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Clifford.Real`, reproducing the Bott-periodic
pattern `1, 1, [ℍ], [ℍ], [ℍ], [ℍ], 1, 1` for `n = 1, …, 8`, governed solely by the `C(n + 1, 4)`
exponent of Lam's comparison (Lam V.3.20). On `⟨-1, -1, -1⟩` (`σ = -3`, `(-3) % 8 = 5`), `c = [ℍ]`
while `s = [ℍ]` and both correction factors in Lam V.3.20 equal `[ℍ]`, confirming that the
discriminant correction `[(-1, d)]^C(n - 1, 2)` cannot be omitted.

The formula also illustrates how additivity behaves over `ℝ` when only one summand lies in
`I(ℝ)²`: `4 ∈ I(ℝ)²` and `3 ∉ I(ℝ)²` still satisfy `c(4 + 3) = 1 = [ℍ] · [ℍ]`. For the general
semireal failure of additivity `c(2 + 1) ≠ c(2) · c(1)`, see
`TauCeti.LinearAlgebra.QuadraticForm.Witt.Clifford`; for the general semireal non-classification
witness `TauCeti.RegularFormClass.four_nsmul_one_invariants_eq_and_ne` showing that
`⟨1, 1, 1, 1⟩` and `⟨-1, -1, -1, -1⟩` share all four invariants `(4, 0, 1, [(-1, -1)])` while
remaining non-isometric, see
`TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Clifford.Basic`.

## Main results

* `TauCeti.WittRing.cliffordInvariant_eq_ite_signature`,
  `TauCeti.RegularFormClass.cliffordInvariant_eq_ite_signature`, and
  `QuadraticForm.cliffordInvariant_formClass_eq_ite_signature`: eightfold-periodic formula for the
  Clifford invariant over an ordered real closed field.
* `TauCeti.cliffordInvariant_formClass_realSignatureForm`: the Clifford invariant of the real
  normal form `p⟨1⟩ ⊥ q⟨-1⟩` is `[ℍ[ℝ]]` when `(p - q) % 8 ∈ {3, 4, 5, 6}` and `1` otherwise.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, §3, Theorems 3.4 and
  3.20, and Caution on p. 120.
-/

public section

open QuadraticMap QuadraticForm TauCeti

namespace TauCeti

section IsRealClosed

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Invertible (2 : K)]
  [IsRealClosed K]

namespace WittRing

/-- Over an ordered real closed field, the Clifford invariant of a Witt class `x` is
`[(-1, -1)]^C((signature x % 8) + 1, 4)`. -/
theorem cliffordInvariant_eq_pow_choose_emod_signature (x : WittRing K) :
    cliffordInvariant x =
      BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ^ ((signature x % 8).toNat + 1).choose 4 := by
  conv_lhs => rw [← intCast_signature x]
  exact cliffordInvariant_intCast (signature x)

/-- **Closed formula for the Clifford invariant on `W(K)` over an ordered real closed field**:
`c(x)` equals `[(-1, -1)]` when `signature x % 8 ∈ {3, 4, 5, 6}` and `1` otherwise. -/
theorem cliffordInvariant_eq_ite_signature (x : WittRing K) :
    cliffordInvariant x =
      if 3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6 then
        BrauerGroup.quaternionClass (-1 : Kˣ) (-1)
      else 1 := by
  have h0 : 0 ≤ signature x % 8 := Int.emod_nonneg _ (by norm_num)
  have _ : signature x % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  have hc : ((signature x % 8).toNat + 1).choose 4 % 2 =
      ((signature x % 8).toNat + 1) / 4 % 2 := by
    simpa [Nat.ModEq] using
      Choose.choose_pow_mul_modEq_choose_div_nat (p := 2) ((signature x % 8).toNat + 1) 2 1
  have heven : Even (((signature x % 8).toNat + 1).choose 4) ↔
      ¬(3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6) := by
    rw [Nat.even_iff, hc]
    omega
  rw [cliffordInvariant_eq_pow_choose_emod_signature, BrauerGroup.quaternionClass_pow]
  simp only [heven, ite_not]

/-- Over an ordered real closed field, the Clifford invariant of a Witt class is trivial if and
only if its signature modulo `8` lies outside `{3, 4, 5, 6}` (that is, `< 3` or `= 7`). -/
theorem cliffordInvariant_eq_one_iff_signature (x : WittRing K) :
    cliffordInvariant x = 1 ↔ signature x % 8 < 3 ∨ signature x % 8 = 7 := by
  have h0 : 0 ≤ signature x % 8 := Int.emod_nonneg _ (by norm_num)
  have _ : signature x % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  rw [cliffordInvariant_eq_ite_signature]
  split_ifs with h
  · exact ⟨fun h1 => absurd h1 BrauerGroup.quaternionClass_neg_one_neg_one_ne_one,
      fun h' => by omega⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

/-- Over an ordered real closed field, the Clifford invariant of a Witt class equals `[(-1, -1)]`
if and only if `3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6`. -/
theorem cliffordInvariant_eq_neg_one_neg_one_iff_signature (x : WittRing K) :
    cliffordInvariant x = BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ↔
      3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6 := by
  rw [cliffordInvariant_eq_ite_signature]
  split_ifs with h
  · simp [h]
  · simp [h, BrauerGroup.quaternionClass_neg_one_neg_one_ne_one.symm]

end WittRing

namespace RegularFormClass

/-- **Closed formula for the Clifford invariant of a regular-form class over an ordered real closed
field**: `c(x)` is `[(-1, -1)]` when `signature x % 8 ∈ {3, 4, 5, 6}` and `1` otherwise. -/
theorem cliffordInvariant_eq_ite_signature (x : RegularFormClass K) :
    cliffordInvariant x =
      if 3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6 then
        BrauerGroup.quaternionClass (-1 : Kˣ) (-1)
      else 1 := by
  rw [← WittRing.cliffordInvariant_wittClass, WittRing.cliffordInvariant_eq_ite_signature,
    WittRing.signature_wittClass]

/-- Over an ordered real closed field, the Clifford invariant of a regular-form class is trivial if
and only if `signature x % 8 < 3 ∨ signature x % 8 = 7`. -/
theorem cliffordInvariant_eq_one_iff_signature (x : RegularFormClass K) :
    cliffordInvariant x = 1 ↔ signature x % 8 < 3 ∨ signature x % 8 = 7 := by
  rw [← WittRing.cliffordInvariant_wittClass, WittRing.cliffordInvariant_eq_one_iff_signature,
    WittRing.signature_wittClass]

/-- Over an ordered real closed field, the Clifford invariant of a regular-form class equals
`[(-1, -1)]` if and only if `3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6`. -/
theorem cliffordInvariant_eq_neg_one_neg_one_iff_signature (x : RegularFormClass K) :
    cliffordInvariant x = BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ↔
      3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6 := by
  rw [← WittRing.cliffordInvariant_wittClass,
    WittRing.cliffordInvariant_eq_neg_one_neg_one_iff_signature, WittRing.signature_wittClass]

end RegularFormClass

end IsRealClosed

end TauCeti

namespace QuadraticForm

variable {K M : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Invertible (2 : K)]
  [IsRealClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- Over an ordered real closed field, the Clifford invariant of a regular quadratic form `Q` is
`[(-1, -1)]` when `(sigPos Q - sigNeg Q) % 8 ∈ {3, 4, 5, 6}` and `1` otherwise. -/
theorem cliffordInvariant_formClass_eq_ite_signature (Q : _root_.QuadraticForm K M)
    (hQ : Q.Nondegenerate) :
    RegularFormClass.cliffordInvariant (formClass Q hQ) =
      if 3 ≤ ((sigPos Q : ℤ) - sigNeg Q) % 8 ∧ ((sigPos Q : ℤ) - sigNeg Q) % 8 ≤ 6 then
        BrauerGroup.quaternionClass (-1 : Kˣ) (-1)
      else 1 := by
  rw [RegularFormClass.cliffordInvariant_eq_ite_signature, signature_formClass]

end QuadraticForm

namespace TauCeti

open scoped _root_.Quaternion

/-! ### Specialization to `ℝ` and worked examples -/

/-- The Clifford invariant of the real normal form `p⟨1⟩ ⊥ q⟨-1⟩` is `[ℍ[ℝ]]` when
`(p - q) % 8 ∈ {3, 4, 5, 6}` and `1` otherwise. -/
@[simp]
theorem cliffordInvariant_formClass_realSignatureForm (p q : ℕ) :
    RegularFormClass.cliffordInvariant
        (formClass (realSignatureForm p q) (nondegenerate_realSignatureForm p q)) =
      if 3 ≤ ((p : ℤ) - q) % 8 ∧ ((p : ℤ) - q) % 8 ≤ 6 then
        BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])
      else 1 := by
  rw [QuadraticForm.cliffordInvariant_formClass_eq_ite_signature, sigPos_realSignatureForm,
    sigNeg_realSignatureForm, BrauerGroup.quaternionClass_neg_one_neg_one_real]

section Examples

/-- **Eightfold Bott periodicity on positive definite forms `⟨1, …, 1⟩` over `ℝ`.** For
`n = 1, …, 8`, the Clifford invariants of `n⟨1⟩` are `1, 1, [ℍ[ℝ]], [ℍ[ℝ]], [ℍ[ℝ]], [ℍ[ℝ]], 1, 1`,
matching the Brauer classes of `ℝ`, `M₂(ℝ)`, `ℍ`, `M₂(ℍ)`, `M₂(ℍ)`, `M₄(ℍ)`, `M₈(ℝ)`, `M₁₆(ℝ)`. -/
example :
    let H := BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])
    [1, 2, 3, 4, 5, 6, 7, 8].map (fun n =>
        RegularFormClass.cliffordInvariant
          (formClass (realSignatureForm n 0) (nondegenerate_realSignatureForm n 0))) =
      [1, 1, H, H, H, H, 1, 1] := by
  simp [cliffordInvariant_formClass_realSignatureForm]

/-- **The negative definite ternary form `⟨-1, -1, -1⟩` over `ℝ`.** Its Hasse invariant is
`[ℍ[ℝ]]`, its discriminant correction `[(-1, d)]^C(n - 1, 2)` in Lam V.3.20 is also `[ℍ[ℝ]]`, and
its Clifford invariant is `[ℍ[ℝ]]` (whereas omitting the discriminant correction would multiply
`s = [ℍ[ℝ]]` by `[(-1, -1)]^C(4, 4) = [ℍ[ℝ]]` to give `1`). -/
example :
    let q := formClass (realSignatureForm 0 3) (nondegenerate_realSignatureForm 0 3)
    let H := BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])
    RegularFormClass.hasseInvariant q = H ∧
      BrauerGroup.quaternionClassOnSquareClasses (squareClass (-1 : ℝˣ))
          (RegularFormClass.discr q) ^ (q.rank - 1).choose 2 = H ∧
      RegularFormClass.cliffordInvariant q = H := by
  dsimp only
  refine ⟨?_, ?_, by simp⟩
  · rw [hasseInvariant_formClass_realSignatureForm,
      ← BrauerGroup.quaternionClass_neg_one_neg_one_real,
      (BrauerGroup.quaternionClass_neg_one_neg_one_pow_eq_self_iff _).mpr (by decide)]
  · rw [← RegularFormClass.sigPos_add_sigNeg_eq_rank, RegularFormClass.discr_eq_sigNeg_nsmul,
      sigPos_formClass, sigNeg_formClass, sigPos_realSignatureForm, sigNeg_realSignatureForm,
      BrauerGroup.quaternionClassOnSquareClasses_nsmul_right,
      BrauerGroup.quaternionClassOnSquareClasses_squareClass, ← pow_mul,
      ← BrauerGroup.quaternionClass_neg_one_neg_one_real]
    exact (BrauerGroup.quaternionClass_neg_one_neg_one_pow_eq_self_iff _).mpr (by decide)

/-- **Mixed-summand `I²` additivity over `ℝ`.** Only one summand needs to lie in `I(ℝ)²` for the
Clifford invariant to be additive: `4 ∈ I(ℝ)²` while `3 ∉ I(ℝ)²`, and both have Clifford invariant
`[ℍ[ℝ]]`, while `4 + 3 = 7` has trivial Clifford invariant `1 = [ℍ[ℝ]] · [ℍ[ℝ]]`. -/
example :
    let H := BrauerGroup.mk (CSA.of ℝ ℍ[ℝ])
    (4 : WittRing ℝ) ∈ fundamentalIdeal ℝ ^ 2 ∧
      (3 : WittRing ℝ) ∉ fundamentalIdeal ℝ ^ 2 ∧
      WittRing.cliffordInvariant (4 : WittRing ℝ) = H ∧
      WittRing.cliffordInvariant (3 : WittRing ℝ) = H ∧
      WittRing.cliffordInvariant ((4 : WittRing ℝ) + 3) = 1 := by
  have hnot3 : (3 : WittRing ℝ) ∉ fundamentalIdeal ℝ ^ 2 := by
    rw [mem_fundamentalIdeal_pow_iff_dvd_signature]
    have hsig3 : WittRing.signature (3 : WittRing ℝ) = 3 := by
      simpa using map_ofNat WittRing.signature 3
    rw [hsig3]
    norm_num
  have h4 : WittRing.cliffordInvariant (4 : WittRing ℝ) = BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) := by
    have h4z : (4 : WittRing ℝ) = ((4 : ℤ) : WittRing ℝ) := by norm_num
    rw [h4z, WittRing.cliffordInvariant_eq_ite_signature, map_intCast]
    norm_num
    exact BrauerGroup.quaternionClass_neg_one_neg_one_real
  have h3 : WittRing.cliffordInvariant (3 : WittRing ℝ) = BrauerGroup.mk (CSA.of ℝ ℍ[ℝ]) := by
    have h3z : (3 : WittRing ℝ) = ((3 : ℤ) : WittRing ℝ) := by norm_num
    rw [h3z, WittRing.cliffordInvariant_eq_ite_signature, map_intCast]
    norm_num
    exact BrauerGroup.quaternionClass_neg_one_neg_one_real
  have h7 : WittRing.cliffordInvariant ((4 : WittRing ℝ) + 3) = 1 := by
    rw [WittRing.cliffordInvariant_add_of_mem_fundamentalIdeal_sq four_mem_fundamentalIdeal_sq,
      h4, h3, ← BrauerGroup.quaternionClass_neg_one_neg_one_real, ← pow_two,
      BrauerGroup.quaternionClass_sq]
  exact ⟨four_mem_fundamentalIdeal_sq, hnot3, h4, h3, h7⟩

end Examples

end TauCeti
