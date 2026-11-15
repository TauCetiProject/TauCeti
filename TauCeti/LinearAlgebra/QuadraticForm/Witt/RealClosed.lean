/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BrauerGroup.Real
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Hasse.RealClosed
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Clifford
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Signature
import Mathlib.FieldTheory.IsRealClosed.Real

/-!
# The Clifford invariant and `I²/I³` over ordered real closed fields and `ℝ`

Over an ordered real closed field `K`, every Witt class equals the integer cast of its signature
`σ = signature x ∈ ℤ` (`WittRing.intCast_signature`). Combined with eightfold periodicity of the
Clifford invariant along multiples of `⟨1⟩` (`8 ∈ I(K)³`), the Clifford invariant of any Witt class
or regular quadratic form depends only on `σ mod 8`:

* `c(x) = [(-1, -1)]` when `σ % 8 ∈ {3, 4, 5, 6}`, and
* `c(x) = 1` when `σ % 8 ∈ {0, 1, 2, 7}`.

On `⟨1, …, 1⟩` of rank `n` (`σ = n`), this reproduces the Bott-periodic pattern
`1, 1, [ℍ], [ℍ], [ℍ], [ℍ], 1, 1` for `n = 1, …, 8`, governed solely by the `C(n + 1, 4)` exponent
of Lam's comparison (Lam V.3.20). On `⟨-1, -1, -1⟩` (`σ = -3`, `(-3) % 8 = 5`), `c = [ℍ]` while
`s = [ℍ]` and both correction factors in Lam V.3.20 equal `[ℍ]`, confirming that the discriminant
correction `[(-1, d)]^C(n - 1, 2)` cannot be omitted.

The formula also witnesses two sharp boundaries of the general theory:

* `c` is **not** additive on `W(K)`: `c(⟨1, 1⟩ + ⟨1⟩) = c(⟨1, 1, 1⟩) = [(-1, -1)]`, whereas
  `c(⟨1, 1⟩) · c(⟨1⟩) = 1`, while `4 ∈ I(K)²` and `3 ∉ I(K)²` still satisfy
  `c(4 + 3) = 1 = [(-1, -1)] · [(-1, -1)]` with only one summand in `I(K)²`;
* even adjoining the Clifford invariant to `(rank, discr, hasseInvariant)` does **not** classify
  regular forms over `K`, since `⟨1, 1, 1, 1⟩` (`σ = 4`) and `⟨-1, -1, -1, -1⟩` (`σ = -4`) share
  all four invariants `(4, 0, 1, [(-1, -1)])`.

On the filtration quotient `I(K)²/I(K)³`, elements of `I(K)²` have signature divisible by `4`, so
`σ % 8` is `0` (when `x ∈ I(K)³`) or `4` (when `x ∉ I(K)³`). Thus `ker(cliffordHomI2) = I(K)³` and
`cliffordHomI2Bar` is injective over every ordered real closed field. Over `ℝ`, Frobenius' theorem
identifies `BrauerGroup ℝ` with `{1, [ℍ[ℝ]]}`, making `cliffordHomI2Bar` an isomorphism
`I(ℝ)²/I(ℝ)³ ≃+ Additive (BrauerGroup ℝ)`.

## Main definitions and results

* `TauCeti.WittRing.cliffordInvariant_eq_ite_signature` and
  `TauCeti.RegularFormClass.cliffordInvariant_eq_ite_signature`: eightfold-periodic formula for the
  Clifford invariant over an ordered real closed field.
* `TauCeti.WittRing.not_forall_cliffordInvariant_add_eq_mul`: the Clifford invariant is not a
  homomorphism on `W(K)` over any semireal field.
* `TauCeti.RegularFormClass.four_nsmul_one_invariants_eq_and_ne`: `⟨1, 1, 1, 1⟩` and
  `⟨-1, -1, -1, -1⟩` share rank, discriminant, Hasse invariant, and Clifford invariant while
  remaining non-isometric over any ordered field.
* `TauCeti.cliffordHomI2_eq_zero_iff_mem_fundamentalIdeal_cube`, `TauCeti.ker_cliffordHomI2`, and
  `TauCeti.cliffordHomI2Bar_injective`: `ker(c : I(K)² → Br(K)) = I(K)³` over any ordered real
  closed field.
* `TauCeti.cliffordHomI2BarEquivReal`: the isomorphism
  `I(ℝ)²/I(ℝ)³ ≃+ Additive (BrauerGroup ℝ)`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, §3, Theorems 3.4 and
  3.20, and Caution on p. 120.
-/

public section

open QuadraticMap QuadraticForm TauCeti

namespace TauCeti

private theorem even_choose_four_succ_iff_of_lt_eight {r : ℕ} (hr : r < 8) :
    Even ((r + 1).choose 4) ↔ ¬(3 ≤ r ∧ r ≤ 6) := by
  interval_cases r <;> decide

section Semireal

variable {K : Type*} [Field K] [IsSemireal K] [Invertible (2 : K)]

namespace WittRing

/-- **Failure of additivity outside `I(K)²`**: over any semireal field, on `2 = ⟨1, 1⟩` and
`1 = ⟨1⟩` in `W(K)` (neither of which lies in `I(K)²`), `c(2 + 1) = c(3) = [(-1, -1)]`, whereas
`c(2) · c(1) = 1`. -/
theorem cliffordInvariant_two_add_one_ne :
    cliffordInvariant ((2 : WittRing K) + 1) ≠
      cliffordInvariant (2 : WittRing K) * cliffordInvariant (1 : WittRing K) := by
  have h3 : ((2 : WittRing K) + 1) = ((3 : ℕ) : WittRing K) := by norm_num
  have h2 : (2 : WittRing K) = ((2 : ℕ) : WittRing K) := by norm_num
  have h1 : (1 : WittRing K) = ((1 : ℕ) : WittRing K) := by norm_num
  rw [h3, cliffordInvariant_natCast, h2, cliffordInvariant_natCast, h1, cliffordInvariant_natCast]
  norm_num
  exact BrauerGroup.quaternionClass_neg_one_neg_one_ne_one

/-- The Clifford invariant is not a homomorphism from the additive group of `W(K)` to
`BrauerGroup K` over any semireal field. -/
theorem not_forall_cliffordInvariant_add_eq_mul :
    ¬∀ x y : WittRing K, cliffordInvariant (x + y) = cliffordInvariant x * cliffordInvariant y :=
  fun h => cliffordInvariant_two_add_one_ne (h 2 1)

end WittRing

end Semireal

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
  have hr : (signature x % 8).toNat < 8 := by omega
  have hcond : (3 ≤ (signature x % 8).toNat ∧ (signature x % 8).toNat ≤ 6) ↔
      (3 ≤ signature x % 8 ∧ signature x % 8 ≤ 6) := by omega
  rw [cliffordInvariant_eq_pow_choose_emod_signature, BrauerGroup.quaternionClass_pow]
  simp only [even_choose_four_succ_iff_of_lt_eight hr, hcond, ite_not]

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

omit [IsRealClosed K] in
/-- Over any ordered field, `⟨1, 1, 1, 1⟩` and `⟨-1, -1, -1, -1⟩` share rank (`4`), discriminant
(`0`), Hasse invariant (`1`), and Clifford invariant (`[(-1, -1)]`), while remaining non-isometric
by signature. -/
theorem four_nsmul_one_invariants_eq_and_ne :
    let posFour : RegularFormClass K := 4 • 1
    let negFour : RegularFormClass K :=
      4 • Quotient.mk (regularFormSetoid K) ⟨1, fun _ => (-1 : Kˣ)⟩
    posFour.rank = 4 ∧ negFour.rank = 4 ∧
      discr posFour = 0 ∧ discr negFour = 0 ∧
      hasseInvariant posFour = 1 ∧ hasseInvariant negFour = 1 ∧
      cliffordInvariant posFour = BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ∧
      cliffordInvariant negFour = BrauerGroup.quaternionClass (-1 : Kˣ) (-1) ∧
      posFour ≠ negFour := by
  obtain ⟨hr1, hr2, hd1, hd2, hs1, hs2, hne⟩ := four_nsmul_one_ne_four_nsmul_neg_one (K := K)
  refine ⟨hr1, hr2, hd1, hd2, hs1, hs2, ?_, ?_, hne⟩
  · rw [cliffordInvariant_nsmul_one,
      (BrauerGroup.quaternionClass_neg_one_neg_one_pow_eq_self_iff (Nat.choose 5 4)).mpr
        (by decide)]
  · rw [cliffordInvariant_eq_hasseInvariant_mul, hs2, hd2, hr2,
      BrauerGroup.quaternionClassOnSquareClasses_zero_right, one_pow, mul_one, one_mul,
      (BrauerGroup.quaternionClass_neg_one_neg_one_pow_eq_self_iff (Nat.choose 5 4)).mpr
        (by decide)]

end RegularFormClass

/-! ### Kernel and injectivity on `I(K)²/I(K)³` -/

/-- **Merkurjev's kernel criterion over an ordered real closed field**: an element of `I(K)²` lies
in the kernel of `cliffordHomI2` if and only if it belongs to `I(K)³`. -/
theorem cliffordHomI2_eq_zero_iff_mem_fundamentalIdeal_cube (x : ↥(fundamentalIdeal K ^ 2)) :
    cliffordHomI2 x = 0 ↔ (x : WittRing K) ∈ fundamentalIdeal K ^ 3 := by
  refine ⟨fun hx => ?_, cliffordHomI2_eq_zero⟩
  rw [cliffordHomI2_apply, ofMul_eq_zero,
    WittRing.cliffordInvariant_eq_one_iff_signature] at hx
  obtain ⟨k, hk⟩ := (mem_fundamentalIdeal_pow_iff_dvd_signature (K := K) 2).mp x.2
  rw [mem_fundamentalIdeal_pow_iff_dvd_signature]
  have hrem : WittRing.signature (x : WittRing K) % (2 ^ 3 : ℤ) = 0 := by omega
  exact Int.dvd_of_emod_eq_zero hrem

/-- Over an ordered real closed field, the kernel of
`cliffordHomI2 : I(K)² →+ Additive (BrauerGroup K)` is `I(K)³`. -/
@[simp]
theorem ker_cliffordHomI2 : (cliffordHomI2 (K := K)).ker = fundamentalI3InI2 K := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_fundamentalI3InI2,
    cliffordHomI2_eq_zero_iff_mem_fundamentalIdeal_cube]

/-- Over an ordered real closed field, the induced Clifford homomorphism
`cliffordHomI2Bar : I(K)²/I(K)³ →+ Additive (BrauerGroup K)` is injective. -/
theorem cliffordHomI2Bar_injective : Function.Injective (cliffordHomI2Bar (K := K)) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [cliffordHomI2Bar_mk, cliffordHomI2_eq_zero_iff_mem_fundamentalIdeal_cube] at hq
  exact (QuotientAddGroup.eq_zero_iff x).mpr (mem_fundamentalI3InI2.mpr hq)

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

/-- Over `ℝ`, `cliffordHomI2Bar` is surjective onto `Additive (BrauerGroup ℝ)`, since `4 ∈ I(ℝ)²`
maps to `[ℍ[ℝ]]`, which generates `BrauerGroup ℝ`. -/
theorem cliffordHomI2Bar_surjective_real :
    Function.Surjective (cliffordHomI2Bar (K := ℝ)) := by
  intro y
  rcases Quaternion.eq_one_or_eq_mk (Additive.toMul y) with hy | hy
  · refine ⟨0, ?_⟩
    rw [map_zero]
    exact Additive.toMul.injective hy.symm
  · refine ⟨(⟨4, four_mem_fundamentalIdeal_sq⟩ : ↥(fundamentalIdeal ℝ ^ 2)), ?_⟩
    rw [cliffordHomI2Bar_mk, cliffordHomI2_apply,
      WittRing.cliffordInvariant_eq_ite_signature]
    have hsig : WittRing.signature (4 : WittRing ℝ) = 4 := by
      simpa using map_ofNat WittRing.signature 4
    rw [hsig]
    norm_num
    rw [BrauerGroup.quaternionClass_neg_one_neg_one_real]
    exact Additive.toMul.injective hy.symm

/-- **The isomorphism `I(ℝ)²/I(ℝ)³ ≃+ Additive (BrauerGroup ℝ)`**: over `ℝ`, the Clifford
homomorphism identifies `I(ℝ)²/I(ℝ)³` with the Brauer group of `ℝ`. -/
noncomputable def cliffordHomI2BarEquivReal :
    (↥(fundamentalIdeal ℝ ^ 2) ⧸ fundamentalI3InI2 ℝ) ≃+ Additive (BrauerGroup.{0, 0} ℝ) :=
  AddEquiv.ofBijective (cliffordHomI2Bar (K := ℝ))
    ⟨cliffordHomI2Bar_injective, cliffordHomI2Bar_surjective_real⟩

/-- `cliffordHomI2BarEquivReal` agrees with `cliffordHomI2Bar` on every class. -/
@[simp]
theorem cliffordHomI2BarEquivReal_apply
    (q : ↥(fundamentalIdeal ℝ ^ 2) ⧸ fundamentalI3InI2 ℝ) :
    cliffordHomI2BarEquivReal q = cliffordHomI2Bar q := (rfl)

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
  · rw [← RegularFormClass.sigPos_add_sigNeg_eq_rank, sigPos_formClass, sigNeg_formClass,
      RegularFormClass.discr_eq_sigNeg_nsmul, sigNeg_formClass, sigPos_realSignatureForm,
      sigNeg_realSignatureForm]
    norm_num
    rw [succ_nsmul, succ_nsmul, one_nsmul,
      BrauerGroup.quaternionClassOnSquareClasses_add_right,
      BrauerGroup.quaternionClassOnSquareClasses_add_right,
      BrauerGroup.quaternionClassOnSquareClasses_squareClass, ← pow_two,
      BrauerGroup.quaternionClass_sq, one_mul,
      BrauerGroup.quaternionClass_neg_one_neg_one_real]

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
