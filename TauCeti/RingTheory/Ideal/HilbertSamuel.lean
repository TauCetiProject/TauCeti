/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Polynomial.HilbertPoly
import TauCeti.RingTheory.Length.SMulTop
import TauCeti.RingTheory.PowerSeries.Basic

/-!
# The Hilbert–Samuel series of an ideal-adic filtration

For a finitely generated ideal `I` with `M / IM` of finite length, the series of cumulative
lengths `ℓ(M / I ^ (n + 1) M)` becomes the series of graded lengths after multiplication by
`1 - X` (`Ideal.hilbertSamuelSeries_mul_one_sub_X`), with the inverse formula
`Ideal.hilbertSamuelSeries_eq_adicGradedLengthSeries_mul_invOneSubPow`. This uses additivity of
module length and `PowerSeries.mk_mul_one_sub_X_eq`.

Under the same finiteness hypotheses, `Ideal.eventually_eval_eq_length_iff_eq_hilbertPoly`
reduces Hilbert–Samuel polynomiality to rationality of the graded series. If the latter has
numerator `q` and denominator `(1 - X) ^ e`, Mathlib's `Polynomial.hilbertPoly q (e + 1)`
gives the unique eventual polynomial for the cumulative lengths.

## References

* The Stacks Project, [Tag 00K1](https://stacks.math.columbia.edu/tag/00K1) and
  [Tag 00K8](https://stacks.math.columbia.edu/tag/00K8).
-/

public section

open Filter PowerSeries
open scoped Polynomial

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [Semiring S]

/-- The series whose coefficient at `n` is the length of `M / I ^ (n + 1) M`.
As for `ENat.toNat`, infinite lengths contribute zero. -/
noncomputable def hilbertSamuelSeries : PowerSeries S :=
  PowerSeries.mk fun n ↦ (Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).toNat

/-- The degree-`n` coefficient of the Hilbert–Samuel series is the corresponding quotient
length, with an infinite length contributing zero. -/
@[simp] theorem coeff_hilbertSamuelSeries (n : ℕ) :
    coeff n (I.hilbertSamuelSeries M S) =
      (Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).toNat := coeff_mk _ _

/-- The series of lengths of the graded pieces `I ^ n M / I ^ (n + 1) M` of the `I`-adic
filtration. Infinite lengths contribute zero. -/
noncomputable def adicGradedLengthSeries : PowerSeries S :=
  PowerSeries.mk fun n ↦ (Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
    (I • ⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))))).toNat

/-- The degree-`n` coefficient of the graded length series is the length of the corresponding
graded piece, with an infinite length contributing zero. -/
@[simp] theorem coeff_adicGradedLengthSeries (n : ℕ) :
    coeff n (I.adicGradedLengthSeries M S) =
      (Module.length R (↥(I ^ n • (⊤ : Submodule R M)) ⧸
        (I • ⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))))).toNat := coeff_mk _ _

variable {M} (S : Type*) [CommRing S]

/-- Multiplication by `1 - X` converts the cumulative Hilbert–Samuel length series into the
graded length series when `I` is finitely generated and `M / IM` has finite length. -/
theorem hilbertSamuelSeries_mul_one_sub_X (hI : I.FG)
    (hM : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M)))) :
    I.hilbertSamuelSeries M S * (1 - X) = I.adicGradedLengthSeries M S := by
  let a (d : ℤ) : S :=
    (Module.length R (M ⧸ (I ^ (d + 1).toNat • (⊤ : Submodule R M)))).toNat
  let c (d : ℤ) : S := if 0 ≤ d then coeff d.toNat (I.adicGradedLengthSeries M S) else 0
  have ha : mk (fun n : ℕ ↦ a n) = I.hilbertSamuelSeries M S := by
    ext n
    simp [a]
  have hc : mk (fun n : ℕ ↦ c n) = I.adicGradedLengthSeries M S := by
    ext n
    simp [c]
  have hstep (d : ℤ) : 0 + a (d + 1) = a d + c (d + 1) := by
    by_cases hd : 0 ≤ d + 1
    · let n := (d + 1).toNat
      have hs : (d + 1 + 1).toNat = n + 1 := by omega
      have hgraded := Module.length_ne_top_iff.mpr
        (I.isFiniteLength_smul_top_quotient_smul_top (J := I ^ n) hI.pow hM)
      have htrunc := Module.length_ne_top_iff.mpr
        (I.isFiniteLength_quotient_pow_smul_top hI hM n)
      simp only [a, c, ite_eq_left hd, zero_add, coeff_adicGradedLengthSeries]
      rw [hs, I.length_quotient_pow_succ_smul_top, ENat.toNat_add hgraded htrunc, Nat.cast_add,
        add_comm]
    · have h₀ : (d + 1).toNat = 0 := by omega
      have h₁ : (d + 1 + 1).toNat = 0 := by omega
      simp only [a, c, ite_eq_right hd, zero_add, add_zero]
      rw [h₀, h₁]
  have hb : (mk (fun _ ↦ 0) : PowerSeries S) = 0 := by
    ext n
    rw [coeff_mk, map_zero]
  have hzero : a (0 - 1) = 0 := by simp [a]
  simpa only [zero_add, ha, hb, hc, mul_zero, sub_zero] using
    (mk_mul_one_sub_X_eq (d₀ := 0) (b := fun _ ↦ 0) hstep hzero rfl)

/-- For finitely generated `I` with `M / IM` of finite length, the cumulative length series
is the adic graded length series divided by `1 - X`. -/
theorem hilbertSamuelSeries_eq_adicGradedLengthSeries_mul_invOneSubPow (hI : I.FG)
    (hM : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M)))) :
    I.hilbertSamuelSeries M S = I.adicGradedLengthSeries M S * invOneSubPow S 1 := by
  have hinv : (invOneSubPow S 1).inv = 1 - X := by
    simpa only [pow_one] using invOneSubPow_inv_eq_one_sub_pow S 1
  rw [← I.hilbertSamuelSeries_mul_one_sub_X S hI hM, mul_assoc, ← hinv, Units.inv_val, mul_one]

variable {S} in
/-- For finitely generated `I` with `M / IM` of finite length, if the graded length series
has numerator `q` and denominator `(1 - X) ^ e`, the Hilbert–Samuel series has the same
numerator and one extra factor of `1 - X` in its denominator. -/
theorem hilbertSamuelSeries_eq_mul_invOneSubPow (hI : I.FG)
    (hM : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M))))
    {q : S[X]} {e : ℕ} (h : I.adicGradedLengthSeries M S * (1 - X) ^ e = q.toPowerSeries) :
    I.hilbertSamuelSeries M S = q * invOneSubPow S (e + 1) := by
  have hmul : I.hilbertSamuelSeries M S * (1 - X) ^ (e + 1) = q.toPowerSeries := by
    rw [pow_succ', ← mul_assoc, I.hilbertSamuelSeries_mul_one_sub_X S hI hM, h]
  rw [← hmul, mul_assoc, ← invOneSubPow_inv_eq_one_sub_pow, Units.inv_val, mul_one]

/-- For finitely generated `I` with `M / IM` of finite length, if the graded length series
has numerator `q` and denominator `(1 - X) ^ e`, then `q.hilbertPoly (e + 1)` eventually
gives the lengths of `M / I ^ (n + 1) M`. -/
theorem eventually_eval_hilbertPoly_eq_of_adicGradedLengthSeries (hI : I.FG)
    (hM : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M))))
    {q : ℚ[X]} {e : ℕ} (h : I.adicGradedLengthSeries M ℚ * (1 - X) ^ e = q.toPowerSeries) :
    ∀ᶠ n : ℕ in atTop, (q.hilbertPoly (e + 1)).eval (n : ℚ) =
      (Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).toNat := by
  filter_upwards [eventually_gt_atTop q.natDegree] with n hn
  rw [← Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn,
    ← I.hilbertSamuelSeries_eq_mul_invOneSubPow hI hM h,
    coeff_hilbertSamuelSeries]

/-- For finitely generated `I` with `M / IM` of finite length, if the graded length series
has numerator `q` and denominator `(1 - X) ^ e`, then a polynomial agrees eventually with
the Hilbert–Samuel lengths exactly when it is `q.hilbertPoly (e + 1)`. -/
theorem eventually_eval_eq_length_iff_eq_hilbertPoly (hI : I.FG)
    (hM : IsFiniteLength R (M ⧸ (I • (⊤ : Submodule R M))))
    {q : ℚ[X]} {e : ℕ} (h : I.adicGradedLengthSeries M ℚ * (1 - X) ^ e = q.toPowerSeries)
    {P : ℚ[X]} :
    (∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) =
      (Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).toNat) ↔
      P = q.hilbertPoly (e + 1) := by
  refine ⟨fun hP ↦ ?_, fun hP ↦ hP ▸
    I.eventually_eval_hilbertPoly_eq_of_adicGradedLengthSeries hI hM h⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  refine Polynomial.eq_hilbertPoly_of_forall_coeff_eq_eval N fun n hn ↦ ?_
  rw [← I.hilbertSamuelSeries_eq_mul_invOneSubPow hI hM h, coeff_hilbertSamuelSeries]
  exact (hN n hn.le).symm

end Ideal
