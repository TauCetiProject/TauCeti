/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Straightening
public import TauCeti.RingTheory.DividedPowers.Commutation
public import TauCeti.RingTheory.Binomial
import Mathlib.Tactic.NoncommRing

/-!
# Integral multiplication of rank-one Kostant monomials

For an associative rational algebra with an `sl₂` triple `(H,E,F)`, this file defines
`orderedKostantMonomial H E F a b c` as `F⁽ᵃ⁾ (H choose b) E⁽ᶜ⁾` and computes the product
of two such monomials as a finite integer linear combination of ordered monomials.
No independence or faithfulness of the triple is required.

`orderedKostantMonomial_mul` gives the multiplication table explicitly. Its outer index is the
rank-one straightening index. Three antidiagonals expand the translated Cartan factors, and
two more linearize their products. Negative integer binomial coefficients are retained: the
coefficients need not be positive. Although divided powers are evaluated in a rational algebra,
the table has only integer coefficients and can therefore be specialized on an integral form
without performing factorial division in the target ring.

The collection argument, relocated from `TauCeti.Algebra.Lie.Sl2.Kostant.Span`, straightens
`E⁽ᶜ⁾ F⁽ᵈ⁾`, moves the Cartan binomials to the middle, and expands their translates using
`Ring.add_choose_eq`. The span module uses the resulting table to prove multiplicative closure.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Sl2

open Finset Associative

attribute [local instance] TauCeti.moduleNNRat

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- An ordered rank-one Kostant monomial `F⁽ᵃ⁾ (H choose b) E⁽ᶜ⁾`. -/
noncomputable def orderedKostantMonomial (H E F : A) (a b c : ℕ) : A :=
  dividedPower a F * Ring.choose H b * dividedPower c E

/-- An ordered monomial is the product of its lowering, Cartan and raising factors. -/
theorem orderedKostantMonomial_def (H E F : A) (a b c : ℕ) :
    orderedKostantMonomial H E F a b c =
      dividedPower a F * Ring.choose H b * dividedPower c E :=
  (rfl)

theorem orderedKostantMonomial_zero_zero_zero (H E F : A) :
    orderedKostantMonomial H E F 0 0 0 = 1 := by
  simp [orderedKostantMonomial]

@[simp]
theorem orderedKostantMonomial_left (H E F : A) (n : ℕ) :
    orderedKostantMonomial H E F n 0 0 = dividedPower n F := by
  simp [orderedKostantMonomial]

@[simp]
theorem orderedKostantMonomial_middle (H E F : A) (n : ℕ) :
    orderedKostantMonomial H E F 0 n 0 = Ring.choose H n := by
  simp [orderedKostantMonomial]

@[simp]
theorem orderedKostantMonomial_right (H E F : A) (n : ℕ) :
    orderedKostantMonomial H E F 0 0 n = dividedPower n E := by
  simp [orderedKostantMonomial]

private theorem collect {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) (a b c d e f : ℕ) :
    orderedKostantMonomial H E F a b c * orderedKostantMonomial H E F d e f =
      ∑ k ∈ range (min c d + 1),
        (Nat.choose (a + (d - k)) a * Nat.choose ((c - k) + f) (c - k)) •
          (dividedPower (a + (d - k)) F *
            (Ring.choose (H + ((-2 * (d - k : ℕ) : ℤ) : A)) b *
              Ring.choose (H + ((((2 * k : ℕ) : ℤ) - (c + d : ℕ) : ℤ) : A)) k *
              Ring.choose (H + ((-2 * (c - k : ℕ) : ℤ) : A)) e) *
            dividedPower ((c - k) + f) E) := by
  have hhf' : H * F = F * (H + (-2 : A)) := by
    simpa using add_intCast_mul_eq_mul_add_intCast (x := H) (y := F) (c := -2)
      (by simpa using hhf) 0
  have hhe' : H * E = E * (H + (2 : A)) := by
    simpa using add_intCast_mul_eq_mul_add_intCast (x := H) (y := E) (c := 2)
      (by simpa using hhe) 0
  -- Isolate the middle raising/lowering product and apply rank-one straightening.
  have hfactor :
      orderedKostantMonomial H E F a b c * orderedKostantMonomial H E F d e f =
        dividedPower a F * Ring.choose H b *
          (dividedPower c E * dividedPower d F) * Ring.choose H e * dividedPower f E := by
    simp only [orderedKostantMonomial, mul_assoc]
  rw [hfactor, dividedPower_e_mul_dividedPower_f hef hhe hhf,
    mul_sum, sum_mul, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  -- Move the two outer Cartan factors past the divided powers to collect them in the middle.
  have hmoveF := ringChoose_mul_dividedPower b hhf'
    ((Nat.cast_commute 2 F).neg_left) (d - k)
  have hmoveE := dividedPower_mul_ringChoose e hhe' (Nat.cast_commute 2 E) (c - k)
  have hnormal :
      dividedPower a F * Ring.choose H b *
          (dividedPower (d - k) F *
            Ring.choose (H - ((c + d : ℕ) : A) + ((2 * k : ℕ) : A)) k *
            dividedPower (c - k) E) * Ring.choose H e * dividedPower f E =
        (dividedPower a F * dividedPower (d - k) F) *
          (Ring.choose (H + (d - k) • (-2 : A)) b *
            Ring.choose (H - ((c + d : ℕ) : A) + ((2 * k : ℕ) : A)) k *
            Ring.choose (H - (c - k) • (2 : A)) e) *
          (dividedPower (c - k) E * dividedPower f E) := by
    calc
      _ = dividedPower a F * (Ring.choose H b * dividedPower (d - k) F) *
          Ring.choose (H - ((c + d : ℕ) : A) + ((2 * k : ℕ) : A)) k *
          (dividedPower (c - k) E * Ring.choose H e) * dividedPower f E := by
        simp only [mul_assoc]
      _ = _ := by rw [hmoveF, hmoveE]; simp only [mul_assoc]
  -- Put all three shifts in integer-cast form for the later Ring.add_choose_eq expansions.
  have h₁ : H + (d - k) • (-2 : A) = H + ((-2 * (d - k : ℕ) : ℤ) : A) := by
    push_cast
    simp only [nsmul_eq_mul]
    noncomm_ring
  have h₂ : H - ((c + d : ℕ) : A) + ((2 * k : ℕ) : A) =
      H + ((((2 * k : ℕ) : ℤ) - (c + d : ℕ) : ℤ) : A) := by
    push_cast
    noncomm_ring
  have h₃ : H - (c - k) • (2 : A) = H + ((-2 * (c - k : ℕ) : ℤ) : A) := by
    push_cast
    simp only [nsmul_eq_mul]
    noncomm_ring
  -- Merge the lowering and raising divided powers, then collect their scalar coefficients.
  rw [hnormal, mul_dividedPower, mul_dividedPower, h₁, h₂, h₃]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring

/-- The explicit integral multiplication table for ordered rank-one Kostant monomials.
All five inner indices run over finite antidiagonals. The coefficient of each displayed
monomial is an integer, expressed using integer and natural binomial coefficients. No
linear independence of the monomials is assumed. -/
theorem orderedKostantMonomial_mul {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) (a b c d e f : ℕ) :
    orderedKostantMonomial H E F a b c * orderedKostantMonomial H E F d e f =
      ∑ k ∈ range (min c d + 1),
        ∑ p ∈ antidiagonal b, ∑ q ∈ antidiagonal k, ∑ r ∈ antidiagonal e,
          ∑ u ∈ antidiagonal q.1, ∑ v ∈ antidiagonal r.1,
            ((Nat.choose (a + (d - k)) a : ℤ) * Nat.choose ((c - k) + f) (c - k) *
              Ring.choose (-2 * (d - k : ℕ) : ℤ) p.2 *
              Ring.choose (((2 * k : ℕ) : ℤ) - (c + d : ℕ)) q.2 *
              Ring.choose (-2 * (c - k : ℕ) : ℤ) r.2 *
              (Nat.choose p.1 u.2 * Nat.choose (p.1 + u.1) p.1) *
              (Nat.choose (p.1 + u.1) v.2 *
                Nat.choose (p.1 + u.1 + v.1) (p.1 + u.1))) •
              orderedKostantMonomial H E F (a + (d - k)) (p.1 + u.1 + v.1)
                ((c - k) + f) := by
  rw [collect hef hhe hhf]
  refine sum_congr rfl fun k _ => ?_
  -- Expand the translated b-th Cartan binomial along p ∈ antidiagonal b.
  rw [Ring.add_choose_eq b (Int.cast_commute (-2 * (d - k : ℕ)) H).symm]
  simp only [sum_mul, mul_sum, Finset.smul_sum]
  refine sum_congr rfl fun p _ => ?_
  -- Expand the translated k-th Cartan binomial along q ∈ antidiagonal k.
  rw [Ring.add_choose_eq k
    (Int.cast_commute (((2 * k : ℕ) : ℤ) - (c + d : ℕ)) H).symm]
  simp only [sum_mul, mul_sum, Finset.smul_sum]
  refine sum_congr rfl fun q _ => ?_
  -- Expand the translated e-th Cartan binomial along r ∈ antidiagonal e.
  rw [Ring.add_choose_eq e (Int.cast_commute (-2 * (c - k : ℕ)) H).symm]
  simp only [sum_mul, mul_sum, Finset.smul_sum]
  refine sum_congr rfl fun r _ => ?_
  simp only [TauCeti.Ring.choose_intCast]
  have hreorder :
      Ring.choose H p.1 * (↑(Ring.choose (-2 * (d - k : ℕ) : ℤ) p.2) : A) *
          (Ring.choose H q.1 *
            (↑(Ring.choose (((2 * k : ℕ) : ℤ) - (c + d : ℕ)) q.2) : A)) *
          (Ring.choose H r.1 * (↑(Ring.choose (-2 * (c - k : ℕ) : ℤ) r.2) : A)) =
        (Ring.choose (-2 * (d - k : ℕ) : ℤ) p.2 *
          Ring.choose (((2 * k : ℕ) : ℤ) - (c + d : ℕ)) q.2 *
          Ring.choose (-2 * (c - k : ℕ) : ℤ) r.2 : ℤ) •
          (Ring.choose H p.1 * Ring.choose H q.1 * Ring.choose H r.1) := by
    simp only [← zsmul_eq_mul', smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1; ring
  -- Linearize the p.1/q.1 Cartan product along u ∈ antidiagonal q.1.
  rw [hreorder, ringChoose_mul_ringChoose, sum_mul]
  simp only [smul_mul_assoc, Finset.smul_sum, mul_sum, sum_mul]
  refine sum_congr rfl fun u _ => ?_
  -- Linearize the remaining Cartan product along v ∈ antidiagonal r.1.
  rw [ringChoose_mul_ringChoose]
  simp only [Finset.smul_sum, mul_sum, sum_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, orderedKostantMonomial, Nat.cast_mul]
  refine sum_congr rfl fun v _ => ?_
  simp only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul, mul_assoc]

end TauCeti.Sl2
