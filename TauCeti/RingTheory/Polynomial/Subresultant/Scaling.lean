/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Sturm.Sequence
public import TauCeti.RingTheory.Polynomial.Subresultant.Euclidean

/-!
# Exact scaling along the signed remainder sequence

The structure theorem identifies subresultants with signed remainders up to nonzero scalars.
Here `Polynomial.sturmSubresultantFactor` records the scalars explicitly as products of signs
and powers of leading coefficients. For consecutive entries `a, b, c` of the signed remainder
sequence, one reduction contributes
`(-1) ^ ((deg a - j + 1) * (deg b - j)) * lc(b) ^ (deg a - deg c)`.
The first step uses a supplied formal bound `m ≥ deg p` in place of `deg p`.
Multiplying these factors transports every subresultant below the next remainder degree.

`Polynomial.subresultant_eq_sturmSubresultantFactor_mul` gives this exact transport.
The two endpoint formulas give the precise multiples of a remainder at the upper and lower
ends of its degree gap. These identities retain the determinant normalization, rather than
normalizing every remainder to be monic. They work in arbitrary characteristic, including two.

## References

S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Chapter 8 (subresultants and signed remainder sequences).
-/

public section

namespace Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- The product of the first `i` Euclidean scaling factors for the subresultant of index `j`.
The first step uses the formal left bound `m`; later steps use actual degrees.
Missing entries of the signed remainder sequence are read as zero. The transport theorem uses
this product only while the required entries exist and `j` is below the next entry's degree. -/
noncomputable def sturmSubresultantFactor (p q : K[X]) (m j i : ℕ) : K :=
  ∏ k ∈ Finset.range i,
    (-1) ^ (((if k = 0 then m else ((sturmSeq p q)[k]?.getD 0).natDegree) - j + 1) *
      (((sturmSeq p q)[k + 1]?.getD 0).natDegree - j)) *
    ((sturmSeq p q)[k + 1]?.getD 0).leadingCoeff ^
      ((if k = 0 then m else ((sturmSeq p q)[k]?.getD 0).natDegree) -
        ((sturmSeq p q)[k + 2]?.getD 0).natDegree)

/-- The scaling factor is the indicated finite product of signs and leading-coefficient powers. -/
theorem sturmSubresultantFactor_def (p q : K[X]) (m j i : ℕ) :
    p.sturmSubresultantFactor q m j i =
      ∏ k ∈ Finset.range i,
        (-1) ^ (((if k = 0 then m else ((sturmSeq p q)[k]?.getD 0).natDegree) - j + 1) *
          (((sturmSeq p q)[k + 1]?.getD 0).natDegree - j)) *
        ((sturmSeq p q)[k + 1]?.getD 0).leadingCoeff ^
          ((if k = 0 then m else ((sturmSeq p q)[k]?.getD 0).natDegree) -
            ((sturmSeq p q)[k + 2]?.getD 0).natDegree) := (rfl)

@[simp]
theorem sturmSubresultantFactor_zero (p q : K[X]) (m j : ℕ) :
    p.sturmSubresultantFactor q m j 0 = 1 := by
  simp [sturmSubresultantFactor_def]

/-- Extending the prefix multiplies its factor by the factor of the next Euclidean step. -/
@[simp]
theorem sturmSubresultantFactor_succ (p q : K[X]) (m j i : ℕ) :
    p.sturmSubresultantFactor q m j (i + 1) =
      p.sturmSubresultantFactor q m j i *
        ((-1) ^ (((if i = 0 then m else ((sturmSeq p q)[i]?.getD 0).natDegree) - j + 1) *
          (((sturmSeq p q)[i + 1]?.getD 0).natDegree - j)) *
        ((sturmSeq p q)[i + 1]?.getD 0).leadingCoeff ^
          ((if i = 0 then m else ((sturmSeq p q)[i]?.getD 0).natDegree) -
            ((sturmSeq p q)[i + 2]?.getD 0).natDegree)) := by
  simp only [sturmSubresultantFactor_def, Finset.prod_range_succ]

/-- All scaling factors are nonzero as long as the prefix ends at an actual sequence entry. -/
theorem sturmSubresultantFactor_ne_zero {p q a : K[X]} {i : ℕ}
    (ha : (sturmSeq p q)[i]? = some a) (m j : ℕ) :
    p.sturmSubresultantFactor q m j i ≠ 0 := by
  rw [sturmSubresultantFactor_def]
  refine Finset.prod_ne_zero_iff.mpr fun k hk ↦ mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  have hi := (List.getElem?_eq_some_iff.mp ha).1
  have hk' : k + 1 < (sturmSeq p q).length := by
    have := Finset.mem_range.mp hk
    omega
  rw [List.getElem?_eq_getElem hk', Option.getD_some]
  exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr
    (ne_zero_of_mem_sturmSeq (List.getElem_mem hk')))

private theorem natDegree_le_sturmBound {p q a : K[X]} {m i : ℕ}
    (hp : p.natDegree ≤ m) (ha : (sturmSeq p q)[i]? = some a) :
    a.natDegree ≤ if i = 0 then m else a.natDegree := by
  split_ifs with hi
  · subst i
    have hp0 : p ≠ 0 := by rintro rfl; simp at ha
    have ha' : a = p := by simpa [sturmSeq_cons hp0] using ha.symm
    simpa [ha'] using hp
  · exact le_rfl

private theorem next_natDegree_le_sturmBound {p q a b : K[X]} {m i : ℕ}
    (hq : i = 0 → q.natDegree ≤ m) (ha : (sturmSeq p q)[i]? = some a)
    (hb : (sturmSeq p q)[i + 1]? = some b) :
    b.natDegree ≤ if i = 0 then m else a.natDegree := by
  rcases i with _ | i
  · have hp0 : p ≠ 0 := by rintro rfl; simp at ha
    have hb' : b = q := by
      have h := congrArg (fun o ↦ o.getD 0) hb
      simpa only [getD_getElem?_sturmSeq hp0, Option.getD_some] using h.symm
    simpa [hb'] using hq rfl
  · simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using
      (natDegree_lt_of_getElem?_sturmSeq ha hb).le

/-- **Exact transport of subresultants along signed remainders.** For the consecutive entries
`a, b` at positions `i, i + 1`, every subresultant below `deg b` is the corresponding
subresultant of `(a, b)` multiplied by the explicit product of the preceding step factors.
The first left bound is `m`; subsequent left bounds are actual degrees.
The first two input degrees need not be ordered. -/
theorem subresultant_eq_sturmSubresultantFactor_mul {p q a b : K[X]} {m i j : ℕ}
    (hp : p.natDegree ≤ m)
    (ha : (sturmSeq p q)[i]? = some a) (hb : (sturmSeq p q)[i + 1]? = some b)
    (hj : j < b.natDegree) :
    subresultant p q m q.natDegree j =
      C (p.sturmSubresultantFactor q m j i) *
        subresultant a b (if i = 0 then m else a.natDegree) b.natDegree j := by
  induction i generalizing a b with
  | zero =>
    have hp0 : p ≠ 0 := by rintro rfl; simp at ha
    have ha' : a = p := by simpa [sturmSeq_cons hp0] using ha.symm
    have hb' : b = q := by
      have h := congrArg (fun o ↦ o.getD 0) hb
      simpa only [getD_getElem?_sturmSeq hp0, Option.getD_some] using h.symm
    simp [ha', hb']
  | succ i ih =>
    -- Recover the preceding entry and append its Euclidean step to the prefix identity.
    obtain ⟨c, hc⟩ : ∃ c, (sturmSeq p q)[i]? = some c := by
      have hi := (List.getElem?_eq_some_iff.mp ha).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hab := natDegree_lt_of_getElem?_sturmSeq ha hb
    have hrec : b = -(c % a) := by
      rw [eq_neg_mod_of_getElem?_sturmSeq hc ha hb, neg_mod]
    have hbc : b.natDegree ≤ (if i = 0 then m else c.natDegree) := by
      rw [hrec, natDegree_neg, mod_def]
      exact natDegree_modByMonic_le_left.trans (natDegree_le_sturmBound hp hc)
    have hstep := subresultant_eq_C_mul_subresultant_neg_mod
      (p := c) (q := a) (r := b.natDegree) (natDegree_le_sturmBound hp hc)
      (by rw [hrec, natDegree_neg]) hbc (by omega : j < min b.natDegree a.natDegree)
    rw [← hrec] at hstep
    rw [ih hc ha (by omega), hstep, ← mul_assoc, ← C_mul,
      sturmSubresultantFactor_succ, hc, ha, hb]
    simp only [Option.getD_some, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      ↓reduceIte]

/-- **The upper end of a degree gap, with its exact scalar.** If `a, b, c` are consecutive
signed remainders, the subresultant at `deg b - 1` is the displayed nonzero scalar multiple
of `c`. Only the initial pair additionally requires `deg q ≤ m`. -/
theorem subresultant_natDegree_sub_one_eq_sturmSubresultantFactor_mul
    {p q a b c : K[X]} {m i : ℕ} (hp : p.natDegree ≤ m) (hq : i = 0 → q.natDegree ≤ m)
    (ha : (sturmSeq p q)[i]? = some a) (hb : (sturmSeq p q)[i + 1]? = some b)
    (hc : (sturmSeq p q)[i + 2]? = some c) :
    subresultant p q m q.natDegree (b.natDegree - 1) =
      C (-(p.sturmSubresultantFactor q m (b.natDegree - 1) i *
        (-b.leadingCoeff) ^ ((if i = 0 then m else a.natDegree) + 1 - b.natDegree))) * c := by
  have hba := next_natDegree_le_sturmBound hq ha hb
  have hcb := natDegree_lt_of_getElem?_sturmSeq hb hc
  have hrec : c = -(a % b) := by
    rw [eq_neg_mod_of_getElem?_sturmSeq ha hb hc, neg_mod]
  rw [subresultant_eq_sturmSubresultantFactor_mul hp ha hb (by omega),
    subresultant_natDegree_sub_one (natDegree_le_sturmBound hp ha) (by omega) hba, hrec]
  simp [mul_assoc]

/-- **The lower end of a degree gap, with its exact scalar.** For three consecutive signed
remainders, the subresultant at `deg c` is the displayed multiple of `c`. The power of
`-lc(c)` records the size of the gap from `deg b` to `deg c`. Only the initial pair
additionally requires `deg q ≤ m`. -/
theorem subresultant_natDegree_eq_sturmSubresultantFactor_mul
    {p q a b c : K[X]} {m i : ℕ} (hp : p.natDegree ≤ m) (hq : i = 0 → q.natDegree ≤ m)
    (ha : (sturmSeq p q)[i]? = some a) (hb : (sturmSeq p q)[i + 1]? = some b)
    (hc : (sturmSeq p q)[i + 2]? = some c) :
    subresultant p q m q.natDegree c.natDegree =
      C (-(p.sturmSubresultantFactor q m c.natDegree i *
        ((-1) ^ (((if i = 0 then m else a.natDegree) - c.natDegree) * (b.natDegree - c.natDegree)) *
          b.leadingCoeff ^ ((if i = 0 then m else a.natDegree) - c.natDegree) *
          (-c.leadingCoeff) ^ (b.natDegree - c.natDegree - 1)))) * c := by
  have hba := next_natDegree_le_sturmBound hq ha hb
  have hcb := natDegree_lt_of_getElem?_sturmSeq hb hc
  have hrec : a % b = -c := by
    rw [eq_neg_mod_of_getElem?_sturmSeq ha hb hc, neg_mod, neg_neg]
  rw [subresultant_eq_sturmSubresultantFactor_mul hp ha hb hcb,
    subresultant_eq_C_mul_mod (natDegree_le_sturmBound hp ha)
      (by rw [hrec, natDegree_neg]) hcb (by omega),
    hrec, coeff_neg, coeff_natDegree]
  simp [mul_assoc]

/-- **Structure theorem for subresultants**, degree gap. For consecutive entries `s, t` of the
signed remainder sequence of `p` and `q` after the first, the subresultants of `p` and `q` at
the indices strictly between `deg t` and `deg s - 1` vanish. -/
theorem subresultant_eq_zero_of_getElem?_sturmSeq
    {p q s t : K[X]} {m i j : ℕ} (hp : p.natDegree ≤ m)
    (hs : (sturmSeq p q)[i + 1]? = some s) (ht : (sturmSeq p q)[i + 2]? = some t)
    (htj : t.natDegree < j) (hjs : j + 1 < s.natDegree) :
    subresultant p q m q.natDegree j = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, (sturmSeq p q)[i]? = some a := by
    have hi := (List.getElem?_eq_some_iff.mp hs).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hrec : t = -(a % s) := by
    rw [eq_neg_mod_of_getElem?_sturmSeq ha hs ht, neg_mod]
  rw [hrec, natDegree_neg] at htj
  rw [subresultant_eq_sturmSubresultantFactor_mul hp ha hs (by omega),
    subresultant_eq_zero_of_degree_mod_lt (natDegree_le_sturmBound hp ha)
      ((degree_le_natDegree).trans_lt (by exact_mod_cast htj)) hjs, mul_zero]

end Polynomial
