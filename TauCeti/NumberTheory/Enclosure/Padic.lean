/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Rational-centred enclosures of `p`-adic numbers

A certified `p`-adic computation records a `p`-adic number `x` by a rational centre `c` and an
integer absolute precision `N` with `‖x - c‖ ≤ p ^ (-N)`, that is, by a rational-centred closed
ball of radius `p ^ (-N)` containing `x`. Every check on the data `(c, N)` of an enclosure, such as
computing its normalized record, is a comparison of rational numbers or of `p`-adic valuations of
rational numbers; proving that the ball contains `x` in the first place is a statement about `x`
itself.

Many centres describe the same ball. This file attaches to an enclosure `(c, N)` its *canonical
normalized record* `(N, v, s)`:

* if `c = 0`, then `(v, s) = (N, 0)`;
* otherwise `v = min (v_p(c), N)`; if `v = N` then `s = 0`, and if `v < N` then `s` is the residue
  of `c · p ^ (-v)` in `[1, p ^ (N - v))`, which is prime to `p`.

The zero test comes first: Mathlib's totalized `padicValRat p 0 = 0` is never read as the
valuation of `0`. The record denotes the same ball, with centre `p ^ v * s`
(`TauCeti.PadicEnclosure.closedBall_normalizedCenter`), and it is canonical: two enclosures of the
same precision have the same record exactly when they denote the same ball
(`TauCeti.PadicEnclosure.normalizedVal_eq_and_normalizedResidue_eq_iff`).

A zero-centred enclosure does not certify vanishing: at `p = 3`, the enclosure `(0, 2)` encloses
`9`.

## Main definitions

* `TauCeti.PadicEnclosure p x`: a rational centre and an integer precision whose closed ball
  contains `x`.
* `TauCeti.PadicEnclosure.normalizedVal`, `TauCeti.PadicEnclosure.normalizedResidue`: the
  components `v` and `s` of the canonical normalized record.
* `TauCeti.PadicEnclosure.normalizedCenter`: the centre `p ^ v * s` of the normalized record.
* `TauCeti.PadicEnclosure.normalize`: the enclosure of `x` given by the normalized record.

## Main results

* `TauCeti.PadicEnclosure.zpow_neg_normalizedVal`: `p ^ (-v) = max (‖c‖, p ^ (-N))`.
* `TauCeti.PadicEnclosure.normalizedResidue_lt`, `TauCeti.PadicEnclosure.coprime_normalizedResidue`:
  the residue lies in `[0, p ^ (N - v))` and is prime to `p` when `v < N`.
* `TauCeti.PadicEnclosure.normalizedResidue_eq_of_norm_sub_le`: the residue is the unique
  `s < p ^ (N - v)` with `‖c - p ^ v * s‖ ≤ p ^ (-N)`.
* `TauCeti.PadicEnclosure.closedBall_normalizedCenter`: the normalized record denotes the ball of
  the enclosure.
* `TauCeti.PadicEnclosure.normalizedVal_eq_and_normalizedResidue_eq_iff`: canonicity of the
  record.
* `TauCeti.PadicEnclosure.normalize_normalize`: normalization is idempotent.

## References

* B. M. M. de Weger, *Algorithms for Diophantine equations*, CWI Tract 65, 1989, §2.5, printed
  pp. 33–34.
* J. R. Doyle, D. Krumm, *Computing algebraic numbers of bounded height*, arXiv:1111.4963, §4
  (before §4.1).
-/

public section

namespace TauCeti

/-- A *`p`-adic enclosure* of `x : ℚ_[p]`: a rational centre `c` and an integer absolute precision
`N` with `‖x - c‖ ≤ p ^ (-N)`. -/
@[ext]
structure PadicEnclosure (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) where
  /-- The rational centre of the ball. -/
  center : ℚ
  /-- The absolute precision: the ball has radius `p ^ (-prec)`. -/
  prec : ℤ
  /-- The enclosed number lies in the closed ball of radius `p ^ (-prec)` about the centre. -/
  norm_sub_le : ‖x - center‖ ≤ (p : ℝ) ^ (-prec)

namespace PadicEnclosure

variable {p : ℕ} [hp : Fact p.Prime] {x : ℚ_[p]}

/-- The enclosed number lies in the closed ball of radius `p ^ (-N)` about the centre. -/
theorem mem_closedBall (E : PadicEnclosure p x) :
    x ∈ Metric.closedBall (E.center : ℚ_[p]) ((p : ℝ) ^ (-E.prec)) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact E.norm_sub_le

/-- The exact enclosure `(q, N)` of a rational number `q`, at any precision `N`. -/
def ofRat (q : ℚ) (N : ℤ) : PadicEnclosure p q where
  center := q
  prec := N
  norm_sub_le := by
    rw [sub_self, norm_zero]
    exact zpow_nonneg (Nat.cast_nonneg p) _

@[simp]
theorem ofRat_center (q : ℚ) (N : ℤ) : (ofRat (p := p) q N).center = q :=
  (rfl)

@[simp]
theorem ofRat_prec (q : ℚ) (N : ℤ) : (ofRat (p := p) q N).prec = N :=
  (rfl)

/-- Lowering the precision of an enclosure gives an enclosure of the same number. -/
def ofLE (E : PadicEnclosure p x) (N : ℤ) (h : N ≤ E.prec) : PadicEnclosure p x where
  center := E.center
  prec := N
  norm_sub_le := E.norm_sub_le.trans
    (zpow_le_zpow_right₀ (Nat.one_lt_cast.mpr hp.out.one_lt).le (neg_le_neg h))

@[simp]
theorem ofLE_center (E : PadicEnclosure p x) (N : ℤ) (h : N ≤ E.prec) :
    (E.ofLE N h).center = E.center :=
  (rfl)

@[simp]
theorem ofLE_prec (E : PadicEnclosure p x) (N : ℤ) (h : N ≤ E.prec) : (E.ofLE N h).prec = N :=
  (rfl)

/-- Any rational point of the ball of an enclosure is again a centre for an enclosure of the same
number at the same precision. -/
def ofNormSubLe (E : PadicEnclosure p x) (c : ℚ)
    (h : ‖(E.center : ℚ_[p]) - c‖ ≤ (p : ℝ) ^ (-E.prec)) : PadicEnclosure p x where
  center := c
  prec := E.prec
  norm_sub_le := (IsUltrametricDist.norm_sub_le_max_norm_sub _ (E.center : ℚ_[p]) _).trans
    (max_le E.norm_sub_le (by rwa [norm_sub_rev]))

@[simp]
theorem ofNormSubLe_center (E : PadicEnclosure p x) (c : ℚ)
    (h : ‖(E.center : ℚ_[p]) - c‖ ≤ (p : ℝ) ^ (-E.prec)) : (E.ofNormSubLe c h).center = c :=
  (rfl)

@[simp]
theorem ofNormSubLe_prec (E : PadicEnclosure p x) (c : ℚ)
    (h : ‖(E.center : ℚ_[p]) - c‖ ≤ (p : ℝ) ^ (-E.prec)) :
    (E.ofNormSubLe c h).prec = E.prec :=
  (rfl)

/-! ### The canonical normalized record -/

/-- The valuation component `v` of the canonical normalized record of `(c, N)`: it is `N` when
`c = 0` and `min (v_p(c), N)` otherwise. -/
noncomputable def normalizedVal (E : PadicEnclosure p x) : ℤ :=
  if E.center = 0 then E.prec else min (padicValRat p E.center) E.prec

@[simp]
theorem normalizedVal_of_center_eq_zero (E : PadicEnclosure p x) (h : E.center = 0) :
    E.normalizedVal = E.prec := by
  simp [normalizedVal, h]

theorem normalizedVal_of_center_ne_zero (E : PadicEnclosure p x) (h : E.center ≠ 0) :
    E.normalizedVal = min (padicValRat p E.center) E.prec := by
  simp [normalizedVal, h]

theorem normalizedVal_le_prec (E : PadicEnclosure p x) : E.normalizedVal ≤ E.prec := by
  by_cases h : E.center = 0
  · rw [E.normalizedVal_of_center_eq_zero h]
  · rw [E.normalizedVal_of_center_ne_zero h]
    exact min_le_right _ _

/-- The valuation component is smaller than the precision exactly when the centre is nonzero and
its valuation is smaller than the precision. -/
theorem normalizedVal_lt_prec_iff (E : PadicEnclosure p x) :
    E.normalizedVal < E.prec ↔ E.center ≠ 0 ∧ padicValRat p E.center < E.prec := by
  by_cases h : E.center = 0
  · simp [h]
  · simp [E.normalizedVal_of_center_ne_zero h, h]

/-- Below the precision, the valuation component is the valuation of the centre. -/
theorem normalizedVal_eq_padicValRat (E : PadicEnclosure p x)
    (h : E.normalizedVal < E.prec) : E.normalizedVal = padicValRat p E.center := by
  obtain ⟨hc, hv⟩ := E.normalizedVal_lt_prec_iff.mp h
  rw [E.normalizedVal_of_center_ne_zero hc, min_eq_left hv.le]

/-- The valuation component of the record is read off from the norm of the centre and the
radius: `p ^ (-v) = max (‖c‖, p ^ (-N))`. -/
theorem zpow_neg_normalizedVal (E : PadicEnclosure p x) :
    (p : ℝ) ^ (-E.normalizedVal) = max ‖(E.center : ℚ_[p])‖ ((p : ℝ) ^ (-E.prec)) := by
  by_cases h : E.center = 0
  · rw [E.normalizedVal_of_center_eq_zero h, h, Rat.cast_zero, norm_zero,
      max_eq_right (zpow_nonneg (Nat.cast_nonneg p) _)]
  · rw [E.normalizedVal_of_center_ne_zero h,
      Padic.norm_eq_zpow_neg_valuation (Rat.cast_ne_zero.mpr h), Padic.valuation_ratCast,
      ← max_neg_neg, (zpow_right_mono₀ (Nat.one_lt_cast.mpr hp.out.one_lt).le).map_max]

/-- The residue component `s` of the canonical normalized record of `(c, N)`: the residue of
`c · p ^ (-v)` in `[0, p ^ (N - v))`, computed from the unit part `Padic.unitPart c`. It is `0`
when `v = N` and lies in `[1, p ^ (N - v))`, prime to `p`, when `v < N`. -/
noncomputable def normalizedResidue (E : PadicEnclosure p x) : ℕ :=
  (Padic.unitPart (E.center : ℚ_[p])).appr (E.prec - E.normalizedVal).toNat

theorem normalizedResidue_lt (E : PadicEnclosure p x) :
    E.normalizedResidue < p ^ (E.prec - E.normalizedVal).toNat :=
  PadicInt.appr_lt _ _

theorem normalizedResidue_eq_zero_of_eq (E : PadicEnclosure p x)
    (h : E.normalizedVal = E.prec) : E.normalizedResidue = 0 := by
  have := E.normalizedResidue_lt
  rw [h, sub_self, Int.toNat_zero, pow_zero] at this
  omega

@[simp]
theorem normalizedResidue_of_center_eq_zero (E : PadicEnclosure p x) (h : E.center = 0) :
    E.normalizedResidue = 0 :=
  E.normalizedResidue_eq_zero_of_eq (E.normalizedVal_of_center_eq_zero h)

/-- The centre `p ^ v * s` of the canonical normalized record. -/
noncomputable def normalizedCenter (E : PadicEnclosure p x) : ℚ :=
  (p : ℚ) ^ E.normalizedVal * E.normalizedResidue

theorem normalizedCenter_def (E : PadicEnclosure p x) :
    E.normalizedCenter = (p : ℚ) ^ E.normalizedVal * E.normalizedResidue :=
  (rfl)

/-- In `ℚ_[p]`, the normalized centre is `p ^ v * s`. -/
@[simp]
theorem ratCast_normalizedCenter (E : PadicEnclosure p x) :
    (E.normalizedCenter : ℚ_[p]) = (p : ℚ_[p]) ^ E.normalizedVal * E.normalizedResidue := by
  simp [normalizedCenter_def]

/-- Below the precision, `c - p ^ v * s = p ^ v * (u - s)` for the unit part `u` of `c`. -/
private theorem norm_center_sub_zpow_mul (E : PadicEnclosure p x) (h : E.normalizedVal < E.prec)
    (s : ℕ) : ‖(E.center : ℚ_[p]) - (p : ℚ_[p]) ^ E.normalizedVal * s‖ =
      (p : ℝ) ^ (-E.normalizedVal) * ‖Padic.unitPart (E.center : ℚ_[p]) - s‖ := by
  have hc : (E.center : ℚ_[p]) =
      (p : ℚ_[p]) ^ E.normalizedVal * Padic.unitPart (E.center : ℚ_[p]) := by
    rw [E.normalizedVal_eq_padicValRat h, ← Padic.valuation_ratCast]
    exact Padic.eq_zpow_valuation_mul_unitPart _
  conv_lhs => rw [hc]
  rw [← mul_sub, norm_mul, Padic.norm_p_zpow, PadicInt.norm_def, PadicInt.coe_sub,
    PadicInt.coe_natCast]

/-- The normalized centre lies in the ball of the enclosure. -/
theorem norm_center_sub_normalizedCenter_le (E : PadicEnclosure p x) :
    ‖(E.center : ℚ_[p]) - E.normalizedCenter‖ ≤ (p : ℝ) ^ (-E.prec) := by
  rcases E.normalizedVal_le_prec.lt_or_eq with hlt | heq
  · -- Below the precision, the residue approximates the unit part to precision `N - v`.
    rw [ratCast_normalizedCenter, E.norm_center_sub_zpow_mul hlt]
    calc (p : ℝ) ^ (-E.normalizedVal) *
          ‖Padic.unitPart (E.center : ℚ_[p]) - (E.normalizedResidue : ℤ_[p])‖
        ≤ (p : ℝ) ^ (-E.normalizedVal) *
          (p : ℝ) ^ (-((E.prec - E.normalizedVal).toNat : ℤ)) :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_sub_appr_le _ _)
            (zpow_nonneg (Nat.cast_nonneg p) _)
      _ = (p : ℝ) ^ (-E.prec) := by
          rw [← zpow_add₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero), Int.toNat_of_nonneg (by omega)]
          ring_nf
  · -- At the precision, the normalized centre is `0` and `‖c‖ ≤ p ^ (-N)`.
    rw [normalizedCenter_def, E.normalizedResidue_eq_zero_of_eq heq, Nat.cast_zero, mul_zero,
      Rat.cast_zero, sub_zero]
    have h := E.zpow_neg_normalizedVal
    rw [heq] at h
    exact h ▸ le_max_left _ _

/-- The canonical normalized record denotes the closed ball of the enclosure. -/
theorem closedBall_normalizedCenter (E : PadicEnclosure p x) :
    Metric.closedBall (E.normalizedCenter : ℚ_[p]) ((p : ℝ) ^ (-E.prec)) =
      Metric.closedBall (E.center : ℚ_[p]) ((p : ℝ) ^ (-E.prec)) :=
  IsUltrametricDist.closedBall_eq_of_mem
    (by rw [Metric.mem_closedBall, dist_eq_norm]
        exact E.norm_center_sub_normalizedCenter_le)

/-- The enclosure of `x` given by the canonical normalized record: centre `p ^ v * s`, same
precision. -/
noncomputable def normalize (E : PadicEnclosure p x) : PadicEnclosure p x :=
  E.ofNormSubLe E.normalizedCenter E.norm_center_sub_normalizedCenter_le

@[simp]
theorem normalize_center (E : PadicEnclosure p x) : E.normalize.center = E.normalizedCenter :=
  (rfl)

@[simp]
theorem normalize_prec (E : PadicEnclosure p x) : E.normalize.prec = E.prec :=
  (rfl)

/-- The residue component is characterized by its defining congruence: it is the unique
`s < p ^ (N - v)` with `‖c - p ^ v * s‖ ≤ p ^ (-N)`. -/
theorem normalizedResidue_eq_of_norm_sub_le (E : PadicEnclosure p x) {s : ℕ}
    (hs : s < p ^ (E.prec - E.normalizedVal).toNat)
    (h : ‖(E.center : ℚ_[p]) - (p : ℚ_[p]) ^ E.normalizedVal * s‖ ≤ (p : ℝ) ^ (-E.prec)) :
    E.normalizedResidue = s := by
  rcases E.normalizedVal_le_prec.lt_or_eq with hlt | heq
  · -- Below the precision, `h` says that `s` approximates the unit part to precision `N - v`.
    refine (PadicInt.appr_eq_iff_norm_sub_le _ hs).mpr ?_
    have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.out.pos
    rw [E.norm_center_sub_zpow_mul hlt] at h
    rw [Int.toNat_of_nonneg (by omega)]
    refine le_of_mul_le_mul_left (h.trans_eq ?_) (zpow_pos hpos (-E.normalizedVal))
    rw [← zpow_add₀ hpos.ne']
    congr 1
    ring
  · -- At the precision, both residues lie below `p ^ 0 = 1`.
    rw [heq, sub_self, Int.toNat_zero, pow_zero] at hs
    rw [E.normalizedResidue_eq_zero_of_eq heq]
    omega

/-- In the case `v < N`, the residue component is prime to `p`, and in particular positive. -/
theorem coprime_normalizedResidue (E : PadicEnclosure p x) (h : E.normalizedVal < E.prec) :
    E.normalizedResidue.Coprime p := by
  have hc := (E.normalizedVal_lt_prec_iff.mp h).1
  have hk : 1 ≤ (E.prec - E.normalizedVal).toNat := by omega
  -- The unit part `u` has norm one and `‖u - s‖ < 1`, so `s` has norm one as well.
  have hu : ‖(Padic.unitPart (E.center : ℚ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.norm_coe, Padic.norm_unitPart (Rat.cast_ne_zero.mpr hc)]
  have h₁ : ‖(Padic.unitPart (E.center : ℚ_[p]) : ℚ_[p]) - (E.normalizedResidue : ℚ_[p])‖ <
      ‖(Padic.unitPart (E.center : ℚ_[p]) : ℚ_[p])‖ := by
    rw [hu, ← PadicInt.coe_natCast, ← PadicInt.coe_sub, PadicInt.norm_coe]
    exact (PadicInt.norm_sub_appr_le _ _).trans_lt
      (zpow_lt_one_of_neg₀ (Nat.one_lt_cast.mpr hp.out.one_lt) (by omega))
  rw [Nat.coprime_comm, ← Padic.norm_natCast_eq_one_iff, ← Padic.norm_eq_of_norm_sub_lt_left h₁,
    hu]

theorem normalizedResidue_pos (E : PadicEnclosure p x) (h : E.normalizedVal < E.prec) :
    0 < E.normalizedResidue := by
  by_contra h0
  have := E.coprime_normalizedResidue h
  rw [Nat.eq_zero_of_not_pos h0, Nat.coprime_zero_left] at this
  exact hp.out.one_lt.ne' this

/-- **Canonicity of the normalized record.** Two enclosures of the same precision, possibly of
different numbers, have the same normalized record exactly when they denote the same ball, that
is, when their centres are at distance at most `p ^ (-N)`. -/
theorem normalizedVal_eq_and_normalizedResidue_eq_iff {y : ℚ_[p]} (E : PadicEnclosure p x)
    (F : PadicEnclosure p y) (hN : E.prec = F.prec) :
    E.normalizedVal = F.normalizedVal ∧ E.normalizedResidue = F.normalizedResidue ↔
      ‖(E.center : ℚ_[p]) - F.center‖ ≤ (p : ℝ) ^ (-E.prec) := by
  constructor
  · rintro ⟨hv, hs⟩
    have hEF : E.normalizedCenter = F.normalizedCenter := by
      rw [normalizedCenter_def, normalizedCenter_def, hv, hs]
    have hF := F.norm_center_sub_normalizedCenter_le
    rw [← hN, ← hEF] at hF
    exact (IsUltrametricDist.norm_sub_le_max_norm_sub _ (E.normalizedCenter : ℚ_[p]) _).trans
      (max_le E.norm_center_sub_normalizedCenter_le hF)
  · intro h
    have hv : E.normalizedVal = F.normalizedVal := by
      have h' : (p : ℝ) ^ (-E.normalizedVal) = (p : ℝ) ^ (-F.normalizedVal) := by
        rw [E.zpow_neg_normalizedVal, F.zpow_neg_normalizedVal, ← hN]
        exact IsUltrametricDist.max_norm_eq_of_norm_sub_le h
      exact neg_inj.mp (zpow_right_injective₀ (Nat.cast_pos.mpr hp.out.pos)
        (Nat.one_lt_cast.mpr hp.out.one_lt).ne' h')
    refine ⟨hv, E.normalizedResidue_eq_of_norm_sub_le (hv ▸ hN ▸ F.normalizedResidue_lt) ?_⟩
    have hF := F.norm_center_sub_normalizedCenter_le
    rw [ratCast_normalizedCenter, ← hN, ← hv] at hF
    exact (IsUltrametricDist.norm_sub_le_max_norm_sub _ (F.center : ℚ_[p]) _).trans
      (max_le h (by rwa [norm_sub_rev]))

/-- Normalizing an enclosure does not change the valuation component of its record. -/
@[simp]
theorem normalizedVal_normalize (E : PadicEnclosure p x) :
    E.normalize.normalizedVal = E.normalizedVal :=
  ((E.normalize.normalizedVal_eq_and_normalizedResidue_eq_iff E rfl).mpr
    ((norm_sub_rev _ _).trans_le E.norm_center_sub_normalizedCenter_le)).1

/-- Normalizing an enclosure does not change the residue component of its record. -/
@[simp]
theorem normalizedResidue_normalize (E : PadicEnclosure p x) :
    E.normalize.normalizedResidue = E.normalizedResidue :=
  ((E.normalize.normalizedVal_eq_and_normalizedResidue_eq_iff E rfl).mpr
    ((norm_sub_rev _ _).trans_le E.norm_center_sub_normalizedCenter_le)).2

/-- Normalization is idempotent: a normalized enclosure is its own normalization. -/
@[simp]
theorem normalize_normalize (E : PadicEnclosure p x) : E.normalize.normalize = E.normalize := by
  ext
  · simp [normalizedCenter_def]
  · rfl

end PadicEnclosure

/-! ### Examples

At `p = 3`: the zero-centred enclosure `(0, 2)` encloses `9 ≠ 0`, and its normalized record is
`(2, 2, 0)` although `padicValRat 3 0 = 0`; the enclosure `(5, 1)` has normalized record
`(1, 0, 2)`, since the balls of radius `1/3` about `5` and about `2` coincide. -/

-- The zero-centred enclosure `(0, 2)` of `9` at `p = 3`.
noncomputable example : PadicEnclosure 3 (9 : ℚ_[3]) where
  center := 0
  prec := 2
  norm_sub_le := by
    -- `Padic.norm_p_pow` is stated for a natural power of the cast of `p`, so `9` is written as
    -- `(3 : ℚ_[3]) ^ (2 : ℕ)`.
    rw [Rat.cast_zero, sub_zero, show (9 : ℚ_[3]) = (3 : ℚ_[3]) ^ (2 : ℕ) by norm_num]
    exact (Padic.norm_p_pow 2).le

example : (PadicEnclosure.ofRat (p := 3) 0 2).normalizedVal = 2 ∧
    (PadicEnclosure.ofRat (p := 3) 0 2).normalizedResidue = 0 := by
  simp

example : (PadicEnclosure.ofRat (p := 3) 5 1).normalizedVal = 0 ∧
    (PadicEnclosure.ofRat (p := 3) 5 1).normalizedResidue = 2 := by
  have hv : (PadicEnclosure.ofRat (p := 3) 5 1).normalizedVal = 0 := by
    -- `padicValRat.of_nat` computes the valuation of the cast of a natural number, so the
    -- rational centre `5` is written as `((5 : ℕ) : ℚ)`.
    rw [PadicEnclosure.normalizedVal_of_center_ne_zero _ (by simp), PadicEnclosure.ofRat_center,
      PadicEnclosure.ofRat_prec, show (5 : ℚ) = ((5 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      multiplicity_eq_zero_of_not_dvd (by norm_num)]
    rfl
  refine ⟨hv, PadicEnclosure.normalizedResidue_eq_of_norm_sub_le _ (by simp [hv]) ?_⟩
  -- As above, `Padic.norm_p_pow` needs the difference `5 - 2` written as a natural power of `3`.
  rw [hv, PadicEnclosure.ofRat_center, PadicEnclosure.ofRat_prec, zpow_zero, one_mul,
    show ((5 : ℚ) : ℚ_[3]) - ((2 : ℕ) : ℚ_[3]) = (3 : ℚ_[3]) ^ (1 : ℕ) by norm_num]
  exact (Padic.norm_p_pow 1).le

end TauCeti
