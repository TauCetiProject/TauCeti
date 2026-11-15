/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Curve.Basic
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.GCDMonoid.Finset
import TauCeti.Algebra.MvPolynomial.Coeff
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Strict `p`-typical coordinate changes and classification of Hazewinkel isomorphisms

For any one-dimensional formal group law `F` over a commutative ring `R`, a natural number `p > 1`,
and a sequence `t : ℕ+ → R`, the finite formal-group sums

  `X +_F t₁ X^p +_F t₂ X^(p²) +_F ⋯ +_F tₙ X^(pⁿ)`

stabilize coefficientwise as `n → ∞`, defining a curve `F.pTypicalStrictCurve p t` with linear
coefficient `1`. Its compositional inverse is the strict formal coordinate
`F.pTypicalStrictCoordinate p t : TauCeti.FormalCoordinate R`, characterized by

  `(F.pTypicalStrictCoordinate p t)⁻¹(X) = X +_F ∑^F_{i ≥ 1} tᵢ X^(pⁱ)`.

Over a `ℚ`-algebra, substituting `pTypicalStrictCurve` into Hazewinkel's logarithm `f_v` yields the
power series with `X^(pⁿ)`-coefficient `mₙ(v) + ∑_{i < n} mᵢ(v) t_{n - i}^(pⁱ)` and zero outside
degrees `pⁿ` (Ravenel's recursion for the right unit of `(BP_*, BP_*BP)`). In particular,
transporting `hazewinkelFormalGroup p v` along `pTypicalStrictCoordinate p t` produces another
Hazewinkel formal group law, and every strict coordinate between two Hazewinkel laws over a
`ℚ`-algebra has this form.

To descend these results to arbitrary commutative rings and torsion coefficients, we establish the
degreewise comparison formula for `TauCeti.hazewinkelIntegralFormalGroup`: if `v` and `w` agree up
to index `n`, then `F_v - F_w` has order at least `p^(n + 1)` and its homogeneous component of
degree `p^(n + 1)` is `-(v_{n + 1} - w_{n + 1}) • C_{p^(n + 1)}`, where `C_d` is Lazard's
primitive symmetric additive `2`-cocycle. Because `r • C_d = 0 ↔ r = 0` over every commutative
ring, `hazewinkelIntegralFormalGroup p` is universally injective without torsion-freeness or
localization hypotheses, and transporting `hazewinkelIntegralFormalGroup p v` along
`pTypicalStrictCoordinate p t` yields a unique `hazewinkelIntegralFormalGroup p w` over every
commutative ring `R`.

Finally, when every prime `q ≠ p` is invertible in `R` (for instance over any `ℤ_(p)`-algebra or
`𝔽_p`-algebra), the binomial greatest common divisor `d_k` is a unit in `R` in every non-`p`-power
degree `k ≥ 2`, forcing every strict isomorphism between integral Hazewinkel formal group laws over
`R` to be `pTypicalStrictCoordinate p t` for a unique sequence `t : ℕ+ → R`.

## Main definitions

* `FormalGroup.pTypicalStrictCurve`: the curve `X +_F ∑^F_{i ≥ 1} tᵢ X^(pⁱ)` on `F` (`X` when
  `p ≤ 1`).
* `FormalGroup.pTypicalStrictCoordinate`: the strict formal coordinate `φ` with
  `φ⁻¹(X) = (F.pTypicalStrictCurve p t)(X)`.

## Main results

* `FormalGroup.pTypicalStrictCurve_injective`, `FormalGroup.pTypicalStrictCoordinate_injective`:
  for `1 < p`, the sequence `t` is uniquely determined by the curve or coordinate over any
  commutative ring.
* `TauCeti.coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog`,
  `TauCeti.coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero`: over a `ℚ`-algebra,
  `f_v((F_v.pTypicalStrictCurve p t)(X))` has `X^(pⁿ)`-coefficient
  `mₙ(v) + ∑_{i < n} mᵢ(v) t_{n - i}^(pⁱ)` and vanishes outside degrees `pⁿ`.
* `TauCeti.homogeneousComponent_hazewinkelIntegralFormalGroup_sub`: if `v` and `w` agree on
  `i ≤ n`, the degree-`p^(n + 1)` difference of `F_v` and `F_w` is
  `-(v_{n + 1} - w_{n + 1}) • C_{p^(n + 1)}`.
* `TauCeti.hazewinkelIntegralFormalGroup_injective`: `hazewinkelIntegralFormalGroup p` is injective
  over every commutative ring.
* `TauCeti.existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup`: over every
  commutative ring, transporting `hazewinkelIntegralFormalGroup p v` by
  `pTypicalStrictCoordinate p t` produces `hazewinkelIntegralFormalGroup p w` for a unique `w`.
* `TauCeti.exists_hazewinkelIntegralFormalGroup_eq_smul_iff`: when every prime `q ≠ p` is a unit in
  `R`, a strict coordinate `φ` transports `hazewinkelIntegralFormalGroup p v` to another integral
  Hazewinkel formal group law if and only if `φ` is `pTypicalStrictCoordinate p t` for a (unique)
  sequence `t : ℕ+ → R`.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*,
  Bull. Amer. Math. Soc. 75 (1969), 1293–1298.
* M. Hazewinkel, *Constructing formal groups. I. The local one dimensional case*,
  J. Pure Appl. Algebra 9 (1977), 131–149.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2 and Chapter IV.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1,
  Theorem A2.1.27.
-/

public section

noncomputable section

open Finset MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### `p`-typical strict curves and coordinates -/

/-- Monomial curve `c X^m` (`m ≠ 0`) on a formal group law `F`. -/
private def pTypicalMonomialCurve (F : FormalGroup R) (c : R) (m : ℕ) (hm : m ≠ 0) : F.Curve where
  toPowerSeries := c • PowerSeries.X ^ m
  constantCoeff_toPowerSeries := by simp [hm]

/-- Finite partial formal-group sum `X +_F t₁ X^p +_F ⋯ +_F tₙ X^(pⁿ)`. -/
private def pTypicalStrictCurveStage (F : FormalGroup R) (p : ℕ) (hp : 1 < p) (t : ℕ+ → R) :
    ℕ → F.Curve
  | 0 => F.tautologicalCurve
  | n + 1 => pTypicalStrictCurveStage F p hp t n +
      pTypicalMonomialCurve F (t n.succPNat) (p ^ (n + 1)) (pow_ne_zero _ (by omega))

private theorem coeff_pTypicalMonomialCurve_eq_zero_of_lt (F : FormalGroup R) (c : R) {m k : ℕ}
    (hm : m ≠ 0) (hk : k < m) :
    PowerSeries.coeff k (pTypicalMonomialCurve F c m hm).toPowerSeries = 0 := by
  simp [pTypicalMonomialCurve, PowerSeries.coeff_X_pow, hk.ne]

private theorem coeff_pTypicalStrictCurveStage_succ_of_lt (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t (n + 1)).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries :=
  Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero _ _ hk fun _ hi ↦
    coeff_pTypicalMonomialCurve_eq_zero_of_lt F _ _ hi

private theorem coeff_pTypicalStrictCurveStage_eq_of_le (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n m k : ℕ} (hnm : n ≤ m) (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t m).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
    have hpow : p ^ (n + 1) ≤ p ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [coeff_pTypicalStrictCurveStage_succ_of_lt F hp t (hk.trans_le hpow), ih]

private theorem pTypicalStrictCurveStage_congr (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    pTypicalStrictCurveStage F p hp t n = pTypicalStrictCurveStage F p hp t' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pTypicalStrictCurveStage, pTypicalStrictCurveStage,
      ih (fun i hi ↦ ht i (hi.trans (Nat.le_succ n))),
      ht n.succPNat (Nat.succ_le_succ le_rfl)]

private theorem map_pTypicalStrictCurveStage (F : FormalGroup R) {p : ℕ} (hp : 1 < p) (t : ℕ+ → R)
    (f : R →+* S) (n : ℕ) :
    Curve.map f (pTypicalStrictCurveStage F p hp t n) =
      pTypicalStrictCurveStage (F.map f) p hp (f ∘ t) n := by
  induction n with
  | zero => exact F.map_tautologicalCurve f
  | succ n ih =>
    rw [pTypicalStrictCurveStage, map_add, ih, pTypicalStrictCurveStage]
    congr 1
    ext k
    simp only [Curve.toPowerSeries_map, PowerSeries.coeff_map, pTypicalMonomialCurve,
      PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul, Function.comp_apply]
    split_ifs <;> simp

/-- **The `p`-typical strict curve** `X +_F t₁ X^p +_F t₂ X^(p²) +_F ⋯` on a formal group law `F`.
For `p ≤ 1`, where the powers `pⁱ` do not grow, this defaults to the tautological curve `X`. -/
def pTypicalStrictCurve (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) : F.Curve :=
  if hp : 1 < p then
    { toPowerSeries := PowerSeries.mk fun k ↦
        PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t k).toPowerSeries
      constantCoeff_toPowerSeries := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
        exact (pTypicalStrictCurveStage F p hp t 0).coeff_zero_toPowerSeries }
  else F.tautologicalCurve

/-- When `p ≤ 1`, `F.pTypicalStrictCurve p t` is the tautological curve `X`. -/
theorem pTypicalStrictCurve_of_le_one (F : FormalGroup R) {p : ℕ} (hp : p ≤ 1) (t : ℕ+ → R) :
    F.pTypicalStrictCurve p t = F.tautologicalCurve := by
  simp [pTypicalStrictCurve, show ¬ 1 < p by omega]

private theorem coeff_pTypicalStrictCurve_eq_stage (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries := by
  rw [pTypicalStrictCurve, dite_eq_left hp, PowerSeries.coeff_mk]
  rcases le_total n k with hnk | hkn
  · exact coeff_pTypicalStrictCurveStage_eq_of_le F hp t hnk hk
  · have hk' : k < p ^ (k + 1) :=
      (Nat.lt_succ_self k).trans_le (Nat.le_of_lt ((k + 1).lt_pow_self hp))
    exact (coeff_pTypicalStrictCurveStage_eq_of_le F hp t hkn hk').symm

/-- The linear coefficient of `F.pTypicalStrictCurve p t` is `1`. -/
@[simp]
theorem coeff_one_pTypicalStrictCurve (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    PowerSeries.coeff 1 (F.pTypicalStrictCurve p t).toPowerSeries = 1 := by
  by_cases hp : 1 < p
  · rw [coeff_pTypicalStrictCurve_eq_stage F hp t (n := 0) (by simpa using hp)]
    simp [pTypicalStrictCurveStage]
  · have hp' : p ≤ 1 := by omega
    rw [F.pTypicalStrictCurve_of_le_one hp']
    simp

/-- **The strict `p`-typical formal coordinate** attached to `F` and `t : ℕ+ → R`: the formal
coordinate `φ` whose compositional inverse is `F.pTypicalStrictCurve p t`, that is,
`φ⁻¹(X) = X +_F ∑^F_{i ≥ 1} tᵢ X^(pⁱ)`. -/
def pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    TauCeti.FormalCoordinate R :=
  ({ toPowerSeries := (F.pTypicalStrictCurve p t).toPowerSeries
     constantCoeff_toPowerSeries := (F.pTypicalStrictCurve p t).constantCoeff_toPowerSeries
     isUnit_coeff_one := by simp } : TauCeti.FormalCoordinate R)⁻¹

/-- The inverse power series of `F.pTypicalStrictCoordinate p t` is `F.pTypicalStrictCurve p t`. -/
theorem toPowerSeries_inv_pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    (F.pTypicalStrictCoordinate p t)⁻¹.toPowerSeries =
      (F.pTypicalStrictCurve p t).toPowerSeries := by
  rw [pTypicalStrictCoordinate, inv_inv]

/-- When `p ≤ 1`, `F.pTypicalStrictCoordinate p t` is the identity coordinate `1`. -/
theorem pTypicalStrictCoordinate_of_le_one (F : FormalGroup R) {p : ℕ} (hp : p ≤ 1)
    (t : ℕ+ → R) : F.pTypicalStrictCoordinate p t = 1 := by
  apply inv_injective
  ext1
  rw [toPowerSeries_inv_pTypicalStrictCoordinate, F.pTypicalStrictCurve_of_le_one hp, inv_one,
    TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]

/-- `F.pTypicalStrictCoordinate p t` has linear coefficient `1` as a unit. -/
@[simp]
theorem linearCoeff_pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalStrictCoordinate p t) = 1 := by
  apply inv_injective
  rw [← map_inv, inv_one]
  ext
  rw [TauCeti.FormalCoordinate.val_linearCoeff, toPowerSeries_inv_pTypicalStrictCoordinate,
    F.coeff_one_pTypicalStrictCurve, Units.val_one]

/-- The linear coefficient of `F.pTypicalStrictCoordinate p t` is `1`. -/
@[simp]
theorem coeff_one_pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    PowerSeries.coeff 1 (F.pTypicalStrictCoordinate p t).toPowerSeries = 1 := by
  rw [← TauCeti.FormalCoordinate.val_linearCoeff, F.linearCoeff_pTypicalStrictCoordinate,
    Units.val_one]

/-- `F.pTypicalStrictCoordinate p t` lies in the subgroup of strict coordinates. -/
theorem pTypicalStrictCoordinate_mem_ker_linearCoeff (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    F.pTypicalStrictCoordinate p t ∈ (TauCeti.FormalCoordinate.linearCoeff (R := R)).ker :=
  F.linearCoeff_pTypicalStrictCoordinate p t

/-- At `t = 0`, `F.pTypicalStrictCurve p 0` is the tautological curve `X`. -/
@[simp]
theorem pTypicalStrictCurve_zero (F : FormalGroup R) (p : ℕ) :
    F.pTypicalStrictCurve p 0 = F.tautologicalCurve := by
  by_cases hp : 1 < p
  · have hstage : ∀ n, pTypicalStrictCurveStage F p hp 0 n = F.tautologicalCurve := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        have hzero : pTypicalMonomialCurve F ((0 : ℕ+ → R) n.succPNat) (p ^ (n + 1))
            (pow_ne_zero _ (by omega)) = 0 := by
          ext k
          simp [pTypicalMonomialCurve]
        rw [pTypicalStrictCurveStage, ih, hzero, _root_.add_zero]
    ext k
    rw [pTypicalStrictCurve, dite_eq_left hp, PowerSeries.coeff_mk, hstage]
  · exact F.pTypicalStrictCurve_of_le_one (by omega) 0

/-- At `t = 0`, `F.pTypicalStrictCoordinate p 0` is the identity coordinate `1`. -/
@[simp]
theorem pTypicalStrictCoordinate_zero (F : FormalGroup R) (p : ℕ) :
    F.pTypicalStrictCoordinate p 0 = 1 := by
  apply inv_injective
  ext1
  rw [toPowerSeries_inv_pTypicalStrictCoordinate, F.pTypicalStrictCurve_zero, inv_one,
    TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]

/-- `pTypicalStrictCurve` commutes with arbitrary ring homomorphisms. -/
@[simp]
theorem map_pTypicalStrictCurve (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) (f : R →+* S) :
    Curve.map f (F.pTypicalStrictCurve p t) = (F.map f).pTypicalStrictCurve p (f ∘ t) := by
  by_cases hp : 1 < p
  · ext k
    have hk : k < p ^ (k + 1) :=
      (Nat.lt_succ_self k).trans_le (Nat.le_of_lt ((k + 1).lt_pow_self hp))
    rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
      coeff_pTypicalStrictCurve_eq_stage F hp t hk,
      coeff_pTypicalStrictCurve_eq_stage (F.map f) hp (f ∘ t) hk,
      ← map_pTypicalStrictCurveStage F hp t f k, Curve.toPowerSeries_map, PowerSeries.coeff_map]
  · have hp' : p ≤ 1 := by omega
    rw [F.pTypicalStrictCurve_of_le_one hp', (F.map f).pTypicalStrictCurve_of_le_one hp',
      F.map_tautologicalCurve]

/-- `pTypicalStrictCoordinate` commutes with arbitrary ring homomorphisms. -/
@[simp]
theorem map_pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) (f : R →+* S) :
    TauCeti.FormalCoordinate.map f (F.pTypicalStrictCoordinate p t) =
      (F.map f).pTypicalStrictCoordinate p (f ∘ t) := by
  apply inv_injective
  rw [← map_inv]
  ext1
  rw [TauCeti.FormalCoordinate.toPowerSeries_map, toPowerSeries_inv_pTypicalStrictCoordinate,
    toPowerSeries_inv_pTypicalStrictCoordinate, ← Curve.toPowerSeries_map,
    F.map_pTypicalStrictCurve]

/-- On the additive formal group law `𝔾ₐ`, `(𝔾ₐ.pTypicalStrictCurve p t)(X)` is the usual power
series `X + ∑_{n ≥ 1} tₙ X^(pⁿ)`. -/
theorem coeff_pTypicalStrictCurve_𝔾ₐ {p : ℕ} (hp : 1 < p) (t : ℕ+ → R) (k : ℕ) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalStrictCurve p t).toPowerSeries =
      if k = 1 then 1
      else if h : p ^ Nat.log p k = k ∧ 0 < Nat.log p k then t (⟨Nat.log p k, h.2⟩ : ℕ+)
      else 0 := by
  have hstage : ∀ n, (pTypicalStrictCurveStage (𝔾ₐ (R := R)) p hp t n).toPowerSeries =
      PowerSeries.X + ∑ i ∈ range n, t i.succPNat • PowerSeries.X ^ p ^ (i + 1) := by
    intro n
    induction n with
    | zero => simp [pTypicalStrictCurveStage]
    | succ n ih =>
      rw [pTypicalStrictCurveStage, Curve.toPowerSeries_add_𝔾ₐ, ih, sum_range_succ, add_assoc]
      rfl
  have hk : k < p ^ (k + 1) :=
    (Nat.lt_succ_self k).trans_le (Nat.le_of_lt ((k + 1).lt_pow_self hp))
  rw [coeff_pTypicalStrictCurve_eq_stage _ hp t hk, hstage k, map_add, PowerSeries.coeff_X,
    map_sum]
  rcases eq_or_ne k 1 with rfl | hk1
  · simp only [↓reduceIte]
    rw [sum_eq_zero]
    · ring
    · intro i _
      have hne : 1 ≠ p ^ (i + 1) := (Nat.one_lt_pow (Nat.succ_ne_zero i) hp).ne
      simp [PowerSeries.coeff_X_pow, hne]
  · simp only [hk1, ite_false, _root_.zero_add]
    split_ifs with hex
    · obtain ⟨hpow, hpos⟩ := hex
      obtain ⟨m, hm⟩ : ∃ m, Nat.log p k = m + 1 := ⟨Nat.log p k - 1, by omega⟩
      have hmk : m ∈ range k := by
        rw [mem_range]
        have hpow' : p ^ (m + 1) = k := hm ▸ hpow
        have h1 : m + 1 < p ^ (m + 1) := (m + 1).lt_pow_self hp
        omega
      rw [sum_eq_single m]
      · have hpnat : (⟨Nat.log p k, hpos⟩ : ℕ+) = m.succPNat := PNat.coe_injective hm
        rw [hpnat, ← hpow, hm]
        simp [PowerSeries.coeff_X_pow]
      · intro j _ hjm
        have hne : k ≠ p ^ (j + 1) := by
          rw [← hpow, hm]
          exact fun heq ↦ hjm <| by have := Nat.pow_right_injective hp heq; omega
        simp [PowerSeries.coeff_X_pow, hne]
      · intro hnot; exact absurd hmk hnot
    · refine sum_eq_zero fun i _ ↦ ?_
      have hne : k ≠ p ^ (i + 1) := by
        rintro rfl
        exact hex ⟨by rw [Nat.log_pow hp], by rw [Nat.log_pow hp]; exact Nat.succ_pos i⟩
      simp [PowerSeries.coeff_X_pow, hne]

/-- The degree-`k` coefficient of `F.pTypicalStrictCurve p t` depends only on those `tᵢ` with
`pⁱ ≤ k`. -/
theorem coeff_pTypicalStrictCurve_congr (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R}
    {k : ℕ} (ht : ∀ i : ℕ+, p ^ (i : ℕ) ≤ k → t i = t' i) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (F.pTypicalStrictCurve p t').toPowerSeries := by
  have hk : k < p ^ (k + 1) :=
    (Nat.lt_succ_self k).trans_le (Nat.le_of_lt ((k + 1).lt_pow_self hp))
  rw [coeff_pTypicalStrictCurve_eq_stage F hp t hk, coeff_pTypicalStrictCurve_eq_stage F hp t' hk]
  suffices ∀ n, ∀ j ≤ k,
      PowerSeries.coeff j (pTypicalStrictCurveStage F p hp t n).toPowerSeries =
        PowerSeries.coeff j (pTypicalStrictCurveStage F p hp t' n).toPowerSeries from
    this k k le_rfl
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro j hj
    rcases lt_or_ge j (p ^ (n + 1)) with hlt | hge
    · rw [coeff_pTypicalStrictCurveStage_succ_of_lt F hp t hlt,
        coeff_pTypicalStrictCurveStage_succ_of_lt F hp t' hlt]
      exact ih j hj
    · refine Curve.coeff_add_congr (fun r hr ↦ ih r (hr.trans hj)) fun r _ ↦ ?_
      have htn : t n.succPNat = t' n.succPNat := ht n.succPNat (hge.trans hj)
      simp [pTypicalMonomialCurve, htn]

/-- If `t` and `t'` agree up to index `n`, then `F.pTypicalStrictCurve p t` and
`F.pTypicalStrictCurve p t'` agree below degree `p^(n + 1)`. -/
theorem le_order_pTypicalStrictCurve_sub (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R}
    {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤
      ((F.pTypicalStrictCurve p t).toPowerSeries -
        (F.pTypicalStrictCurve p t').toPowerSeries).order := by
  refine PowerSeries.nat_le_order _ _ fun k hk ↦ ?_
  rw [map_sub, F.coeff_pTypicalStrictCurve_congr hp fun i hi ↦ ht i ?_, sub_self]
  by_contra! hlt
  have hpow : p ^ (n + 1) ≤ p ^ (i : ℕ) := Nat.pow_le_pow_right (by omega) hlt
  omega

/-- If `t` and `t'` agree up to index `n`, the coefficient of `X^(p^(n + 1))` in
`F.pTypicalStrictCurve p t - F.pTypicalStrictCurve p t'` is `t_{n + 1} - t'_{n + 1}`. -/
theorem coeff_pow_succ_pTypicalStrictCurve_sub (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    PowerSeries.coeff (p ^ (n + 1))
        ((F.pTypicalStrictCurve p t).toPowerSeries -
          (F.pTypicalStrictCurve p t').toPowerSeries) =
      t n.succPNat - t' n.succPNat := by
  have hk : p ^ (n + 1) < p ^ (n + 1 + 1) := Nat.pow_lt_pow_right hp (Nat.lt_succ_self _)
  rw [map_sub, coeff_pTypicalStrictCurve_eq_stage F hp t hk,
    coeff_pTypicalStrictCurve_eq_stage F hp t' hk, pTypicalStrictCurveStage,
    pTypicalStrictCurveStage,
    Curve.coeff_add_of_forall_lt_coeff_eq_zero _ _ (pow_ne_zero _ (by omega)) le_rfl
      (fun _ hi ↦ coeff_pTypicalMonomialCurve_eq_zero_of_lt F _ _ hi),
    Curve.coeff_add_of_forall_lt_coeff_eq_zero _ _ (pow_ne_zero _ (by omega)) le_rfl
      (fun _ hi ↦ coeff_pTypicalMonomialCurve_eq_zero_of_lt F _ _ hi),
    pTypicalStrictCurveStage_congr F hp ht]
  simp [pTypicalMonomialCurve, PowerSeries.coeff_X_pow]

/-- For `1 < p`, `F.pTypicalStrictCurve p` is injective over any commutative ring. -/
theorem pTypicalStrictCurve_injective (F : FormalGroup R) {p : ℕ} (hp : 1 < p) :
    Function.Injective (F.pTypicalStrictCurve p) := by
  intro t t' h
  suffices ∀ n, ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i from
    funext fun i ↦ this (i : ℕ) i le_rfl
  intro n
  induction n with
  | zero => intro i hi; have := i.pos; omega
  | succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact ih i (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : i = n.succPNat := PNat.coe_injective heq
      have hsub := F.coeff_pow_succ_pTypicalStrictCurve_sub hp ih
      rw [h, sub_self, map_zero, eq_comm, sub_eq_zero] at hsub
      exact hsub

/-- For `1 < p`, `F.pTypicalStrictCoordinate p` is injective over any commutative ring. -/
theorem pTypicalStrictCoordinate_injective (F : FormalGroup R) {p : ℕ} (hp : 1 < p) :
    Function.Injective (F.pTypicalStrictCoordinate p) := fun _ _ h ↦
  F.pTypicalStrictCurve_injective hp <| Curve.ext <| by
    simpa only [toPowerSeries_inv_pTypicalStrictCoordinate] using
      congrArg (fun φ : TauCeti.FormalCoordinate R ↦ φ⁻¹.toPowerSeries) h

@[simp]
theorem pTypicalStrictCurve_eq_iff (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R} :
    F.pTypicalStrictCurve p t = F.pTypicalStrictCurve p t' ↔ t = t' :=
  (F.pTypicalStrictCurve_injective hp).eq_iff

@[simp]
theorem pTypicalStrictCoordinate_eq_iff (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R} :
    F.pTypicalStrictCoordinate p t = F.pTypicalStrictCoordinate p t' ↔ t = t' :=
  (F.pTypicalStrictCoordinate_injective hp).eq_iff

end FormalGroup

namespace TauCeti

/-! ### Rational logarithm of `p`-typical strict coordinate changes -/

section Rational

variable {K : Type*} [CommRing K] [Algebra ℚ K] {p : ℕ}

open scoped Classical in
private theorem coeff_subst_smul_X_pow_hazewinkelLog (hp : 1 < p) (v : ℕ+ → K) (c : K) (m k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.subst (c • PowerSeries.X ^ p ^ (m + 1)) (hazewinkelLog p v).toPowerSeries) =
      if h : ∃ j, p ^ (j + m + 1) = k then c ^ p ^ h.choose * hazewinkelLogCoeff p v h.choose
      else 0 := by
  have hne : p ^ (m + 1) ≠ 0 := pow_ne_zero _ (by omega)
  have h0 : PowerSeries.constantCoeff (c • PowerSeries.X ^ p ^ (m + 1) : PowerSeries K) = 0 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_X_pow, hne.symm]
  rw [PowerSeries.coeff_def Finsupp.single_eq_same,
    PowerSeries.coeff_subst_eq_sum_range_degree (τ := Unit) (a := c • PowerSeries.X ^ p ^ (m + 1))
      (by simpa [← PowerSeries.constantCoeff_eq] using h0) (hazewinkelLog p v).toPowerSeries
      (Finsupp.single () k)]
  simp only [Finsupp.degree_single]
  split_ifs with hex
  · have ⟨j, hj⟩ := hex
    subst hj
    have huniq : hex.choose = j := by
      have := Nat.pow_right_injective hp hex.choose_spec
      omega
    rw [huniq, sum_eq_single (p ^ j)]
    · rw [coeff_hazewinkelLog_pow v hp j, smul_pow, ← pow_mul, ← pow_add,
        show m + 1 + j = j + m + 1 by omega]
      simp [← PowerSeries.coeff_def Finsupp.single_eq_same, PowerSeries.coeff_X_pow, mul_comm]
    · intro d _ hdj
      by_cases hpow : ∃ r, p ^ r = d
      · obtain ⟨r, rfl⟩ := hpow
        have hrj : r ≠ j := fun h ↦ hdj (h ▸ rfl)
        have hne' : p ^ (j + m + 1) ≠ p ^ (m + 1) * p ^ r := by
          rw [← pow_add]
          intro heq
          have := Nat.pow_right_injective hp heq
          omega
        rw [smul_pow, ← pow_mul]
        simp [← PowerSeries.coeff_def Finsupp.single_eq_same, PowerSeries.coeff_X_pow, hne']
      · push Not at hpow
        rw [coeff_hazewinkelLog_eq_zero v hpow, zero_smul]
    · intro hnot
      refine absurd (mem_range.mpr ?_) hnot
      have : p ^ j ≤ p ^ (j + m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
  · refine sum_eq_zero fun d _ ↦ ?_
    by_cases hpow : ∃ r, p ^ r = d
    · obtain ⟨r, rfl⟩ := hpow
      have hne' : k ≠ p ^ (m + 1) * p ^ r := by
        rw [← pow_add, show m + 1 + r = r + m + 1 by omega]
        exact fun h ↦ hex ⟨r, h.symm⟩
      rw [smul_pow, ← pow_mul]
      simp [← PowerSeries.coeff_def Finsupp.single_eq_same, PowerSeries.coeff_X_pow, hne']
    · push Not at hpow
      rw [coeff_hazewinkelLog_eq_zero v hpow, zero_smul]

private theorem subst_pTypicalStrictCurve_hazewinkelLog_stage (hp : 1 < p) (v t : ℕ+ → K) (N k : ℕ)
    (hk : k < p ^ (N + 1)) :
    PowerSeries.coeff k
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) =
      PowerSeries.coeff k ((hazewinkelLog p v).toPowerSeries +
        ∑ i ∈ range N,
          PowerSeries.subst (t i.succPNat • PowerSeries.X ^ p ^ (i + 1))
            (hazewinkelLog p v).toPowerSeries) := by
  let F := hazewinkelFormalGroup p v
  let γN := FormalGroup.pTypicalStrictCurveStage F p hp t N
  have hdvd : PowerSeries.X ^ p ^ (N + 1) ∣
      (F.pTypicalStrictCurve p t).toPowerSeries - γN.toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun j hj ↦ by
      rw [map_sub, FormalGroup.coeff_pTypicalStrictCurve_eq_stage F hp t hj, sub_self]
  have hsub := PowerSeries.X_pow_dvd_iff.mp
    (PowerSeries.X_pow_dvd_subst_sub_subst (F.pTypicalStrictCurve p t).constantCoeff_toPowerSeries
      hdvd (hazewinkelLog p v).toPowerSeries) k hk
  rw [map_sub, sub_eq_zero] at hsub
  rw [hsub]
  congr 1
  have hcurve : ∀ M,
      (F.logHom.mapCurve (FormalGroup.pTypicalStrictCurveStage F p hp t M)).toPowerSeries =
        (hazewinkelLog p v).toPowerSeries +
          ∑ i ∈ range M,
            PowerSeries.subst (t i.succPNat • PowerSeries.X ^ p ^ (i + 1))
              (hazewinkelLog p v).toPowerSeries := by
    intro M
    induction M with
    | zero =>
      rw [FormalGroup.pTypicalStrictCurveStage, FormalGroupHom.toPowerSeries_mapCurve,
        FormalGroup.toPowerSeries_tautologicalCurve, FormalGroup.logHom_toPowerSeries,
        log_hazewinkelFormalGroup, PowerSeries.X_subst, range_zero, sum_empty, add_zero]
    | succ M ih =>
      rw [FormalGroup.pTypicalStrictCurveStage, map_add, FormalGroup.Curve.toPowerSeries_add_𝔾ₐ,
        ih, sum_range_succ, add_assoc]
      congr 2
      rw [FormalGroupHom.toPowerSeries_mapCurve, FormalGroup.logHom_toPowerSeries,
        log_hazewinkelFormalGroup]
      rfl
  have hN := hcurve N
  rwa [FormalGroupHom.toPowerSeries_mapCurve, FormalGroup.logHom_toPowerSeries,
    log_hazewinkelFormalGroup] at hN

/-- **Ravenel's logarithm formula for a strict `p`-typical coordinate change**: over a `ℚ`-algebra,
the coefficient of `X^(pⁿ)` in `f_v((F_v.pTypicalStrictCurve p t)(X))` is
`mₙ(v) + ∑_{i < n} mᵢ(v) t_{n - i}^(pⁱ)`. -/
theorem coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog (hp : 1 < p) (v t : ℕ+ → K) (n : ℕ) :
    PowerSeries.coeff (p ^ n)
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) =
      hazewinkelLogCoeff p v n +
        ∑ i ∈ range n, hazewinkelLogCoeff p v i * t (n - 1 - i).succPNat ^ p ^ i := by
  classical
  have hk : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp (Nat.lt_succ_self n)
  rw [subst_pTypicalStrictCurve_hazewinkelLog_stage hp v t n (p ^ n) hk, map_add,
    coeff_hazewinkelLog_pow v hp n, map_sum]
  congr 1
  refine Finset.sum_bij (fun m _ ↦ n - 1 - m)
    (fun m hm ↦ mem_range.mpr (by have := mem_range.mp hm; omega))
    (fun m₁ hm₁ m₂ hm₂ h ↦ by have := mem_range.mp hm₁; have := mem_range.mp hm₂; omega)
    (fun i hi ↦ ⟨n - 1 - i, mem_range.mpr (by have := mem_range.mp hi; omega),
      by have := mem_range.mp hi; omega⟩) ?_
  intro m hm
  have hlt : m < n := mem_range.mp hm
  have hex : ∃ j, p ^ (j + m + 1) = p ^ n := ⟨n - 1 - m, by congr 1; omega⟩
  rw [coeff_subst_smul_X_pow_hazewinkelLog hp v (t m.succPNat) m (p ^ n), dite_eq_left hex]
  have hj : hex.choose = n - 1 - m := by
    have := Nat.pow_right_injective hp hex.choose_spec
    omega
  have hm' : (n - 1 - (n - 1 - m)).succPNat = m.succPNat := by congr 1; omega
  rw [hj, hm', mul_comm]

/-- Outside the degrees `pⁿ`, `f_v((F_v.pTypicalStrictCurve p t)(X))` vanishes. -/
theorem coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero (hp : 1 < p) (v t : ℕ+ → K) {k : ℕ}
    (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) = 0 := by
  classical
  have hlt : k < p ^ (k + 1) :=
    (Nat.lt_succ_self k).trans_le (Nat.le_of_lt ((k + 1).lt_pow_self hp))
  rw [subst_pTypicalStrictCurve_hazewinkelLog_stage hp v t k k hlt, map_add,
    coeff_hazewinkelLog_eq_zero v hk, zero_add, map_sum]
  refine sum_eq_zero fun m _ ↦ ?_
  rw [coeff_subst_smul_X_pow_hazewinkelLog hp v (t m.succPNat) m k,
    dite_eq_right fun ⟨j, hj⟩ ↦ hk (j + m + 1) hj]

/-- The formal logarithm of `(F_v.pTypicalStrictCoordinate p t) • F_v` is
`f_v((F_v.pTypicalStrictCurve p t)(X))`. -/
theorem log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup (v t : ℕ+ → K) :
    (((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t) •
        hazewinkelFormalGroup p v).log =
      PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
        (hazewinkelLog p v).toPowerSeries := by
  rw [FormalGroup.log_smul, log_hazewinkelFormalGroup,
    FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]
  simp

/-- Over a `ℚ`-algebra, transporting `hazewinkelFormalGroup p v` along its `p`-typical strict
coordinate `t` produces `hazewinkelFormalGroup p w` for a unique sequence `w : ℕ+ → K`. -/
theorem existsUnique_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup (hp : 1 < p)
    (v t : ℕ+ → K) :
    ∃! w : ℕ+ → K,
      ((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t) • hazewinkelFormalGroup p v =
        hazewinkelFormalGroup p w :=
  existsUnique_eq_hazewinkelFormalGroup hp fun k hk ↦ by
    rw [log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup,
      coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero hp v t hk]

/-- Recursive reconstruction of the `p`-typical coordinate parameters `t` sending `F_v` to `F_w`
over a `ℚ`-algebra: `tₙ = mₙ(w) - mₙ(v) - ∑_{1 ≤ i < n} mᵢ(v) t_{n - i}^(pⁱ)`. -/
private def pTypicalCoordParamsRat (p : ℕ) (v w : ℕ+ → K) : ℕ → K
  | n => hazewinkelLogCoeff p w (n + 1) - hazewinkelLogCoeff p v (n + 1) -
      ∑ i : Fin n,
        hazewinkelLogCoeff p v ((i : ℕ) + 1) *
          pTypicalCoordParamsRat p v w (n - ((i : ℕ) + 1)) ^ p ^ ((i : ℕ) + 1)
decreasing_by have := i.isLt; omega

/-- Over a `ℚ`-algebra, any two Hazewinkel formal group laws `F_v` and `F_w` are strictly
isomorphic via `(hazewinkelLog p w)⁻¹ * hazewinkelLog p v`, which equals
`(hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t` for a unique `t : ℕ+ → K`. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_inv_hazewinkelLog_mul (hp : 1 < p)
    (v w : ℕ+ → K) :
    ∃! t : ℕ+ → K,
      (hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t =
        (hazewinkelLog p w)⁻¹ * hazewinkelLog p v := by
  let t : ℕ+ → K := fun j ↦ pTypicalCoordParamsRat p v w j.natPred
  have ht_rec (n : ℕ) : t n.succPNat = hazewinkelLogCoeff p w (n + 1) -
      hazewinkelLogCoeff p v (n + 1) -
      ∑ i ∈ range n, hazewinkelLogCoeff p v (i + 1) * t (n - 1 - i).succPNat ^ p ^ (i + 1) := by
    simp only [t, Nat.natPred_succPNat]
    rw [pTypicalCoordParamsRat, Fin.sum_univ_eq_sum_range (fun j ↦
      hazewinkelLogCoeff p v (j + 1) * pTypicalCoordParamsRat p v w (n - (j + 1)) ^ p ^ (j + 1))]
    refine congrArg
      (fun s ↦ hazewinkelLogCoeff p w (n + 1) - hazewinkelLogCoeff p v (n + 1) - s)
      (sum_congr rfl fun i _ ↦ ?_)
    rw [show n - 1 - i = n - (i + 1) by omega]
  have hlog : PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
      (hazewinkelLog p v).toPowerSeries = (hazewinkelLog p w).toPowerSeries := by
    ext k
    by_cases hpow : ∃ n, p ^ n = k
    · obtain ⟨_ | n, rfl⟩ := hpow
      · rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp v t 0,
          coeff_hazewinkelLog_pow w hp 0, hazewinkelLogCoeff_zero, hazewinkelLogCoeff_zero,
          range_zero, sum_empty, add_zero]
      · rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp v t (n + 1),
          coeff_hazewinkelLog_pow w hp (n + 1), sum_range_succ', pow_zero, pow_one,
          hazewinkelLogCoeff_zero, one_mul, show n + 1 - 1 - 0 = n by omega, ht_rec n]
        have hsum : ∑ x ∈ range n,
            hazewinkelLogCoeff p v (x + 1) * t (n + 1 - 1 - (x + 1)).succPNat ^ p ^ (x + 1) =
          ∑ x ∈ range n,
            hazewinkelLogCoeff p v (x + 1) * t (n - 1 - x).succPNat ^ p ^ (x + 1) :=
          sum_congr rfl fun x _ ↦ by rw [show n + 1 - 1 - (x + 1) = n - 1 - x by omega]
        rw [hsum]
        ring
    · push Not at hpow
      rw [coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero hp v t hpow,
        coeff_hazewinkelLog_eq_zero w hpow]
  have hcoord : (hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t =
      (hazewinkelLog p w)⁻¹ * hazewinkelLog p v := by
    apply inv_injective
    rw [mul_inv_rev, inv_inv]
    have hmul : hazewinkelLog p v * ((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t)⁻¹ =
        hazewinkelLog p w := FormalCoordinate.ext <| by
      rw [FormalCoordinate.toPowerSeries_mul,
        FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate, hlog]
    rw [← hmul, inv_mul_cancel_left]
  exact ⟨t, hcoord, fun t' ht' ↦
    (hazewinkelFormalGroup p v).pTypicalStrictCoordinate_injective hp (ht'.trans hcoord.symm)⟩

end Rational

/-! ### Degreewise comparison and universal injectivity of `hazewinkelIntegralFormalGroup` -/

section Comparison

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

omit p hp in
/-- If `η • F = G` and `η(X) = X + X^m s(X)` (`m ≠ 0`), then `F - G` has order at least `m` and
degree-`m` homogeneous component `-s(0) • ((X₀ + X₁)^m - X₀^m - X₁^m)`. -/
private theorem order_and_homogeneousComponent_of_smul_eq {F G : FormalGroup R}
    {η : FormalCoordinate R} (hsmul : η • F = G) {m : ℕ} (hm : m ≠ 0) {s : PowerSeries R}
    (hη : η.toPowerSeries = PowerSeries.X + PowerSeries.X ^ m * s) :
    (m : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order ∧
      homogeneousComponent m (F.toPowerSeries - G.toPowerSeries) =
        -((PowerSeries.constantCoeff s •
            ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ m - MvPolynomial.X 0 ^ m -
              MvPolynomial.X 1 ^ m) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  set c := PowerSeries.constantCoeff s
  have hdef_η : F.homDefect G η.toPowerSeries = 0 := by
    rw [← hsmul, FormalGroup.homDefect_eq_sub_subst_pair,
      FormalGroup.subst_toPowerSeries_eq_subst_smul_toPowerSeries, sub_self]
  have hη_ord : (m : ℕ∞) ≤ (η.toPowerSeries - PowerSeries.X).order :=
    PowerSeries.nat_le_order _ _ fun k hk ↦ by
      rw [hη, add_sub_cancel_left, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega)]
  have hord : (m : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order := by
    have h := F.le_order_homDefect_sub (G := G) PowerSeries.constantCoeff_X hη_ord
    rwa [hdef_η, zero_sub, order_neg, FormalGroup.homDefect_X] at h
  have hη_approx : ((m + 1 : ℕ) : ℕ∞) ≤
      (η.toPowerSeries - (PowerSeries.X + c • PowerSeries.X ^ m)).order :=
    PowerSeries.nat_le_order _ _ fun k hk ↦ by
      rw [hη, map_sub, map_add, map_add]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
      · simp [PowerSeries.coeff_X_pow_mul', show ¬ m ≤ k by omega, PowerSeries.coeff_X_pow, hlt.ne]
      · simp [c, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_X_pow]
  have hg0 : PowerSeries.constantCoeff (PowerSeries.X + c • PowerSeries.X ^ m : PowerSeries R) =
      0 := by simp [hm]
  have hdef_step := F.le_order_homDefect_sub (G := G) hg0 hη_approx
  rw [hdef_η, zero_sub, order_neg] at hdef_step
  have hhom0 : homogeneousComponent m (F.homDefect G (PowerSeries.X + c • PowerSeries.X ^ m)) = 0 :=
    homogeneousComponent_of_lt_order_eq_zero
      ((Nat.cast_lt.mpr (Nat.lt_succ_self m)).trans_le hdef_step)
  have hlead := F.homogeneousComponent_homDefect_add_sub (G := G) PowerSeries.constantCoeff_X hm c
  rw [map_sub, hhom0, FormalGroup.homDefect_X, zero_sub, neg_eq_iff_eq_neg] at hlead
  exact ⟨hord, hlead⟩

omit p hp in
private theorem exists_toPowerSeries_mul_eq_X_add_X_pow_mul {φ ψ : FormalCoordinate R}
    (hφ : FormalCoordinate.linearCoeff φ = 1) {m : ℕ} (hm : m ≠ 0) {r : PowerSeries R}
    (hψ : ψ.toPowerSeries = φ⁻¹.toPowerSeries + PowerSeries.X ^ m * r) :
    ∃ s : PowerSeries R,
      (φ * ψ).toPowerSeries = PowerSeries.X + PowerSeries.X ^ m * s ∧
        PowerSeries.constantCoeff s = PowerSeries.constantCoeff r := by
  obtain ⟨s, hs, hs0⟩ := PowerSeries.exists_subst_add_X_pow_mul φ.toPowerSeries
    φ⁻¹.constantCoeff_toPowerSeries r hm
  have hφ_inv : PowerSeries.subst φ⁻¹.toPowerSeries φ.toPowerSeries = PowerSeries.X := by
    simpa only [FormalCoordinate.toPowerSeries_mul, FormalCoordinate.toPowerSeries_one] using
      congrArg FormalCoordinate.toPowerSeries (mul_inv_cancel φ)
  have hφ1 : PowerSeries.coeff 1 φ.toPowerSeries = 1 := by
    rw [← FormalCoordinate.val_linearCoeff, hφ, Units.val_one]
  refine ⟨s, ?_, by simpa [hφ1] using hs0⟩
  rw [FormalCoordinate.toPowerSeries_mul, hψ, hs, hφ_inv]

private theorem hazewinkelLogCoeff_eq_of_forall_le_rat {K : Type*} [CommRing K] [Algebra ℚ K]
    {v w : ℕ+ → K} {n : ℕ} (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    (∀ m ≤ n, hazewinkelLogCoeff p v m = hazewinkelLogCoeff p w m) ∧
      hazewinkelLogCoeff p v (n + 1) - hazewinkelLogCoeff p w (n + 1) =
        (p : ℚ)⁻¹ • (v n.succPNat - w n.succPNat) := by
  have hrec (u : ℕ+ → K) (m : ℕ) : (p : K) * hazewinkelLogCoeff p u (m + 1) =
      u m.succPNat +
        ∑ i ∈ range m, hazewinkelLogCoeff p u (i + 1) * u (m - (i + 1)).succPNat ^ p ^ (i + 1) := by
    rw [natCast_mul_hazewinkelLogCoeff_succ u hp.out.ne_zero, sum_range_succ', add_comm]
    simp
  have hlog_eq : ∀ m ≤ n, hazewinkelLogCoeff p v m = hazewinkelLogCoeff p w m := by
    intro m hm
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | m
      · simp
      · have h1 := hrec v m
        have h2 := hrec w m
        have hs : ∑ i ∈ range m,
            hazewinkelLogCoeff p v (i + 1) * v (m - (i + 1)).succPNat ^ p ^ (i + 1) =
          ∑ i ∈ range m,
            hazewinkelLogCoeff p w (i + 1) * w (m - (i + 1)).succPNat ^ p ^ (i + 1) :=
          sum_congr rfl fun i hi ↦ by
            have := mem_range.mp hi
            rw [ih (i + 1) (by omega) (by omega), hvw _ (by simp; omega)]
        rw [hvw m.succPNat hm, hs, ← h2] at h1
        simp only [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ] at h1
        exact smul_right_injective K (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℚ) ≠ 0) h1
  refine ⟨hlog_eq, ?_⟩
  have hs : ∑ i ∈ range n,
      hazewinkelLogCoeff p v (i + 1) * v (n - (i + 1)).succPNat ^ p ^ (i + 1) =
    ∑ i ∈ range n,
      hazewinkelLogCoeff p w (i + 1) * w (n - (i + 1)).succPNat ^ p ^ (i + 1) :=
    sum_congr rfl fun i hi ↦ by
      have := mem_range.mp hi
      rw [hlog_eq (i + 1) (by omega), hvw _ (by simp; omega)]
  have hdiff : (p : ℚ) • (hazewinkelLogCoeff p v (n + 1) - hazewinkelLogCoeff p w (n + 1)) =
      v n.succPNat - w n.succPNat := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_sub, hrec v n, hrec w n, hs]
    ring
  rw [← hdiff, inv_smul_smul₀ (Nat.cast_ne_zero.2 hp.out.ne_zero)]

/-- Over a `ℚ`-algebra, if `v` and `w` agree on `i ≤ n`, then `f_v - f_w` equals
`p⁻¹ (v_{n + 1} - w_{n + 1}) X^(p^(n + 1))` modulo `X^(p^(n + 1) + 1)`. -/
private theorem hazewinkelLog_sub_of_forall_le_rat {K : Type*} [CommRing K] [Algebra ℚ K]
    {v w : ℕ+ → K} {n : ℕ} (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    PowerSeries.X ^ (p ^ (n + 1) + 1) ∣
      ((hazewinkelLog p v).toPowerSeries - (hazewinkelLog p w).toPowerSeries) -
        ((p : ℚ)⁻¹ • (v n.succPNat - w n.succPNat)) • PowerSeries.X ^ p ^ (n + 1) := by
  have hp1 : 1 < p := hp.out.one_lt
  obtain ⟨hlog_eq, hlog_succ⟩ := hazewinkelLogCoeff_eq_of_forall_le_rat p hvw
  refine PowerSeries.X_pow_dvd_iff.mpr fun k hk ↦ ?_
  rw [map_sub, map_sub]
  by_cases hpow : ∃ m, p ^ m = k
  · obtain ⟨m, rfl⟩ := hpow
    rcases lt_trichotomy m (n + 1) with hlt | rfl | hgt
    · have hne : p ^ m ≠ p ^ (n + 1) := (Nat.pow_lt_pow_right hp1 hlt).ne
      rw [coeff_hazewinkelLog_pow v hp1, coeff_hazewinkelLog_pow w hp1, hlog_eq m (by omega),
        sub_self, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, ite_eq_right hne, smul_zero,
        sub_zero]
    · rw [coeff_hazewinkelLog_pow v hp1, coeff_hazewinkelLog_pow w hp1, hlog_succ,
        PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, ite_eq_left rfl, smul_eq_mul, mul_one,
        sub_self]
    · exfalso
      have h1 : p ^ (n + 1) * p ≤ p ^ m := by
        rw [← pow_succ]
        exact Nat.pow_le_pow_right hp.out.pos hgt
      have h2 : p ^ (n + 1) + 1 ≤ p ^ (n + 1) * p := by
        have : 2 ≤ p := hp.out.two_le
        have : 1 ≤ p ^ (n + 1) := Nat.one_le_pow _ _ hp.out.pos
        nlinarith
      omega
  · push Not at hpow
    have hkN : k ≠ p ^ (n + 1) := (hpow (n + 1)).symm
    rw [coeff_hazewinkelLog_eq_zero v hpow, coeff_hazewinkelLog_eq_zero w hpow, sub_zero,
      PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, ite_eq_right hkN, smul_zero, zero_sub,
      neg_zero]

/-- Over a `ℚ`-algebra, if `v` and `w` agree on `i ≤ n`, then `F_v - F_w` has order at least
`p^(n + 1)` and degree-`p^(n + 1)` homogeneous component
`-(v_{n + 1} - w_{n + 1}) • C_{p^(n + 1)}`. -/
private theorem hazewinkelFormalGroup_sub_of_forall_le_rat {K : Type*} [CommRing K] [Algebra ℚ K]
    {v w : ℕ+ → K} {n : ℕ} (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤
        ((hazewinkelFormalGroup p v).toPowerSeries -
          (hazewinkelFormalGroup p w).toPowerSeries).order ∧
      homogeneousComponent (p ^ (n + 1))
          ((hazewinkelFormalGroup p v).toPowerSeries -
            (hazewinkelFormalGroup p w).toPowerSeries) =
        -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) K :
            MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) := by
  set N := p ^ (n + 1)
  have hN0 : N ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  set c : K := (p : ℚ)⁻¹ • (v n.succPNat - w n.succPNat)
  obtain ⟨r, hr⟩ := hazewinkelLog_sub_of_forall_le_rat p hvw
  have hfv : (hazewinkelLog p v).toPowerSeries = (hazewinkelLog p w).toPowerSeries +
      PowerSeries.X ^ N * (PowerSeries.C c + PowerSeries.X * r) := by
    have hcX : c • PowerSeries.X ^ N = PowerSeries.X ^ N * PowerSeries.C c := by
      rw [Algebra.smul_def, PowerSeries.algebraMap_eq, mul_comm]
    linear_combination hr + hcX
  let η : FormalCoordinate K := (hazewinkelLog p w)⁻¹ * hazewinkelLog p v
  have hη_smul : η • hazewinkelFormalGroup p v = hazewinkelFormalGroup p w := by
    rw [hazewinkelFormalGroup_def, hazewinkelFormalGroup_def]
    simp only [η, mul_smul, smul_inv_smul]
  obtain ⟨s, hη_series, hs_c⟩ := exists_toPowerSeries_mul_eq_X_add_X_pow_mul
    (φ := (hazewinkelLog p w)⁻¹) (ψ := hazewinkelLog p v) (by simp) hN0 (by simpa using hfv)
  simp only [map_add, PowerSeries.constantCoeff_C, map_mul, PowerSeries.constantCoeff_X, zero_mul,
    add_zero] at hs_c
  obtain ⟨hord, hhom⟩ := order_and_homogeneousComponent_of_smul_eq hη_smul hN0 hη_series
  refine ⟨hord, ?_⟩
  rw [hhom, hs_c]
  congr 1
  have hcoc := lazardGcd_nsmul_lazardCocycle (R := K) hN0
  rw [lazardGcd_prime_pow hp.out (Nat.succ_ne_zero n)] at hcoc
  have hpc : (p : ℚ) • c = v n.succPNat - w n.succPNat :=
    smul_inv_smul₀ (Nat.cast_ne_zero.2 hp.out.ne_zero) _
  rw [← hcoc, ← Nat.cast_smul_eq_nsmul ℚ, smul_comm c (p : ℚ), ← smul_assoc, hpc]

private theorem universal_hazewinkelIntegralFormalGroup_sub (n : ℕ) :
    let vU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦ MvPolynomial.X (Sum.inl i)
    let wU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦
      if (i : ℕ) ≤ n then MvPolynomial.X (Sum.inl i) else MvPolynomial.X (Sum.inr i)
    let D_U := (hazewinkelIntegralFormalGroup p vU).toPowerSeries -
      (hazewinkelIntegralFormalGroup p wU).toPowerSeries
    (∀ d : Fin 2 →₀ ℕ, d.degree < p ^ (n + 1) → coeff d D_U = 0) ∧
      ∀ d : Fin 2 →₀ ℕ, d.degree = p ^ (n + 1) →
        coeff d D_U =
          -((vU n.succPNat - wU n.succPNat) *
            (lazardCocycle (p ^ (n + 1)) (MvPolynomial (ℕ+ ⊕ ℕ+) ℤ)).coeff d) := by
  intro vU wU D_U
  let ι : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* MvPolynomial (ℕ+ ⊕ ℕ+) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hι_inj : Function.Injective ι := MvPolynomial.map_injective _ Int.cast_injective
  have hrat := hazewinkelFormalGroup_sub_of_forall_le_rat p
    (v := ι ∘ vU) (w := ι ∘ wU) (n := n) (fun i hi ↦ by simp [vU, wU, hi])
  have hmap_DU : D_U.map ι =
      (hazewinkelFormalGroup p (ι ∘ vU)).toPowerSeries -
        (hazewinkelFormalGroup p (ι ∘ wU)).toPowerSeries := by
    rw [map_sub, ← FormalGroup.map_toPowerSeries, ← FormalGroup.map_toPowerSeries,
      map_hazewinkelIntegralFormalGroup, map_hazewinkelIntegralFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  refine ⟨fun d hd ↦ hι_inj ?_, fun d hd ↦ hι_inj ?_⟩
  · rw [map_zero, ← coeff_map, hmap_DU]
    exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le hrat.1)
  · have hcoeff := congrArg (coeff d) hrat.2
    rw [← hmap_DU, coeff_homogeneousComponent, ite_eq_left hd, coeff_map] at hcoeff
    rw [hcoeff, map_neg ι, map_mul ι, map_sub ι, ← MvPolynomial.coeff_map, map_lazardCocycle]
    simp [MvPolynomial.coe_smul]

private theorem hazewinkelIntegralFormalGroup_sub_of_forall_le {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤
      ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries).order ∧
    homogeneousComponent (p ^ (n + 1))
        ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
      -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) R :
          MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  let vU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦ MvPolynomial.X (Sum.inl i)
  let wU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦
    if (i : ℕ) ≤ n then MvPolynomial.X (Sum.inl i) else MvPolynomial.X (Sum.inr i)
  let D_U := (hazewinkelIntegralFormalGroup p vU).toPowerSeries -
    (hazewinkelIntegralFormalGroup p wU).toPowerSeries
  obtain ⟨hDU_ord, hDU_coeff⟩ := universal_hazewinkelIntegralFormalGroup_sub p n
  let ev : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v w)
  have hev_v : ev ∘ vU = v := funext fun i ↦ by simp [ev, vU]
  have hev_w : ev ∘ wU = w := funext fun i ↦ by
    dsimp [ev, wU]
    split_ifs with hi <;> simp [hvw, hi]
  have hD_R : D_U.map ev =
      (hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries := by
    rw [map_sub, ← FormalGroup.map_toPowerSeries, ← FormalGroup.map_toPowerSeries,
      map_hazewinkelIntegralFormalGroup, map_hazewinkelIntegralFormalGroup, hev_v, hev_w]
  refine ⟨nat_le_order fun d hd ↦ ?_, ?_⟩
  · rw [← hD_R, coeff_map, hDU_ord d hd, map_zero]
  · ext d
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · rw [← hD_R, coeff_map, hDU_coeff d hd, map_neg, map_mul, map_sub,
        ← MvPolynomial.coeff_map, map_lazardCocycle]
      simp [ev, MvPolynomial.coe_smul]
    · have h0 : (lazardCocycle (p ^ (n + 1)) R).coeff d = 0 := by
        rw [coeff_lazardCocycle, ite_eq_right]
        rintro ⟨hsum, _, _⟩
        exact hd (by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hsum)
      simp [MvPolynomial.coe_smul, h0]

/-- **Degreewise congruence of Hazewinkel's integral formal group law**: over any commutative ring,
if `v` and `w` agree up to index `n`, then `hazewinkelIntegralFormalGroup p v` and
`hazewinkelIntegralFormalGroup p w` agree strictly below degree `p^(n + 1)`. -/
theorem le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤
      ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries).order :=
  (hazewinkelIntegralFormalGroup_sub_of_forall_le p hvw).1

/-- If `v` and `w` agree on `i ≤ n`, the homogeneous component of degree `p^(n + 1)` of
`hazewinkelIntegralFormalGroup p v - hazewinkelIntegralFormalGroup p w` is
`-(v_{n + 1} - w_{n + 1}) • C_{p^(n + 1)}`. -/
theorem homogeneousComponent_hazewinkelIntegralFormalGroup_sub {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    homogeneousComponent (p ^ (n + 1))
        ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
      -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) R :
          MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) :=
  (hazewinkelIntegralFormalGroup_sub_of_forall_le p hvw).2

/-- **Universal injectivity of Hazewinkel's integral formal group law**: over every commutative ring
`R` (including rings with arbitrary torsion), `hazewinkelIntegralFormalGroup p` is injective. -/
theorem hazewinkelIntegralFormalGroup_injective :
    Function.Injective (hazewinkelIntegralFormalGroup p : (ℕ+ → R) → FormalGroup R) := by
  intro v w h
  suffices ∀ n, ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i from
    funext fun i ↦ this (i : ℕ) i le_rfl
  intro n
  induction n with
  | zero => intro i hi; have := i.pos; omega
  | succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact ih i (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : i = n.succPNat := PNat.coe_injective heq
      have hhom := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p ih
      rw [h, sub_self, map_zero, eq_comm, neg_eq_zero] at hhom
      have hpoly : (v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) R = 0 :=
        MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])
      have h2 : 2 ≤ p ^ (n + 1) :=
        hp.out.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero n) p)
      exact sub_eq_zero.mp ((smul_lazardCocycle_eq_zero_iff h2).mp hpoly)

@[simp]
theorem hazewinkelIntegralFormalGroup_eq_iff {v w : ℕ+ → R} :
    hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w ↔ v = w :=
  (hazewinkelIntegralFormalGroup_injective p).eq_iff

/-- At `v = 0`, `hazewinkelIntegralFormalGroup p 0` is the additive formal group law `𝔾ₐ`. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_zero :
    hazewinkelIntegralFormalGroup p (0 : ℕ+ → R) = FormalGroup.𝔾ₐ := by
  have hQ0 : (Int.castRingHom ℚ) ∘ (0 : ℕ+ → ℤ) = 0 := funext fun _ ↦ map_zero _
  have hR0 : (Int.castRingHom R) ∘ (0 : ℕ+ → ℤ) = 0 := funext fun _ ↦ map_zero _
  have hQ : hazewinkelFormalGroup p (0 : ℕ+ → ℚ) = FormalGroup.𝔾ₐ := by
    rw [eq_comm, eq_hazewinkelFormalGroup_iff, FormalGroup.log_𝔾ₐ]
    ext k
    rcases eq_or_ne k 1 with rfl | hk1
    · simp
    · by_cases hpow : ∃ n, p ^ n = k
      · obtain ⟨_ | n, rfl⟩ := hpow
        · exact absurd rfl hk1
        · rw [PowerSeries.coeff_X, ite_eq_right hk1,
            coeff_hazewinkelLog_pow _ hp.out.one_lt (n + 1)]
          have h0 := natCast_mul_hazewinkelLogCoeff_succ (0 : ℕ+ → ℚ) hp.out.ne_zero n
          rw [sum_range_succ'] at h0
          simp only [Pi.zero_apply, zero_pow (pow_ne_zero _ hp.out.ne_zero), mul_zero,
            sum_const_zero, add_zero] at h0
          have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
          exact ((mul_eq_zero.mp h0).resolve_left hp0).symm
      · push Not at hpow
        rw [PowerSeries.coeff_X, ite_eq_right hk1, coeff_hazewinkelLog_eq_zero _ hpow]
  have hZ : hazewinkelIntegralFormalGroup p (0 : ℕ+ → ℤ) = FormalGroup.𝔾ₐ := by
    apply FormalGroup.map_injective (f := Int.castRingHom ℚ) Int.cast_injective
    dsimp only
    rw [map_hazewinkelIntegralFormalGroup, FormalGroup.map_𝔾ₐ,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup, hQ0, hQ]
  have hR := congrArg (fun F : FormalGroup ℤ ↦ F.map (Int.castRingHom R)) hZ
  rw [map_hazewinkelIntegralFormalGroup, FormalGroup.map_𝔾ₐ, hR0] at hR
  exact hR

end Comparison

/-! ### Integrality and classification of strict `p`-typical coordinate changes -/

section Classification

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

omit p hp in
/-- If every degree-`m` mixed coefficient of `r • C_m` (`m ≥ 2`) in `B` lies in `ι.range`, then `r`
lies in `ι.range`, because the coefficients `m.choose i / d_m` have greatest common divisor `1`. -/
private theorem mem_range_of_coeff_smul_lazardCocycle_mem {A B : Type*} [CommRing A] [CommRing B]
    (ι : A →+* B) {m : ℕ} (hm : 2 ≤ m) {r : B}
    (hr : ∀ i ∈ Icc 1 (m - 1),
      (r • lazardCocycle m B).coeff (Finsupp.single 0 i + Finsupp.single 1 (m - i)) ∈ ι.range) :
    r ∈ ι.range := by
  obtain ⟨c, hc⟩ :=
    Finset.gcd_eq_one_iff_exists_sum_natCast_mul_eq_one.1 (gcd_choose_div_lazardGcd_eq_one hm)
  have h1 : (∑ i ∈ Icc 1 (m - 1),
      ((m.choose i / lazardGcd m : ℕ) : B) * (c i : B)) = 1 := by
    simpa only [map_sum, map_mul, map_natCast, Int.coe_castRingHom, map_one] using
      congrArg (Int.castRingHom B) hc
  have hsum : ∑ i ∈ Icc 1 (m - 1),
      (c i : B) * (r • lazardCocycle m B).coeff (Finsupp.single 0 i + Finsupp.single 1 (m - i)) =
        r := by
    calc ∑ i ∈ Icc 1 (m - 1),
          (c i : B) * (r • lazardCocycle m B).coeff
            (Finsupp.single 0 i + Finsupp.single 1 (m - i))
        = (∑ i ∈ Icc 1 (m - 1), ((m.choose i / lazardGcd m : ℕ) : B) * (c i : B)) * r := by
          rw [sum_mul]
          refine sum_congr rfl fun i hi ↦ ?_
          rw [mem_Icc] at hi
          rw [MvPolynomial.coeff_smul,
            coeff_single_add_single_lazardCocycle (by omega) (by omega), smul_eq_mul]
          ring
      _ = r := by rw [h1, one_mul]
  rw [← hsum]
  exact ι.range.sum_mem fun i hi ↦ ι.range.mul_mem ⟨c i, map_intCast ι (c i)⟩ (hr i hi)

private theorem exists_universal_pTypicalStrictCoordinate_smul_stage
    (GZ : FormalGroup (MvPolynomial (ℕ+ ⊕ ℕ+) ℤ))
    {wQ : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℚ}
    (hwQ : GZ.map (MvPolynomial.map (Int.castRingHom ℚ)) = hazewinkelFormalGroup p wQ) :
    ∀ n (i : ℕ+), (i : ℕ) ≤ n →
      wQ i ∈ (MvPolynomial.map (Int.castRingHom ℚ) :
        MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* MvPolynomial (ℕ+ ⊕ ℕ+) ℚ).range := by
  let ι : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* MvPolynomial (ℕ+ ⊕ ℕ+) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  intro n
  induction n with
  | zero => intro i hi; have := i.pos; omega
  | succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact ih i (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : i = n.succPNat := PNat.coe_injective heq
      let w_truncZ : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun j ↦
        if hj : (j : ℕ) ≤ n then (ih j hj).choose else 0
      have htrunc : ∀ j : ℕ+, (j : ℕ) ≤ n → wQ j = ι (w_truncZ j) := fun j hj ↦ by
        dsimp only [w_truncZ]
        rw [dite_eq_left hj]
        exact (ih j hj).choose_spec.symm
      have hhom := (hazewinkelFormalGroup_sub_of_forall_le_rat p (v := wQ)
        (w := ι ∘ w_truncZ) (n := n) htrunc).2
      have hw_trunc0 : (ι ∘ w_truncZ) n.succPNat = 0 := by simp [w_truncZ]
      rw [hw_trunc0, sub_zero, ← hwQ,
        ← hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup p (ι ∘ w_truncZ),
        ← map_hazewinkelIntegralFormalGroup] at hhom
      have h2 : 2 ≤ p ^ (n + 1) :=
        hp.out.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero n) p)
      refine mem_range_of_coeff_smul_lazardCocycle_mem ι h2 fun j hj ↦ ?_
      rw [mem_Icc] at hj
      let d : Fin 2 →₀ ℕ := Finsupp.single 0 j + Finsupp.single 1 (p ^ (n + 1) - j)
      have hd : d.degree = p ^ (n + 1) := by
        simp [d, Finsupp.degree_eq_sum, Fin.sum_univ_two]; omega
      refine ⟨-coeff d (GZ.toPowerSeries -
        (hazewinkelIntegralFormalGroup p w_truncZ).toPowerSeries), ?_⟩
      have hcoeff := congrArg (coeff d) hhom
      rw [coeff_homogeneousComponent, ite_eq_left hd, FormalGroup.map_toPowerSeries,
        FormalGroup.map_toPowerSeries, ← map_sub (MvPowerSeries.map ι), coeff_map, map_neg,
        MvPolynomial.coeff_coe] at hcoeff
      rw [map_neg, hcoeff, neg_neg]

/-- Universal integral descent of strict `p`-typical coordinate change over `ℤ[v₁, …][t₁, …]`. -/
private theorem exists_universal_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup :
    ∃ wZ : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ,
      ((hazewinkelIntegralFormalGroup p
          (fun i ↦ (MvPolynomial.X (Sum.inl i) :
            MvPolynomial (ℕ+ ⊕ ℕ+) ℤ))).pTypicalStrictCoordinate
          p (fun i ↦ (MvPolynomial.X (Sum.inr i) : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ))) •
        hazewinkelIntegralFormalGroup p
          (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ)) =
      hazewinkelIntegralFormalGroup p wZ := by
  let UZ := MvPolynomial (ℕ+ ⊕ ℕ+) ℤ
  let UQ := MvPolynomial (ℕ+ ⊕ ℕ+) ℚ
  let ι : UZ →+* UQ := MvPolynomial.map (Int.castRingHom ℚ)
  have hι_inj : Function.Injective ι := MvPolynomial.map_injective _ Int.cast_injective
  let vZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inl i)
  let tZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inr i)
  let FZ := hazewinkelIntegralFormalGroup p vZ
  set GZ := (FZ.pTypicalStrictCoordinate p tZ) • FZ
  have hmap_GZ : GZ.map ι =
      ((hazewinkelFormalGroup p (ι ∘ vZ)).pTypicalStrictCoordinate p (ι ∘ tZ)) •
        hazewinkelFormalGroup p (ι ∘ vZ) := by
    rw [FormalGroup.map_smul, FormalGroup.map_pTypicalStrictCoordinate,
      map_hazewinkelIntegralFormalGroup, hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  obtain ⟨wQ, hwQ, _⟩ :=
    existsUnique_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup hp.out.one_lt (ι ∘ vZ) (ι ∘ tZ)
  have hwQ_mem := exists_universal_pTypicalStrictCoordinate_smul_stage p GZ (hmap_GZ.trans hwQ)
  choose wZ hwZ using fun i : ℕ+ ↦ RingHom.mem_range.mp (hwQ_mem i.val i le_rfl)
  refine ⟨wZ, FormalGroup.map_injective hι_inj ?_⟩
  dsimp only
  rw [hmap_GZ, hwQ, map_hazewinkelIntegralFormalGroup,
    hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  congr 1
  exact funext fun i ↦ (hwZ i).symm

/-- **Integrality of strict `p`-typical coordinate changes**: over every commutative ring `R`,
transporting `hazewinkelIntegralFormalGroup p v` along its `p`-typical strict coordinate `t`
produces `hazewinkelIntegralFormalGroup p w` for a unique sequence `w : ℕ+ → R`. -/
theorem existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup
    (v t : ℕ+ → R) :
    ∃! w : ℕ+ → R,
      ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
          hazewinkelIntegralFormalGroup p v =
        hazewinkelIntegralFormalGroup p w := by
  obtain ⟨wZ, hwZ⟩ :=
    exists_universal_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p
  let ev : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v t)
  have hev_v : ev ∘ (fun i ↦ (MvPolynomial.X (Sum.inl i) : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ)) = v :=
    funext fun i ↦ by simp [ev]
  have hev_t : ev ∘ (fun i ↦ (MvPolynomial.X (Sum.inr i) : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ)) = t :=
    funext fun i ↦ by simp [ev]
  have hR : ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
      hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p (ev ∘ wZ) := by
    have h := congrArg (fun F : FormalGroup (MvPolynomial (ℕ+ ⊕ ℕ+) ℤ) ↦ F.map ev) hwZ
    simpa only [FormalGroup.map_smul, FormalGroup.map_pTypicalStrictCoordinate,
      map_hazewinkelIntegralFormalGroup, hev_v, hev_t] using h
  exact ⟨ev ∘ wZ, hR, fun w' hw' ↦
    hazewinkelIntegralFormalGroup_injective p (hw'.symm.trans hR)⟩

/-- Two integral Hazewinkel formal group laws that agree below a non-`p`-power degree `m ≠ 0`
automatically agree through degree `m`. -/
private theorem succ_le_order_hazewinkelIntegralFormalGroup_sub_of_not_pow {v w : ℕ+ → R} {m : ℕ}
    (hpow : ∀ k : ℕ+, p ^ (k : ℕ) ≠ m) (hm0 : m ≠ 0)
    (hord : (m : ℕ∞) ≤
      ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries).order) :
    ((m + 1 : ℕ) : ℕ∞) ≤
      ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries).order := by
  have hw_eq : ∀ r : ℕ, ∀ i : ℕ+, (i : ℕ) ≤ r → p ^ (i : ℕ) ≤ m → v i = w i := by
    intro r
    induction r with
    | zero => intro i hi _; have := i.pos; omega
    | succ r ihr =>
      intro i hi hpim
      rcases lt_or_eq_of_le hi with hlt | heq
      · exact ihr i (Nat.lt_succ_iff.mp hlt) hpim
      · obtain rfl : i = r.succPNat := PNat.coe_injective heq
        have hplt : p ^ (r + 1) < m := lt_of_le_of_ne hpim (hpow r.succPNat)
        have hhom := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p (v := v)
          (w := w) (n := r) fun j hj ↦
            ihr j hj ((Nat.pow_le_pow_right hp.out.pos (Nat.le_succ_of_le hj)).trans hpim)
        have hzero : homogeneousComponent (p ^ (r + 1))
            ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
              (hazewinkelIntegralFormalGroup p w).toPowerSeries) = 0 :=
          homogeneousComponent_of_lt_order_eq_zero ((Nat.cast_lt.mpr hplt).trans_le hord)
        rw [hzero, eq_comm, neg_eq_zero] at hhom
        have hpoly : (v r.succPNat - w r.succPNat) • lazardCocycle (p ^ (r + 1)) R = 0 :=
          MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])
        have h2 : 2 ≤ p ^ (r + 1) :=
          hp.out.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero r) p)
        exact sub_eq_zero.mp ((smul_lazardCocycle_eq_zero_iff h2).mp hpoly)
  let N := Nat.log p m
  have hN_le : ∀ i : ℕ+, (i : ℕ) ≤ N → v i = w i := fun i hi ↦
    hw_eq N i hi ((Nat.pow_le_pow_right hp.out.pos hi).trans (Nat.pow_log_le_self p hm0))
  exact (Nat.cast_le.mpr (Nat.lt_pow_succ_log_self hp.out.one_lt m)).trans
    (le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le p hN_le)

/-- Vanishing of the first non-`p`-power discrepancy between `φ⁻¹` and `F_v.pTypicalStrictCurve p t`
when primes `q ≠ p` are units in `R`. -/
private theorem coeff_eq_of_smul_hazewinkelIntegralFormalGroup_eq
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {v w t : ℕ+ → R}
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1)
    (hsmul : φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w)
    {m : ℕ} (hm2 : 2 ≤ m) (hpow : ∀ k : ℕ+, p ^ (k : ℕ) ≠ m)
    (hbelow : ∀ j < m, PowerSeries.coeff j φ⁻¹.toPowerSeries =
      PowerSeries.coeff j
        ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries) :
    PowerSeries.coeff m φ⁻¹.toPowerSeries =
      PowerSeries.coeff m
        ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries := by
  let F_v := hazewinkelIntegralFormalGroup p v
  let φ_t := F_v.pTypicalStrictCoordinate p t
  obtain ⟨w_t, hw_t, _⟩ :=
    existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p v t
  have hη_smul : (φ * φ_t⁻¹) • hazewinkelIntegralFormalGroup p w_t =
      hazewinkelIntegralFormalGroup p w := by
    rw [← hw_t, mul_smul, inv_smul_smul, hsmul]
  set c := PowerSeries.coeff m (F_v.pTypicalStrictCurve p t).toPowerSeries -
    PowerSeries.coeff m φ⁻¹.toPowerSeries
  obtain ⟨r, hr⟩ : PowerSeries.X ^ m ∣
      (F_v.pTypicalStrictCurve p t).toPowerSeries - φ⁻¹.toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun j hj ↦ by rw [map_sub, hbelow j hj, sub_self]
  have hr0 : PowerSeries.constantCoeff r = c := by
    have h := congrArg (PowerSeries.coeff m) hr
    simpa [c, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_zero_eq_constantCoeff_apply] using h.symm
  obtain ⟨s, hη_series, hs_c⟩ := exists_toPowerSeries_mul_eq_X_add_X_pow_mul (ψ := φ_t⁻¹) hφ
    (by omega : m ≠ 0) (r := r) (by
      rw [FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]
      linear_combination hr)
  obtain ⟨hF_ord, hhom⟩ :=
    order_and_homogeneousComponent_of_smul_eq hη_smul (by omega : m ≠ 0) hη_series
  have hhom0 : homogeneousComponent m
      ((hazewinkelIntegralFormalGroup p w_t).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries) = 0 :=
    homogeneousComponent_of_lt_order_eq_zero ((Nat.cast_lt.mpr (Nat.lt_succ_self m)).trans_le
      (succ_le_order_hazewinkelIntegralFormalGroup_sub_of_not_pow p hpow (by omega) hF_ord))
  rw [hhom0, hs_c, hr0, eq_comm, neg_eq_zero] at hhom
  have hpoly : ((lazardGcd m : R) * c) • lazardCocycle m R = 0 := by
    have h1 : c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ m - MvPolynomial.X 0 ^ m -
        MvPolynomial.X 1 ^ m : MvPolynomial (Fin 2) R) = 0 :=
      MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])
    rwa [← lazardGcd_nsmul_lazardCocycle (R := R) (by omega : m ≠ 0),
      ← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm] at h1
  have hgcd_c : (lazardGcd m : R) * c = 0 := (smul_lazardCocycle_eq_zero_iff hm2).mp hpoly
  have hunit : IsUnit (lazardGcd m : R) := by
    by_cases hpp : IsPrimePow m
    · obtain ⟨q, k, hq, hk, hmk⟩ := (isPrimePow_nat_iff m).1 hpp
      rw [← hmk, lazardGcd_prime_pow hq hk.ne']
      exact hlocal q hq fun hqp ↦ hpow ⟨k, hk⟩ (hqp ▸ hmk)
    · rw [lazardGcd_eq_one_of_not_isPrimePow (by omega) hpp, Nat.cast_one]
      exact isUnit_one
  exact (sub_eq_zero.mp (hunit.mul_right_eq_zero.mp hgcd_c)).symm

/-- Recursive approximations to the `p`-typical parameters of an inverse coordinate `ψ`. -/
private def pTypicalInvParamsStage (p : ℕ) (F : FormalGroup R) (ψ : PowerSeries R) :
    ℕ → (ℕ+ → R)
  | 0 => 0
  | n + 1 => Function.update (pTypicalInvParamsStage p F ψ n) n.succPNat
      (PowerSeries.coeff (p ^ (n + 1)) ψ -
        PowerSeries.coeff (p ^ (n + 1))
          (F.pTypicalStrictCurve p (pTypicalInvParamsStage p F ψ n)).toPowerSeries)

omit hp in
private theorem pTypicalInvParamsStage_eq_zero_of_lt (F : FormalGroup R) (ψ : PowerSeries R) :
    ∀ n (i : ℕ+), n < (i : ℕ) → pTypicalInvParamsStage p F ψ n i = 0
  | 0, _, _ => rfl
  | n + 1, i, hi => by
    rw [pTypicalInvParamsStage, Function.update_of_ne (by intro h; subst h; simp at hi)]
    exact pTypicalInvParamsStage_eq_zero_of_lt F ψ n i (by omega)

omit hp in
private theorem pTypicalInvParamsStage_eq_of_le (F : FormalGroup R) (ψ : PowerSeries R)
    {n m : ℕ} (hnm : n ≤ m) {i : ℕ+} (hi : (i : ℕ) ≤ n) :
    pTypicalInvParamsStage p F ψ m i = pTypicalInvParamsStage p F ψ n i := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ihm =>
    rw [pTypicalInvParamsStage,
      Function.update_of_ne (by intro h; subst h; simp at hi; omega), ihm]

private theorem coeff_pow_succ_pTypicalInvParamsStage (F : FormalGroup R) (ψ : PowerSeries R)
    (n : ℕ) :
    PowerSeries.coeff (p ^ (n + 1)) ψ =
      PowerSeries.coeff (p ^ (n + 1))
        (F.pTypicalStrictCurve p
          (fun i ↦ pTypicalInvParamsStage p F ψ (i : ℕ) i)).toPowerSeries := by
  have hp1 : 1 < p := hp.out.one_lt
  let s_n := pTypicalInvParamsStage p F ψ n
  let s_succ := pTypicalInvParamsStage p F ψ (n + 1)
  have hprev :
      PowerSeries.coeff (p ^ (n + 1))
        (F.pTypicalStrictCurve p (fun i ↦ pTypicalInvParamsStage p F ψ (i : ℕ) i)).toPowerSeries =
      PowerSeries.coeff (p ^ (n + 1)) (F.pTypicalStrictCurve p s_succ).toPowerSeries :=
    F.coeff_pTypicalStrictCurve_congr hp1 fun i hi ↦ by
      have hle : (i : ℕ) ≤ n + 1 := by
        by_contra! hgt
        have := Nat.pow_lt_pow_right hp1 hgt
        omega
      exact (pTypicalInvParamsStage_eq_of_le p F ψ hle le_rfl).symm
  have hstep := F.coeff_pow_succ_pTypicalStrictCurve_sub hp1
    (t := s_succ) (t' := s_n) (n := n) fun i hi ↦ by
      dsimp [s_succ, s_n]
      rw [pTypicalInvParamsStage, Function.update_of_ne (by intro h; subst h; simp at hi)]
  have hs_succ : s_succ n.succPNat =
      PowerSeries.coeff (p ^ (n + 1)) ψ -
        PowerSeries.coeff (p ^ (n + 1)) (F.pTypicalStrictCurve p s_n).toPowerSeries := by
    dsimp [s_succ, s_n]
    rw [pTypicalInvParamsStage, Function.update_self]
  have hs_n : s_n n.succPNat = 0 :=
    pTypicalInvParamsStage_eq_zero_of_lt p F ψ n n.succPNat (Nat.lt_succ_self n)
  rw [map_sub, hs_succ, hs_n, sub_zero] at hstep
  rw [hprev]
  linear_combination -hstep

/-- **Classification of strict isomorphisms between Hazewinkel laws over `p`-local rings**:
suppose every prime `q ≠ p` is invertible in `R`, and let `φ` be a strict coordinate over `R`
such that `φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w`. Then `φ` is
`pTypicalStrictCoordinate p t` for a unique sequence `t : ℕ+ → R`. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {v w : ℕ+ → R}
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1)
    (hsmul : φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) :
    ∃! t : ℕ+ → R, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t := by
  let F_v := hazewinkelIntegralFormalGroup p v
  let t : ℕ+ → R := fun i ↦ pTypicalInvParamsStage p F_v φ⁻¹.toPowerSeries (i : ℕ) i
  have hmatch : ∀ d : ℕ, PowerSeries.coeff d φ⁻¹.toPowerSeries =
      PowerSeries.coeff d (F_v.pTypicalStrictCurve p t).toPowerSeries := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      rcases d with _ | _ | d
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, φ⁻¹.constantCoeff_toPowerSeries,
          (F_v.pTypicalStrictCurve p t).constantCoeff_toPowerSeries]
      · have hψ1 : PowerSeries.coeff 1 φ⁻¹.toPowerSeries = 1 := by
          rw [← FormalCoordinate.val_linearCoeff, map_inv, hφ, inv_one, Units.val_one]
        rw [hψ1, F_v.coeff_one_pTypicalStrictCurve]
      · set m := d + 2
        by_cases hpow : ∃ k : ℕ+, p ^ (k : ℕ) = m
        · obtain ⟨k, hkm⟩ := hpow
          obtain ⟨n, hn⟩ : ∃ n, (k : ℕ) = n + 1 :=
            ⟨k.natPred, (Nat.succ_pred_eq_of_pos k.pos).symm⟩
          have hk_eq : k = n.succPNat := PNat.coe_injective hn
          rw [← hkm, hk_eq, Nat.succPNat_coe]
          exact coeff_pow_succ_pTypicalInvParamsStage p F_v φ⁻¹.toPowerSeries n
        · push Not at hpow
          exact coeff_eq_of_smul_hazewinkelIntegralFormalGroup_eq p hlocal hφ hsmul
            (by omega : 2 ≤ m) hpow ih
  have hφ_eq : φ = F_v.pTypicalStrictCoordinate p t := by
    apply inv_injective
    ext1
    rw [FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]
    exact PowerSeries.ext hmatch
  exact ⟨t, hφ_eq, fun t' ht' ↦
    F_v.pTypicalStrictCoordinate_injective hp.out.one_lt (ht'.symm.trans hφ_eq)⟩

/-- When every prime `q ≠ p` is invertible in `R`, a strict formal coordinate `φ` transports
`hazewinkelIntegralFormalGroup p v` into `Set.range (hazewinkelIntegralFormalGroup p)` if and only
if `φ` is `(hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t` for some
`t : ℕ+ → R`. -/
theorem exists_hazewinkelIntegralFormalGroup_eq_smul_iff
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (v : ℕ+ → R)
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1) :
    (∃ w : ℕ+ → R, φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) ↔
      ∃ t : ℕ+ → R, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t := by
  refine ⟨fun ⟨w, hw⟩ ↦ ?_, fun ⟨t, ht⟩ ↦ ?_⟩
  · obtain ⟨t, ht, _⟩ := existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ hw
    exact ⟨t, ht⟩
  · subst ht
    obtain ⟨w, hw, _⟩ :=
      existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p v t
    exact ⟨w, hw⟩

end Classification

end TauCeti
