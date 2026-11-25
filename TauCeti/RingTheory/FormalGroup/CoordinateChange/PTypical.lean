/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.FormalGroup.Curve.Arithmetic
import TauCeti.Data.Nat.Pow

/-!
# Strict `p`-typical curves and coordinate changes on formal group laws

For a formal group law `F` over an arbitrary commutative ring `R`, `p > 1`, and a parameter family
`t : ℕ+ → R`, the finite formal-group partial sums `X +_F t₁ X^p +_F ⋯ +_F tₙ X^(pⁿ)` stabilize
coefficientwise to the strict `p`-typical curve `F.pTypicalStrictCurve p t` (defaulting to the
tautological curve `X` when `p ≤ 1`). Taking its compositional inverse defines the strict
`p`-typical formal coordinate `F.pTypicalStrictCoordinate p t`.

Both constructions commute with arbitrary ring homomorphisms (`FormalGroup.map_pTypicalStrictCurve`,
`FormalGroup.map_pTypicalStrictCoordinate`), agree on a commutative formal group law below degree
`p^(n + 1)` with the finite sum `∑^F_{j ≤ n} t_j X^(p^j)` with `t₀ = 1`
(`FormalGroup.coeff_pTypicalStrictCurve_eq_coeff_sum`), satisfy degreewise truncation congruence and
a leading-difference formula in degree `p^(n + 1)`
(`FormalGroup.coeff_pow_succ_pTypicalStrictCurve_sub`), and are injective in `t` over every
commutative ring when `1 < p` (`FormalGroup.pTypicalStrictCurve_injective`,
`FormalGroup.pTypicalStrictCoordinate_injective`).

## Main definitions

* `FormalGroup.pTypicalStrictCurve`: the strict `p`-typical curve `X +_F ∑^F_{i ≥ 1} t_i X^(p^i)`
  on `F`.
* `FormalGroup.pTypicalStrictCoordinate`: the strict formal coordinate whose inverse power series is
  `F.pTypicalStrictCurve p t`.

## Main results

* `FormalGroup.map_pTypicalStrictCurve`, `FormalGroup.map_pTypicalStrictCoordinate`: naturality
  under arbitrary ring homomorphisms.
* `FormalGroup.coeff_pTypicalStrictCurve_eq_coeff_tautologicalCurve_add_sum`,
  `FormalGroup.coeff_pTypicalStrictCurve_eq_coeff_sum`: finite-sum approximation on commutative
  laws.
* `FormalGroup.coeff_pow_succ_pTypicalStrictCurve_sub`: leading difference `t_{n + 1} - t'_{n + 1}`
  in degree `p^(n + 1)`.
* `FormalGroup.pTypicalStrictCurve_injective`, `FormalGroup.pTypicalStrictCoordinate_injective`:
  universal injectivity in `t` for `1 < p`.

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, 1969.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2 and Chapter III,
  §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open Finset

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

private def pTypicalStrictCurveStage (F : FormalGroup R) (p : ℕ) (hp : 1 < p) (t : ℕ+ → R) :
    ℕ → F.Curve
  | 0 => F.tautologicalCurve
  | n + 1 => pTypicalStrictCurveStage F p hp t n +
      F.monomialCurve (p ^ (n + 1)) (pow_ne_zero _ (Nat.ne_zero_of_lt hp)) (t n.succPNat)

private theorem coeff_pTypicalStrictCurveStage_succ_of_lt (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t (n + 1)).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries :=
  Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero _ _ hk fun _ hi ↦ by
    simp [PowerSeries.coeff_X_pow, hi.ne]

private theorem coeff_pTypicalStrictCurveStage_eq_of_le (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n m k : ℕ} (hnm : n ≤ m) (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t m).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
    rw [coeff_pTypicalStrictCurveStage_succ_of_lt F hp t
      (hk.trans_le (Nat.pow_le_pow_right (by omega) (by omega))), ih]

private theorem pTypicalStrictCurveStage_congr (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    pTypicalStrictCurveStage F p hp t n = pTypicalStrictCurveStage F p hp t' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pTypicalStrictCurveStage, pTypicalStrictCurveStage,
      ih (fun i hi ↦ ht i (hi.trans (Nat.le_succ n))), ht n.succPNat le_rfl]

private theorem map_pTypicalStrictCurveStage (F : FormalGroup R) {p : ℕ} (hp : 1 < p) (t : ℕ+ → R)
    (f : R →+* S) (n : ℕ) :
    Curve.map f (pTypicalStrictCurveStage F p hp t n) =
      pTypicalStrictCurveStage (F.map f) p hp (f ∘ t) n := by
  induction n with
  | zero => exact F.map_tautologicalCurve f
  | succ n ih =>
    rw [pTypicalStrictCurveStage, map_add, ih, F.map_monomialCurve, pTypicalStrictCurveStage,
      Function.comp_apply]

/-- **The `p`-typical strict curve** `X +_F t₁ X^p +_F t₂ X^(p²) +_F ⋯` on `F` (`X` if `p ≤ 1`). -/
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
  simp [pTypicalStrictCurve, not_lt.mpr hp]

private theorem coeff_pTypicalStrictCurve_eq_stage (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries := by
  rw [pTypicalStrictCurve, dite_eq_left hp, PowerSeries.coeff_mk]
  rcases le_total n k with hnk | hkn
  · exact coeff_pTypicalStrictCurveStage_eq_of_le F hp t hnk hk
  · exact (coeff_pTypicalStrictCurveStage_eq_of_le F hp t hkn
      (Nat.lt_pow_add_one_self hp k)).symm

/-- On a commutative formal group law `F`, `F.pTypicalStrictCurve p t` agrees below degree
`p ^ (n + 1)` with `X +_F ∑^F_{i < n} t_{i + 1} X ^ (p ^ (i + 1))`. -/
theorem coeff_pTypicalStrictCurve_eq_coeff_tautologicalCurve_add_sum (F : FormalGroup R)
    [F.IsComm] {p : ℕ} (hp : 1 < p) (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (F.tautologicalCurve + ∑ i ∈ range n,
        F.monomialCurve (p ^ (i + 1)) (pow_ne_zero _ (Nat.ne_zero_of_lt hp))
          (t i.succPNat)).toPowerSeries := by
  rw [coeff_pTypicalStrictCurve_eq_stage F hp t hk]
  clear hk
  congr 2
  induction n with
  | zero => simp [pTypicalStrictCurveStage]
  | succ n ih => rw [pTypicalStrictCurveStage, ih, sum_range_succ, add_assoc]

/-- On a commutative formal group law `F`, `F.pTypicalStrictCurve p t` agrees below degree
`p ^ (n + 1)` with `∑^F_{j ≤ n} t_j X ^ (p ^ j)` (setting `t₀ = 1`). -/
theorem coeff_pTypicalStrictCurve_eq_coeff_sum (F : FormalGroup R) [F.IsComm] {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (∑ j ∈ range (n + 1),
        F.monomialCurve (p ^ j) (pow_ne_zero j (Nat.ne_zero_of_lt hp))
          (Nat.casesOn j 1 fun m ↦ t m.succPNat)).toPowerSeries := by
  rw [coeff_pTypicalStrictCurve_eq_coeff_tautologicalCurve_add_sum F hp t hk,
    sum_range_succ', add_comm]
  simp

/-- The linear coefficient of `F.pTypicalStrictCurve p t` is `1`. -/
@[simp] theorem coeff_one_pTypicalStrictCurve (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    PowerSeries.coeff 1 (F.pTypicalStrictCurve p t).toPowerSeries = 1 := by
  by_cases hp : 1 < p
  · rw [coeff_pTypicalStrictCurve_eq_stage F hp t (n := 0) (by simpa using hp)]
    simp [pTypicalStrictCurveStage]
  · rw [F.pTypicalStrictCurve_of_le_one (by omega)]; simp

/-- **The strict `p`-typical formal coordinate** whose inverse is `F.pTypicalStrictCurve p t`. -/
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
theorem pTypicalStrictCoordinate_of_le_one (F : FormalGroup R) {p : ℕ} (hp : p ≤ 1) (t : ℕ+ → R) :
    F.pTypicalStrictCoordinate p t = 1 := by
  apply inv_injective; ext1
  rw [toPowerSeries_inv_pTypicalStrictCoordinate, F.pTypicalStrictCurve_of_le_one hp, inv_one,
    TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]

/-- `F.pTypicalStrictCoordinate p t` has linear coefficient `1` as a unit. -/
@[simp] theorem linearCoeff_pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    TauCeti.FormalCoordinate.linearCoeff (F.pTypicalStrictCoordinate p t) = 1 := by
  apply inv_injective; rw [← map_inv, inv_one]; ext
  rw [TauCeti.FormalCoordinate.val_linearCoeff, toPowerSeries_inv_pTypicalStrictCoordinate,
    F.coeff_one_pTypicalStrictCurve, Units.val_one]

/-- The linear coefficient of `F.pTypicalStrictCoordinate p t` is `1`. -/
@[simp] theorem coeff_one_pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    PowerSeries.coeff 1 (F.pTypicalStrictCoordinate p t).toPowerSeries = 1 := by
  rw [← TauCeti.FormalCoordinate.val_linearCoeff, F.linearCoeff_pTypicalStrictCoordinate,
    Units.val_one]

/-- `F.pTypicalStrictCoordinate p t` lies in the subgroup of strict coordinates. -/
theorem pTypicalStrictCoordinate_mem_ker_linearCoeff (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) :
    F.pTypicalStrictCoordinate p t ∈ (TauCeti.FormalCoordinate.linearCoeff (R := R)).ker :=
  F.linearCoeff_pTypicalStrictCoordinate p t

/-- At `t = 0`, `F.pTypicalStrictCurve p 0` is the tautological curve `X`. -/
@[simp] theorem pTypicalStrictCurve_zero (F : FormalGroup R) (p : ℕ) :
    F.pTypicalStrictCurve p 0 = F.tautologicalCurve := by
  by_cases hp : 1 < p
  · have hstage (n : ℕ) : pTypicalStrictCurveStage F p hp 0 n = F.tautologicalCurve := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pTypicalStrictCurveStage, ih, Pi.zero_apply, F.monomialCurve_zero, _root_.add_zero]
    ext k; rw [pTypicalStrictCurve, dite_eq_left hp, PowerSeries.coeff_mk, hstage]
  · exact F.pTypicalStrictCurve_of_le_one (by omega) 0

/-- At `t = 0`, `F.pTypicalStrictCoordinate p 0` is the identity coordinate `1`. -/
@[simp] theorem pTypicalStrictCoordinate_zero (F : FormalGroup R) (p : ℕ) :
    F.pTypicalStrictCoordinate p 0 = 1 := by
  apply inv_injective; ext1
  rw [toPowerSeries_inv_pTypicalStrictCoordinate, F.pTypicalStrictCurve_zero, inv_one,
    TauCeti.FormalCoordinate.toPowerSeries_one, toPowerSeries_tautologicalCurve]

/-- `pTypicalStrictCurve` commutes with arbitrary ring homomorphisms. -/
@[simp] theorem map_pTypicalStrictCurve (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R) (f : R →+* S) :
    Curve.map f (F.pTypicalStrictCurve p t) = (F.map f).pTypicalStrictCurve p (f ∘ t) := by
  by_cases hp : 1 < p
  · ext k
    have hk : k < p ^ (k + 1) := Nat.lt_pow_add_one_self hp k
    rw [Curve.toPowerSeries_map, PowerSeries.coeff_map,
      coeff_pTypicalStrictCurve_eq_stage F hp t hk,
      coeff_pTypicalStrictCurve_eq_stage (F.map f) hp (f ∘ t) hk,
      ← map_pTypicalStrictCurveStage F hp t f k, Curve.toPowerSeries_map, PowerSeries.coeff_map]
  · rw [F.pTypicalStrictCurve_of_le_one (by omega),
      (F.map f).pTypicalStrictCurve_of_le_one (by omega), F.map_tautologicalCurve]

/-- `pTypicalStrictCoordinate` commutes with arbitrary ring homomorphisms. -/
@[simp] theorem map_pTypicalStrictCoordinate (F : FormalGroup R) (p : ℕ) (t : ℕ+ → R)
    (f : R →+* S) : TauCeti.FormalCoordinate.map f (F.pTypicalStrictCoordinate p t) =
      (F.map f).pTypicalStrictCoordinate p (f ∘ t) := by
  apply inv_injective; rw [← map_inv]; ext1
  rw [TauCeti.FormalCoordinate.toPowerSeries_map, toPowerSeries_inv_pTypicalStrictCoordinate,
    toPowerSeries_inv_pTypicalStrictCoordinate, ← Curve.toPowerSeries_map,
    F.map_pTypicalStrictCurve]

/-- On `𝔾ₐ`, `(𝔾ₐ.pTypicalStrictCurve p t)(X)` is `X + ∑_{n ≥ 1} tₙ X^(pⁿ)`. -/
theorem coeff_pTypicalStrictCurve_𝔾ₐ {p : ℕ} (hp : 1 < p) (t : ℕ+ → R) (k : ℕ) :
    PowerSeries.coeff k ((𝔾ₐ (R := R)).pTypicalStrictCurve p t).toPowerSeries =
      if k = 1 then 1
      else if h : p ^ Nat.log p k = k ∧ 0 < Nat.log p k then t (⟨Nat.log p k, h.right⟩ : ℕ+)
      else 0 := by
  have hstage (n : ℕ) : (pTypicalStrictCurveStage (𝔾ₐ (R := R)) p hp t n).toPowerSeries =
      PowerSeries.X + ∑ i ∈ range n, t i.succPNat • PowerSeries.X ^ p ^ (i + 1) := by
    induction n with
    | zero => simp [pTypicalStrictCurveStage]
    | succ n ih =>
      rw [pTypicalStrictCurveStage, Curve.toPowerSeries_add_𝔾ₐ, ih, sum_range_succ, add_assoc,
        toPowerSeries_monomialCurve]
  rw [coeff_pTypicalStrictCurve_eq_stage _ hp t (Nat.lt_pow_add_one_self hp k),
    hstage k, map_add, PowerSeries.coeff_X, map_sum]
  rcases eq_or_ne k 1 with rfl | hk1
  · simp [hp.ne]
  · simp only [hk1, ite_false, _root_.zero_add]
    split_ifs with hex
    · obtain ⟨hpow, hpos⟩ := hex
      set m := Nat.log p k - 1; have hm : Nat.log p k = m + 1 := by omega
      rw [sum_eq_single m]
      · rw [(PNat.coe_injective hm : (⟨Nat.log p k, hpos⟩ : ℕ+) = m.succPNat), ← hpow, hm]
        simp [PowerSeries.coeff_X_pow]
      · exact fun j _ hjm ↦ by
          have hne : k ≠ p ^ (j + 1) := fun h ↦ hjm <| by
            have := Nat.pow_right_injective hp (hpow.trans h); omega
          simp [PowerSeries.coeff_X_pow, hne]
      · exact fun hnot ↦ absurd (mem_range.mpr <| by
          have := (m + 1).lt_pow_self hp; have : p ^ (m + 1) = k := hm ▸ hpow; omega) hnot
    · exact sum_eq_zero fun i _ ↦ by
        have hne : k ≠ p ^ (i + 1) := by
          rintro rfl; exact hex ⟨by rw [Nat.log_pow hp], by rw [Nat.log_pow hp]; exact i.succ_pos⟩
        simp [PowerSeries.coeff_X_pow, hne]

/-- The degree-`k` coefficient of `F.pTypicalStrictCurve p t` depends only on `tᵢ` with `pⁱ ≤ k`. -/
theorem coeff_pTypicalStrictCurve_congr (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R}
    {k : ℕ} (ht : ∀ i : ℕ+, p ^ (i : ℕ) ≤ k → t i = t' i) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (F.pTypicalStrictCurve p t').toPowerSeries := by
  have hk : k < p ^ (k + 1) := Nat.lt_pow_add_one_self hp k
  rw [coeff_pTypicalStrictCurve_eq_stage F hp t hk, coeff_pTypicalStrictCurve_eq_stage F hp t' hk]
  suffices ∀ n, ∀ j ≤ k,
      PowerSeries.coeff j (pTypicalStrictCurveStage F p hp t n).toPowerSeries =
        PowerSeries.coeff j (pTypicalStrictCurveStage F p hp t' n).toPowerSeries from
    this k k le_rfl
  intro n; induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro j hj; rcases lt_or_ge j (p ^ (n + 1)) with hlt | hge
    · rw [coeff_pTypicalStrictCurveStage_succ_of_lt F hp t hlt,
        coeff_pTypicalStrictCurveStage_succ_of_lt F hp t' hlt, ih j hj]
    · exact Curve.coeff_add_congr (fun r hr ↦ ih r (hr.trans hj)) fun _ _ ↦ by
        simp [ht n.succPNat (hge.trans hj)]

/-- If `t` and `t'` agree up to index `n`, `F.pTypicalStrictCurve p t` and `t'` agree below
`p^(n + 1)`. -/
theorem le_order_pTypicalStrictCurve_sub (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R}
    {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤ ((F.pTypicalStrictCurve p t).toPowerSeries -
        (F.pTypicalStrictCurve p t').toPowerSeries).order :=
  PowerSeries.nat_le_order _ _ fun k hk ↦ by
    rw [map_sub, F.coeff_pTypicalStrictCurve_congr hp fun i hi ↦ ht i (by
      by_contra! hlt
      have : p ^ (n + 1) ≤ p ^ (i : ℕ) := Nat.pow_le_pow_right (by omega) hlt; omega), sub_self]

/-- If `t` and `t'` agree up to index `n`, the coefficient of `X^(p^(n + 1))` in
`F.pTypicalStrictCurve p t - F.pTypicalStrictCurve p t'` is `t_{n + 1} - t'_{n + 1}`. -/
theorem coeff_pow_succ_pTypicalStrictCurve_sub (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    PowerSeries.coeff (p ^ (n + 1)) ((F.pTypicalStrictCurve p t).toPowerSeries -
      (F.pTypicalStrictCurve p t').toPowerSeries) = t n.succPNat - t' n.succPNat := by
  have hk : p ^ (n + 1) < p ^ (n + 1 + 1) := Nat.pow_lt_pow_right hp (Nat.lt_succ_self _)
  have h0 (c : R) : ∀ j < p ^ (n + 1), PowerSeries.coeff j
      (F.monomialCurve (p ^ (n + 1)) (pow_ne_zero _ (Nat.ne_zero_of_lt hp)) c).toPowerSeries = 0 :=
    fun _ hi ↦ by simp [PowerSeries.coeff_X_pow, hi.ne]
  rw [map_sub, coeff_pTypicalStrictCurve_eq_stage F hp t hk,
    coeff_pTypicalStrictCurve_eq_stage F hp t' hk, pTypicalStrictCurveStage,
    pTypicalStrictCurveStage,
    Curve.coeff_add_of_forall_lt_coeff_eq_zero _ _ (pow_ne_zero _ (by omega)) le_rfl (h0 _),
    Curve.coeff_add_of_forall_lt_coeff_eq_zero _ _ (pow_ne_zero _ (by omega)) le_rfl (h0 _),
    pTypicalStrictCurveStage_congr F hp ht]
  simp [PowerSeries.coeff_X_pow]

/-- For `1 < p`, `F.pTypicalStrictCurve p` is injective over any commutative ring. -/
theorem pTypicalStrictCurve_injective (F : FormalGroup R) {p : ℕ} (hp : 1 < p) :
    Function.Injective (F.pTypicalStrictCurve p) := fun t t' h ↦ funext fun i ↦ by
  induction i using PNat.strongInductionOn with | _ i ih =>
  obtain ⟨n, rfl⟩ : ∃ n, n.succPNat = i := ⟨i.natPred, i.succPNat_natPred⟩
  have hsub := F.coeff_pow_succ_pTypicalStrictCurve_sub hp (n := n) fun j hj ↦
    ih j ((PNat.coe_lt_coe j n.succPNat).mp (by simpa using Nat.lt_succ_of_le hj))
  rwa [h, sub_self, map_zero, eq_comm, sub_eq_zero] at hsub

/-- For `1 < p`, `F.pTypicalStrictCoordinate p` is injective over any commutative ring. -/
theorem pTypicalStrictCoordinate_injective (F : FormalGroup R) {p : ℕ} (hp : 1 < p) :
    Function.Injective (F.pTypicalStrictCoordinate p) := fun _ _ h ↦
  F.pTypicalStrictCurve_injective hp <| Curve.ext <| by
    simpa only [toPowerSeries_inv_pTypicalStrictCoordinate] using
      congrArg (fun φ : TauCeti.FormalCoordinate R ↦ φ⁻¹.toPowerSeries) h

/-- For `1 < p`, two `p`-typical strict curves on `F` are equal if and only if their parameter
families agree. -/
@[simp] theorem pTypicalStrictCurve_inj (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} : F.pTypicalStrictCurve p t = F.pTypicalStrictCurve p t' ↔ t = t' :=
  (F.pTypicalStrictCurve_injective hp).eq_iff

/-- For `1 < p`, two `p`-typical strict coordinates on `F` are equal if and only if their parameter
families agree. -/
@[simp] theorem pTypicalStrictCoordinate_inj (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} : F.pTypicalStrictCoordinate p t = F.pTypicalStrictCoordinate p t' ↔ t = t' :=
  (F.pTypicalStrictCoordinate_injective hp).eq_iff

end FormalGroup
