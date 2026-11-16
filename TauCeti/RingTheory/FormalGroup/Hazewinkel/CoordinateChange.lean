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

For a formal group law `F` over `R`, `p > 1`, and `t : ℕ+ → R`, the partial sums
`X +_F t₁ X^p +_F ⋯ +_F tₙ X^(pⁿ)` stabilize coefficientwise to `F.pTypicalStrictCurve p t`, with
inverse `F.pTypicalStrictCoordinate p t` (`FormalGroup.pTypicalStrictCurve_injective`). Over a
`ℚ`-algebra, substituting `pTypicalStrictCurve` into Hazewinkel's logarithm `f_v` satisfies
Ravenel's recursion (`TauCeti.coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog`,
`TauCeti.coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero`).

Comparing `TauCeti.hazewinkelIntegralFormalGroup` degreewise via Lazard's `2`-cocycle
`C_{p^(n + 1)}` (`TauCeti.homogeneousComponent_hazewinkelIntegralFormalGroup_sub`) gives universal
injectivity (`TauCeti.hazewinkelIntegralFormalGroup_injective`), universal integrality of strict
`p`-typical coordinate transport
(`TauCeti.existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup`), and `p`-local
classification (`TauCeti.existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq`,
`TauCeti.exists_hazewinkelIntegralFormalGroup_eq_smul_iff`).

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, 1969.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2 and Chapter IV.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open Finset MvPowerSeries

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

private def pTypicalMonomialCurve (F : FormalGroup R) (c : R) (m : ℕ) (hm : m ≠ 0) : F.Curve where
  toPowerSeries := c • PowerSeries.X ^ m
  constantCoeff_toPowerSeries := by simp [hm]

private def pTypicalStrictCurveStage (F : FormalGroup R) (p : ℕ) (hp : 1 < p) (t : ℕ+ → R) :
    ℕ → F.Curve
  | 0 => F.tautologicalCurve
  | n + 1 => pTypicalStrictCurveStage F p hp t n +
      pTypicalMonomialCurve F (t n.succPNat) (p ^ (n + 1)) (pow_ne_zero _ (by omega))

private theorem coeff_pTypicalStrictCurveStage_succ_of_lt (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t (n + 1)).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries :=
  Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero _ _ hk fun _ hi ↦ by
    simp [pTypicalMonomialCurve, PowerSeries.coeff_X_pow, hi.ne]

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
    rw [pTypicalStrictCurveStage, map_add, ih, pTypicalStrictCurveStage]; congr 1; ext k
    simp only [Curve.toPowerSeries_map, PowerSeries.coeff_map, pTypicalMonomialCurve,
      PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul, Function.comp_apply]
    split_ifs <;> simp

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
  simp [pTypicalStrictCurve, show ¬ 1 < p by omega]

private theorem coeff_pTypicalStrictCurve_eq_stage (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    (t : ℕ+ → R) {n k : ℕ} (hk : k < p ^ (n + 1)) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (pTypicalStrictCurveStage F p hp t n).toPowerSeries := by
  rw [pTypicalStrictCurve, dite_eq_left hp, PowerSeries.coeff_mk]
  rcases le_total n k with hnk | hkn
  · exact coeff_pTypicalStrictCurveStage_eq_of_le F hp t hnk hk
  · exact (coeff_pTypicalStrictCurveStage_eq_of_le F hp t hkn
      ((Nat.lt_succ_self k).trans ((k + 1).lt_pow_self hp))).symm

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
      (F.pTypicalStrictCurve p t).toPowerSeries := by rw [pTypicalStrictCoordinate, inv_inv]

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
        have h0 : pTypicalMonomialCurve F ((0 : ℕ+ → R) n.succPNat) (p ^ (n + 1))
            (pow_ne_zero _ (by omega)) = 0 := by ext; simp [pTypicalMonomialCurve]
        rw [pTypicalStrictCurveStage, ih, h0, _root_.add_zero]
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
    have hk : k < p ^ (k + 1) := (Nat.lt_succ_self k).trans ((k + 1).lt_pow_self hp)
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
      else if h : p ^ Nat.log p k = k ∧ 0 < Nat.log p k then t (⟨Nat.log p k, h.2⟩ : ℕ+)
      else 0 := by
  have hstage (n : ℕ) : (pTypicalStrictCurveStage (𝔾ₐ (R := R)) p hp t n).toPowerSeries =
      PowerSeries.X + ∑ i ∈ range n, t i.succPNat • PowerSeries.X ^ p ^ (i + 1) := by
    induction n with
    | zero => simp [pTypicalStrictCurveStage]
    | succ n ih =>
      rw [pTypicalStrictCurveStage, Curve.toPowerSeries_add_𝔾ₐ, ih, sum_range_succ, add_assoc]; rfl
  rw [coeff_pTypicalStrictCurve_eq_stage _ hp t
      ((Nat.lt_succ_self k).trans ((k + 1).lt_pow_self hp)),
    hstage k, map_add, PowerSeries.coeff_X, map_sum]
  rcases eq_or_ne k 1 with rfl | hk1
  · simp only [↓reduceIte]
    rw [sum_eq_zero fun i _ ↦ by
      simp [PowerSeries.coeff_X_pow, (Nat.one_lt_pow i.succ_ne_zero hp).ne]]; ring
  · simp only [hk1, ite_false, _root_.zero_add]; split_ifs with hex
    · obtain ⟨hpow, hpos⟩ := hex
      set m := Nat.log p k - 1
      have hm : Nat.log p k = m + 1 := by omega
      have hmk : m ∈ range k := mem_range.mpr <| by
        have := (m + 1).lt_pow_self hp; have : p ^ (m + 1) = k := hm ▸ hpow; omega
      rw [sum_eq_single m]
      · rw [show (⟨Nat.log p k, hpos⟩ : ℕ+) = m.succPNat from PNat.coe_injective hm, ← hpow, hm]
        simp [PowerSeries.coeff_X_pow]
      · intro j _ hjm
        have hne : k ≠ p ^ (j + 1) := by
          rw [← hpow, hm]; exact fun heq ↦ hjm <| by have := Nat.pow_right_injective hp heq; omega
        simp [PowerSeries.coeff_X_pow, hne]
      · exact fun hnot ↦ absurd hmk hnot
    · refine sum_eq_zero fun i _ ↦ ?_
      have hne : k ≠ p ^ (i + 1) := by
        rintro rfl; exact hex ⟨by rw [Nat.log_pow hp], by rw [Nat.log_pow hp]; exact i.succ_pos⟩
      simp [PowerSeries.coeff_X_pow, hne]

/-- The degree-`k` coefficient of `F.pTypicalStrictCurve p t` depends only on `tᵢ` with `pⁱ ≤ k`. -/
theorem coeff_pTypicalStrictCurve_congr (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R}
    {k : ℕ} (ht : ∀ i : ℕ+, p ^ (i : ℕ) ≤ k → t i = t' i) :
    PowerSeries.coeff k (F.pTypicalStrictCurve p t).toPowerSeries =
      PowerSeries.coeff k (F.pTypicalStrictCurve p t').toPowerSeries := by
  have hk : k < p ^ (k + 1) := (Nat.lt_succ_self k).trans ((k + 1).lt_pow_self hp)
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
        coeff_pTypicalStrictCurveStage_succ_of_lt F hp t' hlt]
      exact ih j hj
    · exact Curve.coeff_add_congr (fun r hr ↦ ih r (hr.trans hj)) fun _ _ ↦ by
        simp [pTypicalMonomialCurve, ht n.succPNat (hge.trans hj)]

/-- If `t` and `t'` agree up to index `n`, `F.pTypicalStrictCurve p t` and `t'` agree below
`p^(n + 1)`. -/
theorem le_order_pTypicalStrictCurve_sub (F : FormalGroup R) {p : ℕ} (hp : 1 < p) {t t' : ℕ+ → R}
    {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤
      ((F.pTypicalStrictCurve p t).toPowerSeries -
        (F.pTypicalStrictCurve p t').toPowerSeries).order := by
  refine PowerSeries.nat_le_order _ _ fun k hk ↦ ?_
  rw [map_sub, F.coeff_pTypicalStrictCurve_congr hp fun i hi ↦ ht i ?_, sub_self]
  by_contra! hlt
  have hpow : p ^ (n + 1) ≤ p ^ (i : ℕ) := Nat.pow_le_pow_right (by omega) hlt; omega

/-- If `t` and `t'` agree up to index `n`, the coefficient of `X^(p^(n + 1))` in
`F.pTypicalStrictCurve p t - F.pTypicalStrictCurve p t'` is `t_{n + 1} - t'_{n + 1}`. -/
theorem coeff_pow_succ_pTypicalStrictCurve_sub (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} {n : ℕ} (ht : ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i) :
    PowerSeries.coeff (p ^ (n + 1)) ((F.pTypicalStrictCurve p t).toPowerSeries -
      (F.pTypicalStrictCurve p t').toPowerSeries) = t n.succPNat - t' n.succPNat := by
  have hk : p ^ (n + 1) < p ^ (n + 1 + 1) := Nat.pow_lt_pow_right hp (Nat.lt_succ_self _)
  have h0 (c : R) : ∀ j < p ^ (n + 1), PowerSeries.coeff j
      (pTypicalMonomialCurve F c (p ^ (n + 1)) (pow_ne_zero _ (by omega))).toPowerSeries = 0 :=
    fun _ hi ↦ by simp [pTypicalMonomialCurve, PowerSeries.coeff_X_pow, hi.ne]
  rw [map_sub, coeff_pTypicalStrictCurve_eq_stage F hp t hk,
    coeff_pTypicalStrictCurve_eq_stage F hp t' hk, pTypicalStrictCurveStage,
    pTypicalStrictCurveStage,
    Curve.coeff_add_of_forall_lt_coeff_eq_zero _ _ (pow_ne_zero _ (by omega)) le_rfl (h0 _),
    Curve.coeff_add_of_forall_lt_coeff_eq_zero _ _ (pow_ne_zero _ (by omega)) le_rfl (h0 _),
    pTypicalStrictCurveStage_congr F hp ht]
  simp [pTypicalMonomialCurve, PowerSeries.coeff_X_pow]

/-- For `1 < p`, `F.pTypicalStrictCurve p` is injective over any commutative ring. -/
theorem pTypicalStrictCurve_injective (F : FormalGroup R) {p : ℕ} (hp : 1 < p) :
    Function.Injective (F.pTypicalStrictCurve p) := by
  intro t t' h
  suffices ∀ n, ∀ i : ℕ+, (i : ℕ) ≤ n → t i = t' i from funext fun i ↦ this (i : ℕ) i le_rfl
  intro n; induction n with
  | zero => intro i hi; have := i.pos; omega
  | succ n ih =>
    intro i hi; rcases lt_or_eq_of_le hi with hlt | heq
    · exact ih i (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : i = n.succPNat := PNat.coe_injective heq
      have hsub := F.coeff_pow_succ_pTypicalStrictCurve_sub hp ih
      rwa [h, sub_self, map_zero, eq_comm, sub_eq_zero] at hsub

/-- For `1 < p`, `F.pTypicalStrictCoordinate p` is injective over any commutative ring. -/
theorem pTypicalStrictCoordinate_injective (F : FormalGroup R) {p : ℕ} (hp : 1 < p) :
    Function.Injective (F.pTypicalStrictCoordinate p) := fun _ _ h ↦
  F.pTypicalStrictCurve_injective hp <| Curve.ext <| by
    simpa only [toPowerSeries_inv_pTypicalStrictCoordinate] using
      congrArg (fun φ : TauCeti.FormalCoordinate R ↦ φ⁻¹.toPowerSeries) h

@[simp] theorem pTypicalStrictCurve_eq_iff (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} : F.pTypicalStrictCurve p t = F.pTypicalStrictCurve p t' ↔ t = t' :=
  (F.pTypicalStrictCurve_injective hp).eq_iff

@[simp] theorem pTypicalStrictCoordinate_eq_iff (F : FormalGroup R) {p : ℕ} (hp : 1 < p)
    {t t' : ℕ+ → R} : F.pTypicalStrictCoordinate p t = F.pTypicalStrictCoordinate p t' ↔ t = t' :=
  (F.pTypicalStrictCoordinate_injective hp).eq_iff

end FormalGroup

namespace TauCeti

section Rational

variable {K : Type*} [CommRing K] [Algebra ℚ K] {p : ℕ}

open scoped Classical in
private theorem coeff_subst_smul_X_pow_hazewinkelLog (hp : 1 < p) (v : ℕ+ → K) (c : K) (m k : ℕ) :
    PowerSeries.coeff k
        (PowerSeries.subst (c • PowerSeries.X ^ p ^ (m + 1)) (hazewinkelLog p v).toPowerSeries) =
      if h : ∃ j, p ^ (j + m + 1) = k then c ^ p ^ h.choose * hazewinkelLogCoeff p v h.choose
      else 0 := by
  have h0 : PowerSeries.constantCoeff (c • PowerSeries.X ^ p ^ (m + 1) : PowerSeries K) = 0 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_X_pow,
      (pow_ne_zero (m + 1) (by omega : p ≠ 0)).symm]
  rw [PowerSeries.coeff_def Finsupp.single_eq_same,
    PowerSeries.coeff_subst_eq_sum_range_degree (τ := Unit) (a := c • PowerSeries.X ^ p ^ (m + 1))
      (by simpa [← PowerSeries.constantCoeff_eq] using h0) (hazewinkelLog p v).toPowerSeries
      (Finsupp.single () k)]
  simp only [Finsupp.degree_single]
  have hoff (d : ℕ) (hne : ∀ r, p ^ r = d → k ≠ p ^ (r + m + 1)) :
      coeff (Finsupp.single () d) (hazewinkelLog p v).toPowerSeries •
        coeff (Finsupp.single () k)
          ((c • PowerSeries.X ^ p ^ (m + 1) : PowerSeries K) ^ d) = 0 := by
    by_cases hpow : ∃ r, p ^ r = d
    · obtain ⟨r, rfl⟩ := hpow
      have hne' : k ≠ p ^ (m + 1) * p ^ r := by
        rw [← pow_add, show m + 1 + r = r + m + 1 by omega]; exact hne r rfl
      rw [smul_pow, ← pow_mul]
      simp [← PowerSeries.coeff_def Finsupp.single_eq_same, PowerSeries.coeff_X_pow, hne']
    · push Not at hpow
      rw [← PowerSeries.coeff_def Finsupp.single_eq_same, coeff_hazewinkelLog_eq_zero v hpow,
        zero_smul]
  split_ifs with hex
  · have ⟨j, hj⟩ := hex; subst hj
    have huniq : hex.choose = j := by have := Nat.pow_right_injective hp hex.choose_spec; omega
    rw [huniq, sum_eq_single (p ^ j)]
    · rw [← PowerSeries.coeff_def Finsupp.single_eq_same, coeff_hazewinkelLog_pow v hp j, smul_pow,
        ← pow_mul, ← pow_add, show m + 1 + j = j + m + 1 by omega]
      simp [PowerSeries.coeff_X_pow, mul_comm]
    · exact fun d _ hdj ↦ hoff d fun r hr ↦ by
        subst hr; intro heq
        exact hdj (by congr 1; have := Nat.pow_right_injective hp heq; omega)
    · exact fun hnot ↦ absurd
        (mem_range.mpr (Nat.lt_succ_of_le (Nat.pow_le_pow_right (by omega) (by omega)))) hnot
  · exact sum_eq_zero fun d _ ↦ hoff d fun r _ hk ↦ hex ⟨r, hk.symm⟩

private theorem subst_pTypicalStrictCurve_hazewinkelLog_stage (hp : 1 < p) (v t : ℕ+ → K) (N k : ℕ)
    (hk : k < p ^ (N + 1)) :
    PowerSeries.coeff k
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) =
      PowerSeries.coeff k ((hazewinkelLog p v).toPowerSeries + ∑ i ∈ range N,
        PowerSeries.subst (t i.succPNat • PowerSeries.X ^ p ^ (i + 1))
          (hazewinkelLog p v).toPowerSeries) := by
  let F := hazewinkelFormalGroup p v
  have hdvd : PowerSeries.X ^ p ^ (N + 1) ∣
      (F.pTypicalStrictCurve p t).toPowerSeries -
        (FormalGroup.pTypicalStrictCurveStage F p hp t N).toPowerSeries :=
    PowerSeries.X_pow_dvd_iff.mpr fun j hj ↦ by
      rw [map_sub, FormalGroup.coeff_pTypicalStrictCurve_eq_stage F hp t hj, sub_self]
  have hsub := PowerSeries.X_pow_dvd_iff.mp
    (PowerSeries.X_pow_dvd_subst_sub_subst (F.pTypicalStrictCurve p t).constantCoeff_toPowerSeries
      hdvd (hazewinkelLog p v).toPowerSeries) k hk
  rw [map_sub, sub_eq_zero] at hsub; rw [hsub]; congr 1
  have hcurve (M : ℕ) :
      (F.logHom.mapCurve (FormalGroup.pTypicalStrictCurveStage F p hp t M)).toPowerSeries =
        (hazewinkelLog p v).toPowerSeries + ∑ i ∈ range M,
          PowerSeries.subst (t i.succPNat • PowerSeries.X ^ p ^ (i + 1))
            (hazewinkelLog p v).toPowerSeries := by
    induction M with
    | zero =>
      rw [FormalGroup.pTypicalStrictCurveStage, FormalGroupHom.toPowerSeries_mapCurve,
        FormalGroup.toPowerSeries_tautologicalCurve, FormalGroup.logHom_toPowerSeries,
        log_hazewinkelFormalGroup, PowerSeries.X_subst, range_zero, sum_empty, add_zero]
    | succ M ih =>
      rw [FormalGroup.pTypicalStrictCurveStage, map_add, FormalGroup.Curve.toPowerSeries_add_𝔾ₐ,
        ih, sum_range_succ, add_assoc, FormalGroupHom.toPowerSeries_mapCurve,
        FormalGroup.logHom_toPowerSeries, log_hazewinkelFormalGroup]; rfl
  simpa only [F, FormalGroupHom.toPowerSeries_mapCurve, FormalGroup.logHom_toPowerSeries,
    log_hazewinkelFormalGroup] using hcurve N

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
  rw [subst_pTypicalStrictCurve_hazewinkelLog_stage hp v t n (p ^ n)
      (Nat.pow_lt_pow_right hp (Nat.lt_succ_self n)),
    map_add, coeff_hazewinkelLog_pow v hp n, map_sum]; congr 1
  refine Finset.sum_bij (fun m _ ↦ n - 1 - m)
    (fun m hm ↦ mem_range.mpr (by have := mem_range.mp hm; omega))
    (fun m₁ hm₁ m₂ hm₂ h ↦ by have := mem_range.mp hm₁; have := mem_range.mp hm₂; omega)
    (fun i hi ↦ ⟨n - 1 - i, mem_range.mpr (by have := mem_range.mp hi; omega),
      by have := mem_range.mp hi; omega⟩) fun m hm ↦ ?_
  have hlt : m < n := mem_range.mp hm
  have hex : ∃ j, p ^ (j + m + 1) = p ^ n := ⟨n - 1 - m, by congr 1; omega⟩
  rw [coeff_subst_smul_X_pow_hazewinkelLog hp v (t m.succPNat) m (p ^ n), dite_eq_left hex,
    show hex.choose = n - 1 - m by have := Nat.pow_right_injective hp hex.choose_spec; omega,
    show (n - 1 - (n - 1 - m)).succPNat = m.succPNat by congr 1; omega, mul_comm]

/-- Outside the degrees `pⁿ`, `f_v((F_v.pTypicalStrictCurve p t)(X))` vanishes. -/
theorem coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero (hp : 1 < p) (v t : ℕ+ → K) {k : ℕ}
    (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) = 0 := by
  classical
  rw [subst_pTypicalStrictCurve_hazewinkelLog_stage hp v t k k
      ((Nat.lt_succ_self k).trans ((k + 1).lt_pow_self hp)),
    map_add, coeff_hazewinkelLog_eq_zero v hk, zero_add, map_sum]
  exact sum_eq_zero fun m _ ↦ by
    rw [coeff_subst_smul_X_pow_hazewinkelLog hp v (t m.succPNat) m k,
      dite_eq_right fun ⟨j, hj⟩ ↦ hk (j + m + 1) hj]

/-- The formal logarithm of `(F_v.pTypicalStrictCoordinate p t) • F_v` is
`f_v((F_v.pTypicalStrictCurve p t)(X))`. -/
theorem log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup (v t : ℕ+ → K) :
    (((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t) • hazewinkelFormalGroup p v).log =
      PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
        (hazewinkelLog p v).toPowerSeries := by
  rw [FormalGroup.log_smul, log_hazewinkelFormalGroup,
    FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]; simp

/-- Over a `ℚ`-algebra, transporting `hazewinkelFormalGroup p v` along `pTypicalStrictCoordinate`
produces `hazewinkelFormalGroup p w` for a unique sequence `w : ℕ+ → K`. -/
theorem existsUnique_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup (hp : 1 < p)
    (v t : ℕ+ → K) :
    ∃! w : ℕ+ → K,
      ((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t) • hazewinkelFormalGroup p v =
        hazewinkelFormalGroup p w :=
  existsUnique_eq_hazewinkelFormalGroup hp fun k hk ↦ by
    rw [log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup,
      coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero hp v t hk]

private def pTypicalCoordParamsRat (p : ℕ) (v w : ℕ+ → K) : ℕ → K
  | n => hazewinkelLogCoeff p w (n + 1) - hazewinkelLogCoeff p v (n + 1) -
      ∑ i : Fin n, hazewinkelLogCoeff p v ((i : ℕ) + 1) *
        pTypicalCoordParamsRat p v w (n - ((i : ℕ) + 1)) ^ p ^ ((i : ℕ) + 1)
decreasing_by have := i.isLt; omega

/-- Over a `ℚ`-algebra, `(hazewinkelLog p w)⁻¹ * hazewinkelLog p v` equals
`(hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t` for a unique `t : ℕ+ → K`. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_inv_hazewinkelLog_mul (hp : 1 < p)
    (v w : ℕ+ → K) :
    ∃! t : ℕ+ → K,
      (hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t =
        (hazewinkelLog p w)⁻¹ * hazewinkelLog p v := by
  let t : ℕ+ → K := fun j ↦ pTypicalCoordParamsRat p v w j.natPred
  have hlog : PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
      (hazewinkelLog p v).toPowerSeries = (hazewinkelLog p w).toPowerSeries := by
    ext k; by_cases hpow : ∃ n, p ^ n = k
    · obtain ⟨_ | n, rfl⟩ := hpow
      · rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp v t 0,
          coeff_hazewinkelLog_pow w hp 0, hazewinkelLogCoeff_zero, hazewinkelLogCoeff_zero,
          range_zero, sum_empty, add_zero]
      · have ht_n : t n.succPNat = hazewinkelLogCoeff p w (n + 1) -
            hazewinkelLogCoeff p v (n + 1) - ∑ i ∈ range n,
              hazewinkelLogCoeff p v (i + 1) * t (n - (i + 1)).succPNat ^ p ^ (i + 1) := by
          dsimp only [t]; rw [Nat.natPred_succPNat, pTypicalCoordParamsRat,
            Fin.sum_univ_eq_sum_range (fun j ↦ hazewinkelLogCoeff p v (j + 1) *
              pTypicalCoordParamsRat p v w (n - (j + 1)) ^ p ^ (j + 1))]; rfl
        rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp v t (n + 1),
          coeff_hazewinkelLog_pow w hp (n + 1), sum_range_succ', pow_zero, pow_one,
          hazewinkelLogCoeff_zero, one_mul, show n + 1 - 1 - 0 = n by omega, ht_n]
        have hsum : (∑ x ∈ range n,
            hazewinkelLogCoeff p v (x + 1) * t (n + 1 - 1 - (x + 1)).succPNat ^ p ^ (x + 1)) =
          ∑ x ∈ range n, hazewinkelLogCoeff p v (x + 1) * t (n - (x + 1)).succPNat ^ p ^ (x + 1) :=
          sum_congr rfl fun x _ ↦ by rw [show n + 1 - 1 - (x + 1) = n - (x + 1) by omega]
        rw [hsum]; ring
    · push Not at hpow
      rw [coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero hp v t hpow,
        coeff_hazewinkelLog_eq_zero w hpow]
  have hcoord : (hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t =
      (hazewinkelLog p w)⁻¹ * hazewinkelLog p v := by
    apply inv_injective; rw [mul_inv_rev, inv_inv]
    have hmul : hazewinkelLog p v * ((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t)⁻¹ =
        hazewinkelLog p w := FormalCoordinate.ext <| by
      rw [FormalCoordinate.toPowerSeries_mul,
        FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate, hlog]
    rw [← hmul, inv_mul_cancel_left]
  exact ⟨t, hcoord, fun t' ht' ↦
    (hazewinkelFormalGroup p v).pTypicalStrictCoordinate_injective hp (ht'.trans hcoord.symm)⟩

end Rational

section Comparison

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

omit p hp in
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
  have hdef_step := F.le_order_homDefect_sub (G := G) (by simp [hm]) hη_approx
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
    ∃ s : PowerSeries R, (φ * ψ).toPowerSeries = PowerSeries.X + PowerSeries.X ^ m * s ∧
      PowerSeries.constantCoeff s = PowerSeries.constantCoeff r := by
  obtain ⟨s, hs, hs0⟩ := PowerSeries.exists_subst_add_X_pow_mul φ.toPowerSeries
    φ⁻¹.constantCoeff_toPowerSeries r hm
  have hφ_inv : PowerSeries.subst φ⁻¹.toPowerSeries φ.toPowerSeries = PowerSeries.X := by
    simpa only [FormalCoordinate.toPowerSeries_mul, FormalCoordinate.toPowerSeries_one] using
      congrArg FormalCoordinate.toPowerSeries (mul_inv_cancel φ)
  have hφ1 : PowerSeries.coeff 1 φ.toPowerSeries = 1 := by
    rw [← FormalCoordinate.val_linearCoeff, hφ, Units.val_one]
  exact ⟨s, by rw [FormalCoordinate.toPowerSeries_mul, hψ, hs, hφ_inv], by simpa [hφ1] using hs0⟩

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
  have hp1 : 1 < p := hp.out.one_lt
  set N := p ^ (n + 1)
  have hN0 : N ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  set c : K := (p : ℚ)⁻¹ • (v n.succPNat - w n.succPNat)
  have hlog_eq : ∀ m ≤ n, hazewinkelLogCoeff p v m = hazewinkelLogCoeff p w m := fun m hm ↦ by
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | m
      · simp
      · rw [hazewinkelLogCoeff_succ, hazewinkelLogCoeff_succ]; congr 1
        refine sum_congr rfl fun i hi ↦ ?_
        have := mem_range.mp hi
        rcases eq_or_ne i 0 with rfl | _
        · simp [hvw m.succPNat hm]
        · rw [ih i (by omega) (by omega), hvw _ (by simp; omega)]
  have hlog_succ : hazewinkelLogCoeff p v (n + 1) - hazewinkelLogCoeff p w (n + 1) = c := by
    rw [hazewinkelLogCoeff_succ, hazewinkelLogCoeff_succ, sum_range_succ', sum_range_succ',
      hazewinkelLogCoeff_zero, hazewinkelLogCoeff_zero, pow_zero, pow_one, one_mul, one_mul,
      Nat.sub_zero, ← smul_sub]; congr 1
    rw [sum_congr rfl fun i hi ↦ by
      have := mem_range.mp hi; rw [hlog_eq (i + 1) (by omega), hvw _ (by simp; omega)]]; ring
  obtain ⟨r, hr⟩ : PowerSeries.X ^ (N + 1) ∣
      ((hazewinkelLog p v).toPowerSeries - (hazewinkelLog p w).toPowerSeries) -
        c • PowerSeries.X ^ N := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun k hk ↦ ?_; rw [map_sub, map_sub]
    by_cases hpow : ∃ m, p ^ m = k
    · obtain ⟨m, rfl⟩ := hpow; rcases lt_trichotomy m (n + 1) with hlt | rfl | hgt
      · rw [coeff_hazewinkelLog_pow v hp1, coeff_hazewinkelLog_pow w hp1, hlog_eq m (by omega),
          sub_self, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow,
          ite_eq_right (Nat.pow_lt_pow_right hp1 hlt).ne, smul_zero, sub_zero]
      · rw [coeff_hazewinkelLog_pow v hp1, coeff_hazewinkelLog_pow w hp1, hlog_succ,
          PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, ite_eq_left rfl, smul_eq_mul, mul_one,
          sub_self]
      · exfalso
        have : N * p ≤ p ^ m := pow_succ p (n + 1) ▸ Nat.pow_le_pow_right hp.out.pos hgt
        have := hp.out.two_le; have : 1 ≤ N := Nat.one_le_pow _ _ hp.out.pos; nlinarith
    · push Not at hpow
      rw [coeff_hazewinkelLog_eq_zero v hpow, coeff_hazewinkelLog_eq_zero w hpow, sub_zero,
        PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, ite_eq_right (hpow (n + 1)).symm,
        smul_zero, zero_sub, neg_zero]
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
  refine ⟨hord, ?_⟩; rw [hhom, hs_c]; congr 1
  have hcoc := lazardGcd_nsmul_lazardCocycle (R := K) hN0
  rw [lazardGcd_prime_pow hp.out n.succ_ne_zero] at hcoc
  rw [← hcoc, ← Nat.cast_smul_eq_nsmul ℚ, smul_comm c (p : ℚ), ← smul_assoc,
    smul_inv_smul₀ (Nat.cast_ne_zero.2 hp.out.ne_zero)]

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
  let ι : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* MvPolynomial (ℕ+ ⊕ ℕ+) ℚ :=
    MvPolynomial.map (Int.castRingHom ℚ)
  have hι_inj : Function.Injective ι := MvPolynomial.map_injective _ Int.cast_injective
  have hrat := hazewinkelFormalGroup_sub_of_forall_le_rat p
    (v := ι ∘ vU) (w := ι ∘ wU) (n := n) (fun i hi ↦ by simp [vU, wU, hi])
  have hmap_DU : D_U.map ι = (hazewinkelFormalGroup p (ι ∘ vU)).toPowerSeries -
      (hazewinkelFormalGroup p (ι ∘ wU)).toPowerSeries := by
    rw [map_sub, ← FormalGroup.map_toPowerSeries, ← FormalGroup.map_toPowerSeries,
      map_hazewinkelIntegralFormalGroup, map_hazewinkelIntegralFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  let ev : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v w)
  have hD_R : D_U.map ev = (hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries := by
    have hw : ev ∘ wU = w := funext fun i ↦ by dsimp [ev, wU]; split_ifs with hi <;> simp [hvw, hi]
    rw [map_sub, ← FormalGroup.map_toPowerSeries, ← FormalGroup.map_toPowerSeries,
      map_hazewinkelIntegralFormalGroup, map_hazewinkelIntegralFormalGroup,
      show ev ∘ vU = v from funext fun i ↦ by simp [ev, vU], hw]
  refine ⟨nat_le_order fun d hd ↦ ?_, ?_⟩
  · have h0 : coeff d D_U = 0 := hι_inj <| by
      rw [map_zero, ← coeff_map, hmap_DU]
      exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le hrat.1)
    rw [← hD_R, coeff_map, h0, map_zero]
  · ext d; rw [coeff_homogeneousComponent]; split_ifs with hd
    · have hDU_d : coeff d D_U = -((vU n.succPNat - wU n.succPNat) *
          (lazardCocycle (p ^ (n + 1)) (MvPolynomial (ℕ+ ⊕ ℕ+) ℤ)).coeff d) := hι_inj <| by
        have hcoeff := congrArg (coeff d) hrat.2
        rw [← hmap_DU, coeff_homogeneousComponent, ite_eq_left hd, coeff_map] at hcoeff
        rw [hcoeff, map_neg ι, map_mul ι, map_sub ι, ← MvPolynomial.coeff_map, map_lazardCocycle]
        simp [MvPolynomial.coe_smul]
      rw [← hD_R, coeff_map, hDU_d, map_neg, map_mul, map_sub, ← MvPolynomial.coeff_map,
        map_lazardCocycle]; simp [ev, vU, wU, MvPolynomial.coe_smul]
    · have h0 : (lazardCocycle (p ^ (n + 1)) R).coeff d = 0 := by
        rw [coeff_lazardCocycle, ite_eq_right]
        exact fun ⟨hsum, _, _⟩ ↦ hd (by simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hsum)
      simp [MvPolynomial.coe_smul, h0]

/-- **Degreewise congruence of Hazewinkel's integral formal group law**: if `v` and `w` agree up to
index `n`, `hazewinkelIntegralFormalGroup p v` and `w` agree strictly below degree `p^(n + 1)`. -/
theorem le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order :=
  (hazewinkelIntegralFormalGroup_sub_of_forall_le p hvw).1

/-- If `v` and `w` agree on `i ≤ n`, the homogeneous component of degree `p^(n + 1)` of
`hazewinkelIntegralFormalGroup p v - hazewinkelIntegralFormalGroup p w` is
`-(v_{n + 1} - w_{n + 1}) • C_{p^(n + 1)}`. -/
theorem homogeneousComponent_hazewinkelIntegralFormalGroup_sub {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    homogeneousComponent (p ^ (n + 1)) ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
      -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) R :
          MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) :=
  (hazewinkelIntegralFormalGroup_sub_of_forall_le p hvw).2

/-- **Universal injectivity of Hazewinkel's integral formal group law** over every commutative ring
`R` (including rings with arbitrary torsion). -/
theorem hazewinkelIntegralFormalGroup_injective :
    Function.Injective (hazewinkelIntegralFormalGroup p : (ℕ+ → R) → FormalGroup R) := by
  intro v w h
  suffices ∀ n, ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i from funext fun i ↦ this (i : ℕ) i le_rfl
  intro n; induction n with
  | zero => intro i hi; have := i.pos; omega
  | succ n ih =>
    intro i hi; rcases lt_or_eq_of_le hi with hlt | heq
    · exact ih i (Nat.lt_succ_iff.mp hlt)
    · obtain rfl : i = n.succPNat := PNat.coe_injective heq
      have hhom := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p ih
      rw [h, sub_self, map_zero, eq_comm, neg_eq_zero] at hhom
      exact sub_eq_zero.mp <| (smul_lazardCocycle_eq_zero_iff
        (hp.out.two_le.trans (Nat.le_self_pow n.succ_ne_zero p))).mp <|
        MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])

@[simp] theorem hazewinkelIntegralFormalGroup_eq_iff {v w : ℕ+ → R} :
    hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w ↔ v = w :=
  (hazewinkelIntegralFormalGroup_injective p).eq_iff

/-- At `v = 0`, `hazewinkelIntegralFormalGroup p 0` is the additive formal group law `𝔾ₐ`. -/
@[simp] theorem hazewinkelIntegralFormalGroup_zero :
    hazewinkelIntegralFormalGroup p (0 : ℕ+ → R) = FormalGroup.𝔾ₐ := by
  have hQ : hazewinkelFormalGroup p (0 : ℕ+ → ℚ) = FormalGroup.𝔾ₐ := by
    rw [eq_comm, eq_hazewinkelFormalGroup_iff, FormalGroup.log_𝔾ₐ]; ext k
    rcases eq_or_ne k 1 with rfl | hk1
    · simp
    · by_cases hpow : ∃ n, p ^ n = k
      · obtain ⟨_ | n, rfl⟩ := hpow
        · exact absurd rfl hk1
        · rw [PowerSeries.coeff_X, ite_eq_right hk1, coeff_hazewinkelLog_pow _ hp.out.one_lt]
          simp [hazewinkelLogCoeff_succ, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
      · push Not at hpow
        rw [PowerSeries.coeff_X, ite_eq_right hk1, coeff_hazewinkelLog_eq_zero _ hpow]
  have hZ : hazewinkelIntegralFormalGroup p (0 : ℕ+ → ℤ) = FormalGroup.𝔾ₐ :=
    FormalGroup.map_injective (f := Int.castRingHom ℚ) Int.cast_injective <| by
      dsimp only; rw [map_hazewinkelIntegralFormalGroup, FormalGroup.map_𝔾ₐ,
        hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
        show Int.castRingHom ℚ ∘ (0 : ℕ+ → ℤ) = 0 from funext fun _ ↦ map_zero _, hQ]
  simpa only [map_hazewinkelIntegralFormalGroup, FormalGroup.map_𝔾ₐ,
    show Int.castRingHom R ∘ (0 : ℕ+ → ℤ) = 0 from funext fun _ ↦ map_zero _] using
    congrArg (fun F : FormalGroup ℤ ↦ F.map (Int.castRingHom R)) hZ

end Comparison

section Classification

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

omit p hp in
private theorem mem_range_of_coeff_smul_lazardCocycle_mem {A B : Type*} [CommRing A] [CommRing B]
    (ι : A →+* B) {m : ℕ} (hm : 2 ≤ m) {r : B}
    (hr : ∀ i ∈ Icc 1 (m - 1),
      (r • lazardCocycle m B).coeff (Finsupp.single 0 i + Finsupp.single 1 (m - i)) ∈ ι.range) :
    r ∈ ι.range := by
  obtain ⟨c, hc⟩ :=
    Finset.gcd_eq_one_iff_exists_sum_natCast_mul_eq_one.1 (gcd_choose_div_lazardGcd_eq_one hm)
  have h1 : (∑ i ∈ Icc 1 (m - 1), ((m.choose i / lazardGcd m : ℕ) : B) * (c i : B)) = 1 := by
    simpa only [map_sum, map_mul, map_natCast, Int.coe_castRingHom, map_one] using
      congrArg (Int.castRingHom B) hc
  have hsum : ∑ i ∈ Icc 1 (m - 1),
      (c i : B) * (r • lazardCocycle m B).coeff (Finsupp.single 0 i + Finsupp.single 1 (m - i)) =
        r := by
    conv_rhs => rw [← one_mul r, ← h1, sum_mul]
    refine sum_congr rfl fun i hi ↦ ?_; rw [mem_Icc] at hi
    rw [MvPolynomial.coeff_smul, coeff_single_add_single_lazardCocycle (by omega) (by omega),
      smul_eq_mul]; ring
  exact hsum ▸ ι.range.sum_mem fun i hi ↦ ι.range.mul_mem ⟨c i, map_intCast ι (c i)⟩ (hr i hi)

/-- **Integrality of strict `p`-typical coordinate changes**: over every commutative ring `R`,
transporting `hazewinkelIntegralFormalGroup p v` along its `p`-typical strict coordinate `t`
produces `hazewinkelIntegralFormalGroup p w` for a unique sequence `w : ℕ+ → R`. -/
theorem existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup
    (v t : ℕ+ → R) :
    ∃! w : ℕ+ → R,
      ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
          hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w := by
  let UZ := MvPolynomial (ℕ+ ⊕ ℕ+) ℤ
  let ι : UZ →+* MvPolynomial (ℕ+ ⊕ ℕ+) ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let vZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inl i)
  let tZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inr i)
  set GZ := ((hazewinkelIntegralFormalGroup p vZ).pTypicalStrictCoordinate p tZ) •
    hazewinkelIntegralFormalGroup p vZ
  have hmap_GZ : GZ.map ι =
      ((hazewinkelFormalGroup p (ι ∘ vZ)).pTypicalStrictCoordinate p (ι ∘ tZ)) •
        hazewinkelFormalGroup p (ι ∘ vZ) := by
    rw [FormalGroup.map_smul, FormalGroup.map_pTypicalStrictCoordinate,
      map_hazewinkelIntegralFormalGroup, hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  obtain ⟨wQ, hwQ, _⟩ :=
    existsUnique_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup hp.out.one_lt (ι ∘ vZ) (ι ∘ tZ)
  have hwQ_mem : ∀ n (i : ℕ+), (i : ℕ) ≤ n → wQ i ∈ ι.range := fun n ↦ by
    induction n with
    | zero => intro i hi; have := i.pos; omega
    | succ n ih =>
      intro i hi; rcases lt_or_eq_of_le hi with hlt | heq
      · exact ih i (Nat.lt_succ_iff.mp hlt)
      · obtain rfl : i = n.succPNat := PNat.coe_injective heq
        let w_truncZ : ℕ+ → UZ := fun j ↦ if hj : (j : ℕ) ≤ n then (ih j hj).choose else 0
        have htrunc : ∀ j : ℕ+, (j : ℕ) ≤ n → wQ j = ι (w_truncZ j) := fun j hj ↦ by
          dsimp only [w_truncZ]; rw [dite_eq_left hj]; exact (ih j hj).choose_spec.symm
        have hhom := (hazewinkelFormalGroup_sub_of_forall_le_rat p (v := wQ)
          (w := ι ∘ w_truncZ) (n := n) htrunc).2
        rw [show (ι ∘ w_truncZ) n.succPNat = 0 by simp [w_truncZ], sub_zero, ← hmap_GZ.trans hwQ,
          ← hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup p (ι ∘ w_truncZ),
          ← map_hazewinkelIntegralFormalGroup] at hhom
        have h2 : 2 ≤ p ^ (n + 1) := hp.out.two_le.trans (Nat.le_self_pow n.succ_ne_zero p)
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
  choose wZ hwZ using fun i : ℕ+ ↦ RingHom.mem_range.mp (hwQ_mem i.val i le_rfl)
  have hwZ_eq : GZ = hazewinkelIntegralFormalGroup p wZ :=
    FormalGroup.map_injective (MvPolynomial.map_injective _ Int.cast_injective) <| by
      dsimp only; rw [hmap_GZ, hwQ, map_hazewinkelIntegralFormalGroup,
        hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
      exact congrArg _ (funext fun i ↦ (hwZ i).symm)
  let ev : UZ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v t)
  have hev_v : ev ∘ vZ = v := funext fun i ↦ by simp [UZ, ev, vZ]
  have hev_t : ev ∘ tZ = t := funext fun i ↦ by simp [UZ, ev, tZ]
  have hR : ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
      hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p (ev ∘ wZ) := by
    simpa only [GZ, FormalGroup.map_smul, FormalGroup.map_pTypicalStrictCoordinate,
      map_hazewinkelIntegralFormalGroup, hev_v, hev_t] using
      congrArg (fun F : FormalGroup UZ ↦ F.map ev) hwZ_eq
  exact ⟨ev ∘ wZ, hR, fun w' hw' ↦ hazewinkelIntegralFormalGroup_injective p (hw'.symm.trans hR)⟩

private def pTypicalInvParamsAux (p : ℕ) (F : FormalGroup R) (ψ : PowerSeries R) : ℕ → R
  | n => PowerSeries.coeff (p ^ (n + 1)) ψ -
      PowerSeries.coeff (p ^ (n + 1)) (F.pTypicalStrictCurve p fun i ↦
        if h : (i : ℕ) - 1 < n then pTypicalInvParamsAux p F ψ ((i : ℕ) - 1) else 0).toPowerSeries
decreasing_by exact h

/-- **Classification of strict isomorphisms between Hazewinkel laws over `p`-local rings**:
when every prime `q ≠ p` is a unit in `R`, any strict coordinate `φ` satisfying
`φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w` equals
`pTypicalStrictCoordinate p t` for a unique `t : ℕ+ → R`. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {v w : ℕ+ → R}
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1)
    (hsmul : φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) :
    ∃! t : ℕ+ → R, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t := by
  let F_v := hazewinkelIntegralFormalGroup p v
  let t : ℕ+ → R := fun i ↦ pTypicalInvParamsAux p F_v φ⁻¹.toPowerSeries ((i : ℕ) - 1)
  have hpow_step (n : ℕ) : PowerSeries.coeff (p ^ (n + 1)) φ⁻¹.toPowerSeries =
      PowerSeries.coeff (p ^ (n + 1)) (F_v.pTypicalStrictCurve p t).toPowerSeries := by
    let s_n : ℕ+ → R := fun i ↦
      if (i : ℕ) - 1 < n then pTypicalInvParamsAux p F_v φ⁻¹.toPowerSeries ((i : ℕ) - 1) else 0
    have hstep := F_v.coeff_pow_succ_pTypicalStrictCurve_sub hp.out.one_lt
      (t := t) (t' := s_n) (n := n) fun i hi ↦ by
        have hi' : (i : ℕ) - 1 < n := by have := i.pos; omega
        simp [t, s_n, hi']
    have htn : t n.succPNat = PowerSeries.coeff (p ^ (n + 1)) φ⁻¹.toPowerSeries -
        PowerSeries.coeff (p ^ (n + 1)) (F_v.pTypicalStrictCurve p s_n).toPowerSeries := by
      dsimp only [t]; rw [Nat.succPNat_coe, Nat.succ_sub_one, pTypicalInvParamsAux]; rfl
    rw [map_sub, htn, show s_n n.succPNat = 0 by simp [s_n], sub_zero] at hstep
    linear_combination -hstep
  have hmatch : ∀ d : ℕ, PowerSeries.coeff d φ⁻¹.toPowerSeries =
      PowerSeries.coeff d (F_v.pTypicalStrictCurve p t).toPowerSeries := fun d ↦ by
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      rcases d with _ | _ | d
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_zero_eq_constantCoeff_apply, φ⁻¹.constantCoeff_toPowerSeries,
          (F_v.pTypicalStrictCurve p t).constantCoeff_toPowerSeries]
      · rw [← FormalCoordinate.val_linearCoeff, map_inv, hφ, inv_one, Units.val_one,
          F_v.coeff_one_pTypicalStrictCurve]
      · by_cases hpow : ∃ k : ℕ+, p ^ (k : ℕ) = d + 2
        · obtain ⟨k, hkm⟩ := hpow
          rw [← hkm, (Nat.succ_pred_eq_of_pos k.pos).symm]; exact hpow_step k.natPred
        · push Not at hpow
          set m := d + 2
          let φ_t := F_v.pTypicalStrictCoordinate p t
          obtain ⟨w_t, hw_t, _⟩ :=
            existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p v t
          have hη_smul : (φ * φ_t⁻¹) • hazewinkelIntegralFormalGroup p w_t =
              hazewinkelIntegralFormalGroup p w := by rw [← hw_t, mul_smul, inv_smul_smul, hsmul]
          set c := PowerSeries.coeff m (F_v.pTypicalStrictCurve p t).toPowerSeries -
            PowerSeries.coeff m φ⁻¹.toPowerSeries
          obtain ⟨r, hr⟩ : PowerSeries.X ^ m ∣
              (F_v.pTypicalStrictCurve p t).toPowerSeries - φ⁻¹.toPowerSeries :=
            PowerSeries.X_pow_dvd_iff.mpr fun j hj ↦ by rw [map_sub, ih j hj, sub_self]
          have hr0 : PowerSeries.constantCoeff r = c := by
            simpa [c, PowerSeries.coeff_X_pow_mul',
              PowerSeries.coeff_zero_eq_constantCoeff_apply] using
              (congrArg (PowerSeries.coeff m) hr).symm
          obtain ⟨s, hη_series, hs_c⟩ := exists_toPowerSeries_mul_eq_X_add_X_pow_mul (ψ := φ_t⁻¹)
            hφ (by omega : m ≠ 0) (r := r)
            (by rw [FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]; linear_combination hr)
          obtain ⟨hF_ord, hhom⟩ :=
            order_and_homogeneousComponent_of_smul_eq hη_smul (by omega : m ≠ 0) hη_series
          have hw_eq : ∀ r : ℕ, ∀ i : ℕ+, (i : ℕ) ≤ r → p ^ (i : ℕ) ≤ m → w_t i = w i := fun r ↦ by
            induction r with
            | zero => intro i hi _; have := i.pos; omega
            | succ r ihr =>
              intro i hi hpim; rcases lt_or_eq_of_le hi with hlt | heq
              · exact ihr i (Nat.lt_succ_iff.mp hlt) hpim
              · obtain rfl : i = r.succPNat := PNat.coe_injective heq
                have hplt : p ^ (r + 1) < m := lt_of_le_of_ne hpim (hpow r.succPNat)
                have hhom' := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p (v := w_t)
                  (w := w) (n := r) fun j hj ↦
                    ihr j hj ((Nat.pow_le_pow_right hp.out.pos (Nat.le_succ_of_le hj)).trans hpim)
                rw [homogeneousComponent_of_lt_order_eq_zero
                    ((Nat.cast_lt.mpr hplt).trans_le hF_ord), eq_comm, neg_eq_zero] at hhom'
                exact sub_eq_zero.mp <| (smul_lazardCocycle_eq_zero_iff
                  (hp.out.two_le.trans (Nat.le_self_pow r.succ_ne_zero p))).mp <|
                  MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])
          have hsucc_ord : ((m + 1 : ℕ) : ℕ∞) ≤
              ((hazewinkelIntegralFormalGroup p w_t).toPowerSeries -
                (hazewinkelIntegralFormalGroup p w).toPowerSeries).order :=
            (Nat.cast_le.mpr (Nat.lt_pow_succ_log_self hp.out.one_lt m)).trans <|
              le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le p fun i hi ↦
                hw_eq (Nat.log p m) i hi
                  ((Nat.pow_le_pow_right hp.out.pos hi).trans (Nat.pow_log_le_self p (by omega)))
          rw [homogeneousComponent_of_lt_order_eq_zero
              ((Nat.cast_lt.mpr (Nat.lt_succ_self m)).trans_le hsucc_ord),
            hs_c, hr0, eq_comm, neg_eq_zero] at hhom
          have hpoly : ((lazardGcd m : R) * c) • lazardCocycle m R = 0 := by
            have h1 : c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ m - MvPolynomial.X 0 ^ m -
                MvPolynomial.X 1 ^ m : MvPolynomial (Fin 2) R) = 0 :=
              MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])
            rwa [← lazardGcd_nsmul_lazardCocycle (R := R) (by omega : m ≠ 0),
              ← Nat.cast_smul_eq_nsmul R, smul_smul, mul_comm] at h1
          have hunit : IsUnit (lazardGcd m : R) := by
            by_cases hpp : IsPrimePow m
            · obtain ⟨q, k, hq, hk, hmk⟩ := (isPrimePow_nat_iff m).1 hpp
              rw [← hmk, lazardGcd_prime_pow hq hk.ne']
              exact hlocal q hq fun hqp ↦ hpow ⟨k, hk⟩ (hqp ▸ hmk)
            · rw [lazardGcd_eq_one_of_not_isPrimePow (by omega) hpp, Nat.cast_one]; exact isUnit_one
          exact (sub_eq_zero.mp (hunit.mul_right_eq_zero.mp
            ((smul_lazardCocycle_eq_zero_iff (by omega)).mp hpoly))).symm
  have hφ_eq : φ = F_v.pTypicalStrictCoordinate p t := by
    apply inv_injective; ext1
    rw [FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]
    exact PowerSeries.ext hmatch
  exact ⟨t, hφ_eq, fun t' ht' ↦
    F_v.pTypicalStrictCoordinate_injective hp.out.one_lt (ht'.symm.trans hφ_eq)⟩

/-- When every prime `q ≠ p` is invertible in `R`, a strict formal coordinate `φ` transports
`hazewinkelIntegralFormalGroup p v` into `Set.range (hazewinkelIntegralFormalGroup p)` if and only
if `φ` is `(hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t` for some `t`. -/
theorem exists_hazewinkelIntegralFormalGroup_eq_smul_iff
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (v : ℕ+ → R)
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1) :
    (∃ w : ℕ+ → R, φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) ↔
      ∃ t : ℕ+ → R, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t := by
  refine ⟨fun ⟨_, hw⟩ ↦ ?_, fun ⟨t, ht⟩ ↦ ht ▸ ?_⟩
  · obtain ⟨t, ht, _⟩ := existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ hw
    exact ⟨t, ht⟩
  · obtain ⟨w, hw, _⟩ := existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup
      p v t
    exact ⟨w, hw⟩

end Classification

end TauCeti
