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
`C_{p^(n + 1)}` (`TauCeti.homogeneousComponent_hazewinkelIntegralFormalGroup_sub`) gives parameter
recovery from order bounds (`TauCeti.eq_of_le_order_hazewinkelIntegralFormalGroup_sub`), universal
injectivity (`TauCeti.hazewinkelIntegralFormalGroup_injective`), parameter descent along injective
ring homomorphisms (`TauCeti.exists_hazewinkelIntegralFormalGroup_eq_of_map_eq`), universal
integrality of strict `p`-typical coordinate transport
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
  simp [pTypicalStrictCurve, not_lt.mpr hp]

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
        rw [pTypicalStrictCurveStage, ih, (by ext; simp [pTypicalMonomialCurve] :
          pTypicalMonomialCurve F ((0 : ℕ+ → R) n.succPNat) (p ^ (n + 1))
            (pow_ne_zero _ (by omega)) = 0), _root_.add_zero]
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
    have hk : k < p ^ (k + 1) := k.lt_succ_self.trans ((k + 1).lt_pow_self hp)
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
  rw [coeff_pTypicalStrictCurve_eq_stage _ hp t (k.lt_succ_self.trans ((k + 1).lt_pow_self hp)),
    hstage k, map_add, PowerSeries.coeff_X, map_sum]
  rcases eq_or_ne k 1 with rfl | hk1
  · simp [hp.ne]
  · simp only [hk1, ite_false, _root_.zero_add]; split_ifs with hex
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
  have hk : k < p ^ (k + 1) := k.lt_succ_self.trans ((k + 1).lt_pow_self hp)
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
        simp [pTypicalMonomialCurve, ht n.succPNat (hge.trans hj)]

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
    Function.Injective (F.pTypicalStrictCurve p) := fun t t' h ↦ by
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
  have h0 : constantCoeff (c • PowerSeries.X ^ p ^ (m + 1) : PowerSeries K) = 0 := by
    simp [← PowerSeries.constantCoeff_eq, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_X_pow, (pow_ne_zero (m + 1) (by omega : p ≠ 0)).symm]
  rw [PowerSeries.coeff_def Finsupp.single_eq_same, PowerSeries.coeff_subst_eq_sum_range_degree
    (τ := Unit) h0 (hazewinkelLog p v).toPowerSeries (Finsupp.single () k)]
  simp only [Finsupp.degree_single]
  have hoff (d : ℕ) (hne : ∀ r, p ^ r = d → k ≠ p ^ (r + m + 1)) :
      coeff (Finsupp.single () d) (hazewinkelLog p v).toPowerSeries •
        coeff (Finsupp.single () k)
          ((c • PowerSeries.X ^ p ^ (m + 1) : PowerSeries K) ^ d) = 0 := by
    by_cases hpow : ∃ r, p ^ r = d
    · obtain ⟨r, rfl⟩ := hpow
      have hne' : k ≠ p ^ (m + 1) * p ^ r := by
        rw [← pow_add, add_right_comm, add_comm m r]; exact hne r rfl
      rw [smul_pow, ← pow_mul]
      simp [← PowerSeries.coeff_def Finsupp.single_eq_same, PowerSeries.coeff_X_pow, hne']
    · push Not at hpow
      rw [← PowerSeries.coeff_def Finsupp.single_eq_same, coeff_hazewinkelLog_eq_zero v hpow,
        zero_smul]
  split_ifs with hex
  · have ⟨j, hj⟩ := hex; subst hj
    rw [(by have := Nat.pow_right_injective hp hex.choose_spec; omega : hex.choose = j),
      sum_eq_single (p ^ j)]
    · rw [← PowerSeries.coeff_def Finsupp.single_eq_same, coeff_hazewinkelLog_pow v hp j, smul_pow,
        ← pow_mul, ← pow_add, (by omega : m + 1 + j = j + m + 1)]
      simp [PowerSeries.coeff_X_pow, mul_comm]
    · exact fun d _ hdj ↦ hoff d fun r hr heq ↦ hdj <| by
        subst hr; congr 1; have := Nat.pow_right_injective hp heq; omega
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
  have hsub := PowerSeries.X_pow_dvd_iff.mp (PowerSeries.X_pow_dvd_subst_sub_subst
    (b := (FormalGroup.pTypicalStrictCurveStage F p hp t N).toPowerSeries)
    (F.pTypicalStrictCurve p t).constantCoeff_toPowerSeries
    (PowerSeries.X_pow_dvd_iff.mpr fun j hj ↦ by
      rw [map_sub, FormalGroup.coeff_pTypicalStrictCurve_eq_stage F hp t hj, sub_self])
    (hazewinkelLog p v).toPowerSeries) k hk
  rw [map_sub, sub_eq_zero] at hsub; rw [hsub]; congr 1
  have hcurve (M : ℕ) :
      (F.logHom.mapCurve (FormalGroup.pTypicalStrictCurveStage F p hp t M)).toPowerSeries =
        (hazewinkelLog p v).toPowerSeries + ∑ i ∈ range M,
          PowerSeries.subst (t i.succPNat • PowerSeries.X ^ p ^ (i + 1))
            (hazewinkelLog p v).toPowerSeries := by
    induction M with
    | zero => simp [F, FormalGroup.pTypicalStrictCurveStage]
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
    (by have := Nat.pow_right_injective hp hex.choose_spec; omega : hex.choose = n - 1 - m),
    (by congr 1; omega : (n - 1 - (n - 1 - m)).succPNat = m.succPNat), mul_comm]

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
      · rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp, coeff_hazewinkelLog_pow _ hp]
        simp
      · have ht_n : t n.succPNat = hazewinkelLogCoeff p w (n + 1) -
            hazewinkelLogCoeff p v (n + 1) - ∑ i ∈ range n,
              hazewinkelLogCoeff p v (i + 1) * t (n - (i + 1)).succPNat ^ p ^ (i + 1) := by
          dsimp only [t]; rw [Nat.natPred_succPNat, pTypicalCoordParamsRat,
            Fin.sum_univ_eq_sum_range (fun j ↦ hazewinkelLogCoeff p v (j + 1) *
              pTypicalCoordParamsRat p v w (n - (j + 1)) ^ p ^ (j + 1))]; rfl
        rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp v t (n + 1),
          coeff_hazewinkelLog_pow w hp (n + 1), sum_range_succ', pow_zero, pow_one,
          hazewinkelLogCoeff_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero, ht_n]; ring
    · push Not at hpow
      rw [coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero hp v t hpow,
        coeff_hazewinkelLog_eq_zero w hpow]
  have hcoord : (hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t =
      (hazewinkelLog p w)⁻¹ * hazewinkelLog p v := by
    apply inv_injective; rw [mul_inv_rev, inv_inv]
    rw [← (FormalCoordinate.ext <| by
      rw [FormalCoordinate.toPowerSeries_mul,
        FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate, hlog] :
      hazewinkelLog p v * ((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t)⁻¹ =
        hazewinkelLog p w), inv_mul_cancel_left]
  exact ⟨t, hcoord, fun t' ht' ↦
    (hazewinkelFormalGroup p v).pTypicalStrictCoordinate_injective hp (ht'.trans hcoord.symm)⟩

end Rational

section Comparison

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- Over a `ℚ`-algebra, agreeing parameters up to `n` give the degree-`p ^ (n + 1)` order bound
and leading Lazard cocycle difference for `hazewinkelFormalGroup`. -/
private theorem hazewinkelFormalGroup_sub_of_forall_le_rat {K : Type*} [CommRing K] [Algebra ℚ K]
    {v w : ℕ+ → K} {n : ℕ} (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤
        ((hazewinkelFormalGroup p v).toPowerSeries -
          (hazewinkelFormalGroup p w).toPowerSeries).order ∧
      homogeneousComponent (p ^ (n + 1)) ((hazewinkelFormalGroup p v).toPowerSeries -
          (hazewinkelFormalGroup p w).toPowerSeries) =
        -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) K :
            MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) := by
  set N := p ^ (n + 1); have hN0 : N ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  -- Stage 1: Compare `f_v` and `f_w` to obtain the coordinate change `η = f_w⁻¹ * f_v`.
  obtain ⟨r, hfv, hr0⟩ := exists_hazewinkelLog_eq_add_X_pow_mul hp.out.one_lt hvw
  let η : FormalCoordinate K := (hazewinkelLog p w)⁻¹ * hazewinkelLog p v
  have hη_smul : η • hazewinkelFormalGroup p v = hazewinkelFormalGroup p w := by
    simp only [η, hazewinkelFormalGroup_def, mul_smul, smul_inv_smul]
  obtain ⟨s, hη_series, hs_c⟩ := FormalCoordinate.exists_toPowerSeries_mul_eq_X_add_X_pow_mul
    (φ := (hazewinkelLog p w)⁻¹) (ψ := hazewinkelLog p v) hN0 (by simpa using hfv)
  have hη_ord : (N : ℕ∞) ≤ (η.toPowerSeries - PowerSeries.X).order :=
    PowerSeries.nat_le_order _ _ fun k hk ↦ by
      rw [hη_series, add_sub_cancel_left, PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.2 hk)]
  have hη_coeff : PowerSeries.coeff N (η.toPowerSeries - PowerSeries.X) =
      (p : ℚ)⁻¹ • (v n.succPNat - w n.succPNat) := by
    rw [hη_series, add_sub_cancel_left, PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl,
      Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hs_c, map_inv,
      linearCoeff_hazewinkelLog, inv_one, Units.val_one, one_mul, hr0]
  -- Stage 2: Transfer the order bound and leading homogeneous component from `η` to `F_v - F_w`.
  refine ⟨FormalGroup.le_order_sub_of_smul_eq hη_smul hη_ord, ?_⟩
  rw [FormalGroup.homogeneousComponent_sub_of_smul_eq hη_smul hN0 hη_ord, hη_coeff]; congr 1
  have hcoc := lazardGcd_nsmul_lazardCocycle (R := K) hN0
  rw [lazardGcd_prime_pow hp.out n.succ_ne_zero] at hcoc
  rw [← hcoc, ← Nat.cast_smul_eq_nsmul ℚ, smul_comm _ (p : ℚ), ← smul_assoc,
    smul_inv_smul₀ (Nat.cast_ne_zero.2 hp.out.ne_zero)]

/-- Rational-to-integral comparison along an injection into a `ℚ`-algebra `K`. -/
private theorem hazewinkelIntegralFormalGroup_sub_of_injective_rat {A K : Type*}
    [CommRing A] [CommRing K] [Algebra ℚ K] {ι : A →+* K} (hι : Function.Injective ι)
    {v w : ℕ+ → A} {n : ℕ} (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries).order ∧
      homogeneousComponent (p ^ (n + 1)) ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
        -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) A :
            MvPolynomial (Fin 2) A) : MvPowerSeries (Fin 2) A) := by
  set D := (hazewinkelIntegralFormalGroup p v).toPowerSeries -
    (hazewinkelIntegralFormalGroup p w).toPowerSeries
  have hmap_D : D.map ι = (hazewinkelFormalGroup p (ι ∘ v)).toPowerSeries -
      (hazewinkelFormalGroup p (ι ∘ w)).toPowerSeries := by
    simp only [D, map_sub, ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  have hrat := hazewinkelFormalGroup_sub_of_forall_le_rat p (v := ι ∘ v) (w := ι ∘ w)
    (fun i hi ↦ congrArg ι (hvw i hi))
  refine ⟨nat_le_order fun d hd ↦ hι <| by
      rw [map_zero, ← coeff_map, hmap_D]
      exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le hrat.1),
    ext fun d ↦ hι <| by
      have hcoeff := congrArg (coeff d) hrat.2
      rw [← hmap_D, coeff_homogeneousComponent, coeff_map] at hcoeff
      rw [coeff_homogeneousComponent, apply_ite ι, map_zero, hcoeff]
      simp only [map_neg, MvPolynomial.coeff_coe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul,
        map_sub, ← MvPolynomial.coeff_map, map_lazardCocycle, Function.comp_apply]⟩

/-- Over an arbitrary ring `R`, specialize the universal comparison over `ℤ[v₁, …, w₁, …]`. -/
private theorem hazewinkelIntegralFormalGroup_sub_of_forall_le {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries).order ∧
      homogeneousComponent (p ^ (n + 1)) ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
        -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) R :
            MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  let vU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦ MvPolynomial.X (Sum.inl i)
  let wU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦
    if (i : ℕ) ≤ n then MvPolynomial.X (Sum.inl i) else MvPolynomial.X (Sum.inr i)
  have hU := hazewinkelIntegralFormalGroup_sub_of_injective_rat p
    (ι := MvPolynomial.map (Int.castRingHom ℚ)) (MvPolynomial.map_injective _ Int.cast_injective)
    (v := vU) (w := wU) (n := n) fun _ hi ↦ by simp [vU, wU, hi]
  let ev : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v w)
  have hD_R : ((hazewinkelIntegralFormalGroup p vU).toPowerSeries -
      (hazewinkelIntegralFormalGroup p wU).toPowerSeries).map ev =
      (hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries := by
    simp only [map_sub, ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup,
      (funext fun _ ↦ by simp [ev, vU] : ev ∘ vU = v),
      (funext fun _ ↦ by dsimp [ev, wU]; split_ifs with hi <;> simp [hvw, hi] : ev ∘ wU = w)]
  refine ⟨hD_R ▸ hU.1.trans (le_order_map ev), ext fun d ↦ ?_⟩
  have hcoeff := congrArg (fun f ↦ ev (coeff d f)) hU.2
  rw [coeff_homogeneousComponent, apply_ite ev, map_zero, ← coeff_map, hD_R] at hcoeff
  rw [coeff_homogeneousComponent, hcoeff]
  simp only [map_neg, MvPolynomial.coeff_coe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul,
    map_sub, ← MvPolynomial.coeff_map, map_lazardCocycle, ev, vU, wU, MvPolynomial.eval₂Hom_X',
    Sum.elim_inl, Sum.elim_inr, Nat.succPNat_coe, Nat.not_succ_le_self, ite_false]

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

/-- **Parameter recovery from order bounds**: if `hazewinkelIntegralFormalGroup p v` and
`hazewinkelIntegralFormalGroup p w` agree below degree `m`, then `v i = w i` for every `i : ℕ+`
with `p ^ (i : ℕ) < m`. -/
theorem eq_of_le_order_hazewinkelIntegralFormalGroup_sub {v w : ℕ+ → R} {m : ℕ}
    (hord : (m : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order)
    {i : ℕ+} (hi : p ^ (i : ℕ) < m) : v i = w i := by
  suffices ∀ r, ∀ j : ℕ+, (j : ℕ) ≤ r → p ^ (j : ℕ) < m → v j = w j from this i i le_rfl hi
  intro r; induction r with
  | zero => intro j hj _; have := j.pos; omega
  | succ r ih =>
    intro j hj hpj; rcases lt_or_eq_of_le hj with hlt | heq
    · exact ih j (Nat.lt_succ_iff.mp hlt) hpj
    · obtain rfl : j = r.succPNat := PNat.coe_injective heq
      rw [Nat.succPNat_coe] at hpj
      have hhom := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p (v := v) (w := w)
        (n := r) fun k hk ↦
          ih k hk ((Nat.pow_le_pow_right hp.out.pos (Nat.le_succ_of_le hk)).trans_lt hpj)
      rw [homogeneousComponent_of_lt_order_eq_zero ((Nat.cast_lt.mpr hpj).trans_le hord),
        eq_comm, neg_eq_zero] at hhom
      exact sub_eq_zero.mp <| (smul_lazardCocycle_eq_zero_iff
        (hp.out.two_le.trans (Nat.le_self_pow r.succ_ne_zero p))).mp <|
        MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])

/-- If `m ≠ 0` is not a positive power of `p` and `hazewinkelIntegralFormalGroup p v` agrees with
`hazewinkelIntegralFormalGroup p w` below degree `m`, then they agree in degree `m` as well. -/
theorem succ_le_order_hazewinkelIntegralFormalGroup_sub_of_not_pow {v w : ℕ+ → R} {m : ℕ}
    (hm : m ≠ 0) (hpow : ∀ k : ℕ+, p ^ (k : ℕ) ≠ m)
    (hord : (m : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order) :
    ((m + 1 : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order :=
  (Nat.cast_le.mpr (Nat.lt_pow_succ_log_self hp.out.one_lt m)).trans <|
    le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le p fun i hi ↦
      eq_of_le_order_hazewinkelIntegralFormalGroup_sub p hord <|
        lt_of_le_of_ne ((Nat.pow_le_pow_right hp.out.pos hi).trans
          (Nat.pow_log_le_self p hm)) (hpow i)

/-- **Universal injectivity of Hazewinkel's integral formal group law** over every commutative ring
`R` (including rings with arbitrary torsion). -/
theorem hazewinkelIntegralFormalGroup_injective :
    Function.Injective (hazewinkelIntegralFormalGroup p : (ℕ+ → R) → FormalGroup R) :=
  fun _ _ h ↦ funext fun i ↦ eq_of_le_order_hazewinkelIntegralFormalGroup_sub p
    (m := p ^ (i : ℕ) + 1) (by rw [h, sub_self, order_zero]; exact le_top) (Nat.lt_succ_self _)

@[simp] theorem hazewinkelIntegralFormalGroup_eq_iff {v w : ℕ+ → R} :
    hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w ↔ v = w :=
  (hazewinkelIntegralFormalGroup_injective p).eq_iff

end Comparison

section Classification

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- **Parameter descent for Hazewinkel's integral formal group law**: along any injective ring
homomorphism `ι : A →+* B`, if `G.map ι = hazewinkelIntegralFormalGroup p wB`, then every
parameter `wB i` lies in `ι.range` and `G = hazewinkelIntegralFormalGroup p wA` for some `wA`. -/
theorem exists_hazewinkelIntegralFormalGroup_eq_of_map_eq
    {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} (hι : Function.Injective ι)
    {G : FormalGroup A} {wB : ℕ+ → B}
    (hG : G.map ι = hazewinkelIntegralFormalGroup p wB) :
    ∃ wA : ℕ+ → A, G = hazewinkelIntegralFormalGroup p wA ∧ ι ∘ wA = wB := by
  -- Descend `wB i` into `ι.range` inductively using the degree-`p ^ (n + 1)` Lazard cocycle.
  have hwB_mem : ∀ n (i : ℕ+), (i : ℕ) ≤ n → wB i ∈ ι.range := fun n ↦ by
    induction n with
    | zero => intro i hi; have := i.pos; omega
    | succ n ih =>
      intro i hi; rcases lt_or_eq_of_le hi with hlt | heq
      · exact ih i (Nat.lt_succ_iff.mp hlt)
      · obtain rfl : i = n.succPNat := PNat.coe_injective heq
        let w_trunc : ℕ+ → A := fun j ↦ if hj : (j : ℕ) ≤ n then (ih j hj).choose else 0
        have htrunc : ∀ j : ℕ+, (j : ℕ) ≤ n → wB j = (ι ∘ w_trunc) j := fun j hj ↦ by
          dsimp only [w_trunc, Function.comp_apply]; rw [dite_eq_left hj]
          exact (ih j hj).choose_spec.symm
        have hhom := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p (n := n) htrunc
        rw [(by simp [w_trunc] : (ι ∘ w_trunc) n.succPNat = 0), sub_zero, ← hG,
          ← map_hazewinkelIntegralFormalGroup] at hhom
        refine mem_range_of_coeff_smul_lazardCocycle_mem ι (m := p ^ (n + 1))
          (hp.out.two_le.trans (Nat.le_self_pow n.succ_ne_zero p)) fun j hj ↦ ?_
        rw [mem_Icc] at hj
        let d : Fin 2 →₀ ℕ := Finsupp.single 0 j + Finsupp.single 1 (p ^ (n + 1) - j)
        have hd : d.degree = p ^ (n + 1) := by
          simp [d, Finsupp.degree_eq_sum, Fin.sum_univ_two]; omega
        have hcoeff := congrArg (coeff d) hhom
        rw [coeff_homogeneousComponent, ite_eq_left hd, FormalGroup.map_toPowerSeries,
          FormalGroup.map_toPowerSeries, ← map_sub (MvPowerSeries.map ι), coeff_map, map_neg,
          MvPolynomial.coeff_coe] at hcoeff
        exact ⟨-coeff d _, by rw [map_neg, hcoeff, neg_neg]⟩
  choose wA hwA using fun i : ℕ+ ↦ RingHom.mem_range.mp (hwB_mem i.val i le_rfl)
  refine ⟨wA, FormalGroup.map_injective hι ?_, funext hwA⟩
  dsimp only; rw [hG, map_hazewinkelIntegralFormalGroup]
  exact congrArg _ (funext fun i ↦ (hwA i).symm)

/-- **Integrality of strict `p`-typical coordinate changes**: over every commutative ring `R`,
transporting `hazewinkelIntegralFormalGroup p v` along its `p`-typical strict coordinate `t`
produces `hazewinkelIntegralFormalGroup p w` for a unique sequence `w : ℕ+ → R`. -/
theorem existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup (v t : ℕ+ → R) :
    ∃! w : ℕ+ → R,
      ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
          hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w := by
  -- Stage 1: Build the universal transported law over `UZ = ℤ[v₁, …, t₁, …]` and compare in `ℚ`.
  let UZ := MvPolynomial (ℕ+ ⊕ ℕ+) ℤ
  let ι : UZ →+* MvPolynomial (ℕ+ ⊕ ℕ+) ℚ := MvPolynomial.map (Int.castRingHom ℚ)
  let vZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inl i)
  let tZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inr i)
  set GZ := ((hazewinkelIntegralFormalGroup p vZ).pTypicalStrictCoordinate p tZ) •
    hazewinkelIntegralFormalGroup p vZ
  obtain ⟨wQ, hwQ, _⟩ :=
    existsUnique_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup hp.out.one_lt (ι ∘ vZ) (ι ∘ tZ)
  have hGZ_map : GZ.map ι = hazewinkelIntegralFormalGroup p wQ := by
    rw [FormalGroup.map_smul, FormalGroup.map_pTypicalStrictCoordinate,
      map_hazewinkelIntegralFormalGroup, hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
      hwQ, ← hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  -- Stage 2: Descend `wQ` to `UZ` and specialize along `(vZ, tZ) ↦ (v, t)`.
  obtain ⟨wZ, hwZ_eq, _⟩ := exists_hazewinkelIntegralFormalGroup_eq_of_map_eq p
    (MvPolynomial.map_injective _ Int.cast_injective) hGZ_map
  let ev : UZ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v t)
  have hR : ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
      hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p (ev ∘ wZ) := by
    simpa only [GZ, FormalGroup.map_smul, FormalGroup.map_pTypicalStrictCoordinate,
      map_hazewinkelIntegralFormalGroup, (funext fun _ ↦ by simp [UZ, ev, vZ] : ev ∘ vZ = v),
      (funext fun _ ↦ by simp [UZ, ev, tZ] : ev ∘ tZ = t)] using
      congrArg (fun F : FormalGroup UZ ↦ F.map ev) hwZ_eq
  exact ⟨ev ∘ wZ, hR, fun w' hw' ↦ hazewinkelIntegralFormalGroup_injective p (hw'.symm.trans hR)⟩

private def pTypicalInvParamsAux (p : ℕ) (F : FormalGroup R) (ψ : PowerSeries R) : ℕ → R
  | n => PowerSeries.coeff (p ^ (n + 1)) ψ -
      PowerSeries.coeff (p ^ (n + 1)) (F.pTypicalStrictCurve p fun i ↦
        if h : (i : ℕ) - 1 < n then pTypicalInvParamsAux p F ψ ((i : ℕ) - 1) else 0).toPowerSeries
decreasing_by exact h

/-- The recursive parameter sequence `pTypicalInvParamsAux` matches every `X^(p ^ (n + 1))`
coefficient of `ψ` against `F.pTypicalStrictCurve`. -/
private theorem coeff_pow_succ_pTypicalStrictCurve_invParamsAux {p : ℕ} (hp1 : 1 < p)
    (F : FormalGroup R) (ψ : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (p ^ (n + 1)) ψ = PowerSeries.coeff (p ^ (n + 1))
      (F.pTypicalStrictCurve p fun i ↦ pTypicalInvParamsAux p F ψ ((i : ℕ) - 1)).toPowerSeries := by
  let t : ℕ+ → R := fun i ↦ pTypicalInvParamsAux p F ψ ((i : ℕ) - 1)
  let s_n : ℕ+ → R := fun i ↦
    if (i : ℕ) - 1 < n then pTypicalInvParamsAux p F ψ ((i : ℕ) - 1) else 0
  have hstep := F.coeff_pow_succ_pTypicalStrictCurve_sub hp1 (t := t) (t' := s_n) (n := n)
    fun i hi ↦ by simp [t, s_n, (by have := i.pos; omega : (i : ℕ) - 1 < n)]
  have htn : t n.succPNat = PowerSeries.coeff (p ^ (n + 1)) ψ -
      PowerSeries.coeff (p ^ (n + 1)) (F.pTypicalStrictCurve p s_n).toPowerSeries := by
    dsimp only [t]; rw [Nat.succPNat_coe, Nat.succ_sub_one, pTypicalInvParamsAux]; rfl
  rw [map_sub, htn, (by simp [s_n] : s_n n.succPNat = 0), sub_zero] at hstep
  linear_combination -hstep

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
  -- Stage 1: Show `φ⁻¹` agrees coefficientwise with `F_v.pTypicalStrictCurve p t`.
  have hmatch : ∀ d : ℕ, PowerSeries.coeff d φ⁻¹.toPowerSeries =
      PowerSeries.coeff d (F_v.pTypicalStrictCurve p t).toPowerSeries := fun d ↦ by
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      rcases d with _ | _ | d
      · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      · rw [← FormalCoordinate.val_linearCoeff, map_inv, hφ, inv_one, Units.val_one,
          F_v.coeff_one_pTypicalStrictCurve]
      · by_cases hpow : ∃ k : ℕ+, p ^ (k : ℕ) = d + 2
        · -- Prime-power degrees match by definition of `t`.
          obtain ⟨k, hkm⟩ := hpow
          rw [← hkm, (Nat.succ_pred_eq_of_pos k.pos).symm]
          exact coeff_pow_succ_pTypicalStrictCurve_invParamsAux hp.out.one_lt F_v _ k.natPred
        · -- Non-`p`-power degree `m = d + 2`: compare via `η = φ * φ_t⁻¹` and `d_m • C_m`.
          push Not at hpow; set m := d + 2; let φ_t := F_v.pTypicalStrictCoordinate p t
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
            simpa [c, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_zero_eq_constantCoeff_apply]
              using (congrArg (PowerSeries.coeff m) hr).symm
          obtain ⟨s, hη_series, hs_c⟩ :=
            FormalCoordinate.exists_toPowerSeries_mul_eq_X_add_X_pow_mul (φ := φ) (ψ := φ_t⁻¹)
              (by omega : m ≠ 0) (r := r) (by
                rw [FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]; linear_combination hr)
          have hη_ord : (m : ℕ∞) ≤ ((φ * φ_t⁻¹).toPowerSeries - PowerSeries.X).order :=
            PowerSeries.nat_le_order _ _ fun k hk ↦ by
              rw [hη_series, add_sub_cancel_left, PowerSeries.coeff_X_pow_mul',
                ite_eq_right (not_le.2 hk)]
          have hη_coeff : PowerSeries.coeff m ((φ * φ_t⁻¹).toPowerSeries - PowerSeries.X) = c := by
            rw [hη_series, add_sub_cancel_left, PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl,
              Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hs_c, hφ, Units.val_one,
              one_mul, hr0]
          have hhom := FormalGroup.homogeneousComponent_sub_of_smul_eq hη_smul (by omega) hη_ord
          -- Since `m` is not a power of `p`, `F_{w_t} - F_w` actually has order at least `m + 1`.
          have hsucc_ord := succ_le_order_hazewinkelIntegralFormalGroup_sub_of_not_pow p (by omega)
            hpow (FormalGroup.le_order_sub_of_smul_eq hη_smul hη_ord)
          rw [homogeneousComponent_of_lt_order_eq_zero
              ((Nat.cast_lt.mpr (Nat.lt_succ_self m)).trans_le hsucc_ord),
            hη_coeff, eq_comm, neg_eq_zero] at hhom
          -- Deduce `(lazardGcd m * c) • C_m = 0`, hence `c = 0` since `lazardGcd m` is a unit.
          have hpoly : ((lazardGcd m : R) * c) • lazardCocycle m R = 0 := by
            have h1 := MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero] :
              ((c • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ m - MvPolynomial.X 0 ^ m -
                MvPolynomial.X 1 ^ m) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) =
              ((0 : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R))
            rwa [← lazardGcd_nsmul_lazardCocycle (R := R) (by omega), ← Nat.cast_smul_eq_nsmul R,
              smul_smul, mul_comm] at h1
          exact (sub_eq_zero.mp ((isUnit_lazardGcd_of_forall_isUnit_prime hlocal (by omega)
            hpow).mul_right_eq_zero.mp ((smul_lazardCocycle_eq_zero_iff (by omega)).mp hpoly))).symm
  -- Stage 2: Conclude equality of formal coordinates and uniqueness of `t`.
  have hφ_eq : φ = F_v.pTypicalStrictCoordinate p t := by
    apply inv_injective; ext1
    rw [FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]; exact PowerSeries.ext hmatch
  exact ⟨t, hφ_eq, fun t' ht' ↦
    F_v.pTypicalStrictCoordinate_injective hp.out.one_lt (ht'.symm.trans hφ_eq)⟩

/-- When every prime `q ≠ p` is invertible in `R`, a strict formal coordinate `φ` transports
`hazewinkelIntegralFormalGroup p v` into `Set.range (hazewinkelIntegralFormalGroup p)` if and only
if `φ` is `(hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t` for some `t`. -/
theorem exists_hazewinkelIntegralFormalGroup_eq_smul_iff
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (v : ℕ+ → R)
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1) :
    (∃ w : ℕ+ → R, φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) ↔
      ∃ t : ℕ+ → R, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t :=
  ⟨fun ⟨_, hw⟩ ↦ (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ hw).exists,
    fun ⟨t, ht⟩ ↦ ht ▸
      (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p v t).exists⟩

end Classification

end TauCeti
