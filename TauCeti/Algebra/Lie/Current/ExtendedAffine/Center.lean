/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import TauCeti.Algebra.Lie.Current.Center
public import TauCeti.Algebra.Lie.Current.ExtendedAffine.Completion
public import TauCeti.RingTheory.PowerSeries.LinearTopology

/-!
# The center of the completed extended enveloping algebra and center reduction

Centrality in `Û'` is detected on `d̂` and `i(Û)` (`mem_center_extendedCompletedEnveloping_iff`).
When `[D, x] = δ₁(x)`, `D' = d̂ - i(D)` is central (`shiftedDegreeElement_mem_center`),
`PS₀ ≃ₐ[R] Û'` (`extendedCompletedRestrictedEquiv`), and `Z(Û') ≤ R[D']` implies `Z(Û) = ⊥`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §4.3.2.
-/

public section

noncomputable section

open Filter Topology
open scoped PowerSeries

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {Φ : LinearMap.BilinForm R L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : R}

local notation "Û" => CompletedEnveloping Φ hΦ hΦs a
local notation "Û'" => ExtendedCompletedEnveloping Φ hΦ hΦs a
local notation "i" => completedToExtended Φ hΦ hΦs a
local notation "d̂" => completedDegreeElement Φ hΦ hΦs a
local notation "δ₁" => vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1)

/-- **Centrality in `Û'` is detected on `d̂` and `Û`.** -/
theorem mem_center_extendedCompletedEnveloping_iff {z : Û'} :
    z ∈ Subalgebra.center R Û' ↔ Commute d̂ z ∧ ∀ x : Û, Commute (i x) z := by
  rw [Subalgebra.mem_center_iff_forall_commute_of_topologicalClosure_adjoin_eq_top
    (topologicalClosure_adjoin_insert_completedDegreeElement_range_completedToExtended Φ hΦ hΦs a),
    Set.forall_mem_insert, Set.forall_mem_range]

/-- `i x` is central in `Û'` iff `x` is central in `Û` and annihilated by `δ₁ = t d/dt`. -/
theorem completedToExtended_mem_center_iff {x : Û} :
    i x ∈ Subalgebra.center R Û' ↔ x ∈ Subalgebra.center R Û ∧ (δ₁ : Module.End R Û) x = 0 := by
  rw [mem_center_extendedCompletedEnveloping_iff]
  refine ⟨fun ⟨hd, hx⟩ ↦ ⟨Subalgebra.mem_center_iff.2 fun y ↦
      completedToExtended_injective Φ hΦ hΦs a (by simpa only [map_mul] using (hx y).eq),
    completedToExtended_injective Φ hΦ hΦs a ?_⟩, fun ⟨hx, hδ⟩ ↦ ⟨?_, fun y ↦ ?_⟩⟩
  · rw [map_zero, ← completedDegreeElement_mul_completedToExtended_sub_mul, hd.eq, sub_self]
  · rw [Commute, SemiconjBy, ← sub_eq_zero,
      completedDegreeElement_mul_completedToExtended_sub_mul, hδ, map_zero]
  · rw [Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hx y]

section ShiftedDegree

variable (Φ hΦ hΦs a) in
/-- **The shifted degree element** `D' = d̂ - i(D) ∈ Û'` associated to `D ∈ Û`. -/
def shiftedDegreeElement (D : Û) : Û' := d̂ - i D

variable {D : CompletedEnveloping Φ hΦ hΦs a}

local notation "D'" => shiftedDegreeElement Φ hΦ hΦs a D

theorem completedDegreeDerivation_eq_zero_of_commutator
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    (δ₁ : Module.End R Û) D = 0 := by rw [← hD D, sub_self]

theorem commute_completedDegreeElement_completedToExtended
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) : Commute d̂ (i D) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, completedDegreeElement_mul_completedToExtended_sub_mul,
    completedDegreeDerivation_eq_zero_of_commutator hD, map_zero]

/-- **Centrality of the shifted degree element** `D' = d̂ - i(D)` when `[D, x] = δ₁(x)`. -/
theorem shiftedDegreeElement_mem_center
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) : D' ∈ Subalgebra.center R Û' := by
  rw [mem_center_extendedCompletedEnveloping_iff]
  refine ⟨(Commute.refl d̂).sub_right (commute_completedDegreeElement_completedToExtended hD),
    fun x ↦ Commute.symm ?_⟩
  rw [Commute, SemiconjBy, shiftedDegreeElement, ← sub_eq_zero,
    show (d̂ - i D) * i x - i x * (d̂ - i D) = (d̂ * i x - i x * d̂) - (i D * i x - i x * i D) by
      rw [mul_sub, sub_mul]; abel,
    completedDegreeElement_mul_completedToExtended_sub_mul, ← map_mul, ← map_mul, ← map_sub, hD x,
    sub_self]

local notation "Î" => completedOrderLeftIdeal Φ hΦ hΦs a
local notation "Î'" => completedExtendedOrderLeftIdeal Φ hΦ hΦs a
local notation "coeff̂" => completedDegreeCoeff Φ hΦ hΦs a
local notation "oTower" => orderQuotientTower Φ hΦ hΦs a
local notation "eTower" => extendedOrderQuotientTower Φ hΦ hΦs a
local notation "PS₀" => PowerSeries.coeffTendstoZeroSubalgebra R Û
local notation "C₀" => PowerSeries.coeffTendstoZeroCAlgHom R Û
local notation "X₀" => PowerSeries.coeffTendstoZeroX R Û

theorem mul_mem_completedOrderLeftIdeal_of_commutator
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ} {x : Û} (hx : x ∈ Î n) :
    x * D ∈ Î n := by
  rw [show x * D = D * x - (D * x - x * D) by abel, hD x]
  exact sub_mem (Submodule.smul_mem _ D hx)
    (vectorFieldCompletedEnvelopingDerivation_mem_completedOrderLeftIdeal Φ hΦ hΦs a
      (HahnSeries.single 1 1) HahnSeries.orderTop_single_le hx)

theorem mul_pow_mem_completedOrderLeftIdeal_of_commutator
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ} {x : Û} (hx : x ∈ Î n)
    (k : ℕ) : x * D ^ k ∈ Î n :=
  Nat.rec (by simpa using hx) (fun k ih ↦ by
    rw [pow_succ, ← mul_assoc]; exact mul_mem_completedOrderLeftIdeal_of_commutator hD ih) k

private theorem mul_term_mem {n : ℕ} {x y : Û} (hy : ∀ z ∈ Î n, z * y ∈ Î n) (hx : x ∈ Î n)
    (k c : ℕ) : x * y ^ k * (c : Û) ∈ Î n := by
  rw [← (Nat.cast_commute c _).eq]
  exact Submodule.smul_mem _ (c : Û) (Nat.rec (by simpa using hx) (fun k ih ↦ by
    rw [pow_succ, ← mul_assoc]; exact hy _ ih) k)

/-- Binomial expansion of `i(u) * (D')^j` in the basis of right powers of `d̂`. -/
theorem completedToExtended_mul_shiftedDegreeElement_pow
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (u : Û) (j : ℕ) :
    i u * D' ^ j = ∑ r ∈ Finset.range (j + 1), i (u * (-D) ^ (j - r) * j.choose r) * d̂ ^ r := by
  have hc : Commute d̂ (i (-D)) :=
    (map_neg i D).symm ▸ (commute_completedDegreeElement_completedToExtended hD).neg_right
  rw [show D' = d̂ + i (-D) by rw [shiftedDegreeElement, map_neg, sub_eq_add_neg],
    hc.add_pow, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hcr : Commute (d̂ ^ r) (i ((-D) ^ (j - r) * j.choose r)) := by
    rw [map_mul, map_pow, map_natCast]
    exact ((hc.pow_left r).pow_right (j - r)).mul_right ((Nat.cast_commute _ _).symm)
  rw [mul_assoc (d̂ ^ r), ← map_pow, ← map_natCast i, ← map_mul, hcr.eq, ← mul_assoc, ← map_mul,
    ← mul_assoc]

@[simp] theorem completedDegreeCoeff_completedToExtended_mul_shiftedDegreeElement_pow
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (k : ℕ) (u : Û) (j : ℕ) :
    coeff̂ k (i u * D' ^ j) = if k ≤ j then u * (-D) ^ (j - k) * j.choose k else 0 := by
  rw [completedToExtended_mul_shiftedDegreeElement_pow hD, map_sum]
  simp only [completedDegreeCoeff_completedToExtended_mul_pow, Finset.sum_ite_eq',
    Finset.mem_range, Nat.lt_succ_iff]

/-- Inverse binomial expansion of `i(u) * d̂^m` in powers of `D' = d̂ - i(D)`. -/
theorem completedToExtended_mul_completedDegreeElement_pow_eq_sum_shiftedDegreeElement
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (u : Û) (m : ℕ) :
    i u * d̂ ^ m = ∑ j ∈ Finset.range (m + 1), i (u * D ^ (m - j) * m.choose j) * D' ^ j := by
  have hz := shiftedDegreeElement_mem_center hD
  have hc : Commute D' (i D) := (Subalgebra.mem_center_iff.1 hz (i D)).symm
  rw [show d̂ = D' + i D from (sub_add_cancel d̂ (i D)).symm, hc.add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcj := (Subalgebra.mem_center_iff.1 (pow_mem hz j) (i (D ^ (m - j) * m.choose j))).symm
  rw [mul_assoc (D' ^ j), ← map_pow, ← map_natCast i, ← map_mul, hcj, ← mul_assoc, ← map_mul,
    ← mul_assoc]

private abbrev DegImpl (D : Û) : Prop := ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x
private def evalShifted (hD : DegImpl D) : PS₀ →ₐ[R] Û' :=
  PowerSeries.coeffTendstoZeroEval (continuous_completedToExtended Φ hΦ hΦs a)
    (shiftedDegreeElement_mem_center hD)
private theorem mul_shifted_pow_mem (hD : DegImpl D) {n : ℕ} {u : Û} (hu : u ∈ Î n) (j : ℕ) :
    i u * D' ^ j ∈ Î' n := by
  rw [Subalgebra.mem_center_iff.1 (pow_mem (shiftedDegreeElement_mem_center hD) j) (i u)]
  exact Submodule.smul_mem _ _ (completedToExtended_mem_completedExtendedOrderLeftIdeal_iff.2 hu)
private theorem limπ_eval_eq_sum (hD : DegImpl D) (f : PS₀) (n J : ℕ)
    (hJ : ∀ j ≥ J, PowerSeries.coeff j (f : Û⟦X⟧) ∈ Î n) :
    (eTower).limπ n (evalShifted hD f) =
      (eTower).limπ n (∑ j ∈ Finset.range J, i (PowerSeries.coeff j (f : Û⟦X⟧)) * D' ^ j) := by
  rw [evalShifted, PowerSeries.coeffTendstoZeroEval_apply, ModuleTower.limπ_tsum_eq_sum _
    (PowerSeries.summable_apply_coeff_mul_pow_of_mem_center
      (continuous_completedToExtended Φ hΦ hΦs a) (shiftedDegreeElement_mem_center hD) f)
    n (Finset.range J), map_sum]
  intro j hj; rw [← mem_completedExtendedOrderLeftIdeal]
  exact mul_shifted_pow_mem hD (hJ j (Nat.le_of_not_lt (Finset.mem_range.not.1 hj))) j

private theorem eval_mem_iff (hD : DegImpl D) {n : ℕ} {f : PS₀} :
    evalShifted hD f ∈ Î' n ↔ ∀ j, PowerSeries.coeff j (f : Û⟦X⟧) ∈ Î n := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := eventually_atTop.1
      (((hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff.1
        (PowerSeries.mem_coeffTendstoZeroSubalgebra_iff.1 f.2)) n trivial)
    have hS : (∑ j ∈ Finset.range J, i (PowerSeries.coeff j (f : Û⟦X⟧)) * D' ^ j) ∈ Î' n := by
      rw [mem_completedExtendedOrderLeftIdeal, ← limπ_eval_eq_sum hD f n J hJ]
      exact mem_completedExtendedOrderLeftIdeal.1 hf
    suffices hback : ∀ m : ℕ, ∀ j ≥ J - m, PowerSeries.coeff j (f : Û⟦X⟧) ∈ Î n from
      fun j ↦ hback J j (by simp)
    intro m; induction m with
    | zero => intro j hj; exact hJ j (by simpa using hj)
    | succ m ih =>
      intro j hj; by_cases hjm : J - m ≤ j; · exact ih j hjm
      have hjJ := Finset.mem_range.2 (lt_of_lt_of_le (not_le.1 hjm) (Nat.sub_le J m))
      let g : ℕ → Û := fun k ↦
        if j ≤ k then PowerSeries.coeff k (f : Û⟦X⟧) * (-D) ^ (k - j) * k.choose j else 0
      have htot : ∑ k ∈ Finset.range J, g k ∈ Î n := by
        simpa only [map_sum, completedDegreeCoeff_completedToExtended_mul_shiftedDegreeElement_pow
          hD, g] using (mem_completedExtendedOrderLeftIdeal_iff_forall_completedDegreeCoeff.1 hS) j
      rw [← Finset.add_sum_erase _ _ hjJ] at htot
      have hrest : ∑ k ∈ (Finset.range J).erase j, g k ∈ Î n := sum_mem fun k hk ↦ by
        have hne : k ≠ j := (Finset.mem_erase.1 hk).1; dsimp only [g]; split_ifs with hjk
        · exact mul_term_mem (fun _ hz ↦ by
            rw [mul_neg]; exact neg_mem (mul_mem_completedOrderLeftIdeal_of_commutator hD hz))
            (ih k (by omega)) (k - j) (k.choose j)
        · exact zero_mem _
      have hgj := sub_mem htot hrest; rw [add_sub_cancel_right] at hgj; simpa [g] using hgj
  · rw [mem_completedExtendedOrderLeftIdeal, limπ_eval_eq_sum hD f n 0 (fun j _ ↦ hf j),
      Finset.range_zero, Finset.sum_empty, map_zero]

private theorem exists_coeff_mem (w : Û') (n : ℕ) : ∃ M, ∀ m ≥ M, coeff̂ m w ∈ Î n :=
  eventually_atTop.1 (((hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff.1
    (tendsto_completedDegreeCoeff_atTop Φ hΦ hΦs a w)) n trivial)
private theorem summable_term (hD : DegImpl D) (w : Û') (j : ℕ) :
    Summable fun k ↦ coeff̂ (j + k) w * D ^ k * (j + k).choose j := by
  rw [ModuleTower.summable_iff_forall_eventually_limπ_eq_zero]; intro n; rw [Nat.cofinite_eq_atTop]
  obtain ⟨M, hM⟩ := exists_coeff_mem w n
  filter_upwards [eventually_ge_atTop M] with k hk; rw [← mem_completedOrderLeftIdeal]
  exact mul_term_mem (fun _ ↦ mul_mem_completedOrderLeftIdeal_of_commutator hD)
    (hM (j + k) (by omega)) k ((j + k).choose j)
private theorem limπ_tsum_term (hD : DegImpl D) (w : Û') (j n M : ℕ)
    (hM : ∀ m ≥ M, coeff̂ m w ∈ Î n) :
    (oTower).limπ n (∑' k, coeff̂ (j + k) w * D ^ k * (j + k).choose j) =
      (oTower).limπ n
        (∑ k ∈ Finset.range (M - j), coeff̂ (j + k) w * D ^ k * (j + k).choose j) := by
  rw [ModuleTower.limπ_tsum_eq_sum _ (summable_term hD w j) n (Finset.range (M - j)), map_sum]
  intro k hk; rw [← mem_completedOrderLeftIdeal]
  have hk' : M - j ≤ k := Nat.le_of_not_lt (Finset.mem_range.not.1 hk)
  exact mul_term_mem (fun _ ↦ mul_mem_completedOrderLeftIdeal_of_commutator hD)
    (hM (j + k) (by omega)) k ((j + k).choose j)

private def seriesCoeff (D : Û) (w : Û') (j : ℕ) : Û :=
  ∑' k, coeff̂ (j + k) w * D ^ k * (j + k).choose j
private theorem tendsto_seriesCoeff (hD : DegImpl D) (w : Û') :
    Tendsto (seriesCoeff D w) atTop (𝓝 0) := by
  rw [(hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff]; rintro n -
  obtain ⟨M, hM⟩ := exists_coeff_mem w n; filter_upwards [eventually_ge_atTop M] with j hj
  rw [SetLike.mem_coe, mem_completedOrderLeftIdeal, seriesCoeff, limπ_tsum_term hD w j n M hM,
    Nat.sub_eq_zero_of_le hj, Finset.range_zero, Finset.sum_empty, map_zero]
private def invEvalFun (hD : DegImpl D) (w : Û') : PS₀ :=
  ⟨PowerSeries.mk (seriesCoeff D w), PowerSeries.mem_coeffTendstoZeroSubalgebra_iff.2
    (by simpa only [PowerSeries.coeff_mk] using tendsto_seriesCoeff hD w)⟩
private theorem coeff_invEvalFun (hD : DegImpl D) (w : Û') (j : ℕ) :
    PowerSeries.coeff j (invEvalFun hD w : Û⟦X⟧) = seriesCoeff D w j := by
  rw [invEvalFun]; exact PowerSeries.coeff_mk j (seriesCoeff D w)
private theorem limπ_sum_coeff_eq (w : Û') (n M : ℕ) (hM : ∀ m ≥ M, coeff̂ m w ∈ Î n) :
    (eTower).limπ n (∑ m ∈ Finset.range M, i (coeff̂ m w) * d̂ ^ m) = (eTower).limπ n w := by
  conv_rhs => rw [← tsum_completedDegreeCoeff_mul_completedDegreeElement_pow Φ hΦ hΦs a w]
  rw [ModuleTower.limπ_tsum_eq_sum _ (summable_completedToExtended_mul_completedDegreeElement_pow
    Φ hΦ hΦs a (tendsto_completedDegreeCoeff_atTop Φ hΦ hΦs a w)) n (Finset.range M), map_sum]
  intro m hm; rw [← mem_completedExtendedOrderLeftIdeal]
  exact mul_completedDegreeElement_pow_mem_completedExtendedOrderLeftIdeal
    (completedToExtended_mem_completedExtendedOrderLeftIdeal_iff.2
      (hM m (Nat.le_of_not_lt (Finset.mem_range.not.1 hm)))) m
private theorem limπ_eval_trunc (hD : DegImpl D) (w : Û') (n M : ℕ)
    (hM : ∀ m ≥ M, coeff̂ m w ∈ Î n) :
    (eTower).limπ n (∑ j ∈ Finset.range M,
        i (PowerSeries.coeff j (invEvalFun hD w : Û⟦X⟧)) * D' ^ j) =
      (eTower).limπ n (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (M - j),
        i (coeff̂ (j + k) w * D ^ k * (j + k).choose j) * D' ^ j) := by
  rw [map_sum, map_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← sub_eq_zero, ← map_sub, ← mem_completedExtendedOrderLeftIdeal]
  have hdiff : seriesCoeff D w j - ∑ k ∈ Finset.range (M - j),
      coeff̂ (j + k) w * D ^ k * (j + k).choose j ∈ Î n := by
    rw [mem_completedOrderLeftIdeal, map_sub, sub_eq_zero, seriesCoeff]
    exact limπ_tsum_term hD w j n M hM
  have hmul : i (PowerSeries.coeff j (invEvalFun hD w : Û⟦X⟧)) * D' ^ j -
      ∑ k ∈ Finset.range (M - j), i (coeff̂ (j + k) w * D ^ k * (j + k).choose j) * D' ^ j =
      i (seriesCoeff D w j - ∑ k ∈ Finset.range (M - j),
        coeff̂ (j + k) w * D ^ k * (j + k).choose j) * D' ^ j := by
    rw [coeff_invEvalFun, map_sub, sub_mul, map_sum, Finset.sum_mul]
  rw [hmul]; exact mul_shifted_pow_mem hD hdiff j

private theorem eval_invEvalFun (hD : DegImpl D) (w : Û') :
    evalShifted hD (invEvalFun hD w) = w := by
  refine ModuleTower.lim_ext _ fun n ↦ ?_
  obtain ⟨M, hM⟩ := exists_coeff_mem w n
  have hfM : ∀ j ≥ M, PowerSeries.coeff j (invEvalFun hD w : Û⟦X⟧) ∈ Î n := fun j hj ↦ by
    rw [coeff_invEvalFun, seriesCoeff, mem_completedOrderLeftIdeal, limπ_tsum_term hD w j n M hM,
      Nat.sub_eq_zero_of_le hj, Finset.range_zero, Finset.sum_empty, map_zero]
  rw [limπ_eval_eq_sum hD (invEvalFun hD w) n M hfM, limπ_eval_trunc hD w n M hM,
    ← Finset.sum_range_diag_flip M
      (fun j k ↦ i (coeff̂ (j + k) w * D ^ k * (j + k).choose j) * D' ^ j)]
  have hdiag : (∑ m ∈ Finset.range M, ∑ j ∈ Finset.range (m + 1),
        i (coeff̂ (j + (m - j)) w * D ^ (m - j) * (j + (m - j)).choose j) * D' ^ j) =
      ∑ m ∈ Finset.range M, i (coeff̂ m w) * d̂ ^ m :=
    Finset.sum_congr rfl fun m _ ↦ by
      rw [completedToExtended_mul_completedDegreeElement_pow_eq_sum_shiftedDegreeElement hD]
      exact Finset.sum_congr rfl fun j hj ↦ by
        rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.1 hj))]
  rw [hdiag]; exact limπ_sum_coeff_eq w n M hM

/-- **Restricted formal power series decomposition** `PS₀ ≃ₐ[R] Û'` via `C x ↦ i(x)`, `X ↦ D'`. -/
def extendedCompletedRestrictedEquiv
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) : PS₀ ≃ₐ[R] Û' :=
  AlgEquiv.ofBijective (evalShifted hD)
    ⟨(injective_iff_map_eq_zero _).2 fun f hf ↦ Subtype.ext <| PowerSeries.ext fun j ↦ by
        rw [Subalgebra.coe_zero, map_zero]; refine ModuleTower.lim_ext _ fun n ↦ ?_
        rw [map_zero, ← mem_completedOrderLeftIdeal]
        exact (eval_mem_iff hD).1 (hf ▸ zero_mem (Î' n)) j,
      fun w ↦ ⟨invEvalFun hD w, eval_invEvalFun hD w⟩⟩

theorem extendedCompletedRestrictedEquiv_apply
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (f : PS₀) :
    extendedCompletedRestrictedEquiv hD f = ∑' n, i (PowerSeries.coeff n (f : Û⟦X⟧)) * D' ^ n :=
  PowerSeries.coeffTendstoZeroEval_apply _ _ f

@[simp]
theorem extendedCompletedRestrictedEquiv_C
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (x : Û) :
    extendedCompletedRestrictedEquiv hD (C₀ x) = i x :=
  PowerSeries.coeffTendstoZeroEval_C _ _ x

@[simp]
theorem extendedCompletedRestrictedEquiv_X
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    extendedCompletedRestrictedEquiv hD X₀ = D' :=
  PowerSeries.coeffTendstoZeroEval_X _ _

@[simp]
theorem extendedCompletedRestrictedEquiv_symm_completedToExtended
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (x : Û) :
    (extendedCompletedRestrictedEquiv hD).symm (i x) = C₀ x :=
  AlgEquiv.symm_apply_eq _ |>.2 (extendedCompletedRestrictedEquiv_C hD x).symm

@[simp]
theorem extendedCompletedRestrictedEquiv_symm_shiftedDegreeElement
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    (extendedCompletedRestrictedEquiv hD).symm D' = X₀ :=
  AlgEquiv.symm_apply_eq _ |>.2 (extendedCompletedRestrictedEquiv_X hD).symm

theorem extendedCompletedRestrictedEquiv_mem_completedExtendedOrderLeftIdeal_iff
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ} {f : PS₀} :
    extendedCompletedRestrictedEquiv hD f ∈ Î' n ↔ ∀ j, PowerSeries.coeff j (f : Û⟦X⟧) ∈ Î n :=
  eval_mem_iff hD

/-- **The image of `Û` and the scalar polynomials in `D'` intersect only in `R`.** -/
@[simp]
theorem range_completedToExtended_inf_adjoin_shiftedDegreeElement
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    (i).range ⊓ Algebra.adjoin R {D'} = ⊥ := by
  let e := extendedCompletedRestrictedEquiv hD
  rw [eq_bot_iff]; rintro w ⟨hx, hw⟩; rcases (AlgHom.mem_range _).1 hx with ⟨x, rfl⟩
  have hmem : e.symm (i x) ∈ (C₀).range ⊓ Algebra.adjoin R ({X₀} : Set PS₀) := by
    refine ⟨(AlgHom.mem_range _).2
      ⟨x, (extendedCompletedRestrictedEquiv_symm_completedToExtended hD x).symm⟩,
      SetLike.mem_coe.2 ?_⟩
    have hmap : e.symm (i x) ∈ (Algebra.adjoin R {D'}).map e.symm.toAlgHom := ⟨i x, hw, rfl⟩
    simpa only [AlgHom.map_adjoin, Set.image_singleton, AlgEquiv.coe_toAlgHom, e,
      extendedCompletedRestrictedEquiv_symm_shiftedDegreeElement] using hmap
  rw [PowerSeries.range_coeffTendstoZeroCAlgHom_inf_adjoin_X, Algebra.mem_bot] at hmem
  rcases hmem with ⟨r, hr⟩; exact Algebra.mem_bot.2
    ⟨r, by simpa only [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using congrArg e hr⟩

/-- **Center reduction from `Û'` to `Û`.** If `Z(Û') ≤ R[D']`, then `Z(Û) = ⊥`. -/
theorem center_completedEnveloping_eq_bot_of_center_extended_le_adjoin
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x)
    (hZ : Subalgebra.center R Û' ≤ Algebra.adjoin R {D'}) : Subalgebra.center R Û = ⊥ := by
  let e := extendedCompletedRestrictedEquiv hD
  refine PowerSeries.center_eq_bot_of_center_coeffTendstoZeroSubalgebra_le_adjoin fun f hf ↦ ?_
  have hef : e f ∈ Subalgebra.center R Û' := Subalgebra.mem_center_iff.2 fun y ↦ by
    obtain ⟨g, rfl⟩ := e.surjective y; rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hf g]
  have hmap : e.symm (e f) ∈ (Algebra.adjoin R {D'}).map e.symm.toAlgHom := ⟨e f, hZ hef, rfl⟩
  simpa only [AlgEquiv.symm_apply_apply, AlgHom.map_adjoin, Set.image_singleton,
    AlgEquiv.coe_toAlgHom, e, extendedCompletedRestrictedEquiv_symm_shiftedDegreeElement] using hmap

end ShiftedDegree

end TauCeti.CurrentAlgebra
