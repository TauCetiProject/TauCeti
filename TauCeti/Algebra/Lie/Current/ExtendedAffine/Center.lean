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

Let `Û = lim_n U / I_n` and `Û' = lim_n U' / I'_n` be the completed enveloping algebras of the
residue central extension `ĝ = L((t)) ⊕ R K` and of the extended affine algebra `ĝ' = ĝ ⋊ R d` at
the central value `a`, with canonical embedding `i : Û →ₐ[R] Û'`
(`TauCeti.CurrentAlgebra.completedToExtended`) and completed degree element `d̂ ∈ Û'`
(`TauCeti.CurrentAlgebra.completedDegreeElement`).

First, without assuming any internal realization of the degree derivation, topological generation
of `Û'` by `d̂` and `i(Û)` detects centrality in `Û'` on `d̂` and `Û`
(`TauCeti.CurrentAlgebra.mem_center_extendedCompletedEnveloping_iff`), and characterizes when `i(x)`
is central in `Û'` (`TauCeti.CurrentAlgebra.completedToExtended_mem_center_iff`).

Next, suppose an element `D ∈ Û` implements the completed degree derivation `δ₁ = t d/dt` via
`[D, x] = δ₁(x)` for all `x ∈ Û` (for instance, a normalized Segal--Sugawara mode `L₀` away from the
critical level). Then:

* **The shifted degree element is central.** Setting `D' = d̂ - i(D)`
  (`TauCeti.CurrentAlgebra.shiftedDegreeElement`), the inner derivations of `d̂` and `i(D)` cancel
  on `i(Û)` while `δ₁(D) = [D, D] = 0`, so `D' ∈ Subalgebra.center R Û'`
  (`TauCeti.CurrentAlgebra.shiftedDegreeElement_mem_center`).
* **Restricted formal power series decomposition `Û⟨⟨D'⟩⟩ ≃ₐ[R] Û'`.** Evaluating restricted formal
  power series in `PowerSeries.coeffTendstoZeroSubalgebra R Û` along `i : Û →ₐ[R] Û'` at the central
  element `D'` gives an `R`-algebra isomorphism
  `TauCeti.CurrentAlgebra.extendedCompletedRestrictedEquiv` sending `C x ↦ i(x)` and `X ↦ D'`.
* **Center reduction from `Û'` to `Û`.** Under this isomorphism, `i(Û)` and `R[D']` intersect only
  in `R` (`TauCeti.CurrentAlgebra.range_completedToExtended_inf_adjoin_shiftedDegreeElement`), and
  if `Subalgebra.center R Û' ≤ Algebra.adjoin R {D'}` then `Subalgebra.center R Û = ⊥`
  (`TauCeti.CurrentAlgebra.center_completedEnveloping_eq_bot_of_center_extended_le_adjoin`).

## Main definitions

* `TauCeti.CurrentAlgebra.shiftedDegreeElement`: the element `D' = d̂ - i(D) ∈ Û'`.
* `TauCeti.CurrentAlgebra.extendedCompletedRestrictedEquiv`: the `R`-algebra isomorphism
  `PowerSeries.coeffTendstoZeroSubalgebra R Û ≃ₐ[R] Û'` induced by `C x ↦ i(x)` and `X ↦ D'`.

## Main results

* `TauCeti.CurrentAlgebra.mem_center_extendedCompletedEnveloping_iff`: centrality in `Û'` is
  detected on `d̂` and `i(Û)`.
* `TauCeti.CurrentAlgebra.shiftedDegreeElement_mem_center`: `D' = d̂ - i(D)` is central in `Û'`
  whenever `[D, x] = δ₁(x)` for all `x ∈ Û`.
* `TauCeti.CurrentAlgebra.range_completedToExtended_inf_adjoin_shiftedDegreeElement`:
  `i(Û) ∩ R[D'] = R`.
* `TauCeti.CurrentAlgebra.center_completedEnveloping_eq_bot_of_center_extended_le_adjoin`:
  if `Z(Û') ≤ R[D']`, then `Z(Û) = ⊥`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §4.3.2, for the decomposition of the
  completed extended enveloping algebra via the shifted degree operator `d' = d - L₀` and the
  deduction of `Z(Û_κ) = ℂ` from `Z(Û'_κ) = ℂ[d']`.
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
local notation "δ₁" =>
  vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1)

/-! ### Centrality in `Û'` -/

/-- **Centrality in `Û'` is detected on `d̂` and `Û`.** An element of `Û'` is central if and only if
it commutes with `d̂` and with the image of every element of `Û`. -/
theorem mem_center_extendedCompletedEnveloping_iff {z : Û'} :
    z ∈ Subalgebra.center R Û' ↔ Commute d̂ z ∧ ∀ x : Û, Commute (i x) z := by
  rw [Subalgebra.mem_center_iff_forall_commute_of_topologicalClosure_adjoin_eq_top
    (topologicalClosure_adjoin_insert_completedDegreeElement_range_completedToExtended Φ hΦ hΦs a),
    Set.forall_mem_insert, Set.forall_mem_range]

/-- An element `x ∈ Û` maps into the center of `Û'` if and only if `x` is central in `Û` and
annihilated by the completed degree derivation `t d/dt`. -/
theorem completedToExtended_mem_center_iff {x : Û} :
    i x ∈ Subalgebra.center R Û' ↔ x ∈ Subalgebra.center R Û ∧ (δ₁ : Module.End R Û) x = 0 := by
  rw [mem_center_extendedCompletedEnveloping_iff]
  refine ⟨fun ⟨hd, hx⟩ ↦ ⟨Subalgebra.mem_center_iff.2 fun y ↦ ?_, ?_⟩, fun ⟨hx, hδ⟩ ↦ ⟨?_, ?_⟩⟩
  · exact completedToExtended_injective Φ hΦ hΦs a (by simpa only [map_mul] using (hx y).eq)
  · refine completedToExtended_injective Φ hΦ hΦs a ?_
    rw [map_zero, ← completedDegreeElement_mul_completedToExtended_sub_mul, hd.eq, sub_self]
  · rw [Commute, SemiconjBy, ← sub_eq_zero,
      completedDegreeElement_mul_completedToExtended_sub_mul, hδ, map_zero]
  · intro y
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hx y]

/-! ### The shifted degree element and restricted formal power series decomposition -/

section ShiftedDegree

variable (Φ hΦ hΦs a) in
/-- **The shifted degree element** `D' = d̂ - i(D) ∈ Û'` associated to an element `D ∈ Û`. -/
def shiftedDegreeElement (D : Û) : Û' :=
  d̂ - i D

variable {D : CompletedEnveloping Φ hΦ hΦs a}

/-- Any element `D ∈ Û` implementing `δ₁` via `[D, x] = δ₁(x)` is annihilated by `δ₁`. -/
theorem completedDegreeDerivation_eq_zero_of_commutator
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    (δ₁ : Module.End R Û) D = 0 := by
  rw [← hD D, sub_self]

/-- If `[D, x] = δ₁(x)` for all `x ∈ Û`, then `d̂` commutes with `i(D)`. -/
theorem commute_completedDegreeElement_completedToExtended
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    Commute d̂ (i D) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, completedDegreeElement_mul_completedToExtended_sub_mul,
    completedDegreeDerivation_eq_zero_of_commutator hD, map_zero]

/-- **Centrality of the shifted degree element.** If `D ∈ Û` implements the completed degree
derivation `[D, x] = δ₁(x)` for all `x ∈ Û`, then `D' = d̂ - i(D)` lies in the center of `Û'`. -/
theorem shiftedDegreeElement_mem_center
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    shiftedDegreeElement Φ hΦ hΦs a D ∈ Subalgebra.center R Û' := by
  rw [mem_center_extendedCompletedEnveloping_iff]
  refine ⟨(Commute.refl d̂).sub_right (commute_completedDegreeElement_completedToExtended hD),
    fun x ↦ ?_⟩
  rw [Commute, SemiconjBy, shiftedDegreeElement, mul_sub, sub_mul, ← sub_eq_zero]
  have h1 := completedDegreeElement_mul_completedToExtended_sub_mul Φ hΦ hΦs a x
  have h2 : i D * i x - i x * i D = i ((δ₁ : Module.End R Û) x) := by
    rw [← map_mul, ← map_mul, ← map_sub, hD x]
  have hsub : i x * (d̂ - i D) - (d̂ - i D) * i x =
      (i D * i x - i x * i D) - (d̂ * i x - i x * d̂) := by
    rw [mul_sub, sub_mul]
    abel
  rw [← mul_sub, ← sub_mul, hsub, h1, h2, sub_self]

/-- Right multiplication by an element `D ∈ Û` implementing `δ₁` preserves every stage kernel
`ker (Û → U / I_n)`. -/
theorem mul_mem_completedOrderLeftIdeal_of_commutator
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ} {x : Û}
    (hx : x ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) :
    x * D ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
  have heq : x * D = D * x - (D * x - x * D) := by abel
  rw [heq, hD x]
  exact sub_mem (Submodule.smul_mem _ D hx)
    (vectorFieldCompletedEnvelopingDerivation_mem_completedOrderLeftIdeal Φ hΦ hΦs a
      (HahnSeries.single 1 1) HahnSeries.orderTop_single_le hx)

/-- Right multiplication by `D ^ k` preserves every stage kernel `ker (Û → U / I_n)` whenever `D`
implements `δ₁`. -/
theorem mul_pow_mem_completedOrderLeftIdeal_of_commutator
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ} {x : Û}
    (hx : x ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) (k : ℕ) :
    x * D ^ k ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ, ← mul_assoc]
    exact mul_mem_completedOrderLeftIdeal_of_commutator hD ih

private theorem mul_neg_pow_mem_completedOrderLeftIdeal_of_commutator
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ} {x : Û}
    (hx : x ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) (k : ℕ) :
    x * (-D) ^ k ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, mul_neg]
    exact neg_mem (mul_mem_completedOrderLeftIdeal_of_commutator hD ih)

private theorem mul_natCast_mem_completedOrderLeftIdeal {n : ℕ} {x : Û}
    (hx : x ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) (c : ℕ) :
    x * (c : Û) ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
  rw [← (Nat.cast_commute c x).eq]
  exact Submodule.smul_mem _ (c : Û) hx

/-- Binomial expansion of `i(u) * (D')^j` in the basis of right powers of `d̂`. -/
theorem completedToExtended_mul_shiftedDegreeElement_pow
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (u : Û) (j : ℕ) :
    i u * shiftedDegreeElement Φ hΦ hΦs a D ^ j =
      ∑ r ∈ Finset.range (j + 1),
        i (u * (-D) ^ (j - r) * j.choose r) * d̂ ^ r := by
  have hc : Commute d̂ (i (-D)) := by
    rw [map_neg]
    exact (commute_completedDegreeElement_completedToExtended hD).neg_right
  have hshift : shiftedDegreeElement Φ hΦ hΦs a D = d̂ + i (-D) := by
    rw [shiftedDegreeElement, map_neg, sub_eq_add_neg]
  rw [hshift, hc.add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hcr : Commute (d̂ ^ r) (i ((-D) ^ (j - r) * j.choose r)) := by
    rw [map_mul, map_pow, map_natCast]
    exact ((hc.pow_left r).pow_right (j - r)).mul_right ((Nat.cast_commute _ _).symm)
  calc
    i u * (d̂ ^ r * i (-D) ^ (j - r) * j.choose r)
      = i u * (d̂ ^ r * i ((-D) ^ (j - r) * j.choose r)) := by
        rw [map_mul, map_pow, map_natCast, mul_assoc]
    _ = i u * (i ((-D) ^ (j - r) * j.choose r) * d̂ ^ r) := by rw [hcr.eq]
    _ = i (u * (-D) ^ (j - r) * j.choose r) * d̂ ^ r := by
        rw [← mul_assoc, ← map_mul, ← mul_assoc]

/-- The `k`-th completed `d̂`-coefficient of `i(u) * (D')^j`. -/
@[simp]
theorem completedDegreeCoeff_completedToExtended_mul_shiftedDegreeElement_pow
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (k : ℕ) (u : Û) (j : ℕ) :
    completedDegreeCoeff Φ hΦ hΦs a k (i u * shiftedDegreeElement Φ hΦ hΦs a D ^ j) =
      if k ≤ j then u * (-D) ^ (j - k) * j.choose k else 0 := by
  rw [completedToExtended_mul_shiftedDegreeElement_pow hD, map_sum]
  simp only [completedDegreeCoeff_completedToExtended_mul_pow, Finset.sum_ite_eq',
    Finset.mem_range, Nat.lt_succ_iff]

/-- Inverse binomial expansion of `i(u) * d̂^m` in powers of the central element
`D' = d̂ - i(D)`. -/
theorem completedToExtended_mul_completedDegreeElement_pow_eq_sum_shiftedDegreeElement
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (u : Û) (m : ℕ) :
    i u * d̂ ^ m =
      ∑ j ∈ Finset.range (m + 1),
        i (u * D ^ (m - j) * m.choose j) * shiftedDegreeElement Φ hΦ hΦs a D ^ j := by
  let D' := shiftedDegreeElement Φ hΦ hΦs a D
  have hz := shiftedDegreeElement_mem_center hD
  have hc : Commute D' (i D) := (Subalgebra.mem_center_iff.1 hz (i D)).symm
  have hd : d̂ = D' + i D := (sub_add_cancel d̂ (i D)).symm
  rw [hd, hc.add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcj : Commute (D' ^ j) (i (D ^ (m - j) * m.choose j)) :=
    (Subalgebra.mem_center_iff.1 (pow_mem hz j) (i (D ^ (m - j) * m.choose j))).symm
  calc
    i u * (D' ^ j * i D ^ (m - j) * m.choose j)
      = i u * (D' ^ j * i (D ^ (m - j) * m.choose j)) := by
        rw [map_mul, map_pow, map_natCast, mul_assoc]
    _ = i u * (i (D ^ (m - j) * m.choose j) * D' ^ j) := by rw [hcj.eq]
    _ = i (u * D ^ (m - j) * m.choose j) * D' ^ j := by
        rw [← mul_assoc, ← map_mul, ← mul_assoc]

/-- Evaluation of restricted formal power series over `Û` at `D' = d̂ - i(D)`. -/
private def evalShiftedDegree
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    PowerSeries.coeffTendstoZeroSubalgebra R Û →ₐ[R] Û' :=
  PowerSeries.coeffTendstoZeroEval (continuous_completedToExtended Φ hΦ hΦs a)
    (shiftedDegreeElement_mem_center hD)

private theorem completedToExtended_mul_shiftedDegreeElement_pow_mem
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ} {u : Û}
    (hu : u ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) (j : ℕ) :
    i u * shiftedDegreeElement Φ hΦ hΦs a D ^ j ∈
      completedExtendedOrderLeftIdeal Φ hΦ hΦs a n := by
  have hz := pow_mem (shiftedDegreeElement_mem_center hD) j
  rw [Subalgebra.mem_center_iff.1 hz (i u)]
  exact Submodule.smul_mem _ _ (completedToExtended_mem_completedExtendedOrderLeftIdeal_iff.2 hu)

private theorem limπ_evalShiftedDegree_eq_sum
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x)
    (f : PowerSeries.coeffTendstoZeroSubalgebra R Û) (n J : ℕ)
    (hJ : ∀ j ≥ J, PowerSeries.coeff j (f : Û⟦X⟧) ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) :
    (extendedOrderQuotientTower Φ hΦ hΦs a).limπ n (evalShiftedDegree hD f) =
      (extendedOrderQuotientTower Φ hΦ hΦs a).limπ n
        (∑ j ∈ Finset.range J,
          i (PowerSeries.coeff j (f : Û⟦X⟧)) * shiftedDegreeElement Φ hΦ hΦs a D ^ j) := by
  rw [evalShiftedDegree, PowerSeries.coeffTendstoZeroEval_apply,
    ModuleTower.limπ_tsum_eq_sum _
      (PowerSeries.summable_apply_coeff_mul_pow_of_mem_center
        (continuous_completedToExtended Φ hΦ hΦs a) (shiftedDegreeElement_mem_center hD) f)
      n (Finset.range J),
    map_sum]
  intro j hj
  rw [← mem_completedExtendedOrderLeftIdeal]
  exact completedToExtended_mul_shiftedDegreeElement_pow_mem hD
    (hJ j (Nat.le_of_not_lt (Finset.mem_range.not.1 hj))) j

private theorem evalShiftedDegree_mem_completedExtendedOrderLeftIdeal_iff
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ}
    {f : PowerSeries.coeffTendstoZeroSubalgebra R Û} :
    evalShiftedDegree hD f ∈ completedExtendedOrderLeftIdeal Φ hΦ hΦs a n ↔
      ∀ j, PowerSeries.coeff j (f : Û⟦X⟧) ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := eventually_atTop.1
      (((hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff.1
        (PowerSeries.mem_coeffTendstoZeroSubalgebra_iff.1 f.2)) n trivial)
    have hS : (∑ j ∈ Finset.range J,
        i (PowerSeries.coeff j (f : Û⟦X⟧)) * shiftedDegreeElement Φ hΦ hΦs a D ^ j) ∈
        completedExtendedOrderLeftIdeal Φ hΦ hΦs a n := by
      rw [mem_completedExtendedOrderLeftIdeal, ← limπ_evalShiftedDegree_eq_sum hD f n J hJ]
      exact mem_completedExtendedOrderLeftIdeal.1 hf
    have hback : ∀ m : ℕ, ∀ j ≥ J - m,
        PowerSeries.coeff j (f : Û⟦X⟧) ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
      intro m
      induction m with
      | zero =>
        intro j hj
        exact hJ j (by simpa using hj)
      | succ m ih =>
        intro j hj
        by_cases hjm : J - m ≤ j
        · exact ih j hjm
        · have hjJ : j ∈ Finset.range J :=
            Finset.mem_range.2 (lt_of_lt_of_le (not_le.1 hjm) (Nat.sub_le J m))
          let g : ℕ → Û := fun k ↦
            if j ≤ k then PowerSeries.coeff k (f : Û⟦X⟧) * (-D) ^ (k - j) * k.choose j else 0
          have htot : ∑ k ∈ Finset.range J, g k ∈ completedOrderLeftIdeal Φ hΦ hΦs a n := by
            have hcoeff :=
              (mem_completedExtendedOrderLeftIdeal_iff_forall_completedDegreeCoeff.1 hS) j
            simpa only [map_sum,
              completedDegreeCoeff_completedToExtended_mul_shiftedDegreeElement_pow hD, g]
              using hcoeff
          rw [← Finset.add_sum_erase _ _ hjJ] at htot
          have hrest : ∑ k ∈ (Finset.range J).erase j, g k ∈
              completedOrderLeftIdeal Φ hΦ hΦs a n := by
            refine sum_mem fun k hk ↦ ?_
            have hne : k ≠ j := (Finset.mem_erase.1 hk).1
            dsimp only [g]
            split_ifs with hjk
            · have hkge : J - m ≤ k := by omega
              exact mul_natCast_mem_completedOrderLeftIdeal
                (mul_neg_pow_mem_completedOrderLeftIdeal_of_commutator hD (ih k hkge) (k - j))
                (k.choose j)
            · exact zero_mem _
          have hgj := sub_mem htot hrest
          rw [add_sub_cancel_right] at hgj
          simpa [g] using hgj
    intro j
    exact hback J j (by simp)
  · rw [mem_completedExtendedOrderLeftIdeal, limπ_evalShiftedDegree_eq_sum hD f n 0
      (fun j _ ↦ hf j), Finset.range_zero, Finset.sum_empty, map_zero]

private theorem evalShiftedDegree_injective
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    Function.Injective (evalShiftedDegree hD) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine Subtype.ext (PowerSeries.ext fun j ↦ ?_)
  rw [Subalgebra.coe_zero, map_zero]
  refine ModuleTower.lim_ext _ fun n ↦ ?_
  rw [map_zero, ← mem_completedOrderLeftIdeal]
  exact (evalShiftedDegree_mem_completedExtendedOrderLeftIdeal_iff hD).1
    (hf ▸ zero_mem (completedExtendedOrderLeftIdeal Φ hΦ hΦs a n)) j

private theorem summable_shiftedDegreeCoeff_term
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (w : Û') (j : ℕ) :
    Summable fun k ↦
      completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j := by
  rw [ModuleTower.summable_iff_forall_eventually_limπ_eq_zero]
  intro n
  rw [Nat.cofinite_eq_atTop]
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (((hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff.1
      (tendsto_completedDegreeCoeff_atTop Φ hΦ hΦs a w)) n trivial)
  filter_upwards [eventually_ge_atTop M] with k hk
  rw [← mem_completedOrderLeftIdeal]
  exact mul_natCast_mem_completedOrderLeftIdeal
    (mul_pow_mem_completedOrderLeftIdeal_of_commutator hD
      (hM (j + k) (by omega)) k) ((j + k).choose j)

private theorem limπ_tsum_shiftedDegreeCoeff_term
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (w : Û') (j n M : ℕ)
    (hM : ∀ m ≥ M, completedDegreeCoeff Φ hΦ hΦs a m w ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) :
    (orderQuotientTower Φ hΦ hΦs a).limπ n
        (∑' k, completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j) =
      (orderQuotientTower Φ hΦ hΦs a).limπ n
        (∑ k ∈ Finset.range (M - j),
          completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j) := by
  rw [ModuleTower.limπ_tsum_eq_sum _ (summable_shiftedDegreeCoeff_term hD w j) n
      (Finset.range (M - j)), map_sum]
  intro k hk
  have hge : M ≤ j + k := by
    have hk' : M - j ≤ k := Nat.le_of_not_lt (Finset.mem_range.not.1 hk)
    omega
  rw [← mem_completedOrderLeftIdeal]
  exact mul_natCast_mem_completedOrderLeftIdeal
    (mul_pow_mem_completedOrderLeftIdeal_of_commutator hD (hM (j + k) hge) k)
    ((j + k).choose j)

private def shiftedDegreeSeriesCoeff (D : Û) (w : Û') (j : ℕ) : Û :=
  ∑' k, completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j

private theorem tendsto_shiftedDegreeSeriesCoeff
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (w : Û') :
    Tendsto (shiftedDegreeSeriesCoeff D w) atTop (𝓝 0) := by
  rw [(hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff]
  rintro n -
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (((hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff.1
      (tendsto_completedDegreeCoeff_atTop Φ hΦ hΦs a w)) n trivial)
  filter_upwards [eventually_ge_atTop M] with j hj
  rw [SetLike.mem_coe, mem_completedOrderLeftIdeal, shiftedDegreeSeriesCoeff,
    limπ_tsum_shiftedDegreeCoeff_term hD w j n M hM, Nat.sub_eq_zero_of_le hj,
    Finset.range_zero, Finset.sum_empty, map_zero]

private def invEvalShiftedDegreeFun
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (w : Û') :
    PowerSeries.coeffTendstoZeroSubalgebra R Û :=
  ⟨PowerSeries.mk (shiftedDegreeSeriesCoeff D w),
    PowerSeries.mem_coeffTendstoZeroSubalgebra_iff.2
      (by simpa only [PowerSeries.coeff_mk] using tendsto_shiftedDegreeSeriesCoeff hD w)⟩

private theorem coeff_invEvalShiftedDegreeFun
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (w : Û') (j : ℕ) :
    PowerSeries.coeff j (invEvalShiftedDegreeFun hD w : Û⟦X⟧) = shiftedDegreeSeriesCoeff D w j := by
  rw [invEvalShiftedDegreeFun]
  exact PowerSeries.coeff_mk j (shiftedDegreeSeriesCoeff D w)

private theorem limπ_sum_completedDegreeCoeff_eq (w : Û') (n M : ℕ)
    (hM : ∀ m ≥ M, completedDegreeCoeff Φ hΦ hΦs a m w ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) :
    (extendedOrderQuotientTower Φ hΦ hΦs a).limπ n
        (∑ m ∈ Finset.range M, i (completedDegreeCoeff Φ hΦ hΦs a m w) * d̂ ^ m) =
      (extendedOrderQuotientTower Φ hΦ hΦs a).limπ n w := by
  conv_rhs => rw [← tsum_completedDegreeCoeff_mul_completedDegreeElement_pow Φ hΦ hΦs a w]
  rw [ModuleTower.limπ_tsum_eq_sum _
    (summable_completedToExtended_mul_completedDegreeElement_pow Φ hΦ hΦs a
      (tendsto_completedDegreeCoeff_atTop Φ hΦ hΦs a w)) n (Finset.range M), map_sum]
  intro m hm
  rw [← mem_completedExtendedOrderLeftIdeal]
  exact mul_completedDegreeElement_pow_mem_completedExtendedOrderLeftIdeal
    (completedToExtended_mem_completedExtendedOrderLeftIdeal_iff.2
      (hM m (Nat.le_of_not_lt (Finset.mem_range.not.1 hm)))) m

private theorem evalShiftedDegree_invEvalShiftedDegreeFun
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (w : Û') :
    evalShiftedDegree hD (invEvalShiftedDegreeFun hD w) = w := by
  refine ModuleTower.lim_ext _ fun n ↦ ?_
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (((hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).tendsto_right_iff.1
      (tendsto_completedDegreeCoeff_atTop Φ hΦ hΦs a w)) n trivial)
  have hfM : ∀ j ≥ M, PowerSeries.coeff j (invEvalShiftedDegreeFun hD w : Û⟦X⟧) ∈
      completedOrderLeftIdeal Φ hΦ hΦs a n := by
    intro j hj
    rw [coeff_invEvalShiftedDegreeFun, shiftedDegreeSeriesCoeff, mem_completedOrderLeftIdeal,
      limπ_tsum_shiftedDegreeCoeff_term hD w j n M hM, Nat.sub_eq_zero_of_le hj,
      Finset.range_zero, Finset.sum_empty, map_zero]
  rw [limπ_evalShiftedDegree_eq_sum hD (invEvalShiftedDegreeFun hD w) n M hfM]
  have htrunc :
      (extendedOrderQuotientTower Φ hΦ hΦs a).limπ n
          (∑ j ∈ Finset.range M,
            i (PowerSeries.coeff j (invEvalShiftedDegreeFun hD w : Û⟦X⟧)) *
              shiftedDegreeElement Φ hΦ hΦs a D ^ j) =
        (extendedOrderQuotientTower Φ hΦ hΦs a).limπ n
          (∑ j ∈ Finset.range M, ∑ k ∈ Finset.range (M - j),
            i (completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j) *
              shiftedDegreeElement Φ hΦ hΦs a D ^ j) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← sub_eq_zero, ← map_sub, ← mem_completedExtendedOrderLeftIdeal]
    have hdiff :
        shiftedDegreeSeriesCoeff D w j -
            ∑ k ∈ Finset.range (M - j),
              completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j ∈
          completedOrderLeftIdeal Φ hΦ hΦs a n := by
      rw [mem_completedOrderLeftIdeal, map_sub, sub_eq_zero, shiftedDegreeSeriesCoeff]
      exact limπ_tsum_shiftedDegreeCoeff_term hD w j n M hM
    have hmul :
        i (PowerSeries.coeff j (invEvalShiftedDegreeFun hD w : Û⟦X⟧)) *
              shiftedDegreeElement Φ hΦ hΦs a D ^ j -
            ∑ k ∈ Finset.range (M - j),
              i (completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j) *
                shiftedDegreeElement Φ hΦ hΦs a D ^ j =
          i (shiftedDegreeSeriesCoeff D w j -
              ∑ k ∈ Finset.range (M - j),
                completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j) *
            shiftedDegreeElement Φ hΦ hΦs a D ^ j := by
      rw [coeff_invEvalShiftedDegreeFun, map_sub, sub_mul, map_sum, Finset.sum_mul]
    rw [hmul]
    exact completedToExtended_mul_shiftedDegreeElement_pow_mem hD hdiff j
  rw [htrunc, ← Finset.sum_range_diag_flip M
    (fun j k ↦ i (completedDegreeCoeff Φ hΦ hΦs a (j + k) w * D ^ k * (j + k).choose j) *
      shiftedDegreeElement Φ hΦ hΦs a D ^ j)]
  have hdiag :
      (∑ m ∈ Finset.range M, ∑ j ∈ Finset.range (m + 1),
          i (completedDegreeCoeff Φ hΦ hΦs a (j + (m - j)) w * D ^ (m - j) *
              (j + (m - j)).choose j) *
            shiftedDegreeElement Φ hΦ hΦs a D ^ j) =
        ∑ m ∈ Finset.range M, i (completedDegreeCoeff Φ hΦ hΦs a m w) * d̂ ^ m := by
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [completedToExtended_mul_completedDegreeElement_pow_eq_sum_shiftedDegreeElement hD]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.1 hj))]
  rw [hdiag]
  exact limπ_sum_completedDegreeCoeff_eq w n M hM

private theorem evalShiftedDegree_surjective
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    Function.Surjective (evalShiftedDegree hD) :=
  fun w ↦ ⟨invEvalShiftedDegreeFun hD w, evalShiftedDegree_invEvalShiftedDegreeFun hD w⟩

/-- **Restricted formal power series decomposition of `Û'`.** When `D ∈ Û` implements the
completed degree derivation `[D, x] = δ₁(x)` for all `x ∈ Û`, evaluating restricted formal power
series over `Û` at the central shifted degree element `D' = d̂ - i(D)` gives an `R`-algebra
isomorphism `PowerSeries.coeffTendstoZeroSubalgebra R Û ≃ₐ[R] Û'`. -/
def extendedCompletedRestrictedEquiv
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    PowerSeries.coeffTendstoZeroSubalgebra R Û ≃ₐ[R] Û' :=
  AlgEquiv.ofBijective (evalShiftedDegree hD)
    ⟨evalShiftedDegree_injective hD, evalShiftedDegree_surjective hD⟩

/-- `extendedCompletedRestrictedEquiv` evaluates a restricted formal power series `f` as
`∑' n, i (coeff n f) * (D')^n`. -/
theorem extendedCompletedRestrictedEquiv_apply
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x)
    (f : PowerSeries.coeffTendstoZeroSubalgebra R Û) :
    extendedCompletedRestrictedEquiv hD f =
      ∑' n, i (PowerSeries.coeff n (f : Û⟦X⟧)) * shiftedDegreeElement Φ hΦ hΦs a D ^ n :=
  PowerSeries.coeffTendstoZeroEval_apply _ _ f

/-- `extendedCompletedRestrictedEquiv` sends a constant series `C x` to `i x`. -/
@[simp]
theorem extendedCompletedRestrictedEquiv_C
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (x : Û) :
    extendedCompletedRestrictedEquiv hD (PowerSeries.coeffTendstoZeroCAlgHom R Û x) = i x :=
  PowerSeries.coeffTendstoZeroEval_C _ _ x

/-- `extendedCompletedRestrictedEquiv` sends the indeterminate `X` to `D' = d̂ - i(D)`. -/
@[simp]
theorem extendedCompletedRestrictedEquiv_X
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    extendedCompletedRestrictedEquiv hD (PowerSeries.coeffTendstoZeroX R Û) =
      shiftedDegreeElement Φ hΦ hΦs a D :=
  PowerSeries.coeffTendstoZeroEval_X _ _

/-- The inverse of `extendedCompletedRestrictedEquiv` sends `i x` to `C x`. -/
@[simp]
theorem extendedCompletedRestrictedEquiv_symm_completedToExtended
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) (x : Û) :
    (extendedCompletedRestrictedEquiv hD).symm (i x) =
      PowerSeries.coeffTendstoZeroCAlgHom R Û x :=
  (extendedCompletedRestrictedEquiv hD).symm_apply_eq.2
    (extendedCompletedRestrictedEquiv_C hD x).symm

/-- The inverse of `extendedCompletedRestrictedEquiv` sends `D' = d̂ - i(D)` to `X`. -/
@[simp]
theorem extendedCompletedRestrictedEquiv_symm_shiftedDegreeElement
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    (extendedCompletedRestrictedEquiv hD).symm (shiftedDegreeElement Φ hΦ hΦs a D) =
      PowerSeries.coeffTendstoZeroX R Û :=
  (extendedCompletedRestrictedEquiv hD).symm_apply_eq.2
    (extendedCompletedRestrictedEquiv_X hD).symm

/-- Under `extendedCompletedRestrictedEquiv`, membership in the `n`-th stage kernel of `Û'` is
equivalent to every formal power series coefficient lying in the `n`-th stage kernel of `Û`. -/
theorem extendedCompletedRestrictedEquiv_mem_completedExtendedOrderLeftIdeal_iff
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) {n : ℕ}
    {f : PowerSeries.coeffTendstoZeroSubalgebra R Û} :
    extendedCompletedRestrictedEquiv hD f ∈ completedExtendedOrderLeftIdeal Φ hΦ hΦs a n ↔
      ∀ j, PowerSeries.coeff j (f : Û⟦X⟧) ∈ completedOrderLeftIdeal Φ hΦ hΦs a n :=
  evalShiftedDegree_mem_completedExtendedOrderLeftIdeal_iff hD

/-- **The image of `Û` and the scalar polynomials in `D'` intersect only in `R`.** -/
@[simp]
theorem range_completedToExtended_inf_adjoin_shiftedDegreeElement
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x) :
    (completedToExtended Φ hΦ hΦs a).range ⊓
        Algebra.adjoin R {shiftedDegreeElement Φ hΦ hΦs a D} = ⊥ := by
  let e := extendedCompletedRestrictedEquiv hD
  rw [eq_bot_iff]
  rintro w ⟨hx, hw⟩
  rcases (AlgHom.mem_range _).1 hx with ⟨x, rfl⟩
  have hmem : e.symm (i x) ∈
      (PowerSeries.coeffTendstoZeroCAlgHom R Û).range ⊓
        Algebra.adjoin R
          ({PowerSeries.coeffTendstoZeroX R Û} :
            Set (PowerSeries.coeffTendstoZeroSubalgebra R Û)) := by
    refine ⟨(AlgHom.mem_range _).2
        ⟨x, (extendedCompletedRestrictedEquiv_symm_completedToExtended hD x).symm⟩, ?_⟩
    have hmap : e.symm (i x) ∈
        (Algebra.adjoin R {shiftedDegreeElement Φ hΦ hΦs a D}).map e.symm.toAlgHom :=
      ⟨i x, hw, rfl⟩
    refine SetLike.mem_coe.2 ?_
    simpa only [AlgHom.map_adjoin, Set.image_singleton, AlgEquiv.coe_toAlgHom, e,
      extendedCompletedRestrictedEquiv_symm_shiftedDegreeElement] using hmap
  rw [PowerSeries.range_coeffTendstoZeroCAlgHom_inf_adjoin_X, Algebra.mem_bot] at hmem
  obtain ⟨r, hr⟩ := hmem
  rw [Algebra.mem_bot]
  refine ⟨r, ?_⟩
  have happly := congrArg e hr
  simpa only [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using happly

/-- **Center reduction from `Û'` to `Û`.** Suppose `D ∈ Û` implements the completed degree
derivation `[D, x] = δ₁(x)` for all `x ∈ Û` and `D' = d̂ - i(D)` is the shifted degree element. If
`Subalgebra.center R Û' ≤ Algebra.adjoin R {D'}`, then `Subalgebra.center R Û = ⊥`. -/
theorem center_completedEnveloping_eq_bot_of_center_extended_le_adjoin
    (hD : ∀ x : Û, D * x - x * D = (δ₁ : Module.End R Û) x)
    (hZ : Subalgebra.center R Û' ≤ Algebra.adjoin R {shiftedDegreeElement Φ hΦ hΦs a D}) :
    Subalgebra.center R Û = ⊥ := by
  let e := extendedCompletedRestrictedEquiv hD
  refine PowerSeries.center_eq_bot_of_center_coeffTendstoZeroSubalgebra_le_adjoin ?_
  intro f hf
  have hef : e f ∈ Subalgebra.center R Û' :=
    Subalgebra.mem_center_iff.2 fun y ↦ by
      obtain ⟨g, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 hf g]
  have hmap : e.symm (e f) ∈
      (Algebra.adjoin R {shiftedDegreeElement Φ hΦ hΦs a D}).map e.symm.toAlgHom :=
    ⟨e f, hZ hef, rfl⟩
  simpa only [AlgEquiv.symm_apply_apply, AlgHom.map_adjoin, Set.image_singleton,
    AlgEquiv.coe_toAlgHom, e, extendedCompletedRestrictedEquiv_symm_shiftedDegreeElement]
    using hmap

end ShiftedDegree

end TauCeti.CurrentAlgebra
