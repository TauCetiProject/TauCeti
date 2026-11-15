/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Chart
public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.RowWeight
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The hive-to-Gelfand–Tsetlin difference map, reconstruction, and stable equivalences

Along each vertical column `j` of the product chart `(i, j) ↦ (n - j, j - i, i)` on `Hive.Vertex n`,
the forward differences `P(i, j) = h(i + 1, j) - h(i, j)` (`0 ≤ i < j ≤ n`) of an integer hive `h`
assemble into a signed Gelfand–Tsetlin pattern `h.toGTPattern : GTPattern n`. The first two
product-chart rhombus families become the two interlacing inequalities of `GTPattern n`, the top row
`P.topRow` is `h.boundary 1`, and the torus weight `P.rowWeight` equals
`(h.boundaryWeight 2).dual - h.boundary 0` (`γ - λ` on `productBoundary λ μ γ`).

Summing along columns recovers every vertex value via the chart completion
`gtCompletion l P i j = prefixSum j l + ∑_{k < i} P(k, j)`. A pattern `P` with top row `μ` and row
weight `γ - λ` comes from a hive in `FixedIntegerHive (productBoundary λ μ γ)` if and only if its
chart completion satisfies the third product-chart rhombus family (`IsHiveAdmissible`,
`gt_reconstruction_iff`), yielding an explicit equivalence of types `fixedHiveEquivGTPattern`. Two
clockwise rotations transport this equivalence to the symmetric cyclic boundary `(λ, μ, ν)` with top
row `λ` and row weight `μ* - ν` (`cyclicToGTPattern`, `fixedHiveCyclicEquivGTPattern`).

Whenever every adjacent gap of the input weight `λ` (or, at fixed row weight `γ - λ`, every adjacent
gap of the output weight `γ`, corresponding to `π = μ*` in the cyclic orientation) dominates the
spread `μ₁ - μₙ`, the remaining rhombus family holds automatically
(`gt_completion_of_uniform_input_gap`, `gt_completion_of_uniform_output_gap`), so the difference map
is an equivalence onto the entire weight-`(γ - λ)` Gelfand–Tsetlin fibre (`stableGTEquiv`,
`exists_stable_gt_equiv`, `stableOutputGapGTEquiv`, `cyclicStableOutputGapEquiv`). Concrete rank-`2`
and rank-`3` examples verify that without the gap hypothesis the admissibility condition is
genuinely restrictive, even on signed patterns of weight zero in the `GL 3` adjoint representation.

## Main definitions

* `TauCeti.Hive.toGTPattern`, `TauCeti.Hive.toGTPatternAddMonoidHom`: the directional difference map
  from normalized integer hives to `TauCeti.GTPattern n`.
* `TauCeti.Hive.gtCompletion`: the inverse chart completion `prefixSum j l + ∑_{k < i} P k j`.
* `TauCeti.Hive.IsHiveAdmissible`, `TauCeti.Hive.hiveOfGTPattern`,
  `TauCeti.Hive.fixedHiveEquivGTPattern`: the remaining rhombus-family predicate, hive
  reconstruction, and fixed-boundary equivalence.
* `TauCeti.Hive.cyclicToGTPattern`, `TauCeti.Hive.fixedHiveCyclicEquivGTPattern`: the cyclic
  `(λ, μ, ν)` difference map and equivalence with top row `λ` and weight `μ* - ν`.
* `TauCeti.Hive.stableGTEquiv`, `TauCeti.Hive.stableOutputGapGTEquiv`,
  `TauCeti.Hive.cyclicStableOutputGapEquiv`, `TauCeti.Hive.fixedHiveEquivGTPatternOfLeOne`:
  full-fibre equivalences under uniform input/output gaps and in ranks `n ≤ 1`.

## Main results

* `TauCeti.Hive.gt_reconstruction_iff`: exact characterization of patterns arising from
  `FixedIntegerHive (productBoundary λ μ γ)`.
* `TauCeti.Hive.gt_completion_of_uniform_input_gap`, `TauCeti.Hive.exists_stable_gt_equiv`:
  automatic admissibility and full weight-fibre equivalence under `λ_r - λ_{r+1} ≥ μ₁ - μₙ`.
* `TauCeti.Hive.gt_completion_of_uniform_output_gap`: automatic admissibility under uniform output
  gaps `γ_r - γ_{r+1} ≥ μ₁ - μₙ`.
* `TauCeti.Hive.isHiveAdmissible_two_iff_of_topRow_of_rowWeight`,
  `TauCeti.Hive.hiveCount_two_clebschGordan_twoZero`,
  `TauCeti.Hive.hiveCount_three_zero_adjoint_zero`: low-rank characterizations and sharpness checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Henriques and J. Kamnitzer, *Crystals and coboundary categories*, Duke Math. J. **132**
  (2006), 191–216, Theorem 7.4.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Forward difference map `Hive.toGTPattern` and inverse chart completion `gtCompletion` -/

section DifferenceAndCompletion

/-- The directional finite-difference Gelfand–Tsetlin pattern of an integer hive in the product
chart: `P(i, j) = h(i + 1, j) - h(i, j)` for `0 ≤ i < j ≤ n`, and `0` outside the triangle. -/
def toGTPattern {n : ℕ} (h : IntegerHive n) : GTPattern n where
  entry i j :=
    if hlt : i < j ∧ j ≤ n then
      h (Vertex.ofChart n (i + 1) j (by omega) hlt.2) -
        h (Vertex.ofChart n i j (by omega) hlt.2)
    else 0
  zeros' {i j} hzero := by
    have hnot : ¬ (i < j ∧ j ≤ n) := by omega
    rw [dite_eq_right hnot]
  interlacing' {i j} hij hjn := by
    have h0 : i < j ∧ j ≤ n := by omega
    have h1 : i < j + 1 ∧ j + 1 ≤ n := by omega
    have h2 : i + 1 < j + 1 ∧ j + 1 ≤ n := by omega
    rw [dite_eq_left h0, dite_eq_left h1, dite_eq_left h2]
    have hi2 : Vertex.ofChart n (i + 1 + 1) (j + 1) (by omega) h2.2 =
        Vertex.ofChart n (i + 2) (j + 1) (by omega) (by omega) :=
      Vertex.ext rfl (by simp) (by simp)
    rw [hi2]
    have hr1 := h.le_of_isRhombus (isRhombus_ofChart_one hij hjn)
    have hr2 := h.le_of_isRhombus (isRhombus_ofChart_two hij hjn)
    exact ⟨by omega, by omega⟩

theorem toGTPattern_apply {n : ℕ} (h : IntegerHive n) (i j : ℕ) :
    h.toGTPattern i j =
      if hlt : i < j ∧ j ≤ n then
        h (Vertex.ofChart n (i + 1) j (by omega) hlt.2) -
          h (Vertex.ofChart n i j (by omega) hlt.2)
      else 0 := (rfl)

@[simp] theorem toGTPattern_apply_of_lt_of_le {n : ℕ} (h : IntegerHive n) {i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) :
    h.toGTPattern i j =
      h (Vertex.ofChart n (i + 1) j (by omega) hjn) -
        h (Vertex.ofChart n i j (by omega) hjn) := by
  rw [toGTPattern_apply, dite_eq_left ⟨hij, hjn⟩]

/-- The top row of `h.toGTPattern` is the second clockwise side `h.boundary 1` (`B → C`). -/
@[simp] theorem topRow_toGTPattern {n : ℕ} (h : IntegerHive n) :
    h.toGTPattern.topRow = h.boundary 1 := by
  ext r
  rw [GTPattern.topRow_apply, toGTPattern_apply_of_lt_of_le h r.isLt le_rfl,
    Vertex.ofChart_last_right n (r.val + 1) r.isLt,
    Vertex.ofChart_last_right n r.val (Nat.le_of_lt r.isLt), boundary_apply]
  rfl

/-- Packaged as a dominant weight, the top weight of `h.toGTPattern` is `h.boundaryWeight 1`. -/
@[simp] theorem topWeight_toGTPattern {n : ℕ} (h : IntegerHive n) :
    h.toGTPattern.topWeight = h.boundaryWeight 1 :=
  Subtype.ext (by simp [GTPattern.topWeight_coe])

@[simp] theorem toGTPattern_zero {n : ℕ} : (0 : IntegerHive n).toGTPattern = 0 := by
  ext i j; simp [toGTPattern_apply]

@[simp] theorem toGTPattern_add {n : ℕ} (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toGTPattern = h₁.toGTPattern + h₂.toGTPattern := by
  ext i j
  rw [GTPattern.add_apply, toGTPattern_apply, toGTPattern_apply, toGTPattern_apply]
  split_ifs
  · simp only [add_apply]; omega
  · omega

@[simp] theorem toGTPattern_nsmul {n : ℕ} (k : ℕ) (h : IntegerHive n) :
    (k • h).toGTPattern = k • h.toGTPattern := by
  ext i j
  rw [GTPattern.nsmul_apply, toGTPattern_apply, toGTPattern_apply]
  split_ifs
  · simp only [nsmul_apply, nsmul_eq_mul]; ring
  · simp

/-- `Hive.toGTPattern` packaged as an additive monoid homomorphism `IntegerHive n →+ GTPattern n`.
-/
def toGTPatternAddMonoidHom (n : ℕ) : IntegerHive n →+ GTPattern n where
  toFun := toGTPattern
  map_zero' := toGTPattern_zero
  map_add' := toGTPattern_add

@[simp] theorem toGTPatternAddMonoidHom_apply {n : ℕ} (h : IntegerHive n) :
    toGTPatternAddMonoidHom n h = h.toGTPattern := (rfl)

/-- Along column `j`, the first `i` entries of `h.toGTPattern` telescope to `h(i, j) - h(0, j)`. -/
theorem sum_range_toGTPattern {n : ℕ} (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
      h (Vertex.ofChart n i j hij hjn) - h (Vertex.ofChart n 0 j (Nat.zero_le j) hjn) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), toGTPattern_apply_of_lt_of_le h (by omega) hjn]
    abel

/-- The `j`-th row sum of `h.toGTPattern` equals `h(j, j) - h(0, j)`. -/
theorem rowSum_toGTPattern {n : ℕ} (h : IntegerHive n) {j : ℕ} (hjn : j ≤ n) :
    h.toGTPattern.rowSum j =
      h (Vertex.ofChart n j j le_rfl hjn) - h (Vertex.ofChart n 0 j (Nat.zero_le j) hjn) := by
  rw [GTPattern.rowSum_def]
  exact sum_range_toGTPattern h le_rfl hjn

/-- For any integer hive `h`, `h.toGTPattern.rowWeight` equals
`(h.boundaryWeight 2).dual - h.boundary 0`. -/
theorem rowWeight_toGTPattern {n : ℕ} (h : IntegerHive n) :
    h.toGTPattern.rowWeight = (h.boundaryWeight 2).dual.1 - h.boundary 0 := by
  ext r
  rw [Pi.sub_apply, GTPattern.rowWeight_apply, rowSum_toGTPattern h r.isLt,
    rowSum_toGTPattern h (Nat.le_of_lt r.isLt),
    apply_ofChart_diag_of_boundaryWeight h r.isLt,
    apply_ofChart_diag_of_boundaryWeight h (Nat.le_of_lt r.isLt),
    apply_ofChart_zero h r.isLt, apply_ofChart_zero h (Nat.le_of_lt r.isLt),
    prefixSum_succ r.isLt, prefixSum_succ r.isLt]
  simp only [Fin.eta]
  omega

/-- On `productBoundary lam μ γ`, `h.toGTPattern.rowWeight` equals `γ - λ`. -/
theorem rowWeight_toGTPattern_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    h.toGTPattern.rowWeight = γ.1 - lam.1 := by
  have hw2 : h.boundaryWeight 2 = γ.dual := Subtype.ext (by simp [coe_boundaryWeight, hb])
  have hb0 : h.boundary 0 = lam.1 := by simp [hb]
  rw [rowWeight_toGTPattern, hw2, DominantWeight.dual_dual, hb0]

/-- The inverse chart completion `h(i, j) = prefixSum j l + ∑_{k < i} P(k, j)` recovering a hive in
product-chart coordinates from its side-`0` boundary `l` and pattern `P`. -/
def gtCompletion {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) : ℤ :=
  prefixSum j l + ∑ k ∈ Finset.range i, P k j

theorem gtCompletion_def {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P i j = prefixSum j l + ∑ k ∈ Finset.range i, P k j := (rfl)

@[simp] theorem gtCompletion_zero_left {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P 0 j = prefixSum j l := by
  simp [gtCompletion_def]

theorem gtCompletion_succ_left {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P (i + 1) j = gtCompletion l P i j + P i j := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_range_succ, add_assoc]

/-- Along the diagonal `i = j` (`j ≤ n`), `gtCompletion l P j j` is `prefixSum j (l + P.rowWeight)`.
-/
theorem gtCompletion_diag {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) {j : ℕ} (hjn : j ≤ n) :
    gtCompletion l P j j = prefixSum j (l + P.rowWeight) := by
  rw [gtCompletion_def, ← GTPattern.rowSum_def, ← P.prefixSum_rowWeight hjn, prefixSum_add]

/-- Along `j = n` (`i ≤ n`), `gtCompletion l P i n` is `|l| + prefixSum i P.topRow`. -/
theorem gtCompletion_last_right {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) {i : ℕ} (hin : i ≤ n) :
    gtCompletion l P i n = (∑ r : Fin n, l r) + prefixSum i P.topRow := by
  rw [gtCompletion_def, prefixSum_of_le le_rfl l]
  congr 1
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, prefixSum_succ (by omega) P.topRow, ih (by omega),
      GTPattern.topRow_apply]

/-- **Inverse formula in chart coordinates**: `gtCompletion (h.boundary 0) h.toGTPattern i j`
recovers `h(i, j)` for every `0 ≤ i ≤ j ≤ n`. -/
@[simp] theorem gtCompletion_toGTPattern_ofChart {n : ℕ} (h : IntegerHive n) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletion (h.boundary 0) h.toGTPattern i j = h (Vertex.ofChart n i j hij hjn) := by
  rw [gtCompletion_def, sum_range_toGTPattern h hij hjn, apply_ofChart_zero h hjn]
  omega

/-- **Inverse formula on vertices**: every vertex value `h v` of an integer hive is recovered from
`h.boundary 0` and `h.toGTPattern` at `(v.z, n - v.x)`. -/
@[simp] theorem gtCompletion_toGTPattern {n : ℕ} (h : IntegerHive n) (v : Vertex n) :
    gtCompletion (h.boundary 0) h.toGTPattern v.z (n - v.x) = h v := by
  have hv := gtCompletion_toGTPattern_ofChart h (i := v.z) (j := n - v.x)
    (by have := v.sum_eq; omega) (Nat.sub_le n v.x)
  rwa [Vertex.ofChart_z_sub_x] at hv

/-- Two integer hives with the same side-`0` boundary and the same Gelfand–Tsetlin pattern are
equal. -/
theorem toGTPattern_injective_of_boundary_zero_eq {n : ℕ} {h₁ h₂ : IntegerHive n}
    (hb : h₁.boundary 0 = h₂.boundary 0) (hP : h₁.toGTPattern = h₂.toGTPattern) : h₁ = h₂ := by
  ext v
  rw [← gtCompletion_toGTPattern h₁ v, ← gtCompletion_toGTPattern h₂ v, hb, hP]

end DifferenceAndCompletion

/-! ### Remaining rhombus family and Gelfand–Tsetlin reconstruction -/

section Reconstruction

/-- A pattern `P : GTPattern n` is **hive-admissible** over side-`0` boundary `l : Fin n → ℤ` when
its chart completion satisfies the third unit-rhombus family in difference form:
`∑_{k ≤ i} (P(k, j + 2) - P(k, j + 1)) ≤ l_j - l_{j + 1} + ∑_{k < i} (P(k, j + 1) - P(k, j))`
for all `0 ≤ i ≤ j` with `j + 2 ≤ n`. -/
def IsHiveAdmissible {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) : Prop :=
  ∀ ⦃i j : ℕ⦄, i ≤ j → (hjn : j + 2 ≤ n) →
    ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)) ≤
      l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ +
        ∑ k ∈ Finset.range i, (P k (j + 1) - P k j)

theorem isHiveAdmissible_def {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) :
    IsHiveAdmissible l P ↔
      ∀ ⦃i j : ℕ⦄, i ≤ j → (hjn : j + 2 ≤ n) →
        ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)) ≤
          l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ +
            ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := Iff.rfl

/-- Bounded `Fin (n + 1)` characterization of `IsHiveAdmissible`, providing decidability. -/
theorem isHiveAdmissible_iff_forall_fin {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) :
    IsHiveAdmissible l P ↔
      ∀ i j : Fin (n + 1), i.val ≤ j.val → (hjn : j.val + 2 ≤ n) →
        ∑ k ∈ Finset.range (i.val + 1), (P k (j.val + 2) - P k (j.val + 1)) ≤
          l ⟨j.val, by omega⟩ - l ⟨j.val + 1, by omega⟩ +
            ∑ k ∈ Finset.range i.val, (P k (j.val + 1) - P k j.val) := by
  rw [isHiveAdmissible_def]
  exact ⟨fun h i j hij hjn => h hij hjn,
    fun h i j hij hjn => h ⟨i, by omega⟩ ⟨j, by omega⟩ hij hjn⟩

instance {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) : Decidable (IsHiveAdmissible l P) :=
  decidable_of_iff _ (isHiveAdmissible_iff_forall_fin l P).symm

/-- `IsHiveAdmissible l P` is equivalent to the third product-chart rhombus inequality on
`gtCompletion l P`. -/
theorem isHiveAdmissible_iff_gtCompletion_le {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) :
    IsHiveAdmissible l P ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
          gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) := by
  rw [isHiveAdmissible_def]
  refine ⟨fun h i j hij hjn => ?_, fun h i j hij hjn => ?_⟩
  · have hineq := h hij hjn
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hineq
    rw [gtCompletion_def, gtCompletion_def, gtCompletion_def, gtCompletion_def,
      prefixSum_succ (by omega : j + 1 < n) l, prefixSum_succ (by omega : j < n) l]
    omega
  · have hineq := h i j hij hjn
    rw [gtCompletion_def, gtCompletion_def, gtCompletion_def, gtCompletion_def,
      prefixSum_succ (by omega : j + 1 < n) l,
      prefixSum_succ (by omega : j < n) l] at hineq
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    omega

/-- The difference pattern of every integer hive is admissible over its side-`0` boundary. -/
theorem IsHiveAdmissible.of_toGTPattern {n : ℕ} (h : IntegerHive n) :
    IsHiveAdmissible (h.boundary 0) h.toGTPattern := by
  rw [isHiveAdmissible_iff_gtCompletion_le]
  intro i j hij hjn
  rw [gtCompletion_toGTPattern_ofChart h hij (by omega),
    gtCompletion_toGTPattern_ofChart h (by omega) hjn,
    gtCompletion_toGTPattern_ofChart h (by omega) (by omega),
    gtCompletion_toGTPattern_ofChart h (by omega) (by omega)]
  exact h.le_of_isRhombus (isRhombus_ofChart_three hij hjn)

/-- Evaluating `IsHiveAdmissible l P` at `i = 0` forces `l` to be antitone. -/
theorem IsHiveAdmissible.antitone_left {n : ℕ} {l : Fin n → ℤ} {P : GTPattern n}
    (hadm : IsHiveAdmissible l P) : Antitone l := by
  cases n with
  | zero => exact Subsingleton.antitone _
  | succ m =>
    refine Fin.antitone_iff_succ_le.mpr fun r => ?_
    have h0 := hadm (Nat.zero_le r.val) (by omega : r.val + 2 ≤ m + 1)
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Finset.range_zero,
      Finset.sum_empty, add_zero] at h0
    have hrow : P 0 (r.val + 1) ≤ P 0 (r.val + 2) :=
      P.entry_le_entry_succ_row (by omega : 0 < r.val + 1) (by omega : r.val + 1 < m + 1)
    have hrc : (⟨r.val, by omega⟩ : Fin (m + 1)) = r.castSucc := rfl
    have hrs : (⟨r.val + 1, by omega⟩ : Fin (m + 1)) = r.succ := rfl
    rw [hrc, hrs] at h0
    omega

/-- Evaluating `IsHiveAdmissible l P` along `i = j` forces `l + P.rowWeight` to be antitone. -/
theorem IsHiveAdmissible.antitone_add_rowWeight {n : ℕ} {l : Fin n → ℤ} {P : GTPattern n}
    (hadm : IsHiveAdmissible l P) : Antitone (l + P.rowWeight) := by
  cases n with
  | zero => exact Subsingleton.antitone _
  | succ m =>
    refine Fin.antitone_iff_succ_le.mpr fun r => ?_
    have hj := hadm le_rfl (by omega : r.val + 2 ≤ m + 1)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hj
    have hdiag : P (r.val + 1) (r.val + 2) ≤ P r.val (r.val + 1) :=
      P.entry_succ_succ_le_entry (i := r.val) (j := r.val + 1) (by omega)
    simp only [Pi.add_apply, GTPattern.rowWeight_eq_sum_sub_sum, Fin.val_succ, Fin.val_castSucc]
    rw [Finset.sum_range_succ _ (r.val + 1),
      Finset.sum_range_succ (fun k => P k (r.val + 1)) r.val]
    rw [Finset.sum_range_succ (fun k => P k (r.val + 1)) r.val] at hj
    have hr2 : r.val + 1 + 1 = r.val + 2 := rfl
    rw [hr2]
    have hrc : (⟨r.val, by omega⟩ : Fin (m + 1)) = r.castSucc := rfl
    have hrs : (⟨r.val + 1, by omega⟩ : Fin (m + 1)) = r.succ := rfl
    rw [hrc, hrs] at hj
    omega

/-- Reconstruct a normalized integer hive from a side-`0` boundary `l` and an admissible pattern `P`
via `gtCompletion l P`. -/
def hiveOfGTPattern {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n) (hadm : IsHiveAdmissible l P) :
    IntegerHive n where
  value v := gtCompletion l P v.z (n - v.x)
  value_cornerA' := by simp
  le_of_isRhombus' := by
    intro a b c d hr
    have hconc : IsRhombusConcave (fun v : Vertex n => gtCompletion l P v.z (n - v.x)) := by
      rw [isRhombusConcave_iff_ofChart]
      refine ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩
      · simp only [Vertex.ofChart_z, Vertex.ofChart_x,
          Nat.sub_sub_self (by omega : j ≤ n), Nat.sub_sub_self (by omega : j + 1 ≤ n)]
        rw [gtCompletion_succ_left, gtCompletion_succ_left]
        have hle := P.entry_le_entry_succ_row hij hjn
        omega
      · simp only [Vertex.ofChart_z, Vertex.ofChart_x,
          Nat.sub_sub_self (by omega : j ≤ n), Nat.sub_sub_self (by omega : j + 1 ≤ n)]
        rw [gtCompletion_succ_left l P (i + 1) (j + 1), gtCompletion_succ_left l P i j]
        have hle := P.entry_succ_succ_le_entry (i := i) (j := j) hjn
        omega
      · simp only [Vertex.ofChart_z, Vertex.ofChart_x,
          Nat.sub_sub_self (by omega : j ≤ n), Nat.sub_sub_self (by omega : j + 1 ≤ n),
          Nat.sub_sub_self hjn]
        exact (isHiveAdmissible_iff_gtCompletion_le l P).mp hadm i j hij hjn
    exact (isRhombusConcave_def _).mp hconc hr

@[simp] theorem hiveOfGTPattern_apply {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n)
    (hadm : IsHiveAdmissible l P) (v : Vertex n) :
    hiveOfGTPattern l P hadm v = gtCompletion l P v.z (n - v.x) := (rfl)

theorem hiveOfGTPattern_ofChart {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n)
    (hadm : IsHiveAdmissible l P) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    hiveOfGTPattern l P hadm (Vertex.ofChart n i j hij hjn) = gtCompletion l P i j := by
  rw [hiveOfGTPattern_apply, Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self hjn]

/-- Taking differences of `hiveOfGTPattern l P hadm` recovers `P`. -/
@[simp] theorem toGTPattern_hiveOfGTPattern {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n)
    (hadm : IsHiveAdmissible l P) :
    (hiveOfGTPattern l P hadm).toGTPattern = P := by
  ext i j
  by_cases hlt : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le _ hlt.1 hlt.2, hiveOfGTPattern_ofChart,
      hiveOfGTPattern_ofChart, gtCompletion_succ_left]
    omega
  · rw [toGTPattern_apply, dite_eq_right hlt, P.entry_eq_zero (by omega)]

/-- Completing `h.toGTPattern` over `h.boundary 0` recovers `h`. -/
@[simp] theorem hiveOfGTPattern_toGTPattern {n : ℕ} (h : IntegerHive n) :
    hiveOfGTPattern (h.boundary 0) h.toGTPattern (IsHiveAdmissible.of_toGTPattern h) = h := by
  ext v; simp

@[simp] theorem boundary_hiveOfGTPattern_zero {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n)
    (hadm : IsHiveAdmissible l P) :
    (hiveOfGTPattern l P hadm).boundary 0 = l := by
  ext r
  have hsucc : Vertex.edgePoint n 0 r.succ =
      Vertex.ofChart n 0 (r.val + 1) (Nat.zero_le _) r.isLt :=
    (Vertex.ofChart_zero_left n (r.val + 1) r.isLt).symm
  have hcast : Vertex.edgePoint n 0 r.castSucc =
      Vertex.ofChart n 0 r.val (Nat.zero_le _) (Nat.le_of_lt r.isLt) :=
    (Vertex.ofChart_zero_left n r.val (Nat.le_of_lt r.isLt)).symm
  rw [boundary_apply, hsucc, hcast, hiveOfGTPattern_ofChart, hiveOfGTPattern_ofChart,
    gtCompletion_zero_left, gtCompletion_zero_left, prefixSum_succ r.isLt l]
  simp only [Fin.eta]
  omega

@[simp] theorem boundary_hiveOfGTPattern_one {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n)
    (hadm : IsHiveAdmissible l P) :
    (hiveOfGTPattern l P hadm).boundary 1 = P.topRow := by
  rw [← topRow_toGTPattern, toGTPattern_hiveOfGTPattern]

@[simp] theorem boundary_hiveOfGTPattern_two {n : ℕ} (l : Fin n → ℤ) (P : GTPattern n)
    (hadm : IsHiveAdmissible l P) :
    (hiveOfGTPattern l P hadm).boundary 2 = fun r => -(l r.rev + P.rowWeight r.rev) := by
  ext r
  have hsucc : Vertex.edgePoint n 2 r.succ =
      Vertex.ofChart n r.rev.val r.rev.val le_rfl (Nat.le_of_lt r.rev.isLt) := by
    rw [Vertex.ofChart_diag]; congr 1; ext; simp [Fin.val_rev]; omega
  have hcast : Vertex.edgePoint n 2 r.castSucc =
      Vertex.ofChart n (r.rev.val + 1) (r.rev.val + 1) le_rfl r.rev.isLt := by
    rw [Vertex.ofChart_diag]; congr 1; ext; simp [Fin.val_rev]; omega
  rw [boundary_apply, hsucc, hcast, hiveOfGTPattern_ofChart, hiveOfGTPattern_ofChart,
    gtCompletion_diag _ _ (Nat.le_of_lt r.rev.isLt), gtCompletion_diag _ _ r.rev.isLt,
    prefixSum_succ r.rev.isLt (l + P.rowWeight), Pi.add_apply]
  simp only [Fin.eta]
  omega

/-- When `P.topRow = m` and `P.rowWeight = g - l`, `hiveOfGTPattern l P hadm` has boundary
`productBoundary l m g`. -/
theorem boundary_hiveOfGTPattern_of_topRow_of_rowWeight {n : ℕ} (l m g : DominantWeight n)
    {P : GTPattern n} (hTop : P.topRow = m.1) (hWeight : P.rowWeight = g.1 - l.1)
    (hadm : IsHiveAdmissible l.1 P) :
    (hiveOfGTPattern l.1 P hadm).boundary = productBoundary l m g := by
  funext s
  fin_cases s
  · simp
  · simp [hTop]
  · ext r
    have hw := congrFun hWeight r.rev
    simp at hw ⊢
    omega

/-- **Equivalence between fixed-boundary integer hives and admissible Gelfand–Tsetlin patterns**:
`FixedIntegerHive (productBoundary l m g)` corresponds bijectively via `toGTPattern` and
`hiveOfGTPattern` to the patterns `P : GTPattern n` with `P.topRow = m`, `P.rowWeight = g - l`,
and `IsHiveAdmissible l P`. -/
def fixedHiveEquivGTPattern {n : ℕ} (l m g : DominantWeight n) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern n // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1 ∧ IsHiveAdmissible l.1 P} where
  toFun h :=
    ⟨h.1.toGTPattern,
      by rw [topRow_toGTPattern, h.2, productBoundary_one],
      rowWeight_toGTPattern_of_productBoundary h.2,
      by
        have hb0 : h.1.boundary 0 = l.1 := by rw [h.2, productBoundary_zero]
        exact hb0 ▸ IsHiveAdmissible.of_toGTPattern h.1⟩
  invFun P :=
    ⟨hiveOfGTPattern l.1 P.1 P.2.2.2,
      boundary_hiveOfGTPattern_of_topRow_of_rowWeight l m g P.2.1 P.2.2.1 P.2.2.2⟩
  left_inv h := by
    apply Subtype.ext
    dsimp only
    have hb0 : h.1.boundary 0 = l.1 := by rw [h.2, productBoundary_zero]
    ext v
    rw [hiveOfGTPattern_apply, ← hb0, gtCompletion_toGTPattern]
  right_inv P := Subtype.ext (toGTPattern_hiveOfGTPattern l.1 P.1 P.2.2.2)

@[simp] theorem fixedHiveEquivGTPattern_apply_coe {n : ℕ} (l m g : DominantWeight n)
    (h : FixedIntegerHive (productBoundary l m g)) :
    (fixedHiveEquivGTPattern l m g h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem fixedHiveEquivGTPattern_symm_apply_coe_apply {n : ℕ} (l m g : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1 ∧ IsHiveAdmissible l.1 P})
    (v : Vertex n) :
    ((fixedHiveEquivGTPattern l m g).symm P).1 v = gtCompletion l.1 P.1 v.z (n - v.x) := (rfl)

/-- **Gelfand–Tsetlin reconstruction characterization**: a pattern `P` with top row `m` and weight
`g - l` is the difference pattern (equivalently, chart completion) of a hive with boundary
`(l, m, g*)` if and only if the third product-chart rhombus family holds on `gtCompletion l P`. -/
theorem gt_reconstruction_iff {n : ℕ} (l m g : DominantWeight n)
    (P : GTPattern n) (hTop : P.topRow = m.1) (hWeight : P.rowWeight = g.1 - l.1) :
    (∃ h : FixedIntegerHive (productBoundary l m g),
      ∀ v : Vertex n, h.1 v = gtCompletion l.1 P v.z (n - v.x)) ↔
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
      gtCompletion l.1 P i j + gtCompletion l.1 P (i + 1) (j + 2) ≤
        gtCompletion l.1 P i (j + 1) + gtCompletion l.1 P (i + 1) (j + 1) := by
  rw [← isHiveAdmissible_iff_gtCompletion_le]
  refine ⟨?_, fun hadm => ⟨(fixedHiveEquivGTPattern l m g).symm ⟨P, hTop, hWeight, hadm⟩,
      fun v => rfl⟩⟩
  rintro ⟨h, hval⟩
  have hb0 : h.1.boundary 0 = l.1 := by rw [h.2, productBoundary_zero]
  have hP : P = h.1.toGTPattern := by
    ext i j
    by_cases hlt : i < j ∧ j ≤ n
    · rw [toGTPattern_apply_of_lt_of_le h.1 hlt.1 hlt.2, hval, hval]
      simp only [Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self hlt.2,
        gtCompletion_succ_left]
      omega
    · rw [P.entry_eq_zero (by omega), toGTPattern_apply, dite_eq_right hlt]
  rw [hP, ← hb0]
  exact IsHiveAdmissible.of_toGTPattern h.1

end Reconstruction

/-! ### Cyclic orientation `(λ, μ, ν)` (Henriques–Kamnitzer Theorem 7.4) -/

section CyclicOrientation

/-- The directional Gelfand–Tsetlin difference map adapted to the symmetric cyclic boundary
`(λ, μ, ν)`, obtained by two clockwise rotations before `toGTPattern`: its top row is side `0`
(`λ`) and its row weight is `(side 1)* - side 2` (`μ* - ν`). -/
def cyclicToGTPattern {n : ℕ} (h : IntegerHive n) : GTPattern n :=
  h.rotate.rotate.toGTPattern

theorem cyclicToGTPattern_def {n : ℕ} (h : IntegerHive n) :
    h.cyclicToGTPattern = h.rotate.rotate.toGTPattern := (rfl)

/-- Explicit gauge-free entry formula for `cyclicToGTPattern` directly in terms of `h`:
`h(j - (i + 1), i + 1, n - j) - h(j - i, i, n - j)` for `0 ≤ i < j ≤ n`. -/
theorem cyclicToGTPattern_apply_of_lt_of_le {n : ℕ} (h : IntegerHive n) {i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) :
    h.cyclicToGTPattern i j =
      h ⟨j - (i + 1), i + 1, n - j, by omega⟩ - h ⟨j - i, i, n - j, by omega⟩ := by
  rw [cyclicToGTPattern_def, toGTPattern_apply_of_lt_of_le _ hij hjn]
  simp only [rotate_apply]
  have hp1 : (Vertex.ofChart n (i + 1) j (by omega) hjn).rotate.rotate =
      ⟨j - (i + 1), i + 1, n - j, by omega⟩ := by ext <;> simp
  have hp0 : (Vertex.ofChart n i j (by omega) hjn).rotate.rotate =
      ⟨j - i, i, n - j, by omega⟩ := by ext <;> simp
  rw [hp1, hp0]
  abel

@[simp] theorem topRow_cyclicToGTPattern {n : ℕ} (h : IntegerHive n) :
    h.cyclicToGTPattern.topRow = h.boundary 0 := by
  rw [cyclicToGTPattern_def, topRow_toGTPattern, boundary_rotate, boundary_rotate]
  rfl

theorem rowWeight_cyclicToGTPattern {n : ℕ} (h : IntegerHive n) :
    h.cyclicToGTPattern.rowWeight = (h.boundaryWeight 1).dual.1 - h.boundary 2 := by
  rw [cyclicToGTPattern_def, rowWeight_toGTPattern, boundaryWeight_rotate,
    boundaryWeight_rotate, boundary_rotate, boundary_rotate]
  rfl

/-- Rotation equivalence identifying `FixedIntegerHive (cyclicBoundary lam μ ν)` with
`FixedIntegerHive (productBoundary ν lam μ.dual)` via `h ↦ h.rotate.rotate` and inverse
`k ↦ k.rotate`. -/
def fixedHiveRotateRotateEquiv {n : ℕ} (lam μ ν : DominantWeight n) :
    FixedIntegerHive (cyclicBoundary lam μ ν) ≃
      FixedIntegerHive (productBoundary ν lam μ.dual) where
  toFun h := ⟨h.1.rotate.rotate, boundary_rotate_rotate_of_cyclicBoundary h.2⟩
  invFun k := ⟨k.1.rotate, boundary_rotate_of_productBoundary_dual k.2⟩
  left_inv _ := Subtype.ext (by simp)
  right_inv _ := Subtype.ext (by simp)

@[simp] theorem fixedHiveRotateRotateEquiv_apply_coe {n : ℕ} (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) :
    (fixedHiveRotateRotateEquiv lam μ ν h).1 = h.1.rotate.rotate := (rfl)

@[simp] theorem fixedHiveRotateRotateEquiv_symm_apply_coe {n : ℕ} (lam μ ν : DominantWeight n)
    (k : FixedIntegerHive (productBoundary ν lam μ.dual)) :
    ((fixedHiveRotateRotateEquiv lam μ ν).symm k).1 = k.1.rotate := (rfl)

/-- **Cyclic-orientation hive-to-Gelfand–Tsetlin equivalence** (Henriques–Kamnitzer, Theorem 7.4):
integer hives with clockwise cyclic boundary `(λ, μ, ν)` correspond via `cyclicToGTPattern` to
patterns with top row `λ`, row weight `μ* - ν`, and `IsHiveAdmissible ν P`, obtained by composing
`fixedHiveRotateRotateEquiv` with `fixedHiveEquivGTPattern ν lam μ.dual`. -/
def fixedHiveCyclicEquivGTPattern {n : ℕ} (lam μ ν : DominantWeight n) :
    FixedIntegerHive (cyclicBoundary lam μ ν) ≃
      {P : GTPattern n // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1 ∧
        IsHiveAdmissible ν.1 P} :=
  (fixedHiveRotateRotateEquiv lam μ ν).trans (fixedHiveEquivGTPattern ν lam μ.dual)

@[simp] theorem fixedHiveCyclicEquivGTPattern_apply_coe {n : ℕ} (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) :
    (fixedHiveCyclicEquivGTPattern lam μ ν h).1 = h.1.cyclicToGTPattern := (rfl)

@[simp] theorem fixedHiveCyclicEquivGTPattern_symm_apply_coe {n : ℕ} (lam μ ν : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1 ∧
      IsHiveAdmissible ν.1 P}) :
    ((fixedHiveCyclicEquivGTPattern lam μ ν).symm P).1 =
      (hiveOfGTPattern ν.1 P.1 P.2.2.2).rotate := (rfl)

end CyclicOrientation

/-! ### Uniform input/output gap theorems and full weight-fibre equivalences -/

section UniformGaps

/-- Difference between any two informative entries of `P : GTPattern (n + 1)` is bounded by the
top-row spread `P.topRow 0 - P.topRow (Fin.last n)`. -/
private theorem entry_sub_entry_le_topRow_spread {n : ℕ} (P : GTPattern (n + 1))
    {i₁ j₁ i₂ j₂ : ℕ} (h₁ : i₁ < j₁) (hj₁ : j₁ ≤ n + 1) (h₂ : i₂ < j₂) (hj₂ : j₂ ≤ n + 1) :
    P i₁ j₁ - P i₂ j₂ ≤ P.topRow 0 - P.topRow (Fin.last n) := by
  have htop := (P.entry_mem_Icc h₁ hj₁).2
  have hbot := (P.entry_mem_Icc h₂ hj₂).1
  have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
  have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := rfl
  rw [hzero] at htop
  rw [hlast] at hbot
  omega

/-- **Uniform input gap implies admissibility**: if every adjacent gap `l_r - l_{r + 1}` of `l` is
at least the spread `P.topRow 0 - P.topRow (Fin.last n)`, then `IsHiveAdmissible l P` holds
automatically. -/
theorem isHiveAdmissible_of_uniform_input_gap {n : ℕ} (l : Fin (n + 1) → ℤ)
    (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ) :
    IsHiveAdmissible l P := by
  rw [isHiveAdmissible_def]
  intro i j hij hjn
  have hleft : 0 ≤ ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
    Finset.sum_nonneg fun k hk => by
      have hk_lt : k < j := (Finset.mem_range.mp hk).trans_le hij
      have hle := P.entry_le_entry_succ_row hk_lt (by omega : j < n + 1)
      omega
  have hright_tele :
      ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)) ≤
        P 0 (j + 2) - P (i + 1) (j + 2) := by
    calc ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))
        ≤ ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P (k + 1) (j + 2)) :=
          Finset.sum_le_sum fun k _ => by
            have hle : P (k + 1) (j + 2) ≤ P k (j + 1) :=
              P.entry_succ_succ_le_entry (i := k) (j := j + 1) (by omega)
            omega
      _ = P 0 (j + 2) - P (i + 1) (j + 2) :=
          Finset.sum_range_sub' (fun k => P k (j + 2)) (i + 1)
  have hspread := entry_sub_entry_le_topRow_spread P (i₁ := 0) (j₁ := j + 2) (by omega) hjn
    (i₂ := i + 1) (j₂ := j + 2) (by omega) hjn
  have hgap_j := hGap ⟨j, by omega⟩
  have hrc : (⟨j, by omega⟩ : Fin n).castSucc = ⟨j, by omega⟩ := rfl
  have hrs : (⟨j, by omega⟩ : Fin n).succ = ⟨j + 1, by omega⟩ := rfl
  rw [hrc, hrs] at hgap_j
  omega

/-- **Uniform input gap makes the remaining rhombus family automatic**: whenever every adjacent gap
`l_r - l_{r + 1}` is at least `m_0 - m_n`, every pattern `P` with top row `m` satisfies the third
rhombus family on `gtCompletion l P`. -/
theorem gt_completion_of_uniform_input_gap {n : ℕ}
    (l m : DominantWeight (n + 1)) (P : GTPattern (n + 1)) (hTop : P.topRow = m.1)
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ) :
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion l.1 P i j + gtCompletion l.1 P (i + 1) (j + 2) ≤
        gtCompletion l.1 P i (j + 1) + gtCompletion l.1 P (i + 1) (j + 1) :=
  (isHiveAdmissible_iff_gtCompletion_le l.1 P).mp
    (isHiveAdmissible_of_uniform_input_gap l.1 P fun r => by rw [hTop]; exact hGap r)

/-- **Stable hive-to-Gelfand–Tsetlin equivalence under a uniform input gap**: when
`m_0 - m_n ≤ l_r - l_{r + 1}` for every `r : Fin n`, `toGTPattern` and `hiveOfGTPattern` identify
`FixedIntegerHive (productBoundary l m g)` with the entire weight-`(g - l)` Gelfand–Tsetlin fibre
over `m`. -/
def stableGTEquiv {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} :=
  (fixedHiveEquivGTPattern l m g).trans
    { toFun := fun P => ⟨P.1, P.2.1, P.2.2.1⟩
      invFun := fun P => ⟨P.1, P.2.1, P.2.2,
        isHiveAdmissible_of_uniform_input_gap l.1 P.1 fun r => by rw [P.2.1]; exact hGap r⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem stableGTEquiv_apply_coe {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ)
    (h : FixedIntegerHive (productBoundary l m g)) :
    (stableGTEquiv l m g hGap h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem stableGTEquiv_symm_apply_coe_apply {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1})
    (v : Vertex (n + 1)) :
    ((stableGTEquiv l m g hGap).symm P).1 v = gtCompletion l.1 P.1 v.z (n + 1 - v.x) := (rfl)

/-- **Existence of the stable Gelfand–Tsetlin equivalence with chart-completion inverse law**: in
the uniform input-gap range `m_0 - m_n ≤ l_r - l_{r + 1}`, the fixed-boundary hive type
`FixedIntegerHive (productBoundary l m g)` is equivalent to the weight-`(g - l)` Gelfand–Tsetlin
fibre over `m`, with `gtCompletion` recovering every hive value. -/
theorem exists_stable_gt_equiv {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ l.1 r.castSucc - l.1 r.succ) :
    ∃ e : FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1},
      ∀ h v, h.1 v = gtCompletion l.1 (e h).1 v.z (n + 1 - v.x) :=
  ⟨stableGTEquiv l m g hGap, fun h v => by
    have hb0 : h.1.boundary 0 = l.1 := by rw [h.2, productBoundary_zero]
    rw [stableGTEquiv_apply_coe, ← hb0, gtCompletion_toGTPattern]⟩

/-- Expressing `gtCompletion l P a r` (`a ≤ r ≤ n`) via the output sequence `g = l + P.rowWeight`
replaces the prefix of row `r` by minus its tail over `Ico a r`. -/
private theorem gtCompletion_eq_sub_sum_Ico_of_rowWeight {n : ℕ} {l g : Fin n → ℤ}
    {P : GTPattern n} (hWeight : P.rowWeight = g - l) {a r : ℕ} (har : a ≤ r) (hrn : r ≤ n) :
    gtCompletion l P a r = prefixSum r g - ∑ k ∈ Finset.Ico a r, P k r := by
  have hg : l + P.rowWeight = g := by ext x; have := congrFun hWeight x; simp at this ⊢; omega
  have hdiag := gtCompletion_diag l P hrn
  rw [hg, gtCompletion_def] at hdiag
  rw [gtCompletion_def, Finset.sum_Ico_eq_sub _ har]
  omega

/-- **Uniform output gap implies admissibility**: when `P.rowWeight = g - l` and every adjacent
gap `g_r - g_{r + 1}` of the output sequence `g` is at least `P.topRow 0 - P.topRow (Fin.last n)`,
`IsHiveAdmissible l P` holds automatically. -/
theorem isHiveAdmissible_of_uniform_output_gap {n : ℕ} {l g : Fin (n + 1) → ℤ}
    (P : GTPattern (n + 1)) (hWeight : P.rowWeight = g - l)
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ g r.castSucc - g r.succ) :
    IsHiveAdmissible l P := by
  rw [isHiveAdmissible_iff_gtCompletion_le]
  intro i j hij hjn
  rw [gtCompletion_eq_sub_sum_Ico_of_rowWeight hWeight hij (by omega),
    gtCompletion_eq_sub_sum_Ico_of_rowWeight hWeight (by omega : i + 1 ≤ j + 2) hjn,
    gtCompletion_eq_sub_sum_Ico_of_rowWeight hWeight (by omega : i ≤ j + 1) (by omega),
    gtCompletion_eq_sub_sum_Ico_of_rowWeight hWeight (by omega : i + 1 ≤ j + 1) (by omega),
    prefixSum_succ (by omega : j + 1 < n + 1) g,
    prefixSum_succ (by omega : j < n + 1) g]
  have htail2 :
      ∑ k ∈ Finset.Ico (i + 1) (j + 1), P k (j + 1) -
          ∑ k ∈ Finset.Ico (i + 1) (j + 2), P k (j + 2) ≤
        -P (j + 1) (j + 2) := by
    rw [Finset.sum_Ico_succ_top (by omega : i + 1 ≤ j + 1) (fun k => P k (j + 2))]
    have hle : ∑ k ∈ Finset.Ico (i + 1) (j + 1), P k (j + 1) ≤
        ∑ k ∈ Finset.Ico (i + 1) (j + 1), P k (j + 2) :=
      Finset.sum_le_sum fun k hk =>
        P.entry_le_entry_succ_row (Finset.mem_Ico.mp hk).2 (by omega : j + 1 < n + 1)
    omega
  have htail1 :
      ∑ k ∈ Finset.Ico i (j + 1), P k (j + 1) - ∑ k ∈ Finset.Ico i j, P k j ≤ P i (j + 1) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i < j + 1) (fun k => P k (j + 1)),
      ← Finset.sum_Ico_add' (fun k => P k (j + 1)) i j 1]
    have hle : ∑ k ∈ Finset.Ico i j, P (k + 1) (j + 1) ≤ ∑ k ∈ Finset.Ico i j, P k j :=
      Finset.sum_le_sum fun k _ => P.entry_succ_succ_le_entry (i := k) (j := j) (by omega)
    omega
  have hspread := entry_sub_entry_le_topRow_spread P (i₁ := i) (j₁ := j + 1) (by omega) (by omega)
    (i₂ := j + 1) (j₂ := j + 2) (by omega) hjn
  have hgap_j := hGap ⟨j, by omega⟩
  have hrc : (⟨j, by omega⟩ : Fin n).castSucc = ⟨j, by omega⟩ := rfl
  have hrs : (⟨j, by omega⟩ : Fin n).succ = ⟨j + 1, by omega⟩ := rfl
  rw [hrc, hrs] at hgap_j
  omega

/-- **Uniform output gap makes the remaining rhombus family automatic**: when
`P.rowWeight = g - l` and every adjacent gap `g_r - g_{r + 1}` is at least `m_0 - m_n`,
`gtCompletion l P` satisfies the third product-chart rhombus family. -/
theorem gt_completion_of_uniform_output_gap {n : ℕ}
    (l m g : DominantWeight (n + 1)) (P : GTPattern (n + 1))
    (hTop : P.topRow = m.1) (hWeight : P.rowWeight = g.1 - l.1)
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ g.1 r.castSucc - g.1 r.succ) :
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion l.1 P i j + gtCompletion l.1 P (i + 1) (j + 2) ≤
        gtCompletion l.1 P i (j + 1) + gtCompletion l.1 P (i + 1) (j + 1) :=
  (isHiveAdmissible_iff_gtCompletion_le l.1 P).mp
    (isHiveAdmissible_of_uniform_output_gap P hWeight fun r => by rw [hTop]; exact hGap r)

/-- Full weight-fibre equivalence for `productBoundary l m g` under the uniform output gap
`m_0 - m_n ≤ g_r - g_{r + 1}`. -/
def stableOutputGapGTEquiv {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ g.1 r.castSucc - g.1 r.succ) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} :=
  (fixedHiveEquivGTPattern l m g).trans
    { toFun := fun P => ⟨P.1, P.2.1, P.2.2.1⟩
      invFun := fun P => ⟨P.1, P.2.1, P.2.2,
        isHiveAdmissible_of_uniform_output_gap P.1 P.2.2 fun r => by rw [P.2.1]; exact hGap r⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem stableOutputGapGTEquiv_apply_coe {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ g.1 r.castSucc - g.1 r.succ)
    (h : FixedIntegerHive (productBoundary l m g)) :
    (stableOutputGapGTEquiv l m g hGap h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem stableOutputGapGTEquiv_symm_apply_coe_apply {n : ℕ} (l m g : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, m.1 0 - m.1 (Fin.last n) ≤ g.1 r.castSucc - g.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1})
    (v : Vertex (n + 1)) :
    ((stableOutputGapGTEquiv l m g hGap).symm P).1 v = gtCompletion l.1 P.1 v.z (n + 1 - v.x) :=
  (rfl)

/-- **Cyclic output-gap equivalence**: in the cyclic convention `(λ, μ, ν)` (representing
`c^π_{λ, ν}` with output weight `π = μ*`), if every adjacent gap `μ_r - μ_{r + 1}` (equivalently
`π_i - π_{i + 1}`) is at least `λ_0 - λ_n`, then `cyclicToGTPattern` is an equivalence onto the
entire weight-`(μ* - ν)` Gelfand–Tsetlin fibre over `λ`. -/
def cyclicStableOutputGapEquiv {n : ℕ} (lam μ ν : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, lam.1 0 - lam.1 (Fin.last n) ≤ μ.1 r.castSucc - μ.1 r.succ) :
    FixedIntegerHive (cyclicBoundary lam μ ν) ≃
      {P : GTPattern (n + 1) // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1} :=
  (fixedHiveRotateRotateEquiv lam μ ν).trans <|
    stableOutputGapGTEquiv ν lam μ.dual fun r => by
      have hr := hGap r.rev
      simp only [DominantWeight.dual_apply, Fin.rev_castSucc, Fin.rev_succ]
      omega

@[simp] theorem cyclicStableOutputGapEquiv_apply_coe {n : ℕ} (lam μ ν : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, lam.1 0 - lam.1 (Fin.last n) ≤ μ.1 r.castSucc - μ.1 r.succ)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) :
    (cyclicStableOutputGapEquiv lam μ ν hGap h).1 = h.1.cyclicToGTPattern := (rfl)

@[simp] theorem cyclicStableOutputGapEquiv_symm_apply_coe {n : ℕ} (lam μ ν : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, lam.1 0 - lam.1 (Fin.last n) ≤ μ.1 r.castSucc - μ.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1}) :
    ((cyclicStableOutputGapEquiv lam μ ν hGap).symm P).1 =
      ((stableOutputGapGTEquiv ν lam μ.dual
        (by
          intro r
          have hr := hGap r.rev
          simp only [DominantWeight.dual_apply, Fin.rev_castSucc, Fin.rev_succ]
          omega)).symm P).1.rotate := (rfl)

/-- For `n ≤ 1`, there are no unit rhombi (`j + 2 ≤ n` is empty), so every `P : GTPattern n` is
hive-admissible over every `l : Fin n → ℤ`. -/
theorem isHiveAdmissible_of_le_one {n : ℕ} (hn : n ≤ 1) (l : Fin n → ℤ) (P : GTPattern n) :
    IsHiveAdmissible l P :=
  fun _ _ _ hjn => absurd hjn (by omega)

/-- For `n ≤ 1` (covering both `n = 0` and `n = 1` unconditionally), `FixedIntegerHive` is
equivalent via `toGTPattern` to the whole weight-`(g - l)` Gelfand–Tsetlin fibre over `m`. -/
def fixedHiveEquivGTPatternOfLeOne {n : ℕ} (hn : n ≤ 1) (l m g : DominantWeight n) :
    FixedIntegerHive (productBoundary l m g) ≃
      {P : GTPattern n // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1} :=
  (fixedHiveEquivGTPattern l m g).trans
    { toFun := fun P => ⟨P.1, P.2.1, P.2.2.1⟩
      invFun := fun P => ⟨P.1, P.2.1, P.2.2, isHiveAdmissible_of_le_one hn l.1 P.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem fixedHiveEquivGTPatternOfLeOne_apply_coe {n : ℕ} (hn : n ≤ 1)
    (l m g : DominantWeight n) (h : FixedIntegerHive (productBoundary l m g)) :
    (fixedHiveEquivGTPatternOfLeOne hn l m g h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem fixedHiveEquivGTPatternOfLeOne_symm_apply_coe_apply {n : ℕ} (hn : n ≤ 1)
    (l m g : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = m.1 ∧ P.rowWeight = g.1 - l.1}) (v : Vertex n) :
    ((fixedHiveEquivGTPatternOfLeOne hn l m g).symm P).1 v =
      gtCompletion l.1 P.1 v.z (n - v.x) := (rfl)

end UniformGaps

/-! ### Low-rank admissibility characterizations and sharpness checks (`n = 2` and `n = 3`) -/

section Checks

/-- At rank `2`, the third rhombus family reduces to the single inequality
`P 0 2 - P 0 1 ≤ l 0 - l 1`. -/
theorem isHiveAdmissible_two_iff (l : Fin 2 → ℤ) (P : GTPattern 2) :
    IsHiveAdmissible l P ↔ P 0 2 - P 0 1 ≤ l 0 - l 1 := by
  rw [isHiveAdmissible_def]
  refine ⟨fun h => ?_, fun h i j hij hjn => ?_⟩
  · simpa using h (Nat.zero_le 0) le_rfl
  · obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    simpa using h

/-- At rank `2`, for a pattern `P` with top row `m` and row weight `g - l`, `IsHiveAdmissible l P`
is equivalent to the single boundary inequality `l 1 + m 0 ≤ g 0` (`γ₁ ≥ λ₂ + μ₁`). -/
theorem isHiveAdmissible_two_iff_of_topRow_of_rowWeight (l m g : DominantWeight 2)
    {P : GTPattern 2} (hTop : P.topRow = m.1) (hWeight : P.rowWeight = g.1 - l.1) :
    IsHiveAdmissible l.1 P ↔ l.1 1 + m.1 0 ≤ g.1 0 := by
  have hm0 : P 0 2 = m.1 0 := by simpa using congrFun hTop 0
  have hw0 : P 0 1 = g.1 0 - l.1 0 := by
    have h0 := congrFun hWeight 0
    simpa [GTPattern.rowSum_def] using h0
  rw [isHiveAdmissible_two_iff, hm0, hw0]
  omega

/-- Helper constructor for a rank-`2` Gelfand–Tsetlin pattern with bottom entry `a` and top row
`(b₀, b₁)` (`b₁ ≤ a ≤ b₀`). -/
private def mkGTPatternTwo (a b₀ b₁ : ℤ) (hlo : b₁ ≤ a) (hhi : a ≤ b₀) : GTPattern 2 :=
  ((default : GTPattern 0).extend ![a] (interlaces_iff.mpr fun i => i.elim0)).extend
    ![b₀, b₁] (interlaces_iff.mpr fun i => by fin_cases i; simp [hlo, hhi])

/-- Rank-`2` sharpness check (`λ = (0, 0)`, `μ = (2, 0)`, `γ = (1, 1)`): the weight-`(1, 1)`
Gelfand–Tsetlin fibre over `(2, 0)` is nonempty (with unique pattern `a = 1`), whereas
`hiveCount (productBoundary (0, 0) (2, 0) (1, 1)) = 0` because `γ₁ = 1 < 0 + 2 = λ₂ + μ₁` fails
admissibility. -/
theorem nonempty_gtPattern_two_twoZero_weight_oneOne :
    Nonempty {P : GTPattern 2 // P.topRow = ![2, 0] ∧ P.rowWeight = ![1, 1]} := by
  refine ⟨⟨mkGTPatternTwo 1 2 0 (by decide) (by decide), by simp [mkGTPatternTwo], ?_⟩⟩
  ext r; fin_cases r <;> simp [mkGTPatternTwo, GTPattern.rowSum_def, Finset.sum_range_succ]

/-- For `λ = (0, 0)`, `μ = (2, 0)`, and `γ = (1, 1)`, no hive exists (`hiveCount = 0`). -/
theorem hiveCount_two_zero_twoZero_oneOne :
    hiveCount (productBoundary (0 : DominantWeight 2) ⟨![2, 0], by decide⟩
      ⟨![1, 1], by decide⟩) = 0 := by
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun h => ?_⟩
  let P := fixedHiveEquivGTPattern (0 : DominantWeight 2) ⟨![2, 0], by decide⟩
    ⟨![1, 1], by decide⟩ h
  have hadm := (isHiveAdmissible_two_iff_of_topRow_of_rowWeight
    (0 : DominantWeight 2) ⟨![2, 0], by decide⟩ ⟨![1, 1], by decide⟩ P.2.1 P.2.2.1).mp P.2.2.2
  simp at hadm

/-- Rank-`2` check (`λ = (0, 0)`, `μ = (2, 0)`, `γ = (2, 0)`): `γ = (2, 0)` satisfies
`γ₁ = 2 ≥ 0 + 2 = λ₂ + μ₁` and has `hiveCount = 1`. -/
theorem hiveCount_two_zero_twoZero_twoZero :
    hiveCount (productBoundary (0 : DominantWeight 2) ⟨![2, 0], by decide⟩
      ⟨![2, 0], by decide⟩) = 1 := by
  let P : GTPattern 2 := mkGTPatternTwo 2 2 0 (by decide) (by decide)
  have hTop : P.topRow = ![2, 0] := by simp [P, mkGTPatternTwo]
  have hWeight : P.rowWeight = (![2, 0] : Fin 2 → ℤ) - (0 : DominantWeight 2).1 := by
    ext r; fin_cases r <;> simp [P, mkGTPatternTwo, GTPattern.rowSum_def, Finset.sum_range_succ]
  have hadm : IsHiveAdmissible (0 : DominantWeight 2).1 P :=
    (isHiveAdmissible_two_iff_of_topRow_of_rowWeight
      (0 : DominantWeight 2) ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ hTop hWeight).mpr (by decide)
  have hpos : 0 < hiveCount (productBoundary (0 : DominantWeight 2) ⟨![2, 0], by decide⟩
      ⟨![2, 0], by decide⟩) :=
    hiveCount_pos_iff.mpr
      ⟨(fixedHiveEquivGTPattern 0 ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩).symm
        ⟨P, hTop, hWeight, hadm⟩⟩
  have hle := hiveCount_le_one_two
    (productBoundary (0 : DominantWeight 2) ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩)
  omega

/-- Rank-`2` Clebsch–Gordan check (`λ = μ = (2, 0)`): the uniform input gap `2 - 0 ≤ 2 - 0` holds,
and for every `k ≤ 2` the Clebsch–Gordan summand `γ = (4 - k, k)` (`(4, 0), (3, 1), (2, 2)`) has
`hiveCount = 1` via `stableGTEquiv`. -/
theorem hiveCount_two_clebschGordan_twoZero (k : ℕ) (hk : k ≤ 2) :
    hiveCount (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩
      ⟨![4 - (k : ℤ), (k : ℤ)],
        Fin.antitone_iff_succ_le.mpr fun r => by fin_cases r; simp; omega⟩) = 1 := by
  set g : DominantWeight 2 :=
    ⟨![4 - (k : ℤ), (k : ℤ)], Fin.antitone_iff_succ_le.mpr fun r => by fin_cases r; simp; omega⟩
  have hGap : ∀ r : Fin 1,
      (![2, 0] : Fin 2 → ℤ) 0 - (![2, 0] : Fin 2 → ℤ) (Fin.last 1) ≤
        (![2, 0] : Fin 2 → ℤ) r.castSucc - (![2, 0] : Fin 2 → ℤ) r.succ := by
    intro r; fin_cases r; decide
  let P : GTPattern 2 := mkGTPatternTwo (2 - (k : ℤ)) 2 0 (by omega) (by omega)
  have hTop : P.topRow = ![2, 0] := by simp [P, mkGTPatternTwo]
  have hWeight : P.rowWeight = g.1 - ![2, 0] := by
    ext r
    fin_cases r
    · simp [P, g, mkGTPatternTwo, GTPattern.rowSum_def]; omega
    · simp [P, g, mkGTPatternTwo, GTPattern.rowSum_def, Finset.sum_range_succ]
  have hpos : 0 < hiveCount (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ g) :=
    hiveCount_pos_iff.mpr
      ⟨(stableGTEquiv ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ g hGap).symm ⟨P, hTop, hWeight⟩⟩
  have hle := hiveCount_le_one_two (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ g)
  omega

/-- **Rank-`3` sharpness check (`λ = 0`, `μ = (1, 0, -1)`, `γ = 0`)**: despite the weight-`0` fibre
over `μ` having `2` patterns (`GTPattern.card_topRow_rowWeight_three_one_zero_neg_one_zero`),
`hiveCount (productBoundary 0 (1, 0, -1) 0) = 0` (`c^0_{0, μ} = 0`), confirming that surjectivity
fails without the uniform gap hypothesis. -/
theorem hiveCount_three_zero_adjoint_zero :
    hiveCount (productBoundary (0 : DominantWeight 3) ⟨![1, 0, -1], by decide⟩
      (0 : DominantWeight 3)) = 0 := by
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun ⟨h, hb⟩ => ?_⟩
  have hb_rot : h.rotate.rotate.boundary =
      productBoundary (0 : DominantWeight 3) (0 : DominantWeight 3) ⟨![1, 0, -1], by decide⟩ := by
    ext s r
    fin_cases s <;> fin_cases r <;> simp [hb]
  have hfirst := first_le_of_productBoundary hb_rot
  simp at hfirst

end Checks

end TauCeti.Hive
