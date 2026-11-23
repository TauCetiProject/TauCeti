/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Weight
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The hive-to-Gelfand–Tsetlin difference map and its reconstruction

In the product chart `Vertex.ofChart n i j hij hj = ⟨n - j, j - i, i, _⟩` (`0 ≤ i ≤ j ≤ n`, inverse
`p ↦ (p.z, n - p.x)`), a normalized integer hive `h : IntegerHive n` of clockwise boundary
`productBoundary lam μ γ = ![lam.1, μ.1, γ.dual.1]` satisfies `h(0, 0) = 0`,
`h(0, j) = TauCeti.prefixSum j lam.1` on `A → B` (`s = 0`),
`h(i, n) = |λ| + TauCeti.prefixSum i μ.1` on `B → C` (`s = 1`), and
`h(j, j) = TauCeti.prefixSum j γ.1` on `C → A` (`s = 2`). By
`TauCeti.Hive.isRhombusConcave_iff_ofChart`, unit-rhombus concavity splits into three families:
1. `h(i + 1, j) + h(i, j + 1) ≤ h(i, j) + h(i + 1, j + 1)` (`0 ≤ i < j < n`),
2. `h(i, j) + h(i + 2, j + 1) ≤ h(i + 1, j) + h(i + 1, j + 1)` (`0 ≤ i < j < n`),
3. `h(i, j) + h(i + 1, j + 2) ≤ h(i, j + 1) + h(i + 1, j + 1)` (`0 ≤ i ≤ j`, `j + 2 ≤ n`).

Taking directional differences `P i j = h(i + 1, j) - h(i, j)` on `0 ≤ i < j ≤ n` (and `0` outside)
turns (1)–(2) into Gelfand–Tsetlin interlacing `P i j ≤ P i (j + 1)` and
`P (i + 1) (j + 1) ≤ P i j`, giving `h.toGTPattern : GTPattern n` with top row `μ` and weight
`γ - λ`. Summing from side `0` recovers `h` via
`gtCompletion lam P i j = TauCeti.prefixSum j lam.1 + ∑ k ∈ Finset.range i, P k j`
(`apply_eq_gtCompletion`), and `P` with top row `μ` and weight `γ - λ` comes from a hive of boundary
`productBoundary lam μ γ` iff `gtCompletion lam P` satisfies (3) (`IsGTCompletable lam P`,
`fixedIntegerHiveEquivGTPattern`, `gt_reconstruction_iff`).

Rotating twice (`TauCeti.Hive.rotateRotateEquiv`, adding gauge offset `∑ r, h.boundary 2 r` in chart
coordinates by `TauCeti.Hive.rotate_rotate_apply_ofChart`) identifies cyclic boundary
`![lam.1, μ.1, ν.1]` with `productBoundary ν lam μ.dual`, yielding the quasi-hive equivalence with
top row `lam` and weight `μ.dual - ν` (`cyclicFixedIntegerHiveEquivGTPattern`). Under the uniform
input gap `P.topRow 0 - P.topRow (Fin.last n) ≤ λᵣ - λᵣ₊₁`, family (3) holds automatically
(`isGTCompletable_of_uniform_input_gap`, `gt_completion_of_uniform_input_gap`), giving a bijection
onto the full weight-`(γ - λ)` fibre over `μ` (`fixedIntegerHiveEquivGTPatternOfUniformInputGap`,
`exists_stable_gt_equiv`). Rank-`2` and rank-`3` checks witness strict exclusion outside this range.

## Main definitions

* `TauCeti.Hive.toGTPattern`, `TauCeti.Hive.toGTPatternAddMonoidHom`: directional difference map
  `IntegerHive n →+ GTPattern n`.
* `TauCeti.Hive.gtCompletion`, `TauCeti.Hive.IsGTCompletable`, `TauCeti.Hive.ofGTPattern`: chart
  completion, the remaining rhombus predicate, and hive reconstruction from `(lam, P)`.
* `TauCeti.Hive.integerHiveEquivGTPattern`, `TauCeti.Hive.fixedIntegerHiveEquivGTPattern`:
  global and fixed-boundary hive–pattern equivalences.
* `TauCeti.Hive.fixedIntegerHiveShiftEquiv`: determinant shifts of the boundary weights, which
  shift the pattern by a constant and add an affine hive.
* `TauCeti.Hive.toCyclicGTPattern`, `TauCeti.Hive.toCyclicGTPatternAddMonoidHom`,
  `TauCeti.Hive.cyclicFixedIntegerHiveEquivGTPattern`: cyclic `(λ, μ, ν)` difference map and
  quasi-hive equivalence.
* `TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfUniformInputGap`,
  `TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfLeOne`: full weight-fibre equivalences in the stable
  range and for `n ≤ 1`.

## Main results

* `TauCeti.Hive.topRow_toGTPattern`, `TauCeti.Hive.rowWeight_toGTPattern`,
  `TauCeti.Hive.apply_eq_gtCompletion`, `TauCeti.Hive.eq_of_boundary_zero_eq_of_toGTPattern_eq`,
  `TauCeti.Hive.apply_eq_gtCompletion_toCyclicGTPattern_sub_sum`: top row, weight, chart
  inversion, and injectivity for `toGTPattern` and `toCyclicGTPattern`.
* `TauCeti.Hive.isGTCompletable_iff_sum_sub_le`, `TauCeti.Hive.gt_reconstruction_iff`: explicit
  difference-sum form of `IsGTCompletable` and fixed-boundary reconstruction criterion.
* `TauCeti.Hive.hiveCount_productBoundary_shift`: shifting the inputs by `a, b` and the output by
  `a + b` preserves hive counts.
* `TauCeti.Hive.isGTCompletable_of_uniform_input_gap`,
  `TauCeti.Hive.gt_completion_of_uniform_input_gap`, `TauCeti.Hive.exists_stable_gt_equiv`:
  automatic completion and full fibre equivalence in the stable range.
* `TauCeti.Hive.isGTCompletable_two_iff`, `TauCeti.Hive.hiveCount_two_productBoundary`,
  `TauCeti.Hive.hiveCount_three_zero_adjoint_zero`: low-rank classifications and concrete counts.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §2.
* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 211–249, Theorem 7.4.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Directional finite-difference map and chart completion -/

section DifferenceAndCompletion

variable {n : ℕ}

/-- Directional finite-difference Gelfand–Tsetlin pattern of an integer hive `h`: in the product
chart, `h.toGTPattern i j = h(i + 1, j) - h(i, j)` on the informative cells `0 ≤ i < j ≤ n`, and
`0` outside. -/
def toGTPattern (h : IntegerHive n) : GTPattern n where
  entry i j :=
    if hij : i < j then if hj : j ≤ n then
      h (Vertex.ofChart n (i + 1) j hij hj) - h (Vertex.ofChart n i j hij.le hj)
    else 0 else 0
  zeros' {i j} hout := by
    rcases hout with hnj | hji <;> split_ifs <;> omega
  interlacing' {i j} hij hj := by
    have hleft := h.le_of_isRhombus (isRhombus_ofChart_diag_y hij hj)
    have hright := h.le_of_isRhombus (isRhombus_ofChart_diag_z hij hj)
    simp only [dite_eq_left hij, dite_eq_left hj.le, dite_eq_left (by omega : i < j + 1),
      dite_eq_left (Nat.succ_le_of_lt hj), dite_eq_left (Nat.succ_lt_succ hij)]
    exact ⟨by linarith, by linarith⟩

theorem toGTPattern_apply (h : IntegerHive n) (i j : ℕ) :
    h.toGTPattern i j =
      if hij : i < j then if hj : j ≤ n then
        h (Vertex.ofChart n (i + 1) j hij hj) - h (Vertex.ofChart n i j hij.le hj)
      else 0 else 0 := (rfl)

@[simp] theorem toGTPattern_apply_of_lt_of_le (h : IntegerHive n) {i j : ℕ} (hij : i < j)
    (hj : j ≤ n) :
    h.toGTPattern i j =
      h (Vertex.ofChart n (i + 1) j hij hj) - h (Vertex.ofChart n i j hij.le hj) := by
  rw [toGTPattern_apply, dite_eq_left hij, dite_eq_left hj]

@[simp] theorem toGTPattern_zero : (0 : IntegerHive n).toGTPattern = 0 := by
  ext i j; by_cases h : i < j ∧ j ≤ n
  · simp [toGTPattern_apply_of_lt_of_le _ h.1 h.2, GTPattern.zero_apply]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.zero_apply]

@[simp] theorem toGTPattern_add (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toGTPattern = h₁.toGTPattern + h₂.toGTPattern := by
  ext i j; by_cases h : i < j ∧ j ≤ n
  · simp only [toGTPattern_apply_of_lt_of_le _ h.1 h.2, add_apply, GTPattern.add_apply]; abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.add_apply,
      GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega), add_zero]

@[simp] theorem toGTPattern_nsmul (k : ℕ) (h : IntegerHive n) :
    (k • h).toGTPattern = k • h.toGTPattern := by
  ext i j; by_cases hij : i < j ∧ j ≤ n
  · simp only [toGTPattern_apply_of_lt_of_le _ hij.1 hij.2, nsmul_apply, GTPattern.nsmul_apply,
      nsmul_eq_mul]; ring
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.nsmul_apply,
      GTPattern.entry_eq_zero _ (by omega), smul_zero]

/-- The difference pattern of the normalized affine hive `affine n β γ` is the constant pattern
`GTPattern.const n (γ - β)`. -/
@[simp] theorem toGTPattern_affine (β γ : ℤ) :
    (affine n β γ).toGTPattern = GTPattern.const n (γ - β) := by
  ext i j; by_cases h : i < j ∧ j ≤ n
  · have hsub : j - i = (j - (i + 1)) + 1 := by omega
    simp only [toGTPattern_apply_of_lt_of_le _ h.1 h.2, affine_apply, Vertex.ofChart_y,
      Vertex.ofChart_z, hsub, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      GTPattern.const_apply_of_lt_of_le _ h.1 h.2]; ring
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega)]

/-- `Hive.toGTPattern` bundled as an additive monoid homomorphism `IntegerHive n →+ GTPattern n`. -/
def toGTPatternAddMonoidHom : IntegerHive n →+ GTPattern n :=
  { toFun := toGTPattern, map_zero' := toGTPattern_zero, map_add' := toGTPattern_add }

@[simp] theorem toGTPatternAddMonoidHom_apply (h : IntegerHive n) :
    toGTPatternAddMonoidHom h = h.toGTPattern := (rfl)

/-- The top row of `h.toGTPattern` is the side-`1` (`B → C`) boundary of `h`. -/
@[simp] theorem topRow_toGTPattern (h : IntegerHive n) : h.toGTPattern.topRow = h.boundary 1 := by
  ext i; rw [GTPattern.topRow_apply, h.toGTPattern_apply_of_lt_of_le i.isLt le_rfl,
    Vertex.ofChart_right, Vertex.ofChart_right, boundary_apply]; rfl

@[simp] theorem topWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topWeight = h.boundaryWeight 1 := Subtype.ext (by simp)

/-- Summing the first `i ≤ j` entries of row `j ≤ n` of `h.toGTPattern` telescopes to
`h(i, j) - h(0, j)`. -/
theorem sum_range_toGTPattern (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
      h (Vertex.ofChart n i j hij hj) - h (Vertex.ofChart n 0 j (Nat.zero_le j) hj) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), h.toGTPattern_apply_of_lt_of_le hij hj]; abel

/-- Row `j ≤ n` of `h.toGTPattern` sums to
`TauCeti.prefixSum j (h.boundaryWeight 2).dual.1 - TauCeti.prefixSum j (h.boundary 0)`. -/
theorem rowSum_toGTPattern (h : IntegerHive n) {j : ℕ} (hj : j ≤ n) :
    h.toGTPattern.rowSum j =
      TauCeti.prefixSum j (h.boundaryWeight 2).dual.val - TauCeti.prefixSum j (h.boundary 0) := by
  have hd : (fun r : Fin n => -h.boundary 2 r.rev) = (h.boundaryWeight 2).dual.val :=
    funext fun r => by simp
  rw [GTPattern.rowSum_def, h.sum_range_toGTPattern le_rfl hj, h.apply_ofChart_self hj, hd,
    h.apply_ofChart_zero_left hj]

/-- The torus weight of `h.toGTPattern` is `(h.boundaryWeight 2).dual.1 - h.boundary 0`. -/
@[simp] theorem rowWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.rowWeight = (h.boundaryWeight 2).dual.val - h.boundary 0 := by
  ext r; rw [GTPattern.rowWeight_eq_rowSum_sub, h.rowSum_toGTPattern r.isLt,
    h.rowSum_toGTPattern r.isLt.le, TauCeti.prefixSum_succ r.isLt, TauCeti.prefixSum_succ r.isLt,
    Pi.sub_apply]; abel

theorem topRow_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.topRow = μ.val := by
  rw [h.topRow_toGTPattern, hb, productBoundary_one]

theorem rowWeight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.rowWeight = γ.val - lam.val := by
  have hb2 : h.boundaryWeight 2 = γ.dual := Subtype.ext (by simp [coe_boundaryWeight, hb])
  rw [h.rowWeight_toGTPattern, hb2, DominantWeight.dual_dual, hb, productBoundary_zero]

/-- Inverse chart formula `TauCeti.prefixSum j lam.1 + ∑ k ∈ Finset.range i, P k j` reconstructing
the hive value at `(i, j)` (`0 ≤ i ≤ j ≤ n`) from the side-`0` dominant weight `lam` and a
Gelfand–Tsetlin pattern `P`. -/
def gtCompletion (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) : ℤ :=
  TauCeti.prefixSum j lam.val + ∑ k ∈ Finset.range i, P k j

theorem gtCompletion_def (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion lam P i j = TauCeti.prefixSum j lam.val + ∑ k ∈ Finset.range i, P k j := (rfl)

@[simp] theorem gtCompletion_zero_left (lam : DominantWeight n) (P : GTPattern n) (j : ℕ) :
    gtCompletion lam P 0 j = TauCeti.prefixSum j lam.val := by simp [gtCompletion_def]

@[simp] theorem gtCompletion_zero_right (lam : DominantWeight n) (P : GTPattern n) (i : ℕ) :
    gtCompletion lam P i 0 = 0 := by
  simp [gtCompletion_def, P.entry_eq_zero_of_le (Nat.zero_le _)]

@[simp] theorem gtCompletion_zero_gtPattern (lam : DominantWeight n) (i j : ℕ) :
    gtCompletion lam 0 i j = TauCeti.prefixSum j lam.val := by
  simp [gtCompletion_def, GTPattern.zero_apply]

@[simp] theorem gtCompletion_zero_dominantWeight (P : GTPattern n) (i j : ℕ) :
    gtCompletion 0 P i j = ∑ k ∈ Finset.range i, P k j := by
  simp [gtCompletion_def]

theorem gtCompletion_succ_left (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion lam P (i + 1) j = gtCompletion lam P i j + P i j := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_range_succ, add_assoc]

/-- Advancing the column index from `j` to `j + 1` (`j < n`) adds `lam.1 ⟨j, hj⟩` and the
row-to-row entry differences below `i`. -/
theorem gtCompletion_succ_right (lam : DominantWeight n) (P : GTPattern n) (i : ℕ) {j : ℕ}
    (hj : j < n) :
    gtCompletion lam P i (j + 1) =
      gtCompletion lam P i j + lam.val ⟨j, hj⟩ + ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
  rw [gtCompletion_def, gtCompletion_def, TauCeti.prefixSum_succ hj, Finset.sum_sub_distrib]; abel

@[simp] theorem gtCompletion_add (lam₁ lam₂ : DominantWeight n) (P₁ P₂ : GTPattern n) (i j : ℕ) :
    gtCompletion (lam₁ + lam₂) (P₁ + P₂) i j =
      gtCompletion lam₁ P₁ i j + gtCompletion lam₂ P₂ i j := by
  simp only [gtCompletion_def, DominantWeight.coe_add, TauCeti.prefixSum_add, GTPattern.add_apply,
    Finset.sum_add_distrib]; abel

@[simp] theorem gtCompletion_nsmul (k : ℕ) (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion (k • lam) (k • P) i j = k • gtCompletion lam P i j := by
  simp only [gtCompletion_def, DominantWeight.coe_nsmul, TauCeti.prefixSum_smul,
    GTPattern.nsmul_apply, ← Finset.smul_sum, smul_add]

theorem gtCompletion_shift_dominantWeight (lam : DominantWeight n) (m : ℤ) (P : GTPattern n)
    (i : ℕ) {j : ℕ} (hj : j ≤ n) :
    gtCompletion (lam.shift m) P i j = gtCompletion lam P i j + j * m := by
  rw [gtCompletion_def, gtCompletion_def, TauCeti.prefixSum_eq_sum_castLE hj,
    TauCeti.prefixSum_eq_sum_castLE hj]
  simp only [DominantWeight.shift_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]; ring

theorem gtCompletion_shift_gtPattern (lam : DominantWeight n) (P : GTPattern n) (m : ℤ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion lam (P.shift m) i j = gtCompletion lam P i j + i * m := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_congr rfl fun k hk =>
    P.shift_apply_of_lt_of_le m ((Finset.mem_range.mp hk).trans_le hij) hj,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_assoc]

theorem gtCompletion_shift (lam : DominantWeight n) (a : ℤ) (P : GTPattern n) (b : ℤ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion (lam.shift a) (P.shift b) i j = gtCompletion lam P i j + j * a + i * b := by
  rw [gtCompletion_shift_dominantWeight lam a (P.shift b) i hj,
    gtCompletion_shift_gtPattern lam P b hij hj]; ring

theorem gtCompletion_const (lam : DominantWeight n) (m : ℤ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion lam (GTPattern.const n m) i j = TauCeti.prefixSum j lam.val + i * m := by
  simpa [GTPattern.shift_eq_add_const] using gtCompletion_shift_gtPattern lam 0 m hij hj

theorem gtCompletion_self (lam : DominantWeight n) (P : GTPattern n) (j : ℕ) :
    gtCompletion lam P j j = TauCeti.prefixSum j lam.val + P.rowSum j := by
  rw [gtCompletion_def, GTPattern.rowSum_def]

/-- Past the diagonal (`j ≤ i`), the completion sums all of row `j`, giving
`TauCeti.prefixSum j lam.1 + P.rowSum j`. -/
theorem gtCompletion_of_le (lam : DominantWeight n) (P : GTPattern n) {i j : ℕ} (hij : j ≤ i) :
    gtCompletion lam P i j = TauCeti.prefixSum j lam.val + P.rowSum j := by
  rw [gtCompletion_def, P.sum_range_entry_eq_rowSum hij]

theorem gtCompletion_self_of_rowWeight {lam : DominantWeight n} {P : GTPattern n} {g : Fin n → ℤ}
    (hw : P.rowWeight = g - lam.val) {j : ℕ} (hj : j ≤ n) :
    gtCompletion lam P j j = TauCeti.prefixSum j g := by
  have hg : g = lam.val + P.rowWeight := by
    ext r; have hr := congrFun hw r; simp only [Pi.sub_apply, Pi.add_apply] at hr ⊢; linarith
  rw [gtCompletion_self, ← P.prefixSum_rowWeight hj, hg, TauCeti.prefixSum_add]

theorem gtCompletion_right (lam : DominantWeight n) (P : GTPattern n) (i : ℕ) :
    gtCompletion lam P i n = (∑ r : Fin n, lam.val r) + TauCeti.prefixSum i P.topRow := by
  rw [gtCompletion_def, TauCeti.prefixSum_of_le le_rfl, P.prefixSum_topRow]

/-- Every hive value in the product chart is recovered from `h.boundaryWeight 0` and
`h.toGTPattern` via `gtCompletion`. -/
theorem apply_ofChart_eq_gtCompletion (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    h (Vertex.ofChart n i j hij hj) = gtCompletion (h.boundaryWeight 0) h.toGTPattern i j := by
  rw [gtCompletion_def, coe_boundaryWeight, ← h.apply_ofChart_zero_left hj,
    h.sum_range_toGTPattern hij hj, add_sub_cancel]

/-- **Chart inversion formula**: every integer hive `h` is recovered at `p : Vertex n` as
`gtCompletion (h.boundaryWeight 0) h.toGTPattern p.z (n - p.x)`. -/
theorem apply_eq_gtCompletion (h : IntegerHive n) (p : Vertex n) :
    h p = gtCompletion (h.boundaryWeight 0) h.toGTPattern p.z (n - p.x) := by
  simpa only [Vertex.ofChart_z_sub_x] using h.apply_ofChart_eq_gtCompletion
    (i := p.z) (j := n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x)

/-- An integer hive is uniquely determined by its side-`0` boundary and its Gelfand–Tsetlin
difference pattern. -/
theorem eq_of_boundary_zero_eq_of_toGTPattern_eq {h₁ h₂ : IntegerHive n}
    (hb : h₁.boundary 0 = h₂.boundary 0) (hP : h₁.toGTPattern = h₂.toGTPattern) : h₁ = h₂ := by
  have hw : h₁.boundaryWeight 0 = h₂.boundaryWeight 0 :=
    Subtype.ext (by rw [coe_boundaryWeight, coe_boundaryWeight, hb])
  ext p
  rw [h₁.apply_eq_gtCompletion p, h₂.apply_eq_gtCompletion p, hw, hP]

theorem apply_eq_gtCompletion_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (p : Vertex n) :
    h p = gtCompletion lam h.toGTPattern p.z (n - p.x) := by
  have hb0 : h.boundaryWeight 0 = lam := Subtype.ext (by simp [coe_boundaryWeight, hb])
  rw [h.apply_eq_gtCompletion p, hb0]

/-- A Gelfand–Tsetlin pattern `P` is **hive-completable** over the side-`0` dominant weight `lam`
when `gtCompletion lam P` satisfies the third (remaining) unit-rhombus family in the product
chart. -/
def IsGTCompletable (lam : DominantWeight n) (P : GTPattern n) : Prop :=
  ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
    gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
      gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1)

theorem isGTCompletable_def (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
          gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) := Iff.rfl

theorem isGTCompletable_iff_fin (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P ↔
      ∀ i j : Fin n, i.val ≤ j.val → j.val + 2 ≤ n →
        gtCompletion lam P i.val j.val + gtCompletion lam P (i.val + 1) (j.val + 2) ≤
          gtCompletion lam P i.val (j.val + 1) + gtCompletion lam P (i.val + 1) (j.val + 1) :=
  ⟨fun h i j hij hj => h i.val j.val hij hj,
    fun h i j hij hj => h ⟨i, by omega⟩ ⟨j, by omega⟩ hij hj⟩

/-- `IsGTCompletable lam P` is decidable by bounded quantification over `i, j : Fin n`. -/
instance instDecidableIsGTCompletable (lam : DominantWeight n) (P : GTPattern n) :
    Decidable (IsGTCompletable lam P) :=
  decidable_of_iff _ (isGTCompletable_iff_fin lam P).symm

/-- Single-cell reformulation of the remaining rhombus inequality for `j + 2 ≤ n` in terms of
row-to-row differences of `P` and the gap `lam.1 ⟨j, _⟩ - lam.1 ⟨j + 1, _⟩`. -/
theorem gtCompletion_add_gtCompletion_le_iff_sum_sub_le (lam : DominantWeight n) (P : GTPattern n)
    {i j : ℕ} (hj : j + 2 ≤ n) :
    gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
      gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) ↔
      (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
        (lam.val ⟨j, by omega⟩ - lam.val ⟨j + 1, by omega⟩) +
          ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
  rw [gtCompletion_succ_right lam P i (by omega),
    gtCompletion_succ_right lam P (i + 1) (by omega)]
  constructor <;> intro _ <;> linarith

/-- **Difference-sum characterization of `IsGTCompletable`**. -/
theorem isGTCompletable_iff_sum_sub_le (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P ↔
      ∀ i j : ℕ, i ≤ j → (hj : j + 2 ≤ n) →
        (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
          (lam.val ⟨j, by omega⟩ - lam.val ⟨j + 1, by omega⟩) +
            ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
  forall₄_congr fun _ _ _ hj => gtCompletion_add_gtCompletion_le_iff_sum_sub_le lam P hj

@[simp] theorem isGTCompletable_zero_right (lam : DominantWeight n) : IsGTCompletable lam 0 := by
  rw [isGTCompletable_iff_sum_sub_le]; intro i j _ hj
  have hle : (⟨j, by omega⟩ : Fin n) ≤ ⟨j + 1, by omega⟩ := Fin.le_def.mpr (Nat.le_succ j)
  simpa [GTPattern.zero_apply, sub_nonneg] using lam.antitone hle

theorem IsGTCompletable.add {lam₁ lam₂ : DominantWeight n} {P₁ P₂ : GTPattern n}
    (h₁ : IsGTCompletable lam₁ P₁) (h₂ : IsGTCompletable lam₂ P₂) :
    IsGTCompletable (lam₁ + lam₂) (P₁ + P₂) := fun i j hij hj => by
  simp only [gtCompletion_add]; linarith [h₁ i j hij hj, h₂ i j hij hj]

theorem IsGTCompletable.nsmul {lam : DominantWeight n} {P : GTPattern n}
    (h : IsGTCompletable lam P) (k : ℕ) : IsGTCompletable (k • lam) (k • P) := fun i j hij hj => by
  simp only [gtCompletion_nsmul, ← smul_add]; exact nsmul_le_nsmul_right (h i j hij hj) k

@[simp] theorem isGTCompletable_shift_left_iff (lam : DominantWeight n) (m : ℤ) (P : GTPattern n) :
    IsGTCompletable (lam.shift m) P ↔ IsGTCompletable lam P := by
  simp only [isGTCompletable_iff_sum_sub_le, DominantWeight.shift_apply, add_sub_add_right_eq_sub]

@[simp] theorem isGTCompletable_shift_right_iff (lam : DominantWeight n) (P : GTPattern n) (m : ℤ) :
    IsGTCompletable lam (P.shift m) ↔ IsGTCompletable lam P :=
  forall₄_congr fun i j hij hj => by
    rw [gtCompletion_shift_gtPattern lam P m hij (by omega),
      gtCompletion_shift_gtPattern lam P m (by omega) hj,
      gtCompletion_shift_gtPattern lam P m (by omega) (by omega),
      gtCompletion_shift_gtPattern lam P m (by omega) (by omega)]
    constructor <;> intro _ <;> linarith

@[simp] theorem isGTCompletable_const (lam : DominantWeight n) (m : ℤ) :
    IsGTCompletable lam (GTPattern.const n m) := by
  simpa [GTPattern.shift_eq_add_const] using (isGTCompletable_shift_right_iff lam 0 m).mpr (by simp)

@[simp] theorem isGTCompletable_toGTPattern (h : IntegerHive n) :
    IsGTCompletable (h.boundaryWeight 0) h.toGTPattern := by
  intro i j hij hj
  simp only [← h.apply_ofChart_eq_gtCompletion hij (by omega),
    ← h.apply_ofChart_eq_gtCompletion (by omega : i + 1 ≤ j + 2) hj,
    ← h.apply_ofChart_eq_gtCompletion (by omega : i ≤ j + 1) (by omega),
    ← h.apply_ofChart_eq_gtCompletion (Nat.succ_le_succ hij) (by omega)]
  exact h.le_of_isRhombus (isRhombus_ofChart_diag_x hij hj)

end DifferenceAndCompletion

/-! ### Hive reconstruction and object equivalences -/

section Reconstruction

variable {n : ℕ}

/-- Reconstruct a normalized integer hive from a side-`0` dominant weight `lam` and a
hive-completable Gelfand–Tsetlin pattern `P`. -/
def ofGTPattern (lam : DominantWeight n) (P : GTPattern n) (hP : IsGTCompletable lam P) :
    IntegerHive n where
  value p := gtCompletion lam P p.z (n - p.x)
  value_cornerA' := by simp
  le_of_isRhombus' {a b c d} hr := by
    refine (isRhombusConcave_def (fun p : Vertex n => gtCompletion lam P p.z (n - p.x))).mp ?_ hr
    rw [isRhombusConcave_iff_ofChart]
    have hchart (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
        gtCompletion lam P (Vertex.ofChart n i j hij hj).z
          (n - (Vertex.ofChart n i j hij hj).x) = gtCompletion lam P i j := by
      simp [Nat.sub_sub_self hj]
    refine ⟨fun i j hij hj => ?_, fun i j hij hj => ?_, fun i j hij hj => ?_⟩
    · simp only [hchart]; rw [gtCompletion_succ_left, gtCompletion_succ_left]
      linarith [P.entry_le_entry_succ_row hij hj]
    · simp only [hchart]
      rw [gtCompletion_succ_left lam P (i + 1) (j + 1), gtCompletion_succ_left lam P i j]
      linarith [P.entry_succ_succ_le_entry (i := i) hj]
    · simp only [hchart]; exact hP i j hij hj

@[simp] theorem ofGTPattern_apply (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) (p : Vertex n) :
    ofGTPattern lam P hP p = gtCompletion lam P p.z (n - p.x) := (rfl)

theorem ofGTPattern_ofChart (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    ofGTPattern lam P hP (Vertex.ofChart n i j hij hj) = gtCompletion lam P i j := by
  simp [Nat.sub_sub_self hj]

@[simp] theorem ofGTPattern_zero (h : IsGTCompletable (0 : DominantWeight n) 0) :
    ofGTPattern 0 0 h = 0 := by ext p; simp

theorem ofGTPattern_add {lam₁ lam₂ : DominantWeight n} {P₁ P₂ : GTPattern n}
    (h₁ : IsGTCompletable lam₁ P₁) (h₂ : IsGTCompletable lam₂ P₂)
    (h : IsGTCompletable (lam₁ + lam₂) (P₁ + P₂)) :
    ofGTPattern (lam₁ + lam₂) (P₁ + P₂) h = ofGTPattern lam₁ P₁ h₁ + ofGTPattern lam₂ P₂ h₂ := by
  ext p; simp

theorem ofGTPattern_nsmul (k : ℕ) {lam : DominantWeight n} {P : GTPattern n}
    (hP : IsGTCompletable lam P) (hk : IsGTCompletable (k • lam) (k • P)) :
    ofGTPattern (k • lam) (k • P) hk = k • ofGTPattern lam P hP := by
  ext p; simp

/-- Determinant shifts on `lam` by `a` and on `P` by `b` add the normalized affine hive
`affine n a (a + b)` under `ofGTPattern`. -/
theorem ofGTPattern_shift {lam : DominantWeight n} {P : GTPattern n} (a b : ℤ)
    (hP : IsGTCompletable lam P) (hshift : IsGTCompletable (lam.shift a) (P.shift b)) :
    ofGTPattern (lam.shift a) (P.shift b) hshift = ofGTPattern lam P hP + affine n a (a + b) := by
  ext p; have := p.sum_eq
  have hsub : ((n - p.x : ℕ) : ℤ) = (p.y : ℤ) + p.z := by omega
  rw [ofGTPattern_apply, gtCompletion_shift lam a P b (by omega) (Nat.sub_le n p.x), hsub,
    add_apply, ofGTPattern_apply, affine_apply, nsmul_eq_mul, nsmul_eq_mul]; ring

@[simp] theorem ofGTPattern_const (a b : ℤ)
    (h : IsGTCompletable ((0 : DominantWeight n).shift a) (GTPattern.const n b)) :
    ofGTPattern ((0 : DominantWeight n).shift a) (GTPattern.const n b) h = affine n a (a + b) := by
  have hc : GTPattern.const n b = (0 : GTPattern n).shift b := by
    rw [GTPattern.shift_eq_add_const, zero_add]
  revert h; rw [hc]; intro h
  rw [ofGTPattern_shift a b (isGTCompletable_zero_right 0) h, ofGTPattern_zero, zero_add]

@[simp] theorem toGTPattern_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) : (ofGTPattern lam P hP).toGTPattern = P := by
  ext i j; by_cases h : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le _ h.1 h.2, ofGTPattern_ofChart, ofGTPattern_ofChart,
       gtCompletion_succ_left, add_sub_cancel_left]
  · exact GTPattern.entry_eq_zero _ (by omega) |>.trans (P.entry_eq_zero (by omega)).symm

@[simp] theorem boundary_ofGTPattern_zero (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) : (ofGTPattern lam P hP).boundary 0 = lam.val := by
  ext r
  simp [boundary_apply, Nat.sub_sub_self r.isLt, Nat.sub_sub_self r.isLt.le,
    TauCeti.prefixSum_succ r.isLt]

@[simp] theorem boundaryWeight_ofGTPattern_zero (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundaryWeight 0 = lam := Subtype.ext (by simp)

@[simp] theorem boundary_ofGTPattern_one (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) : (ofGTPattern lam P hP).boundary 1 = P.topRow := by
  rw [← topRow_toGTPattern, toGTPattern_ofGTPattern]

@[simp] theorem boundaryWeight_ofGTPattern_one (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundaryWeight 1 = P.topWeight := Subtype.ext (by simp)

theorem coe_dual_boundaryWeight_ofGTPattern_two (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    ((ofGTPattern lam P hP).boundaryWeight 2).dual.val = lam.val + P.rowWeight := by
  have hw := rowWeight_toGTPattern (ofGTPattern lam P hP)
  rw [toGTPattern_ofGTPattern, boundary_ofGTPattern_zero] at hw
  ext r; have hr := congrFun hw r; simp only [Pi.sub_apply, Pi.add_apply] at hr ⊢; linarith

/-- Whenever `P` is hive-completable over `lam`, `lam.1 + P.rowWeight` is automatically antitone
(dominant), as the dual of side `2` of `ofGTPattern lam P hP`. -/
theorem antitone_add_rowWeight_of_isGTCompletable {lam : DominantWeight n} {P : GTPattern n}
    (hP : IsGTCompletable lam P) : Antitone (lam.val + P.rowWeight) :=
  coe_dual_boundaryWeight_ofGTPattern_two lam P hP ▸
    ((ofGTPattern lam P hP).boundaryWeight 2).dual.property

@[simp] theorem boundaryWeight_ofGTPattern_two (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundaryWeight 2 =
      DominantWeight.dual ⟨lam.val + P.rowWeight, antitone_add_rowWeight_of_isGTCompletable hP⟩
          := by
  rw [← DominantWeight.dual_dual ((ofGTPattern lam P hP).boundaryWeight 2)]
  exact congrArg DominantWeight.dual
    (Subtype.ext (coe_dual_boundaryWeight_ofGTPattern_two lam P hP))

@[simp] theorem boundary_ofGTPattern_two (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundary 2 = fun r => -(lam.val r.rev + P.rowWeight r.rev) := by
  ext r; simp [← coe_boundaryWeight, boundaryWeight_ofGTPattern_two]

theorem boundary_ofGTPattern_eq_productBoundary {lam μ γ : DominantWeight n} {P : GTPattern n}
    (hTop : P.topRow = μ.val) (hWeight : P.rowWeight = γ.val - lam.val)
        (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundary = productBoundary lam μ γ := by
  ext s r; fin_cases s
  · simp
  · rw [Fin.mk_one, boundary_ofGTPattern_one, hTop, productBoundary_one]
  · simp [hWeight]

@[simp] theorem ofGTPattern_toGTPattern (h : IntegerHive n) :
    ofGTPattern (h.boundaryWeight 0) h.toGTPattern h.isGTCompletable_toGTPattern = h := by
  ext p; exact (h.apply_eq_gtCompletion p).symm

/-- Global equivalence between normalized integer hives of size `n` and pairs `(lam, P)` of a
dominant weight and a hive-completable Gelfand–Tsetlin pattern. -/
def integerHiveEquivGTPattern (n : ℕ) :
    IntegerHive n ≃ {lp : DominantWeight n × GTPattern n // IsGTCompletable lp.1 lp.2} where
  toFun h := ⟨(h.boundaryWeight 0, h.toGTPattern), h.isGTCompletable_toGTPattern⟩
  invFun lp := ofGTPattern lp.val.1 lp.val.2 lp.property
  left_inv h := h.ofGTPattern_toGTPattern
  right_inv lp := Subtype.ext <| Prod.ext (boundaryWeight_ofGTPattern_zero lp.val.1 lp.val.2
      lp.property)
    (toGTPattern_ofGTPattern lp.val.1 lp.val.2 lp.property)

@[simp] theorem integerHiveEquivGTPattern_apply_coe (h : IntegerHive n) :
    (integerHiveEquivGTPattern n h).val = (h.boundaryWeight 0, h.toGTPattern) := (rfl)

@[simp] theorem integerHiveEquivGTPattern_symm_apply
    (lp : {lp : DominantWeight n × GTPattern n // IsGTCompletable lp.1 lp.2}) :
    (integerHiveEquivGTPattern n).symm lp = ofGTPattern lp.val.1 lp.val.2 lp.property := (rfl)

/-- **Fixed-boundary hive–pattern equivalence**: integer hives with boundary
`productBoundary lam μ γ` correspond bijectively to Gelfand–Tsetlin patterns `P` with top row `μ`,
weight `γ - λ`, and `IsGTCompletable lam P`. -/
def fixedIntegerHiveEquivGTPattern (lam μ γ : DominantWeight n) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val ∧ IsGTCompletable lam P}
          where
  toFun h := ⟨h.val.toGTPattern, topRow_toGTPattern_of_productBoundary h.property,
    rowWeight_toGTPattern_of_productBoundary h.property, by
      have hb0 : h.val.boundaryWeight 0 = lam := Subtype.ext (by simp [coe_boundaryWeight,
          h.property])
      exact hb0.subst (motive := fun l => IsGTCompletable l h.val.toGTPattern)
        h.val.isGTCompletable_toGTPattern⟩
  invFun P := ⟨ofGTPattern lam P.val P.property.2.2,
    boundary_ofGTPattern_eq_productBoundary P.property.1 P.property.2.1 P.property.2.2⟩
  left_inv h := Subtype.ext <| ext fun p =>
    (apply_eq_gtCompletion_of_productBoundary h.property p).symm
  right_inv P := Subtype.ext (toGTPattern_ofGTPattern lam P.val P.property.2.2)

@[simp] theorem fixedIntegerHiveEquivGTPattern_apply_coe (lam μ γ : DominantWeight n)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h).val = h.val.toGTPattern := (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val ∧ IsGTCompletable lam
        P}) :
    ((fixedIntegerHiveEquivGTPattern lam μ γ).symm P).val = ofGTPattern lam P.val P.property.2.2 :=
        (rfl)

theorem hiveCount_productBoundary_eq_card_gtPattern (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern n //
        P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val ∧ IsGTCompletable lam P} := by
  rw [← natCard_fixedIntegerHive]; exact Nat.card_congr (fixedIntegerHiveEquivGTPattern lam μ γ)

/-- **Determinant-shift covariance of hive fibres**: shifting the inputs `lam, μ` by `a, b` and
the output `γ` by `a + b` identifies the integer hives of boundary `productBoundary lam μ γ` with
those of the shifted boundary, by adding the affine hive `affine n a (a + b)`
(`fixedIntegerHiveShiftEquiv_apply_coe`). -/
def fixedIntegerHiveShiftEquiv (lam μ γ : DominantWeight n) (a b : ℤ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) :=
  ((fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquiv (GTPattern.shiftEquiv n b) fun P => by
      simp only [GTPattern.shiftEquiv_apply, GTPattern.topRow_shift, GTPattern.rowWeight_shift,
        isGTCompletable_shift_left_iff, isGTCompletable_shift_right_iff, funext_iff,
        Pi.sub_apply, DominantWeight.shift_apply]
      refine and_congr (forall_congr' fun i => add_left_inj b).symm
        (and_congr_left' (forall_congr' fun i => ?_))
      constructor <;> intro h <;> linarith)).trans
    (fixedIntegerHiveEquivGTPattern _ _ _).symm

@[simp] theorem fixedIntegerHiveShiftEquiv_apply_coe (lam μ γ : DominantWeight n) (a b : ℤ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveShiftEquiv lam μ γ a b h).val = h.val + affine n a (a + b) := by
  have hb0 : h.val.boundaryWeight 0 = lam := Subtype.ext (by simp [coe_boundaryWeight, h.property])
  -- `h` is the hive reconstructed from its own pattern over its side-`0` weight `lam`.
  have hrec : ∀ (l : DominantWeight n) (_ : h.val.boundaryWeight 0 = l)
      (hP : IsGTCompletable l h.val.toGTPattern), ofGTPattern l h.val.toGTPattern hP = h.val := by
    rintro l rfl _; exact ofGTPattern_toGTPattern h.val
  have hP : IsGTCompletable lam h.val.toGTPattern := (fixedIntegerHiveEquivGTPattern lam μ γ
      h).property.2.2
  simp only [fixedIntegerHiveShiftEquiv, Equiv.trans_apply,
    fixedIntegerHiveEquivGTPattern_symm_apply_coe, Equiv.subtypeEquiv_apply,
    GTPattern.shiftEquiv_apply, fixedIntegerHiveEquivGTPattern_apply_coe]
  rw [ofGTPattern_shift a b hP, hrec lam hb0 hP]

@[simp] theorem fixedIntegerHiveShiftEquiv_symm_apply_coe (lam μ γ : DominantWeight n) (a b : ℤ)
    (h : FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)))) :
    ⇑((fixedIntegerHiveShiftEquiv lam μ γ a b).symm h).val = ⇑h.val - ⇑(affine n a (a + b)) := by
  rw [eq_sub_iff_add_eq, ← coe_add, ← fixedIntegerHiveShiftEquiv_apply_coe, Equiv.apply_symm_apply]

/-- Determinant shifts of the inputs by `a, b` and of the output by `a + b` preserve hive
counts. -/
theorem hiveCount_productBoundary_shift (lam μ γ : DominantWeight n) (a b : ℤ) :
    hiveCount (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) =
      hiveCount (productBoundary lam μ γ) := by
  simp only [← natCard_fixedIntegerHive]
  exact (Nat.card_congr (fixedIntegerHiveShiftEquiv lam μ γ a b)).symm

/-- **Gelfand–Tsetlin reconstruction criterion**: a pattern `P` with top row `μ` and weight
`γ - λ` is the difference pattern of a hive with boundary `productBoundary lam μ γ` (realized via
`gtCompletion lam P`) if and only if the remaining rhombus family holds on `gtCompletion lam P`. -/
theorem gt_reconstruction_iff (lam μ γ : DominantWeight n) (P : GTPattern n)
    (hTop : P.topRow = μ.val) (hWeight : P.rowWeight = γ.val - lam.val) :
    (∃ h : FixedIntegerHive (productBoundary lam μ γ),
      ∀ v : Vertex n, h.val v = gtCompletion lam P v.z (n - v.x)) ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
          gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) := by
  refine ⟨fun ⟨h, hv⟩ i j hij hj => ?_, fun hrem =>
    ⟨(fixedIntegerHiveEquivGTPattern lam μ γ).symm ⟨P, hTop, hWeight, hrem⟩, fun _ => rfl⟩⟩
  simpa only [hv, Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self (by omega : j ≤ n),
    Nat.sub_sub_self hj, Nat.sub_sub_self (by omega : j + 1 ≤ n)] using
    h.val.le_of_isRhombus (isRhombus_ofChart_diag_x hij hj)

end Reconstruction

/-! ### Cyclic `(λ, μ, ν)` orientation and Henriques–Kamnitzer quasi-hive conversion -/

section CyclicOrientation

variable {n : ℕ}

/-- Directional difference pattern attached to a hive in the cyclic `(λ, μ, ν)` orientation:
`h.toCyclicGTPattern = h.rotate.rotate.toGTPattern`. -/
def toCyclicGTPattern (h : IntegerHive n) : GTPattern n := h.rotate.rotate.toGTPattern

theorem toCyclicGTPattern_def (h : IntegerHive n) :
    h.toCyclicGTPattern = h.rotate.rotate.toGTPattern := (rfl)

/-- The constant gauge offset cancels in `toCyclicGTPattern`, giving the direct lattice difference
`h ⟨j - (i + 1), i + 1, n - j, _⟩ - h ⟨j - i, i, n - j, _⟩` for `0 ≤ i < j ≤ n`. -/
@[simp] theorem toCyclicGTPattern_apply_of_lt_of_le (h : IntegerHive n) {i j : ℕ} (hij : i < j)
    (hj : j ≤ n) :
    h.toCyclicGTPattern i j =
      h ⟨j - (i + 1), i + 1, n - j, by omega⟩ - h ⟨j - i, i, n - j, by omega⟩ := by
  rw [toCyclicGTPattern_def, toGTPattern_apply_of_lt_of_le _ hij hj,
    h.rotate_rotate_apply_ofChart hij hj, h.rotate_rotate_apply_ofChart hij.le hj]; abel

theorem toCyclicGTPattern_apply (h : IntegerHive n) (i j : ℕ) :
    h.toCyclicGTPattern i j =
      if hij : i < j then if hj : j ≤ n then
        h ⟨j - (i + 1), i + 1, n - j, by omega⟩ - h ⟨j - i, i, n - j, by omega⟩
      else 0 else 0 := by
  split_ifs with hij hj
  · exact h.toCyclicGTPattern_apply_of_lt_of_le hij hj
  · exact h.toCyclicGTPattern.entry_eq_zero (by omega)
  · exact h.toCyclicGTPattern.entry_eq_zero (by omega)

@[simp] theorem toCyclicGTPattern_rotate (h : IntegerHive n) :
    h.rotate.toCyclicGTPattern = h.toGTPattern := by
  rw [toCyclicGTPattern_def, rotate_rotate_rotate]

@[simp] theorem toCyclicGTPattern_zero : (0 : IntegerHive n).toCyclicGTPattern = 0 := by
  simp [toCyclicGTPattern_def]

@[simp] theorem toCyclicGTPattern_add (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toCyclicGTPattern = h₁.toCyclicGTPattern + h₂.toCyclicGTPattern := by
  simp [toCyclicGTPattern_def]

@[simp] theorem toCyclicGTPattern_nsmul (k : ℕ) (h : IntegerHive n) :
    (k • h).toCyclicGTPattern = k • h.toCyclicGTPattern := by
  simp [toCyclicGTPattern_def]

/-- In the cyclic orientation, the normalized affine hive `affine n β γ` has constant difference
pattern `GTPattern.const n β`. -/
@[simp] theorem toCyclicGTPattern_affine (β γ : ℤ) :
    (affine n β γ).toCyclicGTPattern = GTPattern.const n β := by
  rw [toCyclicGTPattern_def, rotate_affine, rotate_affine, toGTPattern_affine]
  exact congrArg (GTPattern.const n) (by ring)

/-- `Hive.toCyclicGTPattern` bundled as an additive monoid homomorphism
`IntegerHive n →+ GTPattern n`. -/
def toCyclicGTPatternAddMonoidHom : IntegerHive n →+ GTPattern n :=
  { toFun := toCyclicGTPattern, map_zero' := toCyclicGTPattern_zero,
    map_add' := toCyclicGTPattern_add }

@[simp] theorem toCyclicGTPatternAddMonoidHom_apply (h : IntegerHive n) :
    toCyclicGTPatternAddMonoidHom h = h.toCyclicGTPattern := (rfl)

@[simp] theorem topRow_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.topRow = h.boundary 0 := by simp [toCyclicGTPattern_def, boundary_rotate]

@[simp] theorem topWeight_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.topWeight = h.boundaryWeight 0 := Subtype.ext (by simp)

theorem rowSum_toCyclicGTPattern (h : IntegerHive n) {j : ℕ} (hj : j ≤ n) :
    h.toCyclicGTPattern.rowSum j =
      TauCeti.prefixSum j (h.boundaryWeight 1).dual.val - TauCeti.prefixSum j (h.boundary 2) := by
  simpa [toCyclicGTPattern_def, boundary_rotate, boundaryWeight_rotate] using
    h.rotate.rotate.rowSum_toGTPattern hj

@[simp] theorem rowWeight_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.rowWeight = (h.boundaryWeight 1).dual.val - h.boundary 2 := by
  simp [toCyclicGTPattern_def, boundary_rotate, boundaryWeight_rotate]

@[simp] theorem isGTCompletable_toCyclicGTPattern (h : IntegerHive n) :
    IsGTCompletable (h.boundaryWeight 2) h.toCyclicGTPattern := by
  simpa [toCyclicGTPattern_def, boundaryWeight_rotate] using
    h.rotate.rotate.isGTCompletable_toGTPattern

theorem rotate_ofGTPattern_apply (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) (p : Vertex n) :
    (ofGTPattern lam P hP).rotate p =
      gtCompletion lam P p.y (n - p.z) - ∑ r : Fin n, lam.val r := by
  simp [TauCeti.prefixSum_of_le le_rfl]

@[simp] theorem rotate_ofGTPattern_toCyclicGTPattern (h : IntegerHive n) :
    (ofGTPattern (h.boundaryWeight 2) h.toCyclicGTPattern
      h.isGTCompletable_toCyclicGTPattern).rotate = h := by
  suffices ofGTPattern (h.boundaryWeight 2) h.toCyclicGTPattern
      h.isGTCompletable_toCyclicGTPattern = h.rotate.rotate by rw [this, rotate_rotate_rotate]
  ext p
  rw [ofGTPattern_apply, h.rotate.rotate.apply_eq_gtCompletion p]
  simp [toCyclicGTPattern_def, boundaryWeight_rotate]

/-- **Cyclic chart inversion formula**: every integer hive `h` is recovered at `p : Vertex n` from
`h.boundaryWeight 2` and `h.toCyclicGTPattern` as
`gtCompletion (h.boundaryWeight 2) h.toCyclicGTPattern p.y (n - p.z) - ∑ r, h.boundary 2 r`. -/
theorem apply_eq_gtCompletion_toCyclicGTPattern_sub_sum (h : IntegerHive n) (p : Vertex n) :
    h p =
      gtCompletion (h.boundaryWeight 2) h.toCyclicGTPattern p.y (n - p.z) -
        ∑ r : Fin n, h.boundary 2 r := by
  conv_lhs => rw [← h.rotate_ofGTPattern_toCyclicGTPattern]
  rw [rotate_ofGTPattern_apply, coe_boundaryWeight]

/-- **Cyclic quasi-hive equivalence (Henriques–Kamnitzer, Theorem 7.4)**: integer hives with
clockwise cyclic boundary `![lam.1, μ.1, ν.1]` correspond bijectively to Gelfand–Tsetlin patterns
with top row `lam.1`, torus weight `μ.dual.1 - ν.1`, and `IsGTCompletable ν P`. -/
def cyclicFixedIntegerHiveEquivGTPattern (lam μ ν : DominantWeight n) :
    FixedIntegerHive ![lam.val, μ.val, ν.val] ≃
      {P : GTPattern n // P.topRow = lam.val ∧ P.rowWeight = μ.dual.val - ν.val ∧ IsGTCompletable ν
          P} :=
  (rotateRotateEquiv lam μ ν).trans (fixedIntegerHiveEquivGTPattern ν lam μ.dual)

@[simp] theorem cyclicFixedIntegerHiveEquivGTPattern_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive ![lam.val, μ.val, ν.val]) :
    (cyclicFixedIntegerHiveEquivGTPattern lam μ ν h).val = h.val.toCyclicGTPattern := by
  simp [cyclicFixedIntegerHiveEquivGTPattern, toCyclicGTPattern_def]

@[simp] theorem cyclicFixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ ν : DominantWeight n)
    (P : {P : GTPattern n //
      P.topRow = lam.val ∧ P.rowWeight = μ.dual.val - ν.val ∧ IsGTCompletable ν P}) :
    ((cyclicFixedIntegerHiveEquivGTPattern lam μ ν).symm P).val =
      (ofGTPattern ν P.val P.property.2.2).rotate := by simp [cyclicFixedIntegerHiveEquivGTPattern]

theorem cyclicFixedIntegerHiveEquivGTPattern_symm_apply (lam μ ν : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = lam.val ∧ P.rowWeight = μ.dual.val - ν.val ∧ IsGTCompletable
        ν P})
    (p : Vertex n) :
    ((cyclicFixedIntegerHiveEquivGTPattern lam μ ν).symm P).val p =
      gtCompletion ν P.val p.y (n - p.z) - ∑ r : Fin n, ν.val r := by
  rw [cyclicFixedIntegerHiveEquivGTPattern_symm_apply_coe, rotate_ofGTPattern_apply]

theorem hiveCount_cyclic_eq_card_gtPattern (lam μ ν : DominantWeight n) :
    hiveCount ![lam.val, μ.val, ν.val] =
      Nat.card {P : GTPattern n //
        P.topRow = lam.val ∧ P.rowWeight = μ.dual.val - ν.val ∧ IsGTCompletable ν P} := by
  rw [hiveCount_cyclic_eq_hiveCount_productBoundary, hiveCount_productBoundary_eq_card_gtPattern]

end CyclicOrientation

/-! ### Uniform input gap and stable Gelfand–Tsetlin fibre equivalence -/

section UniformInputGap

/-- **Uniform input gap**: when `P.topRow 0 - P.topRow (Fin.last n)` is at most
`lam.1 r.castSucc - lam.1 r.succ` for every `r : Fin n`, `P` is automatically hive-completable
over `lam`. -/
theorem isGTCompletable_of_uniform_input_gap {n : ℕ} {lam : DominantWeight (n + 1)}
    {P : GTPattern (n + 1)}
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ lam.val r.castSucc - lam.val r.succ) :
    IsGTCompletable lam P := by
  rw [isGTCompletable_iff_sum_sub_le]
  intro i j hij hj
  have : 0 ≤ ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
    Finset.sum_nonneg fun k hk => sub_nonneg.mpr <|
      P.entry_le_entry_succ_row (by have := Finset.mem_range.mp hk; omega) (by omega)
  have : (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      P 0 (j + 2) - P (i + 1) (j + 2) :=
    (Finset.sum_le_sum fun k _ =>
      sub_le_sub_left (P.entry_succ_succ_le_entry (by omega)) _).trans_eq
      (Finset.sum_range_sub' (fun k => P k (j + 2)) (i + 1))
  have : P 0 (j + 2) ≤ P.topRow 0 := (P.entry_mem_Icc (Nat.zero_lt_succ (j + 1)) hj).2
  have : P.topRow (Fin.last n) ≤ P (i + 1) (j + 2) :=
    (P.entry_mem_Icc (Nat.succ_lt_succ (Nat.lt_succ_of_le hij)) hj).1
  have hg := hGap ⟨j, by omega⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hg
  linarith

/-- **Uniform input gap** (unfolded on patterns of top row `μ`): when
`μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ` for all `r : Fin n`, the remaining
rhombus family holds on `gtCompletion lam P` for every `P : GTPattern (n + 1)` with top row `μ`. -/
theorem gt_completion_of_uniform_input_gap {n : ℕ} (lam μ : DominantWeight (n + 1))
    (P : GTPattern (n + 1)) (hTop : P.topRow = μ.val)
    (hGap : ∀ r : Fin n, μ.val 0 - μ.val (Fin.last n) ≤ lam.val r.castSucc - lam.val r.succ) :
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
        gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) :=
  isGTCompletable_of_uniform_input_gap (hTop ▸ hGap)

section UniformInputGapEquiv

variable {n : ℕ} (lam μ γ : DominantWeight (n + 1))
  (hGap : ∀ r : Fin n, μ.val 0 - μ.val (Fin.last n) ≤ lam.val r.castSucc - lam.val r.succ)
include hGap

/-- Under the uniform input gap on `lam`, fixed-boundary integer hives with boundary
`productBoundary lam μ γ` are equivalent to the entire weight-`(γ - λ)` Gelfand–Tsetlin fibre over
`μ`. -/
def fixedIntegerHiveEquivGTPatternOfUniformInputGap :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans <| Equiv.subtypeEquivRight fun _ =>
    ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
      fun ⟨ht, hw⟩ => ⟨ht, hw, isGTCompletable_of_uniform_input_gap (by rwa [ht])⟩⟩

@[simp] theorem fixedIntegerHiveEquivGTPatternOfUniformInputGap_apply_coe
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfUniformInputGap lam μ γ hGap h).val = h.val.toGTPattern :=
        (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPatternOfUniformInputGap_symm_apply_coe
    (P : {P : GTPattern (n + 1) // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val}) :
    ((fixedIntegerHiveEquivGTPatternOfUniformInputGap lam μ γ hGap).symm P).val =
      ofGTPattern lam P.val (isGTCompletable_of_uniform_input_gap (by rwa [P.property.1])) := by
  simp [fixedIntegerHiveEquivGTPatternOfUniformInputGap]

theorem fixedIntegerHiveEquivGTPatternOfUniformInputGap_symm_apply
    (P : {P : GTPattern (n + 1) // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val})
    (v : Vertex (n + 1)) :
    ((fixedIntegerHiveEquivGTPatternOfUniformInputGap lam μ γ hGap).symm P).val v =
      gtCompletion lam P.val v.z (n + 1 - v.x) := by simp

theorem hiveCount_eq_card_gtPattern_of_uniform_input_gap :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPatternOfUniformInputGap lam μ γ hGap)

/-- In the stable range, the difference map gives an equivalence onto the full weight-`(γ - λ)`
Gelfand–Tsetlin fibre over `μ` with `gtCompletion` as inverse chart formula. -/
theorem exists_stable_gt_equiv :
    ∃ e : FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val},
      ∀ h v, h.val v = gtCompletion lam (e h).val v.z (n + 1 - v.x) :=
  ⟨fixedIntegerHiveEquivGTPatternOfUniformInputGap lam μ γ hGap,
    fun h v => apply_eq_gtCompletion_of_productBoundary h.property v⟩

end UniformInputGapEquiv

end UniformInputGap

/-! ### Low-rank equivalences and concrete fibre counts (`n ≤ 1`, `n = 2`, `n = 3`) -/

section LowRankAndChecks

/-- For `n ≤ 1`, there are no `j` with `j + 2 ≤ n`, so `IsGTCompletable` holds vacuously. -/
theorem isGTCompletable_of_le_one {n : ℕ} (hn : n ≤ 1) (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P := fun _ _ _ hj => absurd hj (by omega)

/-- For `n ≤ 1`, fixed-boundary integer hives correspond unconditionally to patterns of top row `μ`
and weight `γ - λ`. -/
def fixedIntegerHiveEquivGTPatternOfLeOne {n : ℕ} (hn : n ≤ 1) (lam μ γ : DominantWeight n) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans <| Equiv.subtypeEquivRight fun P =>
    ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
      fun ⟨ht, hw⟩ => ⟨ht, hw, isGTCompletable_of_le_one hn lam P⟩⟩

@[simp] theorem fixedIntegerHiveEquivGTPatternOfLeOne_apply_coe {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n) (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ h).val = h.val.toGTPattern := (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPatternOfLeOne_symm_apply_coe {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val}) :
    ((fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ).symm P).val =
      ofGTPattern lam P.val (isGTCompletable_of_le_one hn lam P.val) := (rfl)

/-- For `n ≤ 1`, `hiveCount (productBoundary lam μ γ)` is the cardinality of the full
weight-`(γ - λ)` Gelfand–Tsetlin fibre over `μ`. -/
theorem hiveCount_productBoundary_eq_card_gtPattern_of_le_one {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern n // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ)

/-- At `n = 1`, `hiveCount (productBoundary lam μ γ)` is `1` when `lam.1 0 + μ.1 0 = γ.1 0` and
`0` otherwise. -/
theorem hiveCount_one_productBoundary (lam μ γ : DominantWeight 1) :
    hiveCount (productBoundary lam μ γ) = if lam.val 0 + μ.val 0 = γ.val 0 then 1 else 0 := by
  rw [hiveCount_eq_card_gtPattern_of_uniform_input_gap lam μ γ (fun r => r.elim0)]
  split_ifs with hsum
  · have hμ : μ.val = γ.val - lam.val :=
      funext fun r => by rw [Subsingleton.elim r 0, Pi.sub_apply]; omega
    exact (Nat.card_congr (β := {P : GTPattern 1 // P.topRow = μ.val}) <| Equiv.subtypeEquivRight
      fun P => ⟨And.left, fun h => ⟨h, by rw [P.rowWeight_eq_topRow, h, hμ]⟩⟩).trans Nat.card_unique
  · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, ht, hw⟩ => hsum ?_⟩)
    have h0 := congrFun (P.rowWeight_eq_topRow.symm.trans hw) 0
    rw [ht, Pi.sub_apply] at h0; omega

/-- **Rank-`2` remaining rhombus criterion**: for any `lam : DominantWeight 2` and
`P : GTPattern 2`, `IsGTCompletable lam P` reduces to the single inequality
`lam.1 1 + P.topRow 0 ≤ lam.1 0 + P.rowWeight 0`. -/
theorem isGTCompletable_two_iff (lam : DominantWeight 2) (P : GTPattern 2) :
    IsGTCompletable lam P ↔ lam.val 1 + P.topRow 0 ≤ lam.val 0 + P.rowWeight 0 := by
  rw [isGTCompletable_iff_sum_sub_le]
  have := P.rowWeight_apply_zero; have : P.topRow 0 = P 0 2 := P.topRow_apply 0
  refine ⟨fun h => ?_, fun _ i j _ _ => ?_⟩
  · have h00 := h 0 0 le_rfl le_rfl
    simp only [Nat.reduceAdd, Finset.sum_range_one, Finset.sum_range_zero, add_zero, Fin.mk_zero,
      Fin.mk_one] at h00; omega
  · obtain ⟨rfl, rfl⟩ : j = 0 ∧ i = 0 := by omega
    simp only [Nat.reduceAdd, Finset.sum_range_one, Finset.sum_range_zero, add_zero, Fin.mk_zero,
      Fin.mk_one]; omega

/-- **Closed-form `GL₂` Clebsch–Gordan formula for `hiveCount`**: at rank `2`,
`hiveCount (productBoundary lam μ γ)` equals `1` when `|λ| + |μ| = |γ|` and
`max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ≤ lam.1 0 + μ.1 0`, and `0` otherwise. -/
theorem hiveCount_two_productBoundary (lam μ γ : DominantWeight 2) :
    hiveCount (productBoundary lam μ γ) =
      if (lam.val 0 + lam.val 1) + (μ.val 0 + μ.val 1) = γ.val 0 + γ.val 1 ∧
          max (lam.val 0 + μ.val 1) (lam.val 1 + μ.val 0) ≤ γ.val 0 ∧ γ.val 0 ≤ lam.val 0 + μ.val 0
        then 1 else 0 := by
  rw [hiveCount_productBoundary_eq_card_gtPattern]
  have heq :
      Nat.card
        {P : GTPattern 2 // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val ∧ IsGTCompletable lam
            P} =
      if lam.val 1 + μ.val 0 ≤ γ.val 0 then
        Nat.card {P : GTPattern 2 // P.topRow = μ.val ∧ P.rowWeight = γ.val - lam.val}
      else 0 := by
    split_ifs with hrem
    · exact Nat.card_congr (Equiv.subtypeEquivRight fun P =>
        ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
          fun ⟨ht, hw⟩ => ⟨ht, hw, (isGTCompletable_two_iff lam P).mpr (by
            have := congrFun ht 0; have hw0 := congrFun hw 0
            simp only [Pi.sub_apply] at hw0; omega)⟩⟩)
    · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨P, ht, hw, hc⟩ => hrem ?_⟩)
      have := (isGTCompletable_two_iff lam P).mp hc
      have := congrFun ht 0; have hw0 := congrFun hw 0
      simp only [Pi.sub_apply] at hw0; omega
  rw [heq, GTPattern.card_topRow_rowWeight_two μ.val (γ.val - lam.val)]
  simp only [Pi.sub_apply, max_le_iff]; split_ifs <;> omega

/-- Rank-`2` exclusion outside the stable range: although the weight-`(1, 1)` Gelfand–Tsetlin fibre
over `μ = (2, 0)` has cardinality `1` (`GTPattern.card_topRow_rowWeight_two_two_zero_one_one`), the
remaining rhombus inequality `λ₁ + μ₀ ≤ γ₀` (`2 ≤ 1`) fails at `λ = (0, 0)` and `γ = (1, 1)`. -/
theorem hiveCount_two_zero_sym_det :
    hiveCount (productBoundary (0 : DominantWeight 2) ⟨![2, 0], by decide⟩ ⟨![1, 1], by decide⟩) =
      0 := by
  rw [hiveCount_two_productBoundary]; simp only [DominantWeight.zero_apply, max_le_iff]; decide

/-- Rank-`2` identity tensor check `c^{(2, 0)}_{(0, 0), (2, 0)} = 1`. -/
theorem hiveCount_two_zero_sym_sym :
    hiveCount (productBoundary (0 : DominantWeight 2) ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩) =
      1 := by
  rw [hiveCount_two_productBoundary]; simp only [DominantWeight.zero_apply, max_le_iff]; decide

/-- Stable-range `GL₂` Clebsch–Gordan check `c^{(4, 0)}_{(2, 0), (2, 0)} = 1`. -/
theorem hiveCount_two_sym_sym_four_zero :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![4, 0], by decide⟩) = 1 := by
  rw [hiveCount_two_productBoundary]; decide

/-- Stable-range `GL₂` Clebsch–Gordan check `c^{(3, 1)}_{(2, 0), (2, 0)} = 1`. -/
theorem hiveCount_two_sym_sym_three_one :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![3, 1], by decide⟩) = 1 := by
  rw [hiveCount_two_productBoundary]; decide

/-- Stable-range `GL₂` Clebsch–Gordan check `c^{(2, 2)}_{(2, 0), (2, 0)} = 1`. -/
theorem hiveCount_two_sym_sym_two_two :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![2, 2], by decide⟩) = 1 := by
  rw [hiveCount_two_productBoundary]; decide

/-- **Signed rank-`2` check**: `λ = (1, 0)`, `μ = (0, -1)`, `γ = (0, 0)` has `hiveCount = 1`
(`V ⊗ V*` contains the trivial representation once), whereas truncating the negative entry of `μ`
to `0` gives `((1, 0), (0, 0), (0, 0))` with `hiveCount = 0`. -/
theorem hiveCount_two_signed_std_dual_triv :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![0, 0], by decide⟩) = 1 ∧
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, 0], by decide⟩ ⟨![0, 0], by decide⟩) = 0 := by
  refine ⟨?_, ?_⟩ <;> rw [hiveCount_two_productBoundary] <;> decide

/-- Rank-`3` exclusion: although the weight-`0` Gelfand–Tsetlin fibre over `μ = (1, 0, -1)` has two
patterns (`GTPattern.card_three_adjoint_rowWeight_zero`), neither satisfies
`IsGTCompletable 0 P`, so `hiveCount (productBoundary 0 ⟨![1, 0, -1], _⟩ 0) = 0`. -/
theorem hiveCount_three_zero_adjoint_zero :
    hiveCount (productBoundary (0 : DominantWeight 3) ⟨![1, 0, -1], by decide⟩ 0) = 0 := by
  rw [hiveCount_eq_zero_iff]; refine ⟨fun h => ?_⟩
  obtain ⟨P, hTop, hW, hComp⟩ := fixedIntegerHiveEquivGTPattern 0 ⟨![1, 0, -1], by decide⟩ 0 h
  have h00 := hComp 0 0 le_rfl (by decide)
  have h01 := hComp 0 1 (Nat.zero_le 1) le_rfl
  have h03 : P 0 3 = 1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 0
  have hP01 : P 0 1 = 0 := by
    simpa [P.rowWeight_apply_zero, DominantWeight.coe_zero] using congrFun hW 0
  simp only [gtCompletion_zero_dominantWeight, Nat.reduceAdd, Finset.sum_range_zero,
    Finset.sum_range_one, zero_add, h03, hP01] at h00 h01
  omega

/-- **Rank-`3` check**: `hiveCount = 1` for `((1, 0, 0), (1, 0, 0), (2, 0, 0))`. -/
theorem hiveCount_three_one_one_two :
    hiveCount
      (productBoundary ⟨![1, 0, 0], by decide⟩ ⟨![1, 0, 0], by decide⟩
        ⟨![2, 0, 0], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_eq_card_gtPattern]
  have heq :
      Nat.card {P : GTPattern 3 //
        P.topRow = ![1, 0, 0] ∧ P.rowWeight = ![2, 0, 0] - ![1, 0, 0] ∧
          IsGTCompletable ⟨![1, 0, 0], by decide⟩ P} =
      Nat.card {P : GTPattern 3 //
        P.topRow = ![1, 0, 0] ∧ P.rowWeight = ![2, 0, 0] - ![1, 0, 0]} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun P =>
      ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩, fun ⟨ht, hw⟩ => ⟨ht, hw, ?_⟩⟩)
    have h01 : P 0 1 = 1 := by simpa [P.rowWeight_apply_zero] using congrFun hw 0
    have h03 : P 0 3 = 1 := by simpa [P.topRow_apply] using congrFun ht 0
    have h13 : P 1 3 = 0 := by simpa [P.topRow_apply] using congrFun ht 1
    have h2 : P 0 2 + P 1 2 = 1 := by
      have hp := P.prefixSum_rowWeight (j := 2) (by decide)
      rw [hw] at hp
      simpa [TauCeti.prefixSum_def, Finset.sum_filter, Fin.sum_univ_three, P.rowSum_def,
        Finset.sum_range_succ] using hp.symm
    have hlo : 1 ≤ P 0 2 := h01 ▸ P.entry_le_entry_succ_row (by decide) (by decide)
    have hhi : P 0 2 ≤ 1 := h03 ▸ P.entry_le_entry_succ_row (by decide) (by decide)
    rw [isGTCompletable_iff_sum_sub_le]
    intro i j hij hj
    rcases (by omega : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp [Finset.sum_range_succ]
      omega
  rw [heq, GTPattern.card_topRow_rowWeight_three]
  decide

/-- **Rank-`3` check**: `hiveCount = 2` for `((2, 1, 0), (2, 1, 0), (3, 2, 1))`, corresponding to
the two middle-row fillings `P 0 2 = 1, P 1 2 = 1` and `P 0 2 = 2, P 1 2 = 0`. -/
theorem hiveCount_three_two_one_two_one_three_two_one :
    hiveCount
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
        ⟨![3, 2, 1], by decide⟩) = 2 := by
  rw [hiveCount_productBoundary_eq_card_gtPattern]
  have heq :
      Nat.card {P : GTPattern 3 //
        P.topRow = ![2, 1, 0] ∧ P.rowWeight = ![3, 2, 1] - ![2, 1, 0] ∧
          IsGTCompletable ⟨![2, 1, 0], by decide⟩ P} =
      Nat.card {P : GTPattern 3 //
        P.topRow = ![2, 1, 0] ∧ P.rowWeight = ![3, 2, 1] - ![2, 1, 0]} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun P =>
      ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩, fun ⟨ht, hw⟩ => ⟨ht, hw, ?_⟩⟩)
    have h01 : P 0 1 = 1 := by simpa [P.rowWeight_apply_zero] using congrFun hw 0
    have h03 : P 0 3 = 2 := by simpa [P.topRow_apply] using congrFun ht 0
    have h13 : P 1 3 = 1 := by simpa [P.topRow_apply] using congrFun ht 1
    have h2 : P 0 2 + P 1 2 = 2 := by
      have hp := P.prefixSum_rowWeight (j := 2) (by decide)
      rw [hw] at hp
      simpa [TauCeti.prefixSum_def, Finset.sum_filter, Fin.sum_univ_three, P.rowSum_def,
        Finset.sum_range_succ] using hp.symm
    have hlo : 1 ≤ P 0 2 := h01 ▸ P.entry_le_entry_succ_row (by decide) (by decide)
    have hhi : P 0 2 ≤ 2 := h03 ▸ P.entry_le_entry_succ_row (by decide) (by decide)
    rw [isGTCompletable_iff_sum_sub_le]
    intro i j hij hj
    rcases (by omega : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1)) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · simp [Finset.sum_range_succ]
      omega
  rw [heq, GTPattern.card_topRow_rowWeight_three]
  decide

end LowRankAndChecks

end TauCeti.Hive
