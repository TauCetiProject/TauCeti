/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Finset.PartialSum
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
coordinates by `TauCeti.Hive.rotate_rotate_ofChart_apply`) identifies cyclic boundary
`![lam.1, μ.1, ν.1]` with `productBoundary ν lam μ.dual`, yielding the quasi-hive equivalence with
top row `lam` and weight `μ.dual - ν` (`cyclicFixedIntegerHiveEquivGTPattern`). Under the uniform
input gap `P.topRow 0 - P.topRow (Fin.last n) ≤ λᵣ - λᵣ₊₁`, family (3) holds automatically
(`isGTCompletable_of_uniform_input_gap`, `gt_completion_of_uniform_input_gap`), giving a bijection
onto the full weight-`(γ - λ)` fibre over `μ` (`stableGTPatternEquiv`, `exists_stable_gt_equiv`).
Rank-`2` and rank-`3` checks witness strict exclusion outside this range.

## Main definitions

* `TauCeti.Hive.toGTPattern`, `TauCeti.Hive.toGTPatternAddMonoidHom`: directional difference map
  `IntegerHive n →+ GTPattern n`.
* `TauCeti.Hive.gtCompletion`, `TauCeti.Hive.IsGTCompletable`, `TauCeti.Hive.ofGTPattern`: chart
  completion, the remaining rhombus predicate, and hive reconstruction from `(lam, P)`.
* `TauCeti.Hive.integerHiveEquivGTPattern`, `TauCeti.Hive.fixedIntegerHiveEquivGTPattern`:
  global and fixed-boundary hive–pattern equivalences.
* `TauCeti.Hive.toCyclicGTPattern`, `TauCeti.Hive.toCyclicGTPatternAddMonoidHom`,
  `TauCeti.Hive.cyclicFixedIntegerHiveEquivGTPattern`: cyclic `(λ, μ, ν)` difference map and
  quasi-hive equivalence.
* `TauCeti.Hive.stableGTPatternEquiv`, `TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfLeOne`: full
  weight-fibre equivalences in the stable range and for `n ≤ 1`.

## Main results

* `TauCeti.Hive.topRow_toGTPattern`, `TauCeti.Hive.weight_toGTPattern`,
  `TauCeti.Hive.apply_eq_gtCompletion`: top row, weight, and chart inversion for `toGTPattern`.
* `TauCeti.Hive.isGTCompletable_iff_sum_sub_le`, `TauCeti.Hive.gt_reconstruction_iff`: explicit
  difference-sum form of `IsGTCompletable` and fixed-boundary reconstruction criterion.
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

/-! ### Product-chart boundary values -/

section ChartBoundaryValues

/-- Along `A → B` (`i = 0`), `h(0, j)` equals `TauCeti.prefixSum j (h.boundary 0)`. -/
theorem apply_ofChart_zero_left {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n 0 j (Nat.zero_le j) hj) = TauCeti.prefixSum j (h.boundary 0) := by
  rw [Vertex.ofChart_zero_left, h.apply_edgePoint_zero, TauCeti.prefixSum_def]

/-- Along `B → C` (`j = n`), `h(i, n)` equals
`(∑ r, h.boundary 0 r) + TauCeti.prefixSum i (h.boundary 1)`. -/
theorem apply_ofChart_right {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) {i : ℕ} (hi : i ≤ n) :
    h (Vertex.ofChart n i n hi le_rfl) =
      (∑ r : Fin n, h.boundary 0 r) + TauCeti.prefixSum i (h.boundary 1) := by
  rw [Vertex.ofChart_right, h.apply_edgePoint_one, TauCeti.prefixSum_def]

/-- Along `C → A` (`i = j`), `h(j, j) = TauCeti.prefixSum j (fun r => -h.boundary 2 r.rev)`. -/
theorem apply_ofChart_self {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]
    (h : Hive n R) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hj) = TauCeti.prefixSum j (fun r => -h.boundary 2 r.rev) := by
  rw [Vertex.ofChart_self, h.apply_edgePoint_two, Fin.val_mk, Finset.sum_filter,
    TauCeti.prefixSum_def, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine (Equiv.sum_comp Fin.revPerm
    (fun k : Fin n => -(if n - j ≤ k.val then h.boundary 2 k else 0))).symm.trans
    (Finset.sum_congr rfl fun r _ => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  by_cases hr : r.val < j
  · rw [ite_eq_left (by omega), ite_eq_left hr]
  · rw [ite_eq_right (by have := r.isLt; omega), ite_eq_right hr, neg_zero]

theorem apply_ofChart_zero_left_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n 0 j (Nat.zero_le j) hj) = TauCeti.prefixSum j lam.1 := by
  rw [h.apply_ofChart_zero_left hj, hb, productBoundary_zero]

theorem apply_ofChart_right_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {i : ℕ} (hi : i ≤ n) :
    h (Vertex.ofChart n i n hi le_rfl) = (∑ r : Fin n, lam.1 r) + TauCeti.prefixSum i μ.1 := by
  rw [h.apply_ofChart_right hi, hb, productBoundary_zero, productBoundary_one]

theorem apply_ofChart_self_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hj : j ≤ n) :
    h (Vertex.ofChart n j j le_rfl hj) = TauCeti.prefixSum j γ.1 := by
  rw [h.apply_ofChart_self hj]; exact congrArg (TauCeti.prefixSum j) (funext fun r => by simp [hb])

end ChartBoundaryValues

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
    rcases hout with hnj | hji
    · by_cases hij : i < j <;> simp [hij, Nat.not_le.mpr hnj]
    · simp [Nat.not_lt.mpr hji]
  interlacing' {i j} hij hj := by
    have hj1 : j + 1 ≤ n := hj
    have hij1 : i < j + 1 := by omega
    have hij2 : i + 1 < j + 1 := Nat.succ_lt_succ hij
    simp only [dite_eq_left hij, dite_eq_left hj.le, dite_eq_left hij1, dite_eq_left hj1,
      dite_eq_left hij2]
    have hleft := h.le_of_isRhombus (isRhombus_ofChart_diag_y hij hj)
    have hright := h.le_of_isRhombus (isRhombus_ofChart_diag_z hij hj)
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
      TauCeti.prefixSum j (h.boundaryWeight 2).dual.1 - TauCeti.prefixSum j (h.boundary 0) := by
  have hd : (fun r : Fin n => -h.boundary 2 r.rev) = (h.boundaryWeight 2).dual.1 :=
    funext fun r => by simp
  rw [GTPattern.rowSum_def, h.sum_range_toGTPattern le_rfl hj, h.apply_ofChart_self hj, hd,
    h.apply_ofChart_zero_left hj]

/-- The torus weight of `h.toGTPattern` is `(h.boundaryWeight 2).dual.1 - h.boundary 0`. -/
@[simp] theorem weight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.weight = (h.boundaryWeight 2).dual.1 - h.boundary 0 := by
  ext r; rw [GTPattern.weight_apply, h.rowSum_toGTPattern r.isLt, h.rowSum_toGTPattern r.isLt.le,
    TauCeti.prefixSum_succ r.isLt, TauCeti.prefixSum_succ r.isLt, Pi.sub_apply]; abel

theorem topRow_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.topRow = μ.1 := by
  rw [h.topRow_toGTPattern, hb, productBoundary_one]

theorem weight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.weight = γ.1 - lam.1 := by
  have hb2 : h.boundaryWeight 2 = γ.dual := Subtype.ext (by simp [coe_boundaryWeight, hb])
  rw [h.weight_toGTPattern, hb2, DominantWeight.dual_dual, hb, productBoundary_zero]

/-- Inverse chart formula `TauCeti.prefixSum j lam.1 + ∑ k ∈ Finset.range i, P k j` reconstructing
the hive value at `(i, j)` (`0 ≤ i ≤ j ≤ n`) from the side-`0` dominant weight `lam` and a
Gelfand–Tsetlin pattern `P`. -/
def gtCompletion (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) : ℤ :=
  TauCeti.prefixSum j lam.1 + ∑ k ∈ Finset.range i, P k j

theorem gtCompletion_def (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion lam P i j = TauCeti.prefixSum j lam.1 + ∑ k ∈ Finset.range i, P k j := (rfl)

@[simp] theorem gtCompletion_zero_left (lam : DominantWeight n) (P : GTPattern n) (j : ℕ) :
    gtCompletion lam P 0 j = TauCeti.prefixSum j lam.1 := by simp [gtCompletion_def]

@[simp] theorem gtCompletion_zero_right (lam : DominantWeight n) (i j : ℕ) :
    gtCompletion lam 0 i j = TauCeti.prefixSum j lam.1 := by
  simp [gtCompletion_def, GTPattern.zero_apply]

theorem gtCompletion_succ_left (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion lam P (i + 1) j = gtCompletion lam P i j + P i j := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_range_succ, add_assoc]

@[simp] theorem gtCompletion_add (lam₁ lam₂ : DominantWeight n) (P₁ P₂ : GTPattern n) (i j : ℕ) :
    gtCompletion (lam₁ + lam₂) (P₁ + P₂) i j =
      gtCompletion lam₁ P₁ i j + gtCompletion lam₂ P₂ i j := by
  have hlam : (lam₁ + lam₂).1 = lam₁.1 + lam₂.1 := rfl
  simp only [gtCompletion_def, hlam, TauCeti.prefixSum_add, GTPattern.add_apply,
    Finset.sum_add_distrib]; abel

@[simp] theorem gtCompletion_nsmul (k : ℕ) (lam : DominantWeight n) (P : GTPattern n) (i j : ℕ) :
    gtCompletion (k • lam) (k • P) i j = k • gtCompletion lam P i j := by
  have hlam : (k • lam).1 = k • lam.1 := rfl
  simp only [gtCompletion_def, hlam, TauCeti.prefixSum_smul, GTPattern.nsmul_apply,
    ← Finset.smul_sum, smul_add]

theorem gtCompletion_shift_left (lam : DominantWeight n) (m : ℤ) (P : GTPattern n) (i : ℕ)
    {j : ℕ} (hj : j ≤ n) :
    gtCompletion (lam.shift m) P i j = gtCompletion lam P i j + j * m := by
  rw [gtCompletion_def, gtCompletion_def, TauCeti.prefixSum_eq_sum_castLE hj,
    TauCeti.prefixSum_eq_sum_castLE hj]
  simp only [DominantWeight.shift_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]; ring

theorem gtCompletion_shift_right (lam : DominantWeight n) (P : GTPattern n) (m : ℤ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion lam (P.shift m) i j = gtCompletion lam P i j + i * m := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_congr rfl fun k hk =>
    P.shift_apply_of_lt_of_le m ((Finset.mem_range.mp hk).trans_le hij) hj,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_assoc]

theorem gtCompletion_shift (lam : DominantWeight n) (a : ℤ) (P : GTPattern n) (b : ℤ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion (lam.shift a) (P.shift b) i j = gtCompletion lam P i j + j * a + i * b := by
  rw [gtCompletion_shift_left lam a (P.shift b) i hj, gtCompletion_shift_right lam P b hij hj]; ring

theorem gtCompletion_const (lam : DominantWeight n) (m : ℤ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion lam (GTPattern.const n m) i j = TauCeti.prefixSum j lam.1 + i * m := by
  have hc : GTPattern.const n m = (0 : GTPattern n).shift m := by
    rw [GTPattern.shift_eq_add_const, zero_add]
  rw [hc, gtCompletion_shift_right lam 0 m hij hj, gtCompletion_zero_right]

theorem gtCompletion_self (lam : DominantWeight n) (P : GTPattern n) (j : ℕ) :
    gtCompletion lam P j j = TauCeti.prefixSum j lam.1 + P.rowSum j := by
  rw [gtCompletion_def, GTPattern.rowSum_def]

theorem gtCompletion_self_of_weight {lam : DominantWeight n} {P : GTPattern n} {g : Fin n → ℤ}
    (hw : P.weight = g - lam.1) {j : ℕ} (hj : j ≤ n) :
    gtCompletion lam P j j = TauCeti.prefixSum j g := by
  have hg : g = lam.1 + P.weight := by
    ext r; have hr := congrFun hw r; simp only [Pi.sub_apply, Pi.add_apply] at hr ⊢; linarith
  rw [gtCompletion_self, ← P.prefixSum_weight hj, hg, TauCeti.prefixSum_add]

theorem gtCompletion_right (lam : DominantWeight n) (P : GTPattern n) {i : ℕ} (hi : i ≤ n) :
    gtCompletion lam P i n = (∑ r : Fin n, lam.1 r) + TauCeti.prefixSum i P.topRow := by
  rw [gtCompletion_def, TauCeti.prefixSum_of_le le_rfl]; congr 1
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), TauCeti.prefixSum_succ hi, GTPattern.topRow_apply]

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
  have hp := h.apply_ofChart_eq_gtCompletion
    (i := p.z) (j := n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x)
  rwa [Vertex.ofChart_z_sub_x] at hp

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
        (lam.1 ⟨j, by omega⟩ - lam.1 ⟨j + 1, by omega⟩) +
          ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
  have : gtCompletion lam P i (j + 1) - gtCompletion lam P i j =
      lam.1 ⟨j, by omega⟩ + ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
    rw [gtCompletion_def, gtCompletion_def, TauCeti.prefixSum_succ (by omega),
      Finset.sum_sub_distrib]; abel
  have : gtCompletion lam P (i + 1) (j + 2) - gtCompletion lam P (i + 1) (j + 1) =
      lam.1 ⟨j + 1, by omega⟩ + ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)) := by
    rw [gtCompletion_def, gtCompletion_def, TauCeti.prefixSum_succ (by omega),
      Finset.sum_sub_distrib]; abel
  constructor <;> intro _ <;> linarith

/-- **Difference-sum characterization of `IsGTCompletable`**. -/
theorem isGTCompletable_iff_sum_sub_le (lam : DominantWeight n) (P : GTPattern n) :
    IsGTCompletable lam P ↔
      ∀ i j : ℕ, i ≤ j → (hj : j + 2 ≤ n) →
        (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
          (lam.1 ⟨j, by omega⟩ - lam.1 ⟨j + 1, by omega⟩) +
            ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
  ⟨fun h i j hij hj => (gtCompletion_add_gtCompletion_le_iff_sum_sub_le lam P hj).mp (h i j hij hj),
    fun h i j hij hj =>
      (gtCompletion_add_gtCompletion_le_iff_sum_sub_le lam P hj).mpr (h i j hij hj)⟩

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

@[simp] theorem isGTCompletable_shift_left (lam : DominantWeight n) (m : ℤ) (P : GTPattern n) :
    IsGTCompletable (lam.shift m) P ↔ IsGTCompletable lam P := by
  simp only [isGTCompletable_iff_sum_sub_le, DominantWeight.shift_apply, add_sub_add_right_eq_sub]

@[simp] theorem isGTCompletable_shift_right (lam : DominantWeight n) (P : GTPattern n) (m : ℤ) :
    IsGTCompletable lam (P.shift m) ↔ IsGTCompletable lam P := by
  simp only [isGTCompletable_iff_sum_sub_le]
  refine forall₄_congr fun i j _ hj => ?_
  have hs1 : (∑ k ∈ Finset.range (i + 1), ((P.shift m) k (j + 2) - (P.shift m) k (j + 1))) =
      ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)) :=
    Finset.sum_congr rfl fun k hk => by
      have := Finset.mem_range.mp hk
      rw [P.shift_apply_of_lt_of_le m (by omega) hj,
        P.shift_apply_of_lt_of_le m (by omega) (by omega), add_sub_add_right_eq_sub]
  have hs2 : (∑ k ∈ Finset.range i, ((P.shift m) k (j + 1) - (P.shift m) k j)) =
      ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
    Finset.sum_congr rfl fun k hk => by
      have := Finset.mem_range.mp hk
      rw [P.shift_apply_of_lt_of_le m (by omega) (by omega),
        P.shift_apply_of_lt_of_le m (by omega) (by omega), add_sub_add_right_eq_sub]
  rw [hs1, hs2]

@[simp] theorem isGTCompletable_const (lam : DominantWeight n) (m : ℤ) :
    IsGTCompletable lam (GTPattern.const n m) := by
  have hc : GTPattern.const n m = (0 : GTPattern n).shift m := by
    rw [GTPattern.shift_eq_add_const, zero_add]
  rw [hc, isGTCompletable_shift_right]; exact isGTCompletable_zero_right lam

theorem isGTCompletable_toGTPattern (h : IntegerHive n) :
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
    ofGTPattern 0 0 h = 0 := by ext p; simp [TauCeti.prefixSum_def]

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
  ext p; have := p.sum_eq
  have hsub : ((n - p.x : ℕ) : ℤ) = (p.y : ℤ) + p.z := by omega
  rw [ofGTPattern_apply, gtCompletion_const _ b (by omega) (Nat.sub_le n p.x),
    TauCeti.prefixSum_eq_sum_castLE (Nat.sub_le n p.x)]
  simp only [DominantWeight.shift_apply, DominantWeight.zero_apply, zero_add, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsub, affine_apply]; ring

@[simp] theorem toGTPattern_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) : (ofGTPattern lam P hP).toGTPattern = P := by
  ext i j; by_cases h : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le _ h.1 h.2, ofGTPattern_ofChart, ofGTPattern_ofChart,
       gtCompletion_succ_left, add_sub_cancel_left]
  · exact GTPattern.entry_eq_zero _ (by omega) |>.trans (P.entry_eq_zero (by omega)).symm

@[simp] theorem boundary_zero_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) : (ofGTPattern lam P hP).boundary 0 = lam.1 := by
  ext r
  have hs : Vertex.edgePoint n 0 r.succ =
      Vertex.ofChart n 0 (r.val + 1) (Nat.zero_le _) r.isLt := by ext <;> simp
  have hc : Vertex.edgePoint n 0 r.castSucc =
      Vertex.ofChart n 0 r.val (Nat.zero_le _) r.isLt.le := by ext <;> simp
  rw [boundary_apply, hs, hc, ofGTPattern_ofChart, ofGTPattern_ofChart,
    gtCompletion_zero_left, gtCompletion_zero_left, TauCeti.prefixSum_succ r.isLt,
    add_sub_cancel_left]

@[simp] theorem boundaryWeight_zero_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundaryWeight 0 = lam := Subtype.ext (by simp)

@[simp] theorem boundary_one_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) : (ofGTPattern lam P hP).boundary 1 = P.topRow := by
  rw [← topRow_toGTPattern, toGTPattern_ofGTPattern]

@[simp] theorem boundaryWeight_one_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundaryWeight 1 = P.topWeight := Subtype.ext (by simp)

@[simp] theorem dual_boundaryWeight_two_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) :
    ((ofGTPattern lam P hP).boundaryWeight 2).dual.1 = lam.1 + P.weight := by
  have hw := weight_toGTPattern (ofGTPattern lam P hP)
  rw [toGTPattern_ofGTPattern, boundary_zero_ofGTPattern] at hw
  ext r; have hr := congrFun hw r; simp only [Pi.sub_apply, Pi.add_apply] at hr ⊢; linarith

/-- Whenever `P` is hive-completable over `lam`, `lam.1 + P.weight` is automatically antitone
(dominant), as the dual of side `2` of `ofGTPattern lam P hP`. -/
theorem antitone_add_weight_of_isGTCompletable {lam : DominantWeight n} {P : GTPattern n}
    (hP : IsGTCompletable lam P) : Antitone (lam.1 + P.weight) :=
  dual_boundaryWeight_two_ofGTPattern lam P hP ▸ ((ofGTPattern lam P hP).boundaryWeight 2).dual.2

@[simp] theorem boundary_two_ofGTPattern (lam : DominantWeight n) (P : GTPattern n)
    (hP : IsGTCompletable lam P) (r : Fin n) :
    (ofGTPattern lam P hP).boundary 2 r = -(lam.1 r.rev + P.weight r.rev) := by
  have hd := congrFun (dual_boundaryWeight_two_ofGTPattern lam P hP) r.rev
  simp only [DominantWeight.dual_apply, coe_boundaryWeight, Fin.rev_rev, Pi.add_apply] at hd
  linarith

theorem boundary_ofGTPattern_eq_productBoundary {lam μ γ : DominantWeight n} {P : GTPattern n}
    (hTop : P.topRow = μ.1) (hWeight : P.weight = γ.1 - lam.1) (hP : IsGTCompletable lam P) :
    (ofGTPattern lam P hP).boundary = productBoundary lam μ γ := by
  ext s r; fin_cases s
  · simp
  · rw [Fin.mk_one, boundary_one_ofGTPattern, hTop, productBoundary_one]
  · simp [hWeight]

@[simp] theorem ofGTPattern_toGTPattern (h : IntegerHive n) :
    ofGTPattern (h.boundaryWeight 0) h.toGTPattern h.isGTCompletable_toGTPattern = h := by
  ext p; exact (h.apply_eq_gtCompletion p).symm

/-- Global equivalence between normalized integer hives of size `n` and pairs `(lam, P)` of a
dominant weight and a hive-completable Gelfand–Tsetlin pattern. -/
def integerHiveEquivGTPattern (n : ℕ) :
    IntegerHive n ≃ {lp : DominantWeight n × GTPattern n // IsGTCompletable lp.1 lp.2} where
  toFun h := ⟨(h.boundaryWeight 0, h.toGTPattern), h.isGTCompletable_toGTPattern⟩
  invFun lp := ofGTPattern lp.1.1 lp.1.2 lp.2
  left_inv h := h.ofGTPattern_toGTPattern
  right_inv lp := Subtype.ext <| Prod.ext (boundaryWeight_zero_ofGTPattern lp.1.1 lp.1.2 lp.2)
    (toGTPattern_ofGTPattern lp.1.1 lp.1.2 lp.2)

@[simp] theorem integerHiveEquivGTPattern_apply_coe (h : IntegerHive n) :
    (integerHiveEquivGTPattern n h).1 = (h.boundaryWeight 0, h.toGTPattern) := (rfl)

@[simp] theorem integerHiveEquivGTPattern_symm_apply
    (lp : {lp : DominantWeight n × GTPattern n // IsGTCompletable lp.1 lp.2}) :
    (integerHiveEquivGTPattern n).symm lp = ofGTPattern lp.1.1 lp.1.2 lp.2 := (rfl)

/-- **Fixed-boundary hive–pattern equivalence**: integer hives with boundary
`productBoundary lam μ γ` correspond bijectively to Gelfand–Tsetlin patterns `P` with top row `μ`,
weight `γ - λ`, and `IsGTCompletable lam P`. -/
def fixedIntegerHiveEquivGTPattern (lam μ γ : DominantWeight n) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P} where
  toFun h := ⟨h.1.toGTPattern, topRow_toGTPattern_of_productBoundary h.2,
    weight_toGTPattern_of_productBoundary h.2, by
      have hb0 : h.1.boundaryWeight 0 = lam := Subtype.ext (by simp [coe_boundaryWeight, h.2])
      exact hb0.subst (motive := fun l => IsGTCompletable l h.1.toGTPattern)
        h.1.isGTCompletable_toGTPattern⟩
  invFun P := ⟨ofGTPattern lam P.1 P.2.2.2,
    boundary_ofGTPattern_eq_productBoundary P.2.1 P.2.2.1 P.2.2.2⟩
  left_inv h := Subtype.ext <| ext fun p =>
    (apply_eq_gtCompletion_of_productBoundary h.2 p).symm
  right_inv P := Subtype.ext (toGTPattern_ofGTPattern lam P.1 P.2.2.2)

@[simp] theorem fixedIntegerHiveEquivGTPattern_apply_coe (lam μ γ : DominantWeight n)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P}) :
    ((fixedIntegerHiveEquivGTPattern lam μ γ).symm P).1 = ofGTPattern lam P.1 P.2.2.2 := (rfl)

theorem hiveCount_productBoundary_eq_card_gtPattern (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card
        {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P} := by
  rw [← natCard_fixedIntegerHive]; exact Nat.card_congr (fixedIntegerHiveEquivGTPattern lam μ γ)

/-- **Gelfand–Tsetlin reconstruction criterion**: a pattern `P` with top row `μ` and weight
`γ - λ` is the difference pattern of a hive with boundary `productBoundary lam μ γ` (realized via
`gtCompletion lam P`) if and only if the remaining rhombus family holds on `gtCompletion lam P`. -/
theorem gt_reconstruction_iff (lam μ γ : DominantWeight n) (P : GTPattern n)
    (hTop : P.topRow = μ.1) (hWeight : P.weight = γ.1 - lam.1) :
    (∃ h : FixedIntegerHive (productBoundary lam μ γ),
      ∀ v : Vertex n, h.1 v = gtCompletion lam P v.z (n - v.x)) ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
          gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) := by
  refine ⟨fun ⟨h, hv⟩ i j hij hj => ?_, fun hrem =>
    ⟨(fixedIntegerHiveEquivGTPattern lam μ γ).symm ⟨P, hTop, hWeight, hrem⟩, fun _ => rfl⟩⟩
  have hr := h.1.le_of_isRhombus (isRhombus_ofChart_diag_x hij hj)
  have hchart (i' j' : ℕ) (hi' : i' ≤ j') (hj' : j' ≤ n) :
      h.1 (Vertex.ofChart n i' j' hi' hj') = gtCompletion lam P i' j' := by
    rw [hv, Vertex.ofChart_z, Vertex.ofChart_x, Nat.sub_sub_self hj']
  rwa [hchart i j hij (by omega), hchart (i + 1) (j + 2) (by omega) hj,
    hchart i (j + 1) (by omega) (by omega),
    hchart (i + 1) (j + 1) (Nat.succ_le_succ hij) (by omega)] at hr

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
    h.rotate_rotate_ofChart_apply hij hj, h.rotate_rotate_ofChart_apply hij.le hj]; abel

@[simp] theorem toCyclicGTPattern_rotate (h : IntegerHive n) :
    h.rotate.toCyclicGTPattern = h.toGTPattern := by
  rw [toCyclicGTPattern_def, rotate_rotate_rotate]

@[simp] theorem toCyclicGTPattern_zero : (0 : IntegerHive n).toCyclicGTPattern = 0 := by
  ext i j; by_cases h : i < j ∧ j ≤ n
  · simp [toCyclicGTPattern_apply_of_lt_of_le _ h.1 h.2, GTPattern.zero_apply]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.zero_apply]

@[simp] theorem toCyclicGTPattern_add (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toCyclicGTPattern = h₁.toCyclicGTPattern + h₂.toCyclicGTPattern := by
  ext i j; by_cases h : i < j ∧ j ≤ n
  · simp only [toCyclicGTPattern_apply_of_lt_of_le _ h.1 h.2, add_apply, GTPattern.add_apply]; abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.add_apply,
      GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega), add_zero]

@[simp] theorem toCyclicGTPattern_nsmul (k : ℕ) (h : IntegerHive n) :
    (k • h).toCyclicGTPattern = k • h.toCyclicGTPattern := by
  ext i j; by_cases hij : i < j ∧ j ≤ n
  · simp only [toCyclicGTPattern_apply_of_lt_of_le _ hij.1 hij.2, nsmul_apply,
      GTPattern.nsmul_apply, nsmul_eq_mul]; ring
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.nsmul_apply,
      GTPattern.entry_eq_zero _ (by omega), smul_zero]

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

@[simp] theorem weight_toCyclicGTPattern (h : IntegerHive n) :
    h.toCyclicGTPattern.weight = (h.boundaryWeight 1).dual.1 - h.boundary 2 := by
  simp [toCyclicGTPattern_def, boundary_rotate, boundaryWeight_rotate]

/-- **Cyclic quasi-hive equivalence (Henriques–Kamnitzer, Theorem 7.4)**: integer hives with
clockwise cyclic boundary `![lam.1, μ.1, ν.1]` correspond bijectively to Gelfand–Tsetlin patterns
with top row `lam.1`, torus weight `μ.dual.1 - ν.1`, and `IsGTCompletable ν P`. -/
def cyclicFixedIntegerHiveEquivGTPattern (lam μ ν : DominantWeight n) :
    FixedIntegerHive ![lam.1, μ.1, ν.1] ≃
      {P : GTPattern n // P.topRow = lam.1 ∧ P.weight = μ.dual.1 - ν.1 ∧ IsGTCompletable ν P} :=
  (rotateRotateEquiv lam μ ν).trans (fixedIntegerHiveEquivGTPattern ν lam μ.dual)

@[simp] theorem cyclicFixedIntegerHiveEquivGTPattern_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive ![lam.1, μ.1, ν.1]) :
    (cyclicFixedIntegerHiveEquivGTPattern lam μ ν h).1 = h.1.toCyclicGTPattern := by
  simp [cyclicFixedIntegerHiveEquivGTPattern, toCyclicGTPattern_def]

@[simp] theorem cyclicFixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ ν : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = lam.1 ∧ P.weight = μ.dual.1 - ν.1 ∧ IsGTCompletable ν P}) :
    ((cyclicFixedIntegerHiveEquivGTPattern lam μ ν).symm P).1 =
      (ofGTPattern ν P.1 P.2.2.2).rotate := by simp [cyclicFixedIntegerHiveEquivGTPattern]

end CyclicOrientation

/-! ### Uniform input gap and stable Gelfand–Tsetlin fibre equivalence -/

section UniformInputGap

/-- **Uniform input gap**: when `P.topRow 0 - P.topRow (Fin.last n)` is at most
`lam.1 r.castSucc - lam.1 r.succ` for every `r : Fin n`, `P` is automatically hive-completable
over `lam`. -/
theorem isGTCompletable_of_uniform_input_gap {n : ℕ} {lam : DominantWeight (n + 1)}
    {P : GTPattern (n + 1)}
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
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
    (P : GTPattern (n + 1)) (hTop : P.topRow = μ.1)
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion lam P i j + gtCompletion lam P (i + 1) (j + 2) ≤
        gtCompletion lam P i (j + 1) + gtCompletion lam P (i + 1) (j + 1) :=
  isGTCompletable_of_uniform_input_gap (hTop ▸ hGap)

/-- Under the uniform input gap on `lam`, fixed-boundary integer hives with boundary
`productBoundary lam μ γ` are equivalent to the entire weight-`(γ - λ)` Gelfand–Tsetlin fibre over
`μ`. -/
def stableGTPatternEquiv {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans <| Equiv.subtypeEquivRight fun _ =>
    ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
      fun ⟨ht, hw⟩ => ⟨ht, hw, isGTCompletable_of_uniform_input_gap (by rwa [ht])⟩⟩

@[simp] theorem stableGTPatternEquiv_apply_coe {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (stableGTPatternEquiv lam μ γ hGap h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem stableGTPatternEquiv_symm_apply_coe {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}) :
    ((stableGTPatternEquiv lam μ γ hGap).symm P).1 =
      ofGTPattern lam P.1 (isGTCompletable_of_uniform_input_gap (by rwa [P.2.1])) := by
  simp [stableGTPatternEquiv]

theorem stableGTPatternEquiv_symm_apply {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}) (v : Vertex (n + 1)) :
    ((stableGTPatternEquiv lam μ γ hGap).symm P).1 v =
      gtCompletion lam P.1 v.z (n + 1 - v.x) := by simp

theorem hiveCount_eq_card_gtPattern_of_uniform_input_gap {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]; exact Nat.card_congr (stableGTPatternEquiv lam μ γ hGap)

/-- In the stable range, the difference map gives an equivalence onto the full weight-`(γ - λ)`
Gelfand–Tsetlin fibre over `μ` with `gtCompletion` as inverse chart formula. -/
theorem exists_stable_gt_equiv {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    ∃ e : FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1},
      ∀ h v, h.1 v = gtCompletion lam (e h).1 v.z (n + 1 - v.x) :=
  ⟨stableGTPatternEquiv lam μ γ hGap, fun h v => apply_eq_gtCompletion_of_productBoundary h.2 v⟩

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
      {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans <| Equiv.subtypeEquivRight fun P =>
    ⟨fun ⟨ht, hw, _⟩ => ⟨ht, hw⟩,
      fun ⟨ht, hw⟩ => ⟨ht, hw, isGTCompletable_of_le_one hn lam P⟩⟩

@[simp] theorem fixedIntegerHiveEquivGTPatternOfLeOne_apply_coe {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n) (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp] theorem fixedIntegerHiveEquivGTPatternOfLeOne_symm_apply_coe {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}) :
    ((fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ).symm P).1 =
      ofGTPattern lam P.1 (isGTCompletable_of_le_one hn lam P.1) := (rfl)

/-- At `n = 1`, `hiveCount (productBoundary lam μ γ)` is `1` when `lam.1 0 + μ.1 0 = γ.1 0` and
`0` otherwise. -/
theorem hiveCount_one_productBoundary (lam μ γ : DominantWeight 1) :
    hiveCount (productBoundary lam μ γ) = if lam.1 0 + μ.1 0 = γ.1 0 then 1 else 0 := by
  rw [hiveCount_eq_card_gtPattern_of_uniform_input_gap lam μ γ (fun r => r.elim0)]
  let P₀ : {P : GTPattern 1 // P.topRow = μ.1} := default
  have hw₀ : P₀.1.weight 0 = μ.1 0 := by
    simpa only [Fin.sum_univ_one, P₀.2] using P₀.1.sum_weight
  have : Subsingleton {P : GTPattern 1 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
    ⟨fun P Q => Subtype.ext <| Subtype.mk.inj <|
      Subsingleton.elim (⟨P.1, P.2.1⟩ : {R : GTPattern 1 // R.topRow = μ.1}) ⟨Q.1, Q.2.1⟩⟩
  split_ifs with hsum
  · have : Unique {P : GTPattern 1 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
      uniqueOfSubsingleton ⟨P₀.1, P₀.2, funext fun r => by
        rw [Subsingleton.elim r 0, hw₀, Pi.sub_apply]; omega⟩
    exact Nat.card_unique
  · refine Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨Q, hQtop, hQw⟩ => hsum ?_⟩)
    have hQeq : Q = P₀.1 := congrArg Subtype.val
      (Subsingleton.elim (⟨Q, hQtop⟩ : {P : GTPattern 1 // P.topRow = μ.1}) P₀)
    have hr := congrFun hQw 0; rw [hQeq, hw₀, Pi.sub_apply] at hr; omega

/-- **Rank-`2` remaining rhombus criterion**: for any `lam : DominantWeight 2` and
`P : GTPattern 2`, `IsGTCompletable lam P` reduces to the single inequality
`lam.1 1 + P.topRow 0 ≤ lam.1 0 + P.weight 0`. -/
theorem isGTCompletable_two_iff (lam : DominantWeight 2) (P : GTPattern 2) :
    IsGTCompletable lam P ↔ lam.1 1 + P.topRow 0 ≤ lam.1 0 + P.weight 0 := by
  rw [isGTCompletable_iff_sum_sub_le]
  have : P.weight 0 = P 0 1 := by simp [GTPattern.weight_apply, GTPattern.rowSum_def]
  have : P.topRow 0 = P 0 2 := P.topRow_apply 0
  refine ⟨fun h => ?_, fun _ i j _ _ => ?_⟩
  · have h00 := h 0 0 le_rfl le_rfl
    simp only [Nat.reduceAdd, Finset.sum_range_one, Finset.sum_range_zero, add_zero, Fin.mk_zero,
      Fin.mk_one] at h00; omega
  · obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    simp only [Nat.reduceAdd, Finset.sum_range_one, Finset.sum_range_zero, add_zero, Fin.mk_zero,
      Fin.mk_one]; omega

/-- **Closed-form `GL₂` Clebsch–Gordan formula for `hiveCount`**: at rank `2`,
`hiveCount (productBoundary lam μ γ)` equals `1` when `|λ| + |μ| = |γ|` and
`max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ≤ lam.1 0 + μ.1 0`, and `0` otherwise. -/
theorem hiveCount_two_productBoundary (lam μ γ : DominantWeight 2) :
    hiveCount (productBoundary lam μ γ) =
      if (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
          max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧ γ.1 0 ≤ lam.1 0 + μ.1 0
        then 1 else 0 := by
  rw [hiveCount_productBoundary_eq_card_gtPattern]
  have heq :
      Nat.card
        {P : GTPattern 2 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧ IsGTCompletable lam P} =
      if lam.1 1 + μ.1 0 ≤ γ.1 0 then
        Nat.card {P : GTPattern 2 // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}
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
  rw [heq, GTPattern.card_gtPattern_two_topRow_weight μ.1 (γ.1 - lam.1)]
  simp only [Pi.sub_apply, max_le_iff]; split_ifs <;> omega

/-- Rank-`2` exclusion outside the stable range: although the weight-`(1, 1)` Gelfand–Tsetlin fibre
over `μ = (2, 0)` has cardinality `1` (`GTPattern.card_gtPattern_two_two_zero_one_one`), the
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

/-- Rank-`3` exclusion: although the weight-`0` Gelfand–Tsetlin fibre over `μ = (1, 0, -1)` has two
patterns (`GTPattern.card_gtPattern_three_adjoint_weight_zero`), neither satisfies
`IsGTCompletable 0 P`, so `hiveCount (productBoundary 0 ⟨![1, 0, -1], _⟩ 0) = 0`. -/
theorem hiveCount_three_zero_adjoint_zero :
    hiveCount (productBoundary (0 : DominantWeight 3) ⟨![1, 0, -1], by decide⟩ 0) = 0 := by
  rw [hiveCount_eq_zero_iff]; refine ⟨fun h => ?_⟩
  obtain ⟨P, hTop, hW, hComp⟩ := fixedIntegerHiveEquivGTPattern 0 ⟨![1, 0, -1], by decide⟩ 0 h
  have hzero : (0 : DominantWeight 3).1 = 0 := by ext; simp
  have h00 := hComp 0 0 le_rfl (by decide)
  have h01 := hComp 0 1 (Nat.zero_le 1) le_rfl
  have h03 : P 0 3 = 1 := by simpa [GTPattern.topRow_apply] using congrFun hTop 0
  have hP01 : P 0 1 = 0 := by
    simpa [GTPattern.weight_apply, GTPattern.rowSum_def, hzero] using congrFun hW 0
  simp only [gtCompletion_def, hzero, TauCeti.prefixSum_def, Pi.zero_apply, Finset.sum_const_zero,
    zero_add, Nat.reduceAdd, Finset.sum_range_zero, Finset.sum_range_one, h03, hP01] at h00 h01
  omega

end LowRankAndChecks

end TauCeti.Hive
