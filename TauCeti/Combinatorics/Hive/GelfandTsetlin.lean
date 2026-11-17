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

/-!
# The hive-to-Gelfand–Tsetlin difference map and its reconstruction

In the product chart `(i, j) ↦ (n - j, j - i, i)` (`0 ≤ i ≤ j ≤ n`,
`TauCeti.Hive.Vertex.productChart`) on `TauCeti.Hive.Vertex n`, a normalized hive `h` with
clockwise boundary `productBoundary lam μ γ = (λ, μ, γ*)` satisfies

* `h(0, j) = prefixSum j λ` along the lower-left side `A → B`,
* `h(i, n) = |λ| + prefixSum i μ` along the top-right side `B → C`, and
* `h(j, j) = prefixSum j γ` along the diagonal `C → A`, with `h(0, 0) = 0`.

Taking directional forward differences along `i` defines `TauCeti.Hive.toGTPattern h : GTPattern n`
with entries `P i j = h(i + 1, j) - h(i, j)` for `0 ≤ i < j ≤ n` and `0` off the triangle. Every
unit rhombus in `Δₙ` belongs to one of three product-chart families
(`TauCeti.Hive.isRhombusConcave_iff_productChart`):

1. `h(i + 1, j) + h(i, j + 1) ≤ h(i, j) + h(i + 1, j + 1)` (`0 ≤ i < j < n`), which is
   `P i j ≤ P i (j + 1)`;
2. `h(i, j) + h(i + 2, j + 1) ≤ h(i + 1, j) + h(i + 1, j + 1)` (`0 ≤ i < j < n`), which is
   `P (i + 1) (j + 1) ≤ P i j`;
3. `h(i, j) + h(i + 1, j + 2) ≤ h(i, j + 1) + h(i + 1, j + 1)` (`0 ≤ i ≤ j`, `j + 2 ≤ n`).

Summing `P` back from the side `A → B` yields the inverse chart completion
`TauCeti.Hive.gtCompletion l P i j = prefixSum j l + ∑ k ∈ Finset.range i, P k j`. For a pattern
`P` with `P.topRow = μ` and `P.rowWeight = γ - λ`, the first two rhombus families hold
automatically by interlacing, while the remaining family becomes
`∑_{k ≤ i} (P k (j + 2) - P k (j + 1)) ≤ λ_j - λ_{j + 1} + ∑_{k < i} (P k (j + 1) - P k j)`
(`TauCeti.Hive.IsProductHiveFeasible`). This gives both the reconstruction theorem
`TauCeti.Hive.gt_reconstruction_iff` and the fibre equivalence
`TauCeti.Hive.fixedIntegerHiveEquivGTPattern`, together with its cyclic `(λ, μ, ν)` counterpart
`TauCeti.Hive.cyclicFixedIntegerHiveEquivGTPattern` (Henriques–Kamnitzer, Theorem 7.4, via
`TauCeti.Hive.fixedIntegerHiveRotateTwiceEquiv`).

In rank `n + 1` (`lam μ γ : DominantWeight (n + 1)`), when `λ` satisfies the uniform input gap
`μ_0 - μ_n ≤ λ_r - λ_{r + 1}` for every `r : Fin n`, the remaining rhombus family holds
automatically for every pattern over `μ` (`TauCeti.Hive.gt_completion_of_uniform_input_gap`), so
`toGTPattern` and `gtCompletion` furnish an equivalence onto the entire weight-`(γ - λ)`
Gelfand–Tsetlin fibre over `μ` (`TauCeti.Hive.stableGTPatternEquiv`,
`TauCeti.Hive.exists_stable_gt_equiv`).

## Main definitions

* `TauCeti.Hive.toGTPattern`, `TauCeti.Hive.toGTPatternAddMonoidHom`, `TauCeti.Hive.gtCompletion`,
  `TauCeti.Hive.gtCompletionVertex`: the hive-to-pattern difference map and its inverse chart
  completion.
* `TauCeti.Hive.IsProductHiveFeasible`: the remaining product-chart rhombus inequalities on a
  pattern.
* `TauCeti.Hive.fixedIntegerHiveEquivGTPattern`,
  `TauCeti.Hive.cyclicFixedIntegerHiveEquivGTPattern`: equivalences between fixed-boundary integer
  hives and feasible Gelfand–Tsetlin weight fibres in product and cyclic orientations.
* `TauCeti.Hive.stableGTPatternEquiv`, `TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfLeOne`:
  unconditional weight-fibre equivalences under the uniform input gap and for `n ≤ 1`.

## Main results

* `TauCeti.Hive.apply_eq_gtCompletion_toGTPattern`,
  `TauCeti.Hive.boundaryLinear_gtCompletionVertex`, `TauCeti.Hive.gt_reconstruction_iff`.
* `TauCeti.Hive.gt_completion_of_uniform_input_gap`, `TauCeti.Hive.exists_stable_gt_equiv`.
* `TauCeti.Hive.isProductHiveFeasible_two_iff`, `TauCeti.Hive.hiveCount_productBoundary_two`:
  rank-`2` Clebsch–Gordan characterization and low-rank checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 211–249, Theorem 7.4.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### Directional difference map `Hive.toGTPattern` and inverse `Hive.gtCompletion` -/

section DifferenceAndCompletion

variable {n : ℕ}

/-- The **hive-to-Gelfand–Tsetlin directional difference map**: on informative cells `0 ≤ i < j ≤ n`
its `(i, j)` entry is `h(i + 1, j) - h(i, j)` in the product chart, and off the triangle it
vanishes. -/
def toGTPattern (h : IntegerHive n) : GTPattern n where
  entry i j :=
    if hij : i < j then
      if hjn : j ≤ n then
        h (Vertex.productChart n (i + 1) j hij hjn) -
          h (Vertex.productChart n i j hij.le hjn)
      else 0
    else 0
  zeros' {i j} h0 := by
    rcases h0 with hlt | hle
    · simp [not_le.mpr hlt]
    · simp [not_lt.mpr hle]
  interlacing' {i j} hij hjn := by
    have hj1 : j + 1 ≤ n := hjn
    rw [dite_eq_left hij, dite_eq_left hjn.le, dite_eq_left (by omega : i < j + 1),
      dite_eq_left hj1, dite_eq_left (Nat.succ_lt_succ hij), dite_eq_left hj1]
    have h1 := h.le_of_isRhombus (isRhombus_productChart_gt_left hij hjn)
    have h2 := h.le_of_isRhombus (isRhombus_productChart_gt_right hij hjn)
    exact ⟨by linarith, by linarith⟩

@[grind =] theorem toGTPattern_apply (h : IntegerHive n) (i j : ℕ) :
    h.toGTPattern i j =
      if hij : i < j then
        if hjn : j ≤ n then
          h (Vertex.productChart n (i + 1) j hij hjn) - h (Vertex.productChart n i j hij.le hjn)
        else 0
      else 0 := (rfl)

@[simp, grind =] theorem toGTPattern_apply_of_lt_of_le (h : IntegerHive n) {i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) :
    h.toGTPattern i j =
      h (Vertex.productChart n (i + 1) j hij hjn) - h (Vertex.productChart n i j hij.le hjn) := by
  rw [toGTPattern_apply, dite_eq_left hij, dite_eq_left hjn]

@[simp, grind =] theorem toGTPattern_zero : (0 : IntegerHive n).toGTPattern = 0 := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le _ h.1 h.2]; simp
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.zero_apply]

@[simp, grind =] theorem toGTPattern_add (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toGTPattern = h₁.toGTPattern + h₂.toGTPattern := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · rw [GTPattern.add_apply, toGTPattern_apply_of_lt_of_le _ h.1 h.2,
      toGTPattern_apply_of_lt_of_le _ h.1 h.2, toGTPattern_apply_of_lt_of_le _ h.1 h.2,
      add_apply, add_apply]
    abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.add_apply,
      GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega), add_zero]

/-- `TauCeti.Hive.toGTPattern` bundled as an additive monoid homomorphism. -/
def toGTPatternAddMonoidHom (n : ℕ) : IntegerHive n →+ GTPattern n where
  toFun := toGTPattern
  map_zero' := toGTPattern_zero
  map_add' := toGTPattern_add

@[simp, grind =] theorem toGTPatternAddMonoidHom_apply (h : IntegerHive n) :
    toGTPatternAddMonoidHom n h = h.toGTPattern := (rfl)

@[simp, grind =] theorem toGTPattern_nsmul (k : ℕ) (h : IntegerHive n) :
    (k • h).toGTPattern = k • h.toGTPattern :=
  map_nsmul (toGTPatternAddMonoidHom n) k h

@[simp, grind =] theorem toGTPattern_affine (β γ : ℤ) :
    (affine n β γ).toGTPattern = GTPattern.const n (γ - β) := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le _ h.1 h.2, GTPattern.const_apply_of_lt_of_le _ h.1 h.2]
    have hsub : j - i = (j - (i + 1)) + 1 := by omega
    simp only [affine_apply, Vertex.productChart_y, Vertex.productChart_z, hsub, add_nsmul,
      one_nsmul]
    abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega)]

/-- Summing the first `i` entries of row `j` of `h.toGTPattern` telescopes to `h(i, j) - h(0, j)`.
-/
theorem sum_range_toGTPattern (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    ∑ k ∈ Finset.range i, h.toGTPattern k j =
      h (Vertex.productChart n i j hij hjn) -
        h (Vertex.productChart n 0 j (Nat.zero_le j) hjn) := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega),
      toGTPattern_apply_of_lt_of_le h (Nat.lt_of_succ_le hij) hjn]; abel

/-- The top row of `h.toGTPattern` is side `1` (`B → C`) of `h.boundary`. -/
@[simp, grind =] theorem topRow_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topRow = h.boundary 1 := by
  ext r
  rw [GTPattern.topRow_apply, toGTPattern_apply_of_lt_of_le h r.isLt le_rfl,
    Vertex.productChart_top_right, Vertex.productChart_top_right, boundary_apply]; rfl

@[simp, grind =] theorem topWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topWeight = h.boundaryWeight 1 := by
  apply Subtype.ext; rw [GTPattern.topWeight_coe, topRow_toGTPattern, coe_boundaryWeight]

theorem rowSum_toGTPattern (h : IntegerHive n) {j : ℕ} (hjn : j ≤ n) :
    h.toGTPattern.rowSum j =
      prefixSum j (h.boundaryWeight 2).dual.1 - prefixSum j (h.boundary 0) := by
  rw [GTPattern.rowSum_def, sum_range_toGTPattern h le_rfl hjn,
    apply_productChart_diag_eq_prefixSum_dual h hjn, apply_productChart_zero_left h hjn]

/-- The torus weight of `h.toGTPattern` is `(h.boundaryWeight 2).dual - h.boundary 0`. -/
@[simp, grind =] theorem rowWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.rowWeight = (h.boundaryWeight 2).dual.1 - h.boundary 0 := by
  ext r
  rw [GTPattern.rowWeight_apply, rowSum_toGTPattern h (by omega),
    rowSum_toGTPattern h r.isLt.le, prefixSum_succ r.isLt, prefixSum_succ r.isLt, Pi.sub_apply]
  abel

theorem topRow_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.topRow = μ.1 := by
  rw [topRow_toGTPattern, hb, productBoundary_one]

theorem rowWeight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : h.toGTPattern.rowWeight = γ.1 - lam.1 := by
  have hd : (h.boundaryWeight 2).dual = γ := by ext r; simp [coe_boundaryWeight, hb]
  rw [rowWeight_toGTPattern, hd, hb, productBoundary_zero]

/-- The **inverse chart completion** `h(i, j) = prefixSum j l + ∑_{k < i} P k j` reconstructing
product-chart hive entries from lower-left boundary `l` and pattern `P`. -/
def gtCompletion (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) : ℤ :=
  prefixSum j l + ∑ k ∈ Finset.range i, P k j

@[grind =] theorem gtCompletion_def (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P i j = prefixSum j l + ∑ k ∈ Finset.range i, P k j := (rfl)

@[simp, grind =] theorem gtCompletion_zero_left (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P 0 j = prefixSum j l := by simp [gtCompletion_def]

@[simp, grind =] theorem gtCompletion_zero_right (l : Fin n → ℤ) (P : GTPattern n) (i : ℕ) :
    gtCompletion l P i 0 = 0 := by
  rw [gtCompletion_def, prefixSum_zero, zero_add]
  exact Finset.sum_eq_zero fun k _ => P.entry_eq_zero_of_le (Nat.zero_le k)

@[simp, grind =] theorem gtCompletion_zero (i j : ℕ) :
    gtCompletion (0 : Fin n → ℤ) (0 : GTPattern n) i j = 0 := by
  simp [gtCompletion_def, prefixSum_def]

@[simp, grind =] theorem gtCompletion_add (l₁ l₂ : Fin n → ℤ) (P₁ P₂ : GTPattern n) (i j : ℕ) :
    gtCompletion (l₁ + l₂) (P₁ + P₂) i j =
      gtCompletion l₁ P₁ i j + gtCompletion l₂ P₂ i j := by
  simp only [gtCompletion_def, prefixSum_add, GTPattern.add_apply, Finset.sum_add_distrib]; abel

@[grind =] theorem gtCompletion_nsmul (k : ℕ) (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion (k • l) (k • P) i j = k • gtCompletion l P i j := by
  simp only [gtCompletion_def, prefixSum_smul, GTPattern.nsmul_apply, ← Finset.smul_sum, smul_add]

theorem gtCompletion_const_of_le (l : Fin n → ℤ) (b : ℤ) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletion l (GTPattern.const n b) i j = prefixSum j l + i • b := by
  rw [gtCompletion_def, Finset.sum_congr rfl fun k hk =>
    GTPattern.const_apply_of_lt_of_le b (lt_of_lt_of_le (Finset.mem_range.mp hk) hij) hjn,
    Finset.sum_const, Finset.card_range]

theorem gtCompletion_shift_of_le (l : Fin n → ℤ) (a b : ℤ) (P : GTPattern n) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletion (fun r => l r + a) (P.shift b) i j =
      gtCompletion l P i j + j • a + i • b := by
  rw [GTPattern.shift_eq_add_const, (Pi.add_def l fun _ => a).symm, gtCompletion_add,
    gtCompletion_const_of_le (fun _ => a) b hij hjn, prefixSum_eq_sum_castLE hjn]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; abel

theorem gtCompletion_of_le (l : Fin n → ℤ) (P : GTPattern n) {i j : ℕ} (hij : j ≤ i) :
    gtCompletion l P i j = prefixSum j l + P.rowSum j := by
  rw [gtCompletion_def, P.sum_range_entry_eq_rowSum hij]

theorem gtCompletion_diag (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P j j = prefixSum j l + P.rowSum j :=
  gtCompletion_of_le l P le_rfl

theorem gtCompletion_diag_of_rowWeight_eq {l g : Fin n → ℤ} {P : GTPattern n}
    (hw : P.rowWeight = g - l) {j : ℕ} (hjn : j ≤ n) :
    gtCompletion l P j j = prefixSum j g := by
  rw [gtCompletion_diag, ← P.prefixSum_rowWeight hjn, hw, ← prefixSum_add, add_sub_cancel]

@[grind =] theorem gtCompletion_top_right (l : Fin n → ℤ) (P : GTPattern n) (i : ℕ) :
    gtCompletion l P i n = (∑ r : Fin n, l r) + prefixSum i P.topRow := by
  rw [gtCompletion_def, prefixSum_of_le le_rfl, funext P.topRow_apply,
    prefixSum_eq_sum_range i (fun k => P k n)]
  rcases le_total i n with hin | hni
  · rw [min_eq_left hin]
  · rw [min_eq_right hni, P.sum_range_entry_eq_rowSum hni, GTPattern.rowSum_def]

@[grind =] theorem gtCompletion_succ_left (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P (i + 1) j = gtCompletion l P i j + P i j := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_range_succ, add_assoc]

@[simp, grind =] theorem gtCompletion_succ_left_sub (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P (i + 1) j - gtCompletion l P i j = P i j := by
  rw [gtCompletion_succ_left, add_sub_cancel_left]

/-- **Inverse formula in the product chart**: `gtCompletion` recovers every chart value of `h` from
`h.boundary 0` and `h.toGTPattern`. -/
theorem gtCompletion_toGTPattern (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletion (h.boundary 0) h.toGTPattern i j = h (Vertex.productChart n i j hij hjn) := by
  rw [gtCompletion_def, sum_range_toGTPattern h hij hjn, apply_productChart_zero_left h hjn]; abel

/-- **Vertex-level inverse formula**: every integer hive `h` is reconstructed at `p : Vertex n` as
`gtCompletion (h.boundary 0) h.toGTPattern p.z (n - p.x)`. -/
@[grind =] theorem apply_eq_gtCompletion_toGTPattern (h : IntegerHive n) (p : Vertex n) :
    h p = gtCompletion (h.boundary 0) h.toGTPattern p.z (n - p.x) := by
  rw [gtCompletion_toGTPattern h (by have := p.sum_eq; omega) (Nat.sub_le n p.x),
    Vertex.productChart_z_sub_x]

theorem apply_eq_gtCompletion_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (p : Vertex n) :
    h p = gtCompletion lam.1 h.toGTPattern p.z (n - p.x) := by
  rw [h.apply_eq_gtCompletion_toGTPattern p, hb, productBoundary_zero]

/-- An integer hive is uniquely determined by its side-`0` boundary and its Gelfand–Tsetlin
difference pattern. -/
theorem eq_of_boundary_zero_eq_of_toGTPattern_eq {h₁ h₂ : IntegerHive n}
    (hb : h₁.boundary 0 = h₂.boundary 0) (hP : h₁.toGTPattern = h₂.toGTPattern) : h₁ = h₂ :=
  ext fun p => by
    rw [h₁.apply_eq_gtCompletion_toGTPattern p, h₂.apply_eq_gtCompletion_toGTPattern p, hb, hP]

end DifferenceAndCompletion

/-! ### Reconstruction (`gt_reconstruction_iff`) and the product-fibre equivalence -/

section Reconstruction

variable {n : ℕ}

/-- Evaluation of `gtCompletion l P` on `Vertex n` via the inverse chart `p ↦ (p.z, n - p.x)`. -/
def gtCompletionVertex (l : Fin n → ℤ) (P : GTPattern n) (p : Vertex n) : ℤ :=
  gtCompletion l P p.z (n - p.x)

@[grind =] theorem gtCompletionVertex_def (l : Fin n → ℤ) (P : GTPattern n) (p : Vertex n) :
    gtCompletionVertex l P p = gtCompletion l P p.z (n - p.x) := (rfl)

@[simp, grind =] theorem gtCompletionVertex_productChart (l : Fin n → ℤ) (P : GTPattern n) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletionVertex l P (Vertex.productChart n i j hij hjn) = gtCompletion l P i j := by
  simp [gtCompletionVertex, Nat.sub_sub_self hjn]

@[simp, grind =] theorem gtCompletionVertex_cornerA (l : Fin n → ℤ) (P : GTPattern n) :
    gtCompletionVertex l P (Vertex.cornerA n) = 0 := by simp [gtCompletionVertex]

/-- The clockwise linear boundary of `gtCompletionVertex l P` has sides `l`, `P.topRow`, and
`r ↦ -(l + P.rowWeight) r.rev`. -/
theorem boundaryLinear_gtCompletionVertex (l : Fin n → ℤ) (P : GTPattern n) :
    boundaryLinear ℤ n ℤ (gtCompletionVertex l P) =
      ![l, P.topRow, fun r => -(l + P.rowWeight) r.rev] := by
  have hdiag (j : ℕ) (hjn : j ≤ n) : gtCompletion l P j j = prefixSum j (l + P.rowWeight) :=
    gtCompletion_diag_of_rowWeight_eq (by abel) hjn
  ext s r
  fin_cases s
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, boundaryLinear_apply, gtCompletionVertex_def,
      Vertex.edgePoint_zero_z, Vertex.edgePoint_zero_x, Fin.val_succ, Fin.val_castSucc,
      gtCompletion_zero_left]
    rw [Nat.sub_sub_self r.isLt, Nat.sub_sub_self r.isLt.le, prefixSum_succ r.isLt]
    abel
  · simp [boundaryLinear_apply, gtCompletionVertex_def, GTPattern.topRow_apply]
  · have hnr : n - r.val = r.rev.val + 1 := by have := r.isLt; rw [Fin.val_rev]; omega
    simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      boundaryLinear_apply, gtCompletionVertex_def, Vertex.edgePoint_two_z,
      Vertex.edgePoint_two_x, Fin.val_succ, Fin.val_castSucc]
    rw [← Fin.val_rev, hnr, hdiag r.rev.val r.rev.isLt.le, hdiag (r.rev.val + 1) r.rev.isLt,
      prefixSum_succ r.rev.isLt, Fin.eta]
    abel

private theorem boundaryLinear_gtCompletionVertex_eq_productBoundary {lam μ γ : DominantWeight n}
    {P : GTPattern n} (hTop : P.topRow = μ.1) (hWeight : P.rowWeight = γ.1 - lam.1) :
    boundaryLinear ℤ n ℤ (gtCompletionVertex lam.1 P) = productBoundary lam μ γ := by
  rw [boundaryLinear_gtCompletionVertex, hTop, hWeight, add_sub_cancel]
  ext s r
  fin_cases s <;> simp

/-- Taking `toGTPattern` of any hive whose entries are given by `gtCompletion l P` returns `P`. -/
theorem toGTPattern_of_eq_gtCompletion {l : Fin n → ℤ} {P : GTPattern n} {h : IntegerHive n}
    (heq : ∀ p : Vertex n, h p = gtCompletion l P p.z (n - p.x)) :
    h.toGTPattern = P := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le h hij.1 hij.2, heq, heq]
    simp only [Vertex.productChart_z, Vertex.productChart_x, Nat.sub_sub_self hij.2,
      gtCompletion_succ_left_sub]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega)]

/-- The remaining unit-rhombus inequalities on a pattern `P` in the product chart with lower-left
boundary `l`: for `0 ≤ i ≤ j` and `j + 2 ≤ n`,
`∑_{k ≤ i} (P k (j + 2) - P k (j + 1)) ≤ l j - l (j + 1) + ∑_{k < i} (P k (j + 1) - P k j)`. -/
def IsProductHiveFeasible (l : Fin n → ℤ) (P : GTPattern n) : Prop :=
  ∀ i j : ℕ, i ≤ j → ∀ _ : j + 2 ≤ n,
    (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ +
        ∑ k ∈ Finset.range i, (P k (j + 1) - P k j)

theorem isProductHiveFeasible_def (l : Fin n → ℤ) (P : GTPattern n) :
    IsProductHiveFeasible l P ↔
      ∀ i j : ℕ, i ≤ j → ∀ _ : j + 2 ≤ n,
        (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
          l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ +
            ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
  Iff.rfl

/-- Bounded-`Fin` characterization of `IsProductHiveFeasible` over `j : Fin (n - 1)` and
`i : Fin (j.val + 1)`, making feasibility computably decidable. -/
theorem isProductHiveFeasible_iff_forall_fin (l : Fin n → ℤ) (P : GTPattern n) :
    IsProductHiveFeasible l P ↔
      ∀ j : Fin (n - 1), ∀ i : Fin (j.val + 1),
        (∑ k ∈ Finset.range (i.val + 1), (P k (j.val + 2) - P k (j.val + 1))) ≤
          l ⟨j.val, by omega⟩ - l ⟨j.val + 1, by omega⟩ +
            ∑ k ∈ Finset.range i.val, (P k (j.val + 1) - P k j.val) :=
  ⟨fun h j i => h i.val j.val (Nat.lt_succ_iff.mp i.isLt) (by omega),
    fun h i j hij hjn => h ⟨j, by omega⟩ ⟨i, Nat.lt_succ_of_le hij⟩⟩

instance (l : Fin n → ℤ) (P : GTPattern n) : Decidable (IsProductHiveFeasible l P) :=
  decidable_of_iff _ (isProductHiveFeasible_iff_forall_fin l P).symm

/-- Equivalence between the remaining product-chart rhombus inequality on `gtCompletion l P` and
its pattern-entry difference form. -/
theorem gtCompletion_rem_le_iff (l : Fin n → ℤ) (P : GTPattern n) {i j : ℕ}
    (hjn : j + 2 ≤ n) :
    gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
        gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) ↔
      (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
        l ⟨j, by omega⟩ - l ⟨j + 1, by omega⟩ +
          ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) := by
  have hj1 : j < n := by omega
  have hj2 : j + 1 < n := by omega
  simp only [gtCompletion_def, Finset.sum_sub_distrib]
  rw [prefixSum_succ hj2, prefixSum_succ hj1]
  omega

theorem isProductHiveFeasible_iff_gtCompletion (l : Fin n → ℤ) (P : GTPattern n) :
    IsProductHiveFeasible l P ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
          gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
    forall_congr' fun hjn => (gtCompletion_rem_le_iff l P hjn).symm

theorem isProductHiveFeasible_zero :
    IsProductHiveFeasible (0 : Fin n → ℤ) (0 : GTPattern n) := by
  rw [isProductHiveFeasible_iff_gtCompletion]
  intro _ _ _ _; simp

theorem IsProductHiveFeasible.add {l₁ l₂ : Fin n → ℤ} {P₁ P₂ : GTPattern n}
    (h₁ : IsProductHiveFeasible l₁ P₁) (h₂ : IsProductHiveFeasible l₂ P₂) :
    IsProductHiveFeasible (l₁ + l₂) (P₁ + P₂) := by
  rw [isProductHiveFeasible_iff_gtCompletion] at h₁ h₂ ⊢
  intro i j hij hjn
  simp only [gtCompletion_add]
  linarith [h₁ i j hij hjn, h₂ i j hij hjn]

theorem IsProductHiveFeasible.nsmul {l : Fin n → ℤ} {P : GTPattern n}
    (h : IsProductHiveFeasible l P) (k : ℕ) :
    IsProductHiveFeasible (k • l) (k • P) := by
  rw [isProductHiveFeasible_iff_gtCompletion] at h ⊢
  intro i j hij hjn
  simp only [gtCompletion_nsmul, ← smul_add]
  exact nsmul_le_nsmul_right (h i j hij hjn) k

/-- Affine shifts of `l` and determinant shifts of `P` leave every remaining product-chart rhombus
slack unchanged, hence preserve `IsProductHiveFeasible`. -/
theorem isProductHiveFeasible_shift_iff (l : Fin n → ℤ) (a b : ℤ) (P : GTPattern n) :
    IsProductHiveFeasible (fun r => l r + a) (P.shift b) ↔ IsProductHiveFeasible l P := by
  simp only [isProductHiveFeasible_iff_gtCompletion]
  refine forall_congr' fun i => forall_congr' fun j => imp_congr_right fun hij =>
    imp_congr_right fun hjn => ?_
  rw [gtCompletion_shift_of_le l a b P hij (by omega),
    gtCompletion_shift_of_le l a b P (by omega) hjn,
    gtCompletion_shift_of_le l a b P (by omega) (by omega),
    gtCompletion_shift_of_le l a b P (by omega) (by omega)]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_mul, one_mul]
  constructor <;> intro h <;> linarith

@[simp, grind =] theorem isProductHiveFeasible_shift_right_iff (l : Fin n → ℤ) (b : ℤ)
    (P : GTPattern n) : IsProductHiveFeasible l (P.shift b) ↔ IsProductHiveFeasible l P := by
  simpa using isProductHiveFeasible_shift_iff l 0 b P

@[simp] theorem isProductHiveFeasible_add_const_left_iff (l : Fin n → ℤ) (a : ℤ)
    (P : GTPattern n) : IsProductHiveFeasible (fun r => l r + a) P ↔ IsProductHiveFeasible l P := by
  simpa using isProductHiveFeasible_shift_iff l a 0 P

@[simp, grind =] theorem isProductHiveFeasible_zero_right_iff (l : Fin n → ℤ) :
    IsProductHiveFeasible l 0 ↔ Antitone l := by
  match n with
  | 0 | 1 =>
    exact ⟨fun _ => Subsingleton.antitone l, fun _ _ _ _ hjn => absurd hjn (by omega)⟩
  | m + 2 =>
    rw [Fin.antitone_iff_succ_le]
    refine ⟨fun h r => ?_, fun h i j _ hjn => ?_⟩
    · have h0 := h 0 r.val (Nat.zero_le _) (by omega)
      simp only [GTPattern.zero_apply, sub_zero, Finset.sum_const_zero, add_zero] at h0
      exact sub_nonneg.mp h0
    · have hr := h ⟨j, by omega⟩
      simp only [Fin.succ_mk, Fin.castSucc_mk] at hr
      simp only [GTPattern.zero_apply, sub_zero, Finset.sum_const_zero, add_zero]
      exact sub_nonneg.mpr hr

@[simp, grind =] theorem isProductHiveFeasible_const_iff (l : Fin n → ℤ) (b : ℤ) :
    IsProductHiveFeasible l (GTPattern.const n b) ↔ Antitone l := by
  have hconst : GTPattern.const n b = (0 : GTPattern n).shift b := by
    rw [GTPattern.shift_eq_add_const, zero_add]
  rw [hconst, isProductHiveFeasible_shift_right_iff, isProductHiveFeasible_zero_right_iff]

/-- `gtCompletionVertex l P` is rhombus-concave iff the remaining rhombus family holds on
`gtCompletion l P`; the two Gelfand–Tsetlin rhombus families hold automatically by interlacing. -/
theorem isRhombusConcave_gtCompletionVertex_iff (l : Fin n → ℤ) (P : GTPattern n) :
    IsRhombusConcave (gtCompletionVertex l P) ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
          gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) := by
  rw [isRhombusConcave_iff_productChart]
  refine ⟨fun h i j hij hjn => by
      simpa only [gtCompletionVertex_productChart] using h.2.2 hij hjn,
    fun hrem => ⟨fun i j hij hjn => ?_, fun i j hij hjn => ?_, fun i j hij hjn => ?_⟩⟩
  · simp only [gtCompletionVertex_productChart, gtCompletion_succ_left]
    linarith [P.entry_le_entry_succ_row hij hjn]
  · simp only [gtCompletionVertex_productChart]
    rw [gtCompletion_succ_left l P (i + 1), gtCompletion_succ_left l P i j]
    linarith [P.entry_succ_succ_le_entry (i := i) hjn]
  · simpa only [gtCompletionVertex_productChart] using hrem i j hij hjn

theorem isProductHiveFeasible_toGTPattern (h : IntegerHive n) :
    IsProductHiveFeasible (h.boundary 0) h.toGTPattern := by
  rw [isProductHiveFeasible_iff_gtCompletion]; intro i j hij hjn
  simp only [gtCompletion_toGTPattern h hij (by omega),
    gtCompletion_toGTPattern h (by omega : i + 1 ≤ j + 2) hjn,
    gtCompletion_toGTPattern h (by omega : i ≤ j + 1) (by omega),
    gtCompletion_toGTPattern h (by omega : i + 1 ≤ j + 1) (by omega)]
  exact h.le_of_isRhombus (isRhombus_productChart_rem hij hjn)

/-- **Product-chart equivalence between fixed-boundary integer hives and Gelfand–Tsetlin patterns**:
`toGTPattern` and `gtCompletion` mutually invert between
`FixedIntegerHive (productBoundary lam μ γ)` and the patterns `P : GTPattern n` with
`P.topRow = μ.1`, `P.rowWeight = γ.1 - lam.1`, and `IsProductHiveFeasible lam.1 P`. -/
def fixedIntegerHiveEquivGTPattern (lam μ γ : DominantWeight n) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1 ∧
        IsProductHiveFeasible lam.1 P} where
  toFun h :=
    ⟨h.1.toGTPattern, topRow_toGTPattern_of_productBoundary h.2,
      rowWeight_toGTPattern_of_productBoundary h.2, by
        have hf := isProductHiveFeasible_toGTPattern h.1; rwa [h.2, productBoundary_zero] at hf⟩
  invFun P :=
    have hconc : IsRhombusConcave (gtCompletionVertex lam.1 P.1) :=
      (isRhombusConcave_gtCompletionVertex_iff lam.1 P.1).mpr
        ((isProductHiveFeasible_iff_gtCompletion lam.1 P.1).mp P.2.2.2)
    ⟨⟨gtCompletionVertex lam.1 P.1, gtCompletionVertex_cornerA lam.1 P.1,
        fun hr => (isRhombusConcave_def _).mp hconc hr⟩, by
      rw [boundary_def]; exact boundaryLinear_gtCompletionVertex_eq_productBoundary P.2.1 P.2.2.1⟩
  left_inv h := Subtype.ext (ext fun p => (apply_eq_gtCompletion_of_productBoundary h.2 p).symm)
  right_inv P := Subtype.ext (toGTPattern_of_eq_gtCompletion fun _ => rfl)

@[simp, grind =] theorem fixedIntegerHiveEquivGTPattern_apply_coe (lam μ γ : DominantWeight n)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp, grind =] theorem fixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1 ∧
      IsProductHiveFeasible lam.1 P}) (p : Vertex n) :
    ((fixedIntegerHiveEquivGTPattern lam μ γ).symm P).1 p =
      gtCompletion lam.1 P.1 p.z (n - p.x) := (rfl)

/-- **Gelfand–Tsetlin reconstruction theorem**: for dominant weights `λ, μ, γ` and a pattern `P`
with `P.topRow = μ` and `P.rowWeight = γ - λ`, an integer hive with boundary `(λ, μ, γ*)` whose
values are given by `gtCompletion` exists iff the remaining product-chart rhombus family holds on
`gtCompletion lam.1 P`. -/
theorem gt_reconstruction_iff (lam μ γ : DominantWeight n) (P : GTPattern n)
    (hTop : P.topRow = μ.1) (hWeight : P.rowWeight = γ.1 - lam.1) :
    (∃ h : FixedIntegerHive (productBoundary lam μ γ),
      ∀ p : Vertex n, h.1 p = gtCompletion lam.1 P p.z (n - p.x)) ↔
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
      gtCompletion lam.1 P i j + gtCompletion lam.1 P (i + 1) (j + 2) ≤
        gtCompletion lam.1 P i (j + 1) + gtCompletion lam.1 P (i + 1) (j + 1) := by
  refine ⟨fun ⟨⟨h, _⟩, heq⟩ => ?_, fun hrem =>
    ⟨(fixedIntegerHiveEquivGTPattern lam μ γ).symm
      ⟨P, hTop, hWeight, (isProductHiveFeasible_iff_gtCompletion lam.1 P).mpr hrem⟩,
      fun _ => rfl⟩⟩
  rw [← isRhombusConcave_gtCompletionVertex_iff]
  have hf : (h : Vertex n → ℤ) = gtCompletionVertex lam.1 P := funext heq
  exact hf ▸ h.isRhombusConcave

theorem hiveCount_productBoundary_eq_card_gtPattern (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1 ∧
        IsProductHiveFeasible lam.1 P} := by
  rw [← natCard_fixedIntegerHive]; exact Nat.card_congr (fixedIntegerHiveEquivGTPattern lam μ γ)

end Reconstruction

/-! ### Cyclic `(λ, μ, ν)` orientation and Henriques–Kamnitzer conversion -/

section CyclicOrientation

variable {n : ℕ}

/-- **Cyclic-orientation hive-to-Gelfand–Tsetlin equivalence** (Henriques–Kamnitzer, Theorem 7.4):
integer hives with cyclic boundary `(λ, μ, ν)` correspond to patterns with top row `λ`, torus
weight `μ* - ν`, and remaining rhombus feasibility with respect to `ν`. -/
def cyclicFixedIntegerHiveEquivGTPattern (lam μ ν : DominantWeight n) :
    FixedIntegerHive (cyclicBoundary lam μ ν) ≃
      {P : GTPattern n // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1 ∧
        IsProductHiveFeasible ν.1 P} :=
  (fixedIntegerHiveRotateTwiceEquiv lam μ ν).trans (fixedIntegerHiveEquivGTPattern ν lam μ.dual)

@[simp, grind =] theorem cyclicFixedIntegerHiveEquivGTPattern_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) :
    (cyclicFixedIntegerHiveEquivGTPattern lam μ ν h).1 = h.1.rotate.rotate.toGTPattern := by
  rw [cyclicFixedIntegerHiveEquivGTPattern, Equiv.trans_apply,
    fixedIntegerHiveEquivGTPattern_apply_coe, fixedIntegerHiveRotateTwiceEquiv_coe]

@[simp, grind =] theorem cyclicFixedIntegerHiveEquivGTPattern_symm_apply_coe
    (lam μ ν : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1 ∧
      IsProductHiveFeasible ν.1 P}) (p : Vertex n) :
    ((cyclicFixedIntegerHiveEquivGTPattern lam μ ν).symm P).1 p =
      gtCompletion ν.1 P.1 p.y (n - p.z) - ∑ r : Fin n, ν.1 r := by
  rw [cyclicFixedIntegerHiveEquivGTPattern, Equiv.symm_trans_apply,
    fixedIntegerHiveRotateTwiceEquiv_symm_apply_coe,
    fixedIntegerHiveEquivGTPattern_symm_apply_coe, Vertex.rotate_z, Vertex.rotate_x]

/-- Forward directional-difference formula in the cyclic orientation `(λ, μ, ν)`: the gauge shift
cancels, leaving `h(j - i - 1, i + 1, n - j) - h(j - i, i, n - j)` for `0 ≤ i < j ≤ n`. -/
theorem cyclicFixedIntegerHiveEquivGTPattern_apply_of_lt_of_le (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    (cyclicFixedIntegerHiveEquivGTPattern lam μ ν h).1 i j =
      h.1 ⟨j - (i + 1), i + 1, n - j, by omega⟩ - h.1 ⟨j - i, i, n - j, by omega⟩ := by
  rw [cyclicFixedIntegerHiveEquivGTPattern_apply_coe, toGTPattern_apply_of_lt_of_le _ hij hjn,
    ← fixedIntegerHiveRotateTwiceEquiv_coe, fixedIntegerHiveRotateTwiceEquiv_apply_coe,
    fixedIntegerHiveRotateTwiceEquiv_apply_coe]
  have hp1 : (Vertex.productChart n (i + 1) j hij hjn).rotate.rotate =
      ⟨j - (i + 1), i + 1, n - j, by omega⟩ := by ext <;> simp
  have hp0 : (Vertex.productChart n i j hij.le hjn).rotate.rotate =
      ⟨j - i, i, n - j, by omega⟩ := by ext <;> simp
  rw [hp1, hp0]; abel

/-- Inverse completion formula in the cyclic orientation `(λ, μ, ν)`:
`h p = gtCompletion ν.1 P p.y (n - p.z) - ∑ r, ν.1 r`. -/
theorem apply_eq_gtCompletion_cyclicFixedIntegerHiveEquivGTPattern (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) (p : Vertex n) :
    h.1 p = gtCompletion ν.1 (cyclicFixedIntegerHiveEquivGTPattern lam μ ν h).1 p.y (n - p.z) -
      ∑ r : Fin n, ν.1 r := by
  have hinv := congrArg (fun x : FixedIntegerHive (cyclicBoundary lam μ ν) => x.1 p)
    ((cyclicFixedIntegerHiveEquivGTPattern lam μ ν).symm_apply_apply h)
  simpa only [cyclicFixedIntegerHiveEquivGTPattern_symm_apply_coe] using hinv.symm

end CyclicOrientation

/-! ### Uniform input gap, stable Gelfand–Tsetlin equivalence, and `n ≤ 1` -/

section UniformGap

/-- **Uniform input gap makes the remaining rhombus family automatic**: if `P : GTPattern (n + 1)`
and `l : Fin (n + 1) → ℤ` satisfy `P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ`
for every `r : Fin n`, then every remaining product-chart rhombus inequality holds on
`gtCompletion l P`. -/
theorem gt_completion_of_uniform_input_gap {n : ℕ} (l : Fin (n + 1) → ℤ) (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ) :
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
        gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) := by
  intro i j hij hjn; rw [gtCompletion_rem_le_iff l P hjn]
  have hleft_nonneg : 0 ≤ ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
    Finset.sum_nonneg fun k hk => sub_nonneg.mpr
      (P.entry_le_entry_succ_row (lt_of_lt_of_le (Finset.mem_range.mp hk) hij) (by omega))
  have hright_tele : (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      P 0 (j + 2) - P (i + 1) (j + 2) :=
    (Finset.sum_le_sum fun k _ => sub_le_sub_left
      (P.entry_succ_succ_le_entry (i := k) (j := j + 1) (by omega)) _).trans_eq
      (Finset.sum_range_sub' (fun k => P k (j + 2)) (i + 1))
  have hhi : P 0 (j + 2) ≤ P.topRow 0 :=
    (P.entry_mem_Icc (i := 0) (j := j + 2) (by omega) hjn).2
  have hlo : P.topRow (Fin.last n) ≤ P (i + 1) (j + 2) := by
    simpa [Fin.last] using (P.entry_mem_Icc (i := i + 1) (j := j + 2) (by omega) hjn).1
  have hgap := hGap ⟨j, by omega⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hgap; linarith

theorem isProductHiveFeasible_of_uniform_input_gap {n : ℕ} (l : Fin (n + 1) → ℤ)
    (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ) :
    IsProductHiveFeasible l P :=
  (isProductHiveFeasible_iff_gtCompletion l P).mpr (gt_completion_of_uniform_input_gap l P hGap)

/-- **Stable Gelfand–Tsetlin equivalence**: under the uniform input gap
`μ_0 - μ_n ≤ λ_r - λ_{r + 1}`, `toGTPattern` and `gtCompletion` establish a canonical bijection
between `FixedIntegerHive (productBoundary lam μ γ)` and the entire weight-`(γ - λ)` pattern fibre
over `μ`. -/
def stableGTPatternEquiv {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquivRight fun P => and_congr_right fun hTop => and_iff_left_of_imp fun _ =>
      isProductHiveFeasible_of_uniform_input_gap lam.1 P fun r => by rw [hTop]; exact hGap r)

@[simp, grind =] theorem stableGTPatternEquiv_apply_coe {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (stableGTPatternEquiv lam μ γ hGap h).1 = h.1.toGTPattern := (rfl)

@[simp, grind =] theorem stableGTPatternEquiv_symm_apply_coe {n : ℕ}
    (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1})
    (p : Vertex (n + 1)) :
    ((stableGTPatternEquiv lam μ γ hGap).symm P).1 p =
      gtCompletion lam.1 P.1 p.z (n + 1 - p.x) := (rfl)

/-- **Existence of the stable Gelfand–Tsetlin equivalence** with `gtCompletion` as inverse entry
formula. -/
theorem exists_stable_gt_equiv {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    ∃ e : FixedIntegerHive (productBoundary lam μ γ) ≃
        {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1},
      ∀ h p, h.1 p = gtCompletion lam.1 (e h).1 p.z (n + 1 - p.x) :=
  ⟨stableGTPatternEquiv lam μ γ hGap, fun h p => apply_eq_gtCompletion_of_productBoundary h.2 p⟩

theorem hiveCount_eq_card_gtPattern_of_uniform_input_gap {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]; exact Nat.card_congr (stableGTPatternEquiv lam μ γ hGap)

/-- For `n ≤ 1`, the remaining rhombus family `j + 2 ≤ n` is empty, so `IsProductHiveFeasible` holds
unconditionally. -/
theorem isProductHiveFeasible_of_le_one {n : ℕ} (hn : n ≤ 1) (l : Fin n → ℤ) (P : GTPattern n) :
    IsProductHiveFeasible l P := fun _ _ _ hjn => absurd hjn (by omega)

/-- Unconditional equivalence onto the entire Gelfand–Tsetlin weight fibre when `n ≤ 1` (covering
both `n = 0` without first/last entries and `n = 1` with empty gap condition). -/
def fixedIntegerHiveEquivGTPatternOfLeOne {n : ℕ} (hn : n ≤ 1) (lam μ γ : DominantWeight n) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquivRight fun P =>
      and_congr_right fun _ => and_iff_left (isProductHiveFeasible_of_le_one hn lam.1 P))

@[simp, grind =] theorem fixedIntegerHiveEquivGTPatternOfLeOne_apply_coe {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n) (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp, grind =] theorem fixedIntegerHiveEquivGTPatternOfLeOne_symm_apply_coe {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1}) (p : Vertex n) :
    ((fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ).symm P).1 p =
      gtCompletion lam.1 P.1 p.z (n - p.x) := (rfl)

theorem hiveCount_productBoundary_eq_card_gtPattern_of_le_one {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ)

end UniformGap

/-! ### Low-rank characterizations and worked examples -/

section LowRank

/-- At rank `1`, `FixedIntegerHive (productBoundary lam μ γ)` matches the unique pattern over `μ`
when `λ₀ + μ₀ = γ₀` and is empty otherwise. -/
theorem hiveCount_productBoundary_one (lam μ γ : DominantWeight 1) :
    hiveCount (productBoundary lam μ γ) = if lam.1 0 + μ.1 0 = γ.1 0 then 1 else 0 := by
  rw [hiveCount_productBoundary_eq_card_gtPattern_of_le_one le_rfl,
    GTPattern.card_topRow_and_rowWeight_one]
  have hiff : (μ.1 0 = (γ.1 - lam.1) 0) ↔ (lam.1 0 + μ.1 0 = γ.1 0) := by
    simp only [Pi.sub_apply]; omega
  by_cases h : lam.1 0 + μ.1 0 = γ.1 0
  · rw [ite_eq_left h, ite_eq_left (hiff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.mp h)]

/-- **Rank-`2` remaining-rhombus simplification**: for any `l : Fin 2 → ℤ` and `P : GTPattern 2`,
`IsProductHiveFeasible l P` reduces to the single `(0, 0)` inequality
`l 1 + P.topRow 0 ≤ l 0 + P.rowWeight 0`. -/
theorem isProductHiveFeasible_two_iff (l : Fin 2 → ℤ) (P : GTPattern 2) :
    IsProductHiveFeasible l P ↔ l 1 + P.topRow 0 ≤ l 0 + P.rowWeight 0 := by
  rw [isProductHiveFeasible_iff_forall_fin]
  have h00 :
      ((∑ k ∈ Finset.range 1, (P k 2 - P k 1)) ≤
          l 0 - l 1 + ∑ k ∈ Finset.range 0, (P k 1 - P k 0)) ↔
        l 1 + P.topRow 0 ≤ l 0 + P.rowWeight 0 := by
    simp only [GTPattern.topRow_apply, GTPattern.rowWeight_apply, GTPattern.rowSum_def,
      Fin.val_zero, zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, add_zero]
    omega
  refine ⟨fun h => h00.mp ?_, fun h j i => ?_⟩
  · simpa only [Fin.val_zero, zero_add, Fin.zero_eta, Fin.mk_one] using h 0 0
  · fin_cases j; fin_cases i
    simpa only [Fin.val_zero, zero_add, Fin.zero_eta, Fin.mk_one] using h00.mpr h

/-- **Complete `GL 2` Clebsch–Gordan formula for integer hives**: `hiveCount` on
`productBoundary lam μ γ` is `1` iff degree conservation `|λ| + |μ| = |γ|` holds and
`max (λ₀ + μ₁) (λ₁ + μ₀) ≤ γ₀ ≤ λ₀ + μ₀`, and `0` otherwise. -/
theorem hiveCount_productBoundary_two (lam μ γ : DominantWeight 2) :
    hiveCount (productBoundary lam μ γ) =
      if (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
          max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧ γ.1 0 ≤ lam.1 0 + μ.1 0
        then 1 else 0 := by
  have hiff : Nonempty (FixedIntegerHive (productBoundary lam μ γ)) ↔
      (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
        max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧ γ.1 0 ≤ lam.1 0 + μ.1 0 := by
    rw [(fixedIntegerHiveEquivGTPattern lam μ γ).nonempty_congr]
    refine ⟨fun ⟨⟨P, hTop, hWeight, hFeas⟩⟩ => ?_, fun h => ?_⟩
    · obtain ⟨hwlo, hwhi, hwsum⟩ :=
        (GTPattern.nonempty_topRow_and_rowWeight_two_iff μ.1 (γ.1 - lam.1)).mp
          ⟨⟨P, hTop, hWeight⟩⟩
      have hrem := (isProductHiveFeasible_two_iff lam.1 P).mp hFeas
      rw [hTop, hWeight, Pi.sub_apply] at hrem
      simp only [Pi.sub_apply] at hwlo hwhi hwsum
      exact ⟨by omega, max_le (by omega) (by omega), by omega⟩
    · have hlo₁ : lam.1 0 + μ.1 1 ≤ γ.1 0 := (le_max_left _ _).trans h.2.1
      have hlo₂ : lam.1 1 + μ.1 0 ≤ γ.1 0 := (le_max_right _ _).trans h.2.1
      obtain ⟨⟨P, hTop, hWeight⟩⟩ :=
        (GTPattern.nonempty_topRow_and_rowWeight_two_iff μ.1 (γ.1 - lam.1)).mpr
          (by simp only [Pi.sub_apply]; exact ⟨by omega, by omega, by omega⟩)
      exact ⟨⟨P, hTop, hWeight,
        (isProductHiveFeasible_two_iff lam.1 P).mpr (by rw [hTop, hWeight, Pi.sub_apply]; omega)⟩⟩
  by_cases hc : (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
      max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧ γ.1 0 ≤ lam.1 0 + μ.1 0
  · rw [ite_eq_left hc]
    have hpos : 0 < hiveCount (productBoundary lam μ γ) := hiveCount_pos_iff.mpr (hiff.mpr hc)
    have hle := hiveCount_le_one_two (productBoundary lam μ γ); omega
  · rw [ite_eq_right hc]; exact hiveCount_eq_zero_iff.mpr ⟨fun h => hc (hiff.mp ⟨h⟩)⟩

/-- At `n = 2` with `λ = (0, 0)` and `μ = (2, 0)`, the weight-`(1, 1)` Gelfand–Tsetlin fibre over
`μ` has cardinality `1` (`GTPattern.card_topRow_two_zero_and_rowWeight_one_one`), whereas the
remaining rhombus inequality `λ₁ + μ₀ ≤ γ₀` (`2 ≤ 1`) rejects `γ = (1, 1)`. -/
theorem hiveCount_two_zero_twoZero_oneOne :
    hiveCount
      (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![1, 1], by decide⟩) = 0 := by
  rw [hiveCount_productBoundary_two]; decide

/-- At `n = 2` with `λ = (0, 0)` and `μ = γ = (2, 0)`, the unique highest-weight pattern survives
the remaining rhombus inequality. -/
theorem hiveCount_two_zero_twoZero_twoZero :
    hiveCount
      (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]; decide

/-- Clebsch–Gordan multiplicity `c^{(4, 0)}_{(2, 0), (2, 0)} = 1` in the uniform-input-gap regime
`λ = μ = (2, 0)`. -/
theorem hiveCount_two_twoZero_twoZero_fourZero :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![4, 0], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]; decide

/-- Clebsch–Gordan multiplicity `c^{(3, 1)}_{(2, 0), (2, 0)} = 1` in the uniform-input-gap regime
`λ = μ = (2, 0)`. -/
theorem hiveCount_two_twoZero_twoZero_threeOne :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![3, 1], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]; decide

/-- Clebsch–Gordan multiplicity `c^{(2, 2)}_{(2, 0), (2, 0)} = 1` in the uniform-input-gap regime
`λ = μ = (2, 0)`. -/
theorem hiveCount_two_twoZero_twoZero_twoTwo :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![2, 2], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]; decide

/-- At `n = 3` with `λ = 0`, `μ = (1, 0, -1)`, and `γ = 0`, the zero-weight Gelfand–Tsetlin fibre
over the adjoint highest weight `(1, 0, -1)` has multiplicity `2`
(`GTPattern.card_topRow_one_zero_neg_one_and_rowWeight_zero`), whereas the remaining rhombus
inequalities exclude all patterns so `hiveCount = 0`. -/
theorem hiveCount_three_zero_adjoint_zero :
    hiveCount (productBoundary (0 : DominantWeight 3) ⟨![1, 0, -1], by decide⟩ 0) = 0 := by
  let μ : DominantWeight 3 := ⟨![1, 0, -1], by decide⟩
  have h0 : (0 : DominantWeight 3) = (0 : DominantWeight 3).dual := by ext i; simp
  rw [congrArg (productBoundary 0 μ) h0, ← cyclicBoundary_eq_productBoundary_dual,
    hiveCount_cyclicBoundary]
  refine hiveCount_eq_zero_iff.mpr ⟨fun ⟨_, hb⟩ => ?_⟩
  have hle := first_le_of_productBoundary hb; simp [μ] at hle

end LowRank

end TauCeti.Hive
