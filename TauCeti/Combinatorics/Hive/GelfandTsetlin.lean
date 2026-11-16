/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.BigOperators.Finset.PartialSum

/-!
# Hives and Gelfand-Tsetlin patterns

In the **chart** `(i, j) ↦ (n - j, j - i, i)`, `0 ≤ i ≤ j ≤ n`, of the triangular lattice, the
corner `A` is `(0, 0)`, side `A → B` is `i = 0`, side `B → C` is `j = n` and side `C → A` is the
diagonal `i = j`. A hive `h` with clockwise boundary `(λ, μ, γ*)` therefore has
`h(0, j) = λ₀ + ⋯ + λⱼ₋₁`, `h(i, n) = |λ| + μ₀ + ⋯ + μᵢ₋₁` and `h(j, j) = γ₀ + ⋯ + γⱼ₋₁`.

The unit rhombi of the lattice fall into three families in this chart
(`TauCeti.Hive.isRhombusConcave_chart_iff`). For `i < j < n` the first two are
`h(i+1, j) + h(i, j+1) ≤ h(i, j) + h(i+1, j+1)` and
`h(i, j) + h(i+2, j+1) ≤ h(i+1, j) + h(i+1, j+1)`, and say exactly that the horizontal differences
`P i j = h(i+1, j) - h(i, j)` interlace: `P i j ≤ P i (j+1)` and `P (i+1) (j+1) ≤ P i j`. So
the differences of an integer hive form a Gelfand-Tsetlin pattern `TauCeti.Hive.toGTPattern` with
top row `μ` and weight `γ - λ`. The hive is recovered from `λ` and its pattern by summing the
differences along each row of the chart (`TauCeti.Hive.gtCompletion`). The third family,
`h(i, j) + h(i+1, j+2) ≤ h(i, j+1) + h(i+1, j+1)` for `i ≤ j`, `j + 2 ≤ n`, is the only condition
a pattern must satisfy beyond interlacing for its completion to be a hive.

This identifies the integer hives with boundary `(λ, μ, γ*)` with the Gelfand-Tsetlin patterns
with top row `μ`, weight `γ - λ`, and completion satisfying the third family
(`TauCeti.Hive.fixedIntegerHiveEquivGTPattern`). When every adjacent gap of `λ` is at least
`μ₀ - μₙ₋₁`, the third family holds automatically
(`TauCeti.Hive.gtCompletionConcave_of_gap`), so that the hives are counted by all patterns of
top row `μ` and weight `γ - λ` (`TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfGap`).

## Main definitions

* `TauCeti.Hive.toGTPattern`: the Gelfand-Tsetlin pattern of horizontal differences of an integer
  hive.
* `TauCeti.Hive.gtCompletion`: the chart function rebuilt from a boundary `λ` and a pattern.
* `TauCeti.Hive.GTCompletionConcave`: the third family of rhombus inequalities for a completion.
* `TauCeti.Hive.ofGTPattern`: the integer hive with values the completion of a pattern.
* `TauCeti.Hive.fixedIntegerHiveEquivGTPattern`, `TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfGap`:
  the equivalences of fixed-boundary hive fibres with sets of patterns.

## Main results

* `TauCeti.Hive.isRhombusConcave_gtCompletion_iff`: the completion of a pattern is
  rhombus-concave iff it satisfies the third family.
* `TauCeti.Hive.topRow_toGTPattern`, `TauCeti.Hive.weight_toGTPattern`,
  `TauCeti.Hive.apply_eq_gtCompletion`: the top row, the weight, and the reconstruction formula.
* `TauCeti.Hive.exists_fixedIntegerHive_eq_gtCompletion_iff`: a pattern of top row `μ` and weight
  `γ - λ` is the difference pattern of a hive with boundary `(λ, μ, γ*)` iff its completion
  satisfies the third family.
* `TauCeti.Hive.gtCompletionConcave_of_gap`, `TauCeti.Hive.hiveCount_eq_card_gtPattern_of_gap`:
  under the uniform input gap the third family is automatic, and the hive count is a count of
  Gelfand-Tsetlin patterns.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Henriques and J. Kamnitzer, *The octahedron recurrence and gl(n) crystals*, Adv. Math. **206**
  (2006), 211–249, §7.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

variable {n : ℕ}

private theorem isRhombusConcave_gtChart (h : IntegerHive n) :
    IsRhombusConcave (fun v : Vertex n => gtChart (⇑h) v.z (n - v.x)) := by
  simpa only [gtChart_z_sub_x] using h.isRhombusConcave

/-! ### The Gelfand-Tsetlin pattern of an integer hive -/

/-- The **Gelfand-Tsetlin pattern of an integer hive**: its entry `(i, j)`, `i < j ≤ n`, is the
horizontal difference `h(i+1, j) - h(i, j)` in the chart. The first two families of rhombus
inequalities are the interlacing inequalities. -/
def toGTPattern (h : IntegerHive n) : GTPattern n where
  entry i j := if i < j then gtChart (⇑h) (i + 1) j - gtChart (⇑h) i j else 0
  zeros' {i j} hij := by
    rcases hij with hj | hj
    · simp [gtChart_eq_zero_of_lt _ hj]
    · simp [not_lt.mpr hj]
  interlacing' {i j} hij hj := by
    obtain ⟨h₁, h₂, -⟩ := (isRhombusConcave_chart_iff _).mp h.isRhombusConcave_gtChart
    have e₁ := h₁ i j hij hj
    have e₂ := h₂ i j hij hj
    simp only [hij, ↓reduceIte, show i < j + 1 by omega, show i + 1 < j + 1 by omega]
    constructor <;> linarith

theorem toGTPattern_apply (h : IntegerHive n) {i j : ℕ} (hij : i < j) :
    h.toGTPattern i j = gtChart (⇑h) (i + 1) j - gtChart (⇑h) i j := ite_eq_left hij

/-- The chart values along row `j` are partial sums of the pattern. -/
theorem gtChart_eq_add_sum (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) :
    gtChart (⇑h) i j = gtChart (⇑h) 0 j + ∑ k ∈ Finset.range i, h.toGTPattern k j := by
  rw [Finset.sum_congr rfl fun k hk => h.toGTPattern_apply (by simp at hk; omega),
    Finset.sum_range_sub (fun k => gtChart (⇑h) k j)]
  abel

/-- Along side `A → B`, the chart values are the partial sums of the first boundary weight. -/
theorem gtChart_zero_eq_sum (h : IntegerHive n) {j : ℕ} (hj : j ≤ n) :
    gtChart (⇑h) 0 j = ∑ r : Fin n with r.val < j, h.boundary 0 r := by
  rw [gtChart_zero_left _ hj, h.apply_edgePoint_zero]

/-! ### The chart completion of a pattern -/

/-- The **chart completion** of a boundary weight `l` and a pattern `P`: the chart function
`(i, j) ↦ (l₀ + ⋯ + lⱼ₋₁) + (P 0 j + ⋯ + P (i-1) j)`, whose value at `(0, j)` is the partial sum of
`l` and whose horizontal differences are the entries of `P`. -/
def gtCompletion (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) : ℤ :=
  (∑ r : Fin n with r.val < j, l r) + ∑ k ∈ Finset.range i, P k j

theorem gtCompletion_def (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P i j = (∑ r : Fin n with r.val < j, l r) + ∑ k ∈ Finset.range i, P k j := (rfl)

@[simp]
theorem gtCompletion_zero_left (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P 0 j = ∑ r : Fin n with r.val < j, l r := by
  simp [gtCompletion]

theorem gtCompletion_succ_left (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P (i + 1) j = gtCompletion l P i j + P i j := by
  simp only [gtCompletion, Finset.sum_range_succ, add_assoc]

/-- On the diagonal, the completion is the partial sum of `l` plus the row sum of `P`. -/
theorem gtCompletion_self (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P j j = (∑ r : Fin n with r.val < j, l r) + P.rowSum j := by
  rw [gtCompletion_def, GTPattern.rowSum_def]

/-- The chart completion of `l` and `P` satisfies the third family of rhombus inequalities
`c(i, j) + c(i+1, j+2) ≤ c(i, j+1) + c(i+1, j+1)` for `i ≤ j` and `j + 2 ≤ n`. The completion
always satisfies the other two families, so this is its rhombus concavity
(`TauCeti.Hive.isRhombusConcave_gtCompletion_iff`). -/
def GTCompletionConcave (l : Fin n → ℤ) (P : GTPattern n) : Prop :=
  ∀ i j, i ≤ j → j + 2 ≤ n →
    gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
      gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1)

theorem gtCompletionConcave_iff {l : Fin n → ℤ} {P : GTPattern n} :
    GTCompletionConcave l P ↔
      ∀ i j, i ≤ j → j + 2 ≤ n →
        gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
          gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) := Iff.rfl

/-- The completion of any pattern satisfies the first two families of rhombus inequalities, which
are its interlacing inequalities; so it is rhombus-concave iff it satisfies the third family. -/
theorem isRhombusConcave_gtCompletion_iff (l : Fin n → ℤ) (P : GTPattern n) :
    IsRhombusConcave (fun v : Vertex n => gtCompletion l P v.z (n - v.x)) ↔
      GTCompletionConcave l P := by
  rw [isRhombusConcave_chart_iff, gtCompletionConcave_iff]
  refine ⟨fun h => h.2.2, fun h => ⟨fun i j hij hj => ?_, fun i j _ hj => ?_, h⟩⟩
  · have := P.entry_le_entry_succ_row hij hj
    simp only [gtCompletion_succ_left]
    linarith
  · have := P.entry_succ_succ_le_entry (i := i) hj
    simp only [gtCompletion_succ_left]
    linarith

/-- **Reconstruction**: an integer hive is the chart completion of its first boundary weight and
its Gelfand-Tsetlin pattern. -/
theorem apply_eq_gtCompletion (h : IntegerHive n) (v : Vertex n) :
    h v = gtCompletion (h.boundary 0) h.toGTPattern v.z (n - v.x) := by
  have := v.sum_eq
  rw [← gtChart_z_sub_x (⇑h) v, h.gtChart_eq_add_sum (by omega), h.gtChart_zero_eq_sum (by omega),
    gtCompletion_def]

/-- The completion of the pattern of an integer hive satisfies the third family of rhombus
inequalities. -/
theorem gtCompletionConcave_toGTPattern (h : IntegerHive n) :
    GTCompletionConcave (h.boundary 0) h.toGTPattern := by
  refine (isRhombusConcave_gtCompletion_iff _ _).mp ?_
  simpa only [← apply_eq_gtCompletion] using h.isRhombusConcave

/-- The top row of the pattern of a hive is its second boundary weight. -/
theorem topRow_toGTPattern (h : IntegerHive n) : h.toGTPattern.topRow = h.boundary 1 := by
  ext i
  rw [GTPattern.topRow_apply, h.toGTPattern_apply i.2, gtChart_right _ i.2,
    gtChart_right _ i.2.le, boundary_apply]
  rfl

/-- The row sums of the pattern of a hive are differences of chart values. -/
theorem rowSum_toGTPattern (h : IntegerHive n) (j : ℕ) :
    h.toGTPattern.rowSum j = gtChart (⇑h) j j - gtChart (⇑h) 0 j := by
  rw [GTPattern.rowSum_def, h.gtChart_eq_add_sum le_rfl]
  abel

/-- The `r`-th weight coordinate of the pattern of a hive with boundary sides `B₀, B₁, B₂` is
`-B₂(n - 1 - r) - B₀(r)`; for the boundary `(λ, μ, γ*)` this is `γᵣ - λᵣ`
(`TauCeti.Hive.weight_toGTPattern_of_boundary_eq`). -/
theorem weight_toGTPattern (h : IntegerHive n) (r : Fin n) :
    h.toGTPattern.weight r = -h.boundary 2 r.rev - h.boundary 0 r := by
  -- Side `A → B` steps from chart column `r` to `r + 1`; side `C → A` down the diagonal.
  have e₀ : h.boundary 0 r = gtChart (⇑h) 0 (r + 1) - gtChart (⇑h) 0 r := by
    rw [boundary_apply, gtChart_zero_left _ r.2, gtChart_zero_left _ r.2.le]
    rfl
  have e₂ : h.boundary 2 r.rev = gtChart (⇑h) r r - gtChart (⇑h) (r + 1) (r + 1) := by
    rw [boundary_apply, gtChart_self _ r.2.le, gtChart_self _ r.2]
    congr 3
    exact Fin.ext (by simp [Fin.val_rev]; omega)
  rw [GTPattern.weight_apply, h.rowSum_toGTPattern, h.rowSum_toGTPattern, e₀, e₂]
  abel

/-! ### The integer hive of a pattern -/

/-- The integer hive whose values are the chart completion of a boundary weight `l` and a pattern
`P` satisfying the third family of rhombus inequalities. -/
def ofGTPattern (l : Fin n → ℤ) (P : GTPattern n) (hP : GTCompletionConcave l P) :
    IntegerHive n where
  value v := gtCompletion l P v.z (n - v.x)
  value_cornerA' := by simp
  le_of_isRhombus' hr :=
    (isRhombusConcave_def _).mp ((isRhombusConcave_gtCompletion_iff l P).mpr hP) hr

variable {l : Fin n → ℤ} {P : GTPattern n} {hP : GTCompletionConcave l P}

@[simp]
theorem ofGTPattern_apply (v : Vertex n) :
    ofGTPattern l P hP v = gtCompletion l P v.z (n - v.x) := (rfl)

theorem gtChart_ofGTPattern {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    gtChart (⇑(ofGTPattern l P hP)) i j = gtCompletion l P i j := by
  rw [gtChart_of_le _ hij hj, ofGTPattern_apply, Vertex.ofYZ_z, Vertex.ofYZ_x,
    show n - (n - (j - i) - i) = j by omega]

/-- The pattern of the hive of a pattern is the pattern itself. -/
@[simp]
theorem toGTPattern_ofGTPattern : (ofGTPattern l P hP).toGTPattern = P := by
  ext i j
  rcases Nat.lt_or_ge i j with hij | hij
  · rcases Nat.lt_or_ge n j with hj | hj
    · rw [GTPattern.entry_eq_zero_of_lt _ hj, GTPattern.entry_eq_zero_of_lt _ hj]
    · rw [toGTPattern_apply _ hij, gtChart_ofGTPattern hij hj, gtChart_ofGTPattern hij.le hj,
        gtCompletion_succ_left, add_sub_cancel_left]
  · rw [GTPattern.entry_eq_zero_of_le _ hij, GTPattern.entry_eq_zero_of_le _ hij]

/-- An integer hive is the hive of its pattern and its first boundary weight. -/
@[simp]
theorem ofGTPattern_toGTPattern (h : IntegerHive n) :
    ofGTPattern (h.boundary 0) h.toGTPattern h.gtCompletionConcave_toGTPattern = h := by
  ext v
  rw [ofGTPattern_apply, ← apply_eq_gtCompletion]

/-- Along side `A → B`, the hive of a pattern takes the partial sums of `l`. -/
private theorem ofGTPattern_edgePoint_zero (k : Fin (n + 1)) :
    ofGTPattern l P hP (Vertex.edgePoint n 0 k) = ∑ r : Fin n with r.val < k.val, l r := by
  rw [ofGTPattern_apply, Vertex.edgePoint_zero_z, Vertex.edgePoint_zero_x,
    Nat.sub_sub_self (Nat.le_of_lt_succ k.2), gtCompletion_zero_left]

/-- Along side `B → C`, the hive of a pattern is the completion in chart column `n`. -/
private theorem ofGTPattern_edgePoint_one (k : Fin (n + 1)) :
    ofGTPattern l P hP (Vertex.edgePoint n 1 k) = gtCompletion l P k n := by
  rw [ofGTPattern_apply, Vertex.edgePoint_one_z, Vertex.edgePoint_one_x, Nat.sub_zero]

/-- Along side `C → A`, the hive of a pattern is the completion on the chart diagonal. -/
private theorem ofGTPattern_edgePoint_two (k : Fin (n + 1)) :
    ofGTPattern l P hP (Vertex.edgePoint n 2 k) = gtCompletion l P (n - k) (n - k) := by
  rw [ofGTPattern_apply, Vertex.edgePoint_two_z, Vertex.edgePoint_two_x]

/-- The clockwise boundary of the hive of a pattern: its sides are `l`, the top row of `P`, and
the dual of `l + wt(P)`. -/
theorem boundary_ofGTPattern :
    (ofGTPattern l P hP).boundary = ![l, P.topRow, fun i => -(l i.rev + P.weight i.rev)] := by
  ext s i
  fin_cases s
  · change (ofGTPattern l P hP).boundary 0 i = l i
    have hl := prefixSum_succ i.2 l
    rw [prefixSum_def, prefixSum_def] at hl
    rw [boundary_apply, ofGTPattern_edgePoint_zero, ofGTPattern_edgePoint_zero]
    exact sub_eq_of_eq_add' hl
  · change (ofGTPattern l P hP).boundary 1 i = P.topRow i
    rw [boundary_apply, ofGTPattern_edgePoint_one, ofGTPattern_edgePoint_one,
      GTPattern.topRow_apply]
    exact sub_eq_of_eq_add' (gtCompletion_succ_left l P i n)
  · change (ofGTPattern l P hP).boundary 2 i = -(l i.rev + P.weight i.rev)
    have hl := prefixSum_succ i.rev.2 l
    simp only [prefixSum_def, Fin.eta] at hl
    have e₁ : n - (i.succ : ℕ) = i.rev := by simp [Fin.val_rev]
    have e₂ : n - (i.castSucc : ℕ) = i.rev + 1 := by simp [Fin.val_rev]; omega
    rw [boundary_apply, ofGTPattern_edgePoint_two, ofGTPattern_edgePoint_two, gtCompletion_self,
      gtCompletion_self, e₁, e₂, hl, GTPattern.weight_apply]
    abel

/-! ### Fixed-boundary fibres as Gelfand-Tsetlin fibres -/

section ProductBoundary

variable (lam μ γ : DominantWeight n)

theorem topRow_toGTPattern_of_boundary_eq {h : IntegerHive n}
    (hB : h.boundary = productBoundary lam μ γ) : h.toGTPattern.topRow = μ.1 := by
  rw [topRow_toGTPattern, hB, productBoundary_one]

/-- The pattern of a hive with boundary `(λ, μ, γ*)` has weight `γ - λ`. -/
theorem weight_toGTPattern_of_boundary_eq {h : IntegerHive n}
    (hB : h.boundary = productBoundary lam μ γ) : h.toGTPattern.weight = γ.1 - lam.1 := by
  ext r
  rw [weight_toGTPattern, hB, productBoundary_two, productBoundary_zero,
    DominantWeight.dual_apply, Fin.rev_rev, Pi.sub_apply, neg_neg]

/-- **Reconstruction of a hive with boundary `(λ, μ, γ*)`**: it is the chart completion of `λ`
and its Gelfand-Tsetlin pattern. -/
theorem apply_eq_gtCompletion_of_boundary_eq {h : IntegerHive n}
    (hB : h.boundary = productBoundary lam μ γ) (v : Vertex n) :
    h v = gtCompletion lam.1 h.toGTPattern v.z (n - v.x) := by
  rw [apply_eq_gtCompletion, hB, productBoundary_zero]

/-- The hive of a pattern with top row `μ` and weight `γ - λ` has boundary `(λ, μ, γ*)`. -/
theorem boundary_ofGTPattern_eq_productBoundary {P : GTPattern n}
    {hP : GTCompletionConcave lam.1 P} (hTop : P.topRow = μ.1) (hW : P.weight = γ.1 - lam.1) :
    (ofGTPattern lam.1 P hP).boundary = productBoundary lam μ γ := by
  rw [boundary_ofGTPattern]
  ext s i
  fin_cases s
  · simp
  · simp [hTop]
  · simp [hW]

/-- **Fixed-boundary hives are Gelfand-Tsetlin patterns.** The integer hives with clockwise
boundary `(λ, μ, γ*)` correspond to the Gelfand-Tsetlin patterns with top row `μ` and weight
`γ - λ` whose chart completion satisfies the third family of rhombus inequalities. The forward map
is `TauCeti.Hive.toGTPattern`, the inverse the chart completion `TauCeti.Hive.ofGTPattern`. -/
def fixedIntegerHiveEquivGTPattern :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧
        GTCompletionConcave lam.1 P} where
  toFun h := ⟨h.1.toGTPattern, topRow_toGTPattern_of_boundary_eq lam μ γ h.2,
    weight_toGTPattern_of_boundary_eq lam μ γ h.2, by
      simpa only [h.2, productBoundary_zero] using h.1.gtCompletionConcave_toGTPattern⟩
  invFun P := ⟨ofGTPattern lam.1 P.1 P.2.2.2,
    boundary_ofGTPattern_eq_productBoundary lam μ γ P.2.1 P.2.2.1⟩
  left_inv h := by
    ext v
    exact (apply_eq_gtCompletion_of_boundary_eq lam μ γ h.2 v).symm
  right_inv P := Subtype.ext (toGTPattern_ofGTPattern (hP := P.2.2.2))

@[simp]
theorem fixedIntegerHiveEquivGTPattern_apply_coe (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h : GTPattern n) = h.1.toGTPattern := (rfl)

@[simp]
theorem fixedIntegerHiveEquivGTPattern_symm_apply_apply
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧
      GTCompletionConcave lam.1 P})
    (v : Vertex n) :
    ((fixedIntegerHiveEquivGTPattern lam μ γ).symm P).1 v =
      gtCompletion lam.1 P.1 v.z (n - v.x) := (rfl)

/-- **Reconstruction of a hive from its pattern.** A Gelfand-Tsetlin pattern with top row `μ` and
weight `γ - λ` is the difference pattern of a hive with boundary `(λ, μ, γ*)`, namely of its chart
completion, iff the completion satisfies the third family of rhombus inequalities. -/
theorem exists_fixedIntegerHive_eq_gtCompletion_iff (P : GTPattern n) (hTop : P.topRow = μ.1)
    (hW : P.weight = γ.1 - lam.1) :
    (∃ h : FixedIntegerHive (productBoundary lam μ γ),
        ∀ v, h.1 v = gtCompletion lam.1 P v.z (n - v.x)) ↔
      GTCompletionConcave lam.1 P := by
  refine ⟨fun ⟨h, hv⟩ => (isRhombusConcave_gtCompletion_iff _ _).mp ?_, fun hP =>
    ⟨⟨ofGTPattern lam.1 P hP, boundary_ofGTPattern_eq_productBoundary lam μ γ hTop hW⟩,
      fun _ => rfl⟩⟩
  simpa only [← hv] using h.1.isRhombusConcave

end ProductBoundary

/-! ### The uniform input gap -/

/-- **The uniform input gap makes the third family automatic.** If every adjacent gap
`lᵣ - lᵣ₊₁` of the boundary weight `l` is at least the spread `μ₀ - μₙ` of the top row `μ` of a
pattern `P`, then the chart completion of `l` and `P` satisfies the third family of rhombus
inequalities. -/
theorem gtCompletionConcave_of_gap (l : Fin (n + 1) → ℤ) (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ) :
    GTCompletionConcave l P := by
  intro i j hij hj
  -- The partial sums of `l` contribute `l (j + 1) - l j`.
  have hl₁ : ∑ r : Fin (n + 1) with r.val < j + 1, l r =
      (∑ r : Fin (n + 1) with r.val < j, l r) + l ⟨j, by omega⟩ := by
    simpa only [prefixSum_def] using prefixSum_succ (by omega : j < n + 1) l
  have hl₂ : ∑ r : Fin (n + 1) with r.val < j + 2, l r =
      (∑ r : Fin (n + 1) with r.val < j + 1, l r) + l ⟨j + 1, by omega⟩ := by
    simpa only [prefixSum_def] using prefixSum_succ (by omega : j + 1 < n + 1) l
  -- The entries of row `j` are at most those of row `j + 1`.
  have hA : ∑ k ∈ Finset.range i, P k j ≤ ∑ k ∈ Finset.range i, P k (j + 1) :=
    Finset.sum_le_sum fun k hk =>
      P.entry_le_entry_succ_row (by simp at hk; omega) (by omega)
  -- The increase from row `j + 1` to row `j + 2` telescopes to the spread of row `j + 2`.
  have hB : ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1)) ≤
      ∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P (k + 1) (j + 2)) :=
    Finset.sum_le_sum fun k _ => sub_le_sub_left (P.entry_succ_succ_le_entry (by omega)) _
  rw [Finset.sum_range_sub' (fun k => P k (j + 2))] at hB
  have h₀ := (P.entry_mem_Icc (i := 0) (j := j + 2) (by omega) hj).2
  have h₁ := (P.entry_mem_Icc (i := i + 1) (j := j + 2) (by omega) hj).1
  have hlast : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [hlast] at h₁
  have hg := hGap ⟨j, by omega⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hg
  simp only [gtCompletion_def, Finset.sum_sub_distrib] at hB ⊢
  simp only [Fin.zero_eta] at h₀
  linarith

/-- **Hives in the stable range are Gelfand-Tsetlin patterns.** Under the uniform input gap
`λᵣ - λᵣ₊₁ ≥ μ₀ - μₙ`, the integer hives with boundary `(λ, μ, γ*)` correspond to all
Gelfand-Tsetlin patterns with top row `μ` and weight `γ - λ`. -/
def fixedIntegerHiveEquivGTPatternOfGap (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans <| Equiv.subtypeEquivRight fun P =>
    ⟨fun hP => ⟨hP.1, hP.2.1⟩, fun hP => ⟨hP.1, hP.2,
      gtCompletionConcave_of_gap lam.1 P (by simpa only [hP.1] using hGap)⟩⟩

@[simp]
theorem fixedIntegerHiveEquivGTPatternOfGap_apply_coe (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap h : GTPattern (n + 1)) =
      h.1.toGTPattern := (rfl)

/-- The inverse of the stable-range equivalence is the chart completion of `λ` and the pattern. -/
@[simp]
theorem fixedIntegerHiveEquivGTPatternOfGap_symm_apply_apply (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1}) (v : Vertex (n + 1)) :
    ((fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap).symm P).1 v =
      gtCompletion lam.1 P.1 v.z (n + 1 - v.x) := (rfl)

/-- Under the uniform input gap, the hive count of `(λ, μ, γ*)` is the number of Gelfand-Tsetlin
patterns with top row `μ` and weight `γ - λ`. -/
theorem hiveCount_eq_card_gtPattern_of_gap (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap)

end TauCeti.Hive
