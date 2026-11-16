/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.BigOperators.Finset.PartialSum
public import TauCeti.Combinatorics.Hive.Fibre
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.AddMonoid

/-!
# Directional differences of integer hives

In the triangular chart `H(i,j) = h(n-j,j-i,i)`, the differences
`H(i+1,j) - H(i,j)` form a signed Gelfand–Tsetlin pattern. Two families of hive
rhombi give the two interlacing inequalities. The top row is the second clockwise
boundary, and the pattern together with the first boundary reconstructs every hive value.
Consequently the difference map is injective on hives with a fixed first boundary.

The construction uses normalized hives and the native pattern's convention of zero
entries outside `i < j ≤ n`. The third rhombus family imposes an additional condition on the
image, the predicate `GTCompletionConcave`: the completion of a pattern is a hive exactly when
it satisfies this third family. This identifies the integer hives with boundary `(λ, μ, γ*)`
with the patterns of top row `μ` and weight `γ - λ` whose completion satisfies the third family.
When every adjacent gap of `λ` is at least `μ₀ - μₙ₋₁`, the third family holds automatically,
so these hives correspond to all patterns of top row `μ` and weight `γ - λ`.

## Main results

* `toGTPattern`, `topRow_toGTPattern`, and `rowWeight_toGTPattern` give the directional
  pattern and its boundary weights. The specializations `topRow_toGTPattern_of_productBoundary`
  and `rowWeight_toGTPattern_of_productBoundary` give the signed product-boundary convention.
* `gtCompletion` integrates row prefixes; its edge and `boundaryLinear` equations
  describe the three boundaries without imposing rhombus concavity.
* `gtCompletion_toGTPattern` and `toGTPattern_eq_of_coe_eq_gtCompletion` are the two
  inverse laws when the lattice function is a hive.
* `sum_toGTPattern_sub_le` records the third rhombus family's necessary image condition.
* `isRhombusConcave_gtCompletion_iff`: a completion is rhombus-concave iff it satisfies
  `GTCompletionConcave`; `ofGTPattern` is the resulting hive.
* `exists_fixedIntegerHive_eq_gtCompletion_iff` and `fixedIntegerHiveEquivGTPattern`: a pattern
  of top row `μ` and weight `γ - λ` is the pattern of a hive with boundary `(λ, μ, γ*)` iff its
  completion satisfies the third family, and the fixed-boundary fibre is equivalent to these
  patterns.
* `gtCompletionConcave_of_gap`, `fixedIntegerHiveEquivGTPatternOfGap` and
  `hiveCount_eq_natCard_gtPattern_of_gap`: under the uniform input gap the third family is
  automatic, and the hive count is a count of Gelfand–Tsetlin patterns.

## References

* A. Henriques and J. Kamnitzer, *The octahedron recurrence and gl(n) crystals*,
  Adv. Math. **206** (2006), 211–249, Theorem 7.4 (the quasi-hive comparison).
* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999),
  1055–1090, Appendix 2 (hive coordinates and rhombus inequalities).
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

variable {n : ℕ}

open Vertex (chart chart_zero chart_self chart_top)

/-- The signed Gelfand–Tsetlin pattern obtained by taking consecutive differences
along the lines of constant first barycentric coordinate. -/
def toGTPattern (h : IntegerHive n) : GTPattern n where
  entry i j := if hij : i < j ∧ j ≤ n then
    h (chart n (i + 1) j (by omega) hij.2) - h (chart n i j (by omega) hij.2)
    else 0
  zeros' hz := by
    rw [dite_eq_right (by omega)]
  interlacing' hij hj := by
    rw [dite_eq_left ⟨hij, by omega⟩, dite_eq_left ⟨by omega, by omega⟩,
      dite_eq_left ⟨by omega, by omega⟩]
    exact ⟨by linarith [h.le_of_isRhombus (isRhombus_chart_left hij hj)],
      by linarith [h.le_of_isRhombus (isRhombus_chart_right hij hj)]⟩

/-- On an informative cell, the pattern is the difference
`h(n-j,j-(i+1),i+1) - h(n-j,j-i,i)`. -/
@[simp] theorem toGTPattern_apply (h : IntegerHive n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) :
    h.toGTPattern i j =
      h (chart n (i + 1) j (by omega) hj) - h (chart n i j (by omega) hj) := by
  simp only [← GTPattern.entry_eq_coe, toGTPattern]
  rw [dite_eq_left ⟨hij, hj⟩]

/-- The top row of the directional pattern is the hive's second clockwise boundary. -/
@[simp high] theorem topRow_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topRow = h.boundary 1 := by
  funext ⟨i, hi⟩
  rw [GTPattern.topRow_apply, toGTPattern_apply h hi le_rfl,
    chart_top _ (by omega), chart_top _ (by omega), boundary_apply,
    Fin.succ_mk, Fin.castSucc_mk]

/-- The top weight of the directional pattern is the second boundary weight. -/
@[simp] theorem topWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topWeight = h.boundaryWeight 1 := by
  apply Subtype.ext
  simpa only [GTPattern.topWeight_coe, coe_boundaryWeight] using topRow_toGTPattern h

/-- The directional difference map preserves the zero hive. -/
@[simp] theorem toGTPattern_zero : (0 : IntegerHive n).toGTPattern = 0 := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · simp [toGTPattern_apply _ hij.1 hij.2, GTPattern.zero_apply]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.zero_apply]

/-- Directional differences commute with addition of hives. -/
@[simp] theorem toGTPattern_add (h k : IntegerHive n) :
    (h + k).toGTPattern = h.toGTPattern + k.toGTPattern := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · simp only [toGTPattern_apply _ hij.1 hij.2, add_apply, GTPattern.add_apply]
    abel
  · rw [GTPattern.add_apply, GTPattern.entry_eq_zero _ (by omega),
      GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega), zero_add]

/-- Directional finite differences, as an additive monoid homomorphism. -/
def toGTPatternHom (n : ℕ) : IntegerHive n →+ GTPattern n where
  toFun := toGTPattern
  map_zero' := toGTPattern_zero
  map_add' := toGTPattern_add

/-- Evaluation of the additive directional difference map. -/
@[simp] theorem toGTPatternHom_apply (h : IntegerHive n) :
    toGTPatternHom n h = h.toGTPattern := (rfl)

/-- Directional differences commute with natural-number scaling. -/
@[simp] theorem toGTPattern_nsmul (k : ℕ) (h : IntegerHive n) :
    (k • h).toGTPattern = k • h.toGTPattern :=
  (toGTPatternHom n).map_nsmul k h

/-- A row prefix of directional differences telescopes to the corresponding hive values. -/
theorem sum_toGTPattern_chart (h : IntegerHive n) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
      h (chart n i j hij hj) - h (chart n 0 j (Nat.zero_le _) hj) := by
  let f : ℕ → ℤ := fun k => h (chart n (min k j) j (Nat.min_le_right _ _) hj)
  calc
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
        ∑ k ∈ Finset.range i, (f (k + 1) - f k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < i := Finset.mem_range.mp hk
      rw [toGTPattern_apply h (by omega) hj]
      simp only [f, Nat.min_eq_left (by omega : k + 1 ≤ j),
        Nat.min_eq_left (by omega : k ≤ j)]
    _ = f i - f 0 := Finset.sum_range_sub f i
    _ = _ := by simp [f, Nat.min_eq_left hij]

/-- Complete a pattern to a triangular lattice function by integrating its rows,
with the prescribed sequence on the first boundary. No rhombus condition on this
function is imposed by the definition. -/
def gtCompletion (lam : Fin n → ℤ) (P : GTPattern n) (p : Vertex n) : ℤ :=
  (∑ r : Fin n with r.val < p.y + p.z, lam r) +
    ∑ k ∈ Finset.range p.z, P k (p.y + p.z)

/-- The prefix formula defining the completion, in the original barycentric coordinates. -/
theorem gtCompletion_apply (lam : Fin n → ℤ) (P : GTPattern n) (p : Vertex n) :
    gtCompletion lam P p = (∑ r : Fin n with r.val < p.y + p.z, lam r) +
      ∑ k ∈ Finset.range p.z, P k (p.y + p.z) := (rfl)

/-- In triangular coordinates, completion adds the first-boundary prefix of
length `j` and the pattern-row prefix of length `i`. -/
theorem gtCompletion_chart (lam : Fin n → ℤ) (P : GTPattern n) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion lam P (chart n i j hij hj) =
      (∑ r : Fin n with r.val < j, lam r) + ∑ k ∈ Finset.range i, P k j := by
  rw [gtCompletion_apply]
  simp only [Vertex.chart_y, Vertex.chart_z]
  rw [Nat.sub_add_cancel hij]

/-- Consecutive directional differences of a completion recover the original
pattern on every informative cell, independently of the first boundary. -/
theorem gtCompletion_sub_gtCompletion (lam : Fin n → ℤ) (P : GTPattern n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) :
    gtCompletion lam P (chart n (i + 1) j (by omega) hj) -
      gtCompletion lam P (chart n i j (by omega) hj) = P i j := by
  rw [gtCompletion_chart lam P (by omega) hj, gtCompletion_chart lam P (by omega) hj,
    Finset.sum_range_succ]
  abel

/-- A hive whose lattice function is a completion has the original pattern. -/
theorem toGTPattern_eq_of_coe_eq_gtCompletion {lam : Fin n → ℤ} {P : GTPattern n}
    {h : IntegerHive n} (heq : ⇑h = gtCompletion lam P) : h.toGTPattern = P := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · rw [toGTPattern_apply h hij.1 hij.2, congrFun heq, congrFun heq,
      gtCompletion_sub_gtCompletion lam P hij.1 hij.2]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega)]

/-- A completion is normalized at the first corner. -/
@[simp] theorem gtCompletion_cornerA (lam : Fin n → ℤ) (P : GTPattern n) :
    gtCompletion lam P (Vertex.cornerA n) = 0 := by
  simp [gtCompletion_apply]

/-- On the first edge, completion has the prescribed boundary prefixes. -/
theorem gtCompletion_edgePoint_zero (lam : Fin n → ℤ) (P : GTPattern n)
    (r : Fin (n + 1)) :
    gtCompletion lam P (Vertex.edgePoint n 0 r) =
      ∑ k : Fin n with k.val < r.val, lam k := by
  simp [gtCompletion_apply]

/-- On the second edge, completion integrates the top row after the first boundary. -/
theorem gtCompletion_edgePoint_one (lam : Fin n → ℤ) (P : GTPattern n)
    (r : Fin (n + 1)) :
    gtCompletion lam P (Vertex.edgePoint n 1 r) =
      (∑ k : Fin n, lam k) + ∑ k ∈ Finset.range r.val, P k n := by
  rw [gtCompletion_apply]
  simp only [Vertex.edgePoint_one_y, Vertex.edgePoint_one_z,
    Nat.sub_add_cancel (by omega : r.val ≤ n)]
  simp

/-- At index `r` on the third edge, completion adds the first-boundary prefix of length
`n - r` and the full sum of row `n - r` of the pattern. -/
theorem gtCompletion_edgePoint_two (lam : Fin n → ℤ) (P : GTPattern n)
    (r : Fin (n + 1)) :
    gtCompletion lam P (Vertex.edgePoint n 2 r) =
      (∑ k : Fin n with k.val < n - r.val, lam k) +
        ∑ k ∈ Finset.range (n - r.val), P k (n - r.val) := by
  simp [gtCompletion_apply]

/-- The first clockwise boundary of a completion is its prescribed sequence. -/
@[simp high] theorem boundaryLinear_gtCompletion_zero (lam : Fin n → ℤ) (P : GTPattern n) :
    boundaryLinear ℤ n ℤ (gtCompletion lam P) 0 = lam := by
  funext r
  have hs := prefixSum_succ r.isLt lam
  rw [prefixSum_def, prefixSum_def] at hs
  simp only [boundaryLinear_apply, gtCompletion_edgePoint_zero, Fin.val_succ,
    Fin.val_castSucc, hs, add_sub_cancel_left]

/-- The second clockwise boundary of a completion is the top row. -/
@[simp high] theorem boundaryLinear_gtCompletion_one (lam : Fin n → ℤ) (P : GTPattern n) :
    boundaryLinear ℤ n ℤ (gtCompletion lam P) 1 = P.topRow := by
  funext r
  simp only [boundaryLinear_apply, gtCompletion_edgePoint_one, Fin.val_succ,
    Fin.val_castSucc, Finset.sum_range_succ, GTPattern.topRow_apply]
  abel

/-- The third clockwise boundary is determined by the reversed row weight and first boundary. -/
@[simp high] theorem boundaryLinear_gtCompletion_two (lam : Fin n → ℤ) (P : GTPattern n) :
    boundaryLinear ℤ n ℤ (gtCompletion lam P) 2 =
      fun r => -P.rowWeight r.rev - lam r.rev := by
  funext r
  rw [boundaryLinear_apply, gtCompletion_edgePoint_two, gtCompletion_edgePoint_two,
    GTPattern.rowWeight_apply]
  have hsucc : n - r.castSucc.val = r.rev.val + 1 := by simp; omega
  have hcast : n - r.succ.val = r.rev.val := by simp
  have hs := prefixSum_succ r.rev.isLt lam
  rw [prefixSum_def, prefixSum_def] at hs
  rw [hsucc, hcast, hs]
  abel

/-- A completion has product boundary exactly as prescribed by its top row and row weight. -/
theorem boundaryLinear_gtCompletion_of_topRow_of_rowWeight
    {lam μ γ : DominantWeight n} {P : GTPattern n}
    (htop : P.topRow = μ.1) (hweight : P.rowWeight = γ.1 - lam.1) :
    boundaryLinear ℤ n ℤ (gtCompletion lam.1 P) = productBoundary lam μ γ := by
  funext s
  fin_cases s <;> simp [htop, hweight, funext_iff]

/-- Corner-normalizing a rhombus-concave completion leaves its underlying lattice
function unchanged. -/
@[simp] theorem coe_ofRhombusConcave_gtCompletion (lam : Fin n → ℤ) (P : GTPattern n)
    (hf : IsRhombusConcave (gtCompletion lam P)) :
    ⇑(ofRhombusConcave (gtCompletion lam P) hf) = gtCompletion lam P := by
  funext p
  simp

/-- Normalizing a rhombus-concave completion preserves its original pattern. -/
@[simp] theorem toGTPattern_ofRhombusConcave_gtCompletion (lam : Fin n → ℤ) (P : GTPattern n)
    (hf : IsRhombusConcave (gtCompletion lam P)) :
    (ofRhombusConcave (gtCompletion lam P) hf).toGTPattern = P := by
  exact toGTPattern_eq_of_coe_eq_gtCompletion (coe_ofRhombusConcave_gtCompletion lam P hf)

/-- Bundling a rhombus-concave completion preserves its original pattern. -/
@[simp] theorem toGTPattern_mk_gtCompletion (lam : Fin n → ℤ) (P : GTPattern n)
    (hf : ∀ {a b c d : Vertex n}, IsRhombus a b c d →
      gtCompletion lam P b + gtCompletion lam P d ≤
        gtCompletion lam P a + gtCompletion lam P c) :
    (Hive.mk (gtCompletion lam P) (gtCompletion_cornerA lam P) hf).toGTPattern = P := by
  exact toGTPattern_eq_of_coe_eq_gtCompletion (coe_mk _ _ _)

/-- Completing zero data gives the zero lattice function. -/
@[simp↓] theorem gtCompletion_zero : gtCompletion (0 : Fin n → ℤ) 0 = 0 := by
  funext p
  simp [gtCompletion_apply, GTPattern.zero_apply]

/-- Completion commutes with addition of its boundary and pattern data. -/
@[simp] theorem gtCompletion_add (lam μ : Fin n → ℤ) (P Q : GTPattern n) :
    gtCompletion (lam + μ) (P + Q) = gtCompletion lam P + gtCompletion μ Q := by
  funext p
  simp only [gtCompletion_apply, Pi.add_apply, GTPattern.add_apply, Finset.sum_add_distrib]
  abel

/-- Completion commutes with natural-number scaling of its data. -/
theorem gtCompletion_nsmul (k : ℕ) (lam : Fin n → ℤ) (P : GTPattern n) :
    gtCompletion (k • lam) (k • P) = k • gtCompletion lam P := by
  funext p
  simp only [gtCompletion_apply, Pi.smul_apply, GTPattern.nsmul_apply,
    ← Finset.smul_sum, smul_add]

/-- Completion commutes with scaling in the pointwise ring normal form. -/
@[simp] theorem gtCompletion_natCast_mul_nsmul (k : ℕ) (lam : Fin n → ℤ) (P : GTPattern n) :
    gtCompletion ((k : Fin n → ℤ) * lam) (k • P) =
      (k : Vertex n → ℤ) * gtCompletion lam P := by
  simpa only [nsmul_eq_mul] using gtCompletion_nsmul k lam P

/-- Every hive value is the prefix of the first boundary followed by the prefix
of the corresponding row of its directional pattern. -/
theorem apply_eq_sum_boundary_zero_add_sum_toGTPattern (h : IntegerHive n) (p : Vertex n) :
    h p = (∑ r : Fin n with r.val < p.y + p.z, h.boundary 0 r) +
      ∑ k ∈ Finset.range p.z, h.toGTPattern k (p.y + p.z) := by
  have hj : p.y + p.z ≤ n := by have := p.sum_eq; omega
  have hs := sum_toGTPattern_chart h (i := p.z) (j := p.y + p.z) (by omega) hj
  rw [Vertex.chart_z_y_add_z, chart_zero, apply_edgePoint_zero] at hs
  exact eq_add_of_sub_eq' hs.symm

/-- Integrating the directional pattern with the hive's first boundary recovers
the original normalized hive as a lattice function. -/
@[simp] theorem gtCompletion_toGTPattern (h : IntegerHive n) :
    gtCompletion (h.boundary 0) h.toGTPattern = ⇑h := by
  funext p
  rw [gtCompletion_apply, ← apply_eq_sum_boundary_zero_add_sum_toGTPattern]

/-- A hive is determined by its first boundary and its directional pattern. -/
theorem eq_of_boundary_zero_eq_of_toGTPattern_eq {h k : IntegerHive n}
    (hb : h.boundary 0 = k.boundary 0) (hP : h.toGTPattern = k.toGTPattern) : h = k := by
  apply DFunLike.coe_injective
  rw [← gtCompletion_toGTPattern h, ← gtCompletion_toGTPattern k, hb, hP]

/-- Recording the first boundary together with the directional pattern is injective. -/
theorem boundary_zero_toGTPattern_injective :
    Function.Injective (fun h : IntegerHive n => (h.boundary 0, h.toGTPattern)) := by
  intro h k heq
  exact eq_of_boundary_zero_eq_of_toGTPattern_eq (congrArg Prod.fst heq) (congrArg Prod.snd heq)

/-- The directional map is injective on the hives having any prescribed first boundary. -/
theorem toGTPattern_subtype_boundary_zero_injective (lam : Fin n → ℤ) :
    Function.Injective (fun h : {h : IntegerHive n // h.boundary 0 = lam} =>
      h.1.toGTPattern) := by
  intro h k hP
  exact Subtype.ext (eq_of_boundary_zero_eq_of_toGTPattern_eq (h.2.trans k.2.symm) hP)

/-- The difference between consecutive row sums is the negative reversed third
boundary minus the first boundary. This is the signed pattern weight in cyclic
hive coordinates. -/
@[simp] theorem rowWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.rowWeight = fun r => -h.boundary 2 r.rev - h.boundary 0 r := by
  funext r
  have hb := congrFun (boundaryLinear_gtCompletion_two (h.boundary 0) h.toGTPattern) r.rev
  simp only [gtCompletion_toGTPattern, boundaryLinear_coe, Fin.rev_rev] at hb
  omega

/-- In product boundary convention, the top row of the directional pattern is `μ`. -/
theorem topRow_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    h.toGTPattern.topRow = μ.1 := by
  rw [topRow_toGTPattern, hb, productBoundary_one]

/-- In product boundary convention, the directional pattern has highest weight `μ`. -/
theorem topWeight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    h.toGTPattern.topWeight = μ := by
  apply Subtype.ext
  simpa only [GTPattern.topWeight_coe] using topRow_toGTPattern_of_productBoundary hb

/-- In product boundary convention, the pattern has weight `γ - λ`:
the difference of the row sums of lengths `r+1` and `r` is `γᵣ - λᵣ`. -/
theorem rowWeight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    h.toGTPattern.rowWeight = γ.1 - lam.1 := by
  ext r
  simp [rowWeight_toGTPattern, hb]

/-- The third rhombus family imposes an additional necessary inequality on the
directional pattern. Unlike interlacing, it involves the first hive boundary. -/
theorem sum_toGTPattern_sub_le (h : IntegerHive n) {i j : ℕ}
    (hij : i ≤ j) (hj : j + 2 ≤ n) :
    (∑ k ∈ Finset.range (i + 1),
      (h.toGTPattern k (j + 2) - h.toGTPattern k (j + 1))) ≤
        h.boundary 0 ⟨j, by omega⟩ - h.boundary 0 ⟨j + 1, by omega⟩ +
          ∑ k ∈ Finset.range i, (h.toGTPattern k (j + 1) - h.toGTPattern k j) := by
  have hb (k : ℕ) (hk : k < n) : h.boundary 0 ⟨k, hk⟩ =
      h (chart n 0 (k + 1) (by omega) (by omega)) -
        h (chart n 0 k (by omega) (by omega)) := by
    rw [chart_zero, chart_zero, boundary_apply, Fin.succ_mk, Fin.castSucc_mk]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith [hb j (by omega), hb (j + 1) (by omega),
    h.le_of_isRhombus (isRhombus_chart_step hij hj),
    sum_toGTPattern_chart h hij (by omega),
    sum_toGTPattern_chart h (i := i) (j := j + 1) (by omega) (by omega),
    sum_toGTPattern_chart h (i := i + 1) (j := j + 1) (by omega) (by omega),
    sum_toGTPattern_chart h (i := i + 1) (j := j + 2) (by omega) hj]

/-- For product boundary `(λ, μ, γ*)`, the third rhombus family imposes this necessary
inequality on the directional pattern in terms of `λ`. -/
theorem sum_toGTPattern_sub_le_of_productBoundary
    {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) {i j : ℕ}
    (hij : i ≤ j) (hj : j + 2 ≤ n) :
    (∑ k ∈ Finset.range (i + 1),
      (h.toGTPattern k (j + 2) - h.toGTPattern k (j + 1))) ≤
        lam.1 ⟨j, by omega⟩ - lam.1 ⟨j + 1, by omega⟩ +
          ∑ k ∈ Finset.range i, (h.toGTPattern k (j + 1) - h.toGTPattern k j) := by
  simpa [hb] using sum_toGTPattern_sub_le h hij hj

/-- A hive in product convention is recovered from `λ` and the prefix sums of
its directional pattern, without any positivity assumption on the weights. -/
theorem apply_eq_sum_add_sum_toGTPattern_of_productBoundary
    {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (p : Vertex n) :
    h p = (∑ r : Fin n with r.val < p.y + p.z, lam.1 r) +
      ∑ k ∈ Finset.range p.z, h.toGTPattern k (p.y + p.z) := by
  simpa [hb] using apply_eq_sum_boundary_zero_add_sum_toGTPattern h p

/-- Affine hives yield constant signed patterns: the first boundary value is
subtracted from the third-coordinate slope. -/
@[simp] theorem toGTPattern_affine (β γ : ℤ) :
    (affine n β γ).toGTPattern = GTPattern.const n (γ - β) := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · rw [toGTPattern_apply _ hij.1 hij.2,
      GTPattern.const_apply_of_lt_of_le _ hij.1 hij.2]
    have hy : j - i = (j - (i + 1)) + 1 := by omega
    simp only [affine_apply, Vertex.chart_y, Vertex.chart_z]
    rw [hy]
    simp only [add_nsmul, one_nsmul]
    abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega)]

/-- A constant first boundary and constant pattern integrate to an affine hive. -/
@[simp] theorem gtCompletion_const (β m : ℤ) :
    gtCompletion (fun _ : Fin n => β) (GTPattern.const n m) = ⇑(affine n β (β + m)) := by
  have h := gtCompletion_toGTPattern (affine n β (β + m))
  simpa using h

/-! ### The third rhombus family and the hive of a pattern -/

/-- The completion of `lam` and `P` satisfies the third family of rhombus inequalities
`c(i, j) + c(i+1, j+2) ≤ c(i, j+1) + c(i+1, j+1)` in the triangular chart, for `i ≤ j` and
`j + 2 ≤ n`. The completion always satisfies the other two families, which are the interlacing
inequalities of `P`, so this is its rhombus concavity (`isRhombusConcave_gtCompletion_iff`). -/
def GTCompletionConcave (lam : Fin n → ℤ) (P : GTPattern n) : Prop :=
  ∀ ⦃i j : ℕ⦄ (hij : i ≤ j) (hj : j + 2 ≤ n),
    gtCompletion lam P (chart n i j hij (by omega)) +
        gtCompletion lam P (chart n (i + 1) (j + 2) (by omega) hj) ≤
      gtCompletion lam P (chart n i (j + 1) (by omega) (by omega)) +
        gtCompletion lam P (chart n (i + 1) (j + 1) (by omega) (by omega))

/-- The completion of any pattern satisfies the first two families of rhombus inequalities, its
interlacing inequalities; so it is rhombus-concave iff it satisfies the third family. -/
theorem isRhombusConcave_gtCompletion_iff (lam : Fin n → ℤ) (P : GTPattern n) :
    IsRhombusConcave (gtCompletion lam P) ↔ GTCompletionConcave lam P := by
  have hc : gtCompletion lam P = fun v : Vertex n =>
      (∑ r : Fin n with r.val < n - v.x, lam r) + ∑ k ∈ Finset.range v.z, P k (n - v.x) := by
    funext v
    have := v.sum_eq
    rw [gtCompletion_apply, show n - v.x = v.y + v.z by omega]
  rw [hc]
  refine (isRhombusConcave_chart_iff
    (fun i j => (∑ r : Fin n with r.val < j, lam r) + ∑ k ∈ Finset.range i, P k j)).trans ?_
  simp only [GTCompletionConcave, gtCompletion_chart]
  refine ⟨fun h => h.2.2, fun h => ⟨fun i j hij hj => ?_, fun i j _ hj => ?_, h⟩⟩
  · have := P.entry_le_entry_succ_row hij hj
    simp only [Finset.sum_range_succ]
    linarith
  · have := P.entry_succ_succ_le_entry (i := i) hj
    simp only [Finset.sum_range_succ]
    linarith

/-- The completion of the pattern of an integer hive with its first boundary satisfies the third
family of rhombus inequalities. -/
theorem gtCompletionConcave_toGTPattern (h : IntegerHive n) :
    GTCompletionConcave (h.boundary 0) h.toGTPattern :=
  (isRhombusConcave_gtCompletion_iff _ _).mp (by
    rw [gtCompletion_toGTPattern]
    exact h.isRhombusConcave)

/-- The integer hive whose values are the completion of a boundary `lam` and a pattern `P`
satisfying the third family of rhombus inequalities. -/
def ofGTPattern (lam : Fin n → ℤ) (P : GTPattern n) (hP : GTCompletionConcave lam P) :
    IntegerHive n :=
  Hive.mk (gtCompletion lam P) (gtCompletion_cornerA lam P) fun hr =>
    (isRhombusConcave_def _).mp ((isRhombusConcave_gtCompletion_iff lam P).mpr hP) hr

/-- The values of the hive of a pattern are its completion. -/
@[simp] theorem coe_ofGTPattern (lam : Fin n → ℤ) (P : GTPattern n)
    (hP : GTCompletionConcave lam P) : ⇑(ofGTPattern lam P hP) = gtCompletion lam P :=
  (rfl)

/-- The pattern of the hive of a pattern is the pattern itself. -/
@[simp] theorem toGTPattern_ofGTPattern (lam : Fin n → ℤ) (P : GTPattern n)
    (hP : GTCompletionConcave lam P) : (ofGTPattern lam P hP).toGTPattern = P :=
  toGTPattern_eq_of_coe_eq_gtCompletion (coe_ofGTPattern lam P hP)

/-- An integer hive is the hive of its first boundary and its pattern. -/
@[simp] theorem ofGTPattern_toGTPattern (h : IntegerHive n) :
    ofGTPattern (h.boundary 0) h.toGTPattern h.gtCompletionConcave_toGTPattern = h :=
  DFunLike.coe_injective (by rw [coe_ofGTPattern, gtCompletion_toGTPattern])

/-- The clockwise boundary of the hive of a pattern is that of its completion. -/
@[simp] theorem boundary_ofGTPattern (lam : Fin n → ℤ) (P : GTPattern n)
    (hP : GTCompletionConcave lam P) :
    (ofGTPattern lam P hP).boundary = boundaryLinear ℤ n ℤ (gtCompletion lam P) := by
  rw [← boundaryLinear_coe ℤ, coe_ofGTPattern]

/-! ### Fixed-boundary fibres as Gelfand–Tsetlin fibres -/

section ProductBoundary

/-- The hive of a pattern with top row `μ` and weight `γ - λ` has boundary `(λ, μ, γ*)`. -/
theorem boundary_ofGTPattern_of_topRow_of_rowWeight {lam μ γ : DominantWeight n}
    {P : GTPattern n} {hP : GTCompletionConcave lam.1 P}
    (htop : P.topRow = μ.1) (hweight : P.rowWeight = γ.1 - lam.1) :
    (ofGTPattern lam.1 P hP).boundary = productBoundary lam μ γ := by
  rw [boundary_ofGTPattern]
  exact boundaryLinear_gtCompletion_of_topRow_of_rowWeight htop hweight

/-- A hive with boundary `(λ, μ, γ*)` is the completion of `λ` and its pattern. -/
theorem gtCompletion_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    gtCompletion lam.1 h.toGTPattern = ⇑h := by
  have := gtCompletion_toGTPattern h
  rwa [hb, productBoundary_zero] at this

variable (lam μ γ : DominantWeight n)

/-- **Fixed-boundary hives are Gelfand–Tsetlin patterns.** The integer hives with clockwise
boundary `(λ, μ, γ*)` correspond to the Gelfand–Tsetlin patterns with top row `μ` and weight
`γ - λ` whose completion satisfies the third family of rhombus inequalities. The forward map is
`toGTPattern`, the inverse the completion `ofGTPattern`. -/
def fixedIntegerHiveEquivGTPattern :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1 ∧
        GTCompletionConcave lam.1 P} where
  toFun h := ⟨h.1.toGTPattern, topRow_toGTPattern_of_productBoundary h.2,
    rowWeight_toGTPattern_of_productBoundary h.2, by
      simpa only [h.2, productBoundary_zero] using h.1.gtCompletionConcave_toGTPattern⟩
  invFun P := ⟨ofGTPattern lam.1 P.1 P.2.2.2,
    boundary_ofGTPattern_of_topRow_of_rowWeight P.2.1 P.2.2.1⟩
  left_inv h := Subtype.ext <| DFunLike.coe_injective <| by
    rw [coe_ofGTPattern]
    exact gtCompletion_toGTPattern_of_productBoundary h.2
  right_inv P := Subtype.ext (toGTPattern_ofGTPattern lam.1 P.1 P.2.2.2)

@[simp]
theorem fixedIntegerHiveEquivGTPattern_apply_coe (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h : GTPattern n) = h.1.toGTPattern := (rfl)

/-- The inverse of the fixed-boundary equivalence is the completion of `λ` and the pattern. -/
@[simp]
theorem fixedIntegerHiveEquivGTPattern_symm_apply_apply
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1 ∧
      GTCompletionConcave lam.1 P}) (v : Vertex n) :
    ((fixedIntegerHiveEquivGTPattern lam μ γ).symm P).1 v = gtCompletion lam.1 P.1 v := (rfl)

/-- **Reconstruction of a hive from its pattern.** A Gelfand–Tsetlin pattern with top row `μ` and
weight `γ - λ` is the difference pattern of a hive with boundary `(λ, μ, γ*)`, namely of its
completion, iff the completion satisfies the third family of rhombus inequalities. -/
theorem exists_fixedIntegerHive_eq_gtCompletion_iff (P : GTPattern n) (htop : P.topRow = μ.1)
    (hweight : P.rowWeight = γ.1 - lam.1) :
    (∃ h : FixedIntegerHive (productBoundary lam μ γ), ⇑h.1 = gtCompletion lam.1 P) ↔
      GTCompletionConcave lam.1 P :=
  ⟨fun ⟨h, hv⟩ => (isRhombusConcave_gtCompletion_iff _ _).mp (hv ▸ h.1.isRhombusConcave),
    fun hP => ⟨⟨ofGTPattern lam.1 P hP, boundary_ofGTPattern_of_topRow_of_rowWeight htop hweight⟩,
      coe_ofGTPattern lam.1 P hP⟩⟩

end ProductBoundary

/-! ### The uniform input gap -/

/-- **The uniform input gap makes the third family automatic.** If every adjacent gap
`lamᵣ - lamᵣ₊₁` of the boundary `lam` is at least the spread `μ₀ - μₙ` of the top row `μ` of a
pattern `P`, then the completion of `lam` and `P` satisfies the third family of rhombus
inequalities. -/
theorem gtCompletionConcave_of_gap (lam : Fin (n + 1) → ℤ) (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ lam r.castSucc - lam r.succ) :
    GTCompletionConcave lam P := by
  intro i j hij hj
  simp only [gtCompletion_chart]
  -- The boundary prefixes contribute `lam (j + 1) - lam j`.
  have hl₁ := prefixSum_succ (by omega : j < n + 1) lam
  have hl₂ : prefixSum (j + 2) lam = prefixSum (j + 1) lam + lam ⟨j + 1, by omega⟩ :=
    prefixSum_succ (by omega) lam
  rw [prefixSum_def, prefixSum_def] at hl₁ hl₂
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
  simp only [Finset.sum_sub_distrib] at hB
  simp only [Fin.zero_eta] at h₀
  linarith

/-- **Hives in the stable range are Gelfand–Tsetlin patterns.** Under the uniform input gap
`λᵣ - λᵣ₊₁ ≥ μ₀ - μₙ`, the integer hives with boundary `(λ, μ, γ*)` correspond to all
Gelfand–Tsetlin patterns with top row `μ` and weight `γ - λ`. -/
def fixedIntegerHiveEquivGTPatternOfGap (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans <| Equiv.subtypeEquivRight fun P =>
    ⟨fun hP => ⟨hP.1, hP.2.1⟩, fun hP => ⟨hP.1, hP.2,
      gtCompletionConcave_of_gap lam.1 P (by simpa only [hP.1] using hGap)⟩⟩

@[simp]
theorem fixedIntegerHiveEquivGTPatternOfGap_apply_coe (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap h : GTPattern (n + 1)) =
      h.1.toGTPattern := (rfl)

/-- The inverse of the stable-range equivalence is the completion of `λ` and the pattern. -/
@[simp]
theorem fixedIntegerHiveEquivGTPatternOfGap_symm_apply_apply (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (P : {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1})
    (v : Vertex (n + 1)) :
    ((fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap).symm P).1 v =
      gtCompletion lam.1 P.1 v := (rfl)

/-- Under the uniform input gap, the hive count of `(λ, μ, γ*)` is the number of Gelfand–Tsetlin
patterns with top row `μ` and weight `γ - λ`. -/
theorem hiveCount_eq_natCard_gtPattern_of_gap (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap)

end TauCeti.Hive
