/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.AddMonoid

/-!
# Directional differences of integer hives

In the triangular chart `H(i,j) = h(n-j,j-i,i)`, the differences
`H(i+1,j) - H(i,j)` form a signed Gelfand–Tsetlin pattern. Two families of hive
rhombi give the two interlacing inequalities. The top row is the second clockwise
boundary, and the pattern together with the first boundary reconstructs every hive value.
Consequently the difference map is injective on hives with a fixed first boundary.

The construction uses normalized hives and the native pattern's convention of zero
entries outside `i < j ≤ n`. It is a directional comparison: the third rhombus family
imposes an additional condition on the image, so no surjectivity onto all patterns is asserted.

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

private def chart (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) : Vertex n :=
  ⟨n - j, j - i, i, by omega⟩

private theorem chart_zero (j : ℕ) (hj : j ≤ n) :
    chart n 0 j (Nat.zero_le _) hj = Vertex.edgePoint n 0 ⟨j, by omega⟩ := by
  ext <;> simp [chart]

private theorem chart_self (j : ℕ) (hj : j ≤ n) :
    chart n j j le_rfl hj = Vertex.edgePoint n 2 ⟨n - j, by omega⟩ := by
  ext <;> simp [chart]; omega

private theorem chart_top (i : ℕ) (hi : i ≤ n) :
    chart n i n hi le_rfl = Vertex.edgePoint n 1 ⟨i, by omega⟩ := by
  ext <;> simp [chart]

private theorem chart_rhombus_left {i j : ℕ} (hij : i < j) (hj : j < n) :
    IsRhombus (chart n i j (by omega) (by omega))
      (chart n (i + 1) j (by omega) (by omega))
      (chart n (i + 1) (j + 1) (by omega) (by omega))
      (chart n i (j + 1) (by omega) (by omega)) := by
  let v : Fin 3 → ℤ := ![0, 1, -1]
  let w : Fin 3 → ℤ := ![-1, 1, 0]
  have hv : IsUnitStep v := by norm_num [isUnitStep_iff, v, Fin.sum_univ_three]
  have hw : IsUnitStep w := by norm_num [isUnitStep_iff, w, Fin.sum_univ_three]
  apply (isRhombus_of_hasStep_iff hv hw ?_ ?_ ?_).mpr
    (by norm_num [v, w, Fin.sum_univ_three])
  all_goals
    rw [hasStep_iff]
    intro k
    fin_cases k <;> simp [chart, v, w] <;> omega

private theorem chart_rhombus_right {i j : ℕ} (hij : i < j) (hj : j < n) :
    IsRhombus (chart n (i + 1) j (by omega) (by omega))
      (chart n i j (by omega) (by omega))
      (chart n (i + 1) (j + 1) (by omega) (by omega))
      (chart n (i + 2) (j + 1) (by omega) (by omega)) := by
  let v : Fin 3 → ℤ := ![0, -1, 1]
  let w : Fin 3 → ℤ := ![-1, 0, 1]
  have hv : IsUnitStep v := by norm_num [isUnitStep_iff, v, Fin.sum_univ_three]
  have hw : IsUnitStep w := by norm_num [isUnitStep_iff, w, Fin.sum_univ_three]
  apply (isRhombus_of_hasStep_iff hv hw ?_ ?_ ?_).mpr
    (by norm_num [v, w, Fin.sum_univ_three])
  all_goals
    rw [hasStep_iff]
    intro k
    fin_cases k <;> simp [chart, v, w] <;> omega

private theorem chart_rhombus_remaining {i j : ℕ} (hij : i ≤ j) (hj : j + 2 ≤ n) :
    IsRhombus (chart n i (j + 1) (by omega) (by omega))
      (chart n i j hij (by omega))
      (chart n (i + 1) (j + 1) (by omega) (by omega))
      (chart n (i + 1) (j + 2) (by omega) hj) := by
  convert isRhombus_ofYZ_step (n := n) (y := j - i) (z := i) (by omega) using 1 <;>
    ext <;> simp [chart] <;> omega

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
    exact ⟨by linarith [h.le_of_isRhombus (chart_rhombus_left hij hj)],
      by linarith [h.le_of_isRhombus (chart_rhombus_right hij hj)]⟩

/-- On an informative cell, the pattern is the difference
`h(n-j,j-(i+1),i+1) - h(n-j,j-i,i)`. -/
@[simp] theorem toGTPattern_apply (h : IntegerHive n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) :
    h.toGTPattern i j =
      h ⟨n - j, j - (i + 1), i + 1, by omega⟩ -
        h ⟨n - j, j - i, i, by omega⟩ := by
  simp only [← GTPattern.entry_eq_coe, toGTPattern]
  rw [dite_eq_left ⟨hij, hj⟩]
  rfl

private theorem toGTPattern_chart (h : IntegerHive n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) :
    h.toGTPattern i j =
      h (chart n (i + 1) j (by omega) hj) - h (chart n i j (by omega) hj) := by
  exact toGTPattern_apply h hij hj

/-- The top row of the directional pattern is the hive's second clockwise boundary. -/
@[simp] theorem topRow_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topRow = h.boundary 1 := by
  funext i
  rw [GTPattern.topRow_apply, toGTPattern_chart h i.isLt le_rfl,
    chart_top _ (by omega), chart_top _ (by omega), boundary_apply]
  rfl

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

private theorem sum_toGTPattern_chart (h : IntegerHive n) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n) :
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
      h (chart n i j hij hj) - h (chart n 0 j (Nat.zero_le _) hj) := by
  let f : ℕ → ℤ := fun k => h (chart n (min k j) j (Nat.min_le_right _ _) hj)
  calc
    (∑ k ∈ Finset.range i, h.toGTPattern k j) =
        ∑ k ∈ Finset.range i, (f (k + 1) - f k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < i := Finset.mem_range.mp hk
      rw [toGTPattern_chart h (by omega) hj]
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
    gtCompletion lam P ⟨n - j, j - i, i, by omega⟩ =
      (∑ r : Fin n with r.val < j, lam r) + ∑ k ∈ Finset.range i, P k j := by
  rw [gtCompletion_apply]
  simp only
  rw [Nat.sub_add_cancel hij]

/-- Consecutive directional differences of a completion recover the original
pattern on every informative cell, independently of the first boundary. -/
theorem gtCompletion_step (lam : Fin n → ℤ) (P : GTPattern n) {i j : ℕ}
    (hij : i < j) (hj : j ≤ n) :
    gtCompletion lam P ⟨n - j, j - (i + 1), i + 1, by omega⟩ -
      gtCompletion lam P ⟨n - j, j - i, i, by omega⟩ = P i j := by
  rw [gtCompletion_chart lam P (by omega) hj, gtCompletion_chart lam P (by omega) hj,
    Finset.sum_range_succ]
  abel

/-- Every hive value is the prefix of the first boundary followed by the prefix
of the corresponding row of its directional pattern. -/
theorem apply_eq_boundary_prefix_add_sum_toGTPattern (h : IntegerHive n) (p : Vertex n) :
    h p = (∑ r : Fin n with r.val < p.y + p.z, h.boundary 0 r) +
      ∑ k ∈ Finset.range p.z, h.toGTPattern k (p.y + p.z) := by
  have hj : p.y + p.z ≤ n := by have := p.sum_eq; omega
  have hv : chart n p.z (p.y + p.z) (by omega) hj = p := by
    have := p.sum_eq
    ext <;> simp [chart]; omega
  have hs := sum_toGTPattern_chart h (i := p.z) (j := p.y + p.z) (by omega) hj
  rw [hv, chart_zero, apply_edgePoint_zero] at hs
  exact eq_add_of_sub_eq' hs.symm

/-- Integrating the directional pattern with the hive's first boundary recovers
the original normalized hive as a lattice function. -/
@[simp] theorem gtCompletion_toGTPattern (h : IntegerHive n) :
    gtCompletion (h.boundary 0) h.toGTPattern = ⇑h := by
  funext p
  rw [gtCompletion_apply, ← apply_eq_boundary_prefix_add_sum_toGTPattern]

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
theorem toGTPattern_injective_on_boundary_zero (lam : Fin n → ℤ) :
    Function.Injective (fun h : {h : IntegerHive n // h.boundary 0 = lam} =>
      h.1.toGTPattern) := by
  intro h k hP
  exact Subtype.ext (eq_of_boundary_zero_eq_of_toGTPattern_eq (h.2.trans k.2.symm) hP)

/-- The difference between consecutive row sums is the negative reversed third
boundary minus the first boundary. This is the signed pattern weight in cyclic
hive coordinates. -/
theorem rowWeight_toGTPattern (h : IntegerHive n) (r : Fin n) :
    (∑ k ∈ Finset.range (r.val + 1), h.toGTPattern k (r.val + 1)) -
      (∑ k ∈ Finset.range r.val, h.toGTPattern k r.val) =
        -h.boundary 2 r.rev - h.boundary 0 r := by
  rw [sum_toGTPattern_chart h le_rfl (by omega),
    sum_toGTPattern_chart h le_rfl (by omega),
    chart_self, chart_self, chart_zero, chart_zero, boundary_apply, boundary_apply]
  have h2s : Vertex.edgePoint n 2 r.rev.succ =
      Vertex.edgePoint n 2 ⟨n - r.val, by omega⟩ := by
    ext <;> simp <;> omega
  have h2c : Vertex.edgePoint n 2 r.rev.castSucc =
      Vertex.edgePoint n 2 ⟨n - (r.val + 1), by omega⟩ := by
    ext <;> simp
  have h0s : r.succ = (⟨r.val + 1, by omega⟩ : Fin (n + 1)) := Fin.ext (by simp)
  have h0c : r.castSucc = (⟨r.val, by omega⟩ : Fin (n + 1)) := Fin.ext (by simp)
  rw [h2s, h2c, h0s, h0c]
  abel

/-- In product boundary convention, the top row of the directional pattern is `μ`. -/
theorem topRow_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) :
    h.toGTPattern.topRow = μ.1 := by
  rw [topRow_toGTPattern, hb, productBoundary_one]

/-- In product boundary convention, the pattern has weight `γ - λ`:
the difference of the row sums of lengths `r+1` and `r` is `γᵣ - λᵣ`. -/
theorem rowWeight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) (r : Fin n) :
    (∑ k ∈ Finset.range (r.val + 1), h.toGTPattern k (r.val + 1)) -
      (∑ k ∈ Finset.range r.val, h.toGTPattern k r.val) = γ.1 r - lam.1 r := by
  simp [rowWeight_toGTPattern, hb]

/-- The third rhombus family imposes an additional necessary inequality on the
directional pattern. Unlike interlacing, it involves the first hive boundary. -/
theorem remaining_inequality_toGTPattern (h : IntegerHive n) {i j : ℕ}
    (hij : i ≤ j) (hj : j + 2 ≤ n) :
    (∑ k ∈ Finset.range (i + 1),
      (h.toGTPattern k (j + 2) - h.toGTPattern k (j + 1))) ≤
        h.boundary 0 ⟨j, by omega⟩ - h.boundary 0 ⟨j + 1, by omega⟩ +
          ∑ k ∈ Finset.range i, (h.toGTPattern k (j + 1) - h.toGTPattern k j) := by
  have h0 : h.boundary 0 ⟨j, by omega⟩ =
      h (chart n 0 (j + 1) (by omega) (by omega)) -
        h (chart n 0 j (by omega) (by omega)) := by
    rw [chart_zero, chart_zero, boundary_apply]
    rfl
  have h1 : h.boundary 0 ⟨j + 1, by omega⟩ =
      h (chart n 0 (j + 2) (by omega) (by omega)) -
        h (chart n 0 (j + 1) (by omega) (by omega)) := by
    rw [chart_zero, chart_zero, boundary_apply]
    rfl
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  linarith [h.le_of_isRhombus (chart_rhombus_remaining hij hj),
    sum_toGTPattern_chart h hij (by omega),
    sum_toGTPattern_chart h (i := i) (j := j + 1) (by omega) (by omega),
    sum_toGTPattern_chart h (i := i + 1) (j := j + 1) (by omega) (by omega),
    sum_toGTPattern_chart h (i := i + 1) (j := j + 2) (by omega) hj]

/-- For product boundary `(λ, μ, γ*)`, the third rhombus family gives the
remaining inequalities in the native Gelfand–Tsetlin image condition. -/
theorem remaining_inequality_toGTPattern_of_productBoundary
    {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) {i j : ℕ}
    (hij : i ≤ j) (hj : j + 2 ≤ n) :
    (∑ k ∈ Finset.range (i + 1),
      (h.toGTPattern k (j + 2) - h.toGTPattern k (j + 1))) ≤
        lam.1 ⟨j, by omega⟩ - lam.1 ⟨j + 1, by omega⟩ +
          ∑ k ∈ Finset.range i, (h.toGTPattern k (j + 1) - h.toGTPattern k j) := by
  simpa [hb] using remaining_inequality_toGTPattern h hij hj

/-- A hive in product convention is recovered from `λ` and the prefix sums of
its directional pattern, without any positivity assumption on the weights. -/
theorem apply_eq_prefix_add_sum_toGTPattern_of_productBoundary
    {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (p : Vertex n) :
    h p = (∑ r : Fin n with r.val < p.y + p.z, lam.1 r) +
      ∑ k ∈ Finset.range p.z, h.toGTPattern k (p.y + p.z) := by
  simpa [hb] using apply_eq_boundary_prefix_add_sum_toGTPattern h p

/-- Affine hives yield constant signed patterns: the first boundary value is
subtracted from the third-coordinate slope. -/
@[simp] theorem toGTPattern_affine (β γ : ℤ) :
    (affine n β γ).toGTPattern = GTPattern.const n (γ - β) := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · rw [toGTPattern_apply _ hij.1 hij.2,
      GTPattern.const_apply_of_lt_of_le _ hij.1 hij.2]
    have hy : j - i = (j - (i + 1)) + 1 := by omega
    simp only [affine_apply]
    rw [hy]
    simp only [add_nsmul, one_nsmul]
    abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega)]

end TauCeti.Hive
