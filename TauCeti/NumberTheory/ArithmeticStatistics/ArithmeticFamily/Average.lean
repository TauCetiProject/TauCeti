/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticStatistics.ArithmeticFamily.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Averages over a height-ordered family

For an arithmetic family `F` with height `h` and a real function `φ` on its members, the
finite-cutoff average

`Avg_F(φ; X) = (∑_{h(i) < X} φ(i)) / #{i : h(i) < X}`

is the mean of `φ` over the members of height strictly below `X`, read as `0` when there are
none. The function `φ` *has average `c`* when `Avg_F(φ; X) → c` as `X → ∞`, and its *upper
average* is `limsup_{X → ∞} Avg_F(φ; X)`. These are the averages in which statements such as
"the average size of the `2`-Selmer group of an elliptic curve over `ℚ`, ordered by height, is
`3`" are made, and upper averages carry statements such as rank bounds that assert no limit.
The strict cutoff follows the convention of Bhargava and Shankar.

Averages are linear, constants average to themselves over any nonempty family, and a limiting
average is its own upper average. Upper averages are monotone in the function, given the
boundedness that a real `limsup` needs to be meaningful (`upperAverage_le_upperAverage`).
Multiplying the height by a positive constant `c` moves every finite-cutoff average from `X` to
`X / c`, so it changes neither limiting nor upper averages (`hasAverage_rescale_iff`,
`upperAverage_rescale`): for elliptic curves the orderings by `max(4|A|³, 27B²)` and by
`max(|I|³, J²/4)`, which differ by the factor `27/4`, have the same averages. Finite-cutoff
averages at the same `X` do differ.

## Main definitions

* `TauCeti.ArithmeticFamily.average`: the finite-cutoff average `Avg_F(φ; X)`.
* `TauCeti.ArithmeticFamily.HasAverage`: `Avg_F(φ; X) → c` as `X → ∞`.
* `TauCeti.ArithmeticFamily.upperAverage`: `limsup_{X → ∞} Avg_F(φ; X)`.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), 191–242,
  Theorem 1.1, Corollary 1.2 and §3.
-/

public section

open Filter Topology

namespace TauCeti

namespace ArithmeticFamily

variable {ι : Type*} (F : ArithmeticFamily ι)

/-! ### Finite-cutoff averages -/

/-- The average of `φ` over the members of height strictly below `X`: the sum of `φ` over the
strict carrier divided by the strict count of the family, read as `0` when the carrier is
empty. -/
noncomputable def average (φ : ι → ℝ) (X : ℝ) : ℝ :=
  (∑ i ∈ F.heightLT X, φ i) / F.countLT Set.univ X

/-- A finite-cutoff average is the sum over the strict carrier divided by the strict count. -/
theorem average_apply (φ : ι → ℝ) (X : ℝ) :
    F.average φ X = (∑ i ∈ F.heightLT X, φ i) / F.countLT Set.univ X := by
  rw [average]

/-- A finite-cutoff average is the sum over the strict carrier divided by its cardinality. -/
theorem average_eq_sum_div_card (φ : ι → ℝ) (X : ℝ) :
    F.average φ X = (∑ i ∈ F.heightLT X, φ i) / (F.heightLT X).card := by
  rw [average_apply, card_heightLT]

/-- The average times the strict count is the sum over the strict carrier; both sides vanish
when the carrier is empty. -/
theorem average_mul_countLT (φ : ι → ℝ) (X : ℝ) :
    F.average φ X * F.countLT Set.univ X = ∑ i ∈ F.heightLT X, φ i := by
  rcases (F.countLT Set.univ X).eq_zero_or_pos with hX | hX
  · simp [hX, Finset.card_eq_zero.mp (card_heightLT F X ▸ hX)]
  · rw [average_apply]
    exact div_mul_cancel₀ _ (by exact_mod_cast hX.ne')

/-- At a cutoff below every height the average is `0`. -/
theorem average_eq_zero_of_le (φ : ι → ℝ) {X : ℝ} (hX : ∀ i, X ≤ F.height i) :
    F.average φ X = 0 := by
  have : F.heightLT X = ∅ :=
    Finset.eq_empty_of_forall_notMem fun i hi ↦ ((mem_heightLT F).mp hi).not_ge (hX i)
  simp [average_apply, this]

/-- The zero function has average `0` at every cutoff. -/
@[simp]
theorem average_zero (X : ℝ) : F.average 0 X = 0 := by
  simp [average_apply]

/-- Finite-cutoff averages are additive in the function. -/
theorem average_add (φ ψ : ι → ℝ) (X : ℝ) :
    F.average (φ + ψ) X = F.average φ X + F.average ψ X := by
  simp [average_apply, Finset.sum_add_distrib, add_div]

/-- Finite-cutoff averages commute with multiplication by a constant. -/
theorem average_const_mul (c : ℝ) (φ : ι → ℝ) (X : ℝ) :
    F.average (fun i ↦ c * φ i) X = c * F.average φ X := by
  simp [average_apply, ← Finset.mul_sum, mul_div_assoc]

/-- Finite-cutoff averages commute with negation. -/
theorem average_neg (φ : ι → ℝ) (X : ℝ) : F.average (-φ) X = -F.average φ X := by
  simp [average_apply, neg_div]

/-- Finite-cutoff averages are compatible with subtraction. -/
theorem average_sub (φ ψ : ι → ℝ) (X : ℝ) :
    F.average (φ - ψ) X = F.average φ X - F.average ψ X := by
  rw [sub_eq_add_neg, average_add, average_neg, ← sub_eq_add_neg]

/-- At a cutoff with some member strictly below it, a constant function averages to itself. -/
theorem average_const (c : ℝ) {X : ℝ} (hX : 0 < F.countLT Set.univ X) :
    F.average (fun _ ↦ c) X = c := by
  rw [average_apply, Finset.sum_const, nsmul_eq_mul, card_heightLT]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hX.ne')

/-- Finite-cutoff averages are monotone in the function. -/
theorem average_mono {φ ψ : ι → ℝ} (h : φ ≤ ψ) (X : ℝ) : F.average φ X ≤ F.average ψ X := by
  rw [average_apply, average_apply]
  gcongr with i
  exact h i

/-- A nonnegative function has nonnegative finite-cutoff averages. -/
theorem average_nonneg {φ : ι → ℝ} (h : 0 ≤ φ) (X : ℝ) : 0 ≤ F.average φ X := by
  simpa using F.average_mono h X

/-- A finite-cutoff average of a function bounded above by `M ≥ 0` is at most `M`. -/
theorem average_le_of_forall_le {φ : ι → ℝ} {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, φ i ≤ M) (X : ℝ) :
    F.average φ X ≤ M := by
  refine (F.average_mono (ψ := fun _ ↦ M) h X).trans ?_
  rcases (F.countLT Set.univ X).eq_zero_or_pos with hX | hX
  · simpa [average_apply, hX] using hM
  · exact (F.average_const M hX).le

/-- A constant function eventually averages to itself over a nonempty family. -/
theorem eventually_average_const [Nonempty ι] (c : ℝ) :
    F.average (fun _ ↦ c) =ᶠ[atTop] fun _ ↦ c := by
  filter_upwards [F.eventually_heightLT_nonempty] with X hX
  exact F.average_const c (card_heightLT F X ▸ hX.card_pos)

/-- Rescaling the height by a positive constant moves the finite-cutoff average from `X` to
`X / c`. -/
theorem average_rescale (c : ℝ) (hc : 0 < c) (φ : ι → ℝ) (X : ℝ) :
    (F.rescale c hc).average φ X = F.average φ (X / c) := by
  rw [average_eq_sum_div_card, average_eq_sum_div_card, heightLT_rescale]

/-- Rescaling the height by a positive constant precomposes the finite-cutoff averages with
division of the cutoff by that constant. -/
private theorem average_rescale_eq_comp (c : ℝ) (hc : 0 < c) (φ : ι → ℝ) :
    (F.rescale c hc).average φ = F.average φ ∘ OrderIso.divRight₀ c hc := by
  ext X
  simp [average_rescale]

/-! ### Limiting averages -/

/-- The function `φ` has average `c` over the family: its finite-cutoff averages tend to `c` as
the cutoff tends to infinity. -/
def HasAverage (φ : ι → ℝ) (c : ℝ) : Prop :=
  Tendsto (F.average φ) atTop (𝓝 c)

/-- Having average `c` is convergence of the finite-cutoff averages to `c`. -/
theorem hasAverage_iff_tendsto {φ : ι → ℝ} {c : ℝ} :
    F.HasAverage φ c ↔ Tendsto (F.average φ) atTop (𝓝 c) := Iff.rfl

variable {F}

/-- A function has at most one average. -/
theorem HasAverage.unique {φ : ι → ℝ} {c d : ℝ} (hc : F.HasAverage φ c)
    (hd : F.HasAverage φ d) : c = d :=
  tendsto_nhds_unique hc hd

/-- Averages add. -/
theorem HasAverage.add {φ ψ : ι → ℝ} {c d : ℝ} (hφ : F.HasAverage φ c)
    (hψ : F.HasAverage ψ d) : F.HasAverage (φ + ψ) (c + d) := by
  rw [hasAverage_iff_tendsto, funext (F.average_add φ ψ)]
  exact Tendsto.add hφ hψ

/-- Averages commute with multiplication by a constant. -/
theorem HasAverage.const_mul {φ : ι → ℝ} {c : ℝ} (a : ℝ) (hφ : F.HasAverage φ c) :
    F.HasAverage (fun i ↦ a * φ i) (a * c) := by
  rw [hasAverage_iff_tendsto, funext (F.average_const_mul a φ)]
  exact Tendsto.const_mul a hφ

/-- Averages commute with negation. -/
theorem HasAverage.neg {φ : ι → ℝ} {c : ℝ} (hφ : F.HasAverage φ c) :
    F.HasAverage (-φ) (-c) := by
  rw [hasAverage_iff_tendsto, funext (F.average_neg φ)]
  exact Tendsto.neg hφ

/-- Averages are compatible with subtraction. -/
theorem HasAverage.sub {φ ψ : ι → ℝ} {c d : ℝ} (hφ : F.HasAverage φ c)
    (hψ : F.HasAverage ψ d) : F.HasAverage (φ - ψ) (c - d) := by
  rw [hasAverage_iff_tendsto, funext (F.average_sub φ ψ)]
  exact Tendsto.sub hφ hψ

/-- Averages are monotone in the function. -/
theorem HasAverage.le {φ ψ : ι → ℝ} {c d : ℝ} (h : φ ≤ ψ) (hφ : F.HasAverage φ c)
    (hψ : F.HasAverage ψ d) : c ≤ d :=
  le_of_tendsto_of_tendsto' hφ hψ (F.average_mono h)

variable (F) in
/-- Over a nonempty family a constant function has itself as average. -/
theorem hasAverage_const [Nonempty ι] (c : ℝ) : F.HasAverage (fun _ ↦ c) c :=
  tendsto_const_nhds.congr' (F.eventually_average_const c).symm

/-- For `c > 0`, a function has the same averages for the height `h` and for the height
`c · h`. -/
theorem hasAverage_rescale_iff {c : ℝ} (hc : 0 < c) {φ : ι → ℝ} {d : ℝ} :
    (F.rescale c hc).HasAverage φ d ↔ F.HasAverage φ d := by
  rw [hasAverage_iff_tendsto, hasAverage_iff_tendsto, average_rescale_eq_comp,
    ← tendsto_map'_iff, OrderIso.map_atTop]

/-! ### Upper averages -/

variable (F) in
/-- The upper average of `φ` over the family: the `limsup` of its finite-cutoff averages as the
cutoff tends to infinity. As a real `limsup` it is meaningful only when those averages are
bounded above and below along the cutoff; the comparison lemmas carry these hypotheses. -/
noncomputable def upperAverage (φ : ι → ℝ) : ℝ :=
  limsup (F.average φ) atTop

variable (F) in
/-- The upper average is the `limsup` of the finite-cutoff averages. -/
theorem upperAverage_apply (φ : ι → ℝ) : F.upperAverage φ = limsup (F.average φ) atTop := by
  rw [upperAverage]

/-- A limiting average is the upper average. -/
theorem HasAverage.upperAverage_eq {φ : ι → ℝ} {c : ℝ} (hφ : F.HasAverage φ c) :
    F.upperAverage φ = c :=
  hφ.limsup_eq

variable (F) in
/-- Over a nonempty family the upper average of a constant function is that constant. -/
theorem upperAverage_const [Nonempty ι] (c : ℝ) : F.upperAverage (fun _ ↦ c) = c :=
  (hasAverage_const F c).upperAverage_eq

/-- **Upper averages are monotone.** If `φ ≤ ψ`, the averages of `ψ` are eventually bounded
above and those of `φ` are cobounded below, then the upper average of `φ` is at most that of `ψ`.
The hypotheses cannot be dropped, because a real `limsup` takes a junk value on an unbounded
sequence. -/
theorem upperAverage_le_upperAverage {φ ψ : ι → ℝ} (h : φ ≤ ψ)
    (hφ : IsCoboundedUnder (· ≤ ·) atTop (F.average φ))
    (hψ : IsBoundedUnder (· ≤ ·) atTop (F.average ψ)) :
    F.upperAverage φ ≤ F.upperAverage ψ :=
  limsup_le_limsup (Eventually.of_forall (F.average_mono h)) hφ hψ

/-- Upper averages are monotone on nonnegative functions: if `0 ≤ φ ≤ ψ` and the averages of `ψ`
are eventually bounded above, then the upper average of `φ` is at most that of `ψ`. -/
theorem upperAverage_le_upperAverage_of_nonneg {φ ψ : ι → ℝ} (h₀ : 0 ≤ φ) (h : φ ≤ ψ)
    (hψ : IsBoundedUnder (· ≤ ·) atTop (F.average ψ)) :
    F.upperAverage φ ≤ F.upperAverage ψ :=
  upperAverage_le_upperAverage h
    (isCoboundedUnder_le_of_le atTop (F.average_nonneg h₀)) hψ

/-- For `c > 0`, a function has the same upper average for the height `h` and for the height
`c · h`. -/
theorem upperAverage_rescale {c : ℝ} (hc : 0 < c) (φ : ι → ℝ) :
    (F.rescale c hc).upperAverage φ = F.upperAverage φ := by
  rw [upperAverage_apply, upperAverage_apply, average_rescale_eq_comp, limsup_comp,
    OrderIso.map_atTop]

end ArithmeticFamily

end TauCeti
