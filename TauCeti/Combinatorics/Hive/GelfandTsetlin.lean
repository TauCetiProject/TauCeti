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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

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
(`TauCeti.Hive.gtCompletion_add_le_of_gap`), so that the hives are counted by all patterns of
top row `μ` and weight `γ - λ` (`TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfGap`).

## Main definitions

* `TauCeti.Hive.gtChart`: a lattice function read in the chart `(i, j)`.
* `TauCeti.Hive.toGTPattern`: the Gelfand-Tsetlin pattern of horizontal differences of an integer
  hive.
* `TauCeti.Hive.gtCompletion`: the chart function rebuilt from a boundary `λ` and a pattern.
* `TauCeti.Hive.ofGTPattern`: the integer hive with values the completion of a pattern.
* `TauCeti.Hive.fixedIntegerHiveEquivGTPattern`, `TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfGap`:
  the equivalences of fixed-boundary hive fibres with sets of patterns.

## Main results

* `TauCeti.Hive.isRhombusConcave_chart_iff`: rhombus concavity in terms of the three chart families.
* `TauCeti.Hive.topRow_toGTPattern`, `TauCeti.Hive.weight_toGTPattern`,
  `TauCeti.Hive.apply_eq_gtCompletion`: the top row, the weight, and the reconstruction formula.
* `TauCeti.Hive.exists_fixedIntegerHive_eq_gtCompletion_iff`: a pattern of top row `μ` and weight
  `γ - λ` is the difference pattern of a hive with boundary `(λ, μ, γ*)` iff its completion
  satisfies the third family.
* `TauCeti.Hive.gtCompletion_add_le_of_gap`, `TauCeti.Hive.hiveCount_eq_card_gtPattern_of_gap`:
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

/-! ### The three families of unit rhombi in the chart -/

section Chart

variable {R : Type*}

/-- The value of `f` at the chart point `(i, j)`, the lattice vertex `(n - j, j - i, i)`, when
`i ≤ j ≤ n`, and `0` off the chart. -/
def gtChart [Zero R] (f : Vertex n → R) (i j : ℕ) : R :=
  if h : i ≤ j ∧ j ≤ n then f (Vertex.ofYZ n (j - i) i (by omega)) else 0

theorem gtChart_of_le [Zero R] (f : Vertex n → R) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    gtChart f i j = f (Vertex.ofYZ n (j - i) i (by omega)) := by
  simp only [gtChart, hij, hj, and_self, ↓reduceDIte]

theorem gtChart_of_lt [Zero R] (f : Vertex n → R) {i j : ℕ} (hj : n < j) : gtChart f i j = 0 := by
  simp only [gtChart, show ¬j ≤ n by omega, and_false, ↓reduceDIte]

/-- Every lattice vertex `v` is the chart point `(v.z, n - v.x)`. -/
@[simp]
theorem gtChart_z_sub_x [Zero R] (f : Vertex n → R) (v : Vertex n) :
    gtChart f v.z (n - v.x) = f v := by
  have := v.sum_eq
  rw [gtChart_of_le f (by omega) (by omega)]
  congr 1
  ext <;> simp <;> omega

/-- The obtuse corners `o₁ = (i, j)`, `o₂ = (i+1, j+1)` and acute corners `a₁ = (i+1, j)`,
`a₂ = (i, j+1)` of a rhombus of the first chart family, in coordinates. -/
private def ChartRhombus₁ (o₁ a₁ o₂ a₂ : Vertex n) : Prop :=
  a₁.x = o₁.x ∧ a₁.z = o₁.z + 1 ∧ o₂.x + 1 = o₁.x ∧ o₂.z = o₁.z + 1 ∧ a₂.x + 1 = o₁.x ∧
    a₂.z = o₁.z

/-- The obtuse corners `o₁ = (i+1, j)`, `o₂ = (i+1, j+1)` and acute corners `a₁ = (i, j)`,
`a₂ = (i+2, j+1)` of a rhombus of the second chart family, in coordinates. -/
private def ChartRhombus₂ (o₁ a₁ o₂ a₂ : Vertex n) : Prop :=
  o₁.x = a₁.x ∧ o₁.z = a₁.z + 1 ∧ o₂.x + 1 = a₁.x ∧ o₂.z = a₁.z + 1 ∧ a₂.x + 1 = a₁.x ∧
    a₂.z = a₁.z + 2

/-- The obtuse corners `o₁ = (i, j+1)`, `o₂ = (i+1, j+1)` and acute corners `a₁ = (i, j)`,
`a₂ = (i+1, j+2)` of a rhombus of the third chart family, in coordinates. -/
private def ChartRhombus₃ (o₁ a₁ o₂ a₂ : Vertex n) : Prop :=
  o₁.x + 1 = a₁.x ∧ o₁.z = a₁.z ∧ o₂.x + 1 = a₁.x ∧ o₂.z = a₁.z + 1 ∧ a₂.x + 2 = a₁.x ∧
    a₂.z = a₁.z + 1

/-- An integer vector with coordinate sum `0` and squared length `2` is a unit lattice step. -/
private theorem unitStep_cases {p q r : ℤ} (hs : p + q + r = 0) (h2 : p ^ 2 + q ^ 2 + r ^ 2 = 2) :
    (p = 1 ∧ q = -1) ∨ (p = -1 ∧ q = 1) ∨ (p = 1 ∧ r = -1) ∨ (p = -1 ∧ r = 1) ∨
      (p = 0 ∧ q = 1) ∨ (p = 0 ∧ q = -1) := by
  have hp1 : -1 ≤ p := by nlinarith
  have hp2 : p ≤ 1 := by nlinarith
  have hq1 : -1 ≤ q := by nlinarith
  have hq2 : q ≤ 1 := by nlinarith
  obtain rfl : r = -p - q := by omega
  interval_cases p <;> interval_cases q <;> simp_all

/-- An integer vector with coordinate sum `0` and squared length `6` is a long rhombus diagonal. -/
private theorem longStep_cases {p q r : ℤ} (hs : p + q + r = 0) (h2 : p ^ 2 + q ^ 2 + r ^ 2 = 6) :
    (p = 2 ∧ q = -1) ∨ (p = -2 ∧ q = 1) ∨ (p = -1 ∧ q = 2) ∨ (p = 1 ∧ q = -2) ∨
      (p = -1 ∧ q = -1) ∨ (p = 1 ∧ q = 1) := by
  have hp1 : -2 ≤ p := by nlinarith
  have hp2 : p ≤ 2 := by nlinarith
  have hq1 : -2 ≤ q := by nlinarith
  have hq2 : q ≤ 2 := by nlinarith
  obtain rfl : r = -p - q := by omega
  interval_cases p <;> interval_cases q <;> simp_all

/-- Every unit rhombus is a rhombus of one of the three chart families, up to exchanging its two
obtuse corners and its two acute corners. The short diagonal is a unit step and the long diagonal
a step of squared length `6`; of the `36` combinations, the `12` compatible with the common
midpoint are the three families in their four orderings. -/
private theorem IsRhombus.chartRhombus {a b c d : Vertex n} (h : IsRhombus a b c d) :
    (ChartRhombus₁ a b c d ∨ ChartRhombus₁ c b a d ∨ ChartRhombus₁ a d c b ∨
        ChartRhombus₁ c d a b) ∨
      (ChartRhombus₂ a b c d ∨ ChartRhombus₂ c b a d ∨ ChartRhombus₂ a d c b ∨
        ChartRhombus₂ c d a b) ∨
      (ChartRhombus₃ a b c d ∨ ChartRhombus₃ c b a d ∨ ChartRhombus₃ a d c b ∨
        ChartRhombus₃ c d a b) := by
  have hs := h.short
  have hl := h.long
  rw [Vertex.sqDist_def] at hs hl
  have ha := a.sum_eq
  have hb := b.sum_eq
  have hc := c.sum_eq
  have hd := d.sum_eq
  have hmx := h.midpoint_x
  have hmy := h.midpoint_y
  unfold ChartRhombus₁ ChartRhombus₂ ChartRhombus₃
  rcases unitStep_cases (by omega) hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ |
      ⟨h₁, h₂⟩ <;>
    rcases longStep_cases (by omega) hl with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ |
      ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩ <;>
    first
    | (exfalso; omega)
    | exact Or.inl (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))
    | exact Or.inl (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    | exact Or.inl (Or.inr (Or.inr (Or.inr
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    | exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))
    | exact Or.inr (Or.inl (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    | exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))
    | exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))
    | exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))
    | exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩))))

/-- The four corners `p + v`, `p`, `p + w`, `p + v + w` given by coordinate offsets of `p` form a
unit rhombus when `v, w` are unit steps of inner product `1`. -/
private theorem isRhombus_of_offsets {p pv pw pvw : Vertex n} (v w : Fin 3 → ℤ)
    (hv : IsUnitStep v) (hw : IsUnitStep w) (hdot : (∑ i, v i * w i) = 1)
    (hx : (pv.x : ℤ) = p.x + v 0 ∧ (pw.x : ℤ) = p.x + w 0 ∧ (pvw.x : ℤ) = p.x + v 0 + w 0)
    (hz : (pv.z : ℤ) = p.z + v 2 ∧ (pw.z : ℤ) = p.z + w 2 ∧ (pvw.z : ℤ) = p.z + v 2 + w 2) :
    IsRhombus pv p pw pvw := by
  have hp := p.sum_eq
  have hpv := pv.sum_eq
  have hpw := pw.sum_eq
  have hpvw := pvw.sum_eq
  have hv0 : v 0 + v 1 + v 2 = 0 := by simpa [Fin.sum_univ_three] using (isUnitStep_iff.mp hv).1
  have hw0 : w 0 + w 1 + w 2 = 0 := by simpa [Fin.sum_univ_three] using (isUnitStep_iff.mp hw).1
  refine (isRhombus_of_hasStep_iff hv hw ?_ ?_ ?_).mpr hdot <;> rw [hasStep_iff] <;> intro k <;>
    fin_cases k <;> simp <;> omega

private theorem ChartRhombus₁.isRhombus {o₁ a₁ o₂ a₂ : Vertex n}
    (h : ChartRhombus₁ o₁ a₁ o₂ a₂) : IsRhombus o₁ a₁ o₂ a₂ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact isRhombus_of_offsets ![0, 1, -1] ![-1, 1, 0] (isUnitStep_iff.mpr (by decide))
    (isUnitStep_iff.mpr (by decide)) (by decide)
    (by simp; omega) (by simp; omega)

private theorem ChartRhombus₂.isRhombus {o₁ a₁ o₂ a₂ : Vertex n}
    (h : ChartRhombus₂ o₁ a₁ o₂ a₂) : IsRhombus o₁ a₁ o₂ a₂ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact isRhombus_of_offsets ![0, -1, 1] ![-1, 0, 1] (isUnitStep_iff.mpr (by decide))
    (isUnitStep_iff.mpr (by decide)) (by decide)
    (by simp; omega) (by simp; omega)

private theorem ChartRhombus₃.isRhombus {o₁ a₁ o₂ a₂ : Vertex n}
    (h : ChartRhombus₃ o₁ a₁ o₂ a₂) : IsRhombus o₁ a₁ o₂ a₂ := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  exact isRhombus_of_offsets ![-1, 1, 0] ![-1, 0, 1] (isUnitStep_iff.mpr (by decide))
    (isUnitStep_iff.mpr (by decide)) (by decide)
    (by simp; omega) (by simp; omega)

/-- The chart value of the vertex `(n - j, j - i, i)` is the value at `(i, j)`. -/
private theorem apply_ofYZ (g : ℕ → ℕ → R) {i j : ℕ} (hij : i ≤ j) (h : j - i + i ≤ n) :
    g (Vertex.ofYZ n (j - i) i h).z (n - (Vertex.ofYZ n (j - i) i h).x) = g i j := by
  rw [Vertex.ofYZ_z, Vertex.ofYZ_x, show n - (n - (j - i) - i) = j by omega]

section Ordered

variable [AddCommGroup R] [Preorder R] (g : ℕ → ℕ → R)

private theorem ChartRhombus₁.le
    (h₁ : ∀ i j, i < j → j < n → g (i + 1) j + g i (j + 1) ≤ g i j + g (i + 1) (j + 1))
    {o₁ a₁ o₂ a₂ : Vertex n} (H : ChartRhombus₁ o₁ a₁ o₂ a₂) :
    g a₁.z (n - a₁.x) + g a₂.z (n - a₂.x) ≤ g o₁.z (n - o₁.x) + g o₂.z (n - o₂.x) := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := H
  have := a₁.sum_eq
  rw [show a₁.z = o₁.z + 1 by omega, show n - a₁.x = n - o₁.x by omega, e₆,
    show n - a₂.x = n - o₁.x + 1 by omega, e₄, show n - o₂.x = n - o₁.x + 1 by omega]
  exact h₁ _ _ (by omega) (by omega)

private theorem ChartRhombus₂.le
    (h₂ : ∀ i j, i < j → j < n → g i j + g (i + 2) (j + 1) ≤ g (i + 1) j + g (i + 1) (j + 1))
    {o₁ a₁ o₂ a₂ : Vertex n} (H : ChartRhombus₂ o₁ a₁ o₂ a₂) :
    g a₁.z (n - a₁.x) + g a₂.z (n - a₂.x) ≤ g o₁.z (n - o₁.x) + g o₂.z (n - o₂.x) := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := H
  have := o₁.sum_eq
  rw [e₆, show n - a₂.x = n - a₁.x + 1 by omega, e₂, e₁, e₄,
    show n - o₂.x = n - a₁.x + 1 by omega]
  exact h₂ _ _ (by omega) (by omega)

private theorem ChartRhombus₃.le
    (h₃ : ∀ i j, i ≤ j → j + 2 ≤ n →
      g i j + g (i + 1) (j + 2) ≤ g i (j + 1) + g (i + 1) (j + 1))
    {o₁ a₁ o₂ a₂ : Vertex n} (H : ChartRhombus₃ o₁ a₁ o₂ a₂) :
    g a₁.z (n - a₁.x) + g a₂.z (n - a₂.x) ≤ g o₁.z (n - o₁.x) + g o₂.z (n - o₂.x) := by
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := H
  have := a₁.sum_eq
  rw [e₆, show n - a₂.x = n - a₁.x + 2 by omega, e₂, show n - o₁.x = n - a₁.x + 1 by omega, e₄,
    show n - o₂.x = n - a₁.x + 1 by omega]
  exact h₃ _ _ (by omega) (by omega)

/-- **Rhombus concavity in the chart.** A lattice function read in the chart `(i, j)` through
`g` is rhombus-concave iff `g` satisfies the inequalities of the three families of unit rhombi:
`g(i+1, j) + g(i, j+1) ≤ g(i, j) + g(i+1, j+1)` and
`g(i, j) + g(i+2, j+1) ≤ g(i+1, j) + g(i+1, j+1)` for `i < j < n`, and
`g(i, j) + g(i+1, j+2) ≤ g(i, j+1) + g(i+1, j+1)` for `i ≤ j` and `j + 2 ≤ n`. -/
theorem isRhombusConcave_chart_iff :
    IsRhombusConcave (fun v : Vertex n => g v.z (n - v.x)) ↔
      (∀ i j, i < j → j < n → g (i + 1) j + g i (j + 1) ≤ g i j + g (i + 1) (j + 1)) ∧
      (∀ i j, i < j → j < n → g i j + g (i + 2) (j + 1) ≤ g (i + 1) j + g (i + 1) (j + 1)) ∧
      (∀ i j, i ≤ j → j + 2 ≤ n →
        g i j + g (i + 1) (j + 2) ≤ g i (j + 1) + g (i + 1) (j + 1)) := by
  rw [isRhombusConcave_def]
  constructor
  · intro hf
    refine ⟨fun i j hij hj => ?_, fun i j hij hj => ?_, fun i j hij hj => ?_⟩
    · have := hf (ChartRhombus₁.isRhombus (n := n) (o₁ := Vertex.ofYZ n (j - i) i (by omega))
        (a₁ := Vertex.ofYZ n (j - (i + 1)) (i + 1) (by omega))
        (o₂ := Vertex.ofYZ n (j + 1 - (i + 1)) (i + 1) (by omega))
        (a₂ := Vertex.ofYZ n (j + 1 - i) i (by omega)) (by simp [ChartRhombus₁]; omega))
      rwa [apply_ofYZ g (by omega), apply_ofYZ g (by omega), apply_ofYZ g (by omega),
        apply_ofYZ g (by omega)] at this
    · have := hf (ChartRhombus₂.isRhombus (n := n)
        (o₁ := Vertex.ofYZ n (j - (i + 1)) (i + 1) (by omega))
        (a₁ := Vertex.ofYZ n (j - i) i (by omega))
        (o₂ := Vertex.ofYZ n (j + 1 - (i + 1)) (i + 1) (by omega))
        (a₂ := Vertex.ofYZ n (j + 1 - (i + 2)) (i + 2) (by omega)) (by simp [ChartRhombus₂]; omega))
      rwa [apply_ofYZ g (by omega), apply_ofYZ g (by omega), apply_ofYZ g (by omega),
        apply_ofYZ g (by omega)] at this
    · have := hf (ChartRhombus₃.isRhombus (n := n)
        (o₁ := Vertex.ofYZ n (j + 1 - i) i (by omega))
        (a₁ := Vertex.ofYZ n (j - i) i (by omega))
        (o₂ := Vertex.ofYZ n (j + 1 - (i + 1)) (i + 1) (by omega))
        (a₂ := Vertex.ofYZ n (j + 2 - (i + 1)) (i + 1) (by omega)) (by simp [ChartRhombus₃]; omega))
      rwa [apply_ofYZ g (by omega), apply_ofYZ g (by omega), apply_ofYZ g (by omega),
        apply_ofYZ g (by omega)] at this
  · rintro ⟨h₁, h₂, h₃⟩ a b c d hr
    -- Each rhombus is one of the three families, with its obtuse and acute pairs in some order.
    rcases hr.chartRhombus with (H | H | H | H) | (H | H | H | H) | (H | H | H | H)
    all_goals first
      | have key := H.le g h₁
      | have key := H.le g h₂
      | have key := H.le g h₃
    all_goals simpa only [add_comm] using key

end Ordered

/-- The chart side `i = 0` is the side `A → B`. -/
private theorem gtChart_zero_left [Zero R] (f : Vertex n → R) {j : ℕ} (hj : j ≤ n) :
    gtChart f 0 j = f (Vertex.edgePoint n 0 ⟨j, by omega⟩) := by
  rw [gtChart_of_le f (Nat.zero_le j) hj]
  congr 1
  ext <;> simp

/-- The chart side `j = n` is the side `B → C`. -/
private theorem gtChart_right [Zero R] (f : Vertex n → R) {i : ℕ} (hi : i ≤ n) :
    gtChart f i n = f (Vertex.edgePoint n 1 ⟨i, by omega⟩) := by
  rw [gtChart_of_le f hi le_rfl]
  congr 1
  ext <;> simp
  omega

/-- The chart diagonal `i = j` is the side `C → A`. -/
private theorem gtChart_self [Zero R] (f : Vertex n → R) {j : ℕ} (hj : j ≤ n) :
    gtChart f j j = f (Vertex.edgePoint n 2 ⟨n - j, by omega⟩) := by
  rw [gtChart_of_le f le_rfl hj]
  congr 1
  ext <;> simp
  omega

end Chart

/-! ### The Gelfand-Tsetlin pattern of an integer hive -/

/-- Splitting off the last term of a prefix sum over `Fin n`. -/
private theorem sum_val_lt_succ (l : Fin n → ℤ) (r : Fin n) :
    ∑ s : Fin n with s.val < r.val + 1, l s = (∑ s : Fin n with s.val < r.val, l s) + l r := by
  rw [show ({s : Fin n | s.val < r.val + 1} : Finset (Fin n)) =
      insert r ({s : Fin n | s.val < r.val} : Finset (Fin n)) by
    ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega, Finset.sum_insert (by simp), add_comm]

private theorem isRhombusConcave_gtChart (h : IntegerHive n) :
    IsRhombusConcave (fun v : Vertex n => gtChart (⇑h) v.z (n - v.x)) := by
  simpa only [gtChart_z_sub_x] using h.isRhombusConcave

/-- The **Gelfand-Tsetlin pattern of an integer hive**: its entry `(i, j)`, `i < j ≤ n`, is the
horizontal difference `h(i+1, j) - h(i, j)` in the chart. The first two families of rhombus
inequalities are the interlacing inequalities. -/
def toGTPattern (h : IntegerHive n) : GTPattern n where
  entry i j := if i < j then gtChart (⇑h) (i + 1) j - gtChart (⇑h) i j else 0
  zeros' {i j} hij := by
    rcases hij with hj | hj
    · simp [gtChart_of_lt _ hj]
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
  simp only [boundary_def]
  rw [sum_boundaryLinear_lt _ 0 j hj, Vertex.edgePoint_zero_zero, h.apply_cornerA, sub_zero,
    gtChart_zero_left _ hj]

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

/-- The completion of any pattern satisfies the first two families of rhombus inequalities, which
are its interlacing inequalities; so it is rhombus-concave iff it satisfies the third family. -/
theorem isRhombusConcave_gtCompletion_iff (l : Fin n → ℤ) (P : GTPattern n) :
    IsRhombusConcave (fun v : Vertex n => gtCompletion l P v.z (n - v.x)) ↔
      ∀ i j, i ≤ j → j + 2 ≤ n →
        gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
          gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) := by
  rw [isRhombusConcave_chart_iff]
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
theorem gtCompletion_toGTPattern_add_le (h : IntegerHive n) :
    ∀ i j, i ≤ j → j + 2 ≤ n →
      gtCompletion (h.boundary 0) h.toGTPattern i j +
          gtCompletion (h.boundary 0) h.toGTPattern (i + 1) (j + 2) ≤
        gtCompletion (h.boundary 0) h.toGTPattern i (j + 1) +
          gtCompletion (h.boundary 0) h.toGTPattern (i + 1) (j + 1) := by
  refine (isRhombusConcave_gtCompletion_iff _ _).mp ?_
  simpa only [← apply_eq_gtCompletion] using h.isRhombusConcave

/-- The top row of the pattern of a hive is its second boundary weight. -/
theorem topRow_toGTPattern (h : IntegerHive n) : h.toGTPattern.topRow = h.boundary 1 := by
  ext i
  rw [GTPattern.topRow_apply, h.toGTPattern_apply i.2, gtChart_right _ i.2,
    gtChart_right _ i.2.le, boundary_apply, show i.succ = ⟨i + 1, by omega⟩ from Fin.ext i.val_succ,
    show i.castSucc = ⟨i, by omega⟩ from Fin.ext i.val_castSucc]

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
  rw [GTPattern.weight_apply, h.rowSum_toGTPattern, h.rowSum_toGTPattern,
    gtChart_self _ r.2, gtChart_self _ r.2.le, gtChart_zero_left _ r.2, gtChart_zero_left _ r.2.le,
    boundary_apply, boundary_apply]
  have e₁ : r.rev.succ = ⟨n - r, by omega⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  have e₂ : r.rev.castSucc = ⟨n - (r + 1), by omega⟩ := Fin.ext (by simp [Fin.val_rev])
  rw [e₁, e₂, show r.succ = ⟨r + 1, by omega⟩ from Fin.ext r.val_succ,
    show r.castSucc = ⟨r, by omega⟩ from Fin.ext r.val_castSucc]
  simp only [Nat.succ_eq_add_one]
  ring

/-! ### The integer hive of a pattern -/

/-- The integer hive whose values are the chart completion of a boundary weight `l` and a pattern
`P` satisfying the third family of rhombus inequalities. -/
def ofGTPattern (l : Fin n → ℤ) (P : GTPattern n)
    (hP : ∀ i j, i ≤ j → j + 2 ≤ n →
      gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
        gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1)) : IntegerHive n where
  value v := gtCompletion l P v.z (n - v.x)
  value_cornerA' := by simp
  le_of_isRhombus' hr :=
    (isRhombusConcave_def _).mp ((isRhombusConcave_gtCompletion_iff l P).mpr hP) hr

variable {l : Fin n → ℤ} {P : GTPattern n}
  {hP : ∀ i j, i ≤ j → j + 2 ≤ n →
    gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
      gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1)}

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
    ofGTPattern (h.boundary 0) h.toGTPattern h.gtCompletion_toGTPattern_add_le = h := by
  ext v
  rw [ofGTPattern_apply, ← apply_eq_gtCompletion]

/-- The clockwise boundary of the hive of a pattern: its sides are `l`, the top row of `P`, and
the dual of `l + wt(P)`. -/
theorem boundary_ofGTPattern :
    (ofGTPattern l P hP).boundary = ![l, P.topRow, fun i => -(l i.rev + P.weight i.rev)] := by
  ext s i
  fin_cases s
  · simp only [boundary_apply, ofGTPattern_apply, Vertex.edgePoint_zero_z,
      Vertex.edgePoint_zero_x, Fin.zero_eta, Matrix.cons_val_zero, gtCompletion_zero_left]
    rw [show n - (n - (i.succ : ℕ)) = (i : ℕ) + 1 by simp; omega,
      show n - (n - (i.castSucc : ℕ)) = i by simp; omega, sum_val_lt_succ]
    abel
  · simp only [boundary_apply, ofGTPattern_apply, Vertex.edgePoint_one_z,
      Vertex.edgePoint_one_x, Nat.sub_zero, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      GTPattern.topRow_apply, Fin.val_succ, Fin.val_castSucc, gtCompletion_succ_left]
    abel
  · have e : n - (i : ℕ) = i.rev + 1 := by rw [Fin.val_rev]; omega
    simp only [boundary_apply, ofGTPattern_apply, Vertex.edgePoint_two_z,
      Vertex.edgePoint_two_x, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Fin.val_succ, Fin.val_castSucc,
      show n - ((i : ℕ) + 1) = i.rev by rw [Fin.val_rev], e, gtCompletion_self,
      sum_val_lt_succ, GTPattern.weight_apply]
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

/-- The hive of a pattern with top row `μ` and weight `γ - λ` has boundary `(λ, μ, γ*)`. -/
theorem boundary_ofGTPattern_eq_productBoundary {P : GTPattern n}
    {hP : ∀ i j, i ≤ j → j + 2 ≤ n →
      gtCompletion lam.1 P i j + gtCompletion lam.1 P (i + 1) (j + 2) ≤
        gtCompletion lam.1 P i (j + 1) + gtCompletion lam.1 P (i + 1) (j + 1)}
    (hTop : P.topRow = μ.1) (hW : P.weight = γ.1 - lam.1) :
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
        ∀ i j, i ≤ j → j + 2 ≤ n →
          gtCompletion lam.1 P i j + gtCompletion lam.1 P (i + 1) (j + 2) ≤
            gtCompletion lam.1 P i (j + 1) + gtCompletion lam.1 P (i + 1) (j + 1)} where
  toFun h := ⟨h.1.toGTPattern, topRow_toGTPattern_of_boundary_eq lam μ γ h.2,
    weight_toGTPattern_of_boundary_eq lam μ γ h.2, by
      simpa only [h.2, productBoundary_zero] using h.1.gtCompletion_toGTPattern_add_le⟩
  invFun P := ⟨ofGTPattern lam.1 P.1 P.2.2.2,
    boundary_ofGTPattern_eq_productBoundary lam μ γ P.2.1 P.2.2.1⟩
  left_inv h := by
    obtain ⟨h, hB⟩ := h
    ext v
    simp only [ofGTPattern_apply]
    rw [apply_eq_gtCompletion h v, hB, productBoundary_zero]
  right_inv P := Subtype.ext (toGTPattern_ofGTPattern (hP := P.2.2.2))

@[simp]
theorem fixedIntegerHiveEquivGTPattern_apply_coe (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h : GTPattern n) = h.1.toGTPattern := (rfl)

@[simp]
theorem fixedIntegerHiveEquivGTPattern_symm_apply_apply
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1 ∧
      ∀ i j, i ≤ j → j + 2 ≤ n →
        gtCompletion lam.1 P i j + gtCompletion lam.1 P (i + 1) (j + 2) ≤
          gtCompletion lam.1 P i (j + 1) + gtCompletion lam.1 P (i + 1) (j + 1)})
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
      ∀ i j, i ≤ j → j + 2 ≤ n →
        gtCompletion lam.1 P i j + gtCompletion lam.1 P (i + 1) (j + 2) ≤
          gtCompletion lam.1 P i (j + 1) + gtCompletion lam.1 P (i + 1) (j + 1) := by
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
theorem gtCompletion_add_le_of_gap (l : Fin (n + 1) → ℤ) (P : GTPattern (n + 1))
    (hGap : ∀ r : Fin n, P.topRow 0 - P.topRow (Fin.last n) ≤ l r.castSucc - l r.succ) :
    ∀ i j, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
        gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) := by
  intro i j hij hj
  -- The partial sums of `l` contribute `l (j + 1) - l j`.
  have hl₁ := sum_val_lt_succ l ⟨j, by omega⟩
  have hl₂ := sum_val_lt_succ l ⟨j + 1, by omega⟩
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
  rw [show j + 2 = (j + 1) + 1 by omega, hl₂, show j + 1 + 1 = j + 2 by omega, hl₁]
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
      gtCompletion_add_le_of_gap lam.1 P (by simpa only [hP.1] using hGap)⟩⟩

@[simp]
theorem fixedIntegerHiveEquivGTPatternOfGap_apply_coe (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap h : GTPattern (n + 1)) =
      h.1.toGTPattern := (rfl)

/-- Under the uniform input gap, the hive count of `(λ, μ, γ*)` is the number of Gelfand-Tsetlin
patterns with top row `μ` and weight `γ - λ`. -/
theorem hiveCount_eq_card_gtPattern_of_gap (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.weight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPatternOfGap lam μ γ hGap)

end TauCeti.Hive
