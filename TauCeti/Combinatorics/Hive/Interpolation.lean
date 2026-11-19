/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Function
public import TauCeti.Combinatorics.Hive.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Piecewise-linear interpolation of lattice functions and the concavity criterion

The lines `y = const`, `z = const` and `y + z = const` through the integer points of the `(y, z)`
chart cut the triangle `0 ≤ y, 0 ≤ z, y + z ≤ n` into the unit triangles of `Δₙ`.
`Hive.interpolation f` is the function on that triangle which agrees with `f : Vertex n → 𝕜` at
the lattice points and is affine on every closed unit triangle (`Hive.interpolation_vertex`,
`Hive.interpolation_up`, `Hive.interpolation_down`). The chart differs from the equilateral
embedding `Hive.Vertex.plane` by an affine change of coordinates, so concavity does not depend on
which of the two is used.

The main result is the concavity criterion `Hive.concaveOn_interpolation_iff`: the interpolation
is concave on the triangle exactly when `f` satisfies all unit-rhombus inequalities. In particular
the interpolation of every hive is concave (`Hive.concaveOn_interpolation`), which is how hives
are compared with real geometry (honeycombs, Hermitian spectra).

## Main definitions

* `TauCeti.Hive.chartTriangle 𝕜 n`: the triangle `0 ≤ y, 0 ≤ z, y + z ≤ n` in `𝕜 × 𝕜`.
* `TauCeti.Hive.interpolation f`: the interpolation of `f : Vertex n → 𝕜` that is affine on unit
  triangles.

## Main results

* `TauCeti.Hive.IsRhombusConcave.le_barycentricLinear`: discrete supporting planes.
* `TauCeti.Hive.concaveOn_interpolation_iff`: the interpolation is concave iff `f` is
  rhombus-concave; `TauCeti.Hive.concaveOn_interpolation` for hives.

## Implementation notes

The forward direction of the criterion evaluates concavity at the common midpoint of the two
diagonals of a rhombus. The converse rests on `Hive.IsRhombusConcave.le_barycentricLinear`. Around
a corner of the unit triangle, the plane splits into the six sectors spanned by consecutive unit
steps `chartStep k`, `chartStep (k + 1)`. In a sector, summing rhombus inequalities over a lattice
parallelogram and along a lattice line bounds the function by its slopes at the corner, and the
rhombi meeting at the corner bound those slopes by the slopes of the affine function. The
interpolation is then, at every point, the value of an affine function that majorizes it
everywhere on the triangle, hence concave.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2.
-/

public section

namespace TauCeti.Hive

variable {n : ℕ}

/-! ### The lattice region of the `(y, z)` chart and the extension by zero -/

/-- The integer points of the `(y, z)` chart of `Δₙ`. -/
private def chartRegion (n : ℕ) : Set (ℤ × ℤ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ n}

private theorem mem_chartRegion {p : ℤ × ℤ} :
    p ∈ chartRegion n ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ n := Iff.rfl

private theorem yz_mem_chartRegion (p : Vertex n) : p.yz ∈ chartRegion n := by
  have := p.sum_eq
  simp only [mem_chartRegion, Vertex.yz_fst, Vertex.yz_snd]
  omega

/-- The vertex with given `(y, z)` chart coordinates. -/
private def chartVertex (p : ℤ × ℤ) (hp : p ∈ chartRegion n) : Vertex n :=
  Vertex.ofYZ n p.1.toNat p.2.toNat (by obtain ⟨_, _, _⟩ := hp; omega)

private theorem chartVertex_yz (p : Vertex n) : chartVertex p.yz (yz_mem_chartRegion p) = p := by
  ext <;> simp [chartVertex]

/-- Extend a lattice function by zero to all integer points of the `(y, z)` chart. -/
private def chartExtend {R : Type*} [Zero R] (f : Vertex n → R) (p : ℤ × ℤ) : R :=
  if hp : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ n then f (chartVertex p hp) else 0

private theorem chartExtend_of_mem {R : Type*} [Zero R] (f : Vertex n → R) {p : ℤ × ℤ}
    (hp : p ∈ chartRegion n) : chartExtend f p = f (chartVertex p hp) := dite_eq_left hp

private theorem chartExtend_yz {R : Type*} [Zero R] (f : Vertex n → R) (p : Vertex n) :
    chartExtend f p.yz = f p := by
  rw [chartExtend_of_mem f (yz_mem_chartRegion p), chartVertex_yz]

private theorem chartExtend_of_yz_eq {R : Type*} [Zero R] (f : Vertex n → R) {x : ℤ × ℤ}
    {p : Vertex n} (h : p.yz = x) : chartExtend f x = f p := by
  rw [← h, chartExtend_yz]

/-! ### Hexagon identities for the six unit steps -/

private theorem chartStep_add_two (k : Fin 6) :
    chartStep (k + 2) = chartStep (k + 1) - chartStep k := by
  fin_cases k <;> ext <;> simp [chartStep_def]

private theorem chartStep_add_three (k : Fin 6) : chartStep (k + 3) = -chartStep k := by
  fin_cases k <;> ext <;> simp [chartStep_def]

private theorem chartStep_add_four (k : Fin 6) : chartStep (k + 4) = -chartStep (k + 1) := by
  fin_cases k <;> ext <;> simp [chartStep_def]

private theorem chartStep_add_five (k : Fin 6) :
    chartStep (k + 5) = chartStep k - chartStep (k + 1) := by
  fin_cases k <;> ext <;> simp [chartStep_def]

/-- Every integer vector lies in the sector spanned by two consecutive unit steps. -/
private theorem exists_chartStep_sector (d : ℤ × ℤ) :
    ∃ (m : Fin 6) (s t : ℕ), d = s • chartStep m + t • chartStep (m + 1) := by
  obtain ⟨a, b⟩ := d
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · exact ⟨0, a.toNat, b.toNat, by ext <;> simp [chartStep_def] <;> omega⟩
  · rcases le_total 0 (a + b) with hab | hab
    · exact ⟨5, (-b).toNat, (a + b).toNat, by ext <;> simp [chartStep_def] <;> omega⟩
    · exact ⟨4, (-a - b).toNat, a.toNat, by ext <;> simp [chartStep_def] <;> omega⟩
  · rcases le_total 0 (a + b) with hab | hab
    · exact ⟨1, (a + b).toNat, (-a).toNat, by ext <;> simp [chartStep_def] <;> omega⟩
    · exact ⟨2, b.toNat, (-a - b).toNat, by ext <;> simp [chartStep_def] <;> omega⟩
  · exact ⟨3, (-a).toNat, (-b).toNat, by ext <;> simp [chartStep_def] <;> omega⟩

/-- The lattice parallelogram spanned by two consecutive unit steps between two points of the
region stays in the region: each barycentric coordinate is monotone along both steps. -/
private theorem mem_chartRegion_of_parallelogram {k : Fin 6} {p : ℤ × ℤ} {s t i j : ℕ}
    (hp : p ∈ chartRegion n) (hv : p + s • chartStep k + t • chartStep (k + 1) ∈ chartRegion n)
    (hi : i ≤ s) (hj : j ≤ t) : p + i • chartStep k + j • chartStep (k + 1) ∈ chartRegion n := by
  simp only [mem_chartRegion] at *
  fin_cases k <;> simp [chartStep_def] at * <;> omega

/-! ### Rhombus concavity in the chart -/

section Linear

variable {R : Type*} [AddCommGroup R]

/-- The additive map `d ↦ d.1 • α + d.2 • β` on chart displacements. -/
private def chartLinear (α β : R) : ℤ × ℤ →+ R := (zmultiplesHom R α).coprod (zmultiplesHom R β)

private theorem chartLinear_apply (α β : R) (d : ℤ × ℤ) :
    chartLinear α β d = d.1 • α + d.2 • β := by
  simp [chartLinear]

/-- The difference of a barycentric-affine function at two vertices, in chart coordinates. -/
private theorem barycentricLinear_sub_barycentricLinear (c₀ α β γ : R) (p q : Vertex n) :
    barycentricLinear c₀ α β γ q - barycentricLinear c₀ α β γ p =
      chartLinear (β - α) (γ - α) (q.yz - p.yz) := by
  have hx : ((q.x : ℤ) - p.x) = -((q.y : ℤ) - p.y) - ((q.z : ℤ) - p.z) := by
    have := p.sum_eq
    have := q.sum_eq
    omega
  have hx' : (q.x : ℤ) • α - (p.x : ℤ) • α = (-((q.y : ℤ) - p.y) - ((q.z : ℤ) - p.z)) • α := by
    rw [← hx]; module
  simp only [barycentricLinear_apply, chartLinear_apply, Prod.fst_sub, Prod.snd_sub, Vertex.yz_fst,
    Vertex.yz_snd, ← natCast_zsmul] at hx' ⊢
  rw [show (c₀ + (q.x : ℤ) • α + (q.y : ℤ) • β + (q.z : ℤ) • γ) -
      (c₀ + (p.x : ℤ) • α + (p.y : ℤ) • β + (p.z : ℤ) • γ) =
      ((q.x : ℤ) • α - (p.x : ℤ) • α) + ((q.y : ℤ) • β - (p.y : ℤ) • β) +
        ((q.z : ℤ) • γ - (p.z : ℤ) • γ) by abel, hx']
  module

end Linear

section Ordered

variable {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]

/-- The unit-rhombus inequalities in the `(y, z)` chart: on the rhombus with acute corners `p` and
`p + chartStep k + chartStep (k + 1)`, the acute sum is at most the obtuse sum. -/
private def ChartConcave (n : ℕ) (g : ℤ × ℤ → R) : Prop :=
  ∀ (k : Fin 6) (p : ℤ × ℤ), p ∈ chartRegion n → p + chartStep k ∈ chartRegion n →
    p + chartStep (k + 1) ∈ chartRegion n → p + chartStep k + chartStep (k + 1) ∈ chartRegion n →
    g p + g (p + chartStep k + chartStep (k + 1)) ≤ g (p + chartStep k) + g (p + chartStep (k + 1))

/-- The barycentric vector of a chart displacement. -/
private def baryStep (d : ℤ × ℤ) : Fin 3 → ℤ := ![-d.1 - d.2, d.1, d.2]

private theorem hasStep_chartVertex {p q : ℤ × ℤ} (hp : p ∈ chartRegion n)
    (hq : q ∈ chartRegion n) :
    HasStep (chartVertex p hp) (chartVertex q hq) (baryStep (q - p)) := by
  obtain ⟨_, _, _⟩ := hp
  obtain ⟨_, _, _⟩ := hq
  rw [hasStep_iff]
  intro i
  fin_cases i <;> simp [chartVertex, baryStep] <;> omega

private theorem isUnitStep_baryStep (k : Fin 6) : IsUnitStep (baryStep (chartStep k)) := by
  fin_cases k <;> simp [isUnitStep_iff, baryStep, chartStep_def, Fin.sum_univ_three]

private theorem sum_baryStep_mul (k : Fin 6) :
    (∑ i, baryStep (chartStep k) i * baryStep (chartStep (k + 1)) i) = 1 := by
  fin_cases k <;> simp [baryStep, chartStep_def, Fin.sum_univ_three]

omit [IsOrderedAddMonoid R] in
private theorem chartConcave_chartExtend {f : Vertex n → R} (hf : IsRhombusConcave f) :
    ChartConcave n (chartExtend f) := by
  intro k p h₀ h₁ h₂ h₃
  rw [chartExtend_of_mem f h₀, chartExtend_of_mem f h₁, chartExtend_of_mem f h₂,
    chartExtend_of_mem f h₃]
  refine (isRhombusConcave_def f).mp hf ((isRhombus_of_hasStep_iff (isUnitStep_baryStep k)
    (isUnitStep_baryStep (k + 1)) ?_ ?_ ?_).mpr (sum_baryStep_mul k))
  · simpa using hasStep_chartVertex h₀ h₁
  · simpa using hasStep_chartVertex h₀ h₂
  · convert hasStep_chartVertex h₀ h₃ using 1
    funext i
    fin_cases i <;> simp [baryStep] <;> ring

variable {g : ℤ × ℤ → R}

omit [IsOrderedAddMonoid R] in
/-- The rhombus whose short diagonal runs from `p` to `p + chartStep m`: its acute corners are
`p + chartStep (m + 5)` and `p + chartStep (m + 1)`. -/
private theorem ChartConcave.corner (hg : ChartConcave n g) (m : Fin 6) {p : ℤ × ℤ}
    (hp : p ∈ chartRegion n) (hm : p + chartStep m ∈ chartRegion n)
    (hm₁ : p + chartStep (m + 1) ∈ chartRegion n) (hm₅ : p + chartStep (m + 5) ∈ chartRegion n) :
    g (p + chartStep (m + 5)) + g (p + chartStep (m + 1)) ≤ g (p + chartStep m) + g p := by
  have hm₂ : m + 1 + 1 = m + 2 := by fin_cases m <;> rfl
  have e₅ : chartStep (m + 5) = chartStep m - chartStep (m + 1) := chartStep_add_five m
  have e₂ : chartStep (m + 2) = chartStep (m + 1) - chartStep m := chartStep_add_two m
  have e₁ : p + chartStep (m + 5) + chartStep (m + 1) = p + chartStep m := by rw [e₅]; abel
  have e₀ : p + chartStep (m + 5) + chartStep (m + 2) = p := by rw [e₅, e₂]; abel
  have e₃ : p + chartStep (m + 5) + chartStep (m + 1) + chartStep (m + 2) =
      p + chartStep (m + 1) := by rw [e₅, e₂]; abel
  have M := hg (m + 1) (p + chartStep (m + 5)) hm₅ (by rwa [e₁]) (by rwa [hm₂, e₀])
    (by rwa [hm₂, e₃])
  rwa [hm₂, e₃, e₁, e₀] at M

/-- Line concavity from the two corner rhombi at `q` on the side of `chartStep j` and
`chartStep (j + 1)`, where `j` is `k + 1` or `k + 4`. -/
private theorem ChartConcave.line_of_side (hg : ChartConcave n g) {k j : Fin 6} {q : ℤ × ℤ}
    (hj : j = k + 1 ∨ j = k + 4) (h₁ : q - chartStep k ∈ chartRegion n) (h₂ : q ∈ chartRegion n)
    (h₃ : q + chartStep k ∈ chartRegion n) (h₄ : q + chartStep j ∈ chartRegion n)
    (h₅ : q + chartStep (j + 1) ∈ chartRegion n) :
    g (q - chartStep k) + g (q + chartStep k) ≤ g q + g q := by
  have hneg : q - chartStep k = q + chartStep (k + 3) := by
    rw [chartStep_add_three, sub_eq_add_neg]
  rw [hneg] at h₁ ⊢
  -- the two corner rhombi have short diagonals along `chartStep j` and `chartStep (j + 1)`
  have hj₁ : j + 1 + 5 = j := by fin_cases j <;> rfl
  have M₁ := hg.corner j h₂ h₄ h₅ (by
    rcases hj with rfl | rfl
    · rwa [show k + 1 + 5 = k by fin_cases k <;> rfl]
    · rwa [show k + 4 + 5 = k + 3 by fin_cases k <;> rfl])
  have M₂ := hg.corner (j + 1) h₂ h₅ (by
    rcases hj with rfl | rfl
    · rwa [show k + 1 + 1 + 1 = k + 3 by fin_cases k <;> rfl]
    · rwa [show k + 4 + 1 + 1 = k by fin_cases k <;> rfl]) (by rwa [hj₁])
  rw [hj₁] at M₂
  have h := add_nonneg (sub_nonneg.mpr M₁) (sub_nonneg.mpr M₂)
  rw [← sub_nonneg]
  rcases hj with rfl | rfl
  · rw [show k + 1 + 5 = k by fin_cases k <;> rfl,
      show k + 1 + 1 + 1 = k + 3 by fin_cases k <;> rfl] at h
    convert h using 1
    abel
  · rw [show k + 4 + 5 = k + 3 by fin_cases k <;> rfl,
      show k + 4 + 1 + 1 = k by fin_cases k <;> rfl] at h
    convert h using 1
    abel

/-- Rhombus concavity implies concavity along every lattice line. -/
private theorem ChartConcave.line (hg : ChartConcave n g) {k : Fin 6} {q : ℤ × ℤ}
    (h₁ : q - chartStep k ∈ chartRegion n) (h₂ : q ∈ chartRegion n)
    (h₃ : q + chartStep k ∈ chartRegion n) :
    g (q - chartStep k) + g (q + chartStep k) ≤ g q + g q := by
  -- the corner rhombi lie on the side of `chartStep (k + 1)` for even `k`, and on the side of
  -- `chartStep (k + 4)` for odd `k`
  fin_cases k <;>
    first
    | exact hg.line_of_side (Or.inl rfl) h₁ h₂ h₃
        (by simp [mem_chartRegion, chartStep_def] at h₁ h₂ h₃ ⊢; omega)
        (by simp [mem_chartRegion, chartStep_def] at h₁ h₂ h₃ ⊢; omega)
    | exact hg.line_of_side (Or.inr rfl) h₁ h₂ h₃
        (by simp [mem_chartRegion, chartStep_def] at h₁ h₂ h₃ ⊢; omega)
        (by simp [mem_chartRegion, chartStep_def] at h₁ h₂ h₃ ⊢; omega)

/-- Along a lattice line inside the region, the function lies below its first secant. -/
private theorem ChartConcave.le_line (hg : ChartConcave n g) {k : Fin 6} {p : ℤ × ℤ} {s : ℕ}
    (hmem : ∀ i ≤ s, p + i • chartStep k ∈ chartRegion n) :
    g (p + s • chartStep k) ≤ g p + s • (g (p + chartStep k) - g p) := by
  set u := chartStep k
  have step : ∀ i, i + 1 ≤ s → g (p + (i + 1) • u) - g (p + i • u) ≤ g (p + u) - g p := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have e₁ : p + (i + 1) • u - u = p + i • u := by rw [succ_nsmul]; abel
      have e₂ : p + (i + 1) • u + u = p + (i + 1 + 1) • u := by rw [succ_nsmul _ (i + 1)]; abel
      have hL := hg.line (q := p + (i + 1) • u) (by rw [e₁]; exact hmem i (by omega))
        (hmem (i + 1) (by omega)) (by rw [e₂]; exact hmem (i + 1 + 1) hi)
      rw [e₁, e₂] at hL
      refine le_trans ?_ (ih (by omega))
      rw [sub_le_sub_iff]
      simpa [add_comm] using hL
  have key : ∀ i ≤ s, g (p + i • u) ≤ g p + i • (g (p + u) - g p) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      calc g (p + (i + 1) • u)
          = g (p + i • u) + (g (p + (i + 1) • u) - g (p + i • u)) := by abel
        _ ≤ (g p + i • (g (p + u) - g p)) + (g (p + u) - g p) :=
          add_le_add (ih (by omega)) (step i hi)
        _ = g p + (i + 1) • (g (p + u) - g p) := by rw [succ_nsmul]; abel
  exact key s le_rfl

/-- Summing rhombus inequalities over a lattice parallelogram. -/
private theorem ChartConcave.parallelogram (hg : ChartConcave n g) {k : Fin 6} {p : ℤ × ℤ}
    {s t : ℕ}
    (hmem : ∀ i ≤ s, ∀ j ≤ t, p + i • chartStep k + j • chartStep (k + 1) ∈ chartRegion n) :
    g p + g (p + s • chartStep k + t • chartStep (k + 1)) ≤
      g (p + s • chartStep k) + g (p + t • chartStep (k + 1)) := by
  set u := chartStep k
  set w := chartStep (k + 1)
  have column : ∀ i, i + 1 ≤ s → ∀ j ≤ t, g (p + i • u) + g (p + (i + 1) • u + j • w) ≤
      g (p + (i + 1) • u) + g (p + i • u + j • w) := by
    intro i hi j
    induction j with
    | zero => intro _; simp [add_comm]
    | succ j ih =>
      intro hj
      have e₁ : p + i • u + j • w + u = p + (i + 1) • u + j • w := by rw [succ_nsmul]; abel
      have e₂ : p + i • u + j • w + w = p + i • u + (j + 1) • w := by rw [succ_nsmul _ j]; abel
      have e₃ : p + i • u + j • w + u + w = p + (i + 1) • u + (j + 1) • w := by
        rw [succ_nsmul _ i, succ_nsmul _ j]; abel
      have M := hg k (p + i • u + j • w) (hmem i (by omega) j (by omega))
        (by rw [e₁]; exact hmem (i + 1) hi j (by omega))
        (by rw [e₂]; exact hmem i (by omega) (j + 1) hj)
        (by rw [e₃]; exact hmem (i + 1) hi (j + 1) hj)
      rw [e₃, e₁, e₂] at M
      have h := add_nonneg (sub_nonneg.mpr (ih (by omega))) (sub_nonneg.mpr M)
      rw [← sub_nonneg]
      convert h using 1
      abel
  have key : ∀ i ≤ s, g p + g (p + i • u + t • w) ≤ g (p + i • u) + g (p + t • w) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h := add_nonneg (sub_nonneg.mpr (ih (by omega))) (sub_nonneg.mpr (column i hi t le_rfl))
      rw [← sub_nonneg]
      convert h using 1
      abel
  exact key s le_rfl

/-- In the sector of two consecutive unit steps, the function lies below the affine function
with its slopes at the corner. -/
private theorem ChartConcave.le_sector (hg : ChartConcave n g) {k : Fin 6} {p : ℤ × ℤ} {s t : ℕ}
    (hp : p ∈ chartRegion n) (hv : p + s • chartStep k + t • chartStep (k + 1) ∈ chartRegion n) :
    g (p + s • chartStep k + t • chartStep (k + 1)) ≤
      g p + s • (g (p + chartStep k) - g p) + t • (g (p + chartStep (k + 1)) - g p) := by
  have hmem := fun i (hi : i ≤ s) j (hj : j ≤ t) => mem_chartRegion_of_parallelogram hp hv hi hj
  have hP := hg.parallelogram hmem
  have hs := hg.le_line (k := k) (s := s) fun i hi => by simpa using hmem i hi 0 (Nat.zero_le _)
  have ht := hg.le_line (k := k + 1) (s := t) fun j hj => by simpa using hmem 0 (Nat.zero_le _) j hj
  calc g (p + s • chartStep k + t • chartStep (k + 1))
      ≤ g (p + s • chartStep k) + g (p + t • chartStep (k + 1)) - g p :=
        le_sub_iff_add_le'.mpr hP
    _ ≤ (g p + s • (g (p + chartStep k) - g p)) +
          (g p + t • (g (p + chartStep (k + 1)) - g p)) - g p := by gcongr
    _ = g p + s • (g (p + chartStep k) - g p) + t • (g (p + chartStep (k + 1)) - g p) := by abel

/-- At a corner `p` of a unit triangle on which `g` agrees with an affine function, the slope of
`g` along each unit step leaving `p` is at most the slope of the affine function. -/
private theorem ChartConcave.slope_le (hg : ChartConcave n g) {k : Fin 6} {p : ℤ × ℤ}
    (hp : p ∈ chartRegion n) (hk : p + chartStep k ∈ chartRegion n)
    (hk₁ : p + chartStep (k + 1) ∈ chartRegion n) {α β : R}
    (h₁ : chartLinear α β (chartStep k) = g (p + chartStep k) - g p)
    (h₂ : chartLinear α β (chartStep (k + 1)) = g (p + chartStep (k + 1)) - g p) (r : Fin 6)
    (hr : p + chartStep (k + r) ∈ chartRegion n) :
    g (p + chartStep (k + r)) - g p ≤ chartLinear α β (chartStep (k + r)) := by
  fin_cases r
  · simp only [Fin.zero_eta, add_zero] at hr ⊢
    rw [h₁]
  · simp only [Fin.mk_one] at hr ⊢
    rw [h₂]
  · -- the rhombus with obtuse corners `p`, `p + chartStep (k + 1)`
    simp only [Fin.reduceFinMk] at hr ⊢
    have hk' : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
    have M := hg.corner (k + 1) hp hk₁ (by rwa [hk'])
      (by rwa [show k + 1 + 5 = k by fin_cases k <;> rfl])
    rw [hk', show k + 1 + 5 = k by fin_cases k <;> rfl] at M
    rw [show chartLinear α β (chartStep (k + 2)) =
        chartLinear α β (chartStep (k + 1)) - chartLinear α β (chartStep k) by
      rw [chartStep_add_two, map_sub], h₁, h₂,
      show g (p + chartStep (k + 1)) - g p - (g (p + chartStep k) - g p) =
        g (p + chartStep (k + 1)) - g (p + chartStep k) by abel, sub_le_sub_iff]
    simpa [add_comm] using M
  · -- concavity along the line of `chartStep k`
    simp only [Fin.reduceFinMk] at hr ⊢
    have e : p + chartStep (k + 3) = p - chartStep k := by
      rw [chartStep_add_three, sub_eq_add_neg]
    rw [e] at hr ⊢
    have hL := hg.line hr hp hk
    rw [chartStep_add_three, map_neg, h₁, neg_sub, sub_le_sub_iff]
    exact hL
  · -- concavity along the line of `chartStep (k + 1)`
    simp only [Fin.reduceFinMk] at hr ⊢
    have e : p + chartStep (k + 4) = p - chartStep (k + 1) := by
      rw [chartStep_add_four, sub_eq_add_neg]
    rw [e] at hr ⊢
    have hL := hg.line hr hp hk₁
    rw [chartStep_add_four, map_neg, h₂, neg_sub, sub_le_sub_iff]
    exact hL
  · -- the rhombus with obtuse corners `p`, `p + chartStep k`
    simp only [Fin.reduceFinMk] at hr ⊢
    have M := hg.corner k hp hk hk₁ hr
    rw [show chartLinear α β (chartStep (k + 5)) =
        chartLinear α β (chartStep k) - chartLinear α β (chartStep (k + 1)) by
      rw [chartStep_add_five, map_sub], h₁, h₂,
      show g (p + chartStep k) - g p - (g (p + chartStep (k + 1)) - g p) =
        g (p + chartStep k) - g (p + chartStep (k + 1)) by abel, sub_le_sub_iff]
    simpa [add_comm] using M

/-- Discrete supporting planes in the chart: an affine function agreeing with `g` on a unit
triangle of the region majorizes `g` on the whole region. -/
private theorem ChartConcave.le_affine (hg : ChartConcave n g) {k : Fin 6} {p : ℤ × ℤ}
    (hp : p ∈ chartRegion n) (hk : p + chartStep k ∈ chartRegion n)
    (hk₁ : p + chartStep (k + 1) ∈ chartRegion n) {α β : R}
    (h₁ : chartLinear α β (chartStep k) = g (p + chartStep k) - g p)
    (h₂ : chartLinear α β (chartStep (k + 1)) = g (p + chartStep (k + 1)) - g p) {v : ℤ × ℤ}
    (hv : v ∈ chartRegion n) : g v ≤ g p + chartLinear α β (v - p) := by
  obtain ⟨m, s, t, hd⟩ := exists_chartStep_sector (v - p)
  obtain ⟨r, rfl⟩ : ∃ r, m = k + r := ⟨m - k, by abel⟩
  have hv' : p + s • chartStep (k + r) + t • chartStep (k + r + 1) = v := by
    rw [add_assoc, ← hd]; abel
  have hS := hg.le_sector (k := k + r) (s := s) (t := t) hp (by rwa [hv'])
  rw [hv'] at hS
  have hslope : ∀ r' : Fin 6, ∀ c : ℕ, (0 < c → p + chartStep (k + r') ∈ chartRegion n) →
      c • (g (p + chartStep (k + r')) - g p) ≤ c • chartLinear α β (chartStep (k + r')) := by
    intro r' c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc'
    · simp
    · exact nsmul_le_nsmul_right (hg.slope_le hp hk hk₁ h₁ h₂ r' (hc hc')) c
  have hmem : ∀ i ≤ s, ∀ j ≤ t, p + i • chartStep (k + r) + j • chartStep (k + r + 1) ∈
      chartRegion n := fun i hi j hj =>
    mem_chartRegion_of_parallelogram hp (by rwa [hv']) hi hj
  have hs := hslope r s fun hs => by simpa using hmem 1 hs 0 (Nat.zero_le _)
  have ht := hslope (r + 1) t fun ht => by
    simpa [add_assoc] using hmem 0 (Nat.zero_le _) 1 ht
  rw [← add_assoc] at ht
  calc g v ≤ g p + s • (g (p + chartStep (k + r)) - g p) +
        t • (g (p + chartStep (k + r + 1)) - g p) := hS
    _ ≤ g p + s • chartLinear α β (chartStep (k + r)) +
        t • chartLinear α β (chartStep (k + r + 1)) := by gcongr
    _ = g p + chartLinear α β (v - p) := by
      rw [hd, map_add, map_nsmul, map_nsmul, add_assoc]

end Ordered

/-- **Discrete supporting planes.** If a rhombus-concave function `f` agrees with a
barycentric-affine function `L` at the three corners `p`, `q`, `r` of a unit triangle, then
`f ≤ L` on all of `Δₙ`. Every unit triangle has this form: its corners, read from any one of them,
differ in the `(y, z)` chart by two consecutive unit steps. -/
theorem IsRhombusConcave.le_barycentricLinear {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] {f : Vertex n → R} (hf : IsRhombusConcave f) {k : Fin 6}
    {p q r : Vertex n} (hq : q.yz = p.yz + chartStep k) (hr : r.yz = p.yz + chartStep (k + 1))
    {c₀ α β γ : R} (hfp : f p = barycentricLinear c₀ α β γ p)
    (hfq : f q = barycentricLinear c₀ α β γ q) (hfr : f r = barycentricLinear c₀ α β γ r)
    (v : Vertex n) : f v ≤ barycentricLinear c₀ α β γ v := by
  have hg := chartConcave_chartExtend hf
  have hle := hg.le_affine (k := k) (p := p.yz) (α := β - α) (β := γ - α) (yz_mem_chartRegion p)
    (by rw [← hq]; exact yz_mem_chartRegion q) (by rw [← hr]; exact yz_mem_chartRegion r)
    (by rw [← hq, chartExtend_yz, chartExtend_yz, hfp, hfq,
      barycentricLinear_sub_barycentricLinear, hq, add_sub_cancel_left])
    (by rw [← hr, chartExtend_yz, chartExtend_yz, hfp, hfr,
      barycentricLinear_sub_barycentricLinear, hr, add_sub_cancel_left])
    (yz_mem_chartRegion v)
  rw [chartExtend_yz, chartExtend_yz, ← barycentricLinear_sub_barycentricLinear c₀ α β γ p v, hfp,
    add_sub_cancel] at hle
  exact hle

/-! ### The piecewise-linear interpolation -/

section Triangle

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]

variable (𝕜) in
/-- The triangle `0 ≤ y, 0 ≤ z, y + z ≤ n` of the `(y, z)` chart of `Δₙ`, in `𝕜 × 𝕜`. -/
def chartTriangle (n : ℕ) : Set (𝕜 × 𝕜) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ n}

@[simp] theorem mem_chartTriangle {q : 𝕜 × 𝕜} :
    q ∈ chartTriangle 𝕜 n ↔ 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ n := Iff.rfl

theorem convex_chartTriangle [IsOrderedRing 𝕜] : Convex 𝕜 (chartTriangle 𝕜 n) := by
  convert ((convex_halfSpace_ge (LinearMap.fst 𝕜 𝕜 𝕜).isLinear 0).inter
    (convex_halfSpace_ge (LinearMap.snd 𝕜 𝕜 𝕜).isLinear 0)).inter
    (convex_halfSpace_le (LinearMap.fst 𝕜 𝕜 𝕜 + LinearMap.snd 𝕜 𝕜 𝕜).isLinear (n : 𝕜)) using 1
  ext q
  simp [and_assoc]

private theorem natCast_mem_chartTriangle [IsOrderedRing 𝕜] (p : Vertex n) :
    ((p.y : 𝕜), (p.z : 𝕜)) ∈ chartTriangle 𝕜 n := by
  rw [mem_chartTriangle]
  dsimp only
  refine ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, ?_⟩
  have := Nat.mono_cast (α := 𝕜) (show p.y + p.z ≤ n by have := p.sum_eq; omega)
  rwa [Nat.cast_add] at this

end Triangle

section Interpolation

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- `ChartConcave.le_affine` for field-valued functions, with the affine function in coordinates. -/
private theorem ChartConcave.le_affine_of_corner {g : ℤ × ℤ → 𝕜} (hg : ChartConcave n g)
    {k : Fin 6} {p : ℤ × ℤ} (hp : p ∈ chartRegion n) (hk : p + chartStep k ∈ chartRegion n)
    (hk₁ : p + chartStep (k + 1) ∈ chartRegion n) {α β : 𝕜}
    (h₁ : ((chartStep k).1 : 𝕜) * α + ((chartStep k).2 : 𝕜) * β = g (p + chartStep k) - g p)
    (h₂ : ((chartStep (k + 1)).1 : 𝕜) * α + ((chartStep (k + 1)).2 : 𝕜) * β =
      g (p + chartStep (k + 1)) - g p) :
    ∀ v ∈ chartRegion n, g v ≤ (g p - p.1 * α - p.2 * β) + α * v.1 + β * v.2 := by
  intro v hv
  have h := hg.le_affine hp hk hk₁ (α := α) (β := β) (by simpa [chartLinear_apply] using h₁)
    (by simpa [chartLinear_apply] using h₂) hv
  simp only [chartLinear_apply, Prod.fst_sub, Prod.snd_sub, zsmul_eq_mul, Int.cast_sub] at h
  linarith

/-- At a lattice point on the side `y + z = n`, a rhombus-concave function agrees with an affine
function that majorizes it at all lattice points of `Δₙ`. -/
private theorem ChartConcave.exists_affine_of_add_eq {g : ℤ × ℤ → 𝕜} (hg : ChartConcave n g)
    {i j : ℤ} (hi : 0 ≤ i) (hj : 0 ≤ j) (hij : i + j = n) :
    ∃ c₀ c₁ c₂ : 𝕜, g (i, j) = c₀ + c₁ * i + c₂ * j ∧
      ∀ v ∈ chartRegion n, g v ≤ c₀ + c₁ * v.1 + c₂ * v.2 := by
  by_cases hj₁ : 1 ≤ j
  · -- the upward triangle below `(i, j)`
    refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 4) (p := (i, j))
      (α := g (i + 1, j - 1) - g (i, j - 1)) (β := g (i, j) - g (i, j - 1)) ⟨hi, hj, by omega⟩
      (by simp [chartStep_def, mem_chartRegion]; omega)
      (by simp [chartStep_def, mem_chartRegion]; omega)
      (by simp [chartStep_def, sub_eq_add_neg]) (by simp [chartStep_def, sub_eq_add_neg])⟩
    ring
  by_cases hi₁ : 1 ≤ i
  · -- the upward triangle to the left of `(i, j)`
    refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 2) (p := (i, j))
      (α := g (i, j) - g (i - 1, j)) (β := g (i - 1, j + 1) - g (i - 1, j)) ⟨hi, hj, by omega⟩
      (by simp [chartStep_def, mem_chartRegion]; omega)
      (by simp [chartStep_def, mem_chartRegion]; omega)
      (by simp [chartStep_def, sub_eq_add_neg]; ring) (by simp [chartStep_def, sub_eq_add_neg])⟩
    ring
  -- `n = 0`, and `Δₙ` is a single point
  refine ⟨g (i, j), 0, 0, by ring, fun v hv => ?_⟩
  obtain ⟨hv₁, hv₂, hv₃⟩ := hv
  obtain rfl : v = (i, j) := Prod.ext (by omega) (by omega)
  simp

variable [FloorRing 𝕜]

/-- The interpolation of `g : ℤ × ℤ → 𝕜` that is affine on the unit triangles cut out by the
lines `y = const`, `z = const` and `y + z = const`. -/
private def chartInterp (g : ℤ × ℤ → 𝕜) (q : 𝕜 × 𝕜) : 𝕜 :=
  if Int.fract q.1 + Int.fract q.2 ≤ 1 then
    (1 - Int.fract q.1 - Int.fract q.2) * g (⌊q.1⌋, ⌊q.2⌋) +
      Int.fract q.1 * g (⌊q.1⌋ + 1, ⌊q.2⌋) + Int.fract q.2 * g (⌊q.1⌋, ⌊q.2⌋ + 1)
  else
    (Int.fract q.1 + Int.fract q.2 - 1) * g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) +
      (1 - Int.fract q.2) * g (⌊q.1⌋ + 1, ⌊q.2⌋) + (1 - Int.fract q.1) * g (⌊q.1⌋, ⌊q.2⌋ + 1)

private theorem chartInterp_of_lt_one (g : ℤ × ℤ → 𝕜) (i j : ℤ) {a b : 𝕜} (ha : 0 ≤ a)
    (ha₁ : a < 1) (hb : 0 ≤ b) (hb₁ : b < 1) :
    chartInterp g ((i : 𝕜) + a, (j : 𝕜) + b) =
      if a + b ≤ 1 then (1 - a - b) * g (i, j) + a * g (i + 1, j) + b * g (i, j + 1)
      else (a + b - 1) * g (i + 1, j + 1) + (1 - b) * g (i + 1, j) + (1 - a) * g (i, j + 1) := by
  have hfa : Int.fract a = a := Int.fract_eq_self.mpr ⟨ha, ha₁⟩
  have hfb : Int.fract b = b := Int.fract_eq_self.mpr ⟨hb, hb₁⟩
  have hla : ⌊a⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨ha, ha₁⟩
  have hlb : ⌊b⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hb, hb₁⟩
  simp only [chartInterp, Int.fract_intCast_add, Int.floor_intCast_add, hfa, hfb, hla, hlb,
    add_zero]

private theorem chartInterp_intCast (g : ℤ × ℤ → 𝕜) (i j : ℤ) :
    chartInterp g ((i : 𝕜), (j : 𝕜)) = g (i, j) := by
  simpa using chartInterp_of_lt_one g i j (a := (0 : 𝕜)) (b := 0) le_rfl one_pos le_rfl one_pos

/-- On a closed upward unit triangle the interpolation is the barycentric combination of the
three corner values. -/
private theorem chartInterp_up (g : ℤ × ℤ → 𝕜) (i j : ℤ) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b ≤ 1) :
    chartInterp g ((i : 𝕜) + a, (j : 𝕜) + b) =
      (1 - a - b) * g (i, j) + a * g (i + 1, j) + b * g (i, j + 1) := by
  rcases (show a ≤ 1 by linarith).lt_or_eq with ha₁ | rfl
  · rcases (show b ≤ 1 by linarith).lt_or_eq with hb₁ | rfl
    · rw [chartInterp_of_lt_one g i j ha ha₁ hb hb₁, ite_eq_left hab]
    · obtain rfl : a = 0 := by linarith
      have := chartInterp_intCast g i (j + 1)
      push_cast at this
      rw [add_zero, this]
      ring
  · obtain rfl : b = 0 := by linarith
    have := chartInterp_intCast g (i + 1) j
    push_cast at this
    rw [add_zero, this]
    ring

/-- On a closed downward unit triangle the interpolation is the barycentric combination of the
three corner values. -/
private theorem chartInterp_down (g : ℤ × ℤ → 𝕜) (i j : ℤ) {a b : 𝕜} (ha : a ≤ 1) (hb : b ≤ 1)
    (hab : 1 ≤ a + b) :
    chartInterp g ((i : 𝕜) + a, (j : 𝕜) + b) =
      (a + b - 1) * g (i + 1, j + 1) + (1 - b) * g (i + 1, j) + (1 - a) * g (i, j + 1) := by
  rcases ha.lt_or_eq with ha₁ | rfl
  · rcases hb.lt_or_eq with hb₁ | rfl
    · rw [chartInterp_of_lt_one g i j (by linarith) ha₁ (by linarith) hb₁]
      split_ifs with h
      · obtain rfl : b = 1 - a := by linarith
        ring
      · rfl
    · have := chartInterp_up g i (j + 1) (a := a) (b := 0) (by linarith) le_rfl (by linarith)
      push_cast at this
      rw [add_zero] at this
      rw [this]
      ring
  · have := chartInterp_up g (i + 1) j (a := 0) (b := b) le_rfl (by linarith) (by linarith)
    push_cast at this
    rw [add_zero] at this
    rw [this]
    ring

/-- The interpolation of `f : Vertex n → 𝕜` over the triangle `chartTriangle 𝕜 n` of the `(y, z)`
chart: on each closed unit triangle it is the affine function through the values of `f` at the
three corners (`interpolation_vertex`, `interpolation_up`, `interpolation_down`). -/
def interpolation (f : Vertex n → 𝕜) : 𝕜 × 𝕜 → 𝕜 := chartInterp (chartExtend f)

/-- The interpolation of `f` agrees with `f` at every lattice point. -/
@[simp] theorem interpolation_vertex (f : Vertex n → 𝕜) (p : Vertex n) :
    interpolation f ((p.y : 𝕜), (p.z : 𝕜)) = f p := by
  have := chartInterp_intCast (chartExtend f) (p.y : ℤ) (p.z : ℤ)
  push_cast at this
  rw [interpolation, this, chartExtend_of_yz_eq f (p := p) (Prod.ext (by simp) (by simp))]

/-- On the upward unit triangle with corners `p`, `p + (1, 0)` and `p + (0, 1)` in the `(y, z)`
chart, the interpolation is the barycentric combination of the corner values. -/
theorem interpolation_up (f : Vertex n → 𝕜) {p q r : Vertex n} (hq : q.yz = p.yz + (1, 0))
    (hr : r.yz = p.yz + (0, 1)) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    interpolation f ((p.y : 𝕜) + a, (p.z : 𝕜) + b) = (1 - a - b) * f p + a * f q + b * f r := by
  have := chartInterp_up (chartExtend f) (p.y : ℤ) (p.z : ℤ) ha hb hab
  push_cast at this
  have e₀ : chartExtend f ((p.y : ℤ), (p.z : ℤ)) = f p :=
    chartExtend_of_yz_eq f (Prod.ext (by simp) (by simp))
  have e₁ : chartExtend f ((p.y : ℤ) + 1, (p.z : ℤ)) = f q :=
    chartExtend_of_yz_eq f (Prod.ext (by simp [hq]) (by simp [hq]))
  have e₂ : chartExtend f ((p.y : ℤ), (p.z : ℤ) + 1) = f r :=
    chartExtend_of_yz_eq f (Prod.ext (by simp [hr]) (by simp [hr]))
  rw [interpolation, this, e₀, e₁, e₂]

/-- On the downward unit triangle with corners `p`, `p - (1, 0)` and `p - (0, 1)` in the
`(y, z)` chart, the interpolation is the barycentric combination of the corner values. -/
theorem interpolation_down (f : Vertex n → 𝕜) {p q r : Vertex n} (hq : q.yz = p.yz + (-1, 0))
    (hr : r.yz = p.yz + (0, -1)) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    interpolation f ((p.y : 𝕜) - a, (p.z : 𝕜) - b) = (1 - a - b) * f p + a * f q + b * f r := by
  have := chartInterp_down (chartExtend f) ((p.y : ℤ) - 1) ((p.z : ℤ) - 1) (a := 1 - a)
    (b := 1 - b) (by linarith) (by linarith) (by linarith)
  push_cast at this
  simp only [sub_add_cancel] at this
  have e₀ : chartExtend f ((p.y : ℤ), (p.z : ℤ)) = f p :=
    chartExtend_of_yz_eq f (Prod.ext (by simp) (by simp))
  have e₁ : chartExtend f ((p.y : ℤ) - 1, (p.z : ℤ)) = f q :=
    chartExtend_of_yz_eq f (Prod.ext (by simp [hq]; ring) (by simp [hq]))
  have e₂ : chartExtend f ((p.y : ℤ), (p.z : ℤ) - 1) = f r :=
    chartExtend_of_yz_eq f (Prod.ext (by simp [hr]) (by simp [hr]; ring))
  rw [show ((p.y : 𝕜) - a, (p.z : 𝕜) - b) = ((p.y : 𝕜) - 1 + (1 - a), (p.z : 𝕜) - 1 + (1 - b)) by
    ext <;> ring, interpolation, this, e₀, e₁, e₂]
  ring

/-! ### The concavity criterion -/

/-- An affine function majorizing `g` at the lattice points of `Δₙ` majorizes its interpolation on
the triangle. -/
private theorem chartInterp_le_of_forall_le {g : ℤ × ℤ → 𝕜} {c₀ c₁ c₂ : 𝕜}
    (hmaj : ∀ v ∈ chartRegion n, g v ≤ c₀ + c₁ * v.1 + c₂ * v.2) {x : 𝕜 × 𝕜}
    (hx : x ∈ chartTriangle 𝕜 n) : chartInterp g x ≤ c₀ + c₁ * x.1 + c₂ * x.2 := by
  obtain ⟨hx₁, hx₂, hx₃⟩ := hx
  have hi : 0 ≤ ⌊x.1⌋ := Int.floor_nonneg.mpr hx₁
  have hj : 0 ≤ ⌊x.2⌋ := Int.floor_nonneg.mpr hx₂
  have ha := Int.fract_nonneg x.1
  have hb := Int.fract_nonneg x.2
  have ha₁ := Int.fract_lt_one x.1
  have hb₁ := Int.fract_lt_one x.2
  have e₁ := Int.floor_add_fract x.1
  have e₂ := Int.floor_add_fract x.2
  have term : ∀ (c : 𝕜) (v : ℤ × ℤ), 0 ≤ c → (0 < c → v ∈ chartRegion n) →
      c * g v ≤ c * (c₀ + c₁ * v.1 + c₂ * v.2) := by
    intro c v hc hv
    rcases hc.lt_or_eq with hc | rfl
    · exact mul_le_mul_of_nonneg_left (hmaj v (hv hc)) hc.le
    · simp
  have hsum : ((⌊x.1⌋ + ⌊x.2⌋ : ℤ) : 𝕜) + (Int.fract x.1 + Int.fract x.2) ≤ n := by
    push_cast; linarith
  have h₀ : (⌊x.1⌋, ⌊x.2⌋) ∈ chartRegion n :=
    ⟨hi, hj, by exact_mod_cast (show ((⌊x.1⌋ + ⌊x.2⌋ : ℤ) : 𝕜) ≤ n by linarith)⟩
  unfold chartInterp
  split_ifs with hab
  · have hlt : 0 < Int.fract x.1 + Int.fract x.2 → ⌊x.1⌋ + ⌊x.2⌋ + 1 ≤ n := fun h => by
      have : ((⌊x.1⌋ + ⌊x.2⌋ : ℤ) : 𝕜) < n := by linarith
      have : ⌊x.1⌋ + ⌊x.2⌋ < (n : ℤ) := by exact_mod_cast this
      omega
    calc _ ≤ (1 - Int.fract x.1 - Int.fract x.2) * (c₀ + c₁ * ⌊x.1⌋ + c₂ * ⌊x.2⌋) +
          Int.fract x.1 * (c₀ + c₁ * ((⌊x.1⌋ + 1 : ℤ) : 𝕜) + c₂ * ⌊x.2⌋) +
          Int.fract x.2 * (c₀ + c₁ * ⌊x.1⌋ + c₂ * ((⌊x.2⌋ + 1 : ℤ) : 𝕜)) := by
          gcongr ?_ + ?_ + ?_
          · exact term _ _ (by linarith) fun _ => h₀
          · exact term _ _ ha fun h => ⟨by omega, hj, by have := hlt (by linarith); omega⟩
          · exact term _ _ hb fun h => ⟨hi, by omega, by have := hlt (by linarith); omega⟩
      _ = c₀ + c₁ * x.1 + c₂ * x.2 := by
          push_cast
          linear_combination c₁ * e₁ + c₂ * e₂
  · have hlt : ⌊x.1⌋ + ⌊x.2⌋ + 2 ≤ n := by
      have : ((⌊x.1⌋ + ⌊x.2⌋ : ℤ) : 𝕜) + 1 < n := by linarith
      have : ⌊x.1⌋ + ⌊x.2⌋ + 1 < (n : ℤ) := by exact_mod_cast this
      omega
    calc _ ≤ (Int.fract x.1 + Int.fract x.2 - 1) *
          (c₀ + c₁ * ((⌊x.1⌋ + 1 : ℤ) : 𝕜) + c₂ * ((⌊x.2⌋ + 1 : ℤ) : 𝕜)) +
          (1 - Int.fract x.2) * (c₀ + c₁ * ((⌊x.1⌋ + 1 : ℤ) : 𝕜) + c₂ * ⌊x.2⌋) +
          (1 - Int.fract x.1) * (c₀ + c₁ * ⌊x.1⌋ + c₂ * ((⌊x.2⌋ + 1 : ℤ) : 𝕜)) := by
          gcongr ?_ + ?_ + ?_
          · exact term _ _ (by linarith) fun _ => ⟨by omega, by omega, by omega⟩
          · exact term _ _ (by linarith) fun _ => ⟨by omega, hj, by omega⟩
          · exact term _ _ (by linarith) fun _ => ⟨hi, by omega, by omega⟩
      _ = c₀ + c₁ * x.1 + c₂ * x.2 := by
          push_cast
          linear_combination c₁ * e₁ + c₂ * e₂

/-- At every point of the triangle, the interpolation of a rhombus-concave function agrees with an
affine function that majorizes the function at all lattice points of `Δₙ`. -/
private theorem ChartConcave.exists_affine {g : ℤ × ℤ → 𝕜} (hg : ChartConcave n g) {q : 𝕜 × 𝕜}
    (hq : q ∈ chartTriangle 𝕜 n) :
    ∃ c₀ c₁ c₂ : 𝕜, chartInterp g q = c₀ + c₁ * q.1 + c₂ * q.2 ∧
      ∀ v ∈ chartRegion n, g v ≤ c₀ + c₁ * v.1 + c₂ * v.2 := by
  obtain ⟨hq₁, hq₂, hq₃⟩ := hq
  have hi : 0 ≤ ⌊q.1⌋ := Int.floor_nonneg.mpr hq₁
  have hj : 0 ≤ ⌊q.2⌋ := Int.floor_nonneg.mpr hq₂
  have ha := Int.fract_nonneg q.1
  have hb := Int.fract_nonneg q.2
  have e₁ := Int.floor_add_fract q.1
  have e₂ := Int.floor_add_fract q.2
  have hsum : ((⌊q.1⌋ + ⌊q.2⌋ : ℤ) : 𝕜) + (Int.fract q.1 + Int.fract q.2) ≤ n := by
    push_cast; linarith
  have hle : ⌊q.1⌋ + ⌊q.2⌋ ≤ n := by
    exact_mod_cast (show ((⌊q.1⌋ + ⌊q.2⌋ : ℤ) : 𝕜) ≤ n by linarith)
  unfold chartInterp
  split_ifs with hab
  · by_cases hn : ⌊q.1⌋ + ⌊q.2⌋ + 1 ≤ n
    · -- the upward triangle at `(⌊y⌋, ⌊z⌋)`
      refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 0) (p := (⌊q.1⌋, ⌊q.2⌋))
        (α := g (⌊q.1⌋ + 1, ⌊q.2⌋) - g (⌊q.1⌋, ⌊q.2⌋))
        (β := g (⌊q.1⌋, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋)) ⟨hi, hj, by omega⟩
        (by simp [chartStep_def, mem_chartRegion]; omega)
        (by simp [chartStep_def, mem_chartRegion]; omega) (by simp [chartStep_def])
        (by simp [chartStep_def])⟩
      linear_combination (g (⌊q.1⌋ + 1, ⌊q.2⌋) - g (⌊q.1⌋, ⌊q.2⌋)) * e₁ +
        (g (⌊q.1⌋, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋)) * e₂
    · -- `q` is a lattice point on the side `y + z = n`
      have hn' : ((⌊q.1⌋ + ⌊q.2⌋ : ℤ) : 𝕜) ≥ n := by exact_mod_cast (show (n : ℤ) ≤ _ by omega)
      have hfa : Int.fract q.1 = 0 := by linarith
      have hfb : Int.fract q.2 = 0 := by linarith
      obtain ⟨c₀, c₁, c₂, hc, hmaj⟩ := hg.exists_affine_of_add_eq hi hj (by omega)
      refine ⟨c₀, c₁, c₂, ?_, hmaj⟩
      rw [hfa] at e₁
      rw [hfb] at e₂
      simp only [hfa, hfb, sub_zero, one_mul, zero_mul, add_zero, hc]
      linear_combination c₁ * e₁ + c₂ * e₂
  · -- the downward triangle with top corner `(⌊y⌋ + 1, ⌊z⌋ + 1)`
    have hlt : ⌊q.1⌋ + ⌊q.2⌋ + 2 ≤ n := by
      have : ((⌊q.1⌋ + ⌊q.2⌋ : ℤ) : 𝕜) + 1 < n := by linarith
      have : ⌊q.1⌋ + ⌊q.2⌋ + 1 < (n : ℤ) := by exact_mod_cast this
      omega
    refine ⟨_, _, _, ?_, hg.le_affine_of_corner (k := 3) (p := (⌊q.1⌋ + 1, ⌊q.2⌋ + 1))
      (α := g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋ + 1))
      (β := g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋ + 1, ⌊q.2⌋)) ⟨by omega, by omega, by omega⟩
      (by simp [chartStep_def, mem_chartRegion]; omega)
      (by simp [chartStep_def, mem_chartRegion]; omega)
      (by simp [chartStep_def, sub_eq_add_neg]) (by simp [chartStep_def, sub_eq_add_neg])⟩
    push_cast
    linear_combination (g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋, ⌊q.2⌋ + 1)) * e₁ +
      (g (⌊q.1⌋ + 1, ⌊q.2⌋ + 1) - g (⌊q.1⌋ + 1, ⌊q.2⌋)) * e₂

/-- The interpolation at the midpoint of a unit lattice edge is the average of the two ends. -/
private theorem chartInterp_midpoint (g : ℤ × ℤ → 𝕜) {x x' : ℤ × ℤ}
    (h : ∃ m, x' = x + chartStep m) :
    chartInterp g (((x.1 : 𝕜) + x'.1) / 2, ((x.2 : 𝕜) + x'.2) / 2) = (g x + g x') / 2 := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨i, j⟩ := x
  obtain ⟨i', j'⟩ := x'
  have h₁ : i' = i + (chartStep m).1 := congrArg Prod.fst hm
  have h₂ : j' = j + (chartStep m).2 := congrArg Prod.snd hm
  dsimp only
  fin_cases m <;>
    simp only [chartStep_def, Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, add_zero] at h₁ h₂ <;>
    rw [h₁, h₂]
  · rw [show (((i : 𝕜) + ((i + 1 : ℤ) : 𝕜)) / 2, ((j : 𝕜) + (j : 𝕜)) / 2) =
        ((i : 𝕜) + 1 / 2, (j : 𝕜) + 0) by ext <;> push_cast <;> ring,
      chartInterp_up g i j (by norm_num) le_rfl (by norm_num)]
    ring
  · rw [show (((i : 𝕜) + (i : 𝕜)) / 2, ((j : 𝕜) + ((j + 1 : ℤ) : 𝕜)) / 2) =
        ((i : 𝕜) + 0, (j : 𝕜) + 1 / 2) by ext <;> push_cast <;> ring,
      chartInterp_up g i j le_rfl (by norm_num) (by norm_num)]
    ring
  · rw [show (((i : 𝕜) + ((i + -1 : ℤ) : 𝕜)) / 2, ((j : 𝕜) + ((j + 1 : ℤ) : 𝕜)) / 2) =
        (((i + -1 : ℤ) : 𝕜) + 1 / 2, (j : 𝕜) + 1 / 2) by ext <;> push_cast <;> ring,
      chartInterp_up g (i + -1) j (by norm_num) (by norm_num) (by norm_num), neg_add_cancel_right]
    ring
  · rw [show (((i : 𝕜) + ((i + -1 : ℤ) : 𝕜)) / 2, ((j : 𝕜) + (j : 𝕜)) / 2) =
        (((i + -1 : ℤ) : 𝕜) + 1 / 2, (j : 𝕜) + 0) by ext <;> push_cast <;> ring,
      chartInterp_up g (i + -1) j (by norm_num) le_rfl (by norm_num), neg_add_cancel_right]
    ring
  · rw [show (((i : 𝕜) + (i : 𝕜)) / 2, ((j : 𝕜) + ((j + -1 : ℤ) : 𝕜)) / 2) =
        ((i : 𝕜) + 0, ((j + -1 : ℤ) : 𝕜) + 1 / 2) by ext <;> push_cast <;> ring,
      chartInterp_up g i (j + -1) le_rfl (by norm_num) (by norm_num), neg_add_cancel_right]
    ring
  · rw [show (((i : 𝕜) + ((i + 1 : ℤ) : 𝕜)) / 2, ((j : 𝕜) + ((j + -1 : ℤ) : 𝕜)) / 2) =
        ((i : 𝕜) + 1 / 2, ((j + -1 : ℤ) : 𝕜) + 1 / 2) by ext <;> push_cast <;> ring,
      chartInterp_up g i (j + -1) (by norm_num) (by norm_num) (by norm_num), neg_add_cancel_right]
    ring

/-- **The concavity criterion.** The interpolation of `f : Vertex n → 𝕜` is concave on the
triangle exactly when `f` satisfies every unit-rhombus inequality. -/
theorem concaveOn_interpolation_iff (f : Vertex n → 𝕜) :
    ConcaveOn 𝕜 (chartTriangle 𝕜 n) (interpolation f) ↔ IsRhombusConcave f := by
  constructor
  · intro hF
    rw [isRhombusConcave_def]
    intro a b c d h
    -- the common midpoint of the two diagonals lies on the unit edge from `a` to `c`
    have hmid := hF.2 (natCast_mem_chartTriangle b) (natCast_mem_chartTriangle d)
      (by norm_num : (0 : 𝕜) ≤ 1 / 2) (by norm_num : (0 : 𝕜) ≤ 1 / 2)
      (by norm_num : (1 / 2 : 𝕜) + 1 / 2 = 1)
    rw [interpolation_vertex, interpolation_vertex] at hmid
    have hpt : (1 / 2 : 𝕜) • ((b.y : 𝕜), (b.z : 𝕜)) + (1 / 2 : 𝕜) • ((d.y : 𝕜), (d.z : 𝕜)) =
        ((((a.yz.1 : ℤ) : 𝕜) + (c.yz.1 : ℤ)) / 2, (((a.yz.2 : ℤ) : 𝕜) + (c.yz.2 : ℤ)) / 2) := by
      have hy : (b.y : 𝕜) + d.y = a.y + c.y := by exact_mod_cast h.midpoint_y.symm
      have hz : (b.z : 𝕜) + d.z = a.z + c.z := by exact_mod_cast h.midpoint_z.symm
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul,
        Vertex.yz_fst, Vertex.yz_snd, Int.cast_natCast] <;> linarith
    rw [hpt, interpolation, chartInterp_midpoint _ (Vertex.sqDist_eq_two_iff.mp h.short),
      chartExtend_yz, chartExtend_yz] at hmid
    simp only [smul_eq_mul] at hmid
    linarith
  · intro hf
    have hg := chartConcave_chartExtend hf
    refine ⟨convex_chartTriangle, fun x hx y hy a b ha hb hab => ?_⟩
    obtain ⟨c₀, c₁, c₂, hz, hmaj⟩ := hg.exists_affine (convex_chartTriangle hx hy ha hb hab)
    have hx' := chartInterp_le_of_forall_le hmaj hx
    have hy' := chartInterp_le_of_forall_le hmaj hy
    simp only [interpolation, smul_eq_mul, hz, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd]
    have := mul_le_mul_of_nonneg_left hx' ha
    have := mul_le_mul_of_nonneg_left hy' hb
    linear_combination this + ‹a * chartInterp (chartExtend f) x ≤ _› + c₀ * hab

/-- The interpolation of a hive is concave on the triangle. -/
theorem concaveOn_interpolation (h : Hive n 𝕜) :
    ConcaveOn 𝕜 (chartTriangle 𝕜 n) (interpolation h) :=
  (concaveOn_interpolation_iff h).2 h.isRhombusConcave

end Interpolation

end TauCeti.Hive
