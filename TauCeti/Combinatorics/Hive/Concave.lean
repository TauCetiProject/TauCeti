/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Discrete concavity of rhombus-concave lattice functions

A function `f : Vertex n → R` with values in an ordered abelian group that satisfies all
unit-rhombus inequalities behaves like a concave function on the lattice points of `Δₙ`. Summing
rhombus inequalities over a lattice parallelogram gives the parallelogram inequality, and an
affine function that agrees with `f` on one unit triangle majorizes `f` on all of `Δₙ`.

## Main definitions

* `TauCeti.Hive.yzTriangle 𝕜 n`: the triangle `0 ≤ y, 0 ≤ z, y + z ≤ n` of the `(y, z)` chart,
  in `𝕜 × 𝕜`.

## Main results

* `TauCeti.Hive.IsRhombusConcave.parallelogram_le_yzStep`: the parallelogram inequality for every
  lattice parallelogram spanned by two consecutive unit steps.
* `TauCeti.Hive.IsRhombusConcave.parallelogram_le`, `TauCeti.Hive.parallelogram_le`: its
  coordinate-aligned case `f(y₀, z₀) + f(y₁, z₁) ≤ f(y₁, z₀) + f(y₀, z₁)` on `[y₀, y₁] × [z₀, z₁]`.
* `TauCeti.Hive.IsRhombusConcave.le_barycentricLinear`: discrete supporting planes.

## Implementation notes

The arguments work in the `(y, z)` chart, with `f` extended by zero to all of `ℤ × ℤ`. Around a
corner of a unit triangle, the plane splits into the six sectors spanned by consecutive unit steps
`yzStep k`, `yzStep (k + 1)`. In a sector, summing rhombus inequalities over a lattice
parallelogram and along a lattice line bounds the function by its slopes at the corner, and the
rhombi meeting at the corner bound those slopes by the slopes of the affine function.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, §2.
-/

public section

namespace TauCeti.Hive

variable {n : ℕ}

/-! ### The triangle of the `(y, z)` chart and the extension by zero -/

section Triangle

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]

variable (𝕜) in
/-- The triangle `0 ≤ y, 0 ≤ z, y + z ≤ n` of the `(y, z)` chart of `Δₙ`, in `𝕜 × 𝕜`. -/
def yzTriangle (n : ℕ) : Set (𝕜 × 𝕜) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ n}

@[simp] theorem mem_yzTriangle {q : 𝕜 × 𝕜} :
    q ∈ yzTriangle 𝕜 n ↔ 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ n := Iff.rfl

/-- Every vertex of `Δₙ` lies in the triangle, at its `(y, z)` chart coordinates. -/
theorem natCast_mem_yzTriangle [IsOrderedRing 𝕜] (p : Vertex n) :
    ((p.y : 𝕜), (p.z : 𝕜)) ∈ yzTriangle 𝕜 n := by
  rw [mem_yzTriangle]
  dsimp only
  refine ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, ?_⟩
  have := Nat.mono_cast (α := 𝕜) (show p.y + p.z ≤ n by have := p.sum_eq; omega)
  rwa [Nat.cast_add] at this

end Triangle

/-- `natCast_mem_yzTriangle` over `ℤ`, stated for the chart coordinates `Vertex.yz`. -/
private theorem yz_mem_yzTriangle (p : Vertex n) : p.yz ∈ yzTriangle ℤ n :=
  (Prod.ext p.yz_fst p.yz_snd : p.yz = ((p.y : ℤ), (p.z : ℤ))) ▸ natCast_mem_yzTriangle p

/-- The vertex with given `(y, z)` chart coordinates. -/
private def yzVertex (p : ℤ × ℤ) (hp : p ∈ yzTriangle ℤ n) : Vertex n :=
  Vertex.ofYZ n p.1.toNat p.2.toNat (by obtain ⟨_, _, _⟩ := hp; omega)

private theorem yzVertex_yz (p : Vertex n) : yzVertex p.yz (yz_mem_yzTriangle p) = p := by
  ext <;> simp [yzVertex]

/-- Extend a lattice function by zero to all integer points of the `(y, z)` chart. -/
private def yzExtend {R : Type*} [Zero R] (f : Vertex n → R) (p : ℤ × ℤ) : R :=
  if hp : 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ n then f (yzVertex p hp) else 0

private theorem yzExtend_of_mem {R : Type*} [Zero R] (f : Vertex n → R) {p : ℤ × ℤ}
    (hp : p ∈ yzTriangle ℤ n) : yzExtend f p = f (yzVertex p hp) := dite_eq_left hp

private theorem yzExtend_yz {R : Type*} [Zero R] (f : Vertex n → R) (p : Vertex n) :
    yzExtend f p.yz = f p := by
  rw [yzExtend_of_mem f (yz_mem_yzTriangle p), yzVertex_yz]

private theorem yzExtend_of_yz_eq {R : Type*} [Zero R] (f : Vertex n → R) {x : ℤ × ℤ}
    {p : Vertex n} (h : p.yz = x) : yzExtend f x = f p := by
  rw [← h, yzExtend_yz]

/-! ### Index arithmetic in `Fin 6` -/

private theorem fin6_add_one_add_one (k : Fin 6) : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
private theorem fin6_add_one_add_five (k : Fin 6) : k + 1 + 5 = k := by fin_cases k <;> rfl
private theorem fin6_add_four_add_five (k : Fin 6) : k + 4 + 5 = k + 3 := by fin_cases k <;> rfl
private theorem fin6_add_one_add_one_add_one (k : Fin 6) : k + 1 + 1 + 1 = k + 3 := by
  fin_cases k <;> rfl
private theorem fin6_add_four_add_one_add_one (k : Fin 6) : k + 4 + 1 + 1 = k := by
  fin_cases k <;> rfl

/-- The lattice parallelogram spanned by two consecutive unit steps between two points of the
triangle stays in the triangle: each barycentric coordinate is monotone along both steps. -/
private theorem mem_yzTriangle_of_parallelogram {k : Fin 6} {p : ℤ × ℤ} {s t i j : ℕ}
    (hp : p ∈ yzTriangle ℤ n) (hv : p + s • yzStep k + t • yzStep (k + 1) ∈ yzTriangle ℤ n)
    (hi : i ≤ s) (hj : j ≤ t) : p + i • yzStep k + j • yzStep (k + 1) ∈ yzTriangle ℤ n := by
  simp only [mem_yzTriangle] at *
  fin_cases k <;> simp [yzStep_def] at * <;> omega

/-! ### Rhombus concavity in the chart -/

section Linear

variable {R : Type*} [AddCommGroup R]

/-- The additive map `d ↦ d.1 • α + d.2 • β` on chart displacements. -/
private def yzLinear (α β : R) : ℤ × ℤ →+ R := (zmultiplesHom R α).coprod (zmultiplesHom R β)

private theorem yzLinear_apply (α β : R) (d : ℤ × ℤ) :
    yzLinear α β d = d.1 • α + d.2 • β := by
  simp [yzLinear]

/-- The difference of a barycentric-affine function at two vertices, in chart coordinates. -/
private theorem barycentricLinear_sub_barycentricLinear (c₀ α β γ : R) (p q : Vertex n) :
    barycentricLinear c₀ α β γ q - barycentricLinear c₀ α β γ p =
      yzLinear (β - α) (γ - α) (q.yz - p.yz) := by
  have hx : (q.x : ℤ) = p.x - ((q.y : ℤ) - p.y) - ((q.z : ℤ) - p.z) := by
    have := p.sum_eq
    have := q.sum_eq
    omega
  simp only [barycentricLinear_apply, yzLinear_apply, Prod.fst_sub, Prod.snd_sub, Vertex.yz_fst,
    Vertex.yz_snd, ← natCast_zsmul, hx]
  module

end Linear

section Ordered

variable {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]

/-- The unit-rhombus inequalities in the `(y, z)` chart: on the rhombus with acute corners `p` and
`p + yzStep k + yzStep (k + 1)`, the acute sum is at most the obtuse sum. -/
private def YZConcave (n : ℕ) (g : ℤ × ℤ → R) : Prop :=
  ∀ (k : Fin 6) (p : ℤ × ℤ), p ∈ yzTriangle ℤ n → p + yzStep k ∈ yzTriangle ℤ n →
    p + yzStep (k + 1) ∈ yzTriangle ℤ n → p + yzStep k + yzStep (k + 1) ∈ yzTriangle ℤ n →
    g p + g (p + yzStep k + yzStep (k + 1)) ≤ g (p + yzStep k) + g (p + yzStep (k + 1))

/-- The barycentric vector of a chart displacement. -/
private def baryStep (d : ℤ × ℤ) : Fin 3 → ℤ := ![-d.1 - d.2, d.1, d.2]

private theorem hasStep_yzVertex {p q : ℤ × ℤ} (hp : p ∈ yzTriangle ℤ n)
    (hq : q ∈ yzTriangle ℤ n) :
    HasStep (yzVertex p hp) (yzVertex q hq) (baryStep (q - p)) := by
  obtain ⟨_, _, _⟩ := hp
  obtain ⟨_, _, _⟩ := hq
  rw [hasStep_iff]
  intro i
  fin_cases i <;> simp [yzVertex, baryStep] <;> omega

private theorem isUnitStep_baryStep (k : Fin 6) : IsUnitStep (baryStep (yzStep k)) := by
  fin_cases k <;> simp [isUnitStep_iff, baryStep, yzStep_def, Fin.sum_univ_three]

private theorem sum_baryStep_mul (k : Fin 6) :
    (∑ i, baryStep (yzStep k) i * baryStep (yzStep (k + 1)) i) = 1 := by
  fin_cases k <;> simp [baryStep, yzStep_def, Fin.sum_univ_three]

omit [IsOrderedAddMonoid R] in
private theorem yzConcave_yzExtend {f : Vertex n → R} (hf : IsRhombusConcave f) :
    YZConcave n (yzExtend f) := by
  intro k p h₀ h₁ h₂ h₃
  rw [yzExtend_of_mem f h₀, yzExtend_of_mem f h₁, yzExtend_of_mem f h₂,
    yzExtend_of_mem f h₃]
  refine (isRhombusConcave_def f).mp hf ((isRhombus_of_hasStep_iff (isUnitStep_baryStep k)
    (isUnitStep_baryStep (k + 1)) ?_ ?_ ?_).mpr (sum_baryStep_mul k))
  · simpa using hasStep_yzVertex h₀ h₁
  · simpa using hasStep_yzVertex h₀ h₂
  · convert hasStep_yzVertex h₀ h₃ using 1
    funext i
    fin_cases i <;> simp [baryStep] <;> ring

variable {g : ℤ × ℤ → R}

omit [IsOrderedAddMonoid R] in
/-- The rhombus whose short diagonal runs from `p` to `p + yzStep m`: its acute corners are
`p + yzStep (m + 5)` and `p + yzStep (m + 1)`. -/
private theorem YZConcave.corner (hg : YZConcave n g) (m : Fin 6) {p : ℤ × ℤ}
    (hp : p ∈ yzTriangle ℤ n) (hm : p + yzStep m ∈ yzTriangle ℤ n)
    (hm₁ : p + yzStep (m + 1) ∈ yzTriangle ℤ n) (hm₅ : p + yzStep (m + 5) ∈ yzTriangle ℤ n) :
    g (p + yzStep (m + 5)) + g (p + yzStep (m + 1)) ≤ g (p + yzStep m) + g p := by
  have hm₂ := fin6_add_one_add_one m
  have e₅ : yzStep (m + 5) = yzStep m - yzStep (m + 1) := yzStep_add_five m
  have e₂ : yzStep (m + 2) = yzStep (m + 1) - yzStep m := yzStep_add_two m
  have e₁ : p + yzStep (m + 5) + yzStep (m + 1) = p + yzStep m := by rw [e₅]; abel
  have e₀ : p + yzStep (m + 5) + yzStep (m + 2) = p := by rw [e₅, e₂]; abel
  have e₃ : p + yzStep (m + 5) + yzStep (m + 1) + yzStep (m + 2) =
      p + yzStep (m + 1) := by rw [e₅, e₂]; abel
  have M := hg (m + 1) (p + yzStep (m + 5)) hm₅ (by rwa [e₁]) (by rwa [hm₂, e₀])
    (by rwa [hm₂, e₃])
  rwa [hm₂, e₃, e₁, e₀] at M

/-- Line concavity from the two corner rhombi at `q` on the side of `yzStep j` and
`yzStep (j + 1)`, where `j` is `k + 1` or `k + 4`. -/
private theorem YZConcave.line_of_side (hg : YZConcave n g) {k j : Fin 6} {q : ℤ × ℤ}
    (hj : j = k + 1 ∨ j = k + 4) (h₁ : q - yzStep k ∈ yzTriangle ℤ n) (h₂ : q ∈ yzTriangle ℤ n)
    (h₃ : q + yzStep k ∈ yzTriangle ℤ n) (h₄ : q + yzStep j ∈ yzTriangle ℤ n)
    (h₅ : q + yzStep (j + 1) ∈ yzTriangle ℤ n) :
    g (q - yzStep k) + g (q + yzStep k) ≤ g q + g q := by
  have hneg : q - yzStep k = q + yzStep (k + 3) := by
    rw [yzStep_add_three, sub_eq_add_neg]
  rw [hneg] at h₁ ⊢
  -- the two corner rhombi have short diagonals along `yzStep j` and `yzStep (j + 1)`
  have hj₁ := fin6_add_one_add_five j
  have M₁ := hg.corner j h₂ h₄ h₅ (by
    rcases hj with rfl | rfl
    · rwa [fin6_add_one_add_five]
    · rwa [fin6_add_four_add_five])
  have M₂ := hg.corner (j + 1) h₂ h₅ (by
    rcases hj with rfl | rfl
    · rwa [fin6_add_one_add_one_add_one]
    · rwa [fin6_add_four_add_one_add_one]) (by rwa [hj₁])
  rw [hj₁] at M₂
  have h := add_nonneg (sub_nonneg.mpr M₁) (sub_nonneg.mpr M₂)
  rw [← sub_nonneg]
  rcases hj with rfl | rfl
  · rw [fin6_add_one_add_five, fin6_add_one_add_one_add_one] at h
    convert h using 1
    abel
  · rw [fin6_add_four_add_five, fin6_add_four_add_one_add_one] at h
    convert h using 1
    abel

/-- Rhombus concavity implies concavity along every lattice line. -/
private theorem YZConcave.line (hg : YZConcave n g) {k : Fin 6} {q : ℤ × ℤ}
    (h₁ : q - yzStep k ∈ yzTriangle ℤ n) (h₂ : q ∈ yzTriangle ℤ n)
    (h₃ : q + yzStep k ∈ yzTriangle ℤ n) :
    g (q - yzStep k) + g (q + yzStep k) ≤ g q + g q := by
  -- the corner rhombi lie on the side of `yzStep (k + 1)` for even `k`, and on the side of
  -- `yzStep (k + 4)` for odd `k`
  fin_cases k <;>
    first
    | exact hg.line_of_side (Or.inl rfl) h₁ h₂ h₃
        (by simp [mem_yzTriangle, yzStep_def] at h₁ h₂ h₃ ⊢; omega)
        (by simp [mem_yzTriangle, yzStep_def] at h₁ h₂ h₃ ⊢; omega)
    | exact hg.line_of_side (Or.inr rfl) h₁ h₂ h₃
        (by simp [mem_yzTriangle, yzStep_def] at h₁ h₂ h₃ ⊢; omega)
        (by simp [mem_yzTriangle, yzStep_def] at h₁ h₂ h₃ ⊢; omega)

/-- Along a lattice line inside the triangle, the function lies below its first secant. -/
private theorem YZConcave.le_line (hg : YZConcave n g) {k : Fin 6} {p : ℤ × ℤ} {s : ℕ}
    (hmem : ∀ i ≤ s, p + i • yzStep k ∈ yzTriangle ℤ n) :
    g (p + s • yzStep k) ≤ g p + s • (g (p + yzStep k) - g p) := by
  set u := yzStep k
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
private theorem YZConcave.parallelogram (hg : YZConcave n g) {k : Fin 6} {p : ℤ × ℤ}
    {s t : ℕ}
    (hmem : ∀ i ≤ s, ∀ j ≤ t, p + i • yzStep k + j • yzStep (k + 1) ∈ yzTriangle ℤ n) :
    g p + g (p + s • yzStep k + t • yzStep (k + 1)) ≤
      g (p + s • yzStep k) + g (p + t • yzStep (k + 1)) := by
  set u := yzStep k
  set w := yzStep (k + 1)
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
private theorem YZConcave.le_sector (hg : YZConcave n g) {k : Fin 6} {p : ℤ × ℤ} {s t : ℕ}
    (hp : p ∈ yzTriangle ℤ n) (hv : p + s • yzStep k + t • yzStep (k + 1) ∈ yzTriangle ℤ n) :
    g (p + s • yzStep k + t • yzStep (k + 1)) ≤
      g p + s • (g (p + yzStep k) - g p) + t • (g (p + yzStep (k + 1)) - g p) := by
  have hmem := fun i (hi : i ≤ s) j (hj : j ≤ t) => mem_yzTriangle_of_parallelogram hp hv hi hj
  have hP := hg.parallelogram hmem
  have hs := hg.le_line (k := k) (s := s) fun i hi => by simpa using hmem i hi 0 (Nat.zero_le _)
  have ht := hg.le_line (k := k + 1) (s := t) fun j hj => by simpa using hmem 0 (Nat.zero_le _) j hj
  calc g (p + s • yzStep k + t • yzStep (k + 1))
      ≤ g (p + s • yzStep k) + g (p + t • yzStep (k + 1)) - g p :=
        le_sub_iff_add_le'.mpr hP
    _ ≤ (g p + s • (g (p + yzStep k) - g p)) +
          (g p + t • (g (p + yzStep (k + 1)) - g p)) - g p := by gcongr
    _ = g p + s • (g (p + yzStep k) - g p) + t • (g (p + yzStep (k + 1)) - g p) := by abel

/-- At a corner `p` of a unit triangle on which `g` agrees with an affine function, the slope of
`g` along each unit step leaving `p` is at most the slope of the affine function. -/
private theorem YZConcave.slope_le (hg : YZConcave n g) {k : Fin 6} {p : ℤ × ℤ}
    (hp : p ∈ yzTriangle ℤ n) (hk : p + yzStep k ∈ yzTriangle ℤ n)
    (hk₁ : p + yzStep (k + 1) ∈ yzTriangle ℤ n) {α β : R}
    (h₁ : yzLinear α β (yzStep k) = g (p + yzStep k) - g p)
    (h₂ : yzLinear α β (yzStep (k + 1)) = g (p + yzStep (k + 1)) - g p) (r : Fin 6)
    (hr : p + yzStep (k + r) ∈ yzTriangle ℤ n) :
    g (p + yzStep (k + r)) - g p ≤ yzLinear α β (yzStep (k + r)) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :=
    (by decide : ∀ r : Fin 6, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) r
  · rw [add_zero, h₁]
  · rw [h₂]
  · -- the rhombus with obtuse corners `p`, `p + yzStep (k + 1)`
    have M := hg.corner (k + 1) hp hk₁ (by rwa [fin6_add_one_add_one])
      (by rwa [fin6_add_one_add_five])
    rw [fin6_add_one_add_one, fin6_add_one_add_five] at M
    rw [show yzLinear α β (yzStep (k + 2)) =
        yzLinear α β (yzStep (k + 1)) - yzLinear α β (yzStep k) by
      rw [yzStep_add_two, map_sub], h₁, h₂,
      show g (p + yzStep (k + 1)) - g p - (g (p + yzStep k) - g p) =
        g (p + yzStep (k + 1)) - g (p + yzStep k) by abel, sub_le_sub_iff]
    simpa [add_comm] using M
  · -- concavity along the line of `yzStep k`
    have e : p + yzStep (k + 3) = p - yzStep k := by
      rw [yzStep_add_three, sub_eq_add_neg]
    rw [e] at hr ⊢
    have hL := hg.line hr hp hk
    rw [yzStep_add_three, map_neg, h₁, neg_sub, sub_le_sub_iff]
    exact hL
  · -- concavity along the line of `yzStep (k + 1)`
    have e : p + yzStep (k + 4) = p - yzStep (k + 1) := by
      rw [yzStep_add_four, sub_eq_add_neg]
    rw [e] at hr ⊢
    have hL := hg.line hr hp hk₁
    rw [yzStep_add_four, map_neg, h₂, neg_sub, sub_le_sub_iff]
    exact hL
  · -- the rhombus with obtuse corners `p`, `p + yzStep k`
    have M := hg.corner k hp hk hk₁ hr
    rw [show yzLinear α β (yzStep (k + 5)) =
        yzLinear α β (yzStep k) - yzLinear α β (yzStep (k + 1)) by
      rw [yzStep_add_five, map_sub], h₁, h₂,
      show g (p + yzStep k) - g p - (g (p + yzStep (k + 1)) - g p) =
        g (p + yzStep k) - g (p + yzStep (k + 1)) by abel, sub_le_sub_iff]
    simpa [add_comm] using M

/-- Discrete supporting planes in the chart: an affine function agreeing with `g` on a unit
triangle of `yzTriangle ℤ n` majorizes `g` at all of its lattice points. -/
private theorem YZConcave.le_affine (hg : YZConcave n g) {k : Fin 6} {p : ℤ × ℤ}
    (hp : p ∈ yzTriangle ℤ n) (hk : p + yzStep k ∈ yzTriangle ℤ n)
    (hk₁ : p + yzStep (k + 1) ∈ yzTriangle ℤ n) {α β : R}
    (h₁ : yzLinear α β (yzStep k) = g (p + yzStep k) - g p)
    (h₂ : yzLinear α β (yzStep (k + 1)) = g (p + yzStep (k + 1)) - g p) {v : ℤ × ℤ}
    (hv : v ∈ yzTriangle ℤ n) : g v ≤ g p + yzLinear α β (v - p) := by
  obtain ⟨m, s, t, hd⟩ := exists_yzStep_sector (v - p)
  obtain ⟨r, rfl⟩ : ∃ r, m = k + r := ⟨m - k, by abel⟩
  have hv' : p + s • yzStep (k + r) + t • yzStep (k + r + 1) = v := by
    rw [add_assoc, ← hd]; abel
  have hS := hg.le_sector (k := k + r) (s := s) (t := t) hp (by rwa [hv'])
  rw [hv'] at hS
  have hslope : ∀ r' : Fin 6, ∀ c : ℕ, (0 < c → p + yzStep (k + r') ∈ yzTriangle ℤ n) →
      c • (g (p + yzStep (k + r')) - g p) ≤ c • yzLinear α β (yzStep (k + r')) := by
    intro r' c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc'
    · simp
    · exact nsmul_le_nsmul_right (hg.slope_le hp hk hk₁ h₁ h₂ r' (hc hc')) c
  have hmem : ∀ i ≤ s, ∀ j ≤ t, p + i • yzStep (k + r) + j • yzStep (k + r + 1) ∈
      yzTriangle ℤ n := fun i hi j hj =>
    mem_yzTriangle_of_parallelogram hp (by rwa [hv']) hi hj
  have hs := hslope r s fun hs => by simpa using hmem 1 hs 0 (Nat.zero_le _)
  have ht := hslope (r + 1) t fun ht => by
    simpa [add_assoc] using hmem 0 (Nat.zero_le _) 1 ht
  rw [← add_assoc] at ht
  calc g v ≤ g p + s • (g (p + yzStep (k + r)) - g p) +
        t • (g (p + yzStep (k + r + 1)) - g p) := hS
    _ ≤ g p + s • yzLinear α β (yzStep (k + r)) +
        t • yzLinear α β (yzStep (k + r + 1)) := by gcongr
    _ = g p + yzLinear α β (v - p) := by
      rw [hd, _root_.map_add, _root_.map_nsmul, _root_.map_nsmul, add_assoc]

end Ordered

/-- **Discrete supporting planes.** If a rhombus-concave function `f` agrees with a
barycentric-affine function `L` at the three corners `p`, `q`, `r` of a unit triangle, then
`f ≤ L` on all of `Δₙ`. Every unit triangle has this form: its corners, read from any one of them,
differ in the `(y, z)` chart by two consecutive unit steps. -/
theorem IsRhombusConcave.le_barycentricLinear {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] {f : Vertex n → R} (hf : IsRhombusConcave f) {k : Fin 6}
    {p q r : Vertex n} (hq : q.yz = p.yz + yzStep k) (hr : r.yz = p.yz + yzStep (k + 1))
    {c₀ α β γ : R} (hfp : f p = barycentricLinear c₀ α β γ p)
    (hfq : f q = barycentricLinear c₀ α β γ q) (hfr : f r = barycentricLinear c₀ α β γ r)
    (v : Vertex n) : f v ≤ barycentricLinear c₀ α β γ v := by
  have hg := yzConcave_yzExtend hf
  have hle := hg.le_affine (k := k) (p := p.yz) (α := β - α) (β := γ - α) (yz_mem_yzTriangle p)
    (by rw [← hq]; exact yz_mem_yzTriangle q) (by rw [← hr]; exact yz_mem_yzTriangle r)
    (by rw [← hq, yzExtend_yz, yzExtend_yz, hfp, hfq,
      barycentricLinear_sub_barycentricLinear, hq, add_sub_cancel_left])
    (by rw [← hr, yzExtend_yz, yzExtend_yz, hfp, hfr,
      barycentricLinear_sub_barycentricLinear, hr, add_sub_cancel_left])
    (yz_mem_yzTriangle v)
  rw [yzExtend_yz, yzExtend_yz, ← barycentricLinear_sub_barycentricLinear c₀ α β γ p v, hfp,
    add_sub_cancel] at hle
  exact hle

/-- **Parallelogram inequality.** Summing the unit-rhombus inequalities over the lattice
parallelogram with corner `p` spanned by `s` steps `yzStep k` and `t` steps `yzStep (k + 1)` bounds
the sum of `f` at the two acute corners `p`, `v` by its sum at the two obtuse corners `q`, `r`. -/
theorem IsRhombusConcave.parallelogram_le_yzStep {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] {f : Vertex n → R} (hf : IsRhombusConcave f) {k : Fin 6} {s t : ℕ}
    {p q r v : Vertex n} (hq : q.yz = p.yz + s • yzStep k) (hr : r.yz = p.yz + t • yzStep (k + 1))
    (hv : v.yz = p.yz + s • yzStep k + t • yzStep (k + 1)) : f p + f v ≤ f q + f r := by
  have h := (yzConcave_yzExtend hf).parallelogram (k := k) (p := p.yz) (s := s) (t := t)
    fun i hi j hj => mem_yzTriangle_of_parallelogram (yz_mem_yzTriangle p)
      (by rw [← hv]; exact yz_mem_yzTriangle v) hi hj
  rw [← hv, ← hq, ← hr] at h
  simpa only [yzExtend_yz] using h

section Parallelogram

variable {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]

/-- **Parallelogram inequality** for rhombus-concave functions on `[y₀, y₁] × [z₀, z₁]`. -/
theorem IsRhombusConcave.parallelogram_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    {y₀ y₁ z₀ z₁ : ℕ} (hy : y₀ ≤ y₁) (hz : z₀ ≤ z₁) (hsum : y₁ + z₁ ≤ n) :
    f (Vertex.ofYZ n y₀ z₀ (by omega)) + f (Vertex.ofYZ n y₁ z₁ hsum) ≤
      f (Vertex.ofYZ n y₁ z₀ (by omega)) + f (Vertex.ofYZ n y₀ z₁ (by omega)) := by
  refine hf.parallelogram_le_yzStep (k := 0) (s := y₁ - y₀) (t := z₁ - z₀) ?_ ?_ ?_ <;>
    ext <;> simp [yzStep_def] <;> omega

/-- Parallelogram inequality specialized to a normalized `Hive`. -/
theorem parallelogram_le (h : Hive n R) {y₀ y₁ z₀ z₁ : ℕ} (hy : y₀ ≤ y₁) (hz : z₀ ≤ z₁)
    (hsum : y₁ + z₁ ≤ n) :
    h (Vertex.ofYZ n y₀ z₀ (by omega)) + h (Vertex.ofYZ n y₁ z₁ hsum) ≤
      h (Vertex.ofYZ n y₁ z₀ (by omega)) + h (Vertex.ofYZ n y₀ z₁ (by omega)) :=
  h.isRhombusConcave.parallelogram_le hy hz hsum

end Parallelogram

end TauCeti.Hive
