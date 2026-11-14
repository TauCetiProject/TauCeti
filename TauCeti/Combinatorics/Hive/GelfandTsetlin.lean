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

In the product chart `(i, j) ↦ (n - j, j - i, i)` (`0 ≤ i ≤ j ≤ n`) on `TauCeti.Hive.Vertex n`, a
normalized hive `h` with clockwise boundary `productBoundary lam μ γ = (λ, μ, γ*)` satisfies

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
`TauCeti.Hive.cyclicFixedIntegerHiveEquivGTPattern` (Henriques–Kamnitzer, Theorem 7.4).

When `λ` satisfies the uniform input gap `μ_0 - μ_n ≤ λ_r - λ_{r + 1}` for every `r : Fin n`, the
remaining rhombus family holds automatically for every pattern over `μ`
(`TauCeti.Hive.gt_completion_of_uniform_input_gap`), so `toGTPattern` and `gtCompletion` furnish an
equivalence onto the entire weight-`(γ - λ)` Gelfand–Tsetlin fibre over `μ`
(`TauCeti.Hive.stableGTPatternEquiv`, `TauCeti.Hive.exists_stable_gt_equiv`).

## Main definitions

* `TauCeti.Hive.Vertex.productChart`: the chart `(i, j) ↦ (n - j, j - i, i)` on `Vertex n`.
* `TauCeti.Hive.toGTPattern`, `TauCeti.Hive.gtCompletion`: the hive-to-pattern difference map and
  its inverse chart completion.
* `TauCeti.Hive.IsProductHiveFeasible`: the remaining product-chart rhombus inequalities on a
  pattern.
* `TauCeti.Hive.fixedIntegerHiveEquivGTPattern`,
  `TauCeti.Hive.cyclicFixedIntegerHiveEquivGTPattern`: equivalences between fixed-boundary integer
  hives and feasible Gelfand–Tsetlin weight fibres in product and cyclic orientations.
* `TauCeti.Hive.stableGTPatternEquiv`, `TauCeti.Hive.fixedIntegerHiveEquivGTPatternOfLeOne`:
  unconditional weight-fibre equivalences under the uniform input gap and for `n ≤ 1`.

## Main results

* `TauCeti.Hive.isRhombusConcave_iff_productChart`: unit-rhombus concavity is equivalent to the
  three product-chart rhombus families.
* `TauCeti.Hive.apply_eq_gtCompletion_toGTPattern`, `TauCeti.Hive.gt_reconstruction_iff`.
* `TauCeti.Hive.gt_completion_of_uniform_input_gap`, `TauCeti.Hive.exists_stable_gt_equiv`.
* `TauCeti.Hive.isProductHiveFeasible_two_iff`, `TauCeti.Hive.hiveCount_productBoundary_two`:
  rank-`2` Clebsch–Gordan characterization and low-rank checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Henriques and J. Kamnitzer, *The octahedron recurrence and $\mathfrak{gl}_n$ crystals*,
  Adv. Math. **206** (2006), 249–266, Theorem 7.4.
-/

public section

open scoped BigOperators

namespace TauCeti.Hive

/-! ### The product chart `(i, j) ↦ (n - j, j - i, i)` and boundary prefix sums -/

namespace Vertex

/-- The **product chart** `(i, j) ↦ (n - j, j - i, i)` on `Vertex n` for `0 ≤ i ≤ j ≤ n`. -/
def productChart (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) : Vertex n :=
  ⟨n - j, j - i, i, by omega⟩

@[simp]
theorem productChart_x (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (productChart n i j hij hjn).x = n - j := (rfl)

@[simp]
theorem productChart_y (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (productChart n i j hij hjn).y = j - i := (rfl)

@[simp]
theorem productChart_z (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    (productChart n i j hij hjn).z = i := (rfl)

theorem productChart_eq_ofYZ (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    productChart n i j hij hjn = ofYZ n (j - i) i (by omega) := by
  ext <;> simp; omega

@[simp]
theorem productChart_eq_iff {n i₁ j₁ i₂ j₂ : ℕ} {hi₁ : i₁ ≤ j₁} {hj₁ : j₁ ≤ n}
    {hi₂ : i₂ ≤ j₂} {hj₂ : j₂ ≤ n} :
    productChart n i₁ j₁ hi₁ hj₁ = productChart n i₂ j₂ hi₂ hj₂ ↔ i₁ = i₂ ∧ j₁ = j₂ := by
  refine ⟨fun h => ?_, fun ⟨hi, hj⟩ => by subst hi; subst hj; rfl⟩
  have hx := congrArg Vertex.x h
  have hz := congrArg Vertex.z h
  simp only [productChart_x, productChart_z] at hx hz
  exact ⟨hz, by omega⟩

/-- Every lattice vertex `p : Vertex n` is `productChart n p.z (n - p.x)`. -/
@[simp]
theorem productChart_z_sub_x {n : ℕ} (p : Vertex n) :
    productChart n p.z (n - p.x) (by have := p.sum_eq; omega) (Nat.sub_le n p.x) = p := by
  have := p.sum_eq
  ext <;> simp <;> omega

@[simp]
theorem productChart_zero_zero (n : ℕ) :
    productChart n 0 0 le_rfl (Nat.zero_le n) = cornerA n := by
  ext <;> simp

/-- Along `i = 0`, `productChart n 0 j` traverses side `0` (`A → B`). -/
theorem productChart_zero_left (n j : ℕ) (hjn : j ≤ n) :
    productChart n 0 j (Nat.zero_le j) hjn = edgePoint n 0 ⟨j, by omega⟩ := by
  ext <;> simp

/-- Along `j = n`, `productChart n i n` traverses side `1` (`B → C`). -/
theorem productChart_top_right (n i : ℕ) (hin : i ≤ n) :
    productChart n i n hin le_rfl = edgePoint n 1 ⟨i, by omega⟩ := by
  ext <;> simp

/-- Along the diagonal `i = j`, `productChart n j j` traverses side `2` (`C → A`) in reverse. -/
theorem productChart_diag (n j : ℕ) (hjn : j ≤ n) :
    productChart n j j le_rfl hjn = edgePoint n 2 ⟨n - j, by omega⟩ := by
  ext <;> simp; omega

end Vertex

section ChartBoundary

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R]

theorem apply_productChart_zero_left (h : Hive n R) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.productChart n 0 j (Nat.zero_le j) hjn) = prefixSum j (h.boundary 0) := by
  rw [Vertex.productChart_zero_left, h.apply_edgePoint_zero, prefixSum_def]

theorem apply_productChart_top_right (h : Hive n R) {i : ℕ} (hin : i ≤ n) :
    h (Vertex.productChart n i n hin le_rfl) =
      (∑ r : Fin n, h.boundary 0 r) + prefixSum i (h.boundary 1) := by
  rw [Vertex.productChart_top_right, h.apply_edgePoint_one, prefixSum_def]

theorem apply_productChart_diag (h : Hive n R) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.productChart n j j le_rfl hjn) =
      -∑ r : Fin n with n - j ≤ r.val, h.boundary 2 r := by
  rw [Vertex.productChart_diag, h.apply_edgePoint_two]

private theorem neg_sum_ge_neg_rev {G : Type*} [AddCommGroup G] (g : Fin n → G)
    {j : ℕ} (hjn : j ≤ n) :
    -(∑ r : Fin n with n - j ≤ r.val, -g r.rev) = prefixSum j g := by
  rw [← Finset.sum_neg_distrib, prefixSum_def, Finset.sum_filter, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun r _ => ?_).trans
    (Equiv.sum_comp Fin.revPerm fun s : Fin n => if s.val < j then g s else 0)
  have hrlt := r.isLt
  simp only [neg_neg, Fin.revPerm_apply, Fin.val_rev]
  by_cases hr : n - j ≤ r.val
  · simp [hr, show n - (r.val + 1) < j by omega]
  · simp [hr, show ¬ n - (r.val + 1) < j by omega]

theorem apply_productChart_diag_eq_prefixSum_dual (h : IntegerHive n) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.productChart n j j le_rfl hjn) = prefixSum j (h.boundaryWeight 2).dual.1 := by
  rw [apply_productChart_diag h hjn]
  have heq : (∑ r : Fin n with n - j ≤ r.val, h.boundary 2 r) =
      ∑ r : Fin n with n - j ≤ r.val, -(h.boundaryWeight 2).dual.1 r.rev :=
    Finset.sum_congr rfl fun r _ => by simp
  rw [heq, neg_sum_ge_neg_rev _ hjn]

theorem apply_productChart_zero_left_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.productChart n 0 j (Nat.zero_le j) hjn) = prefixSum j lam.1 := by
  rw [apply_productChart_zero_left, hb, productBoundary_zero]

theorem apply_productChart_top_right_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {i : ℕ} (hin : i ≤ n) :
    h (Vertex.productChart n i n hin le_rfl) = (∑ r, lam.1 r) + prefixSum i μ.1 := by
  rw [apply_productChart_top_right, hb, productBoundary_zero, productBoundary_one]

theorem apply_productChart_diag_of_productBoundary {lam μ γ : DominantWeight n}
    {h : IntegerHive n} (hb : h.boundary = productBoundary lam μ γ) {j : ℕ} (hjn : j ≤ n) :
    h (Vertex.productChart n j j le_rfl hjn) = prefixSum j γ.1 := by
  have hd : (h.boundaryWeight 2).dual = γ := by
    ext r
    simp [coe_boundaryWeight, hb]
  rw [apply_productChart_diag_eq_prefixSum_dual h hjn, hd]

end ChartBoundary

/-! ### The three unit-rhombus families in the product chart -/

section ProductChartRhombi

/-- First Gelfand–Tsetlin rhombus family in the product chart (`0 ≤ i < j < n`), encoding the
horizontal-strip inequality `h(i + 1, j) + h(i, j + 1) ≤ h(i, j) + h(i + 1, j + 1)`. -/
theorem isRhombus_productChart_gt_left {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (Vertex.productChart n i j hij.le hjn.le)
      (Vertex.productChart n (i + 1) j hij hjn.le)
      (Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)
      (Vertex.productChart n i (j + 1) (by omega) hjn) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy0 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy1 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy2 : ((j + 1 - i : ℕ) : ℤ) = (j : ℤ) - i + 1 := by omega
  have hy3 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  refine ⟨rfl, by simp only [Vertex.productChart_y]; omega,
    by simp only [Vertex.productChart_z]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.productChart_x, Vertex.productChart_y, Vertex.productChart_z,
      hx0, hx1, hy0, hy1, hy2, hy3, Nat.cast_add, Nat.cast_one]
    ring

/-- Second Gelfand–Tsetlin rhombus family in the product chart (`0 ≤ i < j < n`), encoding the
diagonal interlacing inequality `h(i, j) + h(i + 2, j + 1) ≤ h(i + 1, j) + h(i + 1, j + 1)`. -/
theorem isRhombus_productChart_gt_right {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    IsRhombus
      (Vertex.productChart n (i + 1) j hij hjn.le)
      (Vertex.productChart n i j hij.le hjn.le)
      (Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)
      (Vertex.productChart n (i + 2) (j + 1) (by omega) hjn) := by
  have hx0 : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
  have hx1 : ((n - (j + 1) : ℕ) : ℤ) = (n : ℤ) - j - 1 := by omega
  have hy0 : ((j - i : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy1 : ((j - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  have hy2 : ((j + 1 - (i + 1) : ℕ) : ℤ) = (j : ℤ) - i := by omega
  have hy3 : ((j + 1 - (i + 2) : ℕ) : ℤ) = (j : ℤ) - i - 1 := by omega
  refine ⟨rfl, by simp only [Vertex.productChart_y]; omega,
    by simp only [Vertex.productChart_z]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.productChart_x, Vertex.productChart_y, Vertex.productChart_z,
      hx0, hx1, hy0, hy1, hy2, hy3, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring

/-- Third (remaining) unit-rhombus family in the product chart (`0 ≤ i ≤ j`, `j + 2 ≤ n`),
encoding `h(i, j) + h(i + 1, j + 2) ≤ h(i, j + 1) + h(i + 1, j + 1)`. -/
theorem isRhombus_productChart_rem {n i j : ℕ} (hij : i ≤ j) (hjn : j + 2 ≤ n) :
    IsRhombus
      (Vertex.productChart n i (j + 1) (by omega) (by omega))
      (Vertex.productChart n i j hij (by omega))
      (Vertex.productChart n (i + 1) (j + 1) (by omega) (by omega))
      (Vertex.productChart n (i + 1) (j + 2) (by omega) hjn) := by
  have hr := isRhombus_ofYZ_step (n := n) (y := j - i) (z := i) (by omega)
  rwa [show Vertex.ofYZ n (j - i + 1) i _ = Vertex.productChart n i (j + 1) (by omega) (by omega)
      by ext <;> simp <;> omega,
    show Vertex.ofYZ n (j - i) i _ = Vertex.productChart n i j hij (by omega)
      by ext <;> simp; omega,
    show Vertex.ofYZ n (j - i) (i + 1) _ =
        Vertex.productChart n (i + 1) (j + 1) (by omega) (by omega)
      by ext <;> simp; omega,
    show Vertex.ofYZ n (j - i + 1) (i + 1) _ =
        Vertex.productChart n (i + 1) (j + 2) (by omega) hjn
      by ext <;> simp <;> omega] at hr

private theorem long_diag_cases {dx dy dz : ℤ} (hsum : dx + dy + dz = 0)
    (hsq : dx ^ 2 + dy ^ 2 + dz ^ 2 = 6) :
    (dx = 2 ∧ dy = -1 ∧ dz = -1) ∨ (dx = -2 ∧ dy = 1 ∧ dz = 1) ∨
      (dx = 1 ∧ dy = -2 ∧ dz = 1) ∨ (dx = -1 ∧ dy = 2 ∧ dz = -1) ∨
      (dx = 1 ∧ dy = 1 ∧ dz = -2) ∨ (dx = -1 ∧ dy = -1 ∧ dz = 2) := by
  have hbd {t : ℤ} (ht : t ^ 2 < 9) : -2 ≤ t ∧ t ≤ 2 :=
    ⟨by by_contra h; have : t ≤ -3 := (by omega); nlinarith,
      by by_contra h; have : 3 ≤ t := (by omega); nlinarith⟩
  have hdx := hbd (by linarith [sq_nonneg dy, sq_nonneg dz] : dx ^ 2 < 9)
  have hdy := hbd (by linarith [sq_nonneg dx, sq_nonneg dz] : dy ^ 2 < 9)
  have hdz : dz = -dx - dy := by omega
  subst hdz
  rcases (by omega : dx = -2 ∨ dx = -1 ∨ dx = 0 ∨ dx = 1 ∨ dx = 2) with
      rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : dy = -2 ∨ dy = -1 ∨ dy = 0 ∨ dy = 1 ∨ dy = 2) with
      rfl | rfl | rfl | rfl | rfl <;>
    (revert hsq; decide)

private theorem unit_step_split {u₁ u₂ u₃ : ℤ} (hsum : u₁ + u₂ + u₃ = 0)
    (hsq₁ : u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 = 2)
    (hsq₂ : (2 - u₁) ^ 2 + (-1 - u₂) ^ 2 + (-1 - u₃) ^ 2 = 2) :
    u₁ = 1 ∧ ((u₂ = 0 ∧ u₃ = -1) ∨ (u₂ = -1 ∧ u₃ = 0)) := by
  have hu₁ : u₁ = 1 := by linarith
  subst hu₁
  have hu₂ : -1 ≤ u₂ ∧ u₂ ≤ 1 :=
    ⟨by by_contra h; have : u₂ ≤ -2 := (by omega); nlinarith [sq_nonneg u₃],
      by by_contra h; have : 2 ≤ u₂ := (by omega); nlinarith [sq_nonneg u₃]⟩
  have hu₃ : u₃ = -1 - u₂ := by omega
  subst hu₃
  refine ⟨rfl, ?_⟩
  rcases (by omega : u₂ = -1 ∨ u₂ = 0 ∨ u₂ = 1) with rfl | rfl | rfl <;> (revert hsq₁; decide)

private theorem le_of_isRhombus_oriented {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    {f : Vertex n → R}
    (hL : ∀ ⦃i j : ℕ⦄ (hij : i < j) (hjn : j < n),
      f (Vertex.productChart n (i + 1) j hij hjn.le) +
          f (Vertex.productChart n i (j + 1) (by omega) hjn) ≤
        f (Vertex.productChart n i j hij.le hjn.le) +
          f (Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn))
    (hR : ∀ ⦃i j : ℕ⦄ (hij : i < j) (hjn : j < n),
      f (Vertex.productChart n i j hij.le hjn.le) +
          f (Vertex.productChart n (i + 2) (j + 1) (by omega) hjn) ≤
        f (Vertex.productChart n (i + 1) j hij hjn.le) +
          f (Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn))
    (hRem : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j) (hjn : j + 2 ≤ n),
      f (Vertex.productChart n i j hij (by omega)) +
          f (Vertex.productChart n (i + 1) (j + 2) (by omega) hjn) ≤
        f (Vertex.productChart n i (j + 1) (by omega) (by omega)) +
          f (Vertex.productChart n (i + 1) (j + 1) (by omega) (by omega)))
    {a b c d : Vertex n} (hr : IsRhombus a b c d)
    (hor : ((b.x : ℤ) - d.x = 2 ∧ (b.y : ℤ) - d.y = -1 ∧ (b.z : ℤ) - d.z = -1) ∨
      ((b.x : ℤ) - d.x = 1 ∧ (b.y : ℤ) - d.y = -2 ∧ (b.z : ℤ) - d.z = 1) ∨
      ((b.x : ℤ) - d.x = 1 ∧ (b.y : ℤ) - d.y = 1 ∧ (b.z : ℤ) - d.z = -2)) :
    f b + f d ≤ f a + f c := by
  have ha_sum := a.sum_eq; have hb_sum := b.sum_eq
  have hc_sum := c.sum_eq; have hd_sum := d.sum_eq
  have hmx := hr.midpoint_x; have hmy := hr.midpoint_y; have _ := hr.midpoint_z
  have hab := hr.side_ab; rw [Vertex.sqDist_def] at hab
  have hda := hr.side_da; rw [Vertex.sqDist_def] at hda
  rcases hor with ⟨hdx, hdy, _⟩ | ⟨hdx, hdy, _⟩ | ⟨hdx, hdy, _⟩
  · have hsplit := unit_step_split
      (u₁ := (a.x : ℤ) - d.x) (u₂ := (a.y : ℤ) - d.y) (u₃ := (a.z : ℤ) - d.z)
      (by omega) (by linarith) (by
        convert hab using 1
        rw [show (b.x : ℤ) = d.x + 2 by omega, show (b.y : ℤ) = d.y - 1 by omega,
          show (b.z : ℤ) = d.z - 1 by omega]; ring)
    obtain ⟨i, hi⟩ : ∃ i, b.z = i := ⟨b.z, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j, n - b.x = j := ⟨n - b.x, rfl⟩
    have hij : i ≤ j := by omega
    have hjn : j + 2 ≤ n := by omega
    have hb_eq : b = Vertex.productChart n i j hij (by omega) := by ext <;> simp <;> omega
    have hd_eq : d = Vertex.productChart n (i + 1) (j + 2) (by omega) hjn := by
      ext <;> simp <;> omega
    have h := hRem hij hjn
    rcases hsplit with ⟨hux, ⟨huy, huz⟩ | ⟨huy, huz⟩⟩
    · have ha_eq : a = Vertex.productChart n i (j + 1) (by omega) (by omega) := by
        ext <;> simp <;> omega
      have hc_eq : c = Vertex.productChart n (i + 1) (j + 1) (by omega) (by omega) := by
        ext <;> simp <;> omega
      rwa [← hb_eq, ← hd_eq, ← ha_eq, ← hc_eq] at h
    · have ha_eq : a = Vertex.productChart n (i + 1) (j + 1) (by omega) (by omega) := by
        ext <;> simp <;> omega
      have hc_eq : c = Vertex.productChart n i (j + 1) (by omega) (by omega) := by
        ext <;> simp <;> omega
      rwa [← hb_eq, ← hd_eq, ← hc_eq, ← ha_eq, add_comm (f c)] at h
  · have hsplit := unit_step_split
      (u₁ := (a.y : ℤ) - b.y) (u₂ := (a.x : ℤ) - b.x) (u₃ := (a.z : ℤ) - b.z)
      (by omega) (by linarith) (by
        convert hda using 1
        rw [show (d.x : ℤ) = b.x - 1 by omega, show (d.y : ℤ) = b.y + 2 by omega,
          show (d.z : ℤ) = b.z - 1 by omega]; ring)
    obtain ⟨i, hi⟩ : ∃ i, d.z = i := ⟨d.z, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j, n - b.x = j := ⟨n - b.x, rfl⟩
    have hij : i < j := by omega
    have hjn : j < n := by omega
    have hb_eq : b = Vertex.productChart n (i + 1) j hij hjn.le := by ext <;> simp <;> omega
    have hd_eq : d = Vertex.productChart n i (j + 1) (by omega) hjn := by ext <;> simp <;> omega
    have h := hL hij hjn
    rcases hsplit with ⟨huy, ⟨hux, huz⟩ | ⟨hux, huz⟩⟩
    · have ha_eq : a = Vertex.productChart n i j hij.le hjn.le := by ext <;> simp <;> omega
      have hc_eq : c = Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn := by
        ext <;> simp <;> omega
      rwa [← hb_eq, ← hd_eq, ← ha_eq, ← hc_eq] at h
    · have ha_eq : a = Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn := by
        ext <;> simp <;> omega
      have hc_eq : c = Vertex.productChart n i j hij.le hjn.le := by ext <;> simp <;> omega
      rwa [← hb_eq, ← hd_eq, ← hc_eq, ← ha_eq, add_comm (f c)] at h
  · have hsplit := unit_step_split
      (u₁ := (a.z : ℤ) - b.z) (u₂ := (a.x : ℤ) - b.x) (u₃ := (a.y : ℤ) - b.y)
      (by omega) (by linarith) (by
        convert hda using 1
        rw [show (d.x : ℤ) = b.x - 1 by omega, show (d.y : ℤ) = b.y - 1 by omega,
          show (d.z : ℤ) = b.z + 2 by omega]; ring)
    obtain ⟨i, hi⟩ : ∃ i, b.z = i := ⟨b.z, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j, n - b.x = j := ⟨n - b.x, rfl⟩
    have hij : i < j := by omega
    have hjn : j < n := by omega
    have hb_eq : b = Vertex.productChart n i j hij.le hjn.le := by ext <;> simp <;> omega
    have hd_eq : d = Vertex.productChart n (i + 2) (j + 1) (by omega) hjn := by
      ext <;> simp <;> omega
    have h := hR hij hjn
    rcases hsplit with ⟨huz, ⟨hux, huy⟩ | ⟨hux, huy⟩⟩
    · have ha_eq : a = Vertex.productChart n (i + 1) j hij hjn.le := by ext <;> simp <;> omega
      have hc_eq : c = Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn := by
        ext <;> simp <;> omega
      rwa [← hb_eq, ← hd_eq, ← ha_eq, ← hc_eq] at h
    · have ha_eq : a = Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn := by
        ext <;> simp <;> omega
      have hc_eq : c = Vertex.productChart n (i + 1) j hij hjn.le := by ext <;> simp <;> omega
      rwa [← hb_eq, ← hd_eq, ← hc_eq, ← ha_eq, add_comm (f c)] at h

/-- **Product-chart characterization of unit-rhombus concavity**: a function `f : Vertex n → R` is
rhombus-concave iff it satisfies the two Gelfand–Tsetlin interlacing rhombus families for
`0 ≤ i < j < n` and the remaining rhombus family for `0 ≤ i ≤ j`, `j + 2 ≤ n`. -/
theorem isRhombusConcave_iff_productChart {n : ℕ} {R : Type*} [AddCommGroup R] [Preorder R]
    (f : Vertex n → R) :
    IsRhombusConcave f ↔
      (∀ ⦃i j : ℕ⦄ (hij : i < j) (hjn : j < n),
        f (Vertex.productChart n (i + 1) j hij hjn.le) +
            f (Vertex.productChart n i (j + 1) (by omega) hjn) ≤
          f (Vertex.productChart n i j hij.le hjn.le) +
            f (Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)) ∧
      (∀ ⦃i j : ℕ⦄ (hij : i < j) (hjn : j < n),
        f (Vertex.productChart n i j hij.le hjn.le) +
            f (Vertex.productChart n (i + 2) (j + 1) (by omega) hjn) ≤
          f (Vertex.productChart n (i + 1) j hij hjn.le) +
            f (Vertex.productChart n (i + 1) (j + 1) (Nat.succ_le_succ hij.le) hjn)) ∧
      (∀ ⦃i j : ℕ⦄ (hij : i ≤ j) (hjn : j + 2 ≤ n),
        f (Vertex.productChart n i j hij (by omega)) +
            f (Vertex.productChart n (i + 1) (j + 2) (by omega) hjn) ≤
          f (Vertex.productChart n i (j + 1) (by omega) (by omega)) +
            f (Vertex.productChart n (i + 1) (j + 1) (by omega) (by omega))) := by
  rw [isRhombusConcave_def]
  refine ⟨fun hf => ⟨fun i j hij hjn => hf (isRhombus_productChart_gt_left hij hjn),
      fun i j hij hjn => hf (isRhombus_productChart_gt_right hij hjn),
      fun i j hij hjn => hf (isRhombus_productChart_rem hij hjn)⟩,
    fun ⟨hL, hR, hRem⟩ a b c d hr => ?_⟩
  have hb_sum := b.sum_eq; have hd_sum := d.sum_eq
  have hlong := hr.long; rw [Vertex.sqDist_def] at hlong
  rcases long_diag_cases
      (dx := (b.x : ℤ) - d.x) (dy := (b.y : ℤ) - d.y) (dz := (b.z : ℤ) - d.z)
      (by omega) hlong with h1 | h2 | h3 | h4 | h5 | h6
  · exact le_of_isRhombus_oriented hL hR hRem hr (Or.inl h1)
  · rw [add_comm (f b), add_comm (f a)]
    exact le_of_isRhombus_oriented hL hR hRem hr.swap_opposite
      (Or.inl ⟨by omega, by omega, by omega⟩)
  · exact le_of_isRhombus_oriented hL hR hRem hr (Or.inr (Or.inl h3))
  · rw [add_comm (f b), add_comm (f a)]
    exact le_of_isRhombus_oriented hL hR hRem hr.swap_opposite
      (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
  · exact le_of_isRhombus_oriented hL hR hRem hr (Or.inr (Or.inr h5))
  · rw [add_comm (f b), add_comm (f a)]
    exact le_of_isRhombus_oriented hL hR hRem hr.swap_opposite
      (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))

end ProductChartRhombi

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

theorem toGTPattern_apply_of_lt_of_le (h : IntegerHive n) {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    h.toGTPattern i j =
      h (Vertex.productChart n (i + 1) j hij hjn) -
        h (Vertex.productChart n i j hij.le hjn) := by
  change (if h1 : i < j then if h2 : j ≤ n then _ else 0 else 0) = _
  rw [dite_eq_left hij, dite_eq_left hjn]

@[simp]
theorem toGTPattern_zero : (0 : IntegerHive n).toGTPattern = 0 := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · simp [toGTPattern_apply_of_lt_of_le _ h.1 h.2]
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.zero_apply]

@[simp]
theorem toGTPattern_add (h₁ h₂ : IntegerHive n) :
    (h₁ + h₂).toGTPattern = h₁.toGTPattern + h₂.toGTPattern := by
  ext i j
  by_cases h : i < j ∧ j ≤ n
  · simp only [GTPattern.add_apply, toGTPattern_apply_of_lt_of_le _ h.1 h.2, add_apply]
    abel
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.add_apply,
      GTPattern.entry_eq_zero _ (by omega), GTPattern.entry_eq_zero _ (by omega), add_zero]

@[simp]
theorem toGTPattern_nsmul (k : ℕ) (h : IntegerHive n) :
    (k • h).toGTPattern = k • h.toGTPattern := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · simp only [GTPattern.nsmul_apply, toGTPattern_apply_of_lt_of_le _ hij.1 hij.2, nsmul_apply,
      nsmul_eq_mul]
    ring
  · rw [GTPattern.entry_eq_zero _ (by omega), GTPattern.nsmul_apply,
      GTPattern.entry_eq_zero _ (by omega), smul_zero]

/-- `TauCeti.Hive.toGTPattern` bundled as an additive monoid homomorphism. -/
def toGTPatternAddMonoidHom (n : ℕ) : IntegerHive n →+ GTPattern n where
  toFun := toGTPattern
  map_zero' := toGTPattern_zero
  map_add' := toGTPattern_add

@[simp]
theorem toGTPatternAddMonoidHom_apply (h : IntegerHive n) :
    toGTPatternAddMonoidHom n h = h.toGTPattern := (rfl)

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
      toGTPattern_apply_of_lt_of_le h (Nat.lt_of_succ_le hij) hjn]
    abel

/-- The top row of `h.toGTPattern` is side `1` (`B → C`) of `h.boundary`. -/
@[simp]
theorem topRow_toGTPattern (h : IntegerHive n) : h.toGTPattern.topRow = h.boundary 1 := by
  ext r
  rw [GTPattern.topRow_apply, toGTPattern_apply_of_lt_of_le h r.isLt le_rfl,
    Vertex.productChart_top_right, Vertex.productChart_top_right, boundary_apply]
  rfl

@[simp]
theorem topWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.topWeight = h.boundaryWeight 1 := by
  apply Subtype.ext
  rw [GTPattern.topWeight_coe, topRow_toGTPattern, coe_boundaryWeight]

theorem rowSum_toGTPattern (h : IntegerHive n) {j : ℕ} (hjn : j ≤ n) :
    h.toGTPattern.rowSum j =
      prefixSum j (h.boundaryWeight 2).dual.1 - prefixSum j (h.boundary 0) := by
  rw [GTPattern.rowSum_def, sum_range_toGTPattern h le_rfl hjn,
    apply_productChart_diag_eq_prefixSum_dual h hjn, apply_productChart_zero_left h hjn]

/-- The torus weight of `h.toGTPattern` is `(h.boundaryWeight 2).dual - h.boundary 0`. -/
@[simp]
theorem rowWeight_toGTPattern (h : IntegerHive n) :
    h.toGTPattern.rowWeight = (h.boundaryWeight 2).dual.1 - h.boundary 0 := by
  ext r
  rw [GTPattern.rowWeight_apply, rowSum_toGTPattern h (by omega),
    rowSum_toGTPattern h r.isLt.le, prefixSum_succ r.isLt, prefixSum_succ r.isLt, Pi.sub_apply]
  abel

theorem topRow_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) :
    h.toGTPattern.topRow = μ.1 := by
  rw [topRow_toGTPattern, hb, productBoundary_one]

theorem rowWeight_toGTPattern_of_productBoundary {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) :
    h.toGTPattern.rowWeight = γ.1 - lam.1 := by
  have hd : (h.boundaryWeight 2).dual = γ := by ext r; simp [coe_boundaryWeight, hb]
  rw [rowWeight_toGTPattern, hd, hb, productBoundary_zero]

/-- The **inverse chart completion** `h(i, j) = prefixSum j l + ∑_{k < i} P k j` reconstructing
product-chart hive entries from lower-left boundary `l` and pattern `P`. -/
def gtCompletion (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) : ℤ :=
  prefixSum j l + ∑ k ∈ Finset.range i, P k j

theorem gtCompletion_def (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P i j = prefixSum j l + ∑ k ∈ Finset.range i, P k j := (rfl)

@[simp]
theorem gtCompletion_zero_left (l : Fin n → ℤ) (P : GTPattern n) (j : ℕ) :
    gtCompletion l P 0 j = prefixSum j l := by
  simp [gtCompletion_def]

@[simp]
theorem gtCompletion_zero_right (l : Fin n → ℤ) (P : GTPattern n) (i : ℕ) :
    gtCompletion l P i 0 = 0 := by
  rw [gtCompletion_def, prefixSum_zero, zero_add]
  exact Finset.sum_eq_zero fun k _ => P.entry_eq_zero_of_le (Nat.zero_le k)

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

theorem gtCompletion_top_right (l : Fin n → ℤ) (P : GTPattern n) {i : ℕ} (hin : i ≤ n) :
    gtCompletion l P i n = (∑ r : Fin n, l r) + prefixSum i P.topRow := by
  rw [gtCompletion_def, prefixSum_of_le le_rfl, prefixSum_eq_sum_castLE hin]
  congr 1
  simpa [GTPattern.topRow_apply] using (Fin.sum_univ_eq_sum_range (fun k => P k n) i).symm

theorem gtCompletion_succ_left (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P (i + 1) j = gtCompletion l P i j + P i j := by
  rw [gtCompletion_def, gtCompletion_def, Finset.sum_range_succ, add_assoc]

@[simp]
theorem gtCompletion_succ_left_sub (l : Fin n → ℤ) (P : GTPattern n) (i j : ℕ) :
    gtCompletion l P (i + 1) j - gtCompletion l P i j = P i j := by
  rw [gtCompletion_succ_left, add_sub_cancel_left]

/-- **Inverse formula in the product chart**: `gtCompletion` recovers every chart value of `h` from
`h.boundary 0` and `h.toGTPattern`. -/
theorem gtCompletion_toGTPattern (h : IntegerHive n) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletion (h.boundary 0) h.toGTPattern i j = h (Vertex.productChart n i j hij hjn) := by
  rw [gtCompletion_def, sum_range_toGTPattern h hij hjn, apply_productChart_zero_left h hjn]
  abel

/-- **Vertex-level inverse formula**: every integer hive `h` is reconstructed at `p : Vertex n` as
`gtCompletion (h.boundary 0) h.toGTPattern p.z (n - p.x)`. -/
theorem apply_eq_gtCompletion_toGTPattern (h : IntegerHive n) (p : Vertex n) :
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

theorem gtCompletionVertex_def (l : Fin n → ℤ) (P : GTPattern n) (p : Vertex n) :
    gtCompletionVertex l P p = gtCompletion l P p.z (n - p.x) := (rfl)

@[simp]
theorem gtCompletionVertex_productChart (l : Fin n → ℤ) (P : GTPattern n) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) :
    gtCompletionVertex l P (Vertex.productChart n i j hij hjn) = gtCompletion l P i j := by
  simp [gtCompletionVertex, show n - (n - j) = j by omega]

@[simp]
theorem gtCompletionVertex_cornerA (l : Fin n → ℤ) (P : GTPattern n) :
    gtCompletionVertex l P (Vertex.cornerA n) = 0 := by
  simp [gtCompletionVertex]

/-- When `P.rowWeight = g - l`, the clockwise linear boundary of `gtCompletionVertex l P` has sides
`l`, `P.topRow`, and `r ↦ -g r.rev`. -/
theorem boundaryLinear_gtCompletionVertex {l g : Fin n → ℤ} {P : GTPattern n}
    (hw : P.rowWeight = g - l) :
    boundaryLinear ℤ n ℤ (gtCompletionVertex l P) = ![l, P.topRow, fun r => -g r.rev] := by
  ext s r
  fin_cases s
  · change boundaryLinear ℤ n ℤ (gtCompletionVertex l P) 0 r = l r
    have hsucc : Vertex.edgePoint n 0 r.succ =
        Vertex.productChart n 0 (r.val + 1) (Nat.zero_le _) (by omega) := by ext <;> simp
    have hcast : Vertex.edgePoint n 0 r.castSucc =
        Vertex.productChart n 0 r.val (Nat.zero_le _) r.isLt.le := by ext <;> simp
    rw [boundaryLinear_apply, hsucc, hcast, gtCompletionVertex_productChart,
      gtCompletionVertex_productChart, gtCompletion_zero_left, gtCompletion_zero_left,
      prefixSum_succ r.isLt]
    abel
  · change boundaryLinear ℤ n ℤ (gtCompletionVertex l P) 1 r = P.topRow r
    have hsucc : Vertex.edgePoint n 1 r.succ =
        Vertex.productChart n (r.val + 1) n (by omega) le_rfl := by ext <;> simp
    have hcast : Vertex.edgePoint n 1 r.castSucc =
        Vertex.productChart n r.val n r.isLt.le le_rfl := by ext <;> simp
    rw [boundaryLinear_apply, hsucc, hcast, gtCompletionVertex_productChart,
      gtCompletionVertex_productChart, gtCompletion_succ_left_sub, GTPattern.topRow_apply]
  · change boundaryLinear ℤ n ℤ (gtCompletionVertex l P) 2 r = -g r.rev
    have hsucc : Vertex.edgePoint n 2 r.succ =
        Vertex.productChart n r.rev.val r.rev.val le_rfl (by omega) := by
      have := r.isLt; ext <;> simp [Fin.val_rev]; omega
    have hcast : Vertex.edgePoint n 2 r.castSucc =
        Vertex.productChart n (r.rev.val + 1) (r.rev.val + 1) le_rfl (by omega) := by
      have := r.isLt; ext <;> simp [Fin.val_rev] <;> omega
    rw [boundaryLinear_apply, hsucc, hcast, gtCompletionVertex_productChart,
      gtCompletionVertex_productChart, gtCompletion_diag_of_rowWeight_eq hw (by omega),
      gtCompletion_diag_of_rowWeight_eq hw (by omega), prefixSum_succ r.rev.isLt, Fin.eta]
    abel

private theorem boundaryLinear_gtCompletionVertex_eq_productBoundary {lam μ γ : DominantWeight n}
    {P : GTPattern n} (hTop : P.topRow = μ.1) (hWeight : P.rowWeight = γ.1 - lam.1) :
    boundaryLinear ℤ n ℤ (gtCompletionVertex lam.1 P) = productBoundary lam μ γ := by
  rw [boundaryLinear_gtCompletionVertex hWeight, hTop]
  ext s r
  fin_cases s <;> simp

/-- Taking `toGTPattern` of any hive whose entries are given by `gtCompletion l P` returns `P`. -/
theorem toGTPattern_of_eq_gtCompletion {l : Fin n → ℤ} {P : GTPattern n} {h : IntegerHive n}
    (heq : ∀ p : Vertex n, h p = gtCompletion l P p.z (n - p.x)) :
    h.toGTPattern = P := by
  ext i j
  by_cases hij : i < j ∧ j ≤ n
  · rw [toGTPattern_apply_of_lt_of_le h hij.1 hij.2, heq, heq]
    simp only [Vertex.productChart_z, Vertex.productChart_x, show n - (n - j) = j by omega,
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
  simp only [gtCompletion_def, show j + 2 = (j + 1) + 1 from rfl,
    prefixSum_succ hj2, prefixSum_succ hj1, Finset.sum_sub_distrib]
  omega

theorem isProductHiveFeasible_iff_gtCompletion (l : Fin n → ℤ) (P : GTPattern n) :
    IsProductHiveFeasible l P ↔
      ∀ i j : ℕ, i ≤ j → j + 2 ≤ n →
        gtCompletion l P i j + gtCompletion l P (i + 1) (j + 2) ≤
          gtCompletion l P i (j + 1) + gtCompletion l P (i + 1) (j + 1) :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr_right fun _ =>
    forall_congr' fun hjn => (gtCompletion_rem_le_iff l P hjn).symm

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
  · simp only [gtCompletionVertex_productChart, show i + 2 = (i + 1) + 1 from rfl,
      gtCompletion_succ_left]
    linarith [P.entry_succ_succ_le_entry (i := i) hjn]
  · simpa only [gtCompletionVertex_productChart] using hrem i j hij hjn

theorem isProductHiveFeasible_toGTPattern (h : IntegerHive n) :
    IsProductHiveFeasible (h.boundary 0) h.toGTPattern := by
  rw [isProductHiveFeasible_iff_gtCompletion]
  intro i j hij hjn
  simp only [gtCompletion_toGTPattern h hij (by omega),
    gtCompletion_toGTPattern h (by omega : i + 1 ≤ j + 2) hjn,
    gtCompletion_toGTPattern h (by omega : i ≤ j + 1) (by omega),
    gtCompletion_toGTPattern h (by omega : i + 1 ≤ j + 1) (by omega)]
  exact h.le_of_isRhombus (isRhombus_productChart_rem hij hjn)

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
  rw [← isRhombusConcave_gtCompletionVertex_iff]
  refine ⟨fun ⟨⟨h, _⟩, heq⟩ => ?_, fun hconc => ?_⟩
  · have hf : (h : Vertex n → ℤ) = gtCompletionVertex lam.1 P := funext heq
    exact hf ▸ h.isRhombusConcave
  · refine ⟨⟨⟨gtCompletionVertex lam.1 P, gtCompletionVertex_cornerA lam.1 P,
        fun hr => (isRhombusConcave_def _).mp hconc hr⟩, ?_⟩, fun _ => rfl⟩
    rw [boundary_def]
    exact boundaryLinear_gtCompletionVertex_eq_productBoundary hTop hWeight

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
        have hf := isProductHiveFeasible_toGTPattern h.1
        rwa [h.2, productBoundary_zero] at hf⟩
  invFun P :=
    have hconc : IsRhombusConcave (gtCompletionVertex lam.1 P.1) :=
      (isRhombusConcave_gtCompletionVertex_iff lam.1 P.1).mpr
        ((isProductHiveFeasible_iff_gtCompletion lam.1 P.1).mp P.2.2.2)
    ⟨⟨gtCompletionVertex lam.1 P.1, gtCompletionVertex_cornerA lam.1 P.1,
        fun hr => (isRhombusConcave_def _).mp hconc hr⟩, by
      rw [boundary_def]
      exact boundaryLinear_gtCompletionVertex_eq_productBoundary P.2.1 P.2.2.1⟩
  left_inv h := Subtype.ext (ext fun p => (apply_eq_gtCompletion_of_productBoundary h.2 p).symm)
  right_inv P := Subtype.ext (toGTPattern_of_eq_gtCompletion fun _ => rfl)

@[simp]
theorem fixedIntegerHiveEquivGTPattern_apply_coe (lam μ γ : DominantWeight n)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPattern lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp]
theorem fixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ γ : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1 ∧
      IsProductHiveFeasible lam.1 P})
    (p : Vertex n) :
    ((fixedIntegerHiveEquivGTPattern lam μ γ).symm P).1 p =
      gtCompletion lam.1 P.1 p.z (n - p.x) := (rfl)

theorem hiveCount_productBoundary_eq_card_gtPattern (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1 ∧
        IsProductHiveFeasible lam.1 P} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (fixedIntegerHiveEquivGTPattern lam μ γ)

end Reconstruction

/-! ### Cyclic `(λ, μ, ν)` orientation and Henriques–Kamnitzer conversion -/

section CyclicOrientation

variable {n : ℕ}

/-- The clockwise cyclic boundary `(λ, μ, ν)` counting invariants in `V_λ ⊗ V_μ ⊗ V_ν`. -/
def cyclicBoundary (lam μ ν : DominantWeight n) : Fin 3 → Fin n → ℤ :=
  ![lam.1, μ.1, ν.1]

@[simp]
theorem cyclicBoundary_zero (lam μ ν : DominantWeight n) : cyclicBoundary lam μ ν 0 = lam.1 := (rfl)
@[simp]
theorem cyclicBoundary_one (lam μ ν : DominantWeight n) : cyclicBoundary lam μ ν 1 = μ.1 := (rfl)
@[simp]
theorem cyclicBoundary_two (lam μ ν : DominantWeight n) : cyclicBoundary lam μ ν 2 = ν.1 := (rfl)

/-- Two clockwise rotations convert `FixedIntegerHive (cyclicBoundary lam μ ν)` into
`FixedIntegerHive (productBoundary ν lam μ.dual)`, shifting entries by `-h C = ∑ r, ν.1 r`. -/
def fixedIntegerHiveRotateTwiceEquiv (lam μ ν : DominantWeight n) :
    FixedIntegerHive (cyclicBoundary lam μ ν) ≃
      FixedIntegerHive (productBoundary ν lam μ.dual) where
  toFun h :=
    ⟨h.1.rotate.rotate, by
      ext s r
      fin_cases s <;> simp [boundary_rotate, h.2, cyclicBoundary]⟩
  invFun h :=
    ⟨h.1.rotate, by
      ext s r
      fin_cases s <;> simp [boundary_rotate, h.2, cyclicBoundary]⟩
  left_inv h := Subtype.ext h.1.rotate_rotate_rotate
  right_inv h := Subtype.ext h.1.rotate_rotate_rotate

/-- Explicit gauge conversion on entries under `fixedIntegerHiveRotateTwiceEquiv`:
`(h.rotate.rotate) p = h p.rotate.rotate + ∑ r, ν.1 r`. -/
@[simp]
theorem fixedIntegerHiveRotateTwiceEquiv_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) (p : Vertex n) :
    (fixedIntegerHiveRotateTwiceEquiv lam μ ν h).1 p =
      h.1 p.rotate.rotate + ∑ r : Fin n, ν.1 r := by
  have hC : (Vertex.cornerA n).rotate.rotate = Vertex.edgePoint n 2 0 := by ext <;> simp
  have hall : ({r : Fin n | 0 ≤ r.val} : Finset (Fin n)) = Finset.univ := by ext r; simp
  have hval : h.1 (Vertex.cornerA n).rotate.rotate = -∑ r : Fin n, ν.1 r := by
    rw [hC, h.1.apply_edgePoint_two 0, Fin.val_zero, hall, h.2, cyclicBoundary_two]
  change h.1.rotate.rotate p = _
  simp only [rotate_apply, hval]
  abel

@[simp]
theorem fixedIntegerHiveRotateTwiceEquiv_symm_apply_coe (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (productBoundary ν lam μ.dual)) (p : Vertex n) :
    ((fixedIntegerHiveRotateTwiceEquiv lam μ ν).symm h).1 p =
      h.1 p.rotate - ∑ r : Fin n, ν.1 r := by
  have hB : (Vertex.cornerA n).rotate = Vertex.edgePoint n 0 (Fin.last n) := by ext <;> simp
  have hall : ({r : Fin n | r.val < n} : Finset (Fin n)) = Finset.univ := by ext r; simp
  have hval : h.1 (Vertex.cornerA n).rotate = ∑ r : Fin n, ν.1 r := by
    rw [hB, h.1.apply_edgePoint_zero, Fin.val_last, hall, h.2, productBoundary_zero]
  change h.1.rotate p = _
  rw [rotate_apply, hval]

/-- **Cyclic-orientation hive-to-Gelfand–Tsetlin equivalence** (Henriques–Kamnitzer, Theorem 7.4):
integer hives with cyclic boundary `(λ, μ, ν)` correspond to patterns with top row `λ`, torus
weight `μ* - ν`, and remaining rhombus feasibility with respect to `ν`. -/
def cyclicFixedIntegerHiveEquivGTPattern (lam μ ν : DominantWeight n) :
    FixedIntegerHive (cyclicBoundary lam μ ν) ≃
      {P : GTPattern n // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1 ∧
        IsProductHiveFeasible ν.1 P} :=
  (fixedIntegerHiveRotateTwiceEquiv lam μ ν).trans (fixedIntegerHiveEquivGTPattern ν lam μ.dual)

@[simp]
theorem cyclicFixedIntegerHiveEquivGTPattern_symm_apply_coe (lam μ ν : DominantWeight n)
    (P : {P : GTPattern n // P.topRow = lam.1 ∧ P.rowWeight = μ.dual.1 - ν.1 ∧
      IsProductHiveFeasible ν.1 P})
    (p : Vertex n) :
    ((cyclicFixedIntegerHiveEquivGTPattern lam μ ν).symm P).1 p =
      gtCompletion ν.1 P.1 p.y (n - p.z) - ∑ r : Fin n, ν.1 r := by
  change ((fixedIntegerHiveRotateTwiceEquiv lam μ ν).symm
    ((fixedIntegerHiveEquivGTPattern ν lam μ.dual).symm P)).1 p = _
  rw [fixedIntegerHiveRotateTwiceEquiv_symm_apply_coe,
    fixedIntegerHiveEquivGTPattern_symm_apply_coe, Vertex.rotate_z, Vertex.rotate_x]

/-- Forward directional-difference formula in the cyclic orientation `(λ, μ, ν)`: the gauge shift
cancels, leaving `h(j - i - 1, i + 1, n - j) - h(j - i, i, n - j)` for `0 ≤ i < j ≤ n`. -/
theorem cyclicFixedIntegerHiveEquivGTPattern_apply_of_lt_of_le (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive (cyclicBoundary lam μ ν)) {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
    (cyclicFixedIntegerHiveEquivGTPattern lam μ ν h).1 i j =
      h.1 ⟨j - (i + 1), i + 1, n - j, by omega⟩ - h.1 ⟨j - i, i, n - j, by omega⟩ := by
  change (fixedIntegerHiveRotateTwiceEquiv lam μ ν h).1.toGTPattern i j = _
  rw [toGTPattern_apply_of_lt_of_le _ hij hjn,
    fixedIntegerHiveRotateTwiceEquiv_apply_coe, fixedIntegerHiveRotateTwiceEquiv_apply_coe]
  have hp1 : (Vertex.productChart n (i + 1) j hij hjn).rotate.rotate =
      ⟨j - (i + 1), i + 1, n - j, by omega⟩ := by ext <;> simp
  have hp0 : (Vertex.productChart n i j hij.le hjn).rotate.rotate =
      ⟨j - i, i, n - j, by omega⟩ := by ext <;> simp
  rw [hp1, hp0]
  abel

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
has top row `μ` and `μ_0 - μ_n ≤ λ_r - λ_{r + 1}` for every `r : Fin n`, then every remaining
product-chart rhombus inequality holds on `gtCompletion lam.1 P`. -/
theorem gt_completion_of_uniform_input_gap {n : ℕ}
    (lam μ : DominantWeight (n + 1)) (P : GTPattern (n + 1))
    (hTop : P.topRow = μ.1)
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    ∀ i j : ℕ, i ≤ j → j + 2 ≤ n + 1 →
      gtCompletion lam.1 P i j + gtCompletion lam.1 P (i + 1) (j + 2) ≤
        gtCompletion lam.1 P i (j + 1) + gtCompletion lam.1 P (i + 1) (j + 1) := by
  intro i j hij hjn
  rw [gtCompletion_rem_le_iff lam.1 P hjn]
  have hleft_nonneg : 0 ≤ ∑ k ∈ Finset.range i, (P k (j + 1) - P k j) :=
    Finset.sum_nonneg fun k hk => sub_nonneg.mpr
      (P.entry_le_entry_succ_row (lt_of_lt_of_le (Finset.mem_range.mp hk) hij) (by omega))
  have hright_tele : (∑ k ∈ Finset.range (i + 1), (P k (j + 2) - P k (j + 1))) ≤
      P 0 (j + 2) - P (i + 1) (j + 2) := by
    refine (Finset.sum_le_sum fun k _ => sub_le_sub_left
      (P.entry_succ_succ_le_entry (i := k) (j := j + 1) (by omega)) _).trans_eq ?_
    exact Finset.sum_range_sub' (fun k => P k (j + 2)) (i + 1)
  have hhi : P 0 (j + 2) ≤ μ.1 0 := by
    have hmem := (P.entry_mem_Icc (i := 0) (j := j + 2) (by omega) hjn).2
    rwa [hTop] at hmem
  have hlo : μ.1 (Fin.last n) ≤ P (i + 1) (j + 2) := by
    have hmem := (P.entry_mem_Icc (i := i + 1) (j := j + 2) (by omega) hjn).1
    rw [hTop] at hmem
    simpa [Fin.last] using hmem
  have hgap := hGap ⟨j, by omega⟩
  simp only [Fin.castSucc_mk, Fin.succ_mk] at hgap
  linarith

theorem isProductHiveFeasible_of_uniform_input_gap {n : ℕ}
    (lam μ : DominantWeight (n + 1)) (P : GTPattern (n + 1))
    (hTop : P.topRow = μ.1)
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    IsProductHiveFeasible lam.1 P :=
  (isProductHiveFeasible_iff_gtCompletion lam.1 P).mpr
    (gt_completion_of_uniform_input_gap lam μ P hTop hGap)

/-- **Stable Gelfand–Tsetlin equivalence**: under the uniform input gap
`μ_0 - μ_n ≤ λ_r - λ_{r + 1}`, `toGTPattern` and `gtCompletion` establish a canonical bijection
between `FixedIntegerHive (productBoundary lam μ γ)` and the entire weight-`(γ - λ)` pattern fibre
over `μ`. -/
def stableGTPatternEquiv {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquivRight fun P =>
      and_congr_right fun hTop =>
        and_iff_left_of_imp fun _ => isProductHiveFeasible_of_uniform_input_gap lam μ P hTop hGap)

@[simp]
theorem stableGTPatternEquiv_apply_coe {n : ℕ} (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (stableGTPatternEquiv lam μ γ hGap h).1 = h.1.toGTPattern := (rfl)

@[simp]
theorem stableGTPatternEquiv_symm_apply_coe {n : ℕ} (lam μ γ : DominantWeight (n + 1))
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

theorem hiveCount_eq_card_gtPattern_of_uniform_input_gap {n : ℕ}
    (lam μ γ : DominantWeight (n + 1))
    (hGap : ∀ r : Fin n, μ.1 0 - μ.1 (Fin.last n) ≤ lam.1 r.castSucc - lam.1 r.succ) :
    hiveCount (productBoundary lam μ γ) =
      Nat.card {P : GTPattern (n + 1) // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} := by
  rw [← natCard_fixedIntegerHive]
  exact Nat.card_congr (stableGTPatternEquiv lam μ γ hGap)

/-- For `n ≤ 1`, the remaining rhombus family `j + 2 ≤ n` is empty, so `IsProductHiveFeasible` holds
unconditionally. -/
theorem isProductHiveFeasible_of_le_one {n : ℕ} (hn : n ≤ 1) (l : Fin n → ℤ) (P : GTPattern n) :
    IsProductHiveFeasible l P :=
  fun _ _ _ hjn => absurd hjn (by omega)

/-- Unconditional equivalence onto the entire Gelfand–Tsetlin weight fibre when `n ≤ 1` (covering
both `n = 0` without first/last entries and `n = 1` with empty gap condition). -/
def fixedIntegerHiveEquivGTPatternOfLeOne {n : ℕ} (hn : n ≤ 1) (lam μ γ : DominantWeight n) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      {P : GTPattern n // P.topRow = μ.1 ∧ P.rowWeight = γ.1 - lam.1} :=
  (fixedIntegerHiveEquivGTPattern lam μ γ).trans
    (Equiv.subtypeEquivRight fun P =>
      and_congr_right fun _ => and_iff_left (isProductHiveFeasible_of_le_one hn lam.1 P))

@[simp]
theorem fixedIntegerHiveEquivGTPatternOfLeOne_apply_coe {n : ℕ} (hn : n ≤ 1)
    (lam μ γ : DominantWeight n) (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (fixedIntegerHiveEquivGTPatternOfLeOne hn lam μ γ h).1 = h.1.toGTPattern := (rfl)

@[simp]
theorem fixedIntegerHiveEquivGTPatternOfLeOne_symm_apply_coe {n : ℕ} (hn : n ≤ 1)
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

/-- **Rank-`2` remaining-rhombus simplification**: for a `GL 2` pattern `P` with top row `μ` and
torus weight `γ - λ`, `IsProductHiveFeasible lam.1 P` reduces to the single inequality
`λ₁ + μ₀ ≤ γ₀` (`γ₁ ≥ λ₂ + μ₁` in `1`-indexed notation). -/
theorem isProductHiveFeasible_two_iff (lam μ γ : DominantWeight 2) (P : GTPattern 2)
    (hTop : P.topRow = μ.1) (hWeight : P.rowWeight = γ.1 - lam.1) :
    IsProductHiveFeasible lam.1 P ↔ lam.1 1 + μ.1 0 ≤ γ.1 0 := by
  have hP02 : P 0 2 = μ.1 0 := by
    simpa [GTPattern.topRow_apply] using congrFun hTop 0
  have hP01 : P 0 1 = γ.1 0 - lam.1 0 := by
    simpa [GTPattern.rowWeight_apply, GTPattern.rowSum_def] using congrFun hWeight 0
  refine ⟨fun h => ?_, fun h i j hij hjn => ?_⟩
  · have h00 := h 0 0 le_rfl le_rfl
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, add_zero,
      hP02, hP01] at h00
    change μ.1 0 - (γ.1 0 - lam.1 0) ≤ lam.1 0 - lam.1 1 at h00
    linarith
  · obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, add_zero,
      hP02, hP01]
    change μ.1 0 - (γ.1 0 - lam.1 0) ≤ lam.1 0 - lam.1 1
    linarith

/-- **Complete `GL 2` Clebsch–Gordan formula for integer hives**: `hiveCount` on
`productBoundary lam μ γ` is `1` iff degree conservation `|λ| + |μ| = |γ|` holds and
`max (λ₀ + μ₁) (λ₁ + μ₀) ≤ γ₀ ≤ λ₀ + μ₀`, and `0` otherwise. -/
theorem hiveCount_productBoundary_two (lam μ γ : DominantWeight 2) :
    hiveCount (productBoundary lam μ γ) =
      if (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
          max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧
          γ.1 0 ≤ lam.1 0 + μ.1 0
        then 1 else 0 := by
  have hiff : Nonempty (FixedIntegerHive (productBoundary lam μ γ)) ↔
      (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
        max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧
        γ.1 0 ≤ lam.1 0 + μ.1 0 := by
    rw [(fixedIntegerHiveEquivGTPattern lam μ γ).nonempty_congr]
    refine ⟨fun ⟨⟨P, hTop, hWeight, hFeas⟩⟩ => ?_, fun h => ?_⟩
    · obtain ⟨hwlo, hwhi, hwsum⟩ :=
        (GTPattern.nonempty_topRow_and_rowWeight_two_iff μ.1 (γ.1 - lam.1)).mp
          ⟨⟨P, hTop, hWeight⟩⟩
      have hrem := (isProductHiveFeasible_two_iff lam μ γ P hTop hWeight).mp hFeas
      simp only [Pi.sub_apply] at hwlo hwhi hwsum
      exact ⟨by omega, max_le (by omega) hrem, by omega⟩
    · have hlo₁ : lam.1 0 + μ.1 1 ≤ γ.1 0 := (le_max_left _ _).trans h.2.1
      have hlo₂ : lam.1 1 + μ.1 0 ≤ γ.1 0 := (le_max_right _ _).trans h.2.1
      obtain ⟨⟨P, hTop, hWeight⟩⟩ :=
        (GTPattern.nonempty_topRow_and_rowWeight_two_iff μ.1 (γ.1 - lam.1)).mpr
          (by simp only [Pi.sub_apply]; exact ⟨by omega, by omega, by omega⟩)
      exact ⟨⟨P, hTop, hWeight, (isProductHiveFeasible_two_iff lam μ γ P hTop hWeight).mpr hlo₂⟩⟩
  by_cases hc : (lam.1 0 + lam.1 1) + (μ.1 0 + μ.1 1) = γ.1 0 + γ.1 1 ∧
      max (lam.1 0 + μ.1 1) (lam.1 1 + μ.1 0) ≤ γ.1 0 ∧ γ.1 0 ≤ lam.1 0 + μ.1 0
  · rw [ite_eq_left hc]
    have hpos : 0 < hiveCount (productBoundary lam μ γ) := hiveCount_pos_iff.mpr (hiff.mpr hc)
    have hle := hiveCount_le_one_two (productBoundary lam μ γ)
    omega
  · rw [ite_eq_right hc]
    exact hiveCount_eq_zero_iff.mpr ⟨fun h => hc (hiff.mp ⟨h⟩)⟩

/-- At `n = 2` with `λ = (0, 0)` and `μ = (2, 0)`, the weight-`(1, 1)` Gelfand–Tsetlin fibre over
`μ` has cardinality `1` (`GTPattern.card_topRow_two_zero_and_rowWeight_one_one`), whereas the
remaining rhombus inequality `λ₁ + μ₀ ≤ γ₀` (`2 ≤ 1`) rejects `γ = (1, 1)`. -/
theorem hiveCount_two_zero_twoZero_oneOne :
    hiveCount
      (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![1, 1], by decide⟩) = 0 := by
  rw [hiveCount_productBoundary_two]
  decide

/-- At `n = 2` with `λ = (0, 0)` and `μ = γ = (2, 0)`, the unique highest-weight pattern survives
the remaining rhombus inequality. -/
theorem hiveCount_two_zero_twoZero_twoZero :
    hiveCount
      (productBoundary ⟨![0, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]
  decide

/-- Clebsch–Gordan multiplicity `c^{(4, 0)}_{(2, 0), (2, 0)} = 1` in the uniform-input-gap regime
`λ = μ = (2, 0)`. -/
theorem hiveCount_two_twoZero_twoZero_fourZero :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![4, 0], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]
  decide

/-- Clebsch–Gordan multiplicity `c^{(3, 1)}_{(2, 0), (2, 0)} = 1` in the uniform-input-gap regime
`λ = μ = (2, 0)`. -/
theorem hiveCount_two_twoZero_twoZero_threeOne :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![3, 1], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]
  decide

/-- Clebsch–Gordan multiplicity `c^{(2, 2)}_{(2, 0), (2, 0)} = 1` in the uniform-input-gap regime
`λ = μ = (2, 0)`. -/
theorem hiveCount_two_twoZero_twoZero_twoTwo :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![2, 0], by decide⟩ ⟨![2, 2], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_two]
  decide

/-- At `n = 3` with `λ = 0`, `μ = (1, 0, -1)`, and `γ = 0`, the zero-weight Gelfand–Tsetlin fibre
over the adjoint highest weight `(1, 0, -1)` has multiplicity `2`
(`GTPattern.card_topRow_one_zero_neg_one_and_rowWeight_zero`), whereas the remaining rhombus
inequalities exclude all patterns so `hiveCount = 0`. -/
theorem hiveCount_three_zero_adjoint_zero :
    hiveCount (productBoundary (0 : DominantWeight 3) ⟨![1, 0, -1], by decide⟩ 0) = 0 := by
  refine hiveCount_eq_zero_iff.mpr ⟨fun ⟨h, hb⟩ => ?_⟩
  have hb' : h.rotate.rotate.boundary =
      productBoundary (0 : DominantWeight 3) 0
        (DominantWeight.dual ⟨![1, 0, -1], by decide⟩) := by
    ext s r
    fin_cases s <;> simp [boundary_rotate, hb]
  have hle := first_le_of_productBoundary hb'
  simp at hle

end LowRank

end TauCeti.Hive
