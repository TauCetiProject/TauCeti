/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Combinatorics.Hive.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Fixed-boundary hive polytopes, properness, and finite integer fibres

Fixing the clockwise edge-difference boundary `B : Fin 3 → Fin n → R` of a normalized hive cuts out
a bounded slice of the hive cone. Summing unit-rhombus inequalities across any `(y, z)`-aligned
parallelogram inside `Δₙ` gives the **parallelogram inequality**
(`TauCeti.Hive.IsRhombusConcave.parallelogram_le`):

`f(y₀, z₀) + f(y₁, z₁) ≤ f(y₁, z₀) + f(y₀, z₁)` for `y₀ ≤ y₁`, `z₀ ≤ z₁`, `y₁ + z₁ ≤ n`.

Evaluating this inequality on two boundary-anchored parallelograms traps every interior entry
`h p` between explicit linear combinations `entryLowerBound h.boundary p` and
`entryUpperBound h.boundary p` of the boundary differences. Four consequences follow uniformly:

1. **Zero-boundary uniqueness** (`TauCeti.Hive.boundary_eq_zero_iff`): the only normalized hive with
   zero boundary over any partially ordered abelian group is `0`.
2. **Matrix presentations** (`TauCeti.Hive.eqMatrix`, `TauCeti.Hive.rhombusMatrix`,
   `TauCeti.Hive.mem_fixedBoundary_iff_mulVec`): over any ring `R` (in particular `ℤ`, `ℚ`, `ℝ`),
   fixed-boundary hives are the solutions of `eqMatrix R n *ᵥ f = eqRHS B` and
   `rhombusMatrix R n *ᵥ f ≤ 0`, with `eqMatrix R n` and `rhombusMatrix R n` obtained by base
   change from `ℤ`.
3. **Compact real hive polytopes and proper boundary projection** (`TauCeti.Hive.properCone`,
   `TauCeti.Hive.isConvexPolyhedron_realFibre`, `TauCeti.Hive.isCompact_realFibre`,
   `TauCeti.Hive.isProperMap_boundary_properCone`): the real hive cone is a `ProperCone` and a
   `TauCeti.IsConvexPolyhedron`, every fixed-boundary real fibre is a compact convex polyhedron, and
   the uniform estimate `‖f‖ ≤ 3 * n * ‖boundaryLinear ℝ n ℝ f‖` makes boundary projection a proper
   map onto its closed image.
4. **Finite integer fibres, `hiveCount`, and finite output support**
   (`TauCeti.Hive.FixedIntegerHive`, `TauCeti.Hive.finite_fixedIntegerHive`,
   `TauCeti.Hive.hiveCount`, `TauCeti.Hive.dominates_add_of_productBoundary`,
   `TauCeti.Hive.detShift_le_of_productBoundary`,
   `TauCeti.Hive.finite_support_hiveCount_productBoundary`): intersecting the bounding box with the
   decidable hive conditions equips `FixedIntegerHive B` with a computable `Fintype` instance, while
   central-degree conservation `|λ| + |μ| = |γ|`, the dominance bound `(λ + μ).Dominates γ`, and the
   lower-coordinate bound `λₙ + μₙ ≤ γₙ` restrict nonempty fibres for fixed `λ, μ` to finitely many
   output weights `γ`.

## Main definitions

* `TauCeti.Hive.Vertex.ofYZ`: chart `(y, z) ↦ (n - y - z, y, z)` on `Vertex n`.
* `TauCeti.Hive.entryLowerBound` and `TauCeti.Hive.entryUpperBound`: explicit linear boundary bounds
  sandwiching every hive entry.
* `TauCeti.Hive.EqConstraintIndex`, `TauCeti.Hive.eqMatrix`, `TauCeti.Hive.eqRHS`, and
  `TauCeti.Hive.rhombusMatrix`: finite equality and inequality matrices cutting out fixed-boundary
  hives over any ring.
* `TauCeti.Hive.properCone` and `TauCeti.Hive.realFibre`: the closed real hive cone and its
  fixed-boundary polytopes.
* `TauCeti.Hive.FixedIntegerHive` and `TauCeti.Hive.hiveCount`: the finite type of integer hives
  with prescribed boundary and its cardinality.

## Main results

* `TauCeti.Hive.IsRhombusConcave.parallelogram_le`: parallelogram inequality on `(y, z)` rectangles.
* `TauCeti.Hive.entryLowerBound_le`, `TauCeti.Hive.le_entryUpperBound`, and
  `TauCeti.Hive.boundary_eq_zero_iff`: two-sided boundary sandwich and zero-boundary uniqueness.
* `TauCeti.Hive.isConvexPolyhedron_realFibre`, `TauCeti.Hive.isCompact_realFibre`, and
  `TauCeti.Hive.isProperMap_boundary_properCone`: polyhedrality, compactness, and properness over
  `ℝ`.
* `TauCeti.Hive.finite_fixedIntegerHive`: finiteness of every integral fixed-boundary fibre.
* `TauCeti.Hive.dominates_add_of_productBoundary`, `TauCeti.Hive.detShift_le_of_productBoundary`,
  and `TauCeti.Hive.finite_support_hiveCount_productBoundary`: output dominance, lower-coordinate
  bound, and finiteness of output support for fixed input weights `λ, μ`.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Knutson, T. Tao, and C. Woodward, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor
  products II: puzzles determine facets of the Littlewood–Richardson cone*, J. Amer. Math. Soc.
  **17** (2004), 19–48, §5, Lemma 9.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §4, Lemma 1.
-/

public section

open scoped BigOperators Matrix

namespace TauCeti.Hive

@[elab_as_elim]
private theorem fin3_cases {P : Fin 3 → Prop} (s : Fin 3) (h0 : P 0) (h1 : P 1) (h2 : P 2) : P s :=
  match s with
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2

/-! ### `(y, z)` chart and the parallelogram inequality -/

namespace Vertex

/-- Construct a lattice vertex `(n - y - z, y, z)` from nonnegative `(y, z)` with `y + z ≤ n`. -/
def ofYZ (n : ℕ) (y z : ℕ) (h : y + z ≤ n) : Vertex n :=
  ⟨n - y - z, y, z, by omega⟩

@[simp]
theorem ofYZ_x (n y z : ℕ) (h : y + z ≤ n) : (ofYZ n y z h).x = n - y - z := (rfl)

@[simp] theorem ofYZ_y (n y z : ℕ) (h : y + z ≤ n) : (ofYZ n y z h).y = y := (rfl)

@[simp] theorem ofYZ_z (n y z : ℕ) (h : y + z ≤ n) : (ofYZ n y z h).z = z := (rfl)

@[simp]
theorem ofYZ_eq_iff {n y₁ z₁ y₂ z₂ : ℕ} {h₁ : y₁ + z₁ ≤ n} {h₂ : y₂ + z₂ ≤ n} :
    ofYZ n y₁ z₁ h₁ = ofYZ n y₂ z₂ h₂ ↔ y₁ = y₂ ∧ z₁ = z₂ := by
  constructor
  · intro h
    exact ⟨congrArg Vertex.y h, congrArg Vertex.z h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp]
theorem ofYZ_y_z {n : ℕ} (p : Vertex n) :
    ofYZ n p.y p.z (by have := p.sum_eq; omega) = p := by
  ext <;> simp
  have := p.sum_eq
  omega

@[simp]
theorem ofYZ_zero_zero (n : ℕ) : ofYZ n 0 0 (Nat.zero_le n) = cornerA n := by
  ext <;> simp

theorem ofYZ_zero_right (n y : ℕ) (hy : y ≤ n) :
    ofYZ n y 0 (by omega) = edgePoint n 0 ⟨y, by omega⟩ := by
  ext <;> simp

theorem ofYZ_zero_left (n z : ℕ) (hz : z ≤ n) :
    ofYZ n 0 z (by omega) = edgePoint n 2 ⟨n - z, by omega⟩ := by
  ext <;> simp; omega

theorem ofYZ_sub_left (n z : ℕ) (hz : z ≤ n) :
    ofYZ n (n - z) z (by omega) = edgePoint n 1 ⟨z, by omega⟩ := by
  ext <;> simp; omega

end Vertex

/-- An elementary `(y, z)`-unit cell inside `Δₙ` forms a unit rhombus with obtuse corners
`(y + 1, z)` and `(y, z + 1)` and acute corners `(y, z)` and `(y + 1, z + 1)`. -/
theorem isRhombus_ofYZ_step {n y z : ℕ} (h : (y + 1) + (z + 1) ≤ n) :
    IsRhombus (Vertex.ofYZ n (y + 1) z (by omega)) (Vertex.ofYZ n y z (by omega))
      (Vertex.ofYZ n y (z + 1) (by omega)) (Vertex.ofYZ n (y + 1) (z + 1) h) := by
  have hx00 : ((n - y - z : ℕ) : ℤ) = (n : ℤ) - y - z := by omega
  have hx10 : ((n - (y + 1) - z : ℕ) : ℤ) = (n : ℤ) - y - z - 1 := by omega
  have hx01 : ((n - y - (z + 1) : ℕ) : ℤ) = (n : ℤ) - y - z - 1 := by omega
  have hx11 : ((n - (y + 1) - (z + 1) : ℕ) : ℤ) = (n : ℤ) - y - z - 2 := by omega
  refine
    { midpoint_x := by simp; omega
      midpoint_y := by simp; omega
      midpoint_z := by simp
      short := ?_
      long := ?_
      side_ab := ?_
      side_bc := ?_
      side_cd := ?_
      side_da := ?_ }
  all_goals
    rw [Vertex.sqDist_def]
    simp only [Vertex.ofYZ_x, Vertex.ofYZ_y, Vertex.ofYZ_z, hx00, hx10, hx01, hx11, Nat.cast_add,
      Nat.cast_one]
    ring

section Parallelogram

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]

private theorem strip_parallelogram_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    (y₀ k z : ℕ) (h : (y₀ + k) + (z + 1) ≤ n) :
    f (Vertex.ofYZ n y₀ z (by omega)) + f (Vertex.ofYZ n (y₀ + k) (z + 1) h) ≤
      f (Vertex.ofYZ n (y₀ + k) z (by omega)) + f (Vertex.ofYZ n y₀ (z + 1) (by omega)) := by
  induction k with
  | zero =>
    have h0 : Vertex.ofYZ n (y₀ + 0) (z + 1) h = Vertex.ofYZ n y₀ (z + 1) (by omega) :=
      Vertex.ofYZ_eq_iff.mpr ⟨by omega, rfl⟩
    have h1 : Vertex.ofYZ n (y₀ + 0) z (by omega) = Vertex.ofYZ n y₀ z (by omega) :=
      Vertex.ofYZ_eq_iff.mpr ⟨by omega, rfl⟩
    rw [h0, h1]
  | succ m ih =>
    have hprev := ih (by omega)
    have hcell := (isRhombusConcave_def f).mp hf
      (isRhombus_ofYZ_step (n := n) (y := y₀ + m) (z := z) (by omega))
    set p00 := Vertex.ofYZ n y₀ z (by omega)
    set p01 := Vertex.ofYZ n y₀ (z + 1) (by omega)
    set pm0 := Vertex.ofYZ n (y₀ + m) z (by omega)
    set pm1 := Vertex.ofYZ n (y₀ + m) (z + 1) (by omega)
    have hs0 : Vertex.ofYZ n (y₀ + (m + 1)) z (by omega) =
        Vertex.ofYZ n (y₀ + m + 1) z (by omega) := Vertex.ofYZ_eq_iff.mpr ⟨by omega, rfl⟩
    have hs1 : Vertex.ofYZ n (y₀ + (m + 1)) (z + 1) h =
        Vertex.ofYZ n (y₀ + m + 1) (z + 1) (by omega) := Vertex.ofYZ_eq_iff.mpr ⟨by omega, rfl⟩
    rw [hs0, hs1]
    set ps0 := Vertex.ofYZ n (y₀ + m + 1) z (by omega)
    set ps1 := Vertex.ofYZ n (y₀ + m + 1) (z + 1) (by omega)
    have hsum : (f p00 + f ps1) + (f pm0 + f pm1) ≤ (f ps0 + f p01) + (f pm0 + f pm1) := by
      calc (f p00 + f ps1) + (f pm0 + f pm1)
          = (f p00 + f pm1) + (f pm0 + f ps1) := by abel
        _ ≤ (f pm0 + f p01) + (f ps0 + f pm1) := add_le_add hprev hcell
        _ = (f ps0 + f p01) + (f pm0 + f pm1) := by abel
    exact le_of_add_le_add_right hsum

private theorem rect_parallelogram_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    (y₀ y₁ z₀ l : ℕ) (hy : y₀ ≤ y₁) (h : y₁ + (z₀ + l) ≤ n) :
    f (Vertex.ofYZ n y₀ z₀ (by omega)) + f (Vertex.ofYZ n y₁ (z₀ + l) h) ≤
      f (Vertex.ofYZ n y₁ z₀ (by omega)) + f (Vertex.ofYZ n y₀ (z₀ + l) (by omega)) := by
  induction l with
  | zero =>
    have h0 : Vertex.ofYZ n y₁ (z₀ + 0) h = Vertex.ofYZ n y₁ z₀ (by omega) :=
      Vertex.ofYZ_eq_iff.mpr ⟨rfl, by omega⟩
    have h1 : Vertex.ofYZ n y₀ (z₀ + 0) (by omega) = Vertex.ofYZ n y₀ z₀ (by omega) :=
      Vertex.ofYZ_eq_iff.mpr ⟨rfl, by omega⟩
    rw [h0, h1, add_comm (f (Vertex.ofYZ n y₁ z₀ _))]
  | succ m ih =>
    have hprev := ih (by omega)
    have hy01 : y₀ + (y₁ - y₀) = y₁ := Nat.add_sub_of_le hy
    have hstrip := strip_parallelogram_le hf y₀ (y₁ - y₀) (z₀ + m) (by omega)
    have hc1 : Vertex.ofYZ n (y₀ + (y₁ - y₀)) (z₀ + m + 1) (by omega) =
        Vertex.ofYZ n y₁ (z₀ + (m + 1)) h := Vertex.ofYZ_eq_iff.mpr ⟨hy01, by omega⟩
    have hc0 : Vertex.ofYZ n (y₀ + (y₁ - y₀)) (z₀ + m) (by omega) =
        Vertex.ofYZ n y₁ (z₀ + m) (by omega) := Vertex.ofYZ_eq_iff.mpr ⟨hy01, rfl⟩
    have hc2 : Vertex.ofYZ n y₀ (z₀ + m + 1) (by omega) =
        Vertex.ofYZ n y₀ (z₀ + (m + 1)) (by omega) := Vertex.ofYZ_eq_iff.mpr ⟨rfl, by omega⟩
    rw [hc1, hc0, hc2] at hstrip
    set q00 := Vertex.ofYZ n y₀ z₀ (by omega)
    set q10 := Vertex.ofYZ n y₁ z₀ (by omega)
    set q0m := Vertex.ofYZ n y₀ (z₀ + m) (by omega)
    set q1m := Vertex.ofYZ n y₁ (z₀ + m) (by omega)
    set q0s := Vertex.ofYZ n y₀ (z₀ + (m + 1)) (by omega)
    set q1s := Vertex.ofYZ n y₁ (z₀ + (m + 1)) h
    have hsum : (f q00 + f q1s) + (f q0m + f q1m) ≤ (f q10 + f q0s) + (f q0m + f q1m) := by
      calc (f q00 + f q1s) + (f q0m + f q1m)
          = (f q00 + f q1m) + (f q0m + f q1s) := by abel
        _ ≤ (f q10 + f q0m) + (f q1m + f q0s) := add_le_add hprev hstrip
        _ = (f q10 + f q0s) + (f q0m + f q1m) := by abel
    exact le_of_add_le_add_right hsum

/-- **Parallelogram inequality** for rhombus-concave functions: summing all elementary `(y, z)`
unit rhombi inside `[y₀, y₁] × [z₀, z₁]` yields
`f(y₀, z₀) + f(y₁, z₁) ≤ f(y₁, z₀) + f(y₀, z₁)`. -/
theorem IsRhombusConcave.parallelogram_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    {y₀ y₁ z₀ z₁ : ℕ} (hy : y₀ ≤ y₁) (hz : z₀ ≤ z₁) (hsum : y₁ + z₁ ≤ n) :
    f (Vertex.ofYZ n y₀ z₀ (by omega)) + f (Vertex.ofYZ n y₁ z₁ hsum) ≤
      f (Vertex.ofYZ n y₁ z₀ (by omega)) + f (Vertex.ofYZ n y₀ z₁ (by omega)) := by
  have hz01 : z₀ + (z₁ - z₀) = z₁ := Nat.add_sub_of_le hz
  have h := rect_parallelogram_le hf y₀ y₁ z₀ (z₁ - z₀) hy (by omega)
  have h1 : Vertex.ofYZ n y₁ (z₀ + (z₁ - z₀)) (by omega) = Vertex.ofYZ n y₁ z₁ hsum :=
    Vertex.ofYZ_eq_iff.mpr ⟨rfl, hz01⟩
  have h2 : Vertex.ofYZ n y₀ (z₀ + (z₁ - z₀)) (by omega) = Vertex.ofYZ n y₀ z₁ (by omega) :=
    Vertex.ofYZ_eq_iff.mpr ⟨rfl, hz01⟩
  rw [h1, h2] at h
  exact h

/-- Parallelogram inequality specialized to a normalized `Hive`. -/
theorem parallelogram_le (h : Hive n R) {y₀ y₁ z₀ z₁ : ℕ} (hy : y₀ ≤ y₁) (hz : z₀ ≤ z₁)
    (hsum : y₁ + z₁ ≤ n) :
    h (Vertex.ofYZ n y₀ z₀ (by omega)) + h (Vertex.ofYZ n y₁ z₁ hsum) ≤
      h (Vertex.ofYZ n y₁ z₀ (by omega)) + h (Vertex.ofYZ n y₀ z₁ (by omega)) :=
  h.isRhombusConcave.parallelogram_le hy hz hsum

/-! ### Explicit two-sided entry bounds and zero-boundary uniqueness -/

/-- Explicit linear lower bound on the entry at `p` of any normalized hive with boundary `B`,
obtained from the parallelogram `[p.y, n - p.z] × [0, p.z]`. -/
def entryLowerBound {n : ℕ} {R : Type*} [AddCommGroup R] (B : Fin 3 → Fin n → R)
    (p : Vertex n) : R :=
  (∑ i : Fin n with i.val < p.y, B 0 i) +
    (∑ i : Fin n with n - p.z ≤ i.val, B 0 i) +
    ∑ i : Fin n with i.val < p.z, B 1 i

/-- Explicit linear upper bound on the entry at `p` of any normalized hive with boundary `B`,
obtained from the parallelogram `[0, p.y] × [0, p.z]`. -/
def entryUpperBound {n : ℕ} {R : Type*} [AddCommGroup R] (B : Fin 3 → Fin n → R)
    (p : Vertex n) : R :=
  (∑ i : Fin n with i.val < p.y, B 0 i) - ∑ i : Fin n with n - p.z ≤ i.val, B 2 i

@[simp]
theorem entryLowerBound_zero {n : ℕ} {R : Type*} [AddCommGroup R] (p : Vertex n) :
    entryLowerBound (0 : Fin 3 → Fin n → R) p = 0 := by
  simp [entryLowerBound]

@[simp]
theorem entryUpperBound_zero {n : ℕ} {R : Type*} [AddCommGroup R] (p : Vertex n) :
    entryUpperBound (0 : Fin 3 → Fin n → R) p = 0 := by
  simp [entryUpperBound]

/-- Every entry `h p` of a normalized hive is bounded below by `entryLowerBound h.boundary p`. -/
theorem entryLowerBound_le (h : Hive n R) (p : Vertex n) :
    entryLowerBound h.boundary p ≤ h p := by
  have hp := p.sum_eq
  have hpar := h.parallelogram_le (y₀ := p.y) (y₁ := n - p.z) (z₀ := 0) (z₁ := p.z)
    (by omega) (Nat.zero_le p.z) (by omega)
  rw [Vertex.ofYZ_y_z p, Vertex.ofYZ_zero_right n p.y (by omega),
    Vertex.ofYZ_sub_left n p.z (by omega), Vertex.ofYZ_zero_right n (n - p.z) (by omega),
    h.apply_edgePoint_zero, h.apply_edgePoint_one, h.apply_edgePoint_zero] at hpar
  have hcompl :
      (∑ i : Fin n with i.val < n - p.z, h.boundary 0 i) +
        (∑ i : Fin n with n - p.z ≤ i.val, h.boundary 0 i) =
      ∑ i : Fin n, h.boundary 0 i := by
    simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < n - p.z) (h.boundary 0)
  set s_py := ∑ i : Fin n with i.val < p.y, h.boundary 0 i
  set s_lt := ∑ i : Fin n with i.val < n - p.z, h.boundary 0 i
  set s_ge := ∑ i : Fin n with n - p.z ≤ i.val, h.boundary 0 i
  set s_pz := ∑ i : Fin n with i.val < p.z, h.boundary 1 i
  change s_py + ((∑ i : Fin n, h.boundary 0 i) + s_pz) ≤ s_lt + h p at hpar
  rw [← hcompl] at hpar
  have hcancel : (s_py + s_ge + s_pz) + s_lt ≤ h p + s_lt := by
    calc (s_py + s_ge + s_pz) + s_lt = s_py + ((s_lt + s_ge) + s_pz) := by abel
      _ ≤ s_lt + h p := hpar
      _ = h p + s_lt := add_comm _ _
  exact le_of_add_le_add_right hcancel

/-- Every entry `h p` of a normalized hive is bounded above by `entryUpperBound h.boundary p`. -/
theorem le_entryUpperBound (h : Hive n R) (p : Vertex n) :
    h p ≤ entryUpperBound h.boundary p := by
  have hp := p.sum_eq
  have hpar := h.parallelogram_le (y₀ := 0) (y₁ := p.y) (z₀ := 0) (z₁ := p.z)
    (Nat.zero_le p.y) (Nat.zero_le p.z) (by omega)
  rw [Vertex.ofYZ_zero_zero, h.apply_cornerA, zero_add, Vertex.ofYZ_y_z p,
    Vertex.ofYZ_zero_right n p.y (by omega), Vertex.ofYZ_zero_left n p.z (by omega),
    h.apply_edgePoint_zero, h.apply_edgePoint_two, ← sub_eq_add_neg] at hpar
  exact hpar

/-- **Zero-boundary uniqueness**: a normalized hive with values in a partially ordered abelian
group has zero boundary if and only if it is the zero hive. -/
@[simp]
theorem boundary_eq_zero_iff (h : Hive n R) : h.boundary = 0 ↔ h = 0 := by
  refine ⟨fun hb => ?_, fun h0 => by rw [h0, boundary_zero]⟩
  ext p
  have hlo := entryLowerBound_le h p
  have hhi := le_entryUpperBound h p
  rw [hb, entryLowerBound_zero] at hlo
  rw [hb, entryUpperBound_zero] at hhi
  exact le_antisymm hhi hlo

end Parallelogram

/-! ### Equality and inequality matrix presentations over rings -/

section MatrixPresentation

/-- Row index type for the linear equality constraints of a fixed-boundary hive: `Sum.inl ()`
normalizes `f(A) = 0`, while `Sum.inr (s, i)` prescribes `boundaryLinear f s i = B s i`. -/
abbrev EqConstraintIndex (n : ℕ) : Type :=
  Unit ⊕ (Fin 3 × Fin n)

/-- Equality constraint matrix over a ring `R` for normalized hives of size `n` with prescribed
boundary. -/
def eqMatrix (R : Type*) [Ring R] (n : ℕ) : Matrix (EqConstraintIndex n) (Vertex n) R
  | Sum.inl () => Pi.single (Vertex.cornerA n) 1
  | Sum.inr (s, i) =>
      Pi.single (Vertex.edgePoint n s i.succ) 1 - Pi.single (Vertex.edgePoint n s i.castSucc) 1

/-- Right-hand side vector `(0, B)` paired with `eqMatrix R n`. -/
def eqRHS {R : Type*} [Zero R] {n : ℕ} (B : Fin 3 → Fin n → R) : EqConstraintIndex n → R
  | Sum.inl () => 0
  | Sum.inr (s, i) => B s i

/-- Inequality constraint matrix over `R` whose rows encode `f b + f d - (f a + f c) ≤ 0` on each
unit rhombus `r : Rhombus n`. -/
def rhombusMatrix (R : Type*) [Ring R] (n : ℕ) : Matrix (Rhombus n) (Vertex n) R :=
  fun r => Pi.single r.1.2.1 1 + Pi.single r.1.2.2.2 1 -
    (Pi.single r.1.1 1 + Pi.single r.1.2.2.1 1)

private theorem sum_single_one_mul {n : ℕ} {R : Type*} [Ring R] (p : Vertex n)
    (f : Vertex n → R) :
    (∑ q : Vertex n, (Pi.single p (1 : R) : Vertex n → R) q * f q) = f p := by
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp [Pi.single_eq_of_ne hqp]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

@[simp]
theorem eqMatrix_mulVec_inl {n : ℕ} {R : Type*} [Ring R] (f : Vertex n → R) :
    (eqMatrix R n *ᵥ f) (Sum.inl ()) = f (Vertex.cornerA n) := by
  simpa [Matrix.mulVec_apply_eq_sum, eqMatrix] using sum_single_one_mul (Vertex.cornerA n) f

@[simp]
theorem eqMatrix_mulVec_inr {n : ℕ} {R : Type*} [Ring R] (f : Vertex n → R)
    (s : Fin 3) (i : Fin n) :
    (eqMatrix R n *ᵥ f) (Sum.inr (s, i)) = boundaryLinear ℤ n R f s i := by
  simp only [Matrix.mulVec_apply_eq_sum, eqMatrix, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
    sum_single_one_mul, boundaryLinear_apply]

@[simp]
theorem rhombusMatrix_mulVec_apply {n : ℕ} {R : Type*} [Ring R] (f : Vertex n → R)
    (r : Rhombus n) :
    (rhombusMatrix R n *ᵥ f) r = -rhombusSlack f r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 := by
  simp only [Matrix.mulVec_apply_eq_sum, rhombusMatrix, Pi.sub_apply, Pi.add_apply, sub_mul,
    add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_single_one_mul, rhombusSlack_def]
  abel

/-- Over any ring `R` (in particular `ℚ` and `ℝ`), `eqMatrix R n` is the base change of the integer
matrix `eqMatrix ℤ n`. -/
@[simp]
theorem map_intCast_eqMatrix (R : Type*) [Ring R] (n : ℕ) :
    (eqMatrix ℤ n).map (Int.cast : ℤ → R) = eqMatrix R n := by
  ext idx q
  rcases idx with ⟨⟨⟩⟩ | ⟨s, i⟩
  · simp [eqMatrix, Pi.single_apply]
  · simp [eqMatrix, Pi.single_apply]

/-- Over any ring `R` (in particular `ℚ` and `ℝ`), `rhombusMatrix R n` is the base change of the
integer matrix `rhombusMatrix ℤ n`. -/
@[simp]
theorem map_intCast_rhombusMatrix (R : Type*) [Ring R] (n : ℕ) :
    (rhombusMatrix ℤ n).map (Int.cast : ℤ → R) = rhombusMatrix R n := by
  ext r q
  simp [rhombusMatrix, Pi.single_apply]

/-- Matrix characterization of fixed-boundary normalized hives over any partially ordered ring
(covering `ℤ`, `ℚ`, and `ℝ` uniformly). -/
theorem mem_fixedBoundary_iff_mulVec {n : ℕ} {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] (B : Fin 3 → Fin n → R) (f : Vertex n → R) :
    (f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f ∧ boundaryLinear ℤ n R f = B) ↔
      eqMatrix R n *ᵥ f = eqRHS B ∧ rhombusMatrix R n *ᵥ f ≤ 0 := by
  constructor
  · rintro ⟨hA, hconc, hB⟩
    refine ⟨?_, fun r => ?_⟩
    · ext idx
      rcases idx with ⟨⟨⟩⟩ | ⟨s, i⟩
      · simp [eqRHS, hA]
      · simp [eqRHS, ← hB]
    · rw [Pi.zero_apply, rhombusMatrix_mulVec_apply, neg_nonpos, rhombusSlack_def]
      exact sub_nonneg.mpr ((isRhombusConcave_def f).mp hconc r.2)
  · rintro ⟨heq, hineq⟩
    refine ⟨?_, (isRhombusConcave_def f).mpr fun a b c d hr => ?_, ?_⟩
    · have h := congrFun heq (Sum.inl ())
      simpa [eqRHS] using h
    · have h := hineq ⟨(a, b, c, d), hr⟩
      rw [Pi.zero_apply, rhombusMatrix_mulVec_apply, neg_nonpos, rhombusSlack_def] at h
      exact sub_nonneg.mp h
    · ext s i
      have h := congrFun heq (Sum.inr (s, i))
      simpa [eqRHS] using h

end MatrixPresentation

/-! ### Real polyhedral cone, compact fixed-boundary polytopes, and properness -/

section RealPolyhedron

private def evalCLM {n : ℕ} (p : Vertex n) : (Vertex n → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj p

@[simp]
private theorem evalCLM_apply {n : ℕ} (p : Vertex n) (f : Vertex n → ℝ) :
    evalCLM p f = f p := (rfl)

/-- The pointed cone of normalized real hives is a `TauCeti.IsConvexPolyhedron`. -/
theorem isConvexPolyhedron_pointedCone (n : ℕ) :
    IsConvexPolyhedron (pointedCone ℝ n : Set (Vertex n → ℝ)) := by
  let g : Bool ⊕ Rhombus n → ((Vertex n → ℝ) →ᴬ[ℝ] ℝ)
    | Sum.inl true => (evalCLM (Vertex.cornerA n)).toContinuousAffineMap
    | Sum.inl false => (-evalCLM (Vertex.cornerA n)).toContinuousAffineMap
    | Sum.inr r =>
        (evalCLM r.1.2.1 + evalCLM r.1.2.2.2 -
          (evalCLM r.1.1 + evalCLM r.1.2.2.1)).toContinuousAffineMap
  have heq : (pointedCone ℝ n : Set (Vertex n → ℝ)) = {f | ∀ i, g i f ≤ 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_pointedCone_iff, Set.mem_ofPred_eq, Sum.forall,
      Bool.forall_bool]
    constructor
    · rintro ⟨hA, hconc⟩
      refine ⟨⟨by simp [g, hA], by simp [g, hA]⟩, fun r => ?_⟩
      simpa [g, sub_nonpos] using (isRhombusConcave_def f).mp hconc r.2
    · rintro ⟨⟨hneg, hpos⟩, hr⟩
      have hA : f (Vertex.cornerA n) = 0 :=
        le_antisymm (by simpa [g] using hpos) (by simpa [g] using hneg)
      refine ⟨hA, (isRhombusConcave_def f).mpr fun a b c d hrh => ?_⟩
      simpa [g, sub_nonpos] using hr ⟨(a, b, c, d), hrh⟩
  rw [heq]
  exact isConvexPolyhedron_setOf_forall g

/-- The closed convex cone of normalized real hives packaged as a `ProperCone`. -/
def properCone (n : ℕ) : ProperCone ℝ (Vertex n → ℝ) where
  toSubmodule := pointedCone ℝ n
  isClosed' := (isConvexPolyhedron_pointedCone n).isClosed

@[simp]
theorem mem_properCone_iff {n : ℕ} {f : Vertex n → ℝ} :
    f ∈ properCone n ↔ f ∈ pointedCone ℝ n :=
  Iff.rfl

@[simp]
theorem coe_properCone (n : ℕ) :
    (properCone n : Set (Vertex n → ℝ)) = (pointedCone ℝ n : Set (Vertex n → ℝ)) := (rfl)

/-- The real fixed-boundary hive polytope inside `Vertex n → ℝ`. -/
def realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) : Set (Vertex n → ℝ) :=
  {f ∈ pointedCone ℝ n | boundaryLinear ℝ n ℝ f = B}

theorem mem_realFibre_iff {n : ℕ} {B : Fin 3 → Fin n → ℝ} {f : Vertex n → ℝ} :
    f ∈ realFibre B ↔ ∃ h : RealHive n, ⇑h = f ∧ h.boundary = B := by
  simp only [realFibre, Set.mem_ofPred_eq, mem_pointedCone_iff]
  constructor
  · rintro ⟨⟨hA, hconc⟩, hB⟩
    let h : RealHive n := ⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩
    have hcoe : ⇑h = f := coe_mk f hA _
    refine ⟨h, hcoe, ?_⟩
    rw [← boundaryLinear_coe ℝ h, hcoe, hB]
  · rintro ⟨h, rfl, hB⟩
    exact ⟨⟨h.apply_cornerA, h.isRhombusConcave⟩, (boundaryLinear_coe ℝ h).trans hB⟩

/-- Every real fixed-boundary hive fibre is a `TauCeti.IsConvexPolyhedron`. -/
theorem isConvexPolyhedron_realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) :
    IsConvexPolyhedron (realFibre B) := by
  let edgeDiff (s : Fin 3) (i : Fin n) : (Vertex n → ℝ) →ᴬ[ℝ] ℝ :=
    (evalCLM (Vertex.edgePoint n s i.succ) -
      evalCLM (Vertex.edgePoint n s i.castSucc)).toContinuousAffineMap
  let g : Bool × Fin 3 × Fin n → ((Vertex n → ℝ) →ᴬ[ℝ] ℝ)
    | (true, s, i) => edgeDiff s i - ContinuousAffineMap.const ℝ (Vertex n → ℝ) (B s i)
    | (false, s, i) => ContinuousAffineMap.const ℝ (Vertex n → ℝ) (B s i) - edgeDiff s i
  have heq : realFibre B =
      (pointedCone ℝ n : Set (Vertex n → ℝ)) ∩ {f | ∀ p, g p f ≤ 0} := by
    ext f
    simp only [realFibre, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Prod.forall,
      Bool.forall_bool]
    refine and_congr_right fun _ => ⟨fun hB => ⟨fun s i => ?_, fun s i => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
    · have hs : boundaryLinear ℝ n ℝ f s i = B s i := by rw [hB]
      simp [g, edgeDiff, ← hs]
    · have hs : boundaryLinear ℝ n ℝ f s i = B s i := by rw [hB]
      simp [g, edgeDiff, ← hs]
    · ext s i
      have hle : boundaryLinear ℝ n ℝ f s i ≤ B s i := by
        simpa [g, edgeDiff, sub_nonpos] using h2 s i
      have hge : B s i ≤ boundaryLinear ℝ n ℝ f s i := by
        simpa [g, edgeDiff, sub_nonpos] using h1 s i
      exact le_antisymm hle hge
  rw [heq]
  exact (isConvexPolyhedron_pointedCone n).inter (isConvexPolyhedron_setOf_forall g)

private theorem norm_sum_filter_boundary_le {n : ℕ} (B : Fin 3 → Fin n → ℝ) (s : Fin 3)
    (S : Finset (Fin n)) :
    ‖∑ i ∈ S, B s i‖ ≤ n * ‖B‖ := by
  have hcoord : ∀ i ∈ S, ‖B s i‖ ≤ ‖B‖ := fun i _ =>
    (norm_le_pi_norm (B s) i).trans (norm_le_pi_norm B s)
  have hcard : (S.card : ℝ) ≤ n := by
    exact_mod_cast (S.card_le_univ.trans_eq (Fintype.card_fin n))
  calc ‖∑ i ∈ S, B s i‖
      ≤ ∑ i ∈ S, ‖B s i‖ := norm_sum_le S (B s)
    _ ≤ ∑ _i ∈ S, ‖B‖ := Finset.sum_le_sum hcoord
    _ = S.card * ‖B‖ := by simp
    _ ≤ n * ‖B‖ := mul_le_mul_of_nonneg_right hcard (norm_nonneg B)

/-- Uniform linear norm bound on the real hive cone: every `f ∈ pointedCone ℝ n` satisfies
`‖f‖ ≤ 3 * n * ‖boundaryLinear ℝ n ℝ f‖`. -/
theorem norm_le_three_mul_norm_boundary {n : ℕ} {f : Vertex n → ℝ} (hf : f ∈ pointedCone ℝ n) :
    ‖f‖ ≤ 3 * n * ‖boundaryLinear ℝ n ℝ f‖ := by
  set B := boundaryLinear ℝ n ℝ f
  have hnonneg : 0 ≤ 3 * (n : ℝ) * ‖B‖ := by positivity
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro p
  obtain ⟨hA, hconc⟩ := mem_pointedCone_iff.mp hf
  let h : RealHive n := ⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩
  have hcoe : ⇑h = f := coe_mk f hA _
  have hB_eq : h.boundary = B := by rw [← boundaryLinear_coe ℝ h, hcoe]
  have hlo : entryLowerBound B p ≤ f p := by
    simpa [hB_eq, hcoe] using entryLowerBound_le h p
  have hhi : f p ≤ entryUpperBound B p := by
    simpa [hB_eq, hcoe] using le_entryUpperBound h p
  have hlo_norm : ‖entryLowerBound B p‖ ≤ 3 * n * ‖B‖ := by
    unfold entryLowerBound
    have h1 := norm_sum_filter_boundary_le B 0 ({i : Fin n | i.val < p.y})
    have h2 := norm_sum_filter_boundary_le B 0 ({i : Fin n | n - p.z ≤ i.val})
    have h3 := norm_sum_filter_boundary_le B 1 ({i : Fin n | i.val < p.z})
    have htri := (norm_add_le
      ((∑ i : Fin n with i.val < p.y, B 0 i) + ∑ i : Fin n with n - p.z ≤ i.val, B 0 i)
      (∑ i : Fin n with i.val < p.z, B 1 i)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    linarith
  have hhi_norm : ‖entryUpperBound B p‖ ≤ 3 * n * ‖B‖ := by
    unfold entryUpperBound
    have h1 := norm_sum_filter_boundary_le B 0 ({i : Fin n | i.val < p.y})
    have h2 := norm_sum_filter_boundary_le B 2 ({i : Fin n | n - p.z ≤ i.val})
    have htri := norm_sub_le (∑ i : Fin n with i.val < p.y, B 0 i)
      (∑ i : Fin n with n - p.z ≤ i.val, B 2 i)
    have hB : 0 ≤ (n : ℝ) * ‖B‖ := mul_nonneg (Nat.cast_nonneg n) (norm_nonneg B)
    linarith
  rw [Real.norm_eq_abs] at hlo_norm hhi_norm ⊢
  rw [abs_le]
  have habs_lo := neg_le_of_abs_le hlo_norm
  have habs_hi := le_of_abs_le hhi_norm
  exact ⟨by linarith [le_abs_self (-entryLowerBound B p), abs_neg (entryLowerBound B p)],
    by linarith⟩

/-- Every real fixed-boundary hive fibre is bounded in `Vertex n → ℝ`. -/
theorem isBounded_realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) :
    Bornology.IsBounded (realFibre B) :=
  isBounded_iff_forall_norm_le.mpr ⟨3 * n * ‖B‖, fun _ hf => by
    simpa [hf.2] using norm_le_three_mul_norm_boundary hf.1⟩

/-- **Every real fixed-boundary hive fibre is compact.** -/
theorem isCompact_realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) :
    IsCompact (realFibre B) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨(isConvexPolyhedron_realFibre B).isClosed, isBounded_realFibre B⟩

theorem continuous_boundaryLinear (n : ℕ) :
    Continuous (boundaryLinear ℝ n ℝ) := by
  refine continuous_pi fun s => continuous_pi fun i => ?_
  simp only [boundaryLinear_apply]
  exact (continuous_apply (Vertex.edgePoint n s i.succ)).sub
    (continuous_apply (Vertex.edgePoint n s i.castSucc))

/-- **Boundary projection on the closed real hive cone is a proper map.** -/
theorem isProperMap_boundary_properCone (n : ℕ) :
    IsProperMap (fun f : properCone n => boundaryLinear ℝ n ℝ f.1) := by
  have hcont : Continuous (fun f : properCone n => boundaryLinear ℝ n ℝ f.1) :=
    (continuous_boundaryLinear n).comp continuous_subtype_val
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let S : Set (Vertex n → ℝ) :=
    (properCone n : Set (Vertex n → ℝ)) ∩ boundaryLinear ℝ n ℝ ⁻¹' K
  have hS_closed : IsClosed S :=
    (properCone n).isClosed.inter (hK.isClosed.preimage (continuous_boundaryLinear n))
  have hS_bounded : Bornology.IsBounded S := by
    refine isBounded_iff_forall_norm_le.mpr ⟨3 * n * max C 0, fun f hf => ?_⟩
    have hB : ‖boundaryLinear ℝ n ℝ f‖ ≤ max C 0 := (hC _ hf.2).trans (le_max_left C 0)
    exact (norm_le_three_mul_norm_boundary hf.1).trans
      (mul_le_mul_of_nonneg_left hB (by positivity))
  have hS_compact : IsCompact S :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hS_closed, hS_bounded⟩
  have hpre : ((fun f : properCone n => boundaryLinear ℝ n ℝ f.1) ⁻¹' K) = Subtype.val ⁻¹' S := by
    ext f
    simp only [Set.mem_preimage, S, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h => ⟨f.2, h⟩, fun h => h.2⟩
  rw [hpre]
  exact (properCone n).isClosed.isProperMap_subtypeVal.isCompact_preimage hS_compact

/-- The image of the real hive cone under boundary projection is closed in `Fin 3 → Fin n → ℝ`. -/
theorem isClosed_range_boundary_properCone (n : ℕ) :
    IsClosed (Set.range fun f : properCone n => boundaryLinear ℝ n ℝ f.1) :=
  (isProperMap_boundary_properCone n).isClosed_range

end RealPolyhedron

/-! ### Finite integer fibres, `hiveCount`, output bounds, and finite output support -/

section IntegerFibre

/-- The integer hives of size `n` with prescribed clockwise cyclic boundary `B`. -/
abbrev FixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) : Type :=
  {h : IntegerHive n // h.boundary = B}

/-- Explicit coordinate bounding-box `Finset` containing the underlying function of every integer
hive with boundary `B`. -/
def fixedIntegerHiveBox {n : ℕ} (B : Fin 3 → Fin n → ℤ) : Finset (Vertex n → ℤ) :=
  (Fintype.piFinset fun p => Finset.Icc (entryLowerBound B p) (entryUpperBound B p)).filter
    fun f => f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f ∧ boundaryLinear ℤ n ℤ f = B

@[simp]
theorem mem_fixedIntegerHiveBox_iff {n : ℕ} {B : Fin 3 → Fin n → ℤ} {f : Vertex n → ℤ} :
    f ∈ fixedIntegerHiveBox B ↔
      f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f ∧ boundaryLinear ℤ n ℤ f = B := by
  simp only [fixedIntegerHiveBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
    and_iff_right_iff_imp]
  rintro ⟨hA, hconc, hB⟩ p
  let h : IntegerHive n := ⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩
  have hcoe : ⇑h = f := coe_mk f hA _
  have hb : h.boundary = B := by rw [← boundaryLinear_coe ℤ h, hcoe, hB]
  exact ⟨by simpa [hb, hcoe] using entryLowerBound_le h p,
    by simpa [hb, hcoe] using le_entryUpperBound h p⟩

/-- Computable equivalence between `FixedIntegerHive B` and `fixedIntegerHiveBox B`. -/
def fixedIntegerHiveEquivBox {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    FixedIntegerHive B ≃ ↥(fixedIntegerHiveBox B) where
  toFun h :=
    ⟨h.1, mem_fixedIntegerHiveBox_iff.mpr
      ⟨h.1.apply_cornerA, h.1.isRhombusConcave, (boundaryLinear_coe ℤ h.1).trans h.2⟩⟩
  invFun f :=
    let hf := mem_fixedIntegerHiveBox_iff.mp f.2
    let h : IntegerHive n := ⟨f.1, hf.1, fun hr => (isRhombusConcave_def f.1).mp hf.2.1 hr⟩
    ⟨h, by rw [← boundaryLinear_coe ℤ h, coe_mk f.1 hf.1 _, hf.2.2]⟩
  left_inv h := by ext p; rfl
  right_inv f := by ext p; rfl

/-- Computable `Fintype` instance on `FixedIntegerHive B` from bounding-box enumeration. -/
instance instFintypeFixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    Fintype (FixedIntegerHive B) :=
  Fintype.ofEquiv ↥(fixedIntegerHiveBox B) (fixedIntegerHiveEquivBox B).symm

/-- **Every fixed-boundary fibre of integer hives is finite.** -/
theorem finite_fixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    Finite (FixedIntegerHive B) :=
  inferInstance

/-- The number of normalized integer hives with clockwise cyclic boundary `B`. -/
def hiveCount {n : ℕ} (B : Fin 3 → Fin n → ℤ) : ℕ :=
  Fintype.card (FixedIntegerHive B)

@[simp]
theorem card_fixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    Fintype.card (FixedIntegerHive B) = hiveCount B :=
  (rfl)

theorem natCard_fixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    Nat.card (FixedIntegerHive B) = hiveCount B :=
  Nat.card_eq_fintype_card

theorem hiveCount_eq_card_box {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    hiveCount B = (fixedIntegerHiveBox B).card := by
  rw [hiveCount, Fintype.card_congr (fixedIntegerHiveEquivBox B), Fintype.card_coe]

theorem hiveCount_pos_iff {n : ℕ} {B : Fin 3 → Fin n → ℤ} :
    0 < hiveCount B ↔ Nonempty (FixedIntegerHive B) :=
  Fintype.card_pos_iff

theorem hiveCount_eq_zero_iff {n : ℕ} {B : Fin 3 → Fin n → ℤ} :
    hiveCount B = 0 ↔ IsEmpty (FixedIntegerHive B) :=
  Fintype.card_eq_zero_iff

/-- Any boundary with nonzero cyclic trace has zero integer hives. -/
theorem hiveCount_eq_zero_of_sum_ne_zero {n : ℕ} {B : Fin 3 → Fin n → ℤ}
    (hsum : (∑ s : Fin 3, ∑ i : Fin n, B s i) ≠ 0) :
    hiveCount B = 0 := by
  rw [hiveCount_eq_zero_iff]
  exact ⟨fun ⟨h, hb⟩ => hsum (hb ▸ h.sum_boundary)⟩

/-- The zero boundary admits the unique normalized integer hive `0`. -/
instance uniqueFixedIntegerHiveZero (n : ℕ) :
    Unique (FixedIntegerHive (0 : Fin 3 → Fin n → ℤ)) where
  default := ⟨0, boundary_zero⟩
  uniq h := Subtype.ext ((boundary_eq_zero_iff h.1).mp h.2)

@[simp]
theorem hiveCount_zero (n : ℕ) : hiveCount (0 : Fin 3 → Fin n → ℤ) = 1 :=
  Fintype.card_unique

/-- At rank `0`, the unique empty boundary has a single normalized integer hive. -/
@[simp]
theorem hiveCount_rank_zero (B : Fin 3 → Fin 0 → ℤ) : hiveCount B = 1 := by
  have hB : B = 0 := Subsingleton.elim B 0
  rw [hB, hiveCount_zero]

/-- Clockwise rotation of the boundary preserves `hiveCount`. -/
@[simp]
theorem hiveCount_rotate {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    hiveCount (fun s => B (s + 1)) = hiveCount B := by
  refine Fintype.card_congr
    { toFun := fun h => ⟨h.1.rotate.rotate, by
        ext s i
        have hs : s + 1 + 1 + 1 = s := by fin_cases s <;> decide
        rw [boundary_rotate, boundary_rotate, h.2]
        dsimp only
        rw [hs]⟩
      invFun := fun h => ⟨h.1.rotate, by ext s i; simp [h.2]⟩
      left_inv := fun h => by ext p; simp
      right_inv := fun h => by ext p; simp }

/-- Reflection of the boundary preserves `hiveCount`. -/
@[simp]
theorem hiveCount_reflect {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    hiveCount (fun s i => -B s.rev i.rev) = hiveCount B := by
  refine Fintype.card_congr
    { toFun := fun h => ⟨h.1.reflect, by ext s i; simp [h.2]⟩
      invFun := fun h => ⟨h.1.reflect, by ext s i; simp [h.2]⟩
      left_inv := fun h => by ext p; simp
      right_inv := fun h => by ext p; simp }

/-- Contragredient duality symmetry of tensor-product hive counts:
`hiveCount (μ*, λ*, γ**) = hiveCount (λ, μ, γ*)`. -/
theorem hiveCount_productBoundary_dual {n : ℕ} (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary μ.dual lam.dual γ.dual) =
      hiveCount (productBoundary lam μ γ) := by
  have hdual_pb :
      productBoundary lam.dual.dual μ.dual.dual γ.dual.dual = productBoundary lam μ γ := by
    ext s i
    induction s using fin3_cases <;> simp
  refine Fintype.card_congr
    { toFun := fun h =>
        ⟨h.1.reflect.rotate, (boundary_reflect_rotate_of_productBoundary h.2).trans hdual_pb⟩
      invFun := fun h => ⟨h.1.reflect.rotate, boundary_reflect_rotate_of_productBoundary h.2⟩
      left_inv := fun h => by ext p; simp
      right_inv := fun h => by ext p; simp }

/-! ### Central-degree conservation, dominance bound, lower-coordinate bound, and finite support -/

/-- **Central-degree conservation**: if an integer hive has boundary `productBoundary lam μ γ`,
then `|λ| + |μ| = |γ|`. -/
theorem sum_eq_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) :
    (∑ i, lam.1 i) + (∑ i, μ.1 i) = ∑ i, γ.1 i :=
  (sum_productBoundary_eq_zero_iff lam μ γ).mp (hb ▸ h.sum_boundary)

/-- Suffix-sum inequality for `productBoundary lam μ γ`: for every `k ≤ n`, the sum of the last
`n - k` coordinates of `γ` is at least the sum of the last `n - k` coordinates of `λ` and `μ`. -/
theorem suffix_sum_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) {k : ℕ} (hk : k ≤ n) :
    (∑ i : Fin n with k ≤ i.val, lam.1 i) + (∑ i : Fin n with k ≤ i.val, μ.1 i) ≤
      ∑ i : Fin n with k ≤ i.val, γ.1 i := by
  let p : Vertex n := Vertex.edgePoint n 1 ⟨n - k, by omega⟩
  have hp_y : p.y = k := by simp [p]; omega
  have hp_z : n - p.z = k := by simp [p]; omega
  have hup := le_entryUpperBound h.rotate p
  rw [apply_edgePoint_one] at hup
  unfold entryUpperBound at hup
  rw [hp_y, hp_z] at hup
  have h01 : (0 : Fin 3) + 1 = 1 := by decide
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have h21 : (2 : Fin 3) + 1 = 0 := by decide
  have hb0 : h.rotate.boundary 0 = μ.1 := by rw [boundary_rotate, hb, h01, productBoundary_one]
  have hb1 : h.rotate.boundary 1 = γ.dual.1 := by
    rw [boundary_rotate, hb, h11, productBoundary_two]
  have hb2 : h.rotate.boundary 2 = lam.1 := by rw [boundary_rotate, hb, h21, productBoundary_zero]
  rw [hb0, hb1, hb2] at hup
  have hdual :
      (∑ i : Fin n with i.val < n - k, γ.dual.1 i) =
        -∑ j : Fin n with k ≤ j.val, γ.1 j := by
    simp only [DominantWeight.dual_apply, Finset.sum_neg_distrib, neg_inj, Finset.sum_filter]
    have hcomp := Equiv.sum_comp Fin.revPerm (fun j : Fin n => if k ≤ j.val then γ.1 j else 0)
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hcomp
    simp only [Fin.revPerm_apply, Fin.val_rev]
    by_cases hi : i.val < n - k
    · have hj : k ≤ n - (i.val + 1) := by omega
      simp [hi, hj]
    · have hj : ¬ k ≤ n - (i.val + 1) := by omega
      simp [hi, hj]
  have hcompl_mu :
      (∑ i : Fin n with i.val < k, μ.1 i) + (∑ i : Fin n with k ≤ i.val, μ.1 i) =
        ∑ i : Fin n, μ.1 i := by
    simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < k) μ.1
  change (∑ i : Fin n, μ.1 i) + (∑ i : Fin n with i.val < n - k, γ.dual.1 i) ≤
    (∑ i : Fin n with i.val < k, μ.1 i) - (∑ i : Fin n with k ≤ i.val, lam.1 i) at hup
  rw [hdual, ← hcompl_mu] at hup
  linarith

/-- **Dominance prefix-sum bound**: if an integer hive has boundary `productBoundary lam μ γ`, then
every leading partial sum of `γ` is at most that of `λ + μ`. -/
theorem prefix_sum_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (k : ℕ) :
    (∑ i : Fin n with i.val < k, γ.1 i) ≤
      (∑ i : Fin n with i.val < k, lam.1 i) + ∑ i : Fin n with i.val < k, μ.1 i := by
  rcases le_or_gt k n with hk | hk
  · have htot := sum_eq_of_productBoundary hb
    have hsuf := suffix_sum_le_of_productBoundary hb hk
    have hc_lam :
        (∑ i : Fin n with i.val < k, lam.1 i) + (∑ i : Fin n with k ≤ i.val, lam.1 i) =
          ∑ i : Fin n, lam.1 i := by
      simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n => i.val < k) lam.1
    have hc_mu :
        (∑ i : Fin n with i.val < k, μ.1 i) + (∑ i : Fin n with k ≤ i.val, μ.1 i) =
          ∑ i : Fin n, μ.1 i := by
      simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n => i.val < k) μ.1
    have hc_gam :
        (∑ i : Fin n with i.val < k, γ.1 i) + (∑ i : Fin n with k ≤ i.val, γ.1 i) =
          ∑ i : Fin n, γ.1 i := by
      simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin n => i.val < k) γ.1
    linarith
  · have hall : ({i : Fin n | i.val < k} : Finset (Fin n)) = Finset.univ := by
      ext i; simp [i.isLt.trans hk]
    rw [hall, ← sum_eq_of_productBoundary hb]

/-- **Dominance bound `γ ≤ λ + μ`**: if an integer hive has boundary `productBoundary lam μ γ`,
then `lam + μ` dominates `γ`. -/
theorem dominates_add_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) :
    (lam + μ).Dominates γ := by
  rw [DominantWeight.dominates_iff]
  refine ⟨?_, fun k => ?_⟩
  · simp [Finset.sum_add_distrib, ← sum_eq_of_productBoundary hb]
  · simpa [Finset.sum_add_distrib] using prefix_sum_le_of_productBoundary hb k

/-- **Lower-coordinate bound `γₙ ≥ λₙ + μₙ`** on nonempty weights. -/
theorem last_le_of_productBoundary {m : ℕ} {lam μ γ : DominantWeight (m + 1)}
    {h : IntegerHive (m + 1)} (hb : h.boundary = productBoundary lam μ γ) :
    lam.1 (Fin.last m) + μ.1 (Fin.last m) ≤ γ.1 (Fin.last m) := by
  have hsuf := suffix_sum_le_of_productBoundary hb (Nat.le_succ m)
  have hlast : ({i : Fin (m + 1) | m ≤ i.val} : Finset (Fin (m + 1))) = {Fin.last m} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_last]
    omega
  simpa [hlast] using hsuf

/-- Uniform determinant-twist lower bound `λ.detShift + μ.detShift ≤ γ.detShift` valid for all
ranks `n` (`0` included). -/
theorem detShift_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) :
    lam.detShift + μ.detShift ≤ γ.detShift := by
  match n, lam, μ, γ, h, hb with
  | 0, _, _, _, _, _ => simp
  | m + 1, _, _, _, _, hb => exact last_le_of_productBoundary hb

/-- If `lam` and `μ` are polynomial dominant weights and `productBoundary lam μ γ` admits an
integer hive, then `γ` is also polynomial. -/
theorem isPolynomial_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) :
    γ.IsPolynomial := by
  rw [DominantWeight.isPolynomial_iff_zero_le_detShift] at hlam hμ ⊢
  linarith [detShift_le_of_productBoundary hb]

/-- Upper first-coordinate bound `γ₁ ≤ λ₁ + μ₁` on nonempty weights. -/
theorem first_le_of_productBoundary {m : ℕ} {lam μ γ : DominantWeight (m + 1)}
    {h : IntegerHive (m + 1)} (hb : h.boundary = productBoundary lam μ γ) :
    γ.1 0 ≤ lam.1 0 + μ.1 0 := by
  have hpre := prefix_sum_le_of_productBoundary hb 1
  have hzero : ({i : Fin (m + 1) | i.val < 1} : Finset (Fin (m + 1))) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
      Fin.val_zero]
    omega
  rw [hzero] at hpre
  simpa using hpre

/-- **Finite output support**: for fixed dominant weights `λ, μ`, only finitely many dominant
weights `γ` satisfy `0 < hiveCount (productBoundary λ μ γ)`. -/
theorem finite_support_hiveCount_productBoundary {n : ℕ} (lam μ : DominantWeight n) :
    {γ : DominantWeight n | 0 < hiveCount (productBoundary lam μ γ)}.Finite := by
  cases n with
  | zero => exact Set.toFinite _
  | succ m =>
    let box : Finset (Fin (m + 1) → ℤ) := Fintype.piFinset fun _ =>
      Finset.Icc (lam.1 (Fin.last m) + μ.1 (Fin.last m)) (lam.1 0 + μ.1 0)
    have hfin :
        (Subtype.val ⁻¹' (box : Set (Fin (m + 1) → ℤ)) : Set (DominantWeight (m + 1))).Finite :=
      box.finite_toSet.preimage Subtype.coe_injective.injOn
    refine hfin.subset fun γ hγ => ?_
    obtain ⟨⟨h, hb⟩⟩ := hiveCount_pos_iff.mp hγ
    simp only [Set.mem_preimage, SetLike.mem_coe, box, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    exact ⟨(last_le_of_productBoundary hb).trans (γ.antitone (Fin.le_last j)),
      (γ.antitone (Fin.zero_le j)).trans (first_le_of_productBoundary hb)⟩

end IntegerFibre

/-! ### Rank-`2` multiplicity-freeness and concrete checks -/

section RankTwoChecks

/-- At size `2`, `Δ₂` has no strictly interior lattice vertices, so `boundary` is injective over
every partially ordered abelian group. -/
theorem boundary_injective_two {R : Type*} [AddCommGroup R] [PartialOrder R] :
    Function.Injective (boundary (n := 2) (R := R)) := by
  intro h₁ h₂ hb
  ext p
  have hp := p.sum_eq
  rcases (by omega : p.z = 0 ∨ p.x = 0 ∨ p.y = 0) with hz | hx | hy
  · have he : p = Vertex.edgePoint 2 0 ⟨p.y, by omega⟩ := by ext <;> simp [hz]; omega
    rw [he, apply_edgePoint_zero, apply_edgePoint_zero, hb]
  · have he : p = Vertex.edgePoint 2 1 ⟨p.z, by omega⟩ := by ext <;> simp [hx]; omega
    rw [he, apply_edgePoint_one, apply_edgePoint_one, hb]
  · have he : p = Vertex.edgePoint 2 2 ⟨p.x, by omega⟩ := by ext <;> simp [hy]; omega
    rw [he, apply_edgePoint_two, apply_edgePoint_two, hb]

instance subsingleton_fixedIntegerHive_two (B : Fin 3 → Fin 2 → ℤ) :
    Subsingleton (FixedIntegerHive B) :=
  ⟨fun h₁ h₂ => Subtype.ext (boundary_injective_two (h₁.2.trans h₂.2.symm))⟩

/-- Every `GL₂` hive fibre has at most one element (`hiveCount B ≤ 1`). -/
theorem hiveCount_le_one_two (B : Fin 3 → Fin 2 → ℤ) : hiveCount B ≤ 1 :=
  Fintype.card_le_one_iff_subsingleton.mpr inferInstance

theorem hiveCount_two_std_std_sym :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 1 := by
  have hpos : 0 < hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩) :=
    hiveCount_pos_iff.mpr ⟨⟨exampleTwo, boundary_exampleTwo⟩⟩
  have hle := hiveCount_le_one_two
    (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩)
  omega

/-- Rank-`2` check for `λ = μ = (1, 0)`, `γ = (1, 1)`: the clockwise perimeter values
`(0, 1, 1, 2, 2, 1)` form a normalized integer hive with unit-rhombus slacks `(0, 1, 0)`. -/
def detTwo : IntegerHive 2 where
  value p := (p.z : ℤ) + if p.y = 0 then 0 else 1
  value_cornerA' := by simp
  le_of_isRhombus' {a b c d} hr := by
    have hshort := hr.short; rw [Vertex.sqDist_def] at hshort
    have hdy : ((a.y : ℤ) - c.y) ^ 2 ≤ 2 := by
      linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.z : ℤ) - c.z)]
    have hdz : ((a.z : ℤ) - c.z) ^ 2 ≤ 2 := by
      linarith [sq_nonneg ((a.x : ℤ) - c.x), sq_nonneg ((a.y : ℤ) - c.y)]
    have hbdy : -1 ≤ (a.y : ℤ) - c.y ∧ (a.y : ℤ) - c.y ≤ 1 := by
      have hprod : 0 < (2 + ((a.y : ℤ) - c.y)) * (2 - ((a.y : ℤ) - c.y)) := by
        linarith [show (2 + ((a.y : ℤ) - c.y)) * (2 - ((a.y : ℤ) - c.y)) =
          4 - ((a.y : ℤ) - c.y) ^ 2 by ring]
      rcases mul_pos_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have hbdz : -1 ≤ (a.z : ℤ) - c.z ∧ (a.z : ℤ) - c.z ≤ 1 := by
      have hprod : 0 < (2 + ((a.z : ℤ) - c.z)) * (2 - ((a.z : ℤ) - c.z)) := by
        linarith [show (2 + ((a.z : ℤ) - c.z)) * (2 - ((a.z : ℤ) - c.z)) =
          4 - ((a.z : ℤ) - c.z) ^ 2 by ring]
      rcases mul_pos_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have := hr.midpoint_y; have := hr.midpoint_z
    have := a.sum_eq; have := b.sum_eq; have := c.sum_eq; have := d.sum_eq
    omega

@[simp]
theorem detTwo_apply (p : Vertex 2) :
    detTwo p = (p.z : ℤ) + if p.y = 0 then 0 else 1 := (rfl)

theorem boundary_detTwo :
    detTwo.boundary =
      productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩ := by
  ext s i
  fin_cases i <;> induction s using fin3_cases <;> simp [boundary_apply]

theorem slacks_detTwo :
    rhombusSlack detTwo ⟨1, 1, 0, rfl⟩ (Vertex.cornerA 2) ⟨1, 0, 1, rfl⟩ ⟨0, 1, 1, rfl⟩ = 0 ∧
    rhombusSlack detTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate (Vertex.cornerA 2).rotate
      (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate = 1 ∧
    rhombusSlack detTwo (⟨1, 1, 0, rfl⟩ : Vertex 2).rotate.rotate
      (Vertex.cornerA 2).rotate.rotate (⟨1, 0, 1, rfl⟩ : Vertex 2).rotate.rotate
      (⟨0, 1, 1, rfl⟩ : Vertex 2).rotate.rotate = 0 := by
  simp [rhombusSlack_def]

/-- Rank-`2` check `c^{(1, 1)}_{(1, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_std_std_det :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩) = 1 := by
  have hpos : 0 < hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩) :=
    hiveCount_pos_iff.mpr ⟨⟨detTwo, boundary_detTwo⟩⟩
  have hle := hiveCount_le_one_two
    (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩)
  omega

/-- Rank-`2` lower-coordinate exclusion check: `λ = μ = (1, 0)` and `γ = (3, -1)` satisfy
`(λ + μ).Dominates γ`, yet `γ₂ = -1 < 0 = λ₂ + μ₂`, so `last_le_of_productBoundary` proves the
fibre empty without enumeration. -/
theorem hiveCount_two_std_std_three_neg_one :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![3, -1], by decide⟩) = 0 := by
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun ⟨h, hb⟩ => ?_⟩
  have hlast := last_le_of_productBoundary hb
  change (0 : ℤ) + 0 ≤ -1 at hlast
  omega

end RankTwoChecks

end TauCeti.Hive
