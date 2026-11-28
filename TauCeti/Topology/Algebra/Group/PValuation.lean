/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-!
# p-valuations on topological groups

A `p)-valuation is an extended real weight on a group. Its finite superlevel sets
are a neighbourhood basis at the identity, and the group is complete for its group uniformity.
Saturation says that elements of weight strictly greater than `p / (p - 1)` have `p`-th roots.

## References

* M. Lazard, *Groupes analytiques p-adiques*, III.2.1.2.
* P. Schneider, *p-Adic Lie Groups*, §§23–26.
-/

public section

open Filter
open scoped ENNReal Topology commutatorElement

namespace TauCeti

/-- A `p`-valuation inducing the given complete group topology. Its value increases by one
under the `p`-th power map, and the value of a commutator is at least the sum of the values. -/
structure PValuation (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] where
  /-- The weight, with infinite value at the identity. -/
  toFun : G → ℝ≥0∞
  /-- The identity is the only element of infinite weight. -/
  eq_top_iff' : ∀ x, toFun x = ⊤ ↔ x = 1
  /-- Every weight is strictly greater than `1 / (p - 1)`. -/
  inv_lt' : ∀ x, ((↑(p - 1 : ℕ) : ℝ≥0∞)⁻¹) < toFun x
  /-- The valuation inequality for right division. -/
  min_le_mul_inv' : ∀ x y, min (toFun x) (toFun y) ≤ toFun (x * y⁻¹)
  /-- The commutator raises weights additively. -/
  add_le_commutator' : ∀ x y, toFun x + toFun y ≤ toFun ⁅x, y⁆
  /-- The exact change in weight under the `p`-th power map. -/
  map_pow' : ∀ x, toFun (x ^ p) = toFun x + 1
  /-- Finite weight superlevel sets determine the topology at the identity. -/
  hasBasis_nhds_one' : (𝓝 (1 : G)).HasBasis (fun r : ℝ≥0∞ ↦ r ≠ ⊤)
    fun r ↦ {x | r ≤ toFun x}
  /-- Completeness for the right uniformity of the given group topology. -/
  completeSpace : @CompleteSpace G (IsTopologicalGroup.rightUniformSpace G)

namespace PValuation

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

instance : FunLike (PValuation p G) G ℝ≥0∞ where
  coe := toFun
  coe_injective := by
    rintro ⟨_, _, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _, _⟩ h
    cases h
    rfl

/-- Coercing a constructed valuation to a function gives its weight function. -/
@[simp]
theorem coe_mk (f : G → ℝ≥0∞) (h_top h_inv h_mul_inv h_comm h_pow h_basis h_complete) :
    ⇑(⟨f, h_top, h_inv, h_mul_inv, h_comm, h_pow, h_basis, h_complete⟩ : PValuation p G) =
      f :=
  (rfl)

@[ext]
theorem ext {v w : PValuation p G} (h : ∀ x, v x = w x) : v = w :=
  DFunLike.ext _ _ h

variable (v : PValuation p G)

/-- The weight function agrees with the function coercion. -/
@[simp]
theorem toFun_eq_coe : v.toFun = ⇑v :=
  (rfl)

/-- Infinite weight characterizes the identity. -/
@[simp]
theorem eq_top_iff (x : G) : v x = ⊤ ↔ x = 1 :=
  v.eq_top_iff' x

@[simp]
theorem map_one : v (1 : G) = ⊤ :=
  (v.eq_top_iff 1).2 rfl

/-- The lower bound on weights of a `p`-valuation. -/
theorem inv_lt (x : G) : (↑(p - 1 : ℕ) : ℝ≥0∞)⁻¹ < v x :=
  v.inv_lt' x

/-- The weight of a right quotient is at least the smaller of the two weights. -/
theorem min_le_mul_inv (x y : G) : min (v x) (v y) ≤ v (x * y⁻¹) :=
  v.min_le_mul_inv' x y

/-- The weight of a commutator is at least the sum of the two weights. -/
theorem add_le_commutator (x y : G) : v x + v y ≤ v ⁅x, y⁆ :=
  v.add_le_commutator' x y

/-- The `p`-th power increases the weight by one. -/
@[simp]
theorem map_pow (x : G) : v (x ^ p) = v x + 1 :=
  v.map_pow' x

@[simp]
theorem map_inv (x : G) : v x⁻¹ = v x := by
  have h (y : G) : v y ≤ v y⁻¹ := by simpa using v.min_le_mul_inv 1 y
  exact le_antisymm (by simpa using h x⁻¹) (h x)

theorem min_le_mul (x y : G) : min (v x) (v y) ≤ v (x * y) := by
  simpa using v.min_le_mul_inv x y⁻¹

include v in
/-- A group carrying a `p`-valuation has no element of order `p`. -/
theorem pow_eq_one_iff (x : G) : x ^ p = 1 ↔ x = 1 := by
  rw [← v.eq_top_iff (x ^ p), v.map_pow]
  simp [ENNReal.add_eq_top]

/-- The terms of the decreasing filtration defined by the valuation. -/
def filtration (r : ℝ≥0∞) : Subgroup G where
  carrier := {x | r ≤ v x}
  one_mem' := by simp
  mul_mem' hx hy := (le_min hx hy).trans (v.min_le_mul _ _)
  inv_mem' hx := by simpa using hx

@[simp]
theorem mem_filtration (r : ℝ≥0∞) (x : G) : x ∈ v.filtration r ↔ r ≤ v x :=
  (Iff.rfl)

/-- A right quotient lies in the filtration term at the smaller of the two thresholds. -/
theorem mul_inv_mem_filtration_min {r s : ℝ≥0∞} {x y : G}
    (hx : x ∈ v.filtration r) (hy : y ∈ v.filtration s) :
    x * y⁻¹ ∈ v.filtration (min r s) := by
  simp only [mem_filtration] at hx hy ⊢
  exact (min_le_min hx hy).trans (v.min_le_mul_inv x y)

theorem filtration_antitone : Antitone v.filtration := fun _ _ h _ hx ↦ h.trans hx

instance (r : ℝ≥0∞) : (v.filtration r).Normal where
  conj_mem x hx y := by
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul, mem_filtration] at ⊢
    have hx' := (v.mem_filtration r x).mp hx
    have hcomm : r ≤ v ⁅y, x⁆ :=
      hx'.trans ((le_add_of_nonneg_left zero_le).trans (v.add_le_commutator y x))
    exact (le_min hcomm hx').trans (v.min_le_mul ⁅y, x⁆ x)

/-- Filtration terms at finite thresholds are a neighbourhood basis at the identity. -/
theorem hasBasis_nhds_one : (𝓝 (1 : G)).HasBasis (fun r : ℝ≥0∞ ↦ r ≠ ⊤)
    fun r ↦ (v.filtration r : Set G) :=
  v.hasBasis_nhds_one'

/-- The valuation is saturated if every element above the Lazard threshold admits a
`p`-th root. The weight of such a root is determined by `PValuation.map_pow`. -/
def IsSaturated : Prop :=
  ∀ x, (p : ℝ≥0∞) / (↑(p - 1 : ℕ) : ℝ≥0∞) < v x → ∃ y, y ^ p = x

theorem isSaturated_iff :
    v.IsSaturated ↔ ∀ x, (p : ℝ≥0∞) / (↑(p - 1 : ℕ) : ℝ≥0∞) < v x → ∃ y, y ^ p = x :=
  (Iff.rfl)

/-- In a saturated group an element above the Lazard threshold has a `p`-th root of
weight one less. -/
theorem IsSaturated.exists_pow_eq_and_weight (hv : v.IsSaturated) {x : G}
    (hx : (p : ℝ≥0∞) / (↑(p - 1 : ℕ) : ℝ≥0∞) < v x) :
    ∃ y, y ^ p = x ∧ v y = v x - 1 := by
  obtain ⟨y, rfl⟩ := hv x hx
  exact ⟨y, rfl, by rw [v.map_pow, ENNReal.add_sub_cancel_right ENNReal.one_ne_top]⟩

end PValuation

end TauCeti
