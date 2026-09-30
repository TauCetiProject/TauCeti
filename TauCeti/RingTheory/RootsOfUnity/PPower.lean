/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.Torsion
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.IntegralDomain

/-!
# Roots of unity of `p`-power order

For a commutative monoid, the `p`-power roots of unity form the primary component of its unit
group. In a domain, this subgroup is cyclic when finite.
-/

public section

namespace TauCeti

variable (p : ℕ) (K : Type*) [CommMonoid K]

/-- The subgroup of `Kˣ` consisting of roots of unity of `p`-power order. -/
abbrev pPowerRootsOfUnity : Subgroup Kˣ := CommGroup.primaryComponent Kˣ p

/-- A unit is a `p`-power root of unity exactly when some power of `p` kills it. -/
theorem mem_pPowerRootsOfUnity_iff (x : Kˣ) :
    x ∈ pPowerRootsOfUnity p K ↔ ∃ n : ℕ, x ^ (p ^ n) = 1 :=
  CommGroup.mem_primaryComponent

/-- The `p`-power roots of unity are the union of the finite-level root groups. -/
theorem pPowerRootsOfUnity_eq_iSup_rootsOfUnity :
    pPowerRootsOfUnity p K = ⨆ n : ℕ, rootsOfUnity (p ^ n) K := by
  ext x
  have hdir : Directed (· ≤ ·) (fun n : ℕ ↦ rootsOfUnity (p ^ n) K) := by
    intro m n
    refine ⟨max m n, rootsOfUnity_le_of_dvd (pow_dvd_pow p (le_max_left m n)),
      rootsOfUnity_le_of_dvd (pow_dvd_pow p (le_max_right m n))⟩
  simp only [mem_pPowerRootsOfUnity_iff, Subgroup.mem_iSup_of_directed hdir,
    mem_rootsOfUnity]

end TauCeti

namespace TauCeti

variable (p : ℕ) (K : Type*) [CommRing K] [IsDomain K]

/-- A finite group of `p`-power roots of unity in a domain is cyclic. -/
theorem isCyclic_pPowerRootsOfUnity (h : Finite (pPowerRootsOfUnity p K)) :
    IsCyclic (pPowerRootsOfUnity p K) := by
  let _ := h
  exact isCyclic_subgroup_units (pPowerRootsOfUnity p K)

end TauCeti
