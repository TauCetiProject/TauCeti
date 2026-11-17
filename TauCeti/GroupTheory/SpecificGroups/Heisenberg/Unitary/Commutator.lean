/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Unitary.Basic
public import TauCeti.FieldTheory.Finite.PowAddSelf
import TauCeti.FieldTheory.Finite.Frobenius

/-!
# The centre and derived subgroup of a unitary root group

For an involution `σ` of a commutative ring admitting an element of trace one, the derived
subgroup of the unitary Heisenberg group consists exactly of the elements on the central
`z`-axis. In fact every such element is a single commutator. Over an integral domain with
nonidentity involution this subgroup is the whole centre.

These results apply to the upper root group of `SU₃(q)` over a field of order `q²`, including
characteristic two. They identify its central root subgroup without division by two, as needed
in the root calculus for the rank-one unitary group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), Chapter 13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11.
-/

public section

open scoped commutatorElement

namespace TauCeti.HeisenbergGroup.unitarySubgroup

variable {R : Type*} [CommRing R] {σ : R →+* R}

/-- If there is an element of trace one, every first coordinate occurs in the unitary root
subgroup. -/
theorem exists_coe_x_eq (hσ : Function.Involutive σ) (htr : ∃ t, t + σ t = 1) (x : R) :
    ∃ a : unitarySubgroup σ, (a : HeisenbergGroup R).x = x := by
  obtain ⟨t, ht⟩ := htr
  have hz : t * (x * σ x) + σ (t * (x * σ x)) = x * σ x := by
    simp only [map_mul, hσ x]
    linear_combination x * σ x * ht
  exact ⟨unitaryMk σ hσ x (t * (x * σ x)) hz, by simp⟩

/-- With a trace-one element, every element on the central axis of the unitary root group is
a single commutator of unitary root elements. -/
theorem exists_commutatorElement_eq_of_mem_zAxis (hσ : Function.Involutive σ)
    (htr : ∃ t, t + σ t = 1) (a : unitarySubgroup σ)
    (ha : (a : HeisenbergGroup R) ∈ zAxis) :
    ∃ b c : unitarySubgroup σ, ⁅b, c⁆ = a := by
  obtain ⟨t, ht⟩ := htr
  obtain ⟨b, hb⟩ := exists_coe_x_eq hσ ⟨t, ht⟩ 1
  obtain ⟨c, hc⟩ := exists_coe_x_eq hσ ⟨t, ht⟩ (-(a : HeisenbergGroup R).z * t)
  refine ⟨b, c, ?_⟩
  obtain ⟨hax, hay⟩ := mem_zAxis_iff.mp ha
  have hz := z_add_map_z a
  rw [hax, zero_mul] at hz
  apply Subtype.ext
  rw [coe_commutatorElement, hb, hc]
  apply HeisenbergGroup.ext
  · exact hax.symm
  · exact hay.symm
  · simp only [map_neg, map_mul, map_one, one_mul, mul_one]
    linear_combination (a : HeisenbergGroup R).z * ht - σ t * hz

/-- The derived subgroup of the unitary root group is precisely its central axis, provided
there is an element of trace one. -/
theorem commutator_eq_zAxis_subgroupOf (hσ : Function.Involutive σ)
    (htr : ∃ t, t + σ t = 1) :
    commutator (unitarySubgroup σ) = zAxis.subgroupOf (unitarySubgroup σ) := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun a _ b _ ↦ ?_) ?_
  · exact commutatorElement_mem_zAxis (a : HeisenbergGroup R) (b : HeisenbergGroup R)
  · intro a ha
    obtain ⟨b, c, rfl⟩ := exists_commutatorElement_eq_of_mem_zAxis hσ htr a ha
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

section Domain

variable {K : Type*} [CommRing K] [IsDomain K] {σ : K →+* K}

/-- Over an integral domain with nonidentity involution, a root element is central exactly
when its first coordinate vanishes. -/
theorem mem_center_iff (hσ : Function.Involutive σ)
    (hne : ∃ t, σ t ≠ t) (a : unitarySubgroup σ) :
    a ∈ Subgroup.center (unitarySubgroup σ) ↔ (a : HeisenbergGroup K).x = 0 := by
  constructor
  · intro ha
    obtain ⟨t, ht⟩ := hne
    have htrace : ∃ u : K, u + σ u ≠ 0 := by
      by_cases h1 : (1 : K) + σ 1 = 0
      · refine ⟨t, fun ht0 ↦ ht ?_⟩
        have h1' : (1 : K) + 1 = 0 := by simpa using h1
        linear_combination ht0 - t * h1'
      · exact ⟨1, h1⟩
    obtain ⟨u, hu⟩ := htrace
    let s := u + σ u
    have hs : σ s = s := by simp only [s, map_add, hσ u, add_comm]
    have hcross (x : K) : (a : HeisenbergGroup K).x * σ x =
        x * σ (a : HeisenbergGroup K).x := by
      have hz : u * (s * x * σ x) + σ (u * (s * x * σ x)) =
          (s * x) * σ (s * x) := by
        simp only [map_mul, hs, hσ x]
        dsimp [s]
        ring
      let b := unitaryMk σ hσ (s * x) (u * (s * x * σ x)) hz
      have hcomm : ⁅a, b⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp ha b).symm
      have hz' := congrArg (fun c : unitarySubgroup σ ↦ (c : HeisenbergGroup K).z) hcomm
      have hzero : s * ((a : HeisenbergGroup K).x * σ x -
          x * σ (a : HeisenbergGroup K).x) = 0 := by
        simp only [coe_commutatorElement, b, coe_unitaryMk, map_mul, hs,
          Subgroup.coe_one, one_z] at hz'
        linear_combination hz'
      exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hu)
    have hx : (a : HeisenbergGroup K).x = σ (a : HeisenbergGroup K).x := by
      simpa using hcross 1
    have hmul : (a : HeisenbergGroup K).x * (σ t - t) = 0 := by
      rw [mul_sub, hcross t, ← hx, mul_comm t, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr ht)
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (zAxis_le_center
      (mem_zAxis_iff.mpr ⟨hx, by simp [hx]⟩)) b

/-- Over an integral domain with nonidentity involution, the centre is
the trace-zero central axis. -/
theorem center_eq_zAxis_subgroupOf (hσ : Function.Involutive σ)
    (hne : ∃ t, σ t ≠ t) :
    Subgroup.center (unitarySubgroup σ) = zAxis.subgroupOf (unitarySubgroup σ) := by
  ext a
  simp only [mem_center_iff hσ hne, Subgroup.mem_subgroupOf, mem_zAxis_iff, y_eq a]
  exact ⟨fun hx ↦ ⟨hx, by simp [hx]⟩, And.left⟩

/-- The derived subgroup and centre of a unitary root group over an integral domain agree when the
involution is nonidentity and has a trace-one element. -/
theorem commutator_eq_center (hσ : Function.Involutive σ) (htr : ∃ t, t + σ t = 1)
    (hne : ∃ t, σ t ≠ t) :
    commutator (unitarySubgroup σ) = Subgroup.center (unitarySubgroup σ) := by
  rw [commutator_eq_zAxis_subgroupOf hσ htr, center_eq_zAxis_subgroupOf hσ hne]

end Domain

variable {K : Type*} [Field K]

variable {p n : ℕ} [ExpChar K p]

/-- Every first coordinate occurs in the quadratic finite-field unitary root group. -/
theorem exists_coe_x_iterateFrobenius_eq (hK : Nat.card K = (p ^ n) ^ 2) (x : K) :
    ∃ a : unitarySubgroup (iterateFrobenius K p n), (a : HeisenbergGroup K).x = x :=
  exists_coe_x_eq (FiniteField.iterateFrobenius_involutive (by simpa [pow_mul] using hK))
    (FiniteField.exists_add_iterateFrobenius_eq_one hK) x

/-- The quadratic finite-field unitary root group has derived subgroup equal to its central
axis, in every characteristic. -/
theorem commutator_eq_zAxis_subgroupOf_iterateFrobenius (hK : Nat.card K = (p ^ n) ^ 2) :
    commutator (unitarySubgroup (iterateFrobenius K p n)) =
      zAxis.subgroupOf (unitarySubgroup (iterateFrobenius K p n)) :=
  commutator_eq_zAxis_subgroupOf
    (FiniteField.iterateFrobenius_involutive (by simpa [pow_mul] using hK))
    (FiniteField.exists_add_iterateFrobenius_eq_one hK)

/-- A quadratic finite-field unitary root element is central exactly when its first coordinate
vanishes. -/
theorem mem_center_iterateFrobenius_iff (hK : Nat.card K = (p ^ n) ^ 2)
    (a : unitarySubgroup (iterateFrobenius K p n)) :
    a ∈ Subgroup.center (unitarySubgroup (iterateFrobenius K p n)) ↔
      (a : HeisenbergGroup K).x = 0 :=
  mem_center_iff (FiniteField.iterateFrobenius_involutive (by simpa [pow_mul] using hK))
    (FiniteField.exists_iterateFrobenius_ne_of_card_eq_sq hK) a

/-- The centre of the quadratic finite-field unitary root group is its trace-zero central
axis. -/
theorem center_eq_zAxis_subgroupOf_iterateFrobenius (hK : Nat.card K = (p ^ n) ^ 2) :
    Subgroup.center (unitarySubgroup (iterateFrobenius K p n)) =
      zAxis.subgroupOf (unitarySubgroup (iterateFrobenius K p n)) :=
  center_eq_zAxis_subgroupOf
    (FiniteField.iterateFrobenius_involutive (by simpa [pow_mul] using hK))
    (FiniteField.exists_iterateFrobenius_ne_of_card_eq_sq hK)

/-- For the quadratic finite-field involution, the derived subgroup of the unitary root group
is its centre, in every characteristic. -/
theorem commutator_eq_center_iterateFrobenius (hK : Nat.card K = (p ^ n) ^ 2) :
    commutator (unitarySubgroup (iterateFrobenius K p n)) =
      Subgroup.center (unitarySubgroup (iterateFrobenius K p n)) := by
  rw [commutator_eq_zAxis_subgroupOf_iterateFrobenius hK,
    center_eq_zAxis_subgroupOf_iterateFrobenius hK]

end TauCeti.HeisenbergGroup.unitarySubgroup

end
