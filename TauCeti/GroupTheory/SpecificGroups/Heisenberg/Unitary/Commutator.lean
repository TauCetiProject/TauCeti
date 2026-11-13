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

/-- Over an integral domain with nonidentity involution and a trace-one element, a root element is
central exactly when its first coordinate vanishes. -/
@[simp]
theorem mem_center_iff (hσ : Function.Involutive σ) (htr : ∃ t, t + σ t = 1)
    (hne : ∃ t, σ t ≠ t) (a : unitarySubgroup σ) :
    a ∈ Subgroup.center (unitarySubgroup σ) ↔ (a : HeisenbergGroup K).x = 0 := by
  constructor
  · intro ha
    have hcross (x : K) : (a : HeisenbergGroup K).x * σ x =
        x * σ (a : HeisenbergGroup K).x := by
      obtain ⟨b, hb⟩ := exists_coe_x_eq hσ htr x
      have hcomm : ⁅a, b⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp ha b).symm
      have hz := congrArg (fun c : unitarySubgroup σ ↦ (c : HeisenbergGroup K).z) hcomm
      simpa only [coe_commutatorElement, hb, Subgroup.coe_one, one_z, sub_eq_zero] using hz
    have hx : (a : HeisenbergGroup K).x = σ (a : HeisenbergGroup K).x := by
      simpa using hcross 1
    obtain ⟨t, ht⟩ := hne
    have hmul : (a : HeisenbergGroup K).x * (σ t - t) = 0 := by
      rw [mul_sub, hcross t, ← hx, mul_comm t, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr ht)
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (zAxis_le_center
      (mem_zAxis_iff.mpr ⟨hx, by simp [hx]⟩)) b

/-- Over an integral domain with nonidentity involution and a trace-one element, the centre is
the trace-zero central axis. -/
theorem center_eq_zAxis_subgroupOf (hσ : Function.Involutive σ)
    (htr : ∃ t, t + σ t = 1) (hne : ∃ t, σ t ≠ t) :
    Subgroup.center (unitarySubgroup σ) = zAxis.subgroupOf (unitarySubgroup σ) := by
  ext a
  simp only [mem_center_iff hσ htr hne, Subgroup.mem_subgroupOf, mem_zAxis_iff, y_eq a]
  exact ⟨fun hx ↦ ⟨hx, by simp [hx]⟩, And.left⟩

/-- The derived subgroup and centre of a unitary root group over an integral domain agree when the
involution is nonidentity and has a trace-one element. -/
theorem commutator_eq_center (hσ : Function.Involutive σ) (htr : ∃ t, t + σ t = 1)
    (hne : ∃ t, σ t ≠ t) :
    commutator (unitarySubgroup σ) = Subgroup.center (unitarySubgroup σ) := by
  rw [commutator_eq_zAxis_subgroupOf hσ htr, center_eq_zAxis_subgroupOf hσ htr hne]

end Domain

variable {K : Type*} [Field K]

/-- For the quadratic finite-field involution, the derived subgroup of the unitary root group
is its centre, in every characteristic. -/
theorem commutator_eq_center_iterateFrobenius {p n : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ n) ^ 2) :
    commutator (unitarySubgroup (iterateFrobenius K p n)) =
      Subgroup.center (unitarySubgroup (iterateFrobenius K p n)) := by
  have hσ : Function.Involutive (iterateFrobenius K p n) :=
    FiniteField.iterateFrobenius_involutive (by simpa [pow_mul] using hK)
  obtain ⟨t, ht⟩ := FiniteField.exists_pow_add_self_eq hK (one_pow (p ^ n))
  have htr : ∃ t : K, t + iterateFrobenius K p n t = 1 :=
    ⟨t, by simpa [iterateFrobenius_def, add_comm] using ht⟩
  apply commutator_eq_center hσ htr
  obtain ⟨c, hc, hcz⟩ := FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero hK 0
  have hcz' : c ^ p ^ n = -c := eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using hcz)
  obtain ⟨s, hs⟩ := FiniteField.exists_add_neg_one_pow_mul_pow_eq hK 1 (by simpa using hcz')
  refine ⟨s, ?_⟩
  intro heq
  apply hc
  have heq' : s ^ p ^ n = s := by simpa [iterateFrobenius_def] using heq
  simpa [heq'] using hs.symm

end TauCeti.HeisenbergGroup.unitarySubgroup

end
