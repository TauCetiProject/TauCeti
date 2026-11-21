/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Additive characters trivial on a neighbourhood of zero

An additive character `ψ` of a topological additive group is trivial on a neighbourhood of `0`
when `{x | ψ x = 1} ∈ 𝓝 0`. Over a nonarchimedean local field this is the condition under which
a nontrivial `ψ` has a conductor, the largest fractional ideal on which it is trivial.

This file records two sources of such characters. A continuous circle-valued character of a
nonarchimedean additive group is trivial on a neighbourhood of `0`: some open subgroup maps into
the arc of angles less than `π / 2`, and the only subgroup of the circle inside that arc is
trivial. The condition is also preserved by the shifts `x ↦ ψ (b * x)` of a character of a
topological ring.

## Main results

* `AddChar.setOf_eq_one_mem_nhds_zero`: a continuous circle-valued additive character of a
  nonarchimedean additive group is trivial on a neighbourhood of `0`.
* `AddChar.setOf_mulShift_eq_one_mem_nhds_zero`: the shift `ψ.mulShift b` of a character trivial
  on a neighbourhood of `0` is again trivial on a neighbourhood of `0`.
-/

public section

open Filter Topology

namespace AddChar

/-- A continuous additive character of a nonarchimedean additive group with values in the unit
circle is trivial on a neighbourhood of `0`. -/
theorem setOf_eq_one_mem_nhds_zero {G : Type*} [AddGroup G] [TopologicalSpace G]
    [NonarchimedeanAddGroup G] {ψ : AddChar G Circle} (hψ : Continuous ψ) :
    {x | ψ x = 1} ∈ 𝓝 (0 : G) := by
  have hN : ψ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : G) := by
    refine hψ.continuousAt.preimage_mem_nhds ((Circle.isOpen_centeredArc _).mem_nhds ?_)
    rw [map_zero_eq_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hN
  refine mem_of_superset V.mem_nhds_zero fun x hx ↦
    Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun k _ ↦ ?_
  rw [← map_nsmul_eq_pow]
  exact hV (nsmul_mem hx k)

/-- The shift `x ↦ ψ (b * x)` of an additive character of a topological ring which is trivial on a
neighbourhood of `0` is again trivial on a neighbourhood of `0`. -/
theorem setOf_mulShift_eq_one_mem_nhds_zero {R M : Type*} [Ring R] [TopologicalSpace R]
    [ContinuousMul R] [CommMonoid M] {ψ : AddChar R M} (h0 : {x | ψ x = 1} ∈ 𝓝 (0 : R)) (b : R) :
    {x | ψ.mulShift b x = 1} ∈ 𝓝 (0 : R) := by
  have hb : Tendsto (b * ·) (𝓝 (0 : R)) (𝓝 0) := by
    simpa using (continuous_const_mul b).tendsto (0 : R)
  simpa using hb h0

end AddChar
