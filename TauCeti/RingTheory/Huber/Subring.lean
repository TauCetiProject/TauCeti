/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic

/-!
# Subrings of Huber rings

A subring of a Tate ring is Tate as soon as it contains a pseudouniformiser and its inverse.
The topology is always the subspace topology. No closedness assumption is needed: intersecting
a ring of definition with the subring supplies an open bounded subring. Closedness is needed
only when one also wants completeness.

A subring containing a pseudouniformiser of the ambient Huber ring also has the same bounded
subsets and the same power-bounded elements as the ambient ring, so its power-bounded subring is
the trace of the ambient one. For an arbitrary subring, boundedness only descends. These are
inputs for rings of invariants of finite group actions on Huber pairs.

## Main results

* `Subring.isTateRing_of_isPseudoUniformizer`: a subring containing a pseudouniformiser and its
  inverse is a Tate ring.
* `Subring.isBounded_image_subtype_iff`, `Subring.isPowerBounded_coe_iff`: boundedness and
  power-boundedness in a subring containing a pseudouniformiser agree with those in `R`.
* `Subring.powerBoundedSubring_eq_comap`: for such a subring, `S° = R° ∩ S`.
-/

public section

open Filter Topology Pointwise TauCeti.Huber

namespace Subring

section Tate

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsTateRing R]

/-- A subring containing a pseudouniformiser as a unit is a Tate ring in its subspace topology.
The unit hypothesis says that the inverse also lies in the subring. -/
theorem isTateRing_of_isPseudoUniformizer (S : Subring R) (u : Rˣ)
    (hu : IsPseudoUniformizer u.val) (hmem : u.val ∈ S) (hinv : (u⁻¹).val ∈ S) :
    IsTateRing S := by
  let v : Sˣ := Units.mkOfMulEqOne ⟨u.val, hmem⟩ ⟨(u⁻¹).val, hinv⟩ (Subtype.ext u.val_inv)
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  exact IsTateRing.of_isOpen_isBounded (P.ringOfDefinition.comap S.subtype)
    (P.isOpen_ringOfDefinition.preimage continuous_subtypeVal)
    (S.isBounded_preimage_subtype P.isBounded_ringOfDefinition)
    (isPseudoUniformizer_iff.mpr ⟨v.isUnit,
      isTopologicallyNilpotent_mk hmem hu.isTopologicallyNilpotent⟩)

end Tate

section Huber

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsHuberRing R]

/-- **Boundedness in a subring containing a pseudouniformiser.** For a subring `S` of a Huber ring
containing a pseudouniformiser of the ambient ring, a subset of `S` is bounded for the subspace
topology exactly when it is bounded in `R`. Only the forward implication holds for arbitrary
subrings (`Subring.isBounded_preimage_subtype`). -/
theorem isBounded_image_subtype_iff (S : Subring R) {ϖ : R} (hϖ : IsPseudoUniformizer ϖ)
    (hmem : ϖ ∈ S) {T : Set S} : IsBounded (Subtype.val '' T) ↔ IsBounded T := by
  refine ⟨fun h ↦ (S.isBounded_preimage_subtype h).subset (Set.subset_preimage_image _ _),
    fun h ↦ ?_⟩
  obtain ⟨P⟩ := IsHuberRing.nonempty_pairOfDefinition (A := R)
  -- Some `ϖ ^ n` multiplies `T` into the ring of definition `A₀`, so `T ⊆ ϖ⁻ⁿ A₀`.
  obtain ⟨V, hV, hVT⟩ := isBounded_iff.mp h _
    ((P.isOpen_ringOfDefinition.preimage continuous_subtypeVal).mem_nhds
      P.ringOfDefinition.zero_mem)
  obtain ⟨n, hn⟩ :=
    ((isTopologicallyNilpotent_mk hmem hϖ.isTopologicallyNilpotent).eventually_mem hV).exists
  obtain ⟨u, hu⟩ := hϖ.isUnit.pow n
  refine ((isBounded_singleton (↑u⁻¹ : R)).mul P.isBounded_ringOfDefinition).subset ?_
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨↑u⁻¹, rfl, ϖ ^ n * t, hVT (Set.mul_mem_mul hn ht), ?_⟩
  simp [← hu, ← mul_assoc]

/-- An element of a subring containing a pseudouniformiser of the ambient Huber ring is
power-bounded in the subring exactly when it is power-bounded in the ambient ring. -/
theorem isPowerBounded_coe_iff (S : Subring R) {ϖ : R} (hϖ : IsPseudoUniformizer ϖ)
    (hmem : ϖ ∈ S) {x : S} : IsPowerBounded (x : R) ↔ IsPowerBounded x := by
  rw [isPowerBounded_iff, isPowerBounded_iff, ← S.isBounded_image_subtype_iff hϖ hmem,
    ← Set.range_comp]
  simp [Function.comp_def]

/-- For a subring containing a pseudouniformiser of the ambient Huber ring, the power-bounded
subring `S°` is `R° ∩ S`. -/
theorem powerBoundedSubring_eq_comap (S : Subring R) [NonarchimedeanAddGroup S] {ϖ : R}
    (hϖ : IsPseudoUniformizer ϖ) (hmem : ϖ ∈ S) :
    powerBoundedSubring S = (powerBoundedSubring R).comap S.subtype := by
  ext x
  simp [S.isPowerBounded_coe_iff hϖ hmem]

end Huber

end Subring
