/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Normed
public import TauCeti.RingTheory.Huber.PowerBounded
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Canonical reduction of a nonarchimedean topological ring

The canonical reduction is `A° / A°°`, using the native power-bounded subring and its
ideal of topologically nilpotent elements. It is always reduced, even when `A` is not:
topological nilpotence of a positive power implies topological nilpotence of the element.
No completeness, uniformity or noetherianity is required.

For an ultrametric normed field `K`, the power-bounded subring `K°` coincides with the valuation
ring `𝒪[K]`, the topologically nilpotent ideal `K°°` corresponds to the maximal ideal of
`𝒪[K]`, and the canonical reduction `K° / K°°` is canonically isomorphic to the valuation residue
field `𝓀[K]`.

## Main definitions

* `TauCeti.Huber.CanonicalReduction`: the canonical reduction `A° / A°°`.
* `TauCeti.Huber.powerBoundedSubringEquivInteger`: the ring isomorphism `K° ≃+* 𝒪[K]` for an
  ultrametric normed field `K`.
* `TauCeti.Huber.canonicalReductionEquivResidueField`: the ring isomorphism
  `K° / K°° ≃+* 𝓀[K]` for an ultrametric normed field `K`.

## Main results

* `TauCeti.Huber.isRadical_topologicallyNilpotentIdeal`: `A°°` is a radical ideal of `A°`.
* `TauCeti.Huber.powerBoundedSubring_eq_integer`: `K° = 𝒪[K]` as subrings of `K`.
* `TauCeti.Huber.map_topologicallyNilpotentIdeal_powerBoundedSubringEquivInteger`: under
  `K° ≃+* 𝒪[K]`, the ideal `K°°` maps onto the maximal ideal of `𝒪[K]`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.3.1.
-/

public section

namespace TauCeti.Huber

variable (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
    [ContinuousMul A]

/-- The ideal of topologically nilpotent elements in the power-bounded subring is radical. -/
theorem isRadical_topologicallyNilpotentIdeal : (topologicallyNilpotentIdeal A).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro a ha
  rw [mem_topologicallyNilpotentIdeal] at ha ⊢
  exact IsTopologicallyNilpotent.of_pow (by decide : 2 ≠ 0) ha

/-- The canonical reduction `A° / A°°` of a nonarchimedean topological ring. -/
abbrev CanonicalReduction := powerBoundedSubring A ⧸ topologicallyNilpotentIdeal A

instance : IsReduced (CanonicalReduction A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_topologicallyNilpotentIdeal A)

section NormedField

open scoped NormedField Valued

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The power-bounded subring of an ultrametric normed field is its valuation ring**: both are
the subring of elements of norm at most one. -/
theorem powerBoundedSubring_eq_integer : powerBoundedSubring K = Valued.integer K := by
  ext x
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, Valuation.mem_integer_iff]
  exact (NNReal.coe_le_coe (r₁ := ‖x‖₊) (r₂ := 1)).symm

/-- The canonical ring isomorphism `K° ≃+* 𝒪[K]` identifying the power-bounded subring of an
ultrametric normed field with its valuation ring. -/
noncomputable def powerBoundedSubringEquivInteger : powerBoundedSubring K ≃+* Valued.integer K :=
  RingEquiv.subringCongr (powerBoundedSubring_eq_integer K)

variable {K} in
/-- `powerBoundedSubringEquivInteger` preserves underlying elements of `K`. -/
@[simp]
theorem coe_powerBoundedSubringEquivInteger (x : powerBoundedSubring K) :
    ((powerBoundedSubringEquivInteger K x : Valued.integer K) : K) = x := (rfl)

variable {K} in
/-- The inverse of `powerBoundedSubringEquivInteger` preserves underlying elements of `K`. -/
@[simp]
theorem coe_powerBoundedSubringEquivInteger_symm (x : Valued.integer K) :
    ((powerBoundedSubringEquivInteger K).symm x : K) = x := (rfl)

/-- Under the identification `K° ≃+* 𝒪[K]`, the topologically nilpotent ideal `K°°` maps onto
the maximal ideal of `𝒪[K]`: both consist of the elements of norm strictly less than one. -/
theorem map_topologicallyNilpotentIdeal_powerBoundedSubringEquivInteger :
    (topologicallyNilpotentIdeal K).map (powerBoundedSubringEquivInteger K).toRingHom =
      IsLocalRing.maximalIdeal (Valued.integer K) := by
  have hint := Valuation.integer.integers (NormedField.valuation (K := K))
  ext y
  rw [Ideal.mem_map_iff_of_surjective (powerBoundedSubringEquivInteger K).toRingHom
    (powerBoundedSubringEquivInteger K).surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
      tendsto_pow_atTop_nhds_zero_iff_norm_lt_one] at hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : ‖(x : K)‖ = 1 := by
      simpa [← NNReal.coe_inj, Algebra.algebraMap_ofSubsemiring_apply] using
        hint.isUnit_iff_valuation_eq_one.mp hu
    exact hx.ne h1
  · intro hy
    refine ⟨(powerBoundedSubringEquivInteger K).symm y, ?_,
      (powerBoundedSubringEquivInteger K).apply_symm_apply y⟩
    rw [mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
      tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, coe_powerBoundedSubringEquivInteger_symm]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    have hle : ‖(y : K)‖ ≤ 1 := by
      simpa using isPowerBounded_iff_norm_le_one.mp
        (mem_powerBoundedSubring.mp ((powerBoundedSubringEquivInteger K).symm y).2)
    refine hle.lt_of_ne fun h1 ↦ hy ?_
    exact hint.isUnit_iff_valuation_eq_one.mpr
      (by simpa [← NNReal.coe_inj, Algebra.algebraMap_ofSubsemiring_apply] using h1)

/-- **The canonical reduction of an ultrametric normed field is its valuation residue field**:
`K° / K°° ≃+* 𝓀[K]`. -/
noncomputable def canonicalReductionEquivResidueField :
    CanonicalReduction K ≃+* 𝓀[K] :=
  Ideal.quotientEquiv (topologicallyNilpotentIdeal K) (IsLocalRing.maximalIdeal (Valued.integer K))
    (powerBoundedSubringEquivInteger K)
    (map_topologicallyNilpotentIdeal_powerBoundedSubringEquivInteger K).symm

variable {K} in
/-- `canonicalReductionEquivResidueField` sends the class of `x ∈ K°` to the residue of `x` in
`𝓀[K]`. -/
@[simp]
theorem canonicalReductionEquivResidueField_mk (x : powerBoundedSubring K) :
    canonicalReductionEquivResidueField K (Ideal.Quotient.mk _ x) =
      IsLocalRing.residue (Valued.integer K) (powerBoundedSubringEquivInteger K x) := (rfl)

end NormedField

end TauCeti.Huber
