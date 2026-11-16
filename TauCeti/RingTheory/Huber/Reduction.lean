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
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Canonical reduction of a nonarchimedean topological ring

The canonical reduction is `A° / A°°`, using the native power-bounded subring and its
ideal of topologically nilpotent elements. It is always reduced, even when `A` is not:
topological nilpotence of a positive power implies topological nilpotence of the element.
No completeness, uniformity or noetherianity is required.

For an ultrametric normed field `K` (equipped with the valuation `NormedField.toValued`), the
power-bounded subring `K°` equals the valuation ring `𝒪[K]`, the topologically nilpotent ideal
`K°°` corresponds to the maximal ideal `𝓂[K]`, and the canonical reduction `K° / K°°` is
canonically isomorphic to the residue field `𝓀[K]`.

## Main results

* `TauCeti.Huber.isRadical_topologicallyNilpotentIdeal`: `A°°` is a radical ideal of `A°`.
* `TauCeti.Huber.CanonicalReduction`: the quotient `A° / A°°`, which is reduced.
* `TauCeti.Huber.powerBoundedSubring_eq_integer` and
  `TauCeti.Huber.powerBoundedSubringEquivInteger`: `K° = 𝒪[K]` and `K° ≃+* 𝒪[K]` for an
  ultrametric normed field `K`.
* `TauCeti.Huber.map_topologicallyNilpotentIdeal_powerBoundedSubringEquivInteger`: the image of
  `K°°` in `𝒪[K]` is the maximal ideal `𝓂[K]`.
* `TauCeti.Huber.canonicalReductionEquivResidueField`: the canonical ring isomorphism
  `CanonicalReduction K ≃+* 𝓀[K]`.

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

open scoped NormedField

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- In an ultrametric normed field, the power-bounded subring equals the valuation ring `𝒪[K]`. -/
theorem powerBoundedSubring_eq_integer : powerBoundedSubring K = Valued.integer K := by
  ext x
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, Valued.integer,
    Valuation.mem_integer_iff]
  exact (NNReal.coe_le_coe (r₁ := ‖x‖₊) (r₂ := 1)).symm

/-- The canonical ring isomorphism `K° ≃+* 𝒪[K]` between the power-bounded subring and the
valuation ring of an ultrametric normed field. -/
noncomputable def powerBoundedSubringEquivInteger : powerBoundedSubring K ≃+* Valued.integer K :=
  RingEquiv.subringCongr (powerBoundedSubring_eq_integer K)

@[simp]
theorem coe_powerBoundedSubringEquivInteger (x : powerBoundedSubring K) :
    ((powerBoundedSubringEquivInteger K x : Valued.integer K) : K) = x := (rfl)

@[simp]
theorem coe_powerBoundedSubringEquivInteger_symm (x : Valued.integer K) :
    (((powerBoundedSubringEquivInteger K).symm x : powerBoundedSubring K) : K) = x := (rfl)

/-- Under `K° ≃+* 𝒪[K]`, the ideal `K°°` of topologically nilpotent elements corresponds to the
maximal ideal of `𝒪[K]`. -/
theorem map_topologicallyNilpotentIdeal_powerBoundedSubringEquivInteger :
    (topologicallyNilpotentIdeal K).map (powerBoundedSubringEquivInteger K : _ →+* _) =
      IsLocalRing.maximalIdeal (Valued.integer K) := by
  rw [Ideal.map_coe, ← Ideal.comap_symm]
  refine Ideal.ext fun x ↦ ?_
  rw [Ideal.mem_comap, mem_topologicallyNilpotentIdeal, coe_powerBoundedSubringEquivInteger_symm,
    IsTopologicallyNilpotent, tendsto_pow_atTop_nhds_zero_iff_norm_lt_one,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hint := Valuation.integer.integers (NormedField.valuation (K := K))
  have hle : ‖(x : K)‖ ≤ 1 :=
    (NNReal.coe_le_coe (r₁ := ‖(x : K)‖₊) (r₂ := 1)).mpr (x.2 : NormedField.valuation (x : K) ≤ 1)
  rw [hint.isUnit_iff_valuation_eq_one]
  exact ⟨fun hlt h1 ↦ hlt.ne (NNReal.coe_inj.mpr h1),
    fun hne ↦ hle.lt_of_ne fun h1 ↦ hne (NNReal.coe_inj.mp h1)⟩

/-- **The canonical reduction of an ultrametric normed field is isomorphic to its residue
field.** -/
noncomputable def canonicalReductionEquivResidueField :
    CanonicalReduction K ≃+* Valued.ResidueField K :=
  Ideal.quotientEquiv (topologicallyNilpotentIdeal K) (IsLocalRing.maximalIdeal (Valued.integer K))
    (powerBoundedSubringEquivInteger K)
    (map_topologicallyNilpotentIdeal_powerBoundedSubringEquivInteger K).symm

@[simp]
theorem canonicalReductionEquivResidueField_mk (x : powerBoundedSubring K) :
    canonicalReductionEquivResidueField K (Ideal.Quotient.mk _ x) =
      IsLocalRing.residue (Valued.integer K) (powerBoundedSubringEquivInteger K x) := (rfl)

@[simp]
theorem canonicalReductionEquivResidueField_symm_residue (x : Valued.integer K) :
    (canonicalReductionEquivResidueField K).symm (IsLocalRing.residue (Valued.integer K) x) =
      Ideal.Quotient.mk _ ((powerBoundedSubringEquivInteger K).symm x) := (rfl)

end NormedField

end TauCeti.Huber
