/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Measure
public import TauCeti.Analysis.Distribution.Support
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.Analysis.Distribution.TestFunction.SmulLeft

/-!
# Support and finiteness of mass

For a real-linear functional of locally finite mass, the support of its mass measure on the
open domain is exactly its distributional support intersected with that domain. In particular,
the complement of the distributional support is mass-null, and a test supported in a mass-null
set has zero evaluation. The comparison is on the open domain: the ambient distributional
support may also contain frontier points, where the mass measure need not be locally finite.

A linear functional with compact distributional support contained in its domain has finite
mass if and only if it has locally finite mass. This last statement also holds for normed
vector-valued functionals and needs neither continuity nor a measure on the ambient space.
It follows by multiplying tests by a single smooth cutoff equal to one near the support,
without enlarging their supremum norm. Local finiteness alone does not imply finite total mass.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (support and mass of currents).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.3
  (distributions with compact support).
-/

public section

open Set MeasureTheory TopologicalSpace Filter
open scoped Distributions Topology BoundedContinuousFunction

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {n : ℕ∞}

section Vanishing

variable {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) V] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V]

/-- Zero local mass means vanishing on every test supported in the set. The set need not be
open or measurable. -/
theorem localMass_eq_zero_iff_isVanishingOn (T : 𝓕) (U : Set E) :
    localMass T U = 0 ↔ IsVanishingOn T U := by
  constructor
  · intro h φ hφ
    have hbound := enorm_apply_le_localMass_mul T hφ
    simpa [h] using hbound
  · intro h
    exact le_antisymm (localMass_le_iff.2 fun φ hφ _ => by simp [h φ hφ]) bot_le

end Vanishing

section CompactSupport

variable [FiniteDimensional ℝ E] {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) V]
  [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V] {T : 𝓕}

/-- A compactly supported linear functional of locally finite mass has finite total mass,
provided its support is contained in the open domain. -/
theorem HasLocallyFiniteMass.mass_ne_top (hT : HasLocallyFiniteMass T)
    (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω) : mass T ≠ ⊤ := by
  obtain ⟨χ, hχ, hχ01⟩ := TestFunction.exists_eventually_eq_one (n := n) hc hΩ
  obtain ⟨C, hC, hTC⟩ := (hasLocallyFiniteMass_def.1 hT)
    (tsupport χ) χ.hasCompactSupport χ.tsupport_subset
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C))
    (mass_le_iff.2 fun φ hφ => ?_)
  have heq : T φ = T (TestFunction.smulLeftCLM χ.contDiff φ) := by
    apply map_eq_map_of_eventuallyEq T
    filter_upwards [hχ] with x hx
    simp [hx]
  have hprod : tsupport (TestFunction.smulLeftCLM χ.contDiff φ) ⊆ tsupport χ :=
    (TestFunction.tsupport_smulLeftCLM_subset χ.contDiff φ).trans inter_subset_left
  have hnorm : ‖(TestFunction.smulLeftCLM χ.contDiff φ : E →ᵇ F)‖ ≤ 1 := by
    refine (BoundedContinuousFunction.norm_le zero_le_one).2 fun x => ?_
    simpa [norm_smul, abs_of_nonneg (hχ01 x).1] using
      (mul_le_of_le_one_left (norm_nonneg (φ x)) (hχ01 x).2).trans (hφ x)
  rw [heq, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((hTC _ hprod).trans (mul_le_of_le_one_right hC hnorm))

/-- For a linear functional whose support is a compact subset of the domain, local and global
finiteness of mass are equivalent. -/
theorem hasLocallyFiniteMass_iff_mass_ne_top_of_isCompact_dsupport (T : 𝓕)
    (hc : IsCompact (dsupport T)) (hΩ : dsupport T ⊆ Ω) :
    HasLocallyFiniteMass T ↔ mass T ≠ ⊤ :=
  ⟨fun hT => hT.mass_ne_top hc hΩ, hasLocallyFiniteMass_of_mass_ne_top T⟩

end CompactSupport

section Measure

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) ℝ] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) ℝ]
  {T : 𝓕}

/-- An open set has zero mass measure exactly when the functional vanishes there. -/
theorem massMeasure_preimage_coe_eq_zero_iff (hT : HasLocallyFiniteMass T)
    {U : Set E} (hU : IsOpen U) :
    massMeasure T ((↑) ⁻¹' U) = 0 ↔ IsVanishingOn T U := by
  rw [massMeasure_preimage_coe hT hU, localMass_eq_zero_iff_isVanishingOn]

/-- On an open set, zero mass is equivalent to disjointness from the distributional support. -/
theorem massMeasure_preimage_coe_eq_zero_iff_disjoint (hT : HasLocallyFiniteMass T)
    {U : Set E} (hU : IsOpen U) :
    massMeasure T ((↑) ⁻¹' U) = 0 ↔ Disjoint U (dsupport T) := by
  rw [massMeasure_preimage_coe_eq_zero_iff hT hU,
    isVanishingOn_iff_disjoint_dsupport T hU]

/-- The support of the mass measure, on the open domain, is the distributional support restricted
to that domain. Ambient frontier points are not points of this measure space. -/
theorem support_massMeasure (hT : HasLocallyFiniteMass T) :
    (massMeasure T).support = (↑) ⁻¹' dsupport T := by
  ext x
  apply not_iff_not.1
  constructor
  · intro hx
    obtain ⟨U, ⟨hxU, hU⟩, hzero⟩ := (nhds_basis_opens x).notMem_measureSupport.1 hx
    have hU' : IsOpen ((↑) '' U : Set E) := Ω.isOpen.isOpenMap_subtype_val U hU
    have hpre : ((Subtype.val : Ω → E) ⁻¹' ((Subtype.val : Ω → E) '' U)) = U :=
      preimage_image_eq U Subtype.val_injective
    have hvan : IsVanishingOn T ((↑) '' U) :=
      (massMeasure_preimage_coe_eq_zero_iff hT hU').1 (by simpa only [hpre] using hzero)
    exact (notMem_dsupport_iff (x : E)).2 ⟨(↑) '' U, hvan, hU', mem_image_of_mem _ hxU⟩
  · intro hx
    obtain ⟨U, hvan, hU, hxU⟩ := (notMem_dsupport_iff (x : E)).1 hx
    exact Measure.notMem_support_iff_exists.2
      ⟨(↑) ⁻¹' U, (hU.preimage continuous_subtype_val).mem_nhds hxU,
        (massMeasure_preimage_coe_eq_zero_iff hT hU).2 hvan⟩

/-- The mass measure gives zero mass to the complement of the distributional support. -/
@[simp]
theorem massMeasure_compl_dsupport (hT : HasLocallyFiniteMass T) :
    massMeasure T ((↑) ⁻¹' dsupport T)ᶜ = 0 := by
  rw [← support_massMeasure hT]
  exact Measure.measure_compl_support_of_regular

/-- A test whose closed support has zero mass has zero evaluation. No openness of its support
is required. -/
theorem map_eq_zero_of_massMeasure_tsupport_eq_zero (hT : HasLocallyFiniteMass T)
    {φ : 𝓓^{n}(Ω, F)} (hφ : massMeasure T ((↑) ⁻¹' tsupport φ) = 0) : T φ = 0 := by
  have hzero : ∫⁻ x, ‖φ x‖ₑ ∂massMeasure T = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hφ] with x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  simpa [hzero] using enorm_apply_le_lintegral_massMeasure hT φ

end Measure

end Distribution
