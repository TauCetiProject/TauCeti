/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Extended flat mass with real normal decompositions

The extended flat mass of a Euclidean current is the infimum of `M(R) + M(S)` over
real normal decompositions `T = R + ∂S`. No support restriction is imposed on the
pieces. It is finite precisely for normal currents. In particular this is not the
integral-decomposition flat mass, nor a flat mass with prescribed filling supports.

The test-form estimate proves nondegeneracy without any finite-mass assumption on
the current. The triangle inequality, real homogeneity and boundary estimate give
the basic quantitative tools for comparing normal currents and their boundaries.
Degree zero uses the ordinary current complex: there is no boundary below degree zero.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.12 (flat seminorms).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6.
-/

public section

noncomputable section

open TopologicalSpace TestFunction ContinuousLinearMap Filter
open scoped Distributions ENNReal BoundedContinuousFunction Topology

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {k : ℕ}

/-- Extended flat mass using real normal remainder and filling currents, without support
constraints. This is distinct from the flat mass using integral decompositions. -/
def normalFlatMass (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) : ℝ≥0∞ :=
  ⨅ (R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
    (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V)
    (_ : IsNormal R) (_ : IsNormal S) (_ : T = R + S ∘L extDerivCLM), mass R + mass S

variable {T U : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}

/-- The infimum defining normal flat mass, in its universal lower-bound form. -/
theorem le_normalFlatMass_iff {a : ℝ≥0∞} : a ≤ normalFlatMass T ↔
    ∀ (R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
      (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V),
      IsNormal R → IsNormal S → T = R + S ∘L extDerivCLM → a ≤ mass R + mass S := by
  simp only [normalFlatMass, le_iInf_iff]

/-- A strict flat-mass bound is witnessed by an actual normal decomposition. -/
theorem normalFlatMass_lt_iff {a : ℝ≥0∞} : normalFlatMass T < a ↔
    ∃ (R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
      (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V),
      IsNormal R ∧ IsNormal S ∧ T = R + S ∘L extDerivCLM ∧ mass R + mass S < a := by
  simp only [normalFlatMass, iInf_lt_iff, exists_prop]

/-- Every admissible normal decomposition bounds the flat mass from above. -/
theorem normalFlatMass_le (R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
    (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V)
    (hR : IsNormal R) (hS : IsNormal S) (h : T = R + S ∘L extDerivCLM) :
    normalFlatMass T ≤ mass R + mass S :=
  iInf_le_of_le R <| iInf_le_of_le S <| iInf_le_of_le hR <| iInf_le_of_le hS <|
    iInf_le_of_le h le_rfl

/-- A normal current has flat mass at most its mass. -/
theorem IsNormal.normalFlatMass_le_mass (hT : IsNormal T) : normalFlatMass T ≤ mass T := by
  simpa using normalFlatMass_le T 0 hT isNormal_zero (by simp)

@[simp]
theorem normalFlatMass_zero :
    normalFlatMass (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) = 0 := by
  exact le_antisymm (by simpa using (IsNormal.normalFlatMass_le_mass
    (T := (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)) isNormal_zero)) bot_le

/-- Finite normal flat mass is equivalent to normality. No compact support is required. -/
theorem normalFlatMass_ne_top_iff : normalFlatMass T ≠ ⊤ ↔ IsNormal T := by
  constructor
  · intro h
    obtain ⟨R, S, hR, hS, heq, _⟩ := normalFlatMass_lt_iff.mp (lt_top_iff_ne_top.mpr h)
    exact heq ▸ hR.add hS.comp_extDerivCLM
  · intro hT
    exact ne_top_of_le_ne_top hT.mass_ne_top hT.normalFlatMass_le_mass

/-- Non-normal currents have infinite flat mass for normal decompositions. -/
@[simp]
theorem normalFlatMass_eq_top_iff : normalFlatMass T = ⊤ ↔ ¬ IsNormal T := by
  simpa only [not_not] using (not_congr (normalFlatMass_ne_top_iff (T := T)))

/-- The triangle inequality, including infinite flat masses. -/
theorem normalFlatMass_add_le : normalFlatMass (T + U) ≤ normalFlatMass T + normalFlatMass U := by
  rw [← tsub_le_iff_right]
  refine le_normalFlatMass_iff.mpr fun R S hR hS hT => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_normalFlatMass_iff.mpr fun R' S' hR' hS' hU => ?_
  rw [tsub_le_iff_left]
  have hdecomp : T + U = (R + R') + (S + S') ∘L extDerivCLM := by
    rw [hT, hU, add_comp]
    abel
  have hmassR : mass (R + R') ≤ mass R + mass R' := mass_add_le
  have hmassS : mass (S + S') ≤ mass S + mass S' := mass_add_le
  calc
    normalFlatMass (T + U) ≤ mass (R + R') + mass (S + S') :=
      normalFlatMass_le _ _ (hR.add hR') (hS.add hS') hdecomp
    _ ≤ (mass R + mass R') + (mass S + mass S') := add_le_add hmassR hmassS
    _ = (mass R + mass S) + (mass R' + mass S') := by ac_rfl

/-- Scaling a normal decomposition bounds the scaled flat mass. -/
private theorem normalFlatMass_smul_le (a : ℝ) :
    normalFlatMass (a • T) ≤ ‖a‖ₑ * normalFlatMass T := by
  by_cases ha : a = 0
  · simp [ha]
  have ha0 : ‖a‖ₑ ≠ 0 := by simpa using ha
  apply (ENNReal.div_le_iff' ha0 enorm_ne_top).mp
  refine le_normalFlatMass_iff.mpr fun R S hR hS hT => ?_
  apply (ENNReal.div_le_iff' ha0 enorm_ne_top).mpr
  have h := normalFlatMass_le (a • R) (a • S) (hR.smul a) (hS.smul a) (T := a • T)
    (by rw [hT, smul_add, smul_comp])
  simpa only [FunLike.coe_smul, mass_smul, mul_add] using h

/-- Real homogeneity of normal flat mass, also at zero and at infinite mass. -/
@[simp]
theorem normalFlatMass_smul (a : ℝ) : normalFlatMass (a • T) = ‖a‖ₑ * normalFlatMass T := by
  refine le_antisymm (normalFlatMass_smul_le a) ?_
  by_cases ha : a = 0
  · simp [ha]
  have h := normalFlatMass_smul_le (T := a • T) a⁻¹
  have hcancel : a⁻¹ • (a • T) = T := inv_smul_smul₀ ha T
  calc
    ‖a‖ₑ * normalFlatMass T ≤ ‖a‖ₑ * (‖a⁻¹‖ₑ * normalFlatMass (a • T)) :=
      mul_le_mul' le_rfl (by simpa only [hcancel] using h)
    _ = normalFlatMass (a • T) := by
      simp [← mul_assoc, -enorm_inv, ← enorm_mul, ha]

@[simp]
theorem normalFlatMass_neg : normalFlatMass (-T) = normalFlatMass T := by
  simpa using normalFlatMass_smul (T := T) (-1)

/-- The flat mass of a difference is bounded by the sum of flat masses. -/
theorem normalFlatMass_sub_le : normalFlatMass (T - U) ≤ normalFlatMass T + normalFlatMass U := by
  simpa only [sub_eq_add_neg, normalFlatMass_neg] using
    (normalFlatMass_add_le (T := T) (U := -U))

/-- The test-form bound for extended normal flat mass. The two supremum norms are finite,
but the flat mass may be infinite. -/
theorem enorm_apply_le_normalFlatMass_mul (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ‖T ω‖ₑ ≤ normalFlatMass T * max ‖(ω : E →ᵇ (E [⋀^Fin k]→L[ℝ] F))‖ₑ
      ‖(extDerivCLM ω : E →ᵇ (E [⋀^Fin (k + 1)]→L[ℝ] F))‖ₑ := by
  let C := max ‖(ω : E →ᵇ (E [⋀^Fin k]→L[ℝ] F))‖ₑ
    ‖(extDerivCLM ω : E →ᵇ (E [⋀^Fin (k + 1)]→L[ℝ] F))‖ₑ
  by_cases hC : C = 0
  · have hω : ω = 0 := (toBoundedContinuousFunction_eq_zero ω).mp
      (enorm_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hC.le) bot_le))
    simp [hω]
  have hCtop : C ≠ ⊤ := by simp [C]
  apply (ENNReal.div_le_iff hC hCtop).mp
  refine le_normalFlatMass_iff.mpr fun R S _ _ heq => ?_
  apply (ENNReal.div_le_iff hC hCtop).mpr
  rw [heq, add_apply, comp_apply]
  calc
    ‖R ω + S (extDerivCLM ω)‖ₑ ≤ ‖R ω‖ₑ + ‖S (extDerivCLM ω)‖ₑ := enorm_add_le _ _
    _ ≤ mass R * C + mass S * C := add_le_add
      ((enorm_apply_le_mass_mul R ω).trans (mul_le_mul' le_rfl (le_max_left _ _)))
      ((enorm_apply_le_mass_mul S (extDerivCLM ω)).trans
        (mul_le_mul' le_rfl (le_max_right _ _)))
    _ = (mass R + mass S) * C := (add_mul _ _ _).symm

/-- Normal flat mass separates all currents, not just normal currents. -/
@[simp]
theorem normalFlatMass_eq_zero_iff : normalFlatMass T = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ normalFlatMass_zero⟩
  ext ω
  exact enorm_eq_zero.mp (le_antisymm
    (by simpa only [h, zero_mul] using enorm_apply_le_normalFlatMass_mul T ω) bot_le)

/-- Taking the boundary does not increase normal flat mass. This is stated only in positive
degree; degree-zero currents have zero boundary in the ordinary current complex. -/
theorem normalFlatMass_comp_extDerivCLM_le
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    normalFlatMass (T ∘L extDerivCLM) ≤ normalFlatMass T := by
  refine le_normalFlatMass_iff.mpr fun R S hR _ heq => ?_
  have hb : T ∘L extDerivCLM = 0 + R ∘L extDerivCLM := by
    simp [heq, add_comp, comp_assoc, extDerivCLM_comp_extDerivCLM]
  exact (normalFlatMass_le 0 R isNormal_zero hR hb).trans (by simp)

/-- Restriction to an open subset does not increase normal flat mass. This is restriction
as a distribution, not restriction to a Borel set, whose boundary may have infinite mass. -/
theorem normalFlatMass_comp_monoCLM_le {Ω' : Opens E} (h : Ω' ≤ Ω) :
    normalFlatMass (T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ≤
      normalFlatMass T := by
  refine le_normalFlatMass_iff.mpr fun R S hR hS heq => ?_
  have hdecomp : T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      (R ∘L monoCLM ℝ) + (S ∘L monoCLM ℝ) ∘L extDerivCLM := by
    rw [comp_monoCLM_comp_extDerivCLM h, ← add_comp, heq]
  exact (normalFlatMass_le _ _ (hR.comp_monoCLM h) (hS.comp_monoCLM h) hdecomp).trans
    (add_le_add (mass_comp_monoCLM_le h) (mass_comp_monoCLM_le h))

/-- Flat convergence implies convergence on each fixed test form. No operator topology on
continuous linear maps is used for this weak-convergence statement. -/
theorem tendsto_apply_of_tendsto_normalFlatMass_sub_zero {ι : Type*} {l : Filter ι}
    {Ts : ι → 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (h : Tendsto (fun i => normalFlatMass (Ts i - T)) l (𝓝 0))
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) : Tendsto (fun i => Ts i ω) l (𝓝 (T ω)) := by
  rw [tendsto_iff_enorm_sub_tendsto_zero]
  have hlim := ENNReal.Tendsto.mul_const h (b :=
    max ‖(ω : E →ᵇ (E [⋀^Fin k]→L[ℝ] F))‖ₑ
      ‖(extDerivCLM ω : E →ᵇ (E [⋀^Fin (k + 1)]→L[ℝ] F))‖ₑ) (Or.inr (by finiteness))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hlim)
  · exact fun _ => bot_le
  · intro i
    exact enorm_apply_le_normalFlatMass_mul (Ts i - T) ω

end Distribution
