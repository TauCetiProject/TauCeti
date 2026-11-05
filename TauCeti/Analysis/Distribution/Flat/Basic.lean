/-
Copyright (c) 2026 The Tau Ceti Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti Contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Real normal flat mass in an open subset of a normed space

`ContinuousLinearMap.normalFlatMass T` is the infimum of `M(R) + M(S)` over real
normal decompositions `T = R + ∂S`. The fillings live in the same open set as `T`;
no compact-support constraint is imposed. This is not an integral-decomposition
flat mass. It is finite precisely on normal currents, and its completion is not
constructed here.

We prove nondegeneracy, the triangle inequality, real homogeneity, contraction
under boundary and open restriction, and the test-form estimate with the maximum
of the sup norms of `ω` and `dω`. These estimates allow flat approximation to be
compared with evaluation on smooth tests. Everything uses the existing continuous
real-linear maps on native test forms, allowing arbitrary real normed coefficient
and value spaces. The pointwise form norm is the native alternating operator norm,
hence the comass in an inner-product space. Boundary contraction is stated in positive
degree; degree-zero currents have zero boundary in the ordinary current complex.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.12 (the real flat norm).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open Distribution TestFunction TopologicalSpace Filter
open scoped Distributions ENNReal NNReal BoundedContinuousFunction Topology

namespace ContinuousLinearMap

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {k : ℕ}

/-- Extended real flat mass using normal residuals and normal fillings in `Ω`.
There is no compact-support or integrality constraint on the decomposition. -/
def normalFlatMass (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) : ℝ≥0∞ :=
  ⨅ (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V)
    (_ : IsNormal S) (_ : IsNormal (T - S ∘L extDerivCLM)),
    mass (T - S ∘L extDerivCLM) + mass S

variable (T U : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)

/-- The defining infimum over normal fillings and normal residuals. -/
theorem normalFlatMass_def : T.normalFlatMass =
    ⨅ (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V)
      (_ : IsNormal S) (_ : IsNormal (T - S ∘L extDerivCLM)),
      mass (T - S ∘L extDerivCLM) + mass S := (rfl)

/-- The infimum defining normal flat mass, in its universal lower-bound form. -/
theorem le_normalFlatMass_iff {a : ℝ≥0∞} : a ≤ T.normalFlatMass ↔
    ∀ (R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
      (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V),
      IsNormal R → IsNormal S → T = R + S ∘L extDerivCLM → a ≤ mass R + mass S := by
  simp only [normalFlatMass_def, le_iInf_iff]
  constructor
  · intro h R S hR hS heq
    have hres : T - S ∘L extDerivCLM = R := by rw [heq]; abel
    simpa only [hres] using h S hS (hres ▸ hR)
  · intro h S hS hR
    exact h _ S hR hS (by abel)

/-- Every normal decomposition gives an upper bound for flat mass. -/
theorem normalFlatMass_le_of_eq_add_comp_extDerivCLM
    {R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    {S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}
    (hR : IsNormal R) (hS : IsNormal S) (h : T = R + S ∘L extDerivCLM) :
    T.normalFlatMass ≤ mass R + mass S :=
  (T.le_normalFlatMass_iff.mp le_rfl) R S hR hS h

/-- A strict flat-mass bound is witnessed by an actual normal decomposition. -/
theorem normalFlatMass_lt_iff {c : ℝ≥0∞} : T.normalFlatMass < c ↔
    ∃ (R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V)
      (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V),
      IsNormal R ∧ IsNormal S ∧ T = R + S ∘L extDerivCLM ∧ mass R + mass S < c := by
  simp only [normalFlatMass_def, iInf_lt_iff]
  constructor
  · rintro ⟨S, hS, hR, hc⟩
    exact ⟨T - S ∘L extDerivCLM, S, hR, hS, by abel, hc⟩
  · rintro ⟨R, S, hR, hS, h, hc⟩
    have heq : T - S ∘L extDerivCLM = R := by rw [h]; abel
    exact ⟨S, hS, heq ▸ hR, by simpa only [heq] using hc⟩

/-- Flat mass is bounded by mass for a normal current. -/
theorem normalFlatMass_le_mass (hT : IsNormal T) : T.normalFlatMass ≤ mass T := by
  simpa using T.normalFlatMass_le_of_eq_add_comp_extDerivCLM hT
    (isNormal_zero (k := k + 1)) (by simp)

/-- The flat mass of zero is zero, in every nonnegative degree. -/
@[simp]
theorem normalFlatMass_zero :
    (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V).normalFlatMass = 0 := by
  apply le_antisymm _ zero_le
  simpa using (normalFlatMass_le_mass
    (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) isNormal_zero)

/-- A nonnormal current has no normal decomposition. -/
theorem normalFlatMass_of_not_isNormal (hT : ¬IsNormal T) : T.normalFlatMass = ⊤ := by
  apply top_unique
  refine T.le_normalFlatMass_iff.mpr fun R S hR hS heq => ?_
  exact False.elim (hT (heq ▸ hR.add hS.comp_extDerivCLM))

/-- Finiteness characterizes the domain of the real normal flat norm. -/
@[simp]
theorem normalFlatMass_ne_top_iff : T.normalFlatMass ≠ ⊤ ↔ IsNormal T := by
  refine ⟨fun h => by_contra fun hn => h (T.normalFlatMass_of_not_isNormal hn), fun h => ?_⟩
  exact ne_top_of_le_ne_top h.mass_ne_top (T.normalFlatMass_le_mass h)

/-- The flat mass satisfies the triangle inequality. -/
theorem normalFlatMass_add_le :
    (T + U).normalFlatMass ≤ T.normalFlatMass + U.normalFlatMass := by
  rw [← tsub_le_iff_right]
  refine T.le_normalFlatMass_iff.mpr fun R S hR hS hT => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine U.le_normalFlatMass_iff.mpr fun R' S' hR' hS' hU => ?_
  rw [tsub_le_iff_left]
  have hdecomp : T + U = (R + R') + (S + S') ∘L extDerivCLM := by
    rw [hT, hU, add_comp]
    abel
  calc
    (T + U).normalFlatMass ≤ mass (R + R') + mass (S + S') :=
      normalFlatMass_le_of_eq_add_comp_extDerivCLM _ (hR.add hR') (hS.add hS') hdecomp
    _ ≤ (mass R + mass R') + (mass S + mass S') := add_le_add mass_add_le mass_add_le
    _ = (mass R + mass S) + (mass R' + mass S') := by ac_rfl

/-- Evaluation is controlled by flat mass and both the test and its exterior derivative. -/
theorem enorm_apply_le_normalFlatMass_mul
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    ‖T ω‖ₑ ≤ T.normalFlatMass *
      max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ
        ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] F)‖ₑ := by
  let C := max ‖(ω : E →ᵇ (E [⋀^Fin k]→L[ℝ] F))‖ₑ
    ‖(extDerivCLM ω : E →ᵇ (E [⋀^Fin (k + 1)]→L[ℝ] F))‖ₑ
  by_cases hC : C = 0
  · have hω : ω = 0 := (toBoundedContinuousFunction_eq_zero ω).mp
      (enorm_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hC.le) bot_le))
    simp [hω]
  have hCtop : C ≠ ⊤ := by simp [C]
  apply (ENNReal.div_le_iff hC hCtop).mp
  refine T.le_normalFlatMass_iff.mpr fun R S _ _ heq => ?_
  apply (ENNReal.div_le_iff hC hCtop).mpr
  rw [heq, add_apply, comp_apply]
  calc
    ‖R ω + S (extDerivCLM ω)‖ₑ ≤ ‖R ω‖ₑ + ‖S (extDerivCLM ω)‖ₑ := enorm_add_le _ _
    _ ≤ mass R * C + mass S * C := add_le_add
      ((enorm_apply_le_mass_mul R ω).trans (mul_le_mul' le_rfl (le_max_left _ _)))
      ((enorm_apply_le_mass_mul S (extDerivCLM ω)).trans
        (mul_le_mul' le_rfl (le_max_right _ _)))
    _ = (mass R + mass S) * C := (add_mul _ _ _).symm

/-- Vanishing flat mass detects the zero current, including in degree zero. -/
@[simp]
theorem normalFlatMass_eq_zero_iff : T.normalFlatMass = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ normalFlatMass_zero⟩
  ext ω
  have hb := T.enorm_apply_le_normalFlatMass_mul ω
  simpa [h] using hb

/-- The one-sided rescaling estimate used to prove exact homogeneity. -/
private theorem normalFlatMass_smul_le (a : ℝ) :
    (a • T).normalFlatMass ≤ ‖a‖ₑ * T.normalFlatMass := by
  by_cases ha : a = 0
  · simp [ha]
  have ha0 : ‖a‖ₑ ≠ 0 := by simpa using ha
  apply (ENNReal.div_le_iff' ha0 enorm_ne_top).mp
  refine T.le_normalFlatMass_iff.mpr fun R S hR hS hT => ?_
  apply (ENNReal.div_le_iff' ha0 enorm_ne_top).mpr
  have h := normalFlatMass_le_of_eq_add_comp_extDerivCLM (a • T) (hR.smul a) (hS.smul a)
    (by rw [hT, smul_add, smul_comp])
  simpa only [FunLike.coe_smul, mass_smul, mul_add] using h

/-- Exact real homogeneity of the normal flat mass. -/
@[simp]
theorem normalFlatMass_smul (a : ℝ) :
    (a • T).normalFlatMass = ‖a‖ₑ * T.normalFlatMass := by
  by_cases ha : a = 0
  · simp [ha]
  refine le_antisymm (T.normalFlatMass_smul_le a) ?_
  have h := (a • T).normalFlatMass_smul_le a⁻¹
  have hnorm : ‖a‖ₑ * ‖a⁻¹‖ₑ = 1 := by rw [← enorm_mul, mul_inv_cancel₀ ha]; simp
  simpa [smul_smul, inv_mul_cancel₀ ha, ← mul_assoc, hnorm] using mul_le_mul' (le_refl ‖a‖ₑ) h

/-- Reversing a current preserves its flat mass. -/
@[simp]
theorem normalFlatMass_neg : (-T).normalFlatMass = T.normalFlatMass := by
  have h := T.normalFlatMass_smul (-1 : ℝ)
  rw [_root_.neg_one_smul ℝ T] at h
  simpa only [enorm_neg, enorm_one, one_mul] using h

/-- The flat mass of a difference is bounded by the sum of flat masses. -/
theorem normalFlatMass_sub_le :
    (T - U).normalFlatMass ≤ T.normalFlatMass + U.normalFlatMass := by
  simpa only [sub_eq_add_neg, normalFlatMass_neg] using normalFlatMass_add_le T (-U)

/-- Boundary is a contraction for the normal flat mass in positive degrees. -/
theorem normalFlatMass_comp_extDerivCLM_le
    (W : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) :
    (W ∘L extDerivCLM).normalFlatMass ≤ W.normalFlatMass := by
  refine W.le_normalFlatMass_iff.mpr fun R S hR _ heq => ?_
  have hb : W ∘L extDerivCLM = 0 + R ∘L extDerivCLM := by
    simp [heq, add_comp, comp_assoc, extDerivCLM_comp_extDerivCLM]
  exact (normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero hR hb).trans (by simp)

/-- Restriction to an open subset is a contraction; fillings are restricted as well.
This is distributional restriction, not restriction to a Borel set. -/
theorem normalFlatMass_comp_monoCLM_le {Ω' : Opens E} (h : Ω' ≤ Ω) :
    (T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)).normalFlatMass ≤
      T.normalFlatMass := by
  refine T.le_normalFlatMass_iff.mpr fun R S hR hS heq => ?_
  have hdecomp : T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      (R ∘L monoCLM ℝ) + (S ∘L monoCLM ℝ) ∘L extDerivCLM := by
    rw [comp_monoCLM_comp_extDerivCLM h, ← add_comp, heq]
  exact (normalFlatMass_le_of_eq_add_comp_extDerivCLM _
    (hR.comp_monoCLM h) (hS.comp_monoCLM h) hdecomp).trans
    (add_le_add (mass_comp_monoCLM_le h) (mass_comp_monoCLM_le h))

/-- Convergence in normal flat mass implies convergence on every fixed smooth test form.
No uniform support bound is needed for this implication. -/
theorem tendsto_apply_of_normalFlatMass_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    {Ts : ι → 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (h : Tendsto (fun i => (Ts i - T).normalFlatMass) l (𝓝 0))
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun i => Ts i ω) l (𝓝 (T ω)) := by
  rw [tendsto_iff_enorm_sub_tendsto_zero]
  have hb : Tendsto (fun i => (Ts i - T).normalFlatMass *
      max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ
        ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] F)‖ₑ) l (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const h (Or.inr (by finiteness))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => zero_le) (fun i => (Ts i - T).enorm_apply_le_normalFlatMass_mul ω)

end ContinuousLinearMap
