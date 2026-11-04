/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Normal

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
real-linear dual of native test forms, without introducing a second current carrier.
The pointwise form norm is the native alternating operator norm, hence the comass
in an inner-product space.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.12 (the real flat norm).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open Distribution TestFunction TopologicalSpace Filter
open scoped Distributions ENNReal NNReal BoundedContinuousFunction Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : Opens E} {k : ℕ}

/-- Extended real flat mass using normal residuals and normal fillings in `Ω`.
There is no compact-support or integrality constraint on the decomposition. -/
def normalFlatMass (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) : ℝ≥0∞ :=
  ⨅ (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (_ : IsNormal S) (_ : IsNormal (T - S ∘L extDerivCLM)),
    mass (T - S ∘L extDerivCLM) + mass S

variable (T U : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)

/-- The defining infimum over normal fillings and normal residuals. -/
theorem normalFlatMass_def : T.normalFlatMass =
    ⨅ (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ)
      (_ : IsNormal S) (_ : IsNormal (T - S ∘L extDerivCLM)),
      mass (T - S ∘L extDerivCLM) + mass S := (rfl)

/-- Every normal decomposition gives an upper bound for flat mass. -/
theorem normalFlatMass_le_of_eq_add_comp_extDerivCLM
    {R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    {S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (hR : IsNormal R) (hS : IsNormal S) (h : T = R + S ∘L extDerivCLM) :
    T.normalFlatMass ≤ mass R + mass S := by
  rw [normalFlatMass_def]
  have hres : T - S ∘L extDerivCLM = R := by rw [h]; abel
  exact iInf_le_of_le S (iInf_le_of_le hS (iInf_le_of_le (hres ▸ hR)
    (by rw [hres])))

/-- A strict flat-mass bound is witnessed by an actual normal decomposition. -/
theorem normalFlatMass_lt_iff {c : ℝ≥0∞} : T.normalFlatMass < c ↔
    ∃ (R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
      (S : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ),
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
    (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ).normalFlatMass = 0 := by
  apply le_antisymm _ zero_le
  simpa using (normalFlatMass_le_mass
    (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) isNormal_zero)

/-- A nonnormal current has no normal decomposition. -/
theorem normalFlatMass_of_not_isNormal (hT : ¬IsNormal T) : T.normalFlatMass = ⊤ := by
  rw [normalFlatMass_def]
  apply iInf_eq_top.2
  intro S
  apply iInf_eq_top.2
  intro hS
  apply iInf_eq_top.2
  intro hR
  exact False.elim (hT (by simpa using hR.add hS.comp_extDerivCLM))

/-- Finiteness characterizes the domain of the real normal flat norm. -/
@[simp]
theorem normalFlatMass_ne_top_iff : T.normalFlatMass ≠ ⊤ ↔ IsNormal T := by
  refine ⟨fun h => by_contra fun hn => h (T.normalFlatMass_of_not_isNormal hn), fun h => ?_⟩
  exact ne_top_of_le_ne_top h.mass_ne_top (T.normalFlatMass_le_mass h)

/-- The flat mass satisfies the triangle inequality. -/
theorem normalFlatMass_add_le :
    (T + U).normalFlatMass ≤ T.normalFlatMass + U.normalFlatMass := by
  simp_rw [normalFlatMass_def, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR =>
    le_iInf fun S' => le_iInf fun hS' => le_iInf fun hR' => ?_
  have hres : T + U - (S + S') ∘L extDerivCLM =
      (T - S ∘L extDerivCLM) + (U - S' ∘L extDerivCLM) := by
    simp only [add_comp]
    abel
  refine (iInf_le_of_le (S + S') (iInf_le_of_le (hS.add hS')
    (iInf_le_of_le (hres ▸ hR.add hR') le_rfl))).trans ?_
  rw [hres, FunLike.coe_add, FunLike.coe_add]
  exact (add_le_add mass_add_le mass_add_le).trans_eq (by ac_rfl)

/-- Evaluation is controlled by flat mass and both the test and its exterior derivative. -/
theorem enorm_apply_le_normalFlatMass_mul
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    ‖T ω‖ₑ ≤ T.normalFlatMass *
      max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖ₑ
        ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖ₑ := by
  by_cases hω : ω = 0
  · simp [hω]
  -- Multiplication preserves the infima over possibly empty normal-decomposition
  -- types only after the fixed test bound is known to be nonzero and finite.
  have hb : (ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hω
    apply TestFunction.ext
    intro x
    exact congrArg (fun f : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ => f x) h
  have hb' : ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖ₑ ≠ 0 := by
    rw [← ofReal_norm]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      ((norm_pos_iff (a := (ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ))).mpr hb))
  have hc : max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖ₑ
      ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖ₑ ≠ 0 :=
    ne_of_gt ((pos_iff_ne_zero.2 hb').trans_le (le_max_left _ _))
  rw [normalFlatMass_def]
  simp_rw [ENNReal.iInf_mul_of_ne hc (by finiteness)]
  refine le_iInf fun S => le_iInf fun _ => le_iInf fun _ => ?_
  have heq : T ω = (T - S ∘L extDerivCLM) ω + S (extDerivCLM ω) := by simp
  rw [heq, add_mul]
  exact (enorm_add_le _ _).trans (add_le_add
    ((enorm_apply_le_mass_mul (T - S ∘L extDerivCLM) ω).trans
      (mul_le_mul' le_rfl (le_max_left _ _)))
    ((enorm_apply_le_mass_mul S (extDerivCLM ω)).trans
      (mul_le_mul' le_rfl (le_max_right _ _))))

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
  have ha' : ‖a‖ₑ ≠ 0 := by simpa using ha
  conv_rhs => rw [normalFlatMass_def]
  simp_rw [ENNReal.mul_iInf_of_ne ha' enorm_ne_top]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR => ?_
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM (a • T) (hR.smul a) (hS.smul a)
    (by simp [smul_sub])).trans_eq ?_
  simp [mass_smul, mul_add]

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

/-- Boundary is a contraction for the normal flat mass in positive degrees. -/
theorem normalFlatMass_comp_extDerivCLM_le
    (V : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (V ∘L extDerivCLM).normalFlatMass ≤ V.normalFlatMass := by
  conv_rhs => rw [normalFlatMass_def]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR => ?_
  have heq : V ∘L extDerivCLM = 0 + (V - S ∘L extDerivCLM) ∘L extDerivCLM := by
    simp [sub_comp, comp_assoc, extDerivCLM_comp_extDerivCLM]
  simpa using (normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero hR heq).trans
    (by simp)

/-- Restriction to an open subset is a contraction; fillings are restricted as well. -/
theorem normalFlatMass_comp_monoCLM_le {Ω' : Opens E} (h : Ω' ≤ Ω) :
    (T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _)).normalFlatMass ≤
      T.normalFlatMass := by
  conv_rhs => rw [normalFlatMass_def]
  refine le_iInf fun S => le_iInf fun hS => le_iInf fun hR => ?_
  have heq : T ∘L (monoCLM ℝ : 𝓓(Ω', E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _) =
      (T - S ∘L extDerivCLM) ∘L monoCLM ℝ +
        (S ∘L monoCLM ℝ) ∘L extDerivCLM := by
    rw [comp_monoCLM_comp_extDerivCLM h, sub_comp]
    abel
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM _
    (hR.comp_monoCLM h) (hS.comp_monoCLM h) heq).trans ?_
  simp only [coe_comp, mass_comp_monoCLM h]
  exact add_le_add localMass_le_mass localMass_le_mass

/-- Convergence in normal flat mass implies convergence on every fixed smooth test form.
No uniform support bound is needed for this implication. -/
theorem tendsto_apply_of_normalFlatMass_sub_tendsto_zero {ι : Type*} {l : Filter ι}
    {Ts : ι → 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ}
    (h : Tendsto (fun i => (Ts i - T).normalFlatMass) l (𝓝 0))
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    Tendsto (fun i => Ts i ω) l (𝓝 (T ω)) := by
  rw [tendsto_iff_enorm_sub_tendsto_zero]
  have hb : Tendsto (fun i => (Ts i - T).normalFlatMass *
      max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖ₑ
        ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖ₑ) l (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const h (Or.inr (by finiteness))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => zero_le) (fun i => (Ts i - T).enorm_apply_le_normalFlatMass_mul ω)

end ContinuousLinearMap
