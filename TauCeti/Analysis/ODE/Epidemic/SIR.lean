/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.ODE.ScalarLinear
import TauCeti.Analysis.SpecialFunctions.Log.SubMulLog
import TauCeti.Topology.Order.Monotone.Convergence

/-!
# The Kermack–McKendrick SIR model

In the SIR model of an epidemic, `S` and `I` are the numbers of susceptible and infective
individuals; an encounter of a susceptible with an infective transmits the disease at rate `β`,
and infectives are removed at rate `γ`:

  `S' = -β S I`,  `I' = β S I - γ I`.

This file states the model as the vector field `TauCeti.sirField β γ` on `ℝ × ℝ`, whose solutions
on `[0, ∞)` (in the sense of Mathlib's `IsIntegralCurveOn`, with a one-sided derivative at `0`)
enter every statement as a hypothesis, and proves the final size relation: along a solution with
`β, γ > 0`, `S(0) > 0` and `I(0) > 0`, the epidemic dies out, `I(t) → 0`, and the number of
susceptibles that escape it is the unique `s ∈ (0, γ / β)` with
`s - (γ / β) log s = S(0) + I(0) - (γ / β) log S(0)`.

## Main definitions

* `TauCeti.sirField β γ`: the field `(S, I) ↦ (-β S I, β S I - γ I)`.

## Main results

* `TauCeti.sir_fst_eq_exp`, `TauCeti.sir_snd_eq_exp`: the explicit forms
  `S t = exp (-β ∫₀ᵗ I) S 0` and `I t = exp (∫₀ᵗ (β S - γ)) I 0`; consequently each of `S` and
  `I` stays positive (resp. nonnegative) if it starts positive (resp. nonnegative)
  (`TauCeti.sir_fst_pos`, `TauCeti.sir_snd_pos`, `TauCeti.sir_fst_nonneg`,
  `TauCeti.sir_snd_nonneg`).
* `TauCeti.sir_conserved`: `I + S - (γ / β) log S` is constant along a solution with `β ≠ 0` and
  `S(0) > 0`.
* `TauCeti.sir_fst_strictAntiOn`, `TauCeti.sir_add_antitoneOn`: `S` is strictly decreasing and
  `S + I` is nonincreasing.
* `TauCeti.sir_finalSize`: the final size relation.

## References

* W. O. Kermack and A. G. McKendrick, *A contribution to the mathematical theory of epidemics*,
  Proc. R. Soc. Lond. A 115 (1927), 700–721.
* H. Weiss, *The SIR model and the foundations of public health*, MATerials MATemàtics 2013,
  no. 3, Sections 2.2.1 and 2.2.2, Proposition 2.2 and equations (5) and (7).
-/

public section

open Filter Set Topology

namespace TauCeti

/-- The Kermack–McKendrick vector field for susceptibles `S = z.1` and infectives `I = z.2`:
`(S, I) ↦ (-β S I, β S I - γ I)`, with transmission rate `β` and removal rate `γ`. -/
def sirField (β γ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (-(β * z.1 * z.2), β * z.1 * z.2 - γ * z.2)

@[simp]
theorem sirField_fst (β γ : ℝ) (z : ℝ × ℝ) : (sirField β γ z).1 = -(β * z.1 * z.2) := (rfl)

@[simp]
theorem sirField_snd (β γ : ℝ) (z : ℝ × ℝ) : (sirField β γ z).2 = β * z.1 * z.2 - γ * z.2 := (rfl)

variable {β γ : ℝ} {z : ℝ → ℝ × ℝ} {t : ℝ}

/-- The susceptible coordinate of a solution solves `S' = -β S I`. -/
private theorem hasDerivWithinAt_sir_fst (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (ht : t ∈ Ici (0 : ℝ)) :
    HasDerivWithinAt (fun u ↦ (z u).1) (-(β * (z t).1 * (z t).2)) (Ici 0) t := by
  exact (hasFDerivAt_fst.comp_hasDerivWithinAt t (hz t ht)).congr_deriv (by simp)

/-- The infective coordinate of a solution solves `I' = β S I - γ I`. -/
private theorem hasDerivWithinAt_sir_snd (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (ht : t ∈ Ici (0 : ℝ)) :
    HasDerivWithinAt (fun u ↦ (z u).2) (β * (z t).1 * (z t).2 - γ * (z t).2) (Ici 0) t := by
  exact (hasFDerivAt_snd.comp_hasDerivWithinAt t (hz t ht)).congr_deriv (by simp)

/-- Along a solution of the SIR model on `[0, ∞)`, `S t = exp (-β ∫₀ᵗ I) S 0`. -/
theorem sir_fst_eq_exp (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0)) (ht : 0 ≤ t) :
    (z t).1 = Real.exp (-(β * ∫ u in 0..t, (z u).2)) * (z 0).1 := by
  have h := eq_exp_integral_smul_of_hasDerivWithinAt_smul ordConnected_Ici
    (g := fun u ↦ -(β * (z u).2))
    ((continuous_snd.comp_continuousOn hz.continuousOn).const_smul β).neg
    (fun u hu ↦ (hasDerivWithinAt_sir_fst hz hu).congr_deriv (by simp only [smul_eq_mul]; ring))
    (mem_Ici.2 le_rfl) (mem_Ici.2 ht)
  rwa [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, smul_eq_mul] at h

/-- Along a solution of the SIR model on `[0, ∞)`, `I t = exp (∫₀ᵗ (β S - γ)) I 0`. -/
theorem sir_snd_eq_exp (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0)) (ht : 0 ≤ t) :
    (z t).2 = Real.exp (∫ u in 0..t, (β * (z u).1 - γ)) * (z 0).2 := by
  have h := eq_exp_integral_smul_of_hasDerivWithinAt_smul ordConnected_Ici
    (g := fun u ↦ β * (z u).1 - γ)
    (((continuous_fst.comp_continuousOn hz.continuousOn).const_smul β).sub continuousOn_const)
    (fun u hu ↦ (hasDerivWithinAt_sir_snd hz hu).congr_deriv (by simp only [smul_eq_mul]; ring))
    (mem_Ici.2 le_rfl) (mem_Ici.2 ht)
  rwa [smul_eq_mul] at h

/-- The number of susceptibles stays positive along a solution that starts with `S(0) > 0`. -/
theorem sir_fst_pos (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (hS : 0 < (z 0).1) (ht : 0 ≤ t) : 0 < (z t).1 := by
  rw [sir_fst_eq_exp hz ht]
  positivity

/-- The number of infectives stays positive along a solution that starts with `I(0) > 0`. -/
theorem sir_snd_pos (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (hI : 0 < (z 0).2) (ht : 0 ≤ t) : 0 < (z t).2 := by
  rw [sir_snd_eq_exp hz ht]
  positivity

/-- The number of susceptibles stays nonnegative along a solution that starts with `S(0) ≥ 0`. -/
theorem sir_fst_nonneg (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (hS : 0 ≤ (z 0).1) (ht : 0 ≤ t) : 0 ≤ (z t).1 := by
  rw [sir_fst_eq_exp hz ht]
  positivity

/-- The number of infectives stays nonnegative along a solution that starts with `I(0) ≥ 0`. -/
theorem sir_snd_nonneg (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (hI : 0 ≤ (z 0).2) (ht : 0 ≤ t) : 0 ≤ (z t).2 := by
  rw [sir_snd_eq_exp hz ht]
  positivity

/-- **The conserved quantity of the SIR model.** Along a solution on `[0, ∞)` with `β ≠ 0` and
`S(0) > 0`, the quantity `I + S - (γ / β) log S` keeps its initial value. -/
theorem sir_conserved (hβ : β ≠ 0) (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (hS : 0 < (z 0).1) (ht : 0 ≤ t) :
    (z t).2 + (z t).1 - γ / β * Real.log (z t).1 =
      (z 0).2 + (z 0).1 - γ / β * Real.log (z 0).1 := by
  refine isPreconnected_Ici.eq_of_hasDerivWithinAt_zero
    (f := fun u ↦ (z u).2 + (z u).1 - γ / β * Real.log (z u).1) (fun u hu ↦ ?_) (mem_Ici.2 ht)
    (mem_Ici.2 le_rfl)
  have hSu := (sir_fst_pos hz hS hu).ne'
  refine (((hasDerivWithinAt_sir_snd hz hu).add (hasDerivWithinAt_sir_fst hz hu)).sub
    (((hasDerivWithinAt_sir_fst hz hu).log hSu).const_mul (γ / β))).congr_deriv ?_
  field_simp
  ring

/-- Along a solution of the SIR model on `[0, ∞)` with `β > 0`, `S(0) > 0` and `I(0) > 0`, the
number of susceptibles is strictly decreasing. -/
theorem sir_fst_strictAntiOn (hβ : 0 < β) (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (hS : 0 < (z 0).1) (hI : 0 < (z 0).2) : StrictAntiOn (fun t ↦ (z t).1) (Ici 0) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (continuous_fst.comp_continuousOn hz.continuousOn)
    (fun u hu ↦ (hasDerivWithinAt_sir_fst hz (interior_subset hu)).mono interior_subset)
    fun u hu ↦ ?_
  have hu : 0 ≤ u := interior_subset (s := Ici (0 : ℝ)) hu
  have := mul_pos (mul_pos hβ (sir_fst_pos hz hS hu)) (sir_snd_pos hz hI hu)
  linarith

/-- Along a solution of the SIR model on `[0, ∞)` with `γ ≥ 0` and `I(0) ≥ 0`, the number `S + I`
of individuals not yet removed is nonincreasing. -/
theorem sir_add_antitoneOn (hγ : 0 ≤ γ) (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0))
    (hI : 0 ≤ (z 0).2) : AntitoneOn (fun t ↦ (z t).1 + (z t).2) (Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    ((continuous_fst.comp_continuousOn hz.continuousOn).add
      (continuous_snd.comp_continuousOn hz.continuousOn))
    (fun u hu ↦ ((hasDerivWithinAt_sir_fst hz (interior_subset hu)).add
      (hasDerivWithinAt_sir_snd hz (interior_subset hu))).mono interior_subset)
    fun u hu ↦ ?_
  have := mul_nonneg hγ (sir_snd_nonneg hz hI (interior_subset (s := Ici (0 : ℝ)) hu))
  linarith

/-- Along a solution of the SIR model with `β, γ > 0`, `S(0) > 0` and `I(0) > 0`, the number of
susceptibles converges to a positive limit, at most `S(0)`. -/
private theorem sir_exists_tendsto_fst (hβ : 0 < β) (hγ : 0 < γ)
    (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0)) (hS : 0 < (z 0).1)
    (hI : 0 < (z 0).2) :
    ∃ s, 0 < s ∧ s ≤ (z 0).1 ∧ Tendsto (fun t ↦ (z t).1) atTop (𝓝 s) := by
  set C := (z 0).2 + (z 0).1 - γ / β * Real.log (z 0).1
  have hρ : 0 < γ / β := div_pos hγ hβ
  -- The conserved quantity bounds `log S` below, so `S` stays above `exp (-C / ρ)`.
  have hlow (t : Ici (0 : ℝ)) : Real.exp (-C / (γ / β)) ≤ (z t).1 := by
    have h := sir_conserved hβ.ne' hz hS t.property
    have hSt := sir_fst_pos hz hS t.property
    have hIt := sir_snd_pos hz hI t.property
    rw [← Real.exp_log hSt, Real.exp_le_exp, div_le_iff₀ hρ]
    nlinarith
  have hbdd : BddBelow ((fun t ↦ (z t).1) '' Ici 0) :=
    ⟨_, by rintro _ ⟨t, ht, rfl⟩; exact hlow ⟨t, ht⟩⟩
  refine ⟨_, (Real.exp_pos _).trans_le (le_ciInf hlow), ?_,
    tendsto_atTop_ciInf_of_antitoneOn_Ici (sir_fst_strictAntiOn hβ hz hS hI).antitoneOn hbdd⟩
  exact ciInf_le (f := fun t : Ici (0 : ℝ) ↦ (z t).1) (by simpa only [image_eq_range] using hbdd)
    ⟨0, le_rfl⟩

/-- Along a solution of the SIR model with `γ > 0`, `S(0) > 0` and `I(0) > 0`, the number of
infectives cannot tend to a positive limit: `S + I` would then decrease without bound. -/
private theorem sir_not_tendsto_snd_pos (hγ : 0 < γ)
    (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0)) (hS : 0 < (z 0).1)
    (hI : 0 < (z 0).2) {c : ℝ} (hc : 0 < c) (hlim : Tendsto (fun t ↦ (z t).2) atTop (𝓝 c)) :
    False := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 <|
    (hlim.eventually (lt_mem_nhds (half_lt_self hc))).and (eventually_ge_atTop 0)
  -- After time `T`, `I > c / 2`, so `S + I + (γ c / 2) t` is nonincreasing.
  set g : ℝ → ℝ := fun t ↦ (z t).1 + (z t).2 + γ * (c / 2) * t
  have hT0 : 0 ≤ T := (hT T le_rfl).2
  have hanti : AntitoneOn g (Ici T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici T)
      (f' := fun u ↦ -(β * (z u).1 * (z u).2) + (β * (z u).1 * (z u).2 - γ * (z u).2) +
        γ * (c / 2))
      (((continuous_fst.comp_continuousOn hz.continuousOn).add
        (continuous_snd.comp_continuousOn hz.continuousOn)).mono (Ici_subset_Ici.2 hT0) |>.add
        (continuousOn_const.mul continuousOn_id))
      (fun u hu ↦ ?_) fun u hu ↦ ?_
    · have hu0 : u ∈ Ici (0 : ℝ) := mem_Ici.2 (hT0.trans (interior_subset hu))
      exact (((hasDerivWithinAt_sir_fst hz hu0).add (hasDerivWithinAt_sir_snd hz hu0)).mono
        (interior_subset.trans (Ici_subset_Ici.2 hT0))).add
        (((hasDerivWithinAt_id u _).const_mul (γ * (c / 2))).congr_deriv (mul_one _))
    · have := mul_le_mul_of_nonneg_left (hT u (interior_subset hu)).1.le hγ.le
      linarith
  -- At a late enough time, `S + I` would be negative.
  set t := T + g T / (γ * (c / 2)) + 1
  have hgT : 0 ≤ g T := by
    have := sir_fst_pos hz hS hT0
    have := sir_snd_pos hz hI hT0
    positivity
  have hTt : T ≤ t := by
    have : 0 ≤ g T / (γ * (c / 2)) := by positivity
    linarith
  have hgt := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hTt) hTt
  have hct : γ * (c / 2) * t = γ * (c / 2) * (T + 1) + g T := by
    simp only [t]
    field_simp
    ring
  have := sir_fst_pos hz hS (hT0.trans hTt)
  have := sir_snd_pos hz hI (hT0.trans hTt)
  have : 0 ≤ γ * (c / 2) * (T + 1) := by positivity
  simp only [g] at hgt hct
  linarith

/-- **The final size of an epidemic.** Along a solution of the SIR model on `[0, ∞)` with
`β, γ > 0`, `S(0) > 0` and `I(0) > 0`, the number of infectives tends to `0`, and the number of
susceptibles tends to the unique `s ∈ (0, γ / β)` with
`s - (γ / β) log s = S(0) + I(0) - (γ / β) log S(0)`. -/
theorem sir_finalSize (hβ : 0 < β) (hγ : 0 < γ)
    (hz : IsIntegralCurveOn z (fun _ ↦ sirField β γ) (Ici 0)) (hS : 0 < (z 0).1)
    (hI : 0 < (z 0).2) :
    ∃ s ∈ Ioo 0 (γ / β),
      s - γ / β * Real.log s = (z 0).1 + (z 0).2 - γ / β * Real.log (z 0).1 ∧
      (∀ s' ∈ Ioo 0 (γ / β),
        s' - γ / β * Real.log s' = (z 0).1 + (z 0).2 - γ / β * Real.log (z 0).1 → s' = s) ∧
      Tendsto (fun t ↦ (z t).1) atTop (𝓝 s) ∧ Tendsto (fun t ↦ (z t).2) atTop (𝓝 0) := by
  obtain ⟨s, hs0, hsS, hSlim⟩ := sir_exists_tendsto_fst hβ hγ hz hS hI
  -- `S + I` is nonincreasing and positive, so it converges, and so does `I`; its limit is `0`.
  obtain ⟨L, hL⟩ : ∃ L, Tendsto (fun t ↦ (z t).1 + (z t).2) atTop (𝓝 L) :=
    ⟨_, tendsto_atTop_ciInf_of_antitoneOn_Ici (sir_add_antitoneOn hγ.le hz hI.le)
      ⟨0, by rintro _ ⟨t, ht, rfl⟩; exact (add_pos (sir_fst_pos hz hS ht)
        (sir_snd_pos hz hI ht)).le⟩⟩
  have hIlim' : Tendsto (fun t ↦ (z t).2) atTop (𝓝 (L - s)) :=
    (hL.sub hSlim).congr fun t ↦ by ring
  have hIlim : Tendsto (fun t ↦ (z t).2) atTop (𝓝 0) := by
    have hnn : 0 ≤ L - s := ge_of_tendsto hIlim' <| (eventually_ge_atTop 0).mono
      fun t ht ↦ (sir_snd_pos hz hI ht).le
    rcases hnn.eq_or_lt with h | h
    · rwa [← h] at hIlim'
    · exact (sir_not_tendsto_snd_pos hγ hz hS hI h hIlim').elim
  -- Passing to the limit in the conserved quantity gives the equation for `s`.
  have heq : s - γ / β * Real.log s = (z 0).1 + (z 0).2 - γ / β * Real.log (z 0).1 := by
    have hlim := (hIlim.add hSlim).sub ((hSlim.log hs0.ne').const_mul (γ / β))
    have hconst := tendsto_nhds_unique hlim <| tendsto_const_nhds.congr' <|
      (eventually_ge_atTop 0).mono fun t ht ↦ (sir_conserved hβ.ne' hz hS ht).symm
    linarith
  have hρ : 0 < γ / β := div_pos hγ hβ
  -- Since `I(0) > 0`, the value at `s` exceeds the value at `S(0) ≥ s`, which forces `s < γ / β`.
  have hsρ : s < γ / β := by
    by_contra! h
    have := Real.sub_mul_one_sub_div_le_sub_mul_log_sub_sub_mul_log hρ.le hs0 hS
    have : 0 ≤ ((z 0).1 - s) * (1 - γ / β / s) :=
      mul_nonneg (sub_nonneg.2 hsS) (sub_nonneg.2 ((div_le_one hs0).2 h))
    linarith
  exact ⟨s, ⟨hs0, hsρ⟩, heq,
    fun s' hs' h ↦ ((Real.strictAntiOn_sub_mul_log _).injOn.mono Ioo_subset_Ioc_self) hs'
      ⟨hs0, hsρ⟩ (h.trans heq.symm), hSlim, hIlim⟩

end TauCeti
