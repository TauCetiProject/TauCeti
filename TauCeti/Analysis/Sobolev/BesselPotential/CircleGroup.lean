/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The group of circle-valued maps of Sobolev class `H^s`, `s > n / 2`

Let `E` be a finite-dimensional real inner product space of dimension `n` and let `s > n / 2`.
The circle-valued maps `u = 1 + h` with `h ∈ H^s(E; ℂ)` and `|u| = 1` on the continuous
representative form a group under pointwise multiplication (`TauCeti.sobolevCircleGroup`). This is
the Sobolev completion of the gauge group of a Hermitian line bundle over `E` with a fixed
trivialization at infinity: the Banach gauge group `G_(k+1)` of framed plane vortices is the case
`E = ℂ`, `s = k + 1`.

A map `u : E → Circle` lies in `sobolevCircleGroup E s hs` when it is continuous and the two real
coordinates `Re u - 1` and `Im u` of `h = u - 1` agree almost everywhere with `L²` functions in
`H^s` (`TemperedDistribution.realSobolevSubmodule`). Using the real coordinates of the target
`ℂ = ℝ²` is the convention of the vortex field space `TauCeti.Vortex.sobolevFields`; the complex
function `h` then lies in `H^s(E; ℂ)` (`TauCeti.exists_memSobolev_ae_eq_coe_sub_one`).

* Closure under multiplication is the algebra property of `H^s`, `s > n / 2`
  (`TemperedDistribution.exists_mem_realSobolevSubmodule_ae_eq_mul`): in the coordinates
  `a = Re u - 1`, `c = Im u`, `b = Re v - 1`, `d = Im v`,

  `Re (u v) - 1 = a b + a + b - c d`,    `Im (u v) = a d + d + c b + c`.

* Closure under inversion uses `u⁻¹ = conj u`, so `Re u⁻¹ - 1 = Re u - 1` and `Im u⁻¹ = - Im u`.
  No division and no logarithm of `u` is needed.
* Every element tends to one at infinity (`TauCeti.tendsto_cocompact_of_mem_sobolevCircleGroup`).
  This follows from the Sobolev embedding `H^s ⊆ C₀` and the continuity of `u`, which makes `u`
  itself the continuous representative.
* Smooth maps with `u - 1` compactly supported lie in the group for every `s`
  (`TauCeti.mem_sobolevCircleGroup_of_hasCompactSupport`), in particular `exp (i f)` for smooth
  compactly supported real `f` (`TauCeti.exp_comp_mem_sobolevCircleGroup`).

The group is defined as a subgroup of all maps `E → Circle`, with no Banach manifold structure;
its topology, charts and actions on Sobolev fields are not constructed here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Proposition 3.7 (the algebra property).
-/

public section

noncomputable section

open MeasureTheory Filter Module Topology Complex TemperedDistribution
open scoped SchwartzMap ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace TauCeti

variable (E) in
/-- **The group of circle-valued `H^s` maps**, `s > dim E / 2`. It consists of the continuous
maps `u : E → Circle` such that `h = u - 1` lies in `H^s(E; ℂ)`, in real coordinates: `Re u - 1`
and `Im u` agree almost everywhere with real `L²` functions in `H^s`. For `E = ℂ` and `s = k + 1`
this is the Banach gauge group `G_(k+1)` of framed plane vortices. -/
def sobolevCircleGroup (s : ℝ) (hs : finrank ℝ E < 2 * s) : Subgroup (E → Circle) where
  carrier := {u | Continuous u ∧
    (∃ g ∈ realSobolevSubmodule E s 2, g =ᵐ[volume] fun x ↦ (u x : ℂ).re - 1) ∧
    ∃ g ∈ realSobolevSubmodule E s 2, g =ᵐ[volume] fun x ↦ (u x : ℂ).im}
  one_mem' :=
    ⟨continuous_const, ⟨0, zero_mem _, .of_forall fun x ↦ by simp⟩,
      ⟨0, zero_mem _, .of_forall fun x ↦ by simp⟩⟩
  mul_mem' := by
    rintro u v ⟨hu, ha, hc⟩ ⟨hv, hb, hd⟩
    -- With `a = Re u - 1`, `c = Im u`, `b = Re v - 1`, `d = Im v`, the coordinates of `u v` are
    -- `Re (u v) - 1 = a b + a + b - c d` and `Im (u v) = a d + d + c b + c`.
    refine ⟨hu.mul hv, exists_mem_realSobolevSubmodule_ae_eq_congr
      (exists_mem_realSobolevSubmodule_ae_eq_add (exists_mem_realSobolevSubmodule_ae_eq_add
        (exists_mem_realSobolevSubmodule_ae_eq_add
          (exists_mem_realSobolevSubmodule_ae_eq_mul_of_exists hs ha hb) ha) hb)
        (exists_mem_realSobolevSubmodule_ae_eq_neg
          (exists_mem_realSobolevSubmodule_ae_eq_mul_of_exists hs hc hd))) fun x ↦ ?_,
      exists_mem_realSobolevSubmodule_ae_eq_congr
      (exists_mem_realSobolevSubmodule_ae_eq_add (exists_mem_realSobolevSubmodule_ae_eq_add
        (exists_mem_realSobolevSubmodule_ae_eq_add
          (exists_mem_realSobolevSubmodule_ae_eq_mul_of_exists hs ha hd) hd)
          (exists_mem_realSobolevSubmodule_ae_eq_mul_of_exists hs hc hb)) hc) fun x ↦ ?_⟩ <;>
    · simp only [Pi.mul_apply, Circle.coe_mul, mul_re, mul_im]
      ring
  inv_mem' := by
    rintro u ⟨hu, ha, hc⟩
    refine ⟨hu.inv, exists_mem_realSobolevSubmodule_ae_eq_congr ha fun x ↦ ?_,
      exists_mem_realSobolevSubmodule_ae_eq_congr (exists_mem_realSobolevSubmodule_ae_eq_neg hc)
        fun x ↦ ?_⟩ <;>
    simp

variable {s : ℝ} {hs : finrank ℝ E < 2 * s} {u : E → Circle}

/-- Membership in `sobolevCircleGroup`: continuity, and `Re u - 1`, `Im u` agree almost
everywhere with real `L²` functions in `H^s`. -/
@[simp]
theorem mem_sobolevCircleGroup :
    u ∈ sobolevCircleGroup E s hs ↔ Continuous u ∧
      (∃ g ∈ realSobolevSubmodule E s 2, g =ᵐ[volume] fun x ↦ (u x : ℂ).re - 1) ∧
      ∃ g ∈ realSobolevSubmodule E s 2, g =ᵐ[volume] fun x ↦ (u x : ℂ).im :=
  Iff.rfl

/-- Elements of `sobolevCircleGroup` are continuous. -/
theorem continuous_of_mem_sobolevCircleGroup (hu : u ∈ sobolevCircleGroup E s hs) :
    Continuous u :=
  (mem_sobolevCircleGroup.1 hu).1

/-- The groups `sobolevCircleGroup E s hs` decrease as the Sobolev order `s` increases. -/
theorem sobolevCircleGroup_mono {s' : ℝ} (hs' : finrank ℝ E < 2 * s') (h : s' ≤ s) :
    sobolevCircleGroup E s hs ≤ sobolevCircleGroup E s' hs' := by
  have hmono : ∀ g, g ∈ realSobolevSubmodule E s 2 → g ∈ realSobolevSubmodule E s' 2 :=
    fun _ hg ↦ mem_realSobolevSubmodule.2 ((mem_realSobolevSubmodule.1 hg).mono h)
  intro u hu
  obtain ⟨hu, ⟨a, ha, hae⟩, ⟨c, hc, hce⟩⟩ := mem_sobolevCircleGroup.1 hu
  exact mem_sobolevCircleGroup.2 ⟨hu, ⟨a, hmono a ha, hae⟩, ⟨c, hmono c hc, hce⟩⟩

/-- **The complex form of `sobolevCircleGroup`.** For `u` in the group, `h = u - 1` agrees almost
everywhere with an `L²` function in the complex Bessel-potential space `H^s(E; ℂ)`. -/
theorem exists_memSobolev_ae_eq_coe_sub_one (hu : u ∈ sobolevCircleGroup E s hs) :
    ∃ h : Lp ℂ 2 (volume : Measure E), MemSobolev s 2 (h : 𝓢'(E, ℂ)) ∧
      h =ᵐ[volume] fun x ↦ (u x : ℂ) - 1 := by
  obtain ⟨-, ⟨a, ha, hae⟩, ⟨c, hc, hce⟩⟩ := mem_sobolevCircleGroup.1 hu
  set A := ofRealCLM.compLp (p := 2) (μ := volume) a
  set C := ofRealCLM.compLp (p := 2) (μ := volume) c
  refine ⟨A + I • C, ?_, ?_⟩
  · rw [← Lp.toTemperedDistributionCLM_apply, map_add, map_smul]
    exact (mem_realSobolevSubmodule.1 ha).add ((mem_realSobolevSubmodule.1 hc).smul I)
  · filter_upwards [Lp.coeFn_add A (I • C), Lp.coeFn_smul I C,
      ofRealCLM.coeFn_compLp (p := 2) (μ := volume) a,
      ofRealCLM.coeFn_compLp (p := 2) (μ := volume) c, hae, hce] with x h₁ h₂ h₃ h₄ h₅ h₆
    rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, h₃, h₄, ofRealCLM_apply, ofRealCLM_apply, h₅, h₆,
      smul_eq_mul]
    apply Complex.ext <;> simp

/-- **Elements of `sobolevCircleGroup` tend to one at infinity.** By the Sobolev embedding
`H^s ⊆ C₀`, `s > dim E / 2`, the continuous coordinates `Re u - 1` and `Im u` tend to zero. -/
theorem tendsto_cocompact_of_mem_sobolevCircleGroup (hu : u ∈ sobolevCircleGroup E s hs) :
    Tendsto u (cocompact E) (𝓝 1) := by
  obtain ⟨hcont, ⟨a, ha, hae⟩, ⟨c, hc, hce⟩⟩ := mem_sobolevCircleGroup.1 hu
  have hcoe : Continuous fun x ↦ (u x : ℂ) := continuous_subtype_val.comp hcont
  have hre := tendsto_cocompact_of_ae_eq_of_mem_realSobolevSubmodule hs
    ((continuous_re.comp hcoe).sub continuous_const) ha hae
  have him := tendsto_cocompact_of_ae_eq_of_mem_realSobolevSubmodule hs
    (continuous_im.comp hcoe) hc hce
  have h : Tendsto (fun x ↦ (u x : ℂ)) (cocompact E) (𝓝 1) := by
    have h₁ := ((continuous_ofReal.tendsto 0).comp hre).add_const 1 |>.add
      (((continuous_ofReal.tendsto 0).comp him).mul_const I)
    simp only [Function.comp_def, ofReal_zero, zero_add, zero_mul, add_zero] at h₁
    refine h₁.congr fun x ↦ ?_
    apply Complex.ext <;> simp
  exact Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2 h

/-- **Smooth compactly supported elements.** A smooth map `u : E → Circle` with `u - 1`
compactly supported lies in `sobolevCircleGroup E s hs` for every `s`. -/
theorem mem_sobolevCircleGroup_of_hasCompactSupport (hu : ContDiff ℝ ∞ fun x ↦ (u x : ℂ))
    (hc : HasCompactSupport fun x ↦ (u x : ℂ) - 1) : u ∈ sobolevCircleGroup E s hs := by
  have hcont : Continuous u :=
    Topology.IsInducing.subtypeVal.continuous_iff.2 hu.continuous
  have hre : (fun x ↦ (u x : ℂ).re - 1) = re ∘ fun x ↦ (u x : ℂ) - 1 := funext fun x ↦ by simp
  have him : (fun x ↦ (u x : ℂ).im) = im ∘ fun x ↦ (u x : ℂ) - 1 := funext fun x ↦ by simp
  refine mem_sobolevCircleGroup.2 ⟨hcont, ?_, ?_⟩
  · rw [hre]
    exact exists_mem_realSobolevSubmodule_ae_eq_of_hasCompactSupport
      (reCLM.contDiff.comp (hu.sub contDiff_const)) (hc.comp_left zero_re) s 2
  · rw [him]
    exact exists_mem_realSobolevSubmodule_ae_eq_of_hasCompactSupport
      (imCLM.contDiff.comp (hu.sub contDiff_const)) (hc.comp_left zero_im) s 2

/-- **Exponentials of smooth compactly supported phases.** For a smooth compactly supported real
function `f`, the map `x ↦ exp (i f x)` lies in `sobolevCircleGroup E s hs` for every `s`. -/
theorem exp_comp_mem_sobolevCircleGroup {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : Circle.exp ∘ f ∈ sobolevCircleGroup E s hs := by
  refine mem_sobolevCircleGroup_of_hasCompactSupport ?_ ?_
  · simp only [Function.comp_apply, Circle.coe_exp]
    exact (ofRealCLM.contDiff.comp hf).mul contDiff_const |>.cexp
  · have h : (fun x ↦ ((Circle.exp ∘ f) x : ℂ) - 1) = (fun t : ℝ ↦ (Circle.exp t : ℂ) - 1) ∘ f :=
      rfl
    rw [h]
    exact hc.comp_left (by simp)

end TauCeti
