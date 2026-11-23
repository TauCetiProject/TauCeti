/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Examples: explicit time-dependent flows on the real line

Two explicit fields on the real line test the maximal time-dependent flow
`TauCeti.timeDependentFlowOf` and its domain `TauCeti.timeDependentFlowDomain`.

* For the field `X_t(y) = y²`, the flow is `φ_{s,t}(x) = x / (1 - (t - s) x)`, defined exactly
  when `(t - s) x < 1`. At `x = 1` and `s = 0` the solution has a pole at `t = 1`: it exists on
  `[0, 1)` but not at time `1`, so local existence alone does not give a flow through `[0, 1]`.
  The solution leaves every compact set before the pole, as the escape criterion
  `TauCeti.mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ico` requires. At `x = 0` the
  solution is constantly `0`.
* For the field `X_t(y) = t`, the flow is `φ_{s,t}(x) = x + (t² - s²) / 2`, defined at all times,
  and the two-time composition law adds the increments `(r² - s²) / 2` and `(t² - r²) / 2`.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.Examples.TimeDependentFlow

/-! ### The field `y ↦ y²` -/

/-- The time-independent field `y ↦ y²` on the real line. -/
def sqField : ℝ → (y : ℝ) → TangentSpace 𝓘(ℝ, ℝ) y := fun _ y ↦ (y ^ 2 : ℝ)

/-- The field `y ↦ y²` is jointly `C¹`. -/
private theorem contMDiff_sqField :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent 1
      (fun p : ℝ × ℝ ↦ (⟨p.2, sqField p.1 p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
  contMDiff_tangentBundle_mk_modelSpace contMDiff_snd
    ((contDiff_id.pow 2).contMDiff.comp contMDiff_snd)

/-- Where `(u - s) x < 1`, the curve `u ↦ x / (1 - (u - s) x)` solves `γ' = γ²`. -/
private theorem hasMFDerivAt_sqSolution {s x u : ℝ} (hu : (u - s) * x < 1) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u ↦ x / (1 - (u - s) * x)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (sqField u (x / (1 - (u - s) * x)))) := by
  have hne : 1 - (u - s) * x ≠ 0 := by linarith
  have hd : HasDerivAt (fun u ↦ 1 - (u - s) * x) (-x) u := by
    simpa using (((hasDerivAt_id u).sub_const s).mul_const x).const_sub 1
  have h : HasDerivAt (fun u ↦ x / (1 - (u - s) * x)) ((x / (1 - (u - s) * x)) ^ 2) u :=
    ((hasDerivAt_const u x).div hd hne).congr_deriv (by rw [div_pow]; ring)
  exact h.hasFDerivAt.hasMFDerivAt

/-- On an open interval containing `s` on which `(u - s) x < 1`, the flow of `y ↦ y²` from `x` at
time `s` is `x / (1 - (u - s) x)`. -/
private theorem timeDependentFlowOf_sqField_of_mem_Ioo {s x u a b : ℝ}
    (hab : ∀ v ∈ Ioo a b, (v - s) * x < 1) (hs : s ∈ Ioo a b) (hu : u ∈ Ioo a b) :
    timeDependentFlowOf sqField s u x = x / (1 - (u - s) * x) := by
  have h := timeDependentFlowOf_eq_of_hasMFDerivAt contMDiff_sqField
    (γ := fun u ↦ x / (1 - (u - s) * x)) (fun v hv ↦ hasMFDerivAt_sqSolution (hab v hv)) hs hu
  simpa using h

/-- If `(t - s) x < 1`, then `s` and `t` lie in an open interval on which `(u - s) x < 1`. -/
private theorem exists_Ioo_of_mul_lt_one {s t x : ℝ} (h : (t - s) * x < 1) :
    ∃ a b, s ∈ Ioo a b ∧ t ∈ Ioo a b ∧ ∀ u ∈ Ioo a b, (u - s) * x < 1 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have ht : 1 / x < t - s := (div_lt_iff_of_neg hx).2 h
    have hx' : 1 / x < 0 := one_div_neg.2 hx
    refine ⟨s + 1 / x, max s t + 1, ⟨by linarith, by linarith [le_max_left s t]⟩,
      ⟨by linarith, by linarith [le_max_right s t]⟩, fun u hu ↦ ?_⟩
    exact (div_lt_iff_of_neg hx).1 (by linarith [hu.1])
  · exact ⟨min s t - 1, max s t + 1, ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩,
      ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩, fun u _ ↦ by simp⟩
  · have ht : t - s < 1 / x := (lt_div_iff₀ hx).2 h
    have hx' : 0 < 1 / x := one_div_pos.2 hx
    refine ⟨min s t - 1, s + 1 / x, ⟨by linarith [min_le_left s t], by linarith⟩,
      ⟨by linarith [min_le_right s t], by linarith⟩, fun u hu ↦ ?_⟩
    exact (lt_div_iff₀ hx).1 (by linarith [hu.2])

/-- If `(u - s) x < 1` on an open interval `J` containing `s`, and the flow of `y ↦ y²` from `x` at
time `s` is defined at a time `u₀` in the closure of `J`, then `(1 - (u₀ - s) x) φ_{s,u₀}(x) = x`.
-/
private theorem mul_timeDependentFlowOf_sqField_eq {s x u₀ a b : ℝ}
    (hab : ∀ v ∈ Ioo a b, (v - s) * x < 1) (hs : s ∈ Ioo a b) (hu₀ : u₀ ∈ closure (Ioo a b))
    (hD : ((s, u₀), x) ∈ timeDependentFlowDomain sqField) :
    (1 - (u₀ - s) * x) * timeDependentFlowOf sqField s u₀ x = x := by
  have hc : ContinuousAt (fun u ↦ (1 - (u - s) * x) * timeDependentFlowOf sqField s u x) u₀ :=
    (by fun_prop : Continuous fun u : ℝ ↦ 1 - (u - s) * x).continuousAt.mul
      (hasMFDerivAt_timeDependentFlowOf contMDiff_sqField hD).continuousAt
  have himage : (fun u ↦ (1 - (u - s) * x) * timeDependentFlowOf sqField s u x) '' Ioo a b ⊆
      {x} := by
    rintro _ ⟨u, hu, rfl⟩
    have hne : 1 - (u - s) * x ≠ 0 := by linarith [hab u hu]
    simp only [mem_singleton_iff]
    rw [timeDependentFlowOf_sqField_of_mem_Ioo hab hs hu]
    field_simp
  simpa using closure_mono himage (hc.continuousWithinAt.mem_closure_image hu₀)

/-- Past the pole the flow of `y ↦ y²` is not defined: if `(t - s) x ≥ 1`, then the pole
`u₀ = s + 1 / x` lies between `s` and `t`, and the identity `(1 - (u - s) x) φ_{s,u}(x) = x` before
the pole would give `0 = x` at it. -/
private theorem notMem_timeDependentFlowDomain_sqField {s t x : ℝ} (hlt : 1 ≤ (t - s) * x) :
    ((s, t), x) ∉ timeDependentFlowDomain sqField := by
  intro h
  have hx : x ≠ 0 := by rintro rfl; simp at hlt; linarith
  set u₀ := s + 1 / x
  have hpole : (u₀ - s) * x = 1 := by simp [u₀, hx]
  have hss := mem_timeDependentFlowDomain_self_of_mem h
  rcases hx.lt_or_gt with hx | hx
  · have hu₀ : t ≤ u₀ ∧ u₀ < s := by
      have h1 : t - s ≤ 1 / x := (le_div_iff_of_neg hx).2 hlt
      have h2 : 1 / x < 0 := one_div_neg.2 hx
      constructor <;> linarith
    have hD : ((s, u₀), x) ∈ timeDependentFlowDomain sqField :=
      (ordConnected_setOf_mem_timeDependentFlowDomain s x).out h hss ⟨hu₀.1, hu₀.2.le⟩
    have hJ : ∀ v ∈ Ioo u₀ (s + 1), (v - s) * x < 1 := fun v hv ↦
      (div_lt_iff_of_neg hx).1 (by linarith [hv.1])
    have hcl : u₀ ∈ closure (Ioo u₀ (s + 1)) := by
      rw [closure_Ioo (by linarith)]
      exact left_mem_Icc.2 (by linarith)
    have heq := mul_timeDependentFlowOf_sqField_eq hJ ⟨hu₀.2, by linarith⟩ hcl hD
    rw [hpole, sub_self, zero_mul] at heq
    exact hx.ne heq.symm
  · have hu₀ : s < u₀ ∧ u₀ ≤ t := by
      have h1 : 1 / x ≤ t - s := (div_le_iff₀ hx).2 hlt
      have h2 : 0 < 1 / x := one_div_pos.2 hx
      constructor <;> linarith
    have hD : ((s, u₀), x) ∈ timeDependentFlowDomain sqField :=
      (ordConnected_setOf_mem_timeDependentFlowDomain s x).out hss h ⟨hu₀.1.le, hu₀.2⟩
    have hJ : ∀ v ∈ Ioo (s - 1) u₀, (v - s) * x < 1 := fun v hv ↦
      (lt_div_iff₀ hx).1 (by linarith [hv.2])
    have hcl : u₀ ∈ closure (Ioo (s - 1) u₀) := by
      rw [closure_Ioo (by linarith)]
      exact right_mem_Icc.2 (by linarith)
    have heq := mul_timeDependentFlowOf_sqField_eq hJ ⟨by linarith, hu₀.1⟩ hcl hD
    rw [hpole, sub_self, zero_mul] at heq
    exact hx.ne' heq.symm

/-- **The flow of `y ↦ y²` is defined exactly before the pole**: the solution through `x` at time
`s` exists at time `t` exactly when `(t - s) x < 1`. -/
theorem mem_timeDependentFlowDomain_sqField_iff {s t x : ℝ} :
    ((s, t), x) ∈ timeDependentFlowDomain sqField ↔ (t - s) * x < 1 := by
  refine ⟨fun h ↦ not_le.1 fun hlt ↦ notMem_timeDependentFlowDomain_sqField hlt h, fun h ↦ ?_⟩
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mul_lt_one h
  have hγ (u : ℝ) (hu : u ∈ Ioo a b) := hasMFDerivAt_sqSolution (s := s) (x := x) (hab u hu)
  simpa using mem_timeDependentFlowDomain_of_hasMFDerivAt (X := sqField) hγ hs ht

/-- **The flow of `y ↦ y²`** from time `s` to time `t` is `x ↦ x / (1 - (t - s) x)`, wherever
it is defined. -/
theorem timeDependentFlowOf_sqField {s t x : ℝ} (h : (t - s) * x < 1) :
    timeDependentFlowOf sqField s t x = x / (1 - (t - s) * x) := by
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mul_lt_one h
  exact timeDependentFlowOf_sqField_of_mem_Ioo hab hs ht

-- The solution of `y' = y²` through `1` at time `0` exists on `[0, 1)`, ...
example : ∀ t ∈ Ico (0 : ℝ) 1, ((0, t), 1) ∈ timeDependentFlowDomain sqField :=
  fun t ht ↦ mem_timeDependentFlowDomain_sqField_iff.2 (by simpa using ht.2)

-- ... but not at time `1`, where it has a pole: there is no flow through `[0, 1]`.
example : ((0, 1), 1) ∉ timeDependentFlowDomain sqField := by
  simp [mem_timeDependentFlowDomain_sqField_iff]

-- It leaves every compact set before the pole, as the escape criterion requires.
example {K : Set ℝ} (hK : IsCompact K) :
    ∃ t ∈ Ico (0 : ℝ) 1, timeDependentFlowOf sqField 0 t 1 ∉ K := by
  by_contra! h
  have h1 := mem_timeDependentFlowDomain_sqField_iff.1
    (mem_timeDependentFlowDomain_of_isCompact_of_mapsTo_Ico contMDiff_sqField hK zero_le_one
      fun t ht ↦ h t ht.2)
  norm_num at h1

-- The solution through `0` is constantly `0`.
example (s t : ℝ) : timeDependentFlowOf sqField s t 0 = 0 := by
  simp [timeDependentFlowOf_sqField]

/-! ### The field `X_t = t` -/

/-- The time-dependent field `X_t(y) = t` on the real line. -/
def clockField : ℝ → (y : ℝ) → TangentSpace 𝓘(ℝ, ℝ) y := fun t _ ↦ (t : ℝ)

/-- The field `X_t = t` is jointly `C¹`. -/
private theorem contMDiff_clockField :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent 1
      (fun p : ℝ × ℝ ↦ (⟨p.2, clockField p.1 p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
  contMDiff_tangentBundle_mk_modelSpace contMDiff_snd contMDiff_fst

/-- The curve `u ↦ x + (u² - s²) / 2` solves `γ' = u`. -/
private theorem hasMFDerivAt_clockSolution (s x u : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u ↦ x + (u ^ 2 - s ^ 2) / 2) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (clockField u (x + (u ^ 2 - s ^ 2) / 2))) := by
  have h : HasDerivAt (fun u ↦ x + (u ^ 2 - s ^ 2) / 2) u u := by
    simpa using (((hasDerivAt_pow 2 u).sub_const (s ^ 2)).div_const 2).const_add x
  exact h.hasFDerivAt.hasMFDerivAt

/-- **The flow of `X_t = t` is defined at all times.** -/
theorem timeDependentFlowDomain_clockField : timeDependentFlowDomain clockField = univ := by
  refine eq_univ_of_forall fun ⟨⟨s, t⟩, x⟩ ↦ ?_
  simpa using mem_timeDependentFlowDomain_of_hasMFDerivAt (X := clockField) (s := s) (t := t)
    (a := min s t - 1) (b := max s t + 1) (fun u _ ↦ hasMFDerivAt_clockSolution s x u)
    ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
    ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩

/-- **The flow of `X_t = t`** from time `s` to time `t` is `x ↦ x + (t² - s²) / 2`. -/
theorem timeDependentFlowOf_clockField (s t x : ℝ) :
    timeDependentFlowOf clockField s t x = x + (t ^ 2 - s ^ 2) / 2 := by
  simpa using timeDependentFlowOf_eq_of_forall_hasMFDerivAt contMDiff_clockField
    (hasMFDerivAt_clockSolution s x) s t

-- Flowing back from `t` to `s` undoes the flow from `s` to `t`.
example (s t x : ℝ) :
    timeDependentFlowOf clockField t s (timeDependentFlowOf clockField s t x) = x := by
  simp only [timeDependentFlowOf_clockField]
  ring

-- Composition through `r` adds the increments `(r² - s²) / 2` and `(t² - r²) / 2`.
example (r s t x : ℝ) :
    timeDependentFlowOf clockField r t (timeDependentFlowOf clockField s r x) =
      timeDependentFlowOf clockField s t x := by
  simp only [timeDependentFlowOf_clockField]
  ring

end TauCeti.Examples.TimeDependentFlow
