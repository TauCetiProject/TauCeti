/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Local power coordinates for a holomorphic germ

A holomorphic function whose difference from its value at a point has finite positive order `m`
is, after subtracting that value, the `m`th power of a biholomorphic coordinate centered at
the point. The coordinate and its inverse are analytic on their domains, and the power identity
holds throughout the coordinate domain, which can be chosen inside any prescribed neighbourhood.
This is the planar local model for ramification of holomorphic maps between Riemann surfaces.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §2, the local normal form theorem.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter II, §4.
-/

public noncomputable section

open Filter Set Topology

namespace AnalyticAt

/-- A holomorphic germ of finite positive order after subtracting its value admits a centered
biholomorphic coordinate in which that difference is exactly a power. Both directions of the
coordinate are analytic, and its source lies inside any prescribed neighbourhood of the point. -/
theorem exists_openPartialHomeomorph_sub_eq_pow {f : ℂ → ℂ} {z₀ : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f z₀) (hm : 0 < m)
    (horder : analyticOrderAt (fun z ↦ f z - f z₀) z₀ = m)
    {W : Set ℂ} (hW : W ∈ 𝓝 z₀) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ e.source ∧ e z₀ = 0 ∧ e.source ⊆ W ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      ∀ z ∈ e.source, f z - f z₀ = e z ^ m := by
  -- Absorb the nonvanishing factor into a root; the resulting coordinate has nonzero derivative.
  obtain ⟨g, hg, hg0, hfg⟩ :=
    (hf.sub analyticAt_const).analyticOrderAt_eq_natCast.mp horder
  obtain ⟨h, hh, hgh⟩ := (TauCeti.exists_eventuallyEq_pow_iff_dvd hg hm.ne').2
    (by rw [hg.analyticOrderAt_eq_zero.mpr hg0]; exact dvd_zero _)
  have hh0 : h z₀ ≠ 0 := by
    intro hz
    exact hg0 (by simpa [hz, hm.ne'] using hgh.self_of_nhds)
  let ψ : ℂ → ℂ := (fun z ↦ z - z₀) * h
  have hψ : AnalyticAt ℂ ψ z₀ := (analyticAt_id.sub analyticAt_const).mul hh
  have hψ0 : ψ z₀ = 0 := by simp [ψ]
  have hψd : deriv ψ z₀ ≠ 0 := by
    have hd := ((hasDerivAt_id z₀).sub_const z₀).mul hh.differentiableAt.hasDerivAt
    have heq : deriv ψ z₀ = h z₀ := by simpa [ψ, Pi.mul_apply] using hd.deriv
    rwa [heq]
  have hpow : ∀ᶠ z in 𝓝 z₀, f z - f z₀ = ψ z ^ m := by
    filter_upwards [hfg, hgh] with z hz hz'
    simp only [Pi.sub_apply] at hz
    simp only [hz, hz', smul_eq_mul, ψ, Pi.mul_apply, mul_pow]
  let e₀ := (hψ.hasStrictDerivAt.hasStrictFDerivAt_equiv hψd).toOpenPartialHomeomorph ψ
  have he₀ : (e₀ : ℂ → ℂ) = ψ :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe _
  have hz₀ : z₀ ∈ e₀.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hinv : AnalyticAt ℂ e₀.symm (ψ z₀) := by
    rw [← he₀]
    apply e₀.analyticAt_symm' hz₀ (he₀ ▸ hψ)
    simpa only [he₀] using
      (hψ.hasStrictDerivAt.hasStrictFDerivAt_equiv hψd).hasFDerivAt.fderiv
  -- Shrink simultaneously for the power identity and analyticity of both coordinate directions.
  have hnhds : ∀ᶠ z in 𝓝 z₀,
      AnalyticAt ℂ ψ z ∧ AnalyticAt ℂ e₀.symm (ψ z) ∧ f z - f z₀ = ψ z ^ m :=
    hψ.eventually_analyticAt.and
      ((hψ.continuousAt.eventually hinv.eventually_analyticAt).and hpow)
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp (inter_mem hnhds hW)
  let e := e₀.restr U
  have hes : e.source = e₀.source ∩ U := e₀.restr_source' U hUopen
  have he : (e : ℂ → ℂ) = ψ := by
    funext z
    rw [OpenPartialHomeomorph.restr_apply]
    exact congrFun he₀ z
  have hei : (e.symm : ℂ → ℂ) = e₀.symm := by simp [e]
  refine ⟨e, by rw [hes]; exact ⟨hz₀, hzU⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he, hψ0]
  · intro z hz
    exact (hUsub ((hes ▸ hz).2)).2
  · intro z hz
    rw [he]
    exact (hUsub ((hes ▸ hz).2)).1.1
  · intro w hw
    have hz := e.map_target hw
    have hza := (hUsub ((hes ▸ hz).2)).1.2.1
    rw [← he, e.right_inv hw] at hza
    rw [hei]
    exact hza
  · intro z hz
    rw [he]
    exact (hUsub ((hes ▸ hz).2)).1.2.2

end AnalyticAt
