/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Inverse
public import TauCeti.Analysis.Complex.BranchLogRoot

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
  obtain ⟨e, he, hz₀, hesub, hea, hei⟩ := hψ.exists_openPartialHomeomorph
    (hψ.hasStrictDerivAt.hasStrictFDerivAt_equiv hψd).hasFDerivAt.fderiv
    (inter_mem hpow hW)
  refine ⟨e, hz₀, ?_, fun z hz ↦ (hesub hz).2, ?_, hei, ?_⟩
  · rw [he, hψ0]
  · rwa [he]
  · intro z hz
    rw [he]
    exact (hesub hz).1

end AnalyticAt
