/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Weyl
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Complex.Pompeiu.Lp
import TauCeti.Analysis.Complex.Pompeiu.Weak
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Locality

/-!
# Regularity for the divergence-form Laplace equation in the plane

Write `z = s + i t` on `ℂ`. Let `V` be a finite-dimensional real normed space, `Ω ⊆ ℂ` open and
`1 < r < ∞`. Suppose that `ξ : ℂ → V` is locally integrable on `Ω`, that `f, g : ℂ → V` are locally
`Lʳ` on `Ω`, and that `Δξ = ∂ₛf + ∂ₜg` weakly on `Ω`:

`∫ Δφ • ξ = -∫ (∂ₛφ • f + ∂ₜφ • g)` for every real test function `φ` on `Ω`.

Then `ξ` lies in `W^{1,r}_loc(Ω)` (`TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`).
The gain is one full derivative over the data `f, g`, and no integrability of `ξ` beyond
`L¹_loc` is assumed: the conclusion includes `ξ ∈ Lʳ_loc(Ω)`. This is the regularity statement
through which a weak solution of a first-order real Cauchy–Riemann equation with rough
coefficients is shown to be weakly differentiable.

## Main results

* `TauCeti.memWkpLoc_one_of_forall_integral_laplacian_smul_eq`: a locally integrable weak solution
  of `Δξ = ∂ₛf + ∂ₜg` with `f, g ∈ Lʳ_loc` lies in `W^{1,r}_loc`.

## The argument

The proof uses the Cauchy transform `T` and Weyl's lemma, not a general second-order theory.
Coordinates in a basis reduce to `V = ℝ`. Near a point of `Ω`, take a cutoff `χ` equal to `1` on a
disc `W` and supported in `Ω`, and put `ξ₀ = ½ Re T(χ (f + I g))`. Since `bar∂ (T h) = h`
distributionally for compactly supported `Lʳ` data `h`, and `T h` is locally `Lʳ`, the interior
regularity of `bar∂` puts `T h`, hence `ξ₀`, in `W^{1,r}_loc`. Since `Δ = 4 ∂ bar∂`, the
distributional Laplacian of `T h` is `4 ∂ h`
(`TauCeti.HasWeakConjWirtingerDerivOn.integral_laplacian_smul_eq`), and for real `f, g` one has
`2 Re ∂(f + I g) = ∂ₛf + ∂ₜg` (`TauCeti.HasWeakConjWirtingerDerivOn.integral_laplacian_mul_re_eq`),
so `Δξ₀ = ∂ₛf + ∂ₜg` weakly on `W`. Hence `ξ - ξ₀` is weakly harmonic on `W`, so it agrees almost
everywhere with a harmonic, in particular smooth, function
(`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq`). Thus `ξ ∈ W^{1,r}` near every point of
`Ω`, and local Sobolev membership glues (`TauCeti.memWkpLoc_iff_locally`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (the proof of Lemma B.4.6, which reduces the first-order equation to this
  divergence-form Laplace equation).
-/

public section

open Complex Function MeasureTheory Metric Set TopologicalSpace Laplacian LineDeriv
open scoped Distributions Topology ENNReal NNReal

namespace TauCeti

variable {r : ℝ≥0∞} {Ω : Opens ℂ}

section Scalar

variable {ξ f g : ℂ → ℝ}

/-- The scalar case near a point: `ξ` is in `W^{1,r}` on a neighbourhood of every point of `Ω`. -/
private theorem exists_mem_nhdsWithin_memWkpLoc_one (hr : 1 < r) (hr_top : r ≠ ⊤)
    (hξ : LocallyIntegrableOn ξ Ω volume) (hf : MemLpLoc r Ω f) (hg : MemLpLoc r Ω g)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) : ∃ U ∈ 𝓝[(Ω : Set ℂ)] z₀, MemWkpLoc r U 1 ξ := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen z₀ hz₀
  set ρ : ℝ≥0 := ⟨ε / 3, by positivity⟩
  have hρε : (ρ : ℝ) = ε / 3 := rfl
  have hρ : (0 : ℝ) < ρ := by rw [hρε]; positivity
  -- A cutoff equal to `1` on the disc `W` of radius `ρ`, supported in the disc of radius `2ρ`.
  let χ : ContDiffBump z₀ := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  have h2ρ : ((2 * ρ : ℝ≥0) : ℝ) = 2 * ρ := by push_cast; rfl
  have h2ρε : 2 * (ρ : ℝ) < ε := by rw [hρε]; linarith
  have hρε_le : (ρ : ℝ) ≤ ε := by rw [hρε]; linarith
  have hχΩ : tsupport χ ⊆ Ω := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball h2ρε).trans hεΩ
  let W : Opens ℂ := ⟨ball z₀ ρ, isOpen_ball⟩
  have hWΩ : W ≤ Ω := (ball_subset_ball hρε_le).trans hεΩ
  have hχW : EqOn χ 1 W := fun z hz ↦ χ.one_of_mem_closedBall (ball_subset_closedBall hz)
  -- The complex datum `k = χ (f + I g)` and its Cauchy transform `u`.
  let k : ℂ → ℂ := fun z ↦ χ z • ((f z : ℂ) + I * g z)
  have hk : MemLpLoc r univ k := by
    have hfg : MemLpLoc r Ω (fun z ↦ (f z : ℂ) + I * g z) :=
      (hf.clm_comp ofRealCLM).add (hg.clm_comp (I • ofRealCLM))
    exact hfg.continuous_smul_of_tsupport_subset χ.continuous hχΩ
  have hks : support k ⊆ closedBall z₀ ((2 * ρ : ℝ≥0) : ℝ) := by
    rw [h2ρ]
    exact (support_smul_subset_left _ _).trans (χ.support_eq.trans_subset ball_subset_closedBall)
  have hkLp : MemLp k r (volume.restrict (closedBall z₀ ((2 * ρ : ℝ≥0) : ℝ))) :=
    memLpLoc_iff.1 hk _ (subset_univ _) (isCompact_closedBall _ _)
  let u : ℂ → ℂ := cauchyTransform k
  have hu (U : Opens ℂ) : HasWeakConjWirtingerDerivOn volume U u k :=
    hasWeakConjWirtingerDerivOn_cauchyTransform_of_memLp hr.le hkLp hks U
  have hu_loc : MemLpLoc r univ u := by
    refine memLpLoc_iff.2 fun K _ hK ↦ ?_
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall z₀
    exact (memLp_cauchyTransform (R := R.toNNReal) hr.le hkLp hks).mono_measure
      (Measure.restrict_mono (hR.trans (closedBall_subset_closedBall (Real.le_coe_toNNReal R)))
        le_rfl)
  have hu_sob : MemWkpLoc r (⊤ : Opens ℂ) 1 u :=
    (hu ⊤).memWkpLoc_one hr hr_top (by simpa using hu_loc) (by simpa using hk)
  -- The particular solution `ξ₀ = ½ Re u` of `Δξ₀ = ∂ₛf + ∂ₜg` on `W`.
  let ξ₀ : ℂ → ℝ := fun z ↦ 2⁻¹ * (u z).re
  have hξ₀ : MemWkpLoc r W 1 ξ₀ := (hu_sob.clm_comp ((2⁻¹ : ℝ) • reCLM)).mono (by simp)
  have hξ₀_int : LocallyIntegrableOn ξ₀ W volume :=
    hξ₀.memLpLoc.locallyIntegrableOn hr.le W.isOpen.isLocallyClosed
  have hpart (φ : 𝓓(W, ℝ)) : ∫ z, Δ (φ : ℂ → ℝ) z • ξ₀ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z) := by
    calc ∫ z, Δ (φ : ℂ → ℝ) z • ξ₀ z = 2⁻¹ * ∫ z, Δ (φ : ℂ → ℝ) z * (u z).re := by
          rw [← integral_const_mul]
          congr 1 with z
          simp only [ξ₀, smul_eq_mul]
          ring
      _ = -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 * (k z).re + fderiv ℝ (φ : ℂ → ℝ) z I * (k z).im) := by
          rw [(hu W).integral_laplacian_mul_re_eq φ]
          ring
      _ = _ := by
          refine congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_))
          simp only [k, smul_eq_mul, real_smul, mul_re, mul_im, ofReal_re, ofReal_im, add_re,
            add_im, I_re, I_im]
          have hφχ (v : ℂ) : fderiv ℝ (φ : ℂ → ℝ) z v * χ z = fderiv ℝ (φ : ℂ → ℝ) z v := by
            rw [mul_comm, ← smul_eq_mul, φ.smul_fderiv_apply_eq_of_eqOn_one hχW]
          linear_combination f z * hφχ 1 + g z * hφχ I
  -- The remainder `ξ - ξ₀` is weakly harmonic on `W`, hence smooth after modification.
  have hharm : WeaklyHarmonicOn volume W (ξ - ξ₀) := by
    refine weaklyHarmonicOn_iff.2 ⟨(hξ.mono_set hWΩ).sub hξ₀_int, fun φ ↦ ?_⟩
    have hφ : ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
        -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z) :=
      h ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hWΩ⟩
    have hint (w : ℂ → ℝ) (hw : LocallyIntegrableOn w W volume) :
        Integrable (fun z ↦ Δ (φ : ℂ → ℝ) z • w z) := by
      simpa only [TestFunction.laplacianCLM_apply] using
        (laplacianCLM ℝ ℂ 𝓓(W, ℝ) φ).integrable_smul hw
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub (hint ξ (hξ.mono_set hWΩ)) (hint ξ₀ hξ₀_int), hφ, hpart, sub_self]
  obtain ⟨v, hv, hξv⟩ := hharm.exists_harmonicOnNhd_ae_eq
  have hvW : MemWkpLoc r W 1 v := (hv.contDiffOn.of_le (by norm_num)).memWkpLoc subset_rfl
  refine ⟨W, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hρ), (hξ₀.add hvW).congr_ae ?_⟩
  filter_upwards [hξv] with z hz
  simp only [Pi.add_apply, ← hz, Pi.sub_apply, add_sub_cancel]

end Scalar

/-- **Regularity for the divergence-form Laplace equation.** Let `V` be finite-dimensional and
`1 < r < ∞`. If `ξ` is locally integrable on the open set `Ω`, `f` and `g` are locally `Lʳ` on
`Ω`, and `Δξ = ∂ₛf + ∂ₜg` weakly on `Ω`, that is
`∫ Δφ • ξ = -∫ (∂ₛφ • f + ∂ₜφ • g)` for every real test function `φ` on `Ω`,
then `ξ ∈ W^{1,r}_loc(Ω)`. -/
theorem memWkpLoc_one_of_forall_integral_laplacian_smul_eq {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ξ f g : ℂ → V} (hr : 1 < r) (hr_top : r ≠ ⊤)
    (hξ : LocallyIntegrableOn ξ Ω volume) (hf : MemLpLoc r Ω f) (hg : MemLpLoc r Ω g)
    (h : ∀ φ : 𝓓(Ω, ℝ), ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z)) :
    MemWkpLoc r Ω 1 ξ := by
  let b := Module.finBasis ℝ V
  refine b.memWkpLoc_iff.2 fun i ↦ memWkpLoc_iff_locally.2 fun z₀ hz₀ ↦ ?_
  let L : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (b.coord i)
  refine exists_mem_nhdsWithin_memWkpLoc_one hr hr_top (L.locallyIntegrableOn_comp hξ)
    (hf.clm_comp L) (hg.clm_comp L)
    (fun φ ↦ ?_) hz₀
  have hfloc := hf.locallyIntegrableOn hr.le Ω.isOpen.isLocallyClosed
  have hgloc := hg.locallyIntegrableOn hr.le Ω.isOpen.isLocallyClosed
  have hint : Integrable fun z ↦ fderiv ℝ (φ : ℂ → ℝ) z 1 • f z + fderiv ℝ (φ : ℂ → ℝ) z I • g z :=
    (integrable_fderiv_smul_of_locallyIntegrableOn hfloc φ 1).add
      (integrable_fderiv_smul_of_locallyIntegrableOn hgloc φ I)
  have e := congrArg L (h φ)
  rw [map_neg, ← L.integral_comp_comm (by
      simpa only [TestFunction.laplacianCLM_apply] using
        (laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) φ).integrable_smul hξ), ← L.integral_comp_comm hint] at e
  simpa only [map_add, map_smul, Function.comp_apply] using e

end TauCeti
