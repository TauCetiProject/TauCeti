/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.UniformLimit
public import TauCeti.Geometry.Symplectic.Floer.Compactness
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp

/-!
# Limits of Floer solutions solve the Floer equation almost everywhere

In local coordinates `z = s + i t ∈ ℂ` on the domain and `x ∈ V` on the target, the inhomogeneous
Cauchy–Riemann equation of Hamiltonian Floer theory reads

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`,

for a domain-dependent almost complex structure `J` and the Hamiltonian one-form `X`, as in
`TauCeti.Geometry.Symplectic.Floer.Compactness`. The compactness theorem
`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` extracts from a
sequence of solutions with bounded energy a subsequence that converges locally uniformly off a
finite set of bubbling points, with derivatives bounded on compact subsets of the complement. It
only asserts that the limit is continuous.

This file shows that such a limit solves the equation. Let `uᵢ` be `C¹` solutions on an open set
`Ω` with values in a compact set `K`, with derivatives eventually bounded on every compact subset
of `Ω`, converging locally uniformly on `Ω` to `v`, and let `J` and `X` be continuous on
`Ω ×ˢ K`. Then `v` is locally Lipschitz on `Ω`, and `fderiv ℝ v` is its weak derivative there
(`TauCeti.locallyLipschitzOn_of_tendsto`, `LocallyLipschitzOn.hasWeakFDerivOn_fderiv`), and at
almost every point of `Ω`, `v` is differentiable and solves the Floer equation
(`TauCeti.Floer.ae_differentiableAt_and_fderiv_I_sub_eq_of_tendstoLocallyUniformlyOn`).

In particular the limit produced by the compactness theorem is, off the bubbling points, a locally
Lipschitz map solving the Floer equation almost everywhere
(`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_ae`).

The equation is linear in the derivative of the map, with coefficients `J(z, u)` and `X(z, u)`
that converge uniformly on compact sets along the sequence. The derivatives only converge weakly
(`TauCeti.tendsto_integral_apply_fderiv_apply_of_tendstoLocallyUniformlyOn`), and that suffices to
pass the equation, tested against smooth compactly supported functions, to the limit. The
fundamental lemma of the calculus of variations then gives it almost everywhere. Only continuity
of `J` and `X` is used. Smoothness of the limit, and with it the equation at every point, is
elliptic regularity for Lipschitz solutions, which is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (convergence away from the bubbling points) and Appendix B.4 (elliptic bootstrapping).
-/

public section

open Complex ContinuousLinearMap Filter MeasureTheory Metric Set Topology

namespace TauCeti.Floer

section Limit

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} {l : Filter ι} {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {Ω : Set ℂ}
  {K : Set V} {u : ι → ℂ → V} {v : ℂ → V}

omit [FiniteDimensional ℝ V] in
/-- Freezing the coefficient `J(z, uᵢ)` at the limit `J(z, v)` costs nothing in the limit: if
`uᵢ → v` uniformly on the support of `φ`, with values in `K` and derivatives eventually bounded
there, then `∫ φ • (J(z, uᵢ) - J(z, v)) (∂ₛuᵢ) → 0`. -/
private theorem tendsto_integral_smul_sub_apply_fderiv_one (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hJ : ContinuousOn J (Ω ×ˢ K)) (hu : ∀ i, ContDiffOn ℝ 1 (u i) Ω)
    (huK : ∀ i, MapsTo (u i) Ω K) (hv : ContinuousOn v Ω) (hvK : MapsTo v Ω K) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) {M : ℝ}
    (hM : ∀ᶠ i in l, ∀ y ∈ tsupport φ, ‖fderiv ℝ (u i) y‖ ≤ M)
    (hU : TendstoUniformlyOn u v l (tsupport φ)) :
    Tendsto (fun i ↦ ∫ y, φ y • (J (y, u i y) - J (y, v y)) (fderiv ℝ (u i) y 1)) l (𝓝 0) := by
  have hJu : ∀ i, ContinuousOn (fun y ↦ J (y, u i y)) Ω := fun i ↦
    hJ.comp (continuousOn_id.prodMk (hu i).continuousOn) fun y hy ↦ ⟨hy, huK i hy⟩
  have hJv : ContinuousOn (fun y ↦ J (y, v y)) Ω :=
    hJ.comp (continuousOn_id.prodMk hv) fun y hy ↦ ⟨hy, hvK hy⟩
  have hJU := IsCompact.tendstoUniformlyOn_comp_prodMk hφc hK
    (hJ.mono (prod_mono hφΩ subset_rfl)) (Eventually.of_forall fun i ↦ (huK i).mono_left hφΩ)
    (hvK.mono_left hφΩ) hU
  -- The coefficients converge uniformly and the derivatives stay bounded by `M`.
  have hsmall : TendstoUniformlyOn
      (fun i y ↦ (J (y, u i y) - J (y, v y)) (fderiv ℝ (u i) y 1)) (fun _ ↦ 0) l (tsupport φ) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    have hη : 0 < ε / (max M 0 + 1) := by positivity
    filter_upwards [hM, Metric.tendstoUniformlyOn_iff.1 hJU _ hη] with i hMi hi y hy
    rw [dist_zero_left]
    calc ‖(J (y, u i y) - J (y, v y)) (fderiv ℝ (u i) y 1)‖
        ≤ ‖J (y, u i y) - J (y, v y)‖ * ‖fderiv ℝ (u i) y 1‖ := le_opNorm _ _
      _ ≤ ε / (max M 0 + 1) * max M 0 := by
        refine mul_le_mul (by simpa [dist_eq_norm'] using (hi y hy).le) ?_ (norm_nonneg _) hη.le
        have hM' := (hMi y hy).trans (le_max_left M 0)
        exact ((fderiv ℝ (u i) y).le_opNorm 1).trans (by simpa using hM')
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  simpa using tendsto_integral_smul_of_tendstoUniformlyOn (μ := volume) hΩ
    (fun i ↦ ((hJu i).sub hJv).clm_apply
      (((hu i).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const))
    continuousOn_const hφ hφc hφΩ hsmall

/-- An equation `∂ₜu - J(z, u) ∂ₛu - Q(z, u) = 0`, tested against a continuous weight `φ` with
compact support in `Ω`, passes to the limit: `∫ φ • (∂ₜv - J(z, v) ∂ₛv - Q(z, v)) = 0`. The
derivative terms converge by weak convergence of the derivatives, after freezing the coefficient
`J(z, uᵢ)` of `∂ₛuᵢ` at `J(z, v)`, and the zeroth-order term converges uniformly. -/
private theorem integral_smul_fderiv_I_sub_sub_eq_zero [l.NeBot] (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hJ : ContinuousOn J (Ω ×ˢ K)) {Q : ℂ × V → V}
    (hQ : ContinuousOn Q (Ω ×ˢ K)) (hu : ∀ i, ContDiffOn ℝ 1 (u i) Ω)
    (hCR : ∀ i, ∀ y ∈ Ω,
      fderiv ℝ (u i) y I - J (y, u i y) (fderiv ℝ (u i) y 1) - Q (y, u i y) = 0)
    (huK : ∀ i, MapsTo (u i) Ω K)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ᶠ i in l, ∀ y ∈ C, ‖fderiv ℝ (u i) y‖ ≤ M)
    (hlim : TendstoLocallyUniformlyOn u v l Ω) (hv : LocallyLipschitzOn Ω v)
    (hvK : MapsTo v Ω K) {φ : ℂ → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) :
    ∫ y, φ y • (fderiv ℝ v y I - J (y, v y) (fderiv ℝ v y 1) - Q (y, v y)) = 0 := by
  have hQu : ∀ i, ContinuousOn (fun y ↦ Q (y, u i y)) Ω := fun i ↦
    hQ.comp (continuousOn_id.prodMk (hu i).continuousOn) fun y hy ↦ ⟨hy, huK i hy⟩
  have hQv : ContinuousOn (fun y ↦ Q (y, v y)) Ω :=
    hQ.comp (continuousOn_id.prodMk hv.continuousOn) fun y hy ↦ ⟨hy, hvK hy⟩
  have hJu : ∀ i, ContinuousOn (fun y ↦ J (y, u i y)) Ω := fun i ↦
    hJ.comp (continuousOn_id.prodMk (hu i).continuousOn) fun y hy ↦ ⟨hy, huK i hy⟩
  have hJv : ContinuousOn (fun y ↦ J (y, v y)) Ω :=
    hJ.comp (continuousOn_id.prodMk hv.continuousOn) fun y hy ↦ ⟨hy, hvK hy⟩
  have hdu : ∀ i (w : ℂ), ContinuousOn (fun y ↦ fderiv ℝ (u i) y w) Ω := fun i w ↦
    ((hu i).continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply continuousOn_const
  have hloc : ∀ w : ℂ, LocallyIntegrableOn (fun y ↦ fderiv ℝ v y w) Ω := fun w ↦
    (hasWeakFDerivOn_iff.1 (hv.hasWeakFDerivOn_fderiv (μ := volume) (Ω := ⟨Ω, hΩ⟩)) w)
      |>.locallyIntegrableOn_deriv
  have hint : ∀ {h : ℂ → V}, LocallyIntegrableOn h Ω → Integrable (fun y ↦ φ y • h y) :=
    fun hh ↦ hh.integrable_smul_left_of_hasCompactSupport hφ hφc hφΩ
  have hint' : ∀ {h : ℂ → V}, ContinuousOn h Ω → Integrable (fun y ↦ φ y • h y) :=
    fun hh ↦ hint (hh.locallyIntegrableOn hΩ.measurableSet)
  obtain ⟨M, hM⟩ := hbd _ hφc hφΩ
  have hU : TendstoUniformlyOn u v l (tsupport φ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hlim _ hφΩ hφc
  -- The four terms of the tested equation converge along the sequence.
  have L₁ := tendsto_integral_smul_fderiv_apply_of_tendstoLocallyUniformlyOn (μ := volume) hΩ hu
    hbd hlim hφ hφc hφΩ I
  have L₂ := tendsto_integral_apply_fderiv_apply_of_tendstoLocallyUniformlyOn (μ := volume) hΩ hu
    hbd hlim (A := fun y ↦ φ y • J (y, v y)) (hφ.continuousOn.smul hJv) hφc.smul_right
    ((tsupport_smul_subset_left _ _).trans hφΩ) 1
  simp only [FunLike.coe_smul, Pi.smul_apply] at L₂
  have L₃ := tendsto_integral_smul_sub_apply_fderiv_one hΩ hK hJ hu huK hv.continuousOn hvK hφ hφc
    hφΩ hM hU
  have L₄ := tendsto_integral_smul_of_tendstoUniformlyOn (μ := volume) hΩ hQu hQv hφ hφc hφΩ
    (IsCompact.tendstoUniformlyOn_comp_prodMk hφc hK (hQ.mono (prod_mono hφΩ subset_rfl))
      (Eventually.of_forall fun i ↦ (huK i).mono_left hφΩ) (hvK.mono_left hφΩ) hU)
  -- Along the sequence they add up to zero, since each `uᵢ` solves the equation.
  have hzero : ∀ i, (∫ y, φ y • fderiv ℝ (u i) y I) -
      (∫ y, φ y • J (y, v y) (fderiv ℝ (u i) y 1)) -
      (∫ y, φ y • (J (y, u i y) - J (y, v y)) (fderiv ℝ (u i) y 1)) -
        (∫ y, φ y • Q (y, u i y)) = 0 := by
    intro i
    have h₁ := hint' (hdu i I)
    have h₂ := hint' (hJv.clm_apply (hdu i 1))
    have h₃ : Integrable (fun y ↦ φ y • (J (y, u i y) - J (y, v y)) (fderiv ℝ (u i) y 1)) :=
      hint' (((hJu i).sub hJv).clm_apply (hdu i 1))
    rw [← integral_sub h₁ h₂, ← integral_sub (h₁.sub' h₂) h₃,
      ← integral_sub ((h₁.sub' h₂).sub' h₃) (hint' (hQu i))]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ Ω
    · have h : φ y • fderiv ℝ (u i) y I - φ y • J (y, v y) (fderiv ℝ (u i) y 1) -
          φ y • (J (y, u i y) - J (y, v y)) (fderiv ℝ (u i) y 1) - φ y • Q (y, u i y) =
          φ y • (fderiv ℝ (u i) y I - J (y, u i y) (fderiv ℝ (u i) y 1) - Q (y, u i y)) := by
        simp only [FunLike.coe_sub, Pi.sub_apply, smul_sub]
        abel
      calc _ = φ y • (fderiv ℝ (u i) y I - J (y, u i y) (fderiv ℝ (u i) y 1) - Q (y, u i y)) := h
        _ = 0 := by rw [hCR i y hy, smul_zero]
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hy (hφΩ h)]
  have hlim0 := tendsto_nhds_unique (((L₁.sub L₂).sub L₃).sub L₄)
    (tendsto_const_nhds.congr fun i ↦ (hzero i).symm)
  rw [sub_zero] at hlim0
  have hJdv := (hloc 1).continuousOn_clm_apply hΩ.isLocallyClosed hJv
  simp_rw [smul_sub]
  rw [integral_sub ((hint (hloc I)).sub' (hint hJdv)) (hint' hQv),
    integral_sub (hint (hloc I)) (hint hJdv), hlim0]

/-- **Locally uniform limits of Floer solutions solve the Floer equation almost everywhere.** Let
`J` and `X` be continuous on `Ω ×ˢ K` for an open `Ω ⊆ ℂ` and a compact `K ⊆ V`. Let `uᵢ` be `C¹`
solutions of `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` on `Ω` with image in `K`, whose
derivatives are eventually bounded on every compact subset of `Ω`, converging locally uniformly on
`Ω` to `v`. Then at almost every point of `Ω`, `v` is differentiable and solves the same equation.
The limit is locally Lipschitz on `Ω` by `TauCeti.locallyLipschitzOn_of_tendsto`, and `fderiv ℝ v`
is its weak derivative there by `LocallyLipschitzOn.hasWeakFDerivOn_fderiv`. -/
theorem ae_differentiableAt_and_fderiv_I_sub_eq_of_tendstoLocallyUniformlyOn [l.NeBot]
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hJ : ContinuousOn J (Ω ×ˢ K))
    (hX : ContinuousOn X (Ω ×ˢ K)) (hu : ∀ i, ContDiffOn ℝ 1 (u i) Ω)
    (hCR : ∀ i, ∀ y ∈ Ω, fderiv ℝ (u i) y I - X (y, u i y) I =
      J (y, u i y) (fderiv ℝ (u i) y 1 - X (y, u i y) 1))
    (huK : ∀ i, MapsTo (u i) Ω K)
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ᶠ i in l, ∀ y ∈ C, ‖fderiv ℝ (u i) y‖ ≤ M)
    (hlim : TendstoLocallyUniformlyOn u v l Ω) :
    ∀ᵐ y, y ∈ Ω → DifferentiableAt ℝ v y ∧
      fderiv ℝ v y I - X (y, v y) I = J (y, v y) (fderiv ℝ v y 1 - X (y, v y) 1) := by
  have hpt : ∀ y ∈ Ω, Tendsto (fun i ↦ u i y) l (𝓝 (v y)) := fun _ hy ↦ hlim.tendsto_at hy
  have hv : LocallyLipschitzOn Ω v := locallyLipschitzOn_of_tendsto hΩ
    (Eventually.of_forall fun i ↦ (hu i).differentiableOn one_ne_zero) hbd hpt
  have hvK : MapsTo v Ω K := fun y hy ↦
    hK.isClosed.mem_of_tendsto (hpt y hy) (Eventually.of_forall fun i ↦ huK i hy)
  have hweak : HasWeakFDerivOn volume ⟨Ω, hΩ⟩ v (fderiv ℝ v) := hv.hasWeakFDerivOn_fderiv
  have hJv : ContinuousOn (fun y ↦ J (y, v y)) Ω :=
    hJ.comp (continuousOn_id.prodMk hv.continuousOn) fun y hy ↦ ⟨hy, hvK hy⟩
  have hloc : ∀ w : ℂ, LocallyIntegrableOn (fun y ↦ fderiv ℝ v y w) Ω :=
    fun w ↦ (hasWeakFDerivOn_iff.1 hweak w).locallyIntegrableOn_deriv
  -- Write the equation as `∂ₜu - J(z, u) ∂ₛu - Q(z, u) = 0` with the zeroth-order term `Q`.
  set Q : ℂ × V → V := fun p ↦ X p I - J p (X p 1) with hQdef
  have hQ : ContinuousOn Q (Ω ×ˢ K) :=
    (hX.clm_apply continuousOn_const).sub (hJ.clm_apply (hX.clm_apply continuousOn_const))
  have hQv : ContinuousOn (fun y ↦ Q (y, v y)) Ω :=
    hQ.comp (continuousOn_id.prodMk hv.continuousOn) fun y hy ↦ ⟨hy, hvK hy⟩
  have hCR' : ∀ i, ∀ y ∈ Ω,
      fderiv ℝ (u i) y I - J (y, u i y) (fderiv ℝ (u i) y 1) - Q (y, u i y) = 0 := by
    intro i y hy
    have h := hCR i y hy
    rw [map_sub] at h
    simp only [hQdef]
    rw [← sub_eq_zero.2 h]
    abel
  -- The defect of the equation is locally integrable and vanishes against every test function.
  have hG := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((hloc I).sub ((hloc 1).continuousOn_clm_apply hΩ.isLocallyClosed hJv)).sub
      (hQv.locallyIntegrableOn hΩ.measurableSet))
    fun φ hφ hφc hφΩ ↦ integral_smul_fderiv_I_sub_sub_eq_zero hΩ hK hJ hQ hu hCR' huK hbd hlim
      hv hvK hφ.continuous hφc hφΩ
  filter_upwards [hG, hv.ae_differentiableAt_of_mem hΩ] with y hGy hdy hy
  refine ⟨hdy hy, ?_⟩
  have h := hGy hy
  simp only [Pi.sub_apply, hQdef] at h
  rw [map_sub, ← sub_eq_zero, ← h]
  abel

end Limit

section Compactness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Floer solutions converge off finitely many bubbling points to an almost-everywhere
solution.** In the setting of the compactness theorem
`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`, the limit `v` of the
subsequence off the finite bubbling set `Z` is locally Lipschitz on `Ω \ Z`, and at almost every
point of `Ω \ Z` it is differentiable and solves `∂ₜv - X(z, v) i = J(z, v)(∂ₛv - X(z, v) 1)`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_ae
    {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {D : Set ℂ} {K : Set V}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ D, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v) :
    ∃ δ > 0, ∀ ⦃Ω : Set ℂ⦄ ⦃u : ℕ → ℂ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, fderiv ℝ (u k) y I - X (y, u k y) I =
        J (y, u k y) (fderiv ℝ (u k) y 1 - X (y, u k y) 1)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun y ↦ ‖fderiv ℝ (u k) y 1‖ ^ 2) Ω) →
      (∀ k, ∫ y in Ω, ‖fderiv ℝ (u k) y 1‖ ^ 2 ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset ℂ) (v : ℂ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y 1‖ ^ 2) ∧
        MapsTo v (Ω \ ↑Z) K ∧ TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) ∧
        LocallyLipschitzOn (Ω \ ↑Z) v ∧
        ∀ᵐ y, y ∈ Ω \ ↑Z → DifferentiableAt ℝ v y ∧
          fderiv ℝ v y I - X (y, v y) I = J (y, v y) (fderiv ℝ v y 1 - X (y, v y) 1) := by
  obtain ⟨δ, hδ, hconv⟩ := exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hW hJ hX
    hD hK hDKW hJsq
  refine ⟨δ, hδ, fun Ω u E hΩ hΩD hu hCR huK hint hE ↦ ?_⟩
  obtain ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, -, hvK, hlim⟩ :=
    hconv hΩ hΩD hu hCR huK hint hE
  have hΩZ : Ω \ ↑Z ⊆ Ω := sdiff_subset
  have hsub : (Ω \ ↑Z) ×ˢ K ⊆ W := (prod_mono (hΩZ.trans hΩD) subset_rfl).trans hDKW
  have hΩZo : IsOpen (Ω \ ↑Z) := hΩ.sdiff Z.finite_toSet.isClosed
  have hu' : ∀ n, ContDiffOn ℝ 1 (u (φ n)) (Ω \ ↑Z) := fun n ↦
    ((hu (φ n)).of_le (by norm_num)).mono hΩZ
  have hbd' : ∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
      ∃ M, ∀ᶠ n in atTop, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M := fun C hC hCZ ↦
    (hbd C hC hCZ).imp fun _ hM ↦ Eventually.of_forall hM
  refine ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hvK, hlim,
    locallyLipschitzOn_of_tendsto hΩZo
      (Eventually.of_forall fun n ↦ (hu' n).differentiableOn one_ne_zero) hbd'
      fun _ hy ↦ hlim.tendsto_at hy, ?_⟩
  exact ae_differentiableAt_and_fderiv_I_sub_eq_of_tendstoLocallyUniformlyOn hΩZo hK
    (hJ.continuousOn.mono hsub) (hX.continuousOn.mono hsub) hu'
    (fun n y hy ↦ hCR (φ n) y (hΩZ hy)) (fun n ↦ (huK (φ n)).mono_left hΩZ) hbd' hlim

end Compactness

end TauCeti.Floer
