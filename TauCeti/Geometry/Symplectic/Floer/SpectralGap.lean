/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Periodic
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The spectral gap at a nondegenerate orbit and the stationary cylinder estimate

Let `(V, ω)` be a symplectic vector space, `J_t` a continuous family of almost complex structures
and `S_t` a continuous family of endomorphisms, with associated forms `g_t = ω(·, J_t ·)`. The
asymptotic operator `A ζ = J_t (ζ' - S_t ζ)` of `TauCeti.Floer.asymptoticOperator` and the
stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)` of
`TauCeti.Floer.stationaryCylinderOperator` describe the linearized Floer equation on a cylindrical
end asymptotic to an orbit with linearized Hamiltonian vector field `S_t`. This file proves the
quantitative form of their invertibility at a nondegenerate orbit, in the `L²` norms of `g_t`.

**The spectral gap.** Suppose that the return map `Ψ(1)` of `ζ' = S_t ζ` fixes no nonzero vector
and that every `J_t` is `ω`-tame. Then there is a constant `C` with

`∫₀¹ g_t(ζ, ζ) dt ≤ C ∫₀¹ g_t(A ζ, A ζ) dt`

for every `C¹` loop `ζ` with `ζ 1 = ζ 0`
(`TauCeti.Floer.exists_integral_associatedBilinForm_le_mul_integral_asymptoticOperator`). This is
the `L²` form of the a priori estimate `‖ζ‖_∞ ≤ C ∫₀¹ ‖ζ' - S ζ‖` for periodic solutions
(`TauCeti.exists_integral_norm_sq_le_mul_integral_norm_sq`), combined with the fact that `J_t`
preserves `g_t(v, v)` and that the forms `g_t` are uniformly equivalent to the norm of `V`
(`TauCeti.SymplecticForm.exists_pos_forall_mul_norm_sq_le_and_le_mul_norm_sq`). For compatible
`J_t` and infinitesimally symplectic `S_t`, `A` is symmetric for the pairing `∫₀¹ g_t`
(`TauCeti.Floer.integral_associatedBilinForm_asymptoticOperator_comm`), and the estimate bounds
`A` away from `0` in this norm: a loop with `A ζ = λ ζ` and `C λ² < 1` has `∫₀¹ g_t(ζ, ζ) = 0`.

**The stationary cylinder estimate.** Let every `J_t` be `ω`-compatible and every `S_t`
infinitesimally symplectic, and let `ξ` be a `C²` map of the cylinder, of period one in `t`, which
tends to zero together with `∂t ξ` as `|s| → ∞`, uniformly in `t`, and whose image `D ξ` is
square integrable on `ℝ × [0, 1]`. Letting the strip `[a, b] × [0, 1]` exhaust the cylinder in
the energy identity `TauCeti.Floer.setIntegral_associatedBilinForm_stationaryCylinderOperator`,
whose boundary terms vanish in the limit, gives

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ)) ≤ ∫ g(D ξ, D ξ)`

with both sides finite
(`TauCeti.Floer.integrableOn_and_setIntegral_le_setIntegral_stationaryCylinderOperator`). If
moreover the return map is nondegenerate, the spectral gap on each slice `s = const` bounds
`∫₀¹ g(ξ, ξ)` by `C ∫₀¹ g(∂t ξ - S ξ, ∂t ξ - S ξ)`, and hence

`∫ g(ξ, ξ) ≤ C ∫ g(D ξ, D ξ)`

over the cylinder, with a constant `C` independent of `ξ`
(`TauCeti.Floer.exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`). Together these
control `ξ`, `∂s ξ` and `∂t ξ - S ξ` in `L²` by `D ξ`. This is the a priori estimate which, on the
Sobolev completion, makes `D` injective with closed range at a nondegenerate orbit.

**The weighted operator.** Conjugating `D` by the weight `e^{δ s}` gives `D - δ`, the stationary
cylinder operator of `S_t - δ J_t` (`TauCeti.Floer.stationaryCylinderOperator_exp_smul`). For
compatible `J_t` the family `S_t - δ J_t` is again infinitesimally symplectic, and at a
nondegenerate orbit of a Hamiltonian it stays nondegenerate for all small `δ`
(`TauCeti.SymplecticForm.eventually_eq_zero_of_asymptoticOperator_eq_smul`). So the estimate
holds for `D - δ` for every weight `δ` close to `0`
(`eventually_exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator_sub_smul` in
`TauCeti.SymplecticForm`): this is the estimate for the linearized operator on the weighted
spaces of maps decaying like `e^{-δ s}`.

The Sobolev realizations of `A` and `D`, their surjectivity and the Fredholm theory of the
linearized operator on a punctured domain are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the operator `∂s + A` at a nondegenerate orbit.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. 45 (1992), 1303–1360.
* A. Floer, *The unregularized gradient flow of the symplectic action*, Comm. Pure Appl. Math. 41
  (1988), 775–813.
-/

public section

open Function Filter Set MeasureTheory Topology
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}

section Loop

/-- **The spectral gap of a nondegenerate asymptotic operator.** Let `J_t` be `ω`-tame and
continuous on `[0, 1]`, let `S` be continuous, and suppose that the return map `Ψ(1)` of the
linearized equation `ζ' = S_t ζ` fixes no nonzero vector. Then there is a constant `C ≥ 0` such
that every `C¹` loop `ζ` with `ζ 1 = ζ 0` satisfies
`∫₀¹ g_t(ζ, ζ) dt ≤ C ∫₀¹ g_t(A ζ, A ζ) dt` for `g_t = ω(·, J_t ·)` and the asymptotic operator
`A ζ = J_t (ζ' - S_t ζ)`. -/
theorem exists_integral_associatedBilinForm_le_mul_integral_asymptoticOperator
    (hJ : ∀ t ∈ Icc (0 : ℝ) 1, ω.Tames (J t)) (hJc : ContinuousOn J (Icc 0 1))
    (hSc : Continuous S) (hnd : ∀ v, dysonSeriesLeft S 1 v = v → v = 0) :
    ∃ C, 0 ≤ C ∧ ∀ ζ : ℝ → V, ContDiff ℝ 1 ζ → ζ 1 = ζ 0 →
      ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (ζ t) (ζ t) ≤
        C * ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t)
          (asymptoticOperator J S ζ t) := by
  obtain ⟨a, ha, M, hM, hg⟩ :=
    SymplecticForm.exists_pos_forall_mul_norm_sq_le_and_le_mul_norm_sq isCompact_Icc hJc hJ
  have hunit : IsUnit ((1 : ℝ) • (1 : V →L[ℝ] V) - dysonSeriesLeft S 1) :=
    isUnit_smul_one_sub_dysonSeriesLeft fun v hv ↦ hnd v (by simpa using hv)
  obtain ⟨C₀, hC₀, hest⟩ := exists_integral_norm_sq_le_mul_integral_norm_sq hSc zero_le_one hunit
  refine ⟨M * C₀ / a, by positivity, fun ζ hζ hζ1 ↦ ?_⟩
  set f : ℝ → V := fun t ↦ deriv ζ t - S t (ζ t)
  have hf : Continuous f := (hζ.continuous_deriv le_rfl).sub (hSc.clm_apply hζ.continuous)
  have hw (t : ℝ) : HasDerivAt ζ (S t (ζ t) + f t) t := by
    simpa only [f, add_sub_cancel] using (hζ.differentiable one_ne_zero t).hasDerivAt
  have hL2 := hest hf hw (by rw [one_smul]; exact hζ1)
  -- `J_t` preserves `g_t(v, v)`, so `g_t(A ζ, A ζ) = g_t(f, f)` for `f = ζ' - S ζ`.
  have hA (t : ℝ) : ω.associatedBilinForm (J t) (asymptoticOperator J S ζ t)
      (asymptoticOperator J S ζ t) = ω.associatedBilinForm (J t) (f t) (f t) := by
    rw [asymptoticOperator_def]
    exact ω.associatedBilinForm_apply_apply_self_eq (J t) (f t)
  have hgc {p : ℝ → V} (hp : Continuous p) :
      IntervalIntegrable (fun t ↦ ω.associatedBilinForm (J t) (p t) (p t)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    simp only [SymplecticForm.associatedBilinForm_apply]
    refine ω.continuousOn_apply_comp hp.continuousOn ?_
    simpa using ((AlmostComplexStructure.continuous_iff.1 continuous_id).comp_continuousOn
      hJc).clm_apply hp.continuousOn
  rw [intervalIntegral.integral_congr fun t _ ↦ hA t]
  calc ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (ζ t) (ζ t)
      ≤ ∫ t in (0 : ℝ)..1, M * ‖ζ t‖ ^ 2 :=
        intervalIntegral.integral_mono_on zero_le_one (hgc hζ.continuous)
          (((hζ.continuous.norm.pow 2).const_mul M).intervalIntegrable _ _) fun t ht ↦ by
          simpa only [SymplecticForm.associatedBilinForm_apply] using (hg t ht (ζ t)).2
    _ = M * ∫ t in (0 : ℝ)..1, ‖ζ t‖ ^ 2 := intervalIntegral.integral_const_mul _ _
    _ ≤ M * (C₀ * ∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) := mul_le_mul_of_nonneg_left hL2 hM
    _ = M * C₀ / a * ∫ t in (0 : ℝ)..1, a * ‖f t‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
        field_simp
    _ ≤ M * C₀ / a * ∫ t in (0 : ℝ)..1, ω.associatedBilinForm (J t) (f t) (f t) := by
        refine mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on zero_le_one
          (((hf.norm.pow 2).const_mul a).intervalIntegrable _ _) (hgc hf) fun t ht ↦ ?_)
          (by positivity)
        simpa only [SymplecticForm.associatedBilinForm_apply] using (hg t ht (f t)).1

end Loop

section Cylinder

variable {ξ : ℝ × ℝ → V}

/-- **The energy estimate of the stationary cylinder operator.** Let each `J_t` be
`ω`-compatible and depend continuously on `t`, and let each `S_t` be infinitesimally symplectic.
Let `ξ` be a `C²` map of period one in `t` which tends to zero together with `∂t ξ` as
`|s| → ∞`, uniformly in `t`, and such that `g(D ξ, D ξ)` is integrable on `ℝ × [0, 1]`, where
`g_t = ω(·, J_t ·)`. Then `g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ)` is integrable on
`ℝ × [0, 1]`, with integral at most that of `g(D ξ, D ξ)`. No nondegeneracy is needed. -/
theorem integrableOn_and_setIntegral_le_setIntegral_stationaryCylinderOperator
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hdecay : Tendsto (fun z ↦ (ξ z, fderiv ℝ ξ z stdComplexLineImag))
      (comap Prod.fst (cocompact ℝ)) (𝓝 0))
    (hD : IntegrableOn (fun z ↦ ω.associatedBilinForm (J z.2)
      (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z))
      (univ ×ˢ Icc 0 1)) :
    IntegrableOn (fun z ↦
        ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
            (fderiv ℝ ξ z stdComplexLineReal) +
          ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
            (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) (univ ×ˢ Icc 0 1) ∧
      ∫ z in univ ×ˢ Icc 0 1,
          (ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
              (fderiv ℝ ξ z stdComplexLineReal) +
            ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
              (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) ≤
        ∫ z in univ ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
          (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z) := by
  have hg0 (t : ℝ) (v : V) := (hJ t).associatedBilinForm_self_nonneg v
  set Φ : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..1,
    ω (fderiv ℝ ξ (s, t) stdComplexLineImag - S t (ξ (s, t))) (ξ (s, t))
  have hΦ : Tendsto Φ (cocompact ℝ) (𝓝 0) := tendsto_integral_slicePairing hSc hdecay
  -- The boundary terms of the energy identity over `[-n, n] × [0, 1]` vanish as `n → ∞`.
  have he : Tendsto (fun n : ℕ ↦ Φ (-(n : ℝ)) - Φ n) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n : ℕ ↦ Φ (-(n : ℝ))) atTop (𝓝 0) :=
      hΦ.comp ((tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop).mono_right
        atBot_le_cocompact)
    have h₂ : Tendsto (fun n : ℕ ↦ Φ n) atTop (𝓝 0) :=
      hΦ.comp (tendsto_natCast_atTop_atTop.mono_right atTop_le_cocompact)
    simpa using h₁.sub h₂
  have hEc := continuous_associatedBilinForm_add_apply_self (ω := ω) hJc hSc
    (hξ.of_le (by norm_num))
  refine integrableOn_univ_prod_and_setIntegral_le_of_setIntegral_Icc_prod_le_add measurableSet_Icc
    (fun z _ ↦ add_nonneg (hg0 _ _) (hg0 _ _)) (fun z _ ↦ hg0 _ _)
    (fun n ↦ hEc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)) hD he
    fun n ↦ ?_
  have h := setIntegral_associatedBilinForm_stationaryCylinderOperator
    (fun t ↦ (hJ t).invariant) hJc hS hSc hξ hper
    (show -(n : ℝ) ≤ n by linarith [n.cast_nonneg (α := ℝ)])
  simp only [Φ] at h ⊢
  linarith

/-- **The estimate of the stationary cylinder operator at a nondegenerate orbit.** Let each
`J_t` be `ω`-compatible and depend continuously on `t`, let each `S_t` be infinitesimally
symplectic, and suppose that the return map `Ψ(1)` of `ζ' = S_t ζ` fixes no nonzero vector. Then
there is a constant `C ≥ 0` with the following property. For every `C²` map `ξ` of period one in
`t` which tends to zero together with `∂t ξ` as `|s| → ∞`, uniformly in `t`, and such that
`g(D ξ, D ξ)` is integrable on `ℝ × [0, 1]`, where `g_t = ω(·, J_t ·)`, the function `g(ξ, ξ)` is
integrable on `ℝ × [0, 1]` and `∫ g(ξ, ξ) ≤ C ∫ g(D ξ, D ξ)`. -/
theorem exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hnd : ∀ v, dysonSeriesLeft S 1 v = v → v = 0) :
    ∃ C, 0 ≤ C ∧ ∀ ξ : ℝ × ℝ → V, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      Tendsto (fun z ↦ (ξ z, fderiv ℝ ξ z stdComplexLineImag))
        (comap Prod.fst (cocompact ℝ)) (𝓝 0) →
      IntegrableOn (fun z ↦ ω.associatedBilinForm (J z.2)
        (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z))
        (univ ×ˢ Icc 0 1) →
      IntegrableOn (fun z ↦ ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) (univ ×ˢ Icc 0 1) ∧
        ∫ z in univ ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (ξ z) (ξ z) ≤
          C * ∫ z in univ ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z) := by
  have hJc' : Continuous J := AlmostComplexStructure.continuous_iff.2 <|
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC, hgap⟩ := exists_integral_associatedBilinForm_le_mul_integral_asymptoticOperator
    (fun t _ ↦ (hJ t).tames) hJc'.continuousOn hSc hnd
  refine ⟨C, hC, fun ξ hξ hper hdecay hD ↦ ?_⟩
  have hg0 (t : ℝ) (v : V) := (hJ t).associatedBilinForm_self_nonneg v
  have hgc {p : ℝ × ℝ → V} (hp : Continuous p) :=
    continuous_associatedBilinForm_apply_self (ω := ω) hJc hp
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv (by norm_num)
  set w : ℝ × ℝ → V := fun z ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z)
  have hwc : Continuous w :=
    (hdξ.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply hξ.continuous)
  set E : ℝ × ℝ → ℝ := fun z ↦
    ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
        (fderiv ℝ ξ z stdComplexLineReal) + ω.associatedBilinForm (J z.2) (w z) (w z)
  obtain ⟨hEi, hEle⟩ := integrableOn_and_setIntegral_le_setIntegral_stationaryCylinderOperator
    hJ hJc hS hSc hξ hper hdecay hD
  -- On each slice the spectral gap bounds `∫₀¹ g(ξ, ξ)` by `C ∫₀¹ g(w, w)`, `w = ∂t ξ - S ξ`.
  have hslice (s : ℝ) : ∫ t in Icc (0 : ℝ) 1, ω.associatedBilinForm (J t) (ξ (s, t)) (ξ (s, t)) ≤
      C * ∫ t in Icc (0 : ℝ) 1, ω.associatedBilinForm (J t) (w (s, t)) (w (s, t)) := by
    have hζ : ContDiff ℝ 1 fun t ↦ ξ (s, t) :=
      (hξ.comp (contDiff_prodMk_right s)).of_le (by norm_num)
    have hA (t : ℝ) : ω.associatedBilinForm (J t) (asymptoticOperator J S (fun t ↦ ξ (s, t)) t)
        (asymptoticOperator J S (fun t ↦ ξ (s, t)) t) =
          ω.associatedBilinForm (J t) (w (s, t)) (w (s, t)) := by
      have hd : deriv (fun t ↦ ξ (s, t)) t = fderiv ℝ ξ (s, t) stdComplexLineImag := by
        rw [stdComplexLineImag_eq]
        exact ((hξ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
          (hasDerivAt_prodMk_right s t)).deriv
      rw [asymptoticOperator_def, hd]
      exact ω.associatedBilinForm_apply_apply_self_eq (J t) _
    have h := hgap _ hζ (by simpa using hper s 0)
    simp only [hA] at h
    rwa [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  -- Integrating over the strips and letting them exhaust the cylinder.
  have hξi := integrableOn_univ_prod_and_setIntegral_le_of_setIntegral_Icc_prod_le_add (e := 0)
    measurableSet_Icc (fun z _ ↦ hg0 _ _) (fun z _ ↦ mul_nonneg hC (add_nonneg (hg0 _ _) (hg0 _ _)))
    (fun n ↦ (hgc hξ.continuous).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)) (hEi.const_mul C) tendsto_const_nhds fun n ↦ by
      rw [Pi.zero_apply, add_zero, integral_const_mul]
      refine (setIntegral_rect_le_mul_of_forall_setIntegral_le (hgc hξ.continuous).continuousOn
        (hgc hwc).continuousOn fun s _ ↦ hslice s).trans
        (mul_le_mul_of_nonneg_left (setIntegral_mono_on ?_ ?_
          (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_) hC)
      · exact (hgc hwc).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      · exact (continuous_associatedBilinForm_add_apply_self hJc hSc (hξ.of_le (by norm_num)))
          |>.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      · exact le_add_of_nonneg_left (hg0 _ _)
  refine ⟨hξi.1, hξi.2.trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hEle hC

end Cylinder

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

open Floer in
/-- **The weighted stationary cylinder estimate at a nondegenerate orbit.** Let `x` be a
nondegenerate one-periodic orbit of a one-periodic, jointly `C²` time-dependent Hamiltonian `H`
whose suspended vector field is globally Lipschitz, let `J_t` be a continuous one-periodic family
of `ω`-compatible structures, and let `D = ∂s + J_t (∂t - S_t)` be the stationary cylinder
operator along `x`, with `S_t = dX_{H_t}(x(t))`. Then for every weight `δ` close enough to `0`
there is a constant `C ≥ 0` such that every `C²` map `ξ` of period one in `t`, which tends to zero
together with `∂t ξ` as `|s| → ∞` and for which `g((D - δ) ξ, (D - δ) ξ)` is integrable on
`ℝ × [0, 1]`, satisfies `∫ g(ξ, ξ) ≤ C ∫ g((D - δ) ξ, (D - δ) ξ)` there, for
`g_t = ω(·, J_t ·)`. By `TauCeti.Floer.stationaryCylinderOperator_exp_smul`, `D - δ` is `D`
conjugated by the weight `e^{δ s}`. -/
theorem eventually_exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator_sub_smul
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → AlmostComplexStructure V} (hJ : ∀ t, ω.Compatible (J t)) (hJc : Continuous J)
    (hJp : Periodic J 1) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), ∃ C, 0 ≤ C ∧ ∀ ξ : ℝ × ℝ → V, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      Tendsto (fun z ↦ (ξ z, fderiv ℝ ξ z stdComplexLineImag))
        (comap Prod.fst (cocompact ℝ)) (𝓝 0) →
      IntegrableOn (fun z ↦ ω.associatedBilinForm (J z.2)
        (Floer.stationaryCylinderOperator J
          (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z - δ • ξ z)
        (Floer.stationaryCylinderOperator J
          (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z - δ • ξ z))
        (univ ×ˢ Icc 0 1) →
      IntegrableOn (fun z ↦ ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) (univ ×ˢ Icc 0 1) ∧
        ∫ z in univ ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (ξ z) (ξ z) ≤
          C * ∫ z in univ ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z - δ • ξ z)
            (Floer.stationaryCylinderOperator J
              (fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)) ξ z - δ • ξ z) := by
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H t)) (x t)
  have hSc : Continuous S := ω.continuous_fderiv_hamiltonianVectorField_comp hH
    (continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt)
  have hSp : Periodic S 1 := fun t ↦ by simp only [S, hHp t, hxp t]
  have hS (t : ℝ) (v w : V) : ω (S t v) w + ω v (S t w) = 0 :=
    ω.apply_fderiv_hamiltonianVectorField_add (hH.comp (contDiff_prodMk_right t)).contDiffAt v w
  have hJc' : Continuous fun p : ℝ × V ↦ J p.1 p.2 := by
    simpa using ((AlmostComplexStructure.continuous_iff.1 hJc).comp continuous_fst).clm_apply
      continuous_snd
  have hJop : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    AlmostComplexStructure.continuous_iff.1 hJc
  filter_upwards [ω.eventually_eq_zero_of_asymptoticOperator_eq_smul hX hH hHp hx hxp hnd hJc
    hJp] with δ hδ
  -- The weighted operator is the stationary cylinder operator of `S_t - δ J_t`.
  set Sδ : ℝ → V →L[ℝ] V :=
    fun t ↦ S t - δ • LinearMap.toContinuousLinearMap (J t).toLinearMap
  have hSδc : Continuous Sδ := hSc.sub (hJop.const_smul δ)
  have hSδp : Periodic Sδ 1 := fun t ↦ by simp only [Sδ, hSp t, hJp t]
  have hSδ (t : ℝ) (v w : V) : ω (Sδ t v) w + ω v (Sδ t w) = 0 := by
    have h₁ := hS t v w
    have h₂ := (hJ t).invariant.apply_add_apply_eq_zero v w
    simp only [Sδ, sub_apply, smul_apply,
      LinearMap.coe_toContinuousLinearMap', map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul] at h₂ ⊢
    linear_combination h₁ - δ * h₂
  -- Nondegeneracy of `A - δ` is nondegeneracy of the return map of `ζ' = (S_t - δ J_t) ζ`.
  have hndδ (v : V) (hv : dysonSeriesLeft Sδ 1 v = v) : v = 0 := by
    by_contra hne
    obtain ⟨ζ, hζ, hζp, hζne, hA⟩ :=
      (exists_ne_zero_asymptoticOperator_eq_zero_iff_exists_ne_zero_dysonSeriesLeft_apply_eq_self
        (J := J) hSδc hSδp).2 ⟨v, hne, hv⟩
    refine hζne (hδ ζ hζ hζp fun t ↦ ?_)
    have h := hA t
    rwa [Floer.asymptoticOperator_sub_smul, sub_eq_zero] at h
  obtain ⟨C, hC, hest⟩ := Floer.exists_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    hJ hJc' hSδ hSδc hndδ
  refine ⟨C, hC, fun ξ hξ hper hdecay hD ↦ ?_⟩
  have heq (z : ℝ × ℝ) : Floer.stationaryCylinderOperator J Sδ ξ z =
      Floer.stationaryCylinderOperator J S ξ z - δ • ξ z :=
    Floer.stationaryCylinderOperator_sub_smul δ ξ z
  simpa only [heq] using hest ξ hξ hper hdecay (by simpa only [heq] using hD)

end SymplecticForm

end TauCeti
