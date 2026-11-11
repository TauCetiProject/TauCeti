/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Action
public import TauCeti.Geometry.Symplectic.Floer.Energy
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Symplectic.Floer.Translation.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.ApproximateBound
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import TauCeti.Topology.UniformSpace.UniformConvergence.Translate

/-!
# Limits of translated Floer cylinders

Along a cylindrical end of a Floer trajectory, or of a pair of pants, a solution with finite
energy breaks off Hamiltonian orbits: translating it further and further along the end, the
translates converge to a stationary cylinder `(s, t) ↦ x(t)` over a Hamiltonian orbit `x`. This
file proves the identification of the limit, which is the first step of Floer breaking at an end.

Let `u` solve the Floer equation `∂_s u + J (∂_t u - X_{H_t}(u)) = 0` for the cylindrical
perturbation `K = H_t dt` on a part `E` of the strip `ℝ × [0, 1]`, for almost complex structures
`J z` with uniform tameness constants `c ‖v‖² ≤ ω(v, J z v)` and `‖J z v‖ ≤ M ‖v‖`, and let `u` have
finite energy over `E`. Let `s_k` be translation parameters tending to infinity, in either
direction, such that every window `[a + s_k, b + s_k] × [0, 1]` eventually lies in `E`; for
instance `E = [s₀, ∞) × [0, 1]` and `s_k → ∞`. Suppose that the translates
`(s, t) ↦ u(s + s_k, t)` converge locally uniformly on the strip to a map `v`. Then:

* `v` does not depend on `s` (`SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add`);
* `x(t) = v(0, t)` is an orbit of the Hamiltonian vector field, `x'(t) = X_{H_t}(x(t))` on
  `[0, 1]` (`SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`);
* if `u(s, 0) = u(s, 1)` on `E`, then `x(0) = x(1)`, so that `x` is a one-periodic orbit for a
  one-periodic Hamiltonian; this boundary condition passes to the limit of the translates by the
  general `TauCeti.apply_eq_apply_of_tendstoLocallyUniformlyOn_comp_add`;
* the limit is a stationary Floer cylinder: its perturbed derivative `dv - X_K(v)` vanishes on the
  open strip (`SymplecticForm.perturbedFDeriv_eq_zero_of_tendstoLocallyUniformlyOn_comp_add`).

If the derivatives of the translates also converge locally uniformly on the strip, to the
derivative of `v`, then the actions `A_H(u(s_k, ·))` of the end loops converge to the action of
`x` (`SymplecticForm.tendsto_hamiltonianAction_of_tendstoLocallyUniformlyOn_comp_add`). This uses
the continuity of the action for uniform `C¹` convergence of loops
(`SymplecticForm.tendsto_hamiltonianAction`). So the limiting end actions, in terms of which the
energy identity is stated, are actions of Hamiltonian orbits.

The argument is the following. By finiteness of the energy, the energy over the translated
windows tends to zero (`TauCeti.tendsto_setLIntegral_of_eventually_subset`). By the coercivity of
the energy density under tameness
(`SymplecticForm.setLIntegral_norm_sq_add_norm_sq_perturbedFDeriv_le`), the `L²` norm, hence the
`L¹` norm, of the perturbed derivative over the windows tends to zero. Its `s`-component is
`∂_s u`, whose integral along a horizontal segment is the variation of `u` along it; its
`t`-component is `∂_t u - X_{H_t}(u)`, whose integral along a vertical segment is the defect of
`u` from the integral equation of the Hamiltonian flow. Both defects therefore vanish in the
limit, which converges uniformly on compact windows.

The convergence of the translates is an assumption here. For periodic data and a solution with
image in a compact set, it comes from the bounded derivatives of finite-energy solutions on
cylindrical ends: `TauCeti.Geometry.Symplectic.Floer.CylindricalEnd` extracts locally uniformly
convergent subsequences of translates and applies the results of this file to them. The
nondegeneracy of the orbits, the convergence of the whole half-cylinder rather than a sequence of
translates, and the exponential decay along the end are not treated here.

## Main results

* `SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add`: the limit of the translates is
  independent of `s`.
* `SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`: the limit is a
  Hamiltonian orbit.
* `SymplecticForm.perturbedFDeriv_eq_zero_of_tendstoLocallyUniformlyOn_comp_add`: the limit is a
  stationary Floer cylinder.
* `SymplecticForm.tendsto_hamiltonianAction_of_tendstoLocallyUniformlyOn_comp_add`: the actions of
  the end loops converge to the action of the limit loop.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer cylinders and their limits at the ends.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 4.5 and the
  chapter on Floer homology, on the removal of the ends of finite-energy solutions.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {H : ℝ → V → ℝ} {u : ℝ × ℝ → V} {U : Set (ℝ × ℝ)}

section Segments

/-- For `K = H_t dt` the `s`-component of the perturbed derivative of a `C¹` map is continuous. -/
private theorem continuousOn_perturbedFDeriv_cylindrical_stdComplexLineReal (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) :
    ContinuousOn
      (fun z ↦ ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal) U := by
  simp_rw [perturbedFDeriv_cylindrical_apply_stdComplexLineReal]
  exact (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const

/-- For `K = H_t dt` with `H` jointly `C¹`, the `t`-component of the perturbed derivative of a `C¹`
map is continuous. -/
private theorem continuousOn_perturbedFDeriv_cylindrical_stdComplexLineImag
    (hH : ContDiff ℝ 1 (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) :
    ContinuousOn
      (fun z ↦ ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag) U := by
  simp_rw [perturbedFDeriv_cylindrical_apply_stdComplexLineImag]
  exact ((hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).sub
    ((ω.continuous_uncurry_hamiltonianVectorField hH).comp_continuousOn
      (continuousOn_snd.prodMk hu.continuousOn))

/-- Along a horizontal segment the variation of `u` is the integral of the `s`-component
`∂_s u` of the perturbed derivative for `K = H_t dt`. Integrating over `t ∈ [0, 1]`, the
variation between the two vertical sides of `[α, β] × [0, 1]` is controlled by the `L¹` norm of
this component over the rectangle. -/
private theorem lintegral_edist_le (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) {α β : ℝ}
    (hαβ : α ≤ β) (hR : Icc α β ×ˢ Icc 0 1 ⊆ U) :
    ∫⁻ t in Icc (0 : ℝ) 1, edist (u (β, t)) (u (α, t)) ≤
      ∫⁻ z in Icc α β ×ˢ Icc 0 1,
        ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal‖ₑ := by
  have hcont : ContinuousOn (fun z ↦ fderiv ℝ u z (1, 0)) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  simp_rw [perturbedFDeriv_cylindrical_apply_stdComplexLineReal]
  rw [Measure.volume_eq_prod, setLIntegral_prod_symm (fun z ↦ ‖fderiv ℝ u z (1, 0)‖ₑ)
    ((hcont.mono hR).enorm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc))]
  refine setLIntegral_mono' measurableSet_Icc fun t ht ↦ ?_
  have hmem {r : ℝ} (hr : r ∈ uIcc α β) : (r, t) ∈ U := hR ⟨by rwa [uIcc_of_le hαβ] at hr, ht⟩
  -- The fundamental theorem of calculus along the segment `[α, β] × {t}`.
  have hderiv : ∀ r ∈ uIcc α β, HasDerivAt (fun r ↦ u (r, t)) (fderiv ℝ u (r, t) (1, 0)) r :=
    fun r hr ↦ hasDerivAt_slice_left
      ((hu.differentiableOn one_ne_zero _ (hmem hr)).differentiableAt (hU.mem_nhds (hmem hr)))
  have hint : IntervalIntegrable (fun r ↦ fderiv ℝ u (r, t) (1, 0)) volume α β :=
    (hcont.comp (by fun_prop) fun r hr ↦ hmem hr).intervalIntegrable
  rw [edist_eq_enorm_sub, ← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    intervalIntegral.integral_of_le hαβ]
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set Ioc_subset_Icc_self)

/-- Along a vertical segment `{r} × [t₁, t₂]` the defect of `u` from the integral equation of the
Hamiltonian flow is the integral of the `t`-component `∂_t u - X_{H_t}(u)` of the perturbed
derivative for `K = H_t dt`. Integrating over `r ∈ [α, β]`, the defect is controlled by the `L¹`
norm of this component over the rectangle `[α, β] × [0, 1]`. -/
private theorem lintegral_enorm_sub_sub_integral_le (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) {α β t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂)
    (ht₂ : t₂ ≤ 1) (hR : Icc α β ×ˢ Icc 0 1 ⊆ U) :
    ∫⁻ r in Icc α β, ‖u (r, t₂) - u (r, t₁) -
        ∫ t in t₁..t₂, ω.hamiltonianVectorField (H t) (u (r, t))‖ₑ ≤
      ∫⁻ z in Icc α β ×ˢ Icc 0 1,
        ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag‖ₑ := by
  have hX := ω.continuous_uncurry_hamiltonianVectorField hH
  have hcont : ContinuousOn (fun z ↦ fderiv ℝ u z (0, 1)) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hcontX : ContinuousOn (fun z : ℝ × ℝ ↦ ω.hamiltonianVectorField (H z.2) (u z)) U :=
    hX.comp_continuousOn (continuousOn_snd.prodMk hu.continuousOn)
  simp_rw [perturbedFDeriv_cylindrical_apply_stdComplexLineImag]
  rw [Measure.volume_eq_prod, setLIntegral_prod
    (fun z ↦ ‖fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z)‖ₑ)
    (((hcont.sub hcontX).mono hR).enorm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc))]
  refine setLIntegral_mono' measurableSet_Icc fun r hr ↦ ?_
  dsimp only
  have hsub : uIcc t₁ t₂ ⊆ Icc 0 1 := uIcc_subset_Icc ⟨ht₁, ht.trans ht₂⟩ ⟨ht₁.trans ht, ht₂⟩
  have hmem {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : (r, t) ∈ U := hR ⟨hr, hsub htm⟩
  -- The fundamental theorem of calculus along the segment `{r} × [t₁, t₂]`.
  have hderiv : ∀ t ∈ uIcc t₁ t₂, HasDerivAt (fun t ↦ u (r, t)) (fderiv ℝ u (r, t) (0, 1)) t :=
    fun t htm ↦ hasDerivAt_slice_right
      ((hu.differentiableOn one_ne_zero _ (hmem htm)).differentiableAt (hU.mem_nhds (hmem htm)))
  have hint : IntervalIntegrable (fun t ↦ fderiv ℝ u (r, t) (0, 1)) volume t₁ t₂ :=
    (hcont.comp (by fun_prop) fun t htm ↦ hmem htm).intervalIntegrable
  have hintX :
      IntervalIntegrable (fun t ↦ ω.hamiltonianVectorField (H t) (u (r, t))) volume t₁ t₂ :=
    (hcontX.comp (by fun_prop) fun t htm ↦ hmem htm).intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    ← intervalIntegral.integral_sub hint hintX, intervalIntegral.integral_of_le ht]
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht₁ ht₂)))

end Segments

section Limit

variable {E : Set (ℝ × ℝ)} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ} {s : ℕ → ℝ}
  {v : ℝ × ℝ → V}

/-- The `L²` norm of the perturbed derivative over the translated windows tends to zero, by the
coercivity of the energy density and the finiteness of the energy. -/
private theorem tendsto_lintegral_norm_sq_perturbedFDeriv
    (hc : 0 < c) (hJc : ∀ z ∈ E, ∀ w, c * ‖w‖ ^ 2 ≤ ω w (J z w))
    (hJM : ∀ z ∈ E, ∀ w, ‖J z w‖ ≤ M * ‖w‖)
    (hfloer : ∀ z ∈ E, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in E,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E) (a b : ℝ) :
    Tendsto (fun k ↦ ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
      ENNReal.ofReal
        (‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal‖ ^ 2 +
          ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag‖ ^ 2))
      atTop (𝓝 0) := by
  have hE := tendsto_setLIntegral_of_eventually_subset hfin
    (A := fun k ↦ Icc (a + s k) (b + s k) ×ˢ Icc 0 1)
    (eventually_Icc_add_prod_subset_inter hs (hW a b))
  have hlim := ENNReal.Tendsto.const_mul hE (Or.inr (ENNReal.ofReal_ne_top (r := (1 + M ^ 2) / c)))
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hW a b] with k hk
  exact ω.setLIntegral_norm_sq_add_norm_sq_perturbedFDeriv_le
    (measurableSet_Icc.prod measurableSet_Icc) hc (fun z hz ↦ hJc z (hk hz))
    (fun z hz ↦ hJM z (hk hz)) fun z hz ↦ hfloer z (hk hz)

/-- On windows of a fixed size, the `L¹` norm of a continuous function is controlled by its `L²`
norm, so the `L¹` norm of each component of the perturbed derivative over the translated windows
tends to zero. -/
private theorem tendsto_lintegral_enorm_perturbedFDeriv (hEU : E ⊆ U)
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E) {e : ℝ × ℝ}
    (he : e = stdComplexLineReal ∨ e = stdComplexLineImag)
    (hg : ContinuousOn (fun z ↦ ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z e) U) {a b : ℝ}
    (h : Tendsto (fun k ↦ ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
      ENNReal.ofReal
        (‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal‖ ^ 2 +
          ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag‖ ^ 2))
      atTop (𝓝 0)) :
    Tendsto (fun k ↦ ∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1,
      ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z e‖ₑ) atTop (𝓝 0) := by
  set g : ℝ × ℝ → V := fun z ↦ ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z e
  have hvol (k : ℕ) :
      volume (Icc (a + s k) (b + s k) ×ˢ Icc (0 : ℝ) 1) = ENNReal.ofReal (b - a) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    simp
  -- The square of a component is bounded by the sum of the squares of both components.
  have hsq (z : ℝ × ℝ) : ‖g z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal
      (‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal‖ ^ 2 +
        ‖ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_two]
    rcases he with rfl | rfl
    · exact le_add_of_nonneg_right (sq_nonneg _)
    · exact le_add_of_nonneg_left (sq_nonneg _)
  have h2 : Tendsto (fun k ↦ (∫⁻ z in Icc (a + s k) (b + s k) ×ˢ Icc 0 1, ‖g z‖ₑ ^ (2 : ℝ)) ^
      (1 / (2 : ℝ)) * ENNReal.ofReal (b - a) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have h' := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun k ↦ lintegral_mono hsq)
    have h'' := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h'
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h''
    simpa using ENNReal.Tendsto.mul_const h''
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hW a b] with k hk
  -- Hölder's inequality on the window, which has measure `b - a`.
  have hmeas : AEStronglyMeasurable g
      (volume.restrict (Icc (a + s k) (b + s k) ×ˢ Icc (0 : ℝ) 1)) :=
    (hg.mono (hk.trans hEU)).aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc)
  have hL := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) one_le_two hmeas
  rw [eLpNorm_one_eq_lintegral_enorm hmeas,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hmeas,
    Measure.restrict_apply_univ, hvol] at hL
  convert hL using 3 <;> norm_num

/-- **The limit of translated Floer cylinders is stationary.** Let `u` be `C¹` on an open set `U`
and solve the Floer equation for the cylindrical perturbation `K = H_t dt` on `E ⊆ U`, for almost
complex structures with `c ‖w‖² ≤ ω(w, J z w)` and `‖J z w‖ ≤ M ‖w‖` on `E`, where `c > 0`, and
let `u` have finite energy over `E`. Let `s_k` tend to infinity, in either direction, such that
each window `[a + s_k, b + s_k] × [0, 1]` eventually lies in `E`. If the translates
`(s, t) ↦ u(s + s_k, t)` converge locally uniformly on the strip `ℝ × [0, 1]` to `v`, then `v`
does not depend on `s`. -/
theorem eq_of_tendstoLocallyUniformlyOn_comp_add
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hEU : E ⊆ U) (hc : 0 < c)
    (hJc : ∀ z ∈ E, ∀ w, c * ‖w‖ ^ 2 ≤ ω w (J z w)) (hJM : ∀ z ∈ E, ∀ w, ‖J z w‖ ≤ M * ‖w‖)
    (hfloer : ∀ z ∈ E, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in E,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E)
    (hv : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) :
    ∀ r, ∀ t ∈ Icc (0 : ℝ) 1, v (r, t) = v (0, t) := by
  -- It suffices to compare the two vertical sides of a rectangle `[α, β] × [0, 1]`.
  have key {α β : ℝ} (hαβ : α ≤ β) : ∀ t ∈ Icc (0 : ℝ) 1, v (β, t) = v (α, t) := by
    obtain ⟨hUC, -, hvK⟩ := tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn isCompact_Icc
      (hu.continuousOn.mono hEU) (hW α β) hv
    have hsides {γ : ℝ} (hγ : γ ∈ Icc α β) : ContinuousOn (fun t ↦ v (γ, t)) (Icc 0 1) :=
      hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦ ⟨hγ, ht⟩
    have hβ : β ∈ Icc α β := ⟨hαβ, le_rfl⟩
    have hα : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
    -- The mean distance between the two sides vanishes.
    have hzero : ∫⁻ t in Icc (0 : ℝ) 1, edist (v (β, t)) (v (α, t)) = 0 := by
      refine lintegral_eq_zero_of_eventually_le_add
        (f := fun k t ↦ edist (u (β + s k, t)) (u (α + s k, t)))
        (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          (tendsto_lintegral_enorm_perturbedFDeriv hEU hW (Or.inl rfl)
            (continuousOn_perturbedFDeriv_cylindrical_stdComplexLineReal hU hu)
            (tendsto_lintegral_norm_sq_perturbedFDeriv hc hJc hJM hfloer hfin hs hW α β))
          (Eventually.of_forall fun _ ↦ zero_le) ?_) fun ε hε ↦ ?_
      · filter_upwards [hW α β] with k hk
        exact lintegral_edist_le hU hu (by linarith) (hk.trans hEU)
      · filter_upwards [EMetric.tendstoUniformlyOn_iff.1 hUC (ε / 2)
          (ENNReal.half_pos (by exact_mod_cast hε.ne'))] with k hk
        refine ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ ?_
        have h₁ := hk (β, t) ⟨hβ, ht⟩
        have h₂ := hk (α, t) ⟨hα, ht⟩
        simp only [Prod.mk_add_mk, add_zero] at h₁ h₂
        calc edist (v (β, t)) (v (α, t))
            ≤ edist (v (β, t)) (u (β + s k, t)) + edist (u (β + s k, t)) (u (α + s k, t)) +
                edist (u (α + s k, t)) (v (α, t)) := edist_triangle4 _ _ _ _
          _ ≤ ε / 2 + edist (u (β + s k, t)) (u (α + s k, t)) + ε / 2 := by
              rw [edist_comm (u (α + s k, t))]
              gcongr
          _ = edist (u (β + s k, t)) (u (α + s k, t)) + ε := by
              rw [add_comm (_ / 2), add_assoc, ENNReal.add_halves]
    have hae := (lintegral_eq_zero_iff' ((continuous_edist.comp_continuousOn
      ((hsides hβ).prodMk (hsides hα))).aemeasurable measurableSet_Icc)).1 hzero
    exact Measure.eqOn_Icc_of_ae_eq volume zero_ne_one (hae.mono fun t ht ↦ edist_eq_zero.1 ht)
      (hsides hβ) (hsides hα)
  intro r t ht
  rcases le_total r 0 with hr | hr
  · exact (key hr t ht).symm
  · exact key hr t ht

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- If the translates of `u` converge uniformly on the window `[0, 1] × [0, 1]` to a continuous
`v`, then the values of a continuous vector field `Φ`, evaluated at the translates together with
the `t`-coordinate, converge uniformly there too. -/
private theorem tendstoUniformlyOn_comp_snd_prodMk {Φ : ℝ × V → V} (hΦ : Continuous Φ)
    (hUC : TendstoUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop (Icc 0 1 ×ˢ Icc 0 1))
    (hvK : ContinuousOn v (Icc 0 1 ×ˢ Icc 0 1)) :
    TendstoUniformlyOn (fun k z ↦ Φ (z.2, u (z + (s k, 0)))) (fun z ↦ Φ (z.2, v z))
      atTop (Icc 0 1 ×ˢ Icc 0 1) := by
  have hpair : TendstoUniformlyOn (fun k z ↦ (z.2, u (z + (s k, 0)))) (fun z ↦ (z.2, v z))
      atTop (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hUC ⊢
    intro ε hε
    filter_upwards [hUC ε hε] with k hk z hz
    simpa [Prod.dist_eq] using hk z hz
  exact ((isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
    (continuousOn_snd.prodMk hvK)).comp_tendstoUniformlyOn (fun _ _ ↦ hΦ.continuousAt) hpair

omit [FiniteDimensional ℝ V] in
/-- The defect of the integral equation of the Hamiltonian flow along the limit path `v (0, ·)` is
eventually, for almost every `r ∈ [0, 1]`, at most `ε` more than the defect of the translate of
`u` along the segment `{r + s k} × [t₁, t₂]`, by the uniform convergence of the translates and of
the vector field along them. -/
private theorem eventually_ae_enorm_sub_sub_integral_le_add {Φ : ℝ × V → V} (hΦ : Continuous Φ)
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1)
    (hUC : TendstoUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop (Icc 0 1 ×ˢ Icc 0 1))
    (hΦUC : TendstoUniformlyOn (fun k z ↦ Φ (z.2, u (z + (s k, 0)))) (fun z ↦ Φ (z.2, v z))
      atTop (Icc 0 1 ×ˢ Icc 0 1))
    (hFc : ∀ᶠ k in atTop, ContinuousOn (fun z ↦ u (z + (s k, 0))) (Icc 0 1 ×ˢ Icc 0 1))
    (hvK : ContinuousOn v (Icc 0 1 ×ˢ Icc 0 1))
    (hstat : ∀ r, ∀ t ∈ Icc (0 : ℝ) 1, v (r, t) = v (0, t)) (ε : ℝ≥0) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ᵐ r ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖v (0, t₂) - v (0, t₁) - ∫ t in t₁..t₂, Φ (t, v (0, t))‖ₑ ≤
        ‖u (r + s k, t₂) - u (r + s k, t₁) - ∫ t in t₁..t₂, Φ (t, u (r + s k, t))‖ₑ + ε := by
  have hsub : uIcc t₁ t₂ ⊆ Icc 0 1 := uIcc_subset_Icc ⟨ht₁, ht.trans ht₂⟩ ⟨ht₁.trans ht, ht₂⟩
  set δ : ℝ := ε / 3 with hδε
  have hδ : 0 < δ := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hUC δ hδ,
    Metric.tendstoUniformlyOn_iff.1 hΦUC δ hδ, hFc] with k hk hkΦ hkc
  refine ae_restrict_of_forall_mem measurableSet_Icc fun r hr ↦ ?_
  have hmem {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : (r, t) ∈ Icc (0 : ℝ) 1 ×ˢ Icc 0 1 :=
    ⟨hr, hsub htm⟩
  have hF (t : ℝ) : u ((r, t) + (s k, 0)) = u (r + s k, t) := by simp
  -- Along the segment the limit is `v(0, ·)`, and the translates are uniformly close to it.
  have hxv : ∫ t in t₁..t₂, Φ (t, v (0, t)) = ∫ t in t₁..t₂, Φ (t, v (r, t)) :=
    intervalIntegral.integral_congr fun t htm ↦ by
      simp only [hstat r t (hsub htm)]
  have hcv : ContinuousOn (fun t ↦ Φ (t, v (r, t))) (uIcc t₁ t₂) :=
    hΦ.comp_continuousOn (continuousOn_id.prodMk
      (hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t htm ↦ hmem htm))
  have hcu : ContinuousOn (fun t ↦ Φ (t, u (r + s k, t))) (uIcc t₁ t₂) := by
    refine hΦ.comp_continuousOn (continuousOn_id.prodMk ?_)
    simp_rw [← hF]
    exact hkc.comp (continuousOn_const.prodMk continuousOn_id) fun t htm ↦ hmem htm
  have hend {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : ‖v (0, t) - u (r + s k, t)‖ ≤ δ := by
    have h := hk (r, t) (hmem htm)
    rw [dist_eq_norm, hF, hstat r t (hsub htm)] at h
    exact h.le
  have hA := intervalIntegral.norm_sub_sub_integral_le (a₁ := v (0, t₁)) (a₂ := v (0, t₂))
    (b₁ := u (r + s k, t₁)) (b₂ := u (r + s k, t₂)) hcv.intervalIntegrable
    hcu.intervalIntegrable fun t htm ↦ by
      have h := hkΦ (r, t) (hmem (uIoc_subset_uIcc htm))
      rw [dist_eq_norm, hF] at h
      exact h.le
  rw [← hxv] at hA
  have hlen : δ * |t₂ - t₁| ≤ δ :=
    mul_le_of_le_one_right hδ.le (by rw [abs_of_nonneg (sub_nonneg.2 ht)]; linarith)
  replace hA := hA.trans (by linarith [hend left_mem_uIcc, hend right_mem_uIcc] :
    _ ≤ ‖u (r + s k, t₂) - u (r + s k, t₁) - ∫ t in t₁..t₂, Φ (t, u (r + s k, t))‖ + ε)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hA

/-- Under the hypotheses of `TauCeti.SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add`, and
for a jointly `C¹` Hamiltonian `H`, the path `x(t) = v(0, t)` satisfies the integral equation
`x(t₂) - x(t₁) = ∫_{t₁}^{t₂} X_{H_t}(x(t)) dt` of the Hamiltonian flow for `0 ≤ t₁ ≤ t₂ ≤ 1`. -/
private theorem sub_sub_integral_eq_zero_of_tendstoLocallyUniformlyOn_comp_add
    (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hEU : E ⊆ U) (hc : 0 < c)
    (hJc : ∀ z ∈ E, ∀ w, c * ‖w‖ ^ 2 ≤ ω w (J z w)) (hJM : ∀ z ∈ E, ∀ w, ‖J z w‖ ≤ M * ‖w‖)
    (hfloer : ∀ z ∈ E, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in E,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E)
    (hv : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1) :
    v (0, t₂) - v (0, t₁) - ∫ t in t₁..t₂, ω.hamiltonianVectorField (H t) (v (0, t)) = 0 := by
  have hstat := eq_of_tendstoLocallyUniformlyOn_comp_add hU hu hEU hc hJc hJM hfloer hfin hs hW hv
  set Φ : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2
  have hΦ : Continuous Φ := ω.continuous_uncurry_hamiltonianVectorField hH
  obtain ⟨hUC, hFc, hvK⟩ := tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn isCompact_Icc
    (hu.continuousOn.mono hEU) (hW 0 1) hv
  -- The vector field along the translates converges uniformly on `[0, 1] × [0, 1]`, since `Φ` is
  -- continuous on the compact set of values of the limit.
  have hΦUC := tendstoUniformlyOn_comp_snd_prodMk hΦ hUC hvK
  set A := v (0, t₂) - v (0, t₁) - ∫ t in t₁..t₂, Φ (t, v (0, t))
  -- The defects of the translates along the segments `{r} × [t₁, t₂]` tend to zero in `L¹`, and
  -- they converge uniformly in `r ∈ [0, 1]` to the defect `A` of the limit.
  have hzero : ∫⁻ r in Icc (0 : ℝ) 1, ‖A‖ₑ = 0 := by
    refine lintegral_eq_zero_of_eventually_le_add
      (f := fun k r ↦ ‖u (r + s k, t₂) - u (r + s k, t₁) -
        ∫ t in t₁..t₂, Φ (t, u (r + s k, t))‖ₑ)
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_lintegral_enorm_perturbedFDeriv hEU hW (Or.inr rfl)
          (continuousOn_perturbedFDeriv_cylindrical_stdComplexLineImag hH hU hu)
          (tendsto_lintegral_norm_sq_perturbedFDeriv hc hJc hJM hfloer hfin hs hW 0 1))
        (Eventually.of_forall fun _ ↦ zero_le) ?_) fun ε hε ↦ ?_
    · filter_upwards [hW 0 1] with k hk
      refine le_of_eq_of_le ?_ (lintegral_enorm_sub_sub_integral_le hH hU hu ht₁ ht ht₂
        (hk.trans hEU))
      -- Translate the segments `{r} × [t₁, t₂]` back to `r ∈ [0, 1]`.
      have hT := (measurePreserving_add_right volume (s k)).setLIntegral_comp_preimage_emb
        (measurableEmbedding_addRight _)
        (fun r ↦ ‖u (r, t₂) - u (r, t₁) - ∫ t in t₁..t₂, Φ (t, u (r, t))‖ₑ)
        (Icc (0 + s k) (1 + s k))
      rwa [preimage_add_const_Icc, add_sub_cancel_right, add_sub_cancel_right] at hT
    · exact eventually_ae_enorm_sub_sub_integral_le_add hΦ ht₁ ht ht₂ hUC hΦUC hFc hvK hstat ε hε
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at hzero
  exact enorm_eq_zero.1 hzero

/-- **The limit of translated Floer cylinders is a Hamiltonian orbit.** Under the hypotheses of
`TauCeti.SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add`, and for a jointly `C¹`
Hamiltonian `H`, the path `x(t) = v(0, t)`,
along which the limit `v(s, t) = x(t)` is stationary, solves `x'(t) = X_{H_t}(x(t))` on
`[0, 1]`. -/
theorem hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hEU : E ⊆ U) (hc : 0 < c)
    (hJc : ∀ z ∈ E, ∀ w, c * ‖w‖ ^ 2 ≤ ω w (J z w)) (hJM : ∀ z ∈ E, ∀ w, ‖J z w‖ ≤ M * ‖w‖)
    (hfloer : ∀ z ∈ E, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in E,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E)
    (hv : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) :
    ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t ↦ v (0, t))
      (ω.hamiltonianVectorField (H t) (v (0, t))) (Icc 0 1) t := by
  obtain ⟨-, -, hvK⟩ := tendstoUniformlyOn_Icc_prod_comp_add_and_continuousOn isCompact_Icc
    (hu.continuousOn.mono hEU) (hW 0 1) hv
  have hx : ContinuousOn (fun t ↦ v (0, t)) (Icc 0 1) :=
    hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦
      ⟨left_mem_Icc.2 zero_le_one, ht⟩
  have hf : ContinuousOn (fun t ↦ ω.hamiltonianVectorField (H t) (v (0, t))) (Icc 0 1) :=
    (ω.continuous_uncurry_hamiltonianVectorField hH).comp_continuousOn
      (continuousOn_id.prodMk hx)
  -- By the integral equation, `x(t) = v(0, t)` is a primitive of the vector field along it.
  intro t ht
  have : Fact (t ∈ Icc (0 : ℝ) 1) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (s := Icc 0 1)
    (t := Icc 0 1) (hf.mono (uIcc_subset_Icc (left_mem_Icc.2 zero_le_one) ht)).intervalIntegrable
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)
  refine (hd.const_add (v (0, 0))).congr_of_mem (fun τ hτ ↦ ?_) ht
  have h := sub_sub_integral_eq_zero_of_tendstoLocallyUniformlyOn_comp_add hH hU hu hEU hc hJc
    hJM hfloer hfin hs hW hv le_rfl hτ.1 hτ.2
  rw [← sub_eq_zero, ← h]
  abel

/-- **The limit of translated Floer cylinders is a stationary solution.** Under the hypotheses
of `TauCeti.SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add`, and for a jointly `C¹`
Hamiltonian `H`, the perturbed derivative
`dv - X_K(v)` of the limit vanishes on the open strip `ℝ × (0, 1)`: the limit is the stationary
solution `(s, t) ↦ v(0, t)` over a Hamiltonian orbit. -/
theorem perturbedFDeriv_eq_zero_of_tendstoLocallyUniformlyOn_comp_add
    (hH : ContDiff ℝ 1 (uncurry H))
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hEU : E ⊆ U) (hc : 0 < c)
    (hJc : ∀ z ∈ E, ∀ w, c * ‖w‖ ^ 2 ≤ ω w (J z w)) (hJM : ∀ z ∈ E, ∀ w, ‖J z w‖ ≤ M * ‖w‖)
    (hfloer : ∀ z ∈ E, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hfin : ∫⁻ z in E,
      ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u z) ≠ ⊤)
    (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E)
    (hv : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) :
    ∀ z ∈ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1,
      ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) v z = 0 := by
  intro z hz
  have hstat := eq_of_tendstoLocallyUniformlyOn_comp_add hU hu hEU hc hJc hJM hfloer hfin hs hW hv
  have hder := hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add hH hU hu hEU hc hJc hJM
    hfloer hfin hs hW hv z.2 (Ioo_subset_Icc_self hz.2)
  -- Near `z` the limit is the stationary map `(s, t) ↦ v(0, t)`.
  have hev : v =ᶠ[𝓝 z] fun w ↦ v (0, w.2) :=
    Filter.mem_of_superset ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)
      fun w hw ↦ hstat w.1 w.2 (Ioo_subset_Icc_self hw.2)
  have hd := hder.hasDerivAt (Icc_mem_nhds hz.2.1 hz.2.2)
  rw [ω.perturbedFDeriv_congr_of_eventuallyEq _ _ hev]
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [perturbedFDeriv_comp_snd_apply hd.differentiableAt, hd.deriv]
  simp

end Limit

section Action

variable {s : ℕ → ℝ} {v : ℝ × ℝ → V}

/-- **The end actions converge to the action of the limit loop.** Let `H` be a continuous
time-dependent Hamiltonian and let `u` be `C¹` on an open set `U` that eventually contains the
segments `{s_k} × [0, 1]`. If the translates `(s, t) ↦ u(s + s_k, t)` and their derivatives
converge locally uniformly on the strip `ℝ × [0, 1]` to `v` and to the derivative of `v`, where `v`
is differentiable along `{0} × [0, 1]`, then the actions of the loops `t ↦ u(s_k, t)` converge to
the action of the loop `x(t) = v(0, t)`.

Under the hypotheses of
`TauCeti.SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`, `x` is a
Hamiltonian orbit, so the end actions converge to the action of an orbit. -/
theorem tendsto_hamiltonianAction_of_tendstoLocallyUniformlyOn_comp_add
    (hH : Continuous (uncurry H)) (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U)
    (hsU : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) 1, (s k, t) ∈ U)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ v (0, t))
    (hx : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1))
    (hdx : TendstoLocallyUniformlyOn (fun k z ↦ fderiv ℝ u (z + (s k, 0))) (fderiv ℝ v) atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) :
    Tendsto (fun k ↦ ω.hamiltonianAction H (fun t ↦ u (s k, t))) atTop
      (𝓝 (ω.hamiltonianAction H (fun t ↦ v (0, t)))) := by
  set γ : ℝ → ℝ × ℝ := fun t ↦ (0, t)
  have hγ : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' (γ '' Icc 0 1) := subset_preimage_image γ _
  have hK : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image (by fun_prop)
  have hKs : γ '' Icc 0 1 ⊆ (univ : Set ℝ) ×ˢ Icc 0 1 := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨mem_univ _, ht⟩
  have hdiff : ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (s k, t) :=
    hsU.mono fun k hk t ht ↦
      (hu.differentiableOn one_ne_zero _ (hk t ht)).differentiableAt (hU.mem_nhds (hk t ht))
  have hline (k : ℕ) : Continuous fun t : ℝ ↦ (s k, t) := by fun_prop
  -- The loops and their derivatives, which are the `∂_t` derivatives of the maps, converge
  -- uniformly on `[0, 1]`.
  refine ω.tendsto_hamiltonianAction hH
    (hsU.mono fun k hk ↦ hu.continuousOn.comp (hline k).continuousOn fun t ht ↦ hk t ht)
    ((hsU.and hdiff).mono fun k hk ↦
      (((hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).comp
        (hline k).continuousOn fun t ht ↦ hk.1 t ht).congr fun t ht ↦
          (hasDerivAt_slice_right (hk.2 t ht)).deriv)
    ?_ ?_
  · simpa [comp_def, γ] using
      (((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1
        (hx.mono hKs)).comp γ).mono hγ
  · have h := (((ContinuousLinearMap.apply ℝ V ((0 : ℝ), (1 : ℝ))).uniformContinuous
      |>.comp_tendstoUniformlyOn ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
        hK).1 (hdx.mono hKs))).comp γ).mono hγ
    refine (h.congr (hdiff.mono fun k hk t ht ↦ ?_)).congr_right fun t ht ↦ ?_
    · simp [γ, (hasDerivAt_slice_right (hk t ht)).deriv]
    · simp [γ, (hasDerivAt_slice_right (hv t ht)).deriv]

end Action

end TauCeti.SymplecticForm
