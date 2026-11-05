/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.MeasureTheory.Integral.Lebesgue.Strip

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
  one-periodic Hamiltonian
  (`SymplecticForm.apply_zero_eq_apply_one_of_tendstoLocallyUniformlyOn_comp_add`);
* the limit is a stationary Floer cylinder: its perturbed derivative `dv - X_K(v)` vanishes on the
  open strip (`SymplecticForm.perturbedFDeriv_eq_zero_of_tendstoLocallyUniformlyOn_comp_add`).

The argument is the following. By finiteness of the energy, the energy over the translated
windows tends to zero (`TauCeti.tendsto_setLIntegral_of_eventually_subset`). By the coercivity of
the energy density under tameness
(`SymplecticForm.setLIntegral_norm_sq_add_norm_sq_perturbedFDeriv_le`), the `L²` norm, hence the
`L¹` norm, of the perturbed derivative over the windows tends to zero. Its `s`-component is
`∂_s u`, whose integral along a horizontal segment is the variation of `u` along it; its
`t`-component is `∂_t u - X_{H_t}(u)`, whose integral along a vertical segment is the defect of
`u` from the integral equation of the Hamiltonian flow. Both defects therefore vanish in the
limit, which converges uniformly on compact windows.

The convergence of the translates is an assumption here. In applications it is to come from
compactness away from bubbling points (`TauCeti.Geometry.Symplectic.Floer.Compactness`): the
energy over the translated windows tends to zero, so no bubbling point survives there. That
combination, which also needs a bound on the image of `u`, is not carried out here. Nor are the
nondegeneracy of the orbits, the convergence of the whole half-cylinder rather than a sequence of
translates, or the exponential decay along the end.

## Main results

* `SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add`: the limit of the translates is
  independent of `s`.
* `SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`: the limit is a
  Hamiltonian orbit.
* `SymplecticForm.perturbedFDeriv_eq_zero_of_tendstoLocallyUniformlyOn_comp_add`: the limit is a
  stationary Floer cylinder.

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

/-- The Hamiltonian vector field `X_{H_t}(x)` of a jointly `C¹` time-dependent Hamiltonian is
jointly continuous in `(t, x)`. -/
private theorem continuous_hamiltonianVectorField_uncurry (hH : ContDiff ℝ 1 (uncurry H)) :
    Continuous fun p : ℝ × V ↦ ω.hamiltonianVectorField (H p.1) p.2 := by
  have h := ω.continuousOn_uncurry_hamiltonianVectorField isOpen_univ hH.contDiffOn
  rw [univ_prod_univ] at h
  exact continuousOn_univ.1 h

/-- For `K = H_t dt` the `s`-component of the perturbed derivative is `∂_s u`. -/
private theorem perturbedFDeriv_cylindrical_apply_stdComplexLineReal (z : ℝ × ℝ) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineReal =
      fderiv ℝ u z (1, 0) := by
  rw [perturbedFDeriv_apply_stdComplexLineReal, stdComplexLineReal_eq,
    hamiltonianVectorField_const, Pi.zero_apply, sub_zero]

/-- For `K = H_t dt` the `t`-component of the perturbed derivative is `∂_t u - X_{H_t}(u)`. -/
private theorem perturbedFDeriv_cylindrical_apply_stdComplexLineImag (z : ℝ × ℝ) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun w ↦ H w.2) u z stdComplexLineImag =
      fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z) := by
  rw [perturbedFDeriv_apply_stdComplexLineImag, stdComplexLineImag_eq]

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
    ((continuous_hamiltonianVectorField_uncurry hH).comp_continuousOn
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
  have hderiv : ∀ r ∈ uIcc α β, HasDerivAt (fun r ↦ u (r, t)) (fderiv ℝ u (r, t) (1, 0)) r := by
    intro r hr
    have hd := HasFDerivAt.comp_hasDerivAt r ((hu.differentiableOn one_ne_zero _
      (hmem hr)).differentiableAt (hU.mem_nhds (hmem hr))).hasFDerivAt
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r t))
    simpa [Function.comp_def] using hd
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
  have hX := continuous_hamiltonianVectorField_uncurry (ω := ω) hH
  have hcont : ContinuousOn (fun z ↦ fderiv ℝ u z (0, 1)) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hcontX : ContinuousOn (fun z : ℝ × ℝ ↦ ω.hamiltonianVectorField (H z.2) (u z)) U :=
    hX.comp_continuousOn (continuousOn_snd.prodMk hu.continuousOn)
  simp_rw [perturbedFDeriv_cylindrical_apply_stdComplexLineImag]
  rw [Measure.volume_eq_prod, setLIntegral_prod
    (fun z ↦ ‖fderiv ℝ u z (0, 1) - ω.hamiltonianVectorField (H z.2) (u z)‖ₑ)
    (((hcont.sub hcontX).mono hR).enorm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc))]
  refine setLIntegral_mono' measurableSet_Icc fun r hr ↦ ?_
  have hsub : uIcc t₁ t₂ ⊆ Icc 0 1 := by
    rw [uIcc_of_le ht]
    exact Icc_subset_Icc ht₁ ht₂
  have hmem {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : (r, t) ∈ U := hR ⟨hr, hsub htm⟩
  -- The fundamental theorem of calculus along the segment `{r} × [t₁, t₂]`.
  have hderiv : ∀ t ∈ uIcc t₁ t₂, HasDerivAt (fun t ↦ u (r, t)) (fderiv ℝ u (r, t) (0, 1)) t := by
    intro t htm
    have hd := HasFDerivAt.comp_hasDerivAt t ((hu.differentiableOn one_ne_zero _
      (hmem htm)).differentiableAt (hU.mem_nhds (hmem htm))).hasFDerivAt
      ((hasDerivAt_const t r).prodMk (hasDerivAt_id t))
    simpa [Function.comp_def] using hd
  have hint : IntervalIntegrable (fun t ↦ fderiv ℝ u (r, t) (0, 1)) volume t₁ t₂ :=
    (hcont.comp (by fun_prop) fun t htm ↦ hmem htm).intervalIntegrable
  have hintX :
      IntervalIntegrable (fun t ↦ ω.hamiltonianVectorField (H t) (u (r, t))) volume t₁ t₂ :=
    (hcontX.comp (by fun_prop) fun t htm ↦ hmem htm).intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    ← intervalIntegral.integral_sub hint hintX, intervalIntegral.integral_of_le ht]
  refine (enorm_integral_le_lintegral_enorm _).trans
    ((lintegral_mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht₁ ht₂))).trans_eq ?_)
  rfl

end Segments

section Limit

variable {E : Set (ℝ × ℝ)} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ} {s : ℕ → ℝ}
  {v : ℝ × ℝ → V}

/-- A lower integral over `[0, 1]` vanishes if, for every `ε > 0`, its integrand is eventually
bounded by integrands `f k` up to `ε`, whose integrals are bounded by quantities tending to zero. -/
private theorem setLIntegral_Icc_eq_zero_of_forall_eventually {g : ℝ → ℝ≥0∞}
    {f : ℕ → ℝ → ℝ≥0∞} {F : ℕ → ℝ≥0∞} (hF : Tendsto F atTop (𝓝 0))
    (hfF : ∀ᶠ k in atTop, ∫⁻ x in Icc (0 : ℝ) 1, f k x ≤ F k)
    (h : ∀ ε : ℝ≥0, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ Icc (0 : ℝ) 1, g x ≤ f k x + ε) :
    ∫⁻ x in Icc (0 : ℝ) 1, g x = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) zero_le
  rw [zero_add]
  have hlim : Tendsto (fun k ↦ F k + ε) atTop (𝓝 (0 + ε)) := hF.add tendsto_const_nhds
  rw [zero_add] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [hfF, h ε hε] with k hk hgk
  calc ∫⁻ x in Icc (0 : ℝ) 1, g x ≤ ∫⁻ x in Icc (0 : ℝ) 1, (f k x + ε) :=
        setLIntegral_mono' measurableSet_Icc hgk
    _ = (∫⁻ x in Icc (0 : ℝ) 1, f k x) + ε := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Icc]
        simp
    _ ≤ F k + ε := add_le_add_left hk _

/-- The windows `[a + s_k, b + s_k] × [0, 1]` eventually lie in `E` and outside every band
`|s| < R`, when `s_k` tends to infinity and every translated window eventually lies in `E`. -/
private theorem eventually_window_subset (hs : Tendsto s atTop (cocompact ℝ))
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E) (a b R : ℝ) :
    ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E ∩ {z | R ≤ |z.1|} := by
  filter_upwards [hW a b,
    hs.eventually (isCompact_closedBall (0 : ℝ) (R + |a| + |b|)).compl_mem_cocompact]
    with k hk hsk z hz
  refine ⟨hk hz, ?_⟩
  have hsk' : R + |a| + |b| < |s k| := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hsk
  have h₁ : |z.1 - s k| ≤ |a| + |b| := by
    obtain ⟨⟨h₁, h₂⟩, -⟩ := hz
    refine abs_le.2 ⟨?_, ?_⟩ <;>
      linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have h₂ : |s k| ≤ |z.1| + |z.1 - s k| := by
    simpa using abs_sub z.1 (z.1 - s k)
  exact (by linarith : R ≤ |z.1|)

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
    (A := fun k ↦ Icc (a + s k) (b + s k) ×ˢ Icc 0 1) (eventually_window_subset hs hW a b)
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

omit [FiniteDimensional ℝ V] in
/-- A point of the rectangle `[α, β] × [0, 1]`, translated by `(r, 0)`, lies in the translated
window `[α + r, β + r] × [0, 1]`. -/
private theorem add_mem_window {α β r : ℝ} {z : ℝ × ℝ} (hz : z ∈ Icc α β ×ˢ Icc (0 : ℝ) 1) :
    z + (r, 0) ∈ Icc (α + r) (β + r) ×ˢ Icc (0 : ℝ) 1 := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hz
  exact ⟨⟨by simp [h₁], by simp [h₂]⟩, by simpa using h₃⟩

omit [FiniteDimensional ℝ V] in
/-- On a compact window `[α, β] × [0, 1]` the translates converge uniformly, they are eventually
continuous, and the limit is continuous. -/
private theorem tendstoUniformlyOn_window (hu : ContDiffOn ℝ 1 u U) (hEU : E ⊆ U)
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E)
    (hv : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) (α β : ℝ) :
    TendstoUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop (Icc α β ×ˢ Icc 0 1) ∧
      (∀ᶠ k in atTop, ContinuousOn (fun z ↦ u (z + (s k, 0))) (Icc α β ×ˢ Icc 0 1)) ∧
      ContinuousOn v (Icc α β ×ˢ Icc 0 1) := by
  have hUC : TendstoUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop (Icc α β ×ˢ Icc 0 1) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_Icc.prod isCompact_Icc)).1 (hv.mono (prod_mono (subset_univ _) le_rfl))
  have hcont : ∀ᶠ k in atTop, ContinuousOn (fun z ↦ u (z + (s k, 0))) (Icc α β ×ˢ Icc 0 1) := by
    filter_upwards [hW α β] with k hk
    exact hu.continuousOn.comp (continuousOn_id.add continuousOn_const)
      fun z hz ↦ hEU (hk (add_mem_window hz))
  exact ⟨hUC, hcont, hUC.continuousOn hcont.frequently⟩

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
    obtain ⟨hUC, -, hvK⟩ := tendstoUniformlyOn_window hu hEU hW hv α β
    have hsides {γ : ℝ} (hγ : γ ∈ Icc α β) : ContinuousOn (fun t ↦ v (γ, t)) (Icc 0 1) :=
      hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦ ⟨hγ, ht⟩
    have hβ : β ∈ Icc α β := ⟨hαβ, le_rfl⟩
    have hα : α ∈ Icc α β := ⟨le_rfl, hαβ⟩
    -- The mean distance between the two sides vanishes.
    have hzero : ∫⁻ t in Icc (0 : ℝ) 1, edist (v (β, t)) (v (α, t)) = 0 := by
      refine setLIntegral_Icc_eq_zero_of_forall_eventually
        (f := fun k t ↦ edist (u (β + s k, t)) (u (α + s k, t)))
        (tendsto_lintegral_enorm_perturbedFDeriv hEU hW (Or.inl rfl)
          (continuousOn_perturbedFDeriv_cylindrical_stdComplexLineReal hU hu)
          (tendsto_lintegral_norm_sq_perturbedFDeriv hc hJc hJM hfloer hfin hs hW α β)) ?_ ?_
      · filter_upwards [hW α β] with k hk
        exact lintegral_edist_le hU hu (by linarith) (hk.trans hEU)
      · intro ε hε
        filter_upwards [EMetric.tendstoUniformlyOn_iff.1 hUC (ε / 2)
          (ENNReal.half_pos (by exact_mod_cast hε.ne'))] with k hk t ht
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

/-- **The limit of translated Floer cylinders is a Hamiltonian orbit.** Under the hypotheses of
`TauCeti.SymplecticForm.eq_of_tendstoLocallyUniformlyOn_comp_add`, and for a jointly `C¹`
Hamiltonian `H`, the loop `x(t) = v(0, t)`,
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
  have hstat := eq_of_tendstoLocallyUniformlyOn_comp_add hU hu hEU hc hJc hJM hfloer hfin hs hW hv
  set x : ℝ → V := fun t ↦ v (0, t)
  set Φ : ℝ × V → V := fun p ↦ ω.hamiltonianVectorField (H p.1) p.2
  have hΦ : Continuous Φ := continuous_hamiltonianVectorField_uncurry hH
  obtain ⟨hUC, hFc, hvK⟩ := tendstoUniformlyOn_window hu hEU hW hv 0 1
  have hrow {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : ContinuousOn (fun t ↦ v (r, t)) (Icc 0 1) :=
    hvK.comp (continuousOn_const.prodMk continuousOn_id) fun t ht ↦ ⟨hr, ht⟩
  have hx : ContinuousOn x (Icc 0 1) := hrow ⟨le_rfl, zero_le_one⟩
  have hf : ContinuousOn (fun t ↦ Φ (t, x t)) (Icc 0 1) :=
    hΦ.comp_continuousOn (continuousOn_id.prodMk hx)
  -- The vector field along the translates converges uniformly on `[0, 1] × [0, 1]`, since
  -- `Φ` is uniformly continuous on a compact neighbourhood of the image of the limit.
  have hΦUC : TendstoUniformlyOn (fun k z ↦ Φ (z.2, u (z + (s k, 0)))) (fun z ↦ Φ (z.2, v z))
      atTop (Icc 0 1 ×ˢ Icc 0 1) := by
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hvK
    have hpair : TendstoUniformlyOn (fun k z ↦ (z.2, u (z + (s k, 0)))) (fun z ↦ (z.2, v z))
        atTop (Icc 0 1 ×ˢ Icc 0 1) := by
      rw [Metric.tendstoUniformlyOn_iff] at hUC ⊢
      intro ε hε
      filter_upwards [hUC ε hε] with k hk z hz
      simpa [Prod.dist_eq] using hk z hz
    have hC : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : V) (B + 1)) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    refine (hC.uniformContinuousOn_of_continuous hΦ.continuousOn).comp_tendstoUniformlyOn_eventually
      ?_ ?_ hpair
    · filter_upwards [Metric.tendstoUniformlyOn_iff.1 hUC 1 one_pos] with k hk z hz
      refine ⟨hz.2, ?_⟩
      have h₁ := hk z hz
      rw [dist_eq_norm] at h₁
      rw [mem_closedBall_zero_iff]
      linarith [hB z hz, norm_le_norm_add_norm_sub' (u (z + (s k, 0))) (v z),
        norm_sub_rev (v z) (u (z + (s k, 0)))]
    · intro z hz
      exact ⟨hz.2, by rw [mem_closedBall_zero_iff]; linarith [hB z hz]⟩
  -- The integral equation of the Hamiltonian flow holds along `x`.
  have hint {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t₂) (ht₂ : t₂ ≤ 1) :
      x t₂ - x t₁ - ∫ t in t₁..t₂, Φ (t, x t) = 0 := by
    set A := x t₂ - x t₁ - ∫ t in t₁..t₂, Φ (t, x t) with hA
    have hsub : uIcc t₁ t₂ ⊆ Icc 0 1 := by
      rw [uIcc_of_le ht]
      exact Icc_subset_Icc ht₁ ht₂
    have hzero : ∫⁻ r in Icc (0 : ℝ) 1, ‖A‖ₑ = 0 := by
      refine setLIntegral_Icc_eq_zero_of_forall_eventually
        (f := fun k r ↦ ‖u (r + s k, t₂) - u (r + s k, t₁) -
          ∫ t in t₁..t₂, Φ (t, u (r + s k, t))‖ₑ)
        (tendsto_lintegral_enorm_perturbedFDeriv hEU hW (Or.inr rfl)
          (continuousOn_perturbedFDeriv_cylindrical_stdComplexLineImag hH hU hu)
          (tendsto_lintegral_norm_sq_perturbedFDeriv hc hJc hJM hfloer hfin hs hW 0 1)) ?_ ?_
      · filter_upwards [hW 0 1] with k hk
        refine le_of_eq_of_le ?_ (lintegral_enorm_sub_sub_integral_le hH hU hu ht₁ ht ht₂
          (hk.trans hEU))
        -- Translate the segments `{r} × [t₁, t₂]` back to `r ∈ [0, 1]`.
        have hT := (measurePreserving_add_right volume (s k)).setLIntegral_comp_preimage_emb
          (measurableEmbedding_addRight _)
          (fun r ↦ ‖u (r, t₂) - u (r, t₁) - ∫ t in t₁..t₂, Φ (t, u (r, t))‖ₑ)
          (Icc (0 + s k) (1 + s k))
        rwa [preimage_add_const_Icc, add_sub_cancel_right, add_sub_cancel_right] at hT
      · intro ε hε
        set δ : ℝ := ε / 3 with hδε
        have hδ : 0 < δ := by positivity
        filter_upwards [Metric.tendstoUniformlyOn_iff.1 hUC δ hδ,
          Metric.tendstoUniformlyOn_iff.1 hΦUC δ hδ, hFc] with k hk hkΦ hkc r hr
        have hmem {t : ℝ} (htm : t ∈ uIcc t₁ t₂) : (r, t) ∈ Icc (0 : ℝ) 1 ×ˢ Icc 0 1 :=
          ⟨hr, hsub htm⟩
        have hF (t : ℝ) : u ((r, t) + (s k, 0)) = u (r + s k, t) := by simp
        -- Along the segment the limit is `x`, and the translates are uniformly close to it.
        have hxv : ∫ t in t₁..t₂, Φ (t, x t) = ∫ t in t₁..t₂, Φ (t, v (r, t)) :=
          intervalIntegral.integral_congr fun t htm ↦ by
            simp only [x, hstat r t (hsub htm)]
        have hcv : ContinuousOn (fun t ↦ Φ (t, v (r, t))) (uIcc t₁ t₂) :=
          hΦ.comp_continuousOn (continuousOn_id.prodMk ((hrow hr).mono hsub))
        have hcu : ContinuousOn (fun t ↦ Φ (t, u (r + s k, t))) (uIcc t₁ t₂) := by
          refine hΦ.comp_continuousOn (continuousOn_id.prodMk ?_)
          simp_rw [← hF]
          exact hkc.comp (continuousOn_const.prodMk continuousOn_id) fun t htm ↦ hmem htm
        have hI : ‖∫ t in t₁..t₂, (Φ (t, v (r, t)) - Φ (t, u (r + s k, t)))‖ ≤ δ := by
          refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := δ)
            fun t htm ↦ ?_).trans ?_
          · have h := hkΦ (r, t) (hmem (uIoc_subset_uIcc htm))
            rw [dist_eq_norm, hF] at h
            exact h.le
          · rw [abs_of_nonneg (sub_nonneg.2 ht)]
            nlinarith
        have h₁ : ‖x t₁ - u (r + s k, t₁)‖ < δ := by
          have h := hk (r, t₁) (hmem left_mem_uIcc)
          rwa [dist_eq_norm, hF, hstat r t₁ (hsub left_mem_uIcc)] at h
        have h₂ : ‖x t₂ - u (r + s k, t₂)‖ < δ := by
          have h := hk (r, t₂) (hmem right_mem_uIcc)
          rwa [dist_eq_norm, hF, hstat r t₂ (hsub right_mem_uIcc)] at h
        have hsplit : A - (u (r + s k, t₂) - u (r + s k, t₁) - ∫ t in t₁..t₂, Φ (t, u (r + s k, t)))
            = (x t₂ - u (r + s k, t₂)) - (x t₁ - u (r + s k, t₁)) -
              ∫ t in t₁..t₂, (Φ (t, v (r, t)) - Φ (t, u (r + s k, t))) := by
          rw [intervalIntegral.integral_sub hcv.intervalIntegrable hcu.intervalIntegrable, ← hxv,
            hA]
          abel
        have hA : ‖A‖ ≤ ‖u (r + s k, t₂) - u (r + s k, t₁) -
            ∫ t in t₁..t₂, Φ (t, u (r + s k, t))‖ + ε := by
          have := norm_le_norm_add_norm_sub' A
            (u (r + s k, t₂) - u (r + s k, t₁) - ∫ t in t₁..t₂, Φ (t, u (r + s k, t)))
          rw [hsplit] at this
          linarith [norm_sub_le ((x t₂ - u (r + s k, t₂)) - (x t₁ - u (r + s k, t₁)))
            (∫ t in t₁..t₂, (Φ (t, v (r, t)) - Φ (t, u (r + s k, t)))),
            norm_sub_le (x t₂ - u (r + s k, t₂)) (x t₁ - u (r + s k, t₁)), hI]
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal hA
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at hzero
    exact enorm_eq_zero.1 hzero
  -- Hence `x` is a primitive of the vector field along it.
  intro t ht
  have : Fact (t ∈ Icc (0 : ℝ) 1) := ⟨ht⟩
  have hsub : uIcc 0 t ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (s := Icc 0 1)
    (t := Icc 0 1) (hf.mono hsub).intervalIntegrable
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)
  refine (hd.const_add (x 0)).congr_of_mem (fun τ hτ ↦ ?_) ht
  have h := hint le_rfl hτ.1 hτ.2
  rw [← sub_eq_zero, ← h]
  abel

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The limit of translated Floer cylinders closes up.** If moreover `u(s, 0) = u(s, 1)` on `E`,
then the limit of the translates satisfies `v(s, 0) = v(s, 1)`. Together with
`TauCeti.SymplecticForm.hasDerivWithinAt_of_tendstoLocallyUniformlyOn_comp_add`, for a
one-periodic Hamiltonian the limit is the stationary cylinder over a one-periodic orbit. -/
theorem apply_zero_eq_apply_one_of_tendstoLocallyUniformlyOn_comp_add
    (hW : ∀ a b : ℝ, ∀ᶠ k in atTop, Icc (a + s k) (b + s k) ×ˢ Icc 0 1 ⊆ E)
    (hper : ∀ r, (r, (0 : ℝ)) ∈ E → u (r, 0) = u (r, 1))
    (hv : TendstoLocallyUniformlyOn (fun k z ↦ u (z + (s k, 0))) v atTop
      ((univ : Set ℝ) ×ˢ Icc 0 1)) (r : ℝ) :
    v (r, 0) = v (r, 1) := by
  have h₀ := hv.tendsto_at (show (r, (0 : ℝ)) ∈ (univ : Set ℝ) ×ˢ Icc 0 1 from
    ⟨mem_univ r, left_mem_Icc.2 zero_le_one⟩)
  have h₁ := hv.tendsto_at (show (r, (1 : ℝ)) ∈ (univ : Set ℝ) ×ˢ Icc 0 1 from
    ⟨mem_univ r, right_mem_Icc.2 zero_le_one⟩)
  refine tendsto_nhds_unique (h₀.congr' ?_) h₁
  filter_upwards [hW r r] with k hk
  have hmem : (r + s k, (0 : ℝ)) ∈ E := hk ⟨⟨le_rfl, le_rfl⟩, left_mem_Icc.2 zero_le_one⟩
  simpa using hper _ hmem

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
  have hd := (hder.hasDerivAt (Icc_mem_nhds hz.2.1 hz.2.2)).hasFDerivAt.comp z hasFDerivAt_snd
  rw [ω.perturbedFDeriv_congr_of_eventuallyEq _ _ hev]
  refine ContinuousLinearMap.ext fun w ↦ ?_
  rw [perturbedFDeriv_apply,
    show (fun w : ℝ × ℝ ↦ v (0, w.2)) = (fun t ↦ v (0, t)) ∘ Prod.snd from rfl, hd.fderiv]
  simp [hamiltonianVectorField_const]

end Limit

end TauCeti.SymplecticForm
