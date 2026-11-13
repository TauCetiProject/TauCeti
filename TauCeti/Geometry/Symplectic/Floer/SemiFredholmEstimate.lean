/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The semi-Fredholm estimate of the linearized Floer operator

Let `(V, ω)` be a symplectic vector space, `H_t` a time-dependent Hamiltonian, `J_t(y)` a family
of almost complex structures and `u` a map of the cylinder whose loops converge, as `s → ±∞`, to
nondegenerate orbits `x_±` of `H`, while the slice defect `∂t u - X_{H_t}(u)` tends
uniformly to zero, as for a Floer cylinder from `x₋` to `x₊`; suppose that `J_t` is
`ω`-compatible along `x_±` and along `u`. The linearized Floer operator along `u` is

`D_u ξ = ∂s ξ + J_t(u) (∂t ξ - dX_{H_t}(u) ξ) + (dJ_t(u) ξ) (∂t u - X_{H_t}(u))`

(`TauCeti.SymplecticForm.floerLinearization` for the datum `K = H_t dt`). This file proves the
estimate behind its Fredholm property: there are constants `C` and `T` such that every `C²` map
`ξ` of period one in `t` and compact support in `s` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over the cylinder
(`SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_setIntegral`).
The last term is an integral over a fixed compact piece of the cylinder; since the inclusion of
`W^{1,2}` into `L²` on such a piece is compact, an estimate of this form shows that the extension
of `D_u` to the Sobolev completion has finite-dimensional kernel and closed range.

The estimate is a patching argument that holds for every operator `D = ∂s + J(z) ∂t + S(z)` with
`J(z)` `ω`-compatible and `J`, `S` continuous on the cylinder, once `D` satisfies `L²` estimates
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C ∫ ‖D ξ‖²` far out on both ends
(`SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_add_setIntegral_of_ends`). The
linearized Floer operator has this form (`TauCeti.SymplecticForm.floerLinearization_eq_add`).

* **The interior estimate.** On the core `[-T, T] × [0, 1]`, maps of period one in `t` that
  vanish on the two slices satisfy `∫ (‖∂s ξ‖² + ‖∂t ξ‖²) ≤ C ∫ (‖D ξ‖² + ‖ξ‖²)`
  (`TauCeti.SymplecticForm.exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic`).
* **The ends.** For `D_u`, the estimate on the two ends, in the norm of `V`, is
  `SymplecticForm.exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization`; it
  controls `ξ` beyond some `R` and below `-R` by `D_u ξ` alone.
* **Patching.** Cutoffs `βm`, `β₀`, `βp` with `βm + β₀ + βp = 1`, equal to one on `(-∞, -T]`,
  on `[-R, R]` and on `[T, ∞)` respectively, where `T = R + 1` and `β₀` vanishes outside
  `(-T, T)` (`TauCeti.exists_contDiff_partitionOfUnity_three`), split `ξ` into three pieces,
  one for each estimate. By the Leibniz rule `D (β ξ) = β D ξ + β' ξ`, the cutoffs only add
  terms `β' ξ`, which are supported in `[-T, T]`.

These are estimates on smooth maps; the Sobolev completion and the Fredholm property itself are
not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the linearized operator `∂s + J ∂t + S(s, t)` along a
  Floer trajectory and its Fredholm property.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendix B (the energy identity of the
  Cauchy–Riemann operator).
* M. Schwarz, *Morse homology*, Progress in Mathematics 111, Birkhäuser, 1993, Section 2.2 (the
  semi-Fredholm estimate from estimates on the ends and a compact core).
-/

public section

open Filter Set MeasureTheory Topology ContinuousLinearMap
open scoped Manifold NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Patching

variable {ω : SymplecticForm V} {J : ℝ × ℝ → AlmostComplexStructure V} {S : ℝ × ℝ → V →L[ℝ] V}

omit [FiniteDimensional ℝ V] in
/-- The density `‖∂s η‖² + ‖∂t η‖² + ‖η‖²` of a `C¹` map `η` of the cylinder is continuous. -/
private theorem continuous_norm_fderiv_sq_add {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η) :
    Continuous fun z ↦ ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2 := by
  have hd := hη.continuous_fderiv one_ne_zero
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add (hη.continuous.norm.pow 2)

/-- The operator `∂s + J ∂t + S` applied to a `C¹` map is continuous on a set where `J` and `S`
are. -/
private theorem continuousOn_fderiv_add {K : Set (ℝ × ℝ)}
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) K)
    (hS : ContinuousOn S K) {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η) :
    ContinuousOn (fun z ↦ fderiv ℝ η z stdComplexLineReal +
      J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)) K := by
  have hd := hη.continuous_fderiv one_ne_zero
  exact ((hd.clm_apply continuous_const).continuousOn.add
    (hJc.clm_apply (hd.clm_apply continuous_const).continuousOn)).add
    (hS.clm_apply hη.continuous.continuousOn)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A map vanishing for `s ∉ (c, d)` vanishes near every point with `s < c` or `s > d`. -/
private theorem eventuallyEq_zero_of_forall_notMem_Ioo {η : ℝ × ℝ → V} {c d : ℝ}
    (hη : ∀ w : ℝ × ℝ, w.1 ∉ Ioo c d → η w = 0) {z : ℝ × ℝ} (hz : z.1 < c ∨ d < z.1) :
    η =ᶠ[𝓝 z] 0 := by
  rcases hz with hz | hz
  · exact eventually_of_mem ((isOpen_lt continuous_fst continuous_const).mem_nhds hz)
      fun w hw ↦ hη w fun hw' ↦ lt_irrefl _ (hw.trans hw'.1)
  · exact eventually_of_mem ((isOpen_lt continuous_const continuous_fst).mem_nhds hz)
      fun w hw ↦ hη w fun hw' ↦ lt_irrefl _ (hw.trans hw'.2)

omit [FiniteDimensional ℝ V] in
/-- For a map `η` vanishing for `s ∉ (c, d)`, the integrals of `‖∂s η‖² + ‖∂t η‖² + ‖η‖²` and of
`‖∂s η + J ∂t η + S η‖²` over a window `[c', d'] × [0, 1]` containing `[c, d] × [0, 1]` are the
integrals over `[c, d] × [0, 1]`. -/
private theorem setIntegral_Icc_prod_eq_of_forall_notMem_Ioo
    (J : ℝ × ℝ → AlmostComplexStructure V) (S : ℝ × ℝ → V →L[ℝ] V) {η : ℝ × ℝ → V}
    {c d c' d' : ℝ} (hη : ∀ w : ℝ × ℝ, w.1 ∉ Ioo c d → η w = 0) (hc : c' ≤ c) (hd : d ≤ d') :
    (∫ z in Icc c' d' ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2)) =
      (∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2)) ∧
    (∫ z in Icc c' d' ×ˢ Icc 0 1, ‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2) =
      ∫ z in Icc c d ×ˢ Icc 0 1, ‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2 := by
  refine ⟨setIntegral_Icc_prod_eq_of_forall_eq_zero measurableSet_Icc hc hd fun z hz ↦ ?_,
    setIntegral_Icc_prod_eq_of_forall_eq_zero measurableSet_Icc hc hd fun z hz ↦ ?_⟩ <;>
  · have h := eventuallyEq_zero_of_forall_notMem_Ioo hη hz
    rw [h.fderiv_eq, h.eq_of_nhds]
    simp

omit [FiniteDimensional ℝ V] in
/-- An estimate over `[c, d] × [0, 1]` of a map `η` vanishing for `s ∉ (c, d)` holds over every
window `[c', d'] × [0, 1]` containing it. -/
private theorem setIntegral_le_of_forall_notMem_Ioo
    (J : ℝ × ℝ → AlmostComplexStructure V) (S : ℝ × ℝ → V →L[ℝ] V) {η : ℝ × ℝ → V}
    {c d c' d' K E : ℝ} (hη : ∀ w : ℝ × ℝ, w.1 ∉ Ioo c d → η w = 0) (hc : c' ≤ c) (hd : d ≤ d')
    (h : ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      K * (∫ z in Icc c d ×ˢ Icc 0 1, ‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2) + E) :
    ∫ z in Icc c' d' ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      K * (∫ z in Icc c' d' ×ˢ Icc 0 1, ‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2) + E := by
  obtain ⟨e₁, e₂⟩ := setIntegral_Icc_prod_eq_of_forall_notMem_Ioo J S hη hc hd
  rwa [e₁, e₂]

omit [FiniteDimensional ℝ V] in
/-- **The Leibniz rule for a cutoff in `s`.** Multiplying `ξ` by a function `β(s)` multiplies
`∂s ξ + J ∂t ξ + S ξ` by `β` and adds `β'(s) ξ`. -/
private theorem fderiv_smul_fst_add {ξ : ℝ × ℝ → V} {β : ℝ → ℝ} {z : ℝ × ℝ}
    (hβ : DifferentiableAt ℝ β z.1) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal +
        J z (fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag) + S z (β z.1 • ξ z) =
      β z.1 • (fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
        S z (ξ z)) + deriv β z.1 • ξ z := by
  have hc : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1)
      (deriv β z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
    hβ.hasDerivAt.comp_hasFDerivAt z (hasFDerivAt_fst (p := z))
  have hd : HasFDerivAt (fun w ↦ β w.1 • ξ w) _ z := hc.smul hξ.hasFDerivAt
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', stdComplexLineReal_fst, stdComplexLineImag_fst, smul_eq_mul,
    mul_zero, mul_one, zero_smul, add_zero, map_smul]
  module

/-- **The `L²` cost of a cutoff.** If `|β| ≤ 1`, `|β'| ≤ L` and `β'` vanishes outside `[c, d]`,
then for `η = β(s) ξ` and `D = ∂s + J ∂t + S`, over a window `[A, B] × [0, 1]` containing
`[c, d] × [0, 1]`, `∫ ‖D η‖² ≤ 2 ∫ ‖D ξ‖² + 2 L² ∫_{[c, d] × [0, 1]} ‖ξ‖²`. -/
private theorem setIntegral_norm_fderiv_add_sq_le_of_eq_smul
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (univ ×ˢ Icc 0 1))
    (hS : ContinuousOn S (univ ×ˢ Icc 0 1)) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ)
    {β : ℝ → ℝ} {L c d A B : ℝ} (hβ : ContDiff ℝ 1 β) (hβ1 : ∀ s, |β s| ≤ 1)
    (hβL : ∀ s, |deriv β s| ≤ L) (hβcd : ∀ s ∉ Icc c d, deriv β s = 0) {η : ℝ × ℝ → V}
    (hη : ∀ w, η w = β w.1 • ξ w) (hA : A ≤ c) (hB : d ≤ B) :
    ∫ z in Icc A B ×ˢ Icc 0 1, ‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2 ≤
      2 * (∫ z in Icc A B ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
        J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2) +
        2 * L ^ 2 * ∫ z in Icc c d ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
  obtain rfl : η = _ := funext hη
  beta_reduce
  have hint {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f (univ ×ˢ Icc 0 1)) {c d : ℝ} :
      IntegrableOn f (Icc c d ×ˢ Icc 0 1) :=
    (hf.mono (prod_mono (subset_univ _) subset_rfl)).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hc₁ : Continuous fun z : ℝ × ℝ ↦ deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 :=
    (((hβ.continuous_deriv le_rfl).comp continuous_fst).pow 2).mul (hξ.continuous.norm.pow 2)
  -- The error term `β'² ‖ξ‖²` is supported in `[c, d] × [0, 1]` and bounded by `L² ‖ξ‖²`.
  have hE : 2 * ∫ z in Icc A B ×ˢ Icc 0 1, deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2 ≤
      2 * L ^ 2 * ∫ z in Icc c d ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
    rw [setIntegral_Icc_prod_eq_of_forall_eq_zero measurableSet_Icc hA hB fun z hz ↦ by
      rw [hβcd z.1 fun h ↦ by rcases hz with hz | hz <;> linarith [h.1, h.2]]
      simp, mul_assoc 2 (L ^ 2)]
    gcongr
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hint hc₁.continuousOn) (hint (continuous_const.mul
      (hξ.continuous.norm.pow 2)).continuousOn) (measurableSet_Icc.prod measurableSet_Icc)
      fun z _ ↦ mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hβL z.1) 2
  refine le_trans ?_ (add_le_add le_rfl hE)
  have i₁ : IntegrableOn (fun z ↦ 2 * ‖fderiv ℝ ξ z stdComplexLineReal +
      J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2) (Icc A B ×ˢ Icc 0 1) :=
    hint (continuousOn_const.mul ((continuousOn_fderiv_add hJc hS hξ).norm.pow 2))
  have i₂ : IntegrableOn (fun z : ℝ × ℝ ↦ 2 * (deriv β z.1 ^ 2 * ‖ξ z‖ ^ 2))
      (Icc A B ×ˢ Icc 0 1) :=
    hint (continuous_const.mul hc₁).continuousOn
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i₁ i₂]
  -- Pointwise, `‖D (β ξ)‖² ≤ 2 ‖D ξ‖² + 2 β'² ‖ξ‖²` by the Leibniz rule.
  refine setIntegral_mono_on (hint ((continuousOn_fderiv_add hJc hS
    ((hβ.comp contDiff_fst).smul hξ)).norm.pow 2)) (i₁.add i₂)
    (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
  rw [fderiv_smul_fst_add (hβ.differentiable one_ne_zero _) (hξ.differentiable one_ne_zero _)]
  generalize fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
    S z (ξ z) = X
  have h₁ : ‖β z.1 • X + deriv β z.1 • ξ z‖ ≤ ‖X‖ + |deriv β z.1| * ‖ξ z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) (hβ1 _)
  refine (pow_le_pow_left₀ (norm_nonneg _) h₁ 2).trans (add_sq_le.trans_eq ?_)
  rw [mul_pow, sq_abs]
  ring

omit [FiniteDimensional ℝ V] in
/-- Multiplying `ξ` by a function `β(s)` with `|β| ≤ 1` does not increase `∫ ‖ξ‖²`. -/
private theorem setIntegral_norm_sq_le_of_eq_smul {ξ : ℝ × ℝ → V} (hξ : Continuous ξ)
    {β : ℝ → ℝ} (hβ : Continuous β) (hβ1 : ∀ s, |β s| ≤ 1) {η : ℝ × ℝ → V}
    (hη : ∀ w, η w = β w.1 • ξ w) (c d : ℝ) :
    ∫ z in Icc c d ×ˢ Icc 0 1, ‖η z‖ ^ 2 ≤ ∫ z in Icc c d ×ˢ Icc 0 1, ‖ξ z‖ ^ 2 := by
  obtain rfl : η = _ := funext hη
  refine setIntegral_mono_on ((((hβ.comp continuous_fst).smul hξ).norm.pow 2).continuousOn
    |>.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    ((hξ.norm.pow 2).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
  rw [norm_smul, mul_pow, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (sq_nonneg _)
    (by simpa [sq_abs] using pow_le_one₀ (abs_nonneg _) (hβ1 z.1) (n := 2))

/-- **Adding the zeroth-order term to the interior estimate.** If
`∫ (‖∂s η‖² + ‖∂t η‖²) ≤ C₀ ∫ (‖D η‖² + ‖η‖²)` over `[c, d] × [0, 1]` for `D = ∂s + J ∂t + S`, and
`∫ ‖η‖² ≤ I` there, then `∫ (‖∂s η‖² + ‖∂t η‖² + ‖η‖²) ≤ C₀ ∫ ‖D η‖² + (C₀ + 1) I`. -/
private theorem setIntegral_norm_fderiv_sq_add_le_of_le
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (univ ×ˢ Icc 0 1))
    (hS : ContinuousOn S (univ ×ˢ Icc 0 1)) {η : ℝ × ℝ → V} (hη : ContDiff ℝ 1 η)
    {c d C₀ I : ℝ} (hC₀ : 0 ≤ C₀)
    (h : ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) ≤
      C₀ * ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2 + ‖η z‖ ^ 2))
    (hI : ∫ z in Icc c d ×ˢ Icc 0 1, ‖η z‖ ^ 2 ≤ I) :
    ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      C₀ * (∫ z in Icc c d ×ˢ Icc 0 1, ‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2) + (C₀ + 1) * I := by
  have hK : IsCompact (Icc c d ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hd := hη.continuous_fderiv one_ne_zero
  have i₁ : IntegrableOn (fun z ↦ ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2) (Icc c d ×ˢ Icc 0 1) :=
    (((hd.clm_apply continuous_const).norm.pow 2).add
      ((hd.clm_apply continuous_const).norm.pow 2)).continuousOn.integrableOn_compact hK
  have i₂ : IntegrableOn (fun z ↦ ‖η z‖ ^ 2) (Icc c d ×ˢ Icc 0 1) :=
    (hη.continuous.norm.pow 2).continuousOn.integrableOn_compact hK
  have i₃ : IntegrableOn (fun z ↦ ‖fderiv ℝ η z stdComplexLineReal +
      J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2) (Icc c d ×ˢ Icc 0 1) :=
    (((continuousOn_fderiv_add hJc hS hη).norm.pow 2).mono
      (prod_mono (subset_univ _) subset_rfl)).integrableOn_compact hK
  rw [integral_add i₁ i₂]
  rw [integral_add i₃ i₂] at h
  nlinarith [mul_le_mul_of_nonneg_left hI hC₀]

omit [FiniteDimensional ℝ V] in
/-- **Subadditivity of the `W^{1,2}` density.** For `C¹` maps `ηᵢ` and `ξ = η₁ + η₂ + η₃`, the
integral of `‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` over `[c, d] × [0, 1]` is at most three times the sum of
the same integrals for the `ηᵢ`. -/
private theorem setIntegral_norm_fderiv_sq_add_le_three_mul {ξ η₁ η₂ η₃ : ℝ × ℝ → V}
    (h₁ : ContDiff ℝ 1 η₁) (h₂ : ContDiff ℝ 1 η₂) (h₃ : ContDiff ℝ 1 η₃)
    (hξ : ∀ w, ξ w = η₁ w + η₂ w + η₃ w) (c d : ℝ) :
    ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      3 * ((∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η₁ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ η₁ z stdComplexLineImag‖ ^ 2 + ‖η₁ z‖ ^ 2)) +
        (∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η₂ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ η₂ z stdComplexLineImag‖ ^ 2 + ‖η₂ z‖ ^ 2)) +
        ∫ z in Icc c d ×ˢ Icc 0 1, (‖fderiv ℝ η₃ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ η₃ z stdComplexLineImag‖ ^ 2 + ‖η₃ z‖ ^ 2)) := by
  obtain rfl : ξ = _ := funext hξ
  have hK : IsCompact (Icc c d ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have i₁ := (continuous_norm_fderiv_sq_add h₁).continuousOn.integrableOn_compact (μ := volume) hK
  have i₂ := (continuous_norm_fderiv_sq_add h₂).continuousOn.integrableOn_compact (μ := volume) hK
  have i₃ := (continuous_norm_fderiv_sq_add h₃).continuousOn.integrableOn_compact (μ := volume) hK
  have i₁₂ := Integrable.fun_add i₁ i₂
  rw [← integral_add i₁ i₂, ← integral_add i₁₂ i₃, ← integral_const_mul]
  refine setIntegral_mono_on ((continuous_norm_fderiv_sq_add ((h₁.add h₂).add h₃)).continuousOn
    |>.integrableOn_compact hK) ((i₁₂.fun_add i₃).const_mul 3)
    (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
  have hd : fderiv ℝ (fun w ↦ η₁ w + η₂ w + η₃ w) z =
      fderiv ℝ η₁ z + fderiv ℝ η₂ z + fderiv ℝ η₃ z :=
    (((h₁.differentiable one_ne_zero z).hasFDerivAt.add
      (h₂.differentiable one_ne_zero z).hasFDerivAt).add
      (h₃.differentiable one_ne_zero z).hasFDerivAt).fderiv
  simp only [hd, add_apply]
  linarith [norm_add₃_sq_le (fderiv ℝ η₁ z stdComplexLineReal)
    (fderiv ℝ η₂ z stdComplexLineReal) (fderiv ℝ η₃ z stdComplexLineReal),
    norm_add₃_sq_le (fderiv ℝ η₁ z stdComplexLineImag)
    (fderiv ℝ η₂ z stdComplexLineImag) (fderiv ℝ η₃ z stdComplexLineImag),
    norm_add₃_sq_le (η₁ z) (η₂ z) (η₃ z)]

omit [FiniteDimensional ℝ V] in
/-- **An end estimate on a piece.** Let `D = ∂s + J ∂t + S` satisfy an `L²` estimate with
constant `C` on the maps of period one in `t` vanishing on two slices `s = c`, `s = d` with
`[c, d] ⊆ U`. Then a piece `η = β(s) ξ` of a `C²` map `ξ` of period one in `t`, with `β` of class
`C²` and `η` vanishing for `s ∉ (c, d)`, satisfies the estimate over every window
`[c', d'] × [0, 1]` containing `[c, d] × [0, 1]`. -/
private theorem setIntegral_le_of_eq_smul_of_forall_notMem_Ioo
    (J : ℝ × ℝ → AlmostComplexStructure V) (S : ℝ × ℝ → V →L[ℝ] V) {U : Set ℝ} {C : ℝ}
    (hU : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ U → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {η : ℝ × ℝ → V} (hη : ∀ w, η w = β w.1 • ξ w)
    {c d c' d' : ℝ} (hcd : c ≤ d) (hcdU : Icc c d ⊆ U)
    (hηcd : ∀ w : ℝ × ℝ, w.1 ∉ Ioo c d → η w = 0) (hc : c' ≤ c) (hd : d ≤ d') :
    ∫ z in Icc c' d' ×ˢ Icc 0 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      C * ∫ z in Icc c' d' ×ˢ Icc 0 1, ‖fderiv ℝ η z stdComplexLineReal +
        J z (fderiv ℝ η z stdComplexLineImag) + S z (η z)‖ ^ 2 := by
  obtain ⟨e₁, e₂⟩ := setIntegral_Icc_prod_eq_of_forall_notMem_Ioo J S hηcd hc hd
  rw [e₁, e₂]
  refine hU (by rw [funext hη]; exact (hβ.comp contDiff_fst).smul hξ)
    (fun s t ↦ by rw [hη, hη, hper]) hcd hcdU (fun t ↦ hηcd _ ?_) fun t ↦ hηcd _ ?_ <;> simp

/-- The arithmetic of the patching: the three pieces' estimates, their cutoff errors and the
factor `3` of the splitting combine to the semi-Fredholm estimate. -/
private theorem le_mul_add_of_le_three_mul {Cm C₀ Cp L Q Qm Q₀ Qp Dm D₀ Dp D I : ℝ}
    (hCm : 0 ≤ Cm) (hC₀ : 0 ≤ C₀) (hCp : 0 ≤ Cp) (hD : 0 ≤ D) (hI : 0 ≤ I)
    (h₃ : Q ≤ 3 * (Qm + Q₀ + Qp)) (hm : Qm ≤ Cm * Dm) (h₀ : Q₀ ≤ C₀ * D₀ + (C₀ + 1) * I)
    (hp : Qp ≤ Cp * Dp) (km : Dm ≤ 2 * D + 2 * L ^ 2 * I) (k₀ : D₀ ≤ 2 * D + 2 * L ^ 2 * I)
    (kp : Dp ≤ 2 * D + 2 * L ^ 2 * I) :
    Q ≤ (6 * (Cm + C₀ + Cp) + 6 * (Cm + C₀ + Cp) * L ^ 2 + 3 * C₀ + 3) * (D + I) := by
  have hS : 0 ≤ Cm + C₀ + Cp := by positivity
  nlinarith [mul_le_mul_of_nonneg_left km hCm, mul_le_mul_of_nonneg_left k₀ hC₀,
    mul_le_mul_of_nonneg_left kp hCp, mul_nonneg (mul_nonneg hS (sq_nonneg L)) hD,
    mul_nonneg hC₀ hD, mul_nonneg hS hI]

/-- **Patching the three estimates.** Let `βm + β₀ + βp = 1` be a partition of unity of the line
as in `TauCeti.exists_contDiff_partitionOfUnity_three` for `R ≥ 0`, and let
`D = ∂s + J ∂t + S` satisfy the `L²` estimates on the ends `s ≤ -R` and `s ≥ R` and the interior
estimate on the core `[-(R + 1), R + 1] × [0, 1]`. Then a `C²` map `ξ` of period one in `t`
vanishing for `s ∉ (a, b)`, where `[a, b]` contains `[-(R + 1), R + 1]`, satisfies the
semi-Fredholm estimate: the pieces `βm ξ`, `β₀ ξ`, `βp ξ` satisfy the three estimates, and the
cutoffs only add the terms `β' ξ`, supported in the core. -/
private theorem setIntegral_le_of_partition
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (univ ×ˢ Icc 0 1))
    (hS : ContinuousOn S (univ ×ˢ Icc 0 1)) {R L Cm C₀ Cp : ℝ} (hR : 0 ≤ R) (hCm : 0 ≤ Cm)
    (hC₀ : 0 ≤ C₀) (hCp : 0 ≤ Cp) {Um Up : Set ℝ} (hUm : ∀ s ≤ -R, s ∈ Um)
    (hUp : ∀ s, R ≤ s → s ∈ Up)
    (hm : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ Um → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cm * ∫ z in Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2)
    (h₀ : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s ∈ Icc (-(R + 1)) (R + 1), ξ (s, 1) = ξ (s, 0)) →
      (∀ t, ξ (-(R + 1), t) = 0) → (∀ t, ξ (R + 1, t) = 0) →
      ∫ z in Icc (-(R + 1)) (R + 1) ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2) ≤
        C₀ * ∫ z in Icc (-(R + 1)) (R + 1) ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2 + ‖ξ z‖ ^ 2))
    (hp : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ Up → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cp * ∫ z in Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2)
    {βm β₀ βp : ℝ → ℝ} (hβc : ContDiff ℝ 2 βm ∧ ContDiff ℝ 2 β₀ ∧ ContDiff ℝ 2 βp)
    (hsum : ∀ s, βm s + β₀ s + βp s = 1) (hβ1 : ∀ s, |βm s| ≤ 1 ∧ |β₀ s| ≤ 1 ∧ |βp s| ≤ 1)
    (hβL : ∀ s, |deriv βm s| ≤ L ∧ |deriv β₀ s| ≤ L ∧ |deriv βp s| ≤ L)
    (hβT : ∀ s ∉ Icc (-(R + 1)) (R + 1), deriv βm s = 0 ∧ deriv β₀ s = 0 ∧ deriv βp s = 0)
    (hβm0 : ∀ s, -R ≤ s → βm s = 0) (hβ₀0 : ∀ s ∉ Ioo (-(R + 1)) (R + 1), β₀ s = 0)
    (hβp0 : ∀ s ≤ R, βp s = 0) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ} (ha : a ≤ -(R + 1)) (hb : R + 1 ≤ b)
    (hsupp : ∀ z : ℝ × ℝ, z.1 ∉ Ioo a b → ξ z = 0) :
    ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      (6 * (Cm + C₀ + Cp) + 6 * (Cm + C₀ + Cp) * L ^ 2 + 3 * C₀ + 3) *
        ((∫ z in Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2) +
          ∫ z in Icc (-(R + 1)) (R + 1) ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) := by
  obtain ⟨hβmc, hβ₀c, hβpc⟩ := hβc
  have hξ0 {w : ℝ × ℝ} (hw : w.1 ≤ a ∨ b ≤ w.1) : ξ w = 0 :=
    hsupp w fun h ↦ by rcases hw with hw | hw <;> linarith [h.1, h.2]
  have hpc {β : ℝ → ℝ} {η : ℝ × ℝ → V} (hβ : ContDiff ℝ 2 β) (hη : ∀ w, η w = β w.1 • ξ w) :
      ContDiff ℝ 2 η := by
    rw [funext hη]
    exact (hβ.comp contDiff_fst).smul hξ
  -- The pieces `βm ξ`, `β₀ ξ`, `βp ξ`, supported in `(a, -R)`, the core and `(R, b)`.
  obtain ⟨ηm, hηm⟩ : ∃ η : ℝ × ℝ → V, ∀ w, η w = βm w.1 • ξ w := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨η₀, hη₀⟩ : ∃ η : ℝ × ℝ → V, ∀ w, η w = β₀ w.1 • ξ w := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨ηp, hηp⟩ : ∃ η : ℝ × ℝ → V, ∀ w, η w = βp w.1 • ξ w := ⟨_, fun _ ↦ rfl⟩
  have hsm (w : ℝ × ℝ) (hw : w.1 ∉ Ioo a (-R)) : ηm w = 0 := by
    rcases not_and_or.1 hw with hw | hw
    · rw [hηm, hξ0 (Or.inl (not_lt.1 hw)), smul_zero]
    · rw [hηm, hβm0 _ (not_lt.1 hw), zero_smul]
  have hs₀ (w : ℝ × ℝ) (hw : w.1 ∉ Ioo (-(R + 1)) (R + 1)) : η₀ w = 0 := by
    rw [hη₀, hβ₀0 _ hw, zero_smul]
  have hsp (w : ℝ × ℝ) (hw : w.1 ∉ Ioo R b) : ηp w = 0 := by
    rcases not_and_or.1 hw with hw | hw
    · rw [hηp, hβp0 _ (not_lt.1 hw), zero_smul]
    · rw [hηp, hξ0 (Or.inr (not_lt.1 hw)), smul_zero]
  -- The end estimates on `βm ξ` and `βp ξ`, and the interior estimate on `β₀ ξ`.
  have em := setIntegral_le_of_eq_smul_of_forall_notMem_Ioo J S (d' := b) hm hξ hper hβmc hηm
    (by linarith) (fun s hs ↦ hUm s hs.2) hsm le_rfl (by linarith)
  have ep := setIntegral_le_of_eq_smul_of_forall_notMem_Ioo J S (c' := a) hp hξ hper hβpc hηp
    (by linarith) (fun s hs ↦ hUp s hs.1) hsp (by linarith) le_rfl
  have e₀ := setIntegral_le_of_forall_notMem_Ioo J S hs₀ ha hb
    (setIntegral_norm_fderiv_sq_add_le_of_le hJc hS ((hpc hβ₀c hη₀).of_le one_le_two) hC₀
      (h₀ (hpc hβ₀c hη₀) (fun s _ ↦ by rw [hη₀, hη₀, ← zero_add (1 : ℝ), hper])
        (fun t ↦ hs₀ _ (by simp)) fun t ↦ hs₀ _ (by simp))
      (setIntegral_norm_sq_le_of_eq_smul hξ.continuous hβ₀c.continuous (fun s ↦ (hβ1 s).2.1)
        hη₀ _ _))
  -- The errors of the cutoffs, supported in the core.
  have hξ1 := hξ.of_le one_le_two
  have km := setIntegral_norm_fderiv_add_sq_le_of_eq_smul hJc hS hξ1 (hβmc.of_le one_le_two)
    (fun s ↦ (hβ1 s).1) (fun s ↦ (hβL s).1) (fun s hs ↦ (hβT s hs).1) hηm ha hb
  have k₀ := setIntegral_norm_fderiv_add_sq_le_of_eq_smul hJc hS hξ1 (hβ₀c.of_le one_le_two)
    (fun s ↦ (hβ1 s).2.1) (fun s ↦ (hβL s).2.1) (fun s hs ↦ (hβT s hs).2.1) hη₀ ha hb
  have kp := setIntegral_norm_fderiv_add_sq_le_of_eq_smul hJc hS hξ1 (hβpc.of_le one_le_two)
    (fun s ↦ (hβ1 s).2.2) (fun s ↦ (hβL s).2.2) (fun s hs ↦ (hβT s hs).2.2) hηp ha hb
  -- Splitting `ξ = βm ξ + β₀ ξ + βp ξ` costs a factor `3`.
  exact le_mul_add_of_le_three_mul hCm hC₀ hCp
    (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _)
    (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _)
    (setIntegral_norm_fderiv_sq_add_le_three_mul ((hpc hβmc hηm).of_le one_le_two)
      ((hpc hβ₀c hη₀).of_le one_le_two) ((hpc hβpc hηp).of_le one_le_two)
      (fun w ↦ by rw [hηm, hη₀, hηp, ← add_smul, ← add_smul, hsum, one_smul]) a b)
    em e₀ ep km k₀ kp

/-- **The semi-Fredholm estimate from estimates on the ends.** Let `J(z)` be `ω`-compatible and
let `J` and `S` be continuous on the cylinder `ℝ × [0, 1]`, and suppose that the operator
`D = ∂s + J(z) ∂t + S(z)` satisfies `L²` estimates far out on both ends: there are constants
`C₊, C₋ ≥ 0` and sets `U₊ ∈ atTop`, `U₋ ∈ atBot` such that every `C²` map `ξ` of period one in
`t`, vanishing on the slices `s = a` and `s = b` with `[a, b] ⊆ U_±`, satisfies
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C_± ∫ ‖D ξ‖²` over `[a, b] × [0, 1]`. Then there are constants
`C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` that vanishes for `s ∉ (a, b)`
satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals over `[a, b] × [0, 1]`. The constants do not depend on `a`, `b` or
`ξ`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_add_setIntegral_of_ends
    (hJ : ∀ z ∈ (univ : Set ℝ) ×ˢ Icc 0 1, ω.Compatible (J z))
    (hJc : ContinuousOn (fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (univ ×ˢ Icc 0 1))
    (hS : ContinuousOn S (univ ×ˢ Icc 0 1)) {Cp Cm : ℝ} (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm)
    {Up Um : Set ℝ} (hUp : Up ∈ atTop) (hUm : Um ∈ atBot)
    (hp : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ Up → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cp * ∫ z in Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2)
    (hm : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ Um → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cm * ∫ z in Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, (∀ z : ℝ × ℝ, z.1 ∉ Ioo a b → ξ z = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc 0 1, ‖fderiv ℝ ξ z stdComplexLineReal +
              J z (fderiv ℝ ξ z stdComplexLineImag) + S z (ξ z)‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) := by
  -- The end estimates hold below `-R` and beyond `R`, the interior estimate on the core
  -- `[-(R + 1), R + 1] × [0, 1]`.
  obtain ⟨Tp, hTp⟩ := mem_atTop_sets.1 hUp
  obtain ⟨Tm, hTm⟩ := mem_atBot_sets.1 hUm
  set R := max (max Tp (-Tm)) 0
  have hR : 0 ≤ R := le_max_right _ _
  have hRp : Tp ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRm : -Tm ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hK : Icc (-(R + 1)) (R + 1) ×ˢ Icc (0 : ℝ) 1 ⊆ univ ×ˢ Icc 0 1 :=
    prod_mono (subset_univ _) subset_rfl
  obtain ⟨C₀, hC₀, h₀⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic
    (by linarith : -(R + 1) ≤ R + 1) (fun z hz ↦ hJ z (hK hz)) (hJc.mono hK) (hS.mono hK)
  -- Cutoffs `βm + β₀ + βp = 1`, equal to one on `(-∞, -(R + 1)]`, on `[-R, R]` and on
  -- `[R + 1, ∞)`, with `β₀` vanishing outside `(-(R + 1), R + 1)`.
  obtain ⟨L, βm, β₀, βp, hβmc, hβ₀c, hβpc, hsum, hβ1, hβL, hβT, hβm0, hβ₀0, hβp0⟩ :=
    exists_contDiff_partitionOfUnity_three hR
  have h1 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : |x| ≤ 1 := (abs_of_nonneg hx.1).trans_le hx.2
  refine ⟨6 * (Cm + C₀ + Cp) + 6 * (Cm + C₀ + Cp) * L ^ 2 + 3 * C₀ + 3, by positivity, R + 1,
    fun ξ hξ hper a b hsupp ↦ ?_⟩
  -- Enlarging `[a, b]` to contain the core does not change the integrals over `[a, b] × [0, 1]`.
  obtain ⟨e₁, e₂⟩ := setIntegral_Icc_prod_eq_of_forall_notMem_Ioo J S hsupp
    (min_le_left a (-(R + 1))) (le_max_left b (R + 1))
  rw [← e₁, ← e₂]
  exact setIntegral_le_of_partition hJc hS hR hCm hC₀ hCp (fun s hs ↦ hTm s (by linarith))
    (fun s hs ↦ hTp s (by linarith)) hm h₀ hp
    ⟨hβmc.of_le (by simp), hβ₀c.of_le (by simp), hβpc.of_le (by simp)⟩ hsum
    (fun s ↦ ⟨h1 (hβ1 s).1, h1 (hβ1 s).2.1, h1 (hβ1 s).2.2⟩) hβL hβT hβm0
    hβ₀0 hβp0 hξ hper (min_le_right _ _) (le_max_right _ _) fun z hz ↦ hsupp z fun h ↦
      hz ⟨(min_le_left _ _).trans_lt h.1, h.2.trans_le (le_max_left _ _)⟩

end Patching

/-- **The semi-Fredholm estimate of the linearized Floer operator along a Floer cylinder.**
Let `H` be a jointly `C²` Hamiltonian whose suspended vector field is globally Lipschitz, with
orbits `x₋` and `x₊` whose initial points are nondegenerate fixed points of the time-one map, and
let `J_t(y)` be a `C¹` family of almost complex structures, compatible with `ω` along `x₋`, `x₊`
and the map `u`, which is `C¹` at the points of `ℝ × [0, 1]`. Suppose that the loops of `u` converge uniformly to `x₋` as
`s → -∞` and to `x₊` as `s → ∞`, while the slice defect `∂t u - X_{H_t}(u)` tends uniformly to
zero, as for a Floer cylinder from `x₋` to `x₊`. Then there are constants `C ≥ 0` and `T` such
that every `C²` map `ξ` of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`,

the first two integrals over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the
datum `K = H_t dt`. The constants do not depend on `a`, `b` or `ξ`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_setIntegral
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (Function.uncurry H)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (H t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (H t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (xp 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJxm : ∀ t, ω.Compatible (J t (xm t))) (hJxp : ∀ t, ω.Compatible (J t (xp t)))
    {u : ℝ × ℝ → V} (hu : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 u (s, t))
    (hJu : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ω.Compatible (J t (u (s, t))))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atBot (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, (∀ z : ℝ × ℝ, z.1 ∉ Ioo a b → ξ z = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc 0 1,
              ‖ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
                (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc 0 1, ‖ξ z‖ ^ 2) := by
  -- The estimates on the two ends, in the norm of `V`.
  obtain ⟨Cp, hCp, Up, hUp, hp⟩ :=
    exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization ω hX hH hxp hndp
      hJ hJxp (Eventually.of_forall hu) huxp hδp
  obtain ⟨Cm, hCm, Um, hUm, hm⟩ :=
    exists_mem_forall_setIntegral_norm_sq_le_mul_setIntegral_floerLinearization ω hX hH hxm hndm
      hJ hJxm (Eventually.of_forall hu) huxm hδm
  -- `D_u = ∂s + J_t(u) ∂t + S` for the zeroth-order coefficient `S` of the linearization.
  simp only [floerLinearization_eq_add, LinearMap.coe_toContinuousLinearMap'] at hp hm ⊢
  exact exists_forall_setIntegral_le_mul_setIntegral_add_setIntegral_of_ends
    (J := fun z ↦ J z.2 (u z)) (fun z hz ↦ hJu z.1 z.2 hz.2)
    (fun z hz ↦ (hJ.continuous.continuousAt.comp
      (continuousAt_snd.prodMk (hu z.1 z.2 hz.2).continuousAt)).continuousWithinAt)
    (ω.continuousOn_floerLinearizationCoeff
      (fun _ _ ↦ (hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
      (fun _ _ ↦ contDiffAt_const)
      (fun _ _ ↦ (hH.comp (contDiff_fst.snd.prodMk contDiff_snd)).contDiffAt)
      fun z hz ↦ hu z.1 z.2 hz.2) hCp hCm hUp hUm hp hm

end TauCeti.SymplecticForm
