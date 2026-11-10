/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Estimate
public import TauCeti.Geometry.Symplectic.Floer.EndLinearization
import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# The `L²` estimate of the linearized Floer operator on a cylindrical end

Let `u` be a map on a cylindrical end of a punctured Floer domain, with perturbation
`K = H_t dt`, whose loops converge to a nondegenerate one-periodic orbit `x` of `H` while the
slice defect `∂t u - X_{H_t}(u)` tends to zero. This file proves that the linearized Floer operator
`D_u` along `u` satisfies, on a far enough part of the end, the same `L²` estimate as the
stationary cylinder operator `D_x = ∂s + J_t(x) (∂t - S_t)` at the orbit, with
`S_t = dX_{H_t}(x(t))`: there are `C` and a far part `I` of the end such that

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D_u ξ, D_u ξ)`

over `[a, b] × [0, 1]`, for every `[a, b] ⊆ I` and every `C²` map `ξ` of period one in `t`
vanishing on the slices `s = a` and `s = b`, where `g_t = ω(·, J_t(x(t)) ·)`
(`TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization`). This
is the injectivity estimate of the linearized operator on the ends, the half of its Fredholm
property that is local to the ends.

The argument has two parts.

* **Stability of the cylinder estimate.** Suppose that `ξ` satisfies the estimate
  `E(ξ) ≤ C₀ ∫ g(D ξ, D ξ)` for the stationary cylinder operator `D` of continuous families `J_t`
  and `S_t`, where `E(ξ)` is the left-hand side above. Then there are `ε > 0` and `C`, depending
  only on `C₀`, `J` and `S`, such that `E(ξ) ≤ C ∫ g(f, f)` for every continuous `f` with
  `‖f - D ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` pointwise on the rectangle
  (`TauCeti.Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le`). Since
  `∂t ξ = (∂t ξ - S ξ) + S ξ`, the error is bounded by `E(ξ)` with a small factor, and it is
  absorbed into the left-hand side.
* **The end.** On a far enough part of the end, `D_u` is such a perturbation of `D_x`
  (`TauCeti.SymplecticForm.eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le`),
  and `D_x` satisfies the cylinder estimate at the nondegenerate orbit `x`
  (`SymplecticForm.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`).

The Sobolev completion, the surjectivity half and the patching with the compact core are not
treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the operator `∂s + J ∂t + S(s, t)` with limits `S^±(t)`.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  on the linearized operator.
-/

public section

open Function Filter Set MeasureTheory Topology
open scoped Manifold NNReal

namespace TauCeti

namespace Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}

omit [FiniteDimensional ℝ V] in
/-- The pointwise step of the stability estimate. If `g = ω(·, J ·)` satisfies
`α ‖v‖² ≤ g(v, v) ≤ β ‖v‖²`, `‖T‖ ≤ σ`, and `f` differs from `d = p + J (q - T y)` by at most
`ε (‖q‖ + ‖y‖)` with `4 β ε² (1 + σ)² ≤ α κ`, then
`g(d, d) ≤ (2 β / α) g(f, f) + κ (g(p, p) + g(q - T y, q - T y) + g(y, y))`. -/
private theorem associatedBilinForm_le_of_norm_sub_le {J : AlmostComplexStructure V}
    {T : V →L[ℝ] V} {α β σ ε κ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hκ : 0 ≤ κ)
    (hε : 0 ≤ ε) (hg : ∀ v, α * ‖v‖ ^ 2 ≤ ω.associatedBilinForm J v v ∧
      ω.associatedBilinForm J v v ≤ β * ‖v‖ ^ 2)
    (hT : ‖T‖ ≤ σ) (hεκ : 4 * β * ε ^ 2 * (1 + σ) ^ 2 ≤ α * κ) {f p q y : V}
    (hf : ‖f - (p + J (q - T y))‖ ≤ ε * (‖q‖ + ‖y‖)) :
    ω.associatedBilinForm J (p + J (q - T y)) (p + J (q - T y)) ≤
      2 * β / α * ω.associatedBilinForm J f f +
        κ * ((ω.associatedBilinForm J p p + ω.associatedBilinForm J (q - T y) (q - T y)) +
          ω.associatedBilinForm J y y) := by
  set d := p + J (q - T y)
  set w := q - T y
  have hσ : 0 ≤ σ := (norm_nonneg _).trans hT
  -- `‖q‖ ≤ ‖w‖ + σ ‖y‖`, hence `‖f - d‖ ≤ ε (1 + σ) (‖w‖ + ‖y‖)`.
  have hq : ‖q‖ ≤ ‖w‖ + σ * ‖y‖ := by
    calc ‖q‖ = ‖w + T y‖ := by rw [sub_add_cancel]
      _ ≤ ‖w‖ + ‖T y‖ := norm_add_le _ _
      _ ≤ ‖w‖ + σ * ‖y‖ := by gcongr; exact (T.le_opNorm y).trans (by gcongr)
  have he : ‖f - d‖ ≤ ε * (1 + σ) * (‖w‖ + ‖y‖) := by
    refine hf.trans ?_
    have : ‖q‖ + ‖y‖ ≤ (1 + σ) * (‖w‖ + ‖y‖) := by
      nlinarith [norm_nonneg w, norm_nonneg y]
    calc ε * (‖q‖ + ‖y‖) ≤ ε * ((1 + σ) * (‖w‖ + ‖y‖)) := by gcongr
      _ = _ := by ring
  -- `‖d‖² ≤ 2 ‖f‖² + 4 ε² (1 + σ)² (‖w‖² + ‖y‖²)`.
  have hd : ‖d‖ ≤ ‖f‖ + ‖f - d‖ := by
    simpa using norm_sub_le f (f - d)
  have hd2 : ‖d‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 4 * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by
    have h1 : ‖d‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 2 * ‖f - d‖ ^ 2 := by
      nlinarith [pow_le_pow_left₀ (norm_nonneg d) hd 2, sq_nonneg (‖f‖ - ‖f - d‖)]
    have h2 : ‖f - d‖ ^ 2 ≤ (ε * (1 + σ)) ^ 2 * (‖w‖ + ‖y‖) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) he 2
    have h3 : (‖w‖ + ‖y‖) ^ 2 ≤ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by
      nlinarith [sq_nonneg (‖w‖ - ‖y‖)]
    have h4 : 0 ≤ (ε * (1 + σ)) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have hpJ := (mul_nonneg hα.le (sq_nonneg ‖p‖)).trans (hg p).1
  have hf' := (hg f).1
  have hw' := (hg w).1
  have hy' := (hg y).1
  have hd' := (hg d).2
  have hfq : 2 * β * ‖f‖ ^ 2 ≤ 2 * β / α * ω.associatedBilinForm J f f := by
    calc 2 * β * ‖f‖ ^ 2 = 2 * β / α * (α * ‖f‖ ^ 2) := by field_simp
      _ ≤ _ := by gcongr
  have hwy : 4 * β * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) ≤
      κ * (ω.associatedBilinForm J w w + ω.associatedBilinForm J y y) := by
    calc _ ≤ α * κ * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by gcongr
      _ = κ * (α * ‖w‖ ^ 2 + α * ‖y‖ ^ 2) := by ring
      _ ≤ _ := by gcongr
  calc ω.associatedBilinForm J d d ≤ β * ‖d‖ ^ 2 := hd'
    _ ≤ β * (2 * ‖f‖ ^ 2 + 4 * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2)) := by gcongr
    _ = 2 * β * ‖f‖ ^ 2 + 4 * β * ε ^ 2 * (1 + σ) ^ 2 * (‖w‖ ^ 2 + ‖y‖ ^ 2) := by ring
    _ ≤ 2 * β / α * ω.associatedBilinForm J f f +
        κ * (ω.associatedBilinForm J w w + ω.associatedBilinForm J y y) := add_le_add hfq hwy
    _ ≤ _ := by gcongr; linarith [mul_nonneg hκ hpJ]

/-- **Stability of the cylinder estimate.** Let each `J_t` be `ω`-tame and depend continuously
on `t`, let `S` be continuous, and let `C₀ ≥ 0`. There are `ε > 0` and `C ≥ 0` with the following
property. Let `ξ` be a `C¹` map satisfying, over `[a, b] × [0, 1]`, the cylinder estimate

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C₀ ∫ g(D ξ, D ξ)`

for `g_t = ω(·, J_t ·)` and the stationary cylinder operator `D ξ = ∂s ξ + J_t (∂t ξ - S_t ξ)`.
Then every `f` continuous on the rectangle with `‖f - D ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` there satisfies
the same estimate with `C` in place of `C₀` and `f` in place of `D ξ`. The constants do not depend
on `a`, `b`, `ξ` or `f`. -/
theorem exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le
    (hJ : ∀ t, ω.Tames (J t)) (hJc : Continuous fun p : ℝ × V ↦ J p.1 p.2) (hSc : Continuous S)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ ε > 0, ∃ C, 0 ≤ C ∧ ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 1 ξ → ∀ ⦃a b : ℝ⦄,
      ∫ z in Icc a b ×ˢ Icc 0 1,
          ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
              (fderiv ℝ ξ z stdComplexLineReal) +
            ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
              (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
            ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
        C₀ * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2)
          (stationaryCylinderOperator J S ξ z) (stationaryCylinderOperator J S ξ z) →
      ∀ ⦃f : ℝ × ℝ → V⦄, ContinuousOn f (Icc a b ×ˢ Icc 0 1) →
        (∀ z ∈ Icc a b ×ˢ Icc 0 1, ‖f z - stationaryCylinderOperator J S ξ z‖ ≤
          ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖)) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
              ω.associatedBilinForm (J z.2) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2) (f z) (f z) := by
  have he : Continuous fun t ↦ LinearMap.toContinuousLinearMap (J t).toLinearMap :=
    continuous_clm_apply.2 fun v ↦ by
      simpa [Function.comp_def] using hJc.comp (continuous_id.prodMk continuous_const)
  obtain ⟨α, hα, β, hβ, hαβ⟩ := ω.exists_pos_forall_mul_norm_sq_le_associatedBilinForm
    isCompact_Icc he.continuousOn fun t (_ : t ∈ Icc (0 : ℝ) 1) ↦ hJ t
  obtain ⟨σ, hσ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hSc.continuousOn
  -- The error is absorbed once `C₀ κ ≤ 1 / 2`, which the choice of `ε` arranges.
  set m := 1 + |σ|
  set κ := 1 / (2 * (C₀ + 1))
  set ε := min 1 (α / (8 * (β + 1) * m ^ 2 * (C₀ + 1)))
  have hm : 0 < m := by positivity
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hεκ : 4 * β * ε ^ 2 * m ^ 2 ≤ α * κ := by
    have h₁ : β * ε ^ 2 ≤ (β + 1) * ε := by
      have hε₁ : ε ≤ 1 := min_le_left _ _
      nlinarith [mul_le_mul_of_nonneg_left hε₁ (mul_nonneg hβ hε.le)]
    calc 4 * β * ε ^ 2 * m ^ 2 = 4 * m ^ 2 * (β * ε ^ 2) := by ring
      _ ≤ 4 * m ^ 2 * ((β + 1) * ε) := by gcongr
      _ ≤ 4 * m ^ 2 * ((β + 1) * (α / (8 * (β + 1) * m ^ 2 * (C₀ + 1)))) := by
        gcongr; exact min_le_right _ _
      _ = α * κ := by simp only [κ]; field_simp; ring
  refine ⟨ε, hε, 4 * C₀ * β / α, by positivity, fun ξ hξ a b hst f hf hfD ↦ ?_⟩
  set R := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  -- The integrands: `e` of the left-hand side, `gD` of `g(D ξ)` and `gF` of `g(f)`.
  set e : ℝ × ℝ → ℝ := fun z ↦
    (ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineReal)
        (fderiv ℝ ξ z stdComplexLineReal) +
      ω.associatedBilinForm (J z.2) (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))
        (fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z))) +
      ω.associatedBilinForm (J z.2) (ξ z) (ξ z)
  set gF : ℝ × ℝ → ℝ := fun z ↦ ω.associatedBilinForm (J z.2) (f z) (f z)
  -- Integrability of the three integrands on the compact rectangle.
  have hdξ : Continuous (fderiv ℝ ξ) := hξ.continuous_fderiv one_ne_zero
  have hDc : Continuous (stationaryCylinderOperator J S ξ) := by
    have hw : Continuous fun z : ℝ × ℝ ↦ fderiv ℝ ξ z stdComplexLineImag - S z.2 (ξ z) :=
      (hdξ.clm_apply continuous_const).sub ((hSc.comp continuous_snd).clm_apply hξ.continuous)
    rw [funext (stationaryCylinderOperator_def J S ξ)]
    exact (hdξ.clm_apply continuous_const).add (hJc.comp (continuous_snd.prodMk hw))
  have hDi := (continuous_associatedBilinForm_apply_self (ω := ω) hJc hDc).continuousOn
    |>.integrableOn_compact (μ := volume) hR
  have hFi : IntegrableOn gF R :=
    (ω.continuousOn_apply_comp hf
      (hJc.comp_continuousOn (continuous_snd.continuousOn.prodMk hf))).integrableOn_compact hR
  have hEi : IntegrableOn e R :=
    ((continuous_associatedBilinForm_add_apply_self (ω := ω) hJc hSc hξ).add
      (continuous_associatedBilinForm_apply_self (ω := ω) hJc hξ.continuous)).continuousOn
      |>.integrableOn_compact hR
  -- Pointwise, `g(D ξ) ≤ (2 β / α) g(f) + κ e`.
  have hpt : ∫ z in R, ω.associatedBilinForm (J z.2) (stationaryCylinderOperator J S ξ z)
      (stationaryCylinderOperator J S ξ z) ≤ ∫ z in R, (2 * β / α * gF z + κ * e z) :=
    setIntegral_mono_on hDi ((hFi.const_mul (2 * β / α)).add (hEi.const_mul κ)) hRm
      fun z hz ↦ by
        have hz₂ : z.2 ∈ Icc (0 : ℝ) 1 := hz.2
        have hS : ‖S z.2‖ ≤ |σ| := (hσ z.2 hz₂).trans (le_abs_self σ)
        have h := hfD z hz
        rw [stationaryCylinderOperator_def] at h ⊢
        exact associatedBilinForm_le_of_norm_sub_le hα hβ (by positivity) hε.le
          (hαβ z.2 hz₂) hS hεκ h
  rw [integral_add (hFi.const_mul _) (hEi.const_mul _), integral_const_mul,
    integral_const_mul] at hpt
  -- Absorb: `E ≤ C₀ ((2 β / α) ∫ g(f) + κ E)` with `C₀ κ ≤ 1 / 2` and `E ≥ 0`.
  set E := ∫ z in R, e z
  have hg0 (z : ℝ × ℝ) (hz : z ∈ R) (v : V) : 0 ≤ ω.associatedBilinForm (J z.2) v v :=
    (mul_nonneg hα.le (sq_nonneg ‖v‖)).trans (hαβ z.2 hz.2 v).1
  have hE0 : 0 ≤ E := setIntegral_nonneg hRm fun z hz ↦
    add_nonneg (add_nonneg (hg0 z hz _) (hg0 z hz _)) (hg0 z hz _)
  have hκ : C₀ * κ ≤ 1 / 2 := by
    simp only [κ]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hfin := hst.trans (mul_le_mul_of_nonneg_left hpt hC₀)
  have hcross : C₀ * (κ * E) ≤ E / 2 := by
    rw [← mul_assoc]; nlinarith
  calc E ≤ 2 * (C₀ * (2 * β / α * ∫ z in R, gF z)) := by
        nlinarith
    _ = _ := by ring

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The `L²` estimate of the linearized Floer operator on a cylindrical end.** Let `x` be a
one-periodic orbit of a one-periodic, jointly `C²` time-dependent Hamiltonian `H` whose suspended
vector field is globally Lipschitz, with `x(0)` a nondegenerate fixed point of the time-one map.
Let `J_t(y)` be a `C¹` family of almost complex structures, `ω`-compatible along `x`. Let `u` be
`C¹` on the far part of an end, along a filter `l` such as `atTop` for a positive end or `atBot`
for a negative one, with loops `u(s, ·)` converging uniformly on `[0, 1]` to `x` and slice defect
`∂t u - X_{H_t}(u)` converging uniformly to zero there.

Then there are a constant `C ≥ 0` and a set `I ∈ l` such that the linearized Floer operator `D_u`
along `u` for the datum `K = H_t dt` satisfies, for every `[a, b] ⊆ I` and every `C²` map `ξ` of
period one in `t` vanishing on the slices `s = a` and `s = b`,

`∫ (g(∂s ξ, ∂s ξ) + g(∂t ξ - S ξ, ∂t ξ - S ξ) + g(ξ, ξ)) ≤ C ∫ g(D_u ξ, D_u ξ)`

over `[a, b] × [0, 1]`, for `g_t = ω(·, J_t(x(t)) ·)` and `S_t = dX_{H_t}(x(t))`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization
    (ω : SymplecticForm V) {H : ℝ → V → ℝ} {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension H))
    (hH : ContDiff ℝ 2 (uncurry H)) (hHp : Periodic H 1) {x : ℝ → V}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H t) (x t)) t) (hxp : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow H hX 0 1) (x 0))
    {J : ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 1 fun p : ℝ × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJx : ∀ t, ω.Compatible (J t (x t))) {l : Filter ℝ} {u : ℝ × ℝ → V}
    (hu : ∀ᶠ s in l, ∀ t, ContDiffAt ℝ 1 u (s, t))
    (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H t)) u (s, t)) 0 l (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ I ∈ l, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ I →
        (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc 0 1,
            ((ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineReal)
                (fderiv ℝ ξ z stdComplexLineReal) +
              ω.associatedBilinForm (J z.2 (x z.2)) (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))
                (fderiv ℝ ξ z stdComplexLineImag -
                  fderiv ℝ (ω.hamiltonianVectorField (H z.2)) (x z.2) (ξ z))) +
              ω.associatedBilinForm (J z.2 (x z.2)) (ξ z) (ξ z)) ≤
          C * ∫ z in Icc a b ×ˢ Icc 0 1, ω.associatedBilinForm (J z.2 (x z.2))
            (ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z)
            (ω.floerLinearization (fun w y ↦ (J w.2 y).toLinearMap.toContinuousLinearMap)
              (fun _ _ ↦ 0) (fun w ↦ H w.2) u ξ z) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦ (hx t).continuousAt
  have hJxc : Continuous fun p : ℝ × V ↦ J p.1 (x p.1) p.2 := by
    simpa [Function.comp_def] using
      ((hJ.continuous.comp (continuous_id.prodMk hxc)).comp continuous_fst).clm_apply
        continuous_snd
  -- The stationary cylinder estimate at `x`, and its stability under small perturbations.
  obtain ⟨C₀, hC₀, hst⟩ := ω.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator
    hX hH hHp hx hxp hnd hJx hJxc
  obtain ⟨ε, hε, C, hC, hpert⟩ :=
    Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le
      (fun t ↦ (hJx t).tames) hJxc (ω.continuous_fderiv_hamiltonianVectorField_comp hH hxc) hC₀
  -- On the far part of the end, `D_u` is within `ε` of the stationary cylinder operator.
  have hev := eventually_norm_floerLinearization_sub_stationaryCylinderOperator_le ω hJ hH
    isCompact_Icc hxc.continuousOn hux hδ hε
  refine ⟨C, hC, _, hev.and hu, fun ξ hξ hper a b hab hI ha hb ↦ ?_⟩
  have hJ' : ContDiff ℝ 1 (uncurry fun (w : ℝ × ℝ) (y : V) ↦
      (J w.2 y).toLinearMap.toContinuousLinearMap) :=
    hJ.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hKt : ContDiff ℝ 2 (uncurry fun (w : ℝ × ℝ) ↦ H w.2) :=
    hH.comp (contDiff_fst.snd.prodMk contDiff_snd)
  refine hpert (hξ.of_le one_le_two) (hst hξ hper hab ha hb) ?_ ?_
  · rintro ⟨s, t⟩ ⟨hs, -⟩
    exact (ω.continuousAt_floerLinearization hJ' contDiff_const hKt ((hI hs).2 t)
      (hξ.of_le one_le_two).contDiffAt).continuousWithinAt
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact (hI hs).1 t ht ξ

end SymplecticForm

end TauCeti
