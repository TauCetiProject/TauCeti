/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.LinearAlgebra.Multilinear.Basis
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Mollified discs

Let `σ : ℂ → E` be a `C¹` map into a finite-dimensional real normed space and `D` a closed disc
in `ℂ`. The disc `σ|D` pairs with a continuous two-form `Θ` on `E` through

`∫_D σ^* Θ = ∫_D Θ(σ z)(∂ₛσ z, ∂ₜσ z) dz`,

where `∂ₛσ z = Dσ(z) 1` and `∂ₜσ z = Dσ(z) i`. Averaging this pairing over the translated discs
`σ + p` against a weight `ρ(p)` turns it into the pairing of `Θ` with a field of tensors, the
**mollified disc**

`ξ(y) = ∫_D ρ(y - σ z) (∂ₛσ z ⊗ ∂ₜσ z) dz`.

On a basis `b` of `E` with coordinates `b*_j`, the field `ξ` has the scalar coefficients

`ξ_s(y) = ∫_D ρ(y - σ z) b*_{s 0}(∂ₛσ z) b*_{s 1}(∂ₜσ z) dz`

(`TauCeti.discMollification b ρ σ z₀ r s`), one for each pair of basis indices `s`, and the
averaging identity reads

`∫_E ρ(p) ∫_D Θ(σ z + p)(∂ₛσ z, ∂ₜσ z) dz dp = ∑ s, ∫_E ξ_s(y) Θ(y)(b (s 0), b (s 1)) dy`

(`TauCeti.integral_mul_setIntegral_add_eq_sum_integral_discMollification_mul`), for every
continuous `Θ`, continuous compactly supported `ρ` and additive Haar measure on `E`. It is
Fubini's theorem combined with the translation invariance of the Haar measure and the expansion
of `Θ(y)` in coordinates (`MultilinearMap.apply_eq_sum_prod_repr_smul`).

The coefficients are as regular as the weight, whatever the regularity of `σ` beyond `C¹`
(`TauCeti.contDiff_discMollification`), and they are supported in `supp ρ + σ(D)`
(`TauCeti.tsupport_discMollification_subset`). So for a smooth compactly supported `ρ` they are
smooth compactly supported test functions. This is how the pairings of a disc with a sequence of
two-forms are controlled by the convergence of the coefficients `Θ(y)(v, w)` of these forms as
distributions: when the pairing is the same for all the translated discs `σ + p` with `p` in the
support of a weight of integral `1`, it equals a finite sum of pairings of coefficients of the
forms with fixed test functions. The translations `p ↦ σ + p` are the flows of the constant
vector fields, which span every tangent space, so in a chart they supply a submersive family of
discs through `σ`.

## Main results

* `TauCeti.discMollification`: the coefficients `ξ_s` of the mollified disc.
* `TauCeti.contDiff_discMollification`, `TauCeti.hasCompactSupport_discMollification`:
  regularity and support.
* `TauCeti.integral_mul_setIntegral_add_eq_sum_integral_discMollification_mul`: the averaging
  identity.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.2 (regularization of currents by convolution).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §1.
-/
public section

noncomputable section

open Complex MeasureTheory Metric Set
open scoped Pointwise

namespace TauCeti

variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {b : Module.Basis κ ℝ E}
  {ρ : E → ℝ} {σ : ℂ → E} {z₀ : ℂ} {r : ℝ}

/-- The coefficients of the **mollified disc** `ξ(y) = ∫_D ρ(y - σ z) (∂ₛσ z ⊗ ∂ₜσ z) dz` of a disc
`σ : ℂ → E` restricted to the closed disc `D` of radius `r` about `z₀`, with weight `ρ`, on the
basis `b`: the coefficient of `b (s 0) ⊗ b (s 1)` at `y` is
`∫_D ρ(y - σ z) b*_{s 0}(∂ₛσ z) b*_{s 1}(∂ₜσ z) dz`, where `∂ₛσ z = Dσ(z) 1`,
`∂ₜσ z = Dσ(z) i` and `b*_j` is the `j`-th coordinate of `b`. -/
def discMollification (b : Module.Basis κ ℝ E) (ρ : E → ℝ) (σ : ℂ → E) (z₀ : ℂ) (r : ℝ)
    (s : Fin 2 → κ) (y : E) : ℝ :=
  ∫ z in closedBall z₀ r,
    ρ (y - σ z) * (b.repr (fderiv ℝ σ z 1) (s 0) * b.repr (fderiv ℝ σ z I) (s 1))

/-- The defining formula of `TauCeti.discMollification`. -/
theorem discMollification_def (b : Module.Basis κ ℝ E) (ρ : E → ℝ) (σ : ℂ → E) (z₀ : ℂ) (r : ℝ)
    (s : Fin 2 → κ) (y : E) :
    discMollification b ρ σ z₀ r s y = ∫ z in closedBall z₀ r,
      ρ (y - σ z) * (b.repr (fderiv ℝ σ z 1) (s 0) * b.repr (fderiv ℝ σ z I) (s 1)) :=
  (rfl)

/-- The mollified disc vanishes outside `supp ρ + σ(D)`. -/
theorem discMollification_eq_zero {y : E} (hy : y ∉ tsupport ρ + σ '' closedBall z₀ r)
    (s : Fin 2 → κ) : discMollification b ρ σ z₀ r s y = 0 := by
  rw [discMollification_def]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz ↦ ?_
  rw [image_eq_zero_of_notMem_tsupport fun h ↦
    hy ⟨y - σ z, h, σ z, mem_image_of_mem σ hz, sub_add_cancel y (σ z)⟩, zero_mul]

/-- The mollified disc of a compactly supported weight is supported in `supp ρ + σ(D)`. -/
theorem tsupport_discMollification_subset (hρ : HasCompactSupport ρ) (hσ : Continuous σ)
    (s : Fin 2 → κ) :
    tsupport (discMollification b ρ σ z₀ r s) ⊆ tsupport ρ + σ '' closedBall z₀ r :=
  closure_minimal (fun _ hy ↦ by_contra fun h ↦ hy (discMollification_eq_zero h s))
    (IsCompact.add hρ ((isCompact_closedBall z₀ r).image hσ)).isClosed

/-- The mollified disc of a compactly supported weight has compact support. -/
theorem hasCompactSupport_discMollification (hρ : HasCompactSupport ρ) (hσ : Continuous σ)
    (s : Fin 2 → κ) : HasCompactSupport (discMollification b ρ σ z₀ r s) :=
  (IsCompact.add hρ ((isCompact_closedBall z₀ r).image hσ)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_discMollification_subset hρ hσ s)

variable [FiniteDimensional ℝ E]

/-- The coordinates of the tangent vectors `∂ₛσ`, `∂ₜσ` of a `C¹` disc are continuous. -/
private theorem continuous_repr_fderiv_mul (hσ : ContDiff ℝ 1 σ) (s : Fin 2 → κ) :
    Continuous fun z ↦ b.repr (fderiv ℝ σ z 1) (s 0) * b.repr (fderiv ℝ σ z I) (s 1) := by
  have hD := hσ.continuous_fderiv one_ne_zero
  simp_rw [← Module.Basis.coord_apply]
  exact ((b.coord (s 0)).continuous_of_finiteDimensional.comp (hD.clm_apply continuous_const)).mul
    ((b.coord (s 1)).continuous_of_finiteDimensional.comp (hD.clm_apply continuous_const))

/-- **Regularity of the mollified disc.** The mollified disc of a `C¹` disc with a `C^n` weight is
`C^n`. -/
theorem contDiff_discMollification {n : ℕ∞} (hρ : ContDiff ℝ n ρ) (hσ : ContDiff ℝ 1 σ)
    (s : Fin 2 → κ) : ContDiff ℝ n (discMollification b ρ σ z₀ r s) := by
  let D := closedBall z₀ r
  have : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall z₀ r)
  have : IsFiniteMeasure (volume.comap ((↑) : D → ℂ)) :=
    ⟨by rw [comap_subtype_coe_apply measurableSet_closedBall, image_univ, Subtype.range_coe]
        exact measure_closedBall_lt_top⟩
  -- Integrate `ρ(y - p)` along `p = σ z` against the continuous weight of the coordinates.
  have hg := (continuous_repr_fderiv_mul (b := b) hσ s).comp
    (continuous_subtype_val (p := (· ∈ D)))
  have key := contDiffOn_integral_smul_of_contDiffOn (μ := volume.comap ((↑) : D → ℂ))
    (ι := fun z : D ↦ σ z) (F := fun q : E × E ↦ ρ (q.1 - q.2))
    (integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ))
    (hσ.continuous.comp (continuous_subtype_val (p := (· ∈ D)))) isOpen_univ
    (hρ.comp (contDiff_fst.sub contDiff_snd)).contDiffOn (U := univ) fun _ _ _ ↦ mem_univ _
  rw [contDiffOn_univ] at key
  convert key using 1
  funext y
  rw [discMollification_def, ← integral_subtype_comap measurableSet_closedBall]
  simp only [Function.comp_apply, smul_eq_mul, mul_comm]
  -- The two sides differ only by unfolding the local abbreviation `D`.
  rfl

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Fintype κ]

/-- **The averaging identity for a mollified disc.** For a continuous two-form `Θ`, a continuous
compactly supported weight `ρ`, a `C¹` disc `σ`, a basis `b` and an additive Haar measure `μ` on
`E`, averaging the pairings of `Θ` with the translated discs `σ + p` against `ρ(p)` gives the
pairing of `Θ` with the mollified disc:

`∫ ρ(p) ∫_D Θ(σ z + p)(∂ₛσ z, ∂ₜσ z) dz dp = ∑ s, ∫ ξ_s(y) Θ(y)(b (s 0), b (s 1)) dy`,

where `ξ_s` are the coefficients `TauCeti.discMollification b ρ σ z₀ r s`. -/
theorem integral_mul_setIntegral_add_eq_sum_integral_discMollification_mul
    [μ.IsAddHaarMeasure] {Θ : E → E [⋀^Fin 2]→L[ℝ] ℝ} (hΘ : Continuous Θ) (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (hσ : ContDiff ℝ 1 σ) :
    ∫ p, ρ p * (∫ z in closedBall z₀ r, Θ (σ z + p) ![fderiv ℝ σ z 1, fderiv ℝ σ z I]) ∂μ =
      ∑ s : Fin 2 → κ, ∫ y, discMollification b ρ σ z₀ r s y * Θ y (fun i ↦ b (s i)) ∂μ := by
  set t : ℂ → Fin 2 → E := fun z ↦ ![fderiv ℝ σ z 1, fderiv ℝ σ z I]
  have hσc := hσ.continuous
  have hD := hσ.continuous_fderiv one_ne_zero
  -- The pairing `(x, z) ↦ Θ(x)(∂ₛσ z, ∂ₜσ z)` is continuous.
  have hev : Continuous fun q : E × ℂ ↦ Θ q.1 (t q.2) :=
    continuous_eval.comp ((hΘ.comp continuous_fst).prodMk
      (((hD.clm_apply continuous_const).matrixVecCons
        ((hD.clm_apply continuous_const).matrixVecCons continuous_const)).comp continuous_snd))
  -- First swap: integrate over the translations first.
  have h₁ : Integrable (Function.uncurry fun p z ↦ ρ p * Θ (σ z + p) (t z))
      (μ.prod (volume.restrict (closedBall z₀ r))) := by
    refine integrable_prod_restrict_of_continuous
      ((hρ.comp continuous_fst).mul (hev.comp ((hσc.comp continuous_snd).add continuous_fst
        |>.prodMk continuous_snd))) hρc (isCompact_closedBall z₀ r) fun p z _ hp ↦ ?_
    simp [image_eq_zero_of_notMem_tsupport hp]
  -- Second swap: integrate over the disc first.
  have h₂ : Integrable (Function.uncurry fun y z ↦ ρ (y - σ z) * Θ y (t z))
      (μ.prod (volume.restrict (closedBall z₀ r))) := by
    refine integrable_prod_restrict_of_continuous
      ((hρ.comp (continuous_fst.sub (hσc.comp continuous_snd))).mul hev)
      (IsCompact.add hρc ((isCompact_closedBall z₀ r).image hσc)) (isCompact_closedBall z₀ r)
      fun y z hz hy ↦ ?_
    simp [image_eq_zero_of_notMem_tsupport fun h ↦
      hy ⟨y - σ z, h, σ z, mem_image_of_mem σ hz, sub_add_cancel y (σ z)⟩]
  -- In coordinates, `Θ(y)(∂ₛσ z, ∂ₜσ z)` is a finite sum of products.
  have hexp (y : E) (z : ℂ) : ρ (y - σ z) * Θ y (t z) = ∑ s : Fin 2 → κ,
      ρ (y - σ z) * (b.repr (fderiv ℝ σ z 1) (s 0) * b.repr (fderiv ℝ σ z I) (s 1)) *
        Θ y (fun i ↦ b (s i)) := by
    -- Evaluate `Θ y` as the underlying multilinear map to expand it in coordinates.
    rw [show Θ y (t z) = (Θ y).toMultilinearMap (t z) from rfl,
      MultilinearMap.apply_eq_sum_prod_repr_smul _ fun _ ↦ b, Finset.mul_sum]
    simp [t, Fin.prod_univ_two, mul_assoc]
  have hcoef (s : Fin 2 → κ) : Continuous (discMollification b ρ σ z₀ r s) :=
    (contDiff_discMollification (n := 0) (contDiff_zero.2 hρ) hσ s).continuous
  calc ∫ p, ρ p * (∫ z in closedBall z₀ r, Θ (σ z + p) (t z)) ∂μ
      = ∫ p, (∫ z in closedBall z₀ r, ρ p * Θ (σ z + p) (t z)) ∂μ := by
        simp_rw [integral_const_mul]
    _ = ∫ z in closedBall z₀ r, ∫ p, ρ p * Θ (σ z + p) (t z) ∂μ := integral_integral_swap h₁
    _ = ∫ z in closedBall z₀ r, ∫ y, ρ (y - σ z) * Θ y (t z) ∂μ := by
        -- Translate the inner integral by `σ z`.
        refine setIntegral_congr_fun measurableSet_closedBall fun z _ ↦ ?_
        rw [← integral_add_right_eq_self (fun y ↦ ρ (y - σ z) * Θ y (t z)) (σ z)]
        simp only [add_sub_cancel_right, add_comm]
    _ = ∫ y, (∫ z in closedBall z₀ r, ρ (y - σ z) * Θ y (t z)) ∂μ :=
        (integral_integral_swap h₂).symm
    _ = ∫ y, ∑ s : Fin 2 → κ, discMollification b ρ σ z₀ r s y * Θ y (fun i ↦ b (s i)) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
        simp only [hexp]
        rw [integral_finsetSum _ fun s _ ↦ ?_]
        · simp_rw [discMollification_def, integral_mul_const]
        · exact ((((hρ.comp (continuous_const.sub hσc)).mul
            (continuous_repr_fderiv_mul hσ s)).mul continuous_const).continuousOn
              |>.integrableOn_compact (isCompact_closedBall z₀ r))
    _ = ∑ s : Fin 2 → κ, ∫ y, discMollification b ρ σ z₀ r s y * Θ y (fun i ↦ b (s i)) ∂μ :=
        integral_finsetSum _ fun s _ ↦ ((hcoef s).mul (continuous_eval_const _ |>.comp hΘ))
          |>.integrable_of_hasCompactSupport
            ((hasCompactSupport_discMollification hρc hσc s).mul_right)

end TauCeti
