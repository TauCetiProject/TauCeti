/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Translation
import TauCeti.Analysis.Holder.MeanValue

/-!
# Spatial derivatives of solutions of the parabolic Cauchy problem

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in `C_b^{α,α/2}`, `0 < α < 1`, with `a` uniformly elliptic, and let
`u ∈ C_b^{2+α,1+α/2}` solve `P u = f`. Fix a direction `e`. Differentiating the equation along
`e` gives the equation for `∂ₑu`, with the differentiated coefficients as lower-order data:

`P (∂ₑu) = ∂ₑf + (∂ₑaⁱʲ) ∂ᵢ∂ⱼu + (∂ₑbⁱ) ∂ᵢu + (∂ₑc) u`.

This file proves that this formal computation is correct in the Hölder class, without assuming
any third derivative of `u`. If the derivatives `∂ₑaⁱʲ`, `∂ₑbⁱ`, `∂ₑc`, `∂ₑf` exist and lie in
`C_b^{α,α/2}`, and the initial trace has `∂ₑu(·, 0) = g'` in `C_b^{2,α}`, then `∂ₑu` is the
`C_b^{2+α,1+α/2}` solution of the differentiated Cauchy problem with initial datum `g'`
(`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE_symm_apply_eq_spatialFDerivL_apply`).
In particular `∂ₑu` has two spatial derivatives and one time derivative in `C_b^{α,α/2}`. This is
the step from order `k = 0` to order `k = 1` of the higher-order parabolic Schauder theory: the
equation for a spatial derivative is the base problem with lower-order data.

## The argument

Let `v` be the solution of the differentiated problem, given by the solution operator
`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`, and for `h ≠ 0` compare it with the
difference quotient `δₕu = h⁻¹ (u(· + h e, ·) - u)`, which lies in `C_b^{2+α,1+α/2}` because
translations do. Translating the equation shows that `P (δₕu) - P v` is a sum of terms such as
`h⁻¹ (aⁱʲ(· + h e) - aⁱʲ) ∂ᵢ∂ⱼu(· + h e) - ∂ₑaⁱʲ ∂ᵢ∂ⱼu`. A first-order Taylor estimate with the
Hölder continuous derivative `∂ₑaⁱʲ` and the Hölder continuity of `∂ᵢ∂ⱼu` make all of them
`O(|h|^α)` uniformly, and similarly the initial values differ by `O(|h|)`. The maximum principle
in the form of the a priori bound
`TauCeti.ParabolicC2HolderSpace.abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le`
then gives `δₕu → v` uniformly as `h → 0`. Since `δₕu → ∂ₑu` pointwise, `v = ∂ₑu`. The
comparison argument avoids the compactness step of the usual proof by difference quotients.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0}

/-! ### Auxiliary estimates -/

section Slab

variable {E Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {t₀ t₁ : ℝ}

/-- The first-order Taylor estimate along `e` for the time slice of a scalar parabolic Hölder map
whose derivative along `e` is a parabolic Hölder map. -/
private theorem abs_sub_sub_mul_le_of_hasLineDerivAt [NormedSpace ℝ E]
    {F F' : HolderSpace α (slab (E := E) t₀ t₁) ℝ} {e : E} {s : Icc t₀ t₁}
    (hF : ∀ x, HasLineDerivAt ℝ (fun y ↦ F (slabMk y s)) (F' (slabMk x s)) x e) (y : E) (h : ℝ) :
    |F (slabMk (y + h • e) s) - F (slabMk y s) - h * F' (slabMk y s)| ≤
      ‖F'‖ * ‖h • e‖ ^ (α : ℝ) * |h| := by
  simpa [Real.norm_eq_abs, smul_eq_mul] using
    (F'.holderWith_slabMk s).norm_sub_sub_smul_le_of_hasLineDerivAt hF y h

/-- One term of the forcing of a difference quotient. For a scalar parabolic Hölder map `F` with
derivative `F'` along `e` and a function `m` on the slab with `|m (y + h e)| ≤ M` and
`|m (y + h e) - m y| ≤ D` at time `s`, the defect
`(F (y + h e) - F y) m (y + h e) - h F' y m y` is at most `|h| ‖F'‖ (‖h • e‖ ^ α M + D)`. -/
private theorem abs_sub_mul_sub_mul_le_of_hasLineDerivAt [NormedSpace ℝ E]
    {F F' : HolderSpace α (slab (E := E) t₀ t₁) ℝ} {e : E} {s : Icc t₀ t₁}
    (hF : ∀ x, HasLineDerivAt ℝ (fun y ↦ F (slabMk y s)) (F' (slabMk x s)) x e)
    {m : slab (E := E) t₀ t₁ → ℝ} {y : E} {h M D : ℝ} (hm : |m (slabMk (y + h • e) s)| ≤ M)
    (hd : |m (slabMk (y + h • e) s) - m (slabMk y s)| ≤ D) :
    |(F (slabMk (y + h • e) s) - F (slabMk y s)) * m (slabMk (y + h • e) s) -
        h * (F' (slabMk y s) * m (slabMk y s))| ≤
      |h| * (‖F'‖ * ‖h • e‖ ^ (α : ℝ) * M + ‖F'‖ * D) := by
  have hF₁ := abs_sub_sub_mul_le_of_hasLineDerivAt hF y h
  have hF' : |F' (slabMk y s)| ≤ ‖F'‖ := by simpa using F'.norm_apply_le (slabMk y s)
  generalize F (slabMk (y + h • e) s) = F₁ at *
  generalize F (slabMk y s) = F₀ at *
  generalize F' (slabMk y s) = G at *
  generalize m (slabMk (y + h • e) s) = m₁ at *
  generalize m (slabMk y s) = m₀ at *
  calc |(F₁ - F₀) * m₁ - h * (G * m₀)| = |(F₁ - F₀ - h * G) * m₁ + h * G * (m₁ - m₀)| := by
        ring_nf
    _ ≤ |F₁ - F₀ - h * G| * |m₁| + |h| * |G| * |m₁ - m₀| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ ‖F'‖ * ‖h • e‖ ^ (α : ℝ) * |h| * M + |h| * ‖F'‖ * D :=
        add_le_add (mul_le_mul hF₁ hm (abs_nonneg _) ((abs_nonneg _).trans hF₁))
          (mul_le_mul (mul_le_mul_of_nonneg_left hF' (abs_nonneg h)) hd (abs_nonneg _)
            (mul_nonneg (abs_nonneg h) (norm_nonneg _)))
    _ = |h| * (‖F'‖ * ‖h • e‖ ^ (α : ℝ) * M + ‖F'‖ * D) := by ring

end Slab

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A local shortcut for the norm on Euclidean Hessians, for the reason explained in
`TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance : NormedAddCommGroup (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
  inferInstance

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- Translating the solution but not the coefficients: `P (u(· + w, ·))` at `(y, s)` is `P u` at
`(y + w, s)` plus the differences of the coefficients at the two points against the derivatives
of `u` at `(y + w, s)`. -/
private theorem euclideanParabolicOperatorL_translateLIE_apply (hα : α ≤ 1)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) (w y : EuclideanSpace ℝ ι)
    (s : Icc t₀ t₁) :
    euclideanParabolicOperatorL hα a b c (translateLIE α ℝ ht w u) (slabMk y s) =
      euclideanParabolicOperatorL hα a b c u (slabMk (y + w) s) +
        (∑ i, ∑ j, (a i j (slabMk (y + w) s) - a i j (slabMk y s)) *
            spatialSecondFDerivL u (slabMk (y + w) s) (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) +
          ∑ i, (b i (slabMk (y + w) s) - b i (slabMk y s)) *
            spatialFDerivL u (slabMk (y + w) s) (EuclideanSpace.single i 1) +
          (c (slabMk (y + w) s) - c (slabMk y s)) * u (slabMk (y + w) s)) := by
  simp only [euclideanParabolicOperatorL_apply, timeDerivL_translateLIE,
    spatialSecondFDerivL_translateLIE, spatialFDerivL_translateLIE, translateLIE_apply,
    slabSpaceMap_slabMk, IsometryEquiv.addRight_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The forcing of `δₕu - v`, where `δₕu = h⁻¹ (u(· + h e, ·) - u)` and `v` solves the
differentiated equation: a sum of difference quotients of the coefficients and the forcing,
against the derivatives of `u` at the translated point, minus their limits. -/
private theorem euclideanParabolicOperatorL_smul_translateLIE_sub_sub_apply (hα : α ≤ 1)
    {a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c c' f f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {u v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht}
    (hu : euclideanParabolicOperatorL hα a b c u = f)
    (hv : euclideanParabolicOperatorL hα a b c v = f' + spatialOperatorL hα
      (euclideanSecondOrderCoeff a') (euclideanFirstOrderCoeff b') (euclideanZerothOrderCoeff c') u)
    {h : ℝ} (hh : h ≠ 0) (e y : EuclideanSpace ℝ ι) (s : Icc t₀ t₁) :
    euclideanParabolicOperatorL hα a b c (h⁻¹ • (translateLIE α ℝ ht (h • e) u - u) - v)
        (slabMk y s) = h⁻¹ *
      ((f (slabMk (y + h • e) s) - f (slabMk y s) - h * f' (slabMk y s)) +
        ∑ i, ∑ j, ((a i j (slabMk (y + h • e) s) - a i j (slabMk y s)) *
            spatialSecondFDerivL u (slabMk (y + h • e) s) (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1) -
          h * (a' i j (slabMk y s) * spatialSecondFDerivL u (slabMk y s)
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) +
        ∑ i, ((b i (slabMk (y + h • e) s) - b i (slabMk y s)) *
            spatialFDerivL u (slabMk (y + h • e) s) (EuclideanSpace.single i 1) -
          h * (b' i (slabMk y s) * spatialFDerivL u (slabMk y s) (EuclideanSpace.single i 1))) +
        ((c (slabMk (y + h • e) s) - c (slabMk y s)) * u (slabMk (y + h • e) s) -
          h * (c' (slabMk y s) * u (slabMk y s)))) := by
  have h₁ : euclideanParabolicOperatorL hα a b c (h⁻¹ • (translateLIE α ℝ ht (h • e) u - u) - v)
      (slabMk y s) = h⁻¹ * (euclideanParabolicOperatorL hα a b c (translateLIE α ℝ ht (h • e) u)
        (slabMk y s) - euclideanParabolicOperatorL hα a b c u (slabMk y s) -
          h * euclideanParabolicOperatorL hα a b c v (slabMk y s)) := by
    simp only [map_sub, map_smul, HolderSpace.sub_apply, HolderSpace.smul_apply, smul_eq_mul]
    field_simp
  rw [h₁, euclideanParabolicOperatorL_translateLIE_apply, hu, hv]
  congr 1
  simp only [HolderSpace.add_apply, spatialOperatorL_apply, euclideanSecondOrderCoeff_apply,
    euclideanFirstOrderCoeff_apply, euclideanZerothOrderCoeff_apply, sub_mul, mul_add,
    Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- The Hessian entries of `u` are bounded by `‖D_x²u‖`, and they change by at most
`‖D_x²u‖ ‖w‖ ^ α` under a spatial translation by `w`. -/
private theorem abs_spatialSecondFDerivL_apply_le
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) (y w : EuclideanSpace ℝ ι)
    (s : Icc t₀ t₁) (i j : ι) :
    |spatialSecondFDerivL u (slabMk (y + w) s) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)| ≤ ‖spatialSecondFDerivL u‖ ∧
      |spatialSecondFDerivL u (slabMk (y + w) s) (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) -
        spatialSecondFDerivL u (slabMk y s) (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1)| ≤ ‖spatialSecondFDerivL u‖ * ‖w‖ ^ (α : ℝ) := by
  refine ⟨(ContinuousLinearMap.abs_apply_single_single_le _ i j).trans
    (HolderSpace.norm_apply_le _ _), ?_⟩
  have h₁ := ContinuousLinearMap.abs_apply_single_single_le
    (spatialSecondFDerivL u (slabMk (y + w) s) - spatialSecondFDerivL u (slabMk y s)) i j
  rw [_root_.sub_apply, _root_.sub_apply, ← dist_eq_norm] at h₁
  refine h₁.trans ?_
  simpa [dist_eq_norm] using ((spatialSecondFDerivL u).holderWith_slabMk s).dist_le (y + w) y

/-- The gradient entries of `u` are bounded by `‖D_xu‖`, and they change by at most
`‖D_x²u‖ ‖w‖` under a spatial translation by `w`. -/
private theorem abs_spatialFDerivL_apply_le (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (y w : EuclideanSpace ℝ ι) (s : Icc t₀ t₁) (i : ι) :
    |spatialFDerivL u (slabMk (y + w) s) (EuclideanSpace.single i 1)| ≤ ‖spatialFDerivL u‖ ∧
      |spatialFDerivL u (slabMk (y + w) s) (EuclideanSpace.single i 1) -
        spatialFDerivL u (slabMk y s) (EuclideanSpace.single i 1)| ≤
          ‖spatialSecondFDerivL u‖ * ‖w‖ := by
  refine ⟨(ContinuousLinearMap.abs_apply_single_le _ i).trans
    ((spatialFDerivL u).norm_coe_le_norm _), ?_⟩
  have h₁ := ContinuousLinearMap.abs_apply_single_le (spatialFDerivL u (slabMk (y + w) s) -
    spatialFDerivL u (slabMk y s)) i
  rw [_root_.sub_apply, ← dist_eq_norm] at h₁
  exact h₁.trans (dist_spatialFDerivL_slabMk_add_le u y w s)

/-- **The forcing of `δₕu - v` tends to zero uniformly.** With the hypotheses of
`euclideanParabolicOperatorL_smul_translateLIE_sub_sub_apply`, and derivatives of the coefficients
and the forcing along `e` in `C_b^{α,α/2}`, the forcing of `δₕu - v` is bounded by `K ‖h • e‖` for
a function `K` tending to zero at zero. -/
private theorem exists_tendsto_and_abs_euclideanParabolicOperatorL_smul_translateLIE_sub_sub_le
    (hα : α ≤ 1) (hα₀ : 0 < α)
    {a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
    {c c' f f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ} {e : EuclideanSpace ℝ ι}
    (ha' : ∀ i j (t : Icc t₀ t₁) x,
      HasLineDerivAt ℝ (fun y ↦ a i j (slabMk y t)) (a' i j (slabMk x t)) x e)
    (hb' : ∀ i (t : Icc t₀ t₁) x,
      HasLineDerivAt ℝ (fun y ↦ b i (slabMk y t)) (b' i (slabMk x t)) x e)
    (hc' : ∀ (t : Icc t₀ t₁) x, HasLineDerivAt ℝ (fun y ↦ c (slabMk y t)) (c' (slabMk x t)) x e)
    (hf' : ∀ (t : Icc t₀ t₁) x, HasLineDerivAt ℝ (fun y ↦ f (slabMk y t)) (f' (slabMk x t)) x e)
    {u v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht}
    (hu : euclideanParabolicOperatorL hα a b c u = f)
    (hv : euclideanParabolicOperatorL hα a b c v = f' + spatialOperatorL hα
      (euclideanSecondOrderCoeff a') (euclideanFirstOrderCoeff b')
        (euclideanZerothOrderCoeff c') u) :
    ∃ K : ℝ → ℝ, Tendsto K (𝓝 0) (𝓝 0) ∧ ∀ h : ℝ, h ≠ 0 → ∀ q,
      |euclideanParabolicOperatorL hα a b c (h⁻¹ • (translateLIE α ℝ ht (h • e) u - u) - v) q| ≤
        K ‖h • e‖ := by
  set N₂ := ‖spatialSecondFDerivL u‖
  set N₁ := ‖spatialFDerivL u‖
  set K : ℝ → ℝ := fun δ ↦ ‖f'‖ * δ ^ (α : ℝ) +
      ∑ i, ∑ j, (‖a' i j‖ * δ ^ (α : ℝ) * N₂ + ‖a' i j‖ * (N₂ * δ ^ (α : ℝ))) +
      ∑ i, (‖b' i‖ * δ ^ (α : ℝ) * N₁ + ‖b' i‖ * (N₂ * δ)) +
      (‖c'‖ * δ ^ (α : ℝ) * ‖valueL u‖ + ‖c'‖ * (N₁ * δ)) with hK
  refine ⟨K, ?_, fun h hh q ↦ ?_⟩
  · have : Continuous fun δ : ℝ ↦ δ ^ (α : ℝ) := Real.continuous_rpow_const α.property
    have hKc : Continuous K := by
      rw [hK]
      fun_prop
    simpa [hK, Real.zero_rpow (NNReal.coe_ne_zero.2 hα₀.ne')] using hKc.tendsto 0
  obtain ⟨y, s, rfl⟩ : ∃ y s, slabMk y s = q := ⟨_, _, slabMk_space_slabTime q⟩
  rw [euclideanParabolicOperatorL_smul_translateLIE_sub_sub_apply hα hu hv hh, abs_mul, abs_inv,
    inv_mul_le_iff₀ (abs_pos.2 hh)]
  have hD₀ := (valueL u).norm_coe_le_norm (slabMk (y + h • e) s)
  rw [Real.norm_eq_abs] at hD₀
  have key := add_le_add (add_le_add (add_le_add
    (abs_sub_sub_mul_le_of_hasLineDerivAt (hf' s) y h)
    (Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ Finset.sum_le_sum (s := Finset.univ)
      fun j _ ↦ abs_sub_mul_sub_mul_le_of_hasLineDerivAt (ha' i j s) (m := fun q ↦
          spatialSecondFDerivL u q (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        (abs_spatialSecondFDerivL_apply_le u y (h • e) s i j).1
        (abs_spatialSecondFDerivL_apply_le u y (h • e) s i j).2))
    (Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ abs_sub_mul_sub_mul_le_of_hasLineDerivAt
      (hb' i s) (m := fun q ↦ spatialFDerivL u q (EuclideanSpace.single i 1))
      (abs_spatialFDerivL_apply_le u y (h • e) s i).1
      (abs_spatialFDerivL_apply_le u y (h • e) s i).2))
    (abs_sub_mul_sub_mul_le_of_hasLineDerivAt (hc' s) (m := fun q ↦ u q) hD₀
      (dist_apply_slabMk_add_le u y (h • e) s))
  refine ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add le_rfl ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _))))
    (Finset.abs_sum_le_sum_abs _ _))) le_rfl)).trans (key.trans (le_of_eq ?_))
  simp only [hK, mul_add, Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- **The initial values of `δₕu - v` are `O(|h|)`.** If the derivative of the initial trace of
`u` along `e` is `g' ∈ C_b^{2,α}` and `v` has initial trace `g'`, then `δₕu - v` at the initial
time is bounded by `‖D g'‖ ‖h • e‖`. -/
private theorem abs_smul_translateLIE_sub_sub_apply_le
    {u v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht} {e : EuclideanSpace ℝ ι}
    {g' : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ}
    (hg' : ∀ x, spatialFDerivL u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) e = g' x)
    (hv : ∀ x, v (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) = g' x) {h : ℝ} (hh : h ≠ 0)
    (y : EuclideanSpace ℝ ι) :
    |(h⁻¹ • (translateLIE α ℝ ht (h • e) u - u) - v) (slabMk y ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤
      ‖g'.iteratedFDeriv 1‖ * ‖h • e‖ := by
  have h₁ := g'.lipschitzWith.holderWith.norm_sub_sub_smul_le_of_hasLineDerivAt
    (φ := fun z ↦ u (slabMk z ⟨t₀, left_mem_Icc.2 ht.le⟩))
    (fun z ↦ by simpa [hg'] using
      (u.hasSpatialFDerivAt ⟨t₀, left_mem_Icc.2 ht.le⟩ z).hasLineDerivAt e) y h
  simp only [Real.norm_eq_abs, smul_eq_mul, NNReal.coe_one, Real.rpow_one, coe_nnNorm] at h₁
  calc _ = |h⁻¹| * |u (slabMk (y + h • e) ⟨t₀, left_mem_Icc.2 ht.le⟩) -
        u (slabMk y ⟨t₀, left_mem_Icc.2 ht.le⟩) - h * g' y| := by
        rw [← abs_mul]
        simp only [sub_apply, smul_apply, translateLIE_apply, slabSpaceMap_slabMk,
          IsometryEquiv.addRight_apply, hv, smul_eq_mul]
        congr 1
        field_simp
    _ ≤ ‖g'.iteratedFDeriv 1‖ * ‖h • e‖ := by
        rw [abs_inv, inv_mul_le_iff₀ (abs_pos.2 hh)]
        linarith

/-- **The spatial derivative of a solution solves the differentiated Cauchy problem.** Let
`0 < α < 1`, let `aⁱʲ`, `bⁱ`, `c` be coefficients in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly
elliptic, and let `u ∈ C_b^{2+α,1+α/2}` solve `∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u = f`. Fix a
direction `e`, and suppose that `a`, `b`, `c` and `f` have derivatives `a'`, `b'`, `c'`, `f'`
along `e` in `C_b^{α,α/2}`, and that the derivative of the initial trace along `e` is
`g' ∈ C_b^{2,α}`. Then `∂ₑu` is the solution in `C_b^{2+α,1+α/2}` of the Cauchy problem
`P v = f' + a'ⁱʲ ∂ᵢ∂ⱼu + b'ⁱ ∂ᵢu + c' u`, `v(·, 0) = g'`. -/
theorem euclideanInitialDataCLE_symm_apply_eq_spatialFDerivL_apply {T : ℝ≥0} (hα₀ : 0 < α)
    (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    {a a' : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {b b' : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    {c c' f f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {e : EuclideanSpace ℝ ι}
    (ha' : ∀ i j (t : Icc (0 : ℝ) T) x,
      HasLineDerivAt ℝ (fun y ↦ a i j (slabMk y t)) (a' i j (slabMk x t)) x e)
    (hb' : ∀ i (t : Icc (0 : ℝ) T) x,
      HasLineDerivAt ℝ (fun y ↦ b i (slabMk y t)) (b' i (slabMk x t)) x e)
    (hc' : ∀ (t : Icc (0 : ℝ) T) x,
      HasLineDerivAt ℝ (fun y ↦ c (slabMk y t)) (c' (slabMk x t)) x e)
    (hf' : ∀ (t : Icc (0 : ℝ) T) x,
      HasLineDerivAt ℝ (fun y ↦ f (slabMk y t)) (f' (slabMk x t)) x e)
    {u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT}
    (hu : euclideanParabolicOperatorL hα₁.le a b c u = f)
    {g' : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ}
    (hg' : ∀ x, spatialFDerivL u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) e = g' x)
    (p : slab (E := EuclideanSpace ℝ ι) 0 T) :
    (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm
        (f' + spatialOperatorL hα₁.le (euclideanSecondOrderCoeff a') (euclideanFirstOrderCoeff b')
          (euclideanZerothOrderCoeff c') u, g') p =
      spatialFDerivL u p e := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  set v := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm
    (f' + spatialOperatorL hα₁.le (euclideanSecondOrderCoeff a') (euclideanFirstOrderCoeff b')
      (euclideanZerothOrderCoeff c') u, g')
  have hPv : euclideanParabolicOperatorL hα₁.le a b c v = f' + spatialOperatorL hα₁.le
      (euclideanSecondOrderCoeff a') (euclideanFirstOrderCoeff b')
        (euclideanZerothOrderCoeff c') u :=
    euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply _
  obtain ⟨K, hK, hPw⟩ :=
    exists_tendsto_and_abs_euclideanParabolicOperatorL_smul_translateLIE_sub_sub_le hα₁.le hα₀
      ha' hb' hc' hf' hu hPv
  have ⟨lam, hlam, hell⟩ := ha
  -- By the maximum principle, the difference quotients `δₕu` tend to `v` uniformly.
  have hmax (h : ℝ) (hh : h ≠ 0) : |(h⁻¹ • (translateLIE α ℝ hT (h • e) u - u) - v) (slabMk x t)| ≤
      Real.exp (‖c‖ * t) * (‖g'.iteratedFDeriv 1‖ * ‖h • e‖ + t * K ‖h • e‖) := by
    simpa using abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα₁.le
      (fun q ξ ↦ (mul_nonneg hlam.le (sq_nonneg _)).trans (hell q ξ))
      (fun q ↦ (le_abs_self _).trans (HolderSpace.norm_apply_le c q)) (norm_nonneg c) _
      (hPw h hh) (abs_smul_translateLIE_sub_sub_apply_le hg'
        (euclideanInitialDataCLE_symm_apply_slabMk_zero _) hh) (slabMk x t)
  have hδ : Tendsto (fun h : ℝ ↦ ‖h • e‖) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_id.smul continuous_const).norm.tendsto (0 : ℝ) :
      Tendsto (fun h : ℝ ↦ ‖h • e‖) _ _)
  have hlim : Tendsto (fun h : ℝ ↦
      Real.exp (‖c‖ * t) * (‖g'.iteratedFDeriv 1‖ * ‖h • e‖ + t * K ‖h • e‖)) (𝓝 0) (𝓝 0) := by
    simpa using ((hδ.const_mul _).add ((hK.comp hδ).const_mul (t : ℝ))).const_mul
      (Real.exp (‖c‖ * t))
  -- The difference quotients converge both to `v` and to the derivative of `u`.
  have h₁ : Tendsto (fun h : ℝ ↦ h⁻¹ • (u (slabMk (x + h • e) t) - u (slabMk x t))) (𝓝[≠] 0)
      (𝓝 (v (slabMk x t))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
      (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa [Real.norm_eq_abs] using hmax h hh
  exact tendsto_nhds_unique h₁
    ((u.hasSpatialFDerivAt t x).hasLineDerivAt e).tendsto_slope_zero

end Euclidean

end TauCeti.ParabolicC2HolderSpace
