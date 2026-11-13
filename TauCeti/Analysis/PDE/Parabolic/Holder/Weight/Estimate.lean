/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
public import TauCeti.Analysis.PDE.Parabolic.Holder.Weight.Backward

/-!
# A priori estimates in spatially weighted parabolic Hölder classes

On `ℝⁿ = EuclideanSpace ℝ ι` let `w = exp ∘ ℓ` be a positive time-independent weight whose
logarithm `ℓ` is `C²` with bounded `α`-Hölder first and second partial derivatives `∂ᵢℓ`,
`∂ᵢ∂ⱼℓ`; `ℓ` itself may be unbounded, so `w` may grow or decay exponentially at infinity. The
**weighted class** consists of the functions `u = w v` with `v` in the bounded order-two parabolic
Hölder space `C_b^{2+α,1+α/2}` on a slab. Such `u` are in general unbounded, so the theory of
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` in bounded spaces does not apply to them directly. By the
conjugation identity `P (w v) = w P_w v`
(`TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanParabolicOperatorL_eq`), where `P_w` has the
same principal coefficients and the bounded Hölder lower-order coefficients `b_w`, `c_w`, it does
apply to `v`. This file transports the a priori theory along this conjugation.

* **The Schauder estimate.** If `P u = w g` and `u = w v`, then
  `‖v‖_{2+α,par} ≤ C (‖g‖_{α,par} + ‖v(·, 0)‖_{2,α})`, that is
  `‖u / w‖_{2+α,par} ≤ C (‖P u / w‖_{α,par} + ‖u(·, 0) / w‖_{2,α})`. The constant depends only
  on the dimension, `α`, the ellipticity constants, a bound on the coefficient norms, a bound on
  the norms of `∂ᵢℓ` and `∂ᵢ∂ⱼℓ`, and a bound on the horizon.
* **The comparison bound in the weighted uniform norm.** For degenerate elliptic `a`, `c_w ≤ γ`
  and `0 ≤ γ`, `|P u| ≤ K w` and `|u(·, t₀)| ≤ M w` give
  `|u(x, t)| ≤ w(x) exp (γ (t - t₀)) (M + (t - t₀) K)`. The sign condition is on `c_w`, not on
  `c`: for `w = exp x` on the line and constant coefficients, `c_w = c + a + b`.
* **Uniqueness.** For degenerate elliptic `a`, with no sign condition on `c`, an element of the
  weighted class is determined by `P u` and `u(·, t₀)`. This is uniqueness for the Cauchy
  problem in the weighted class `w C_b^{2+α,1+α/2}`, whose elements grow at most like `w`, for
  weights such as `w = exp ⟨x⟩` with `⟨x⟩ = √(1 + ‖x‖²)`. Some growth restriction is necessary:
  Tychonoff constructed a nonzero solution of the heat equation with zero initial data. The
  weight `exp ‖x‖²` is not admissible here, since its logarithm has unbounded gradient and the
  conjugated coefficient `c_w` is then unbounded.
* **Time reversal.** The backward operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u`
  conjugates in the same way, `P_back (w v) = w P_back,w v`, with the same coefficients
  `b_w`, `c_w`, because `w` does not depend on time
  (`TauCeti.ParabolicC2HolderSpace.exp_mul_euclideanBackwardParabolicOperatorL_eq`). The
  terminal-value problem therefore has the same comparison bound, again under `c_w ≤ γ` and
  `0 ≤ γ` with `|P_back u| ≤ K w` and `|u(·, t₁)| ≤ M w`, and the same uniqueness in the weighted
  class.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_norm_le_of_eq_exp_mul`: the weighted Schauder estimate.
* `TauCeti.ParabolicC2HolderSpace.abs_le_exp_mul_exp_mul_mul_add_mul_of_eq_exp_mul`: the weighted
  comparison bound.
* `TauCeti.ParabolicC2HolderSpace.eq_of_eq_exp_mul`: uniqueness in the weighted class.
* `TauCeti.ParabolicC2HolderSpace.abs_le_exp_mul_exp_mul_mul_add_mul_of_eq_exp_mul_backward` and
  `TauCeti.ParabolicC2HolderSpace.eq_of_eq_exp_mul_backward`: the comparison bound and uniqueness
  for the terminal-value problem.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the substitution
  `u = w v` by a positive weight).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* A. N. Tychonoff, *Théorèmes d'unicité pour l'équation de la chaleur*, Mat. Sb. 42 (1935),
  199–216.
-/

public section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime Real
open scoped NNReal

variable {α : ℝ≥0} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The forward problem -/

section Forward

/-- **The Schauder estimate in a weighted class.** For `0 < α < 1`, ellipticity constants
`λ > 0` and `Λ`, a bound `K` on the Hölder norms of the coefficients, a bound `L` on the Hölder
norms of the partial derivatives `∂ᵢℓ` and `∂ᵢ∂ⱼℓ` of the logarithm of the weight, and a bound
`T₀` on the horizon, there is a constant `C` with the following property. On `ℝⁿ × [0, T]`,
`T ≤ T₀`, let `u = exp ℓ * v` with `v ∈ C_b^{2+α,1+α/2}`, and let `u` be a classical solution of
`P u = exp ℓ * g` with `g ∈ C_b^{α,α/2}`, where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. Then
`‖v‖_{2+α,par} ≤ C (‖g‖_{α,par} + ‖v(·, 0)‖_{2,α})`. -/
theorem exists_norm_le_of_eq_exp_mul (hα₀ : 0 < α) (hα₁ : α < 1) {lam Lam : ℝ} (hlam : 0 < lam)
    (K L T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
      ∀ (dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ)
        (d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ),
        (∀ i, ‖dℓ i‖ ≤ L) → (∀ i j, ‖d2ℓ i j‖ ≤ L) →
      ∀ ℓ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ 2 ℓ →
        (∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x) →
        (∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) = d2ℓ i j x) →
      ∀ (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT)
        (u : EuclideanSpace ℝ ι → ℝ → ℝ)
        (g : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ y (s : Icc (0 : ℝ) T), u y s = exp (ℓ y) * v (slabMk y s)) →
        (∀ x (t : Icc (0 : ℝ) T), derivWithin (u x) (Icc 0 T) t -
          (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
            c (slabMk x t) * u x t) = exp (ℓ x) * g (slabMk x t)) →
        ‖v‖ ≤ C * (‖g‖ + ‖v.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖) := by
  -- A bound `K'` on the norms of the conjugated coefficients `a`, `b_w` and `c_w`.
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ)
  set K' : ℝ := K + n * (2 * K * L) + n * (n * (K * (L + L * L))) + n * (K * L)
  have hb₀ : 0 ≤ n * (2 * K * L) := by positivity
  have hc₀ : 0 ≤ n * (n * (K * (L + L * L))) := by positivity
  have hd₀ : 0 ≤ n * (K * L) := by positivity
  obtain ⟨C, hC, hest⟩ := exists_norm_le_euclideanParabolicOperatorL (ι := ι) hα₀ hα₁
    (Lam := Lam) hlam K'.toNNReal T₀
  refine ⟨C, hC, fun T hT hTT₀ a b c ha ha' hak hbk hck dℓ d2ℓ hdk hd2k ℓ hℓ hdℓ hd2ℓ v u g hu
    hP ↦ ?_⟩
  have hK' : (K'.toNNReal : ℝ) = K' := Real.coe_toNNReal _ (by positivity)
  have ha'' : ∀ i j, ‖a i j‖ ≤ K'.toNNReal := fun i j ↦ by
    rw [hK']
    linarith [hak i j, hb₀, hc₀, hd₀]
  have hb' : ∀ i, ‖euclideanWeightedFirstOrderCoeff a b dℓ i‖ ≤ K'.toNNReal := fun i ↦ by
    rw [hK']
    linarith [norm_euclideanWeightedFirstOrderCoeff_le_of_le hak hbk hdk i, hc₀, hd₀]
  have hc' : ‖euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ‖ ≤ K'.toNNReal := by
    rw [hK']
    linarith [norm_euclideanWeightedZerothOrderCoeff_le_of_le hak hbk hck hdk hd2k, hb₀]
  -- The classical equation for `u` is the conjugated equation `P_w v = g` for `v`.
  have hPv := (euclideanParabolicOperatorL_weightedCoeff_eq_iff hα₁.le hℓ hdℓ hd2ℓ v hu g).2 hP
  have h := hest T hT hTT₀ a (euclideanWeightedFirstOrderCoeff a b dℓ)
    (euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha ha' ha'' hb' hc' v
  rwa [hPv] at h

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ}

include hα

/-- **The comparison bound in the weighted uniform norm.** Let `a` be degenerate elliptic and let
the conjugated zeroth-order coefficient satisfy `c_w ≤ γ` with `0 ≤ γ`. If `u = exp ℓ * v` with
`v ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` satisfies `|P u| ≤ K exp ℓ` and
`|u(·, t₀)| ≤ M exp ℓ`, then `|u(x, t)| ≤ exp (ℓ x) exp (γ (t - t₀)) (M + (t - t₀) K)`. -/
theorem abs_le_exp_mul_exp_mul_mul_add_mul_of_eq_exp_mul
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ p ≤ γ) (hγ : 0 ≤ γ)
    {M K : ℝ} (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (hP : ∀ x (t : Icc t₀ t₁), |derivWithin (u x) (Icc t₀ t₁) t -
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u x t)| ≤ K * exp (ℓ x))
    (hinit : ∀ x, |u x t₀| ≤ M * exp (ℓ x)) (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁) :
    |u x t| ≤ exp (ℓ x) * (exp (γ * (t - t₀)) * (M + (t - t₀) * K)) := by
  have h := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα ha hc hγ v
    (fun p ↦ by
      rw [← slabMk_space_slabTime p]
      have hp := hP (p : ParabolicSpaceTime _).space (slabTime p)
      rwa [← exp_mul_euclideanParabolicOperatorL_eq hα hℓ hdℓ hd2ℓ v hu, abs_mul,
        abs_of_pos (exp_pos _), mul_comm, mul_le_mul_iff_left₀ (exp_pos _)] at hp)
    (fun y ↦ by
      have hy := hinit y
      rwa [hu y ⟨t₀, left_mem_Icc.2 ht.le⟩, abs_mul, abs_of_pos (exp_pos _), mul_comm,
        mul_le_mul_iff_left₀ (exp_pos _)] at hy)
    (slabMk x t)
  rw [slabTime_slabMk] at h
  rw [hu x t, abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_mul_of_nonneg_left h (exp_pos _).le

/-- **Uniqueness in the weighted class.** Let `a` be degenerate elliptic. If `u₁ = exp ℓ * v₁`
and `u₂ = exp ℓ * v₂` with `v₁, v₂ ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` have the same
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` and the same initial values, then `v₁ = v₂`, so `u₁` and
`u₂` agree on `ℝⁿ × [t₀, t₁]`. No sign condition on `c` is needed. -/
theorem eq_of_eq_exp_mul
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hℓ : ContDiff ℝ 2 ℓ) (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    {v₁ v₂ : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht}
    {u₁ u₂ : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu₁ : ∀ y (s : Icc t₀ t₁), u₁ y s = exp (ℓ y) * v₁ (slabMk y s))
    (hu₂ : ∀ y (s : Icc t₀ t₁), u₂ y s = exp (ℓ y) * v₂ (slabMk y s))
    (hP : ∀ x (t : Icc t₀ t₁), derivWithin (u₁ x) (Icc t₀ t₁) t -
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u₁ y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u₁ y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u₁ x t) = derivWithin (u₂ x) (Icc t₀ t₁) t -
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u₂ y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u₂ y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u₂ x t))
    (hinit : ∀ x, u₁ x t₀ = u₂ x t₀) : v₁ = v₂ := by
  -- Both `v₁` and `v₂` solve the conjugated equation with the forcing `P_w v₁`.
  have h₁ := (euclideanParabolicOperatorL_weightedCoeff_eq_iff (a := a) (b := b) (c := c) hα hℓ
    hdℓ hd2ℓ v₁ hu₁ _).1 rfl
  have h₂ := (euclideanParabolicOperatorL_weightedCoeff_eq_iff hα hℓ hdℓ hd2ℓ v₂ hu₂ _).2
    fun x t ↦ (hP x t).symm.trans (h₁ x t)
  refine eq_of_euclideanParabolicOperatorL_eq hα ha h₂.symm fun y ↦ ?_
  have hy := hinit y
  rw [hu₁ y ⟨t₀, left_mem_Icc.2 ht.le⟩, hu₂ y ⟨t₀, left_mem_Icc.2 ht.le⟩] at hy
  exact mul_left_cancel₀ (exp_pos _).ne' hy

end Forward

/-! ### The terminal-value problem -/

section Backward

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {dℓ : ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ}
  {d2ℓ : ι → ι → HolderSpace α (EuclideanSpace ℝ ι) ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ}

include hα

/-- **The terminal-value comparison bound in the weighted uniform norm.** Let `a` be degenerate
elliptic and `c_w ≤ γ` with `0 ≤ γ`. If `u = exp ℓ * v` with `v ∈ C_b^{2+α,1+α/2}` on
`ℝⁿ × [t₀, t₁]` satisfies `|P_back u| ≤ K exp ℓ` and `|u(·, t₁)| ≤ M exp ℓ`, then
`|u(x, t)| ≤ exp (ℓ x) exp (γ (t₁ - t)) (M + (t₁ - t) K)`. -/
theorem abs_le_exp_mul_exp_mul_mul_add_mul_of_eq_exp_mul_backward
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ p ≤ γ) (hγ : 0 ≤ γ)
    {M K : ℝ} (hℓ : ContDiff ℝ 2 ℓ)
    (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    (v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht) {u : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu : ∀ y (s : Icc t₀ t₁), u y s = exp (ℓ y) * v (slabMk y s))
    (hP : ∀ x (t : Icc t₀ t₁), |derivWithin (u x) (Icc t₀ t₁) t +
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u x t)| ≤ K * exp (ℓ x))
    (hterm : ∀ x, |u x t₁| ≤ M * exp (ℓ x)) (x : EuclideanSpace ℝ ι) (t : Icc t₀ t₁) :
    |u x t| ≤ exp (ℓ x) * (exp (γ * (t₁ - t)) * (M + (t₁ - t) * K)) := by
  have h :=
    abs_le_exp_mul_mul_add_mul_of_abs_euclideanBackwardParabolicOperatorL_le hα ha hc hγ v
    (fun p ↦ by
      rw [← slabMk_space_slabTime p]
      have hp := hP (p : ParabolicSpaceTime _).space (slabTime p)
      rwa [← exp_mul_euclideanBackwardParabolicOperatorL_eq hα hℓ hdℓ hd2ℓ v hu, abs_mul,
        abs_of_pos (exp_pos _), mul_comm, mul_le_mul_iff_left₀ (exp_pos _)] at hp)
    (fun y ↦ by
      have hy := hterm y
      rwa [hu y ⟨t₁, right_mem_Icc.2 ht.le⟩, abs_mul, abs_of_pos (exp_pos _), mul_comm,
        mul_le_mul_iff_left₀ (exp_pos _)] at hy)
    (slabMk x t)
  rw [slabTime_slabMk] at h
  rw [hu x t, abs_mul, abs_of_pos (exp_pos _)]
  exact mul_le_mul_of_nonneg_left h (exp_pos _).le

/-- **Uniqueness for the terminal-value problem in the weighted class.** Let `a` be degenerate
elliptic. If `u₁ = exp ℓ * v₁` and `u₂ = exp ℓ * v₂` with `v₁, v₂ ∈ C_b^{2+α,1+α/2}` on
`ℝⁿ × [t₀, t₁]` have the same `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` and the same terminal
values, then `v₁ = v₂`, so `u₁` and `u₂` agree on `ℝⁿ × [t₀, t₁]`. -/
theorem eq_of_eq_exp_mul_backward
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hℓ : ContDiff ℝ 2 ℓ) (hdℓ : ∀ i x, fderiv ℝ ℓ x (EuclideanSpace.single i 1) = dℓ i x)
    (hd2ℓ : ∀ i j x, fderiv ℝ (fderiv ℝ ℓ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) = d2ℓ i j x)
    {v₁ v₂ : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht}
    {u₁ u₂ : EuclideanSpace ℝ ι → ℝ → ℝ}
    (hu₁ : ∀ y (s : Icc t₀ t₁), u₁ y s = exp (ℓ y) * v₁ (slabMk y s))
    (hu₂ : ∀ y (s : Icc t₀ t₁), u₂ y s = exp (ℓ y) * v₂ (slabMk y s))
    (hP : ∀ x (t : Icc t₀ t₁), derivWithin (u₁ x) (Icc t₀ t₁) t +
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u₁ y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u₁ y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u₁ x t) = derivWithin (u₂ x) (Icc t₀ t₁) t +
      (∑ i, ∑ j, a i j (slabMk x t) * fderiv ℝ (fderiv ℝ fun y ↦ u₂ y t) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        ∑ i, b i (slabMk x t) * fderiv ℝ (fun y ↦ u₂ y t) x (EuclideanSpace.single i 1) +
        c (slabMk x t) * u₂ x t))
    (hterm : ∀ x, u₁ x t₁ = u₂ x t₁) : v₁ = v₂ := by
  refine eq_of_euclideanBackwardParabolicOperatorL_eq hα
    (b := euclideanWeightedFirstOrderCoeff a b dℓ)
    (c := euclideanWeightedZerothOrderCoeff a b c dℓ d2ℓ) ha (HolderSpace.ext fun p ↦ ?_)
    fun y ↦ ?_
  · rw [← slabMk_space_slabTime p]
    have hp := hP (p : ParabolicSpaceTime _).space (slabTime p)
    rw [← exp_mul_euclideanBackwardParabolicOperatorL_eq hα hℓ hdℓ hd2ℓ v₁ hu₁,
      ← exp_mul_euclideanBackwardParabolicOperatorL_eq hα hℓ hdℓ hd2ℓ v₂ hu₂] at hp
    exact mul_left_cancel₀ (exp_pos _).ne' hp
  · have hy := hterm y
    rw [hu₁ y ⟨t₁, right_mem_Icc.2 ht.le⟩, hu₂ y ⟨t₁, right_mem_Icc.2 ht.le⟩] at hy
    exact mul_left_cancel₀ (exp_pos _).ne' hy

end Backward

end TauCeti.ParabolicC2HolderSpace
