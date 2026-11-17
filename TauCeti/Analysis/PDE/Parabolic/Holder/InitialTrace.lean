/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.PDE.HeatKernel.ModulusOfContinuity
import TauCeti.Analysis.Holder.MeanValue

/-!
# The rate of attainment of the initial trace

Let `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` on the slab `ℝⁿ × [t₀, t₁]`, with degenerate elliptic
Hölder coefficients bounded by `∑ᵢⱼ |aⁱʲ| ≤ Λ`, `∑ᵢ |bⁱ| ≤ β` and `|c| ≤ γ`. This file shows that
an element `u` of `C_b^{2+α,1+α/2}` attains its initial trace `g = u(·, t₀)` at a rate governed
only by the modulus of continuity of `g`, by `‖P u‖_∞` and by `‖g‖_∞`: if `|P u| ≤ K`, `|g| ≤ M`
and `g` moves by at most `η` over distances at most `√s`, where `s = t - t₀`, then

`|u(x, t) - g(x)| ≤ exp (γ s) (C (2 + Λ + β √s) η + s (K + γ M))`

(`TauCeti.ParabolicC2HolderSpace.exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le`), where
`C` depends only on the dimension. No Hölder norm of `g` or of the coefficients enters, so the
estimate is uniform over every family of solutions whose initial traces share a modulus of
continuity `ω`: taking `η = ω(√s)`,

`‖u(·, t₀ + s) - g‖_∞ ≤ C' (ω(√s) + s (‖g‖_∞ + ‖P u‖_∞))`.

In particular, for a uniformly bounded family of solutions with uniformly bounded `P u` whose
initial traces are uniformly equicontinuous, `u(·, t) → u(·, t₀)` uniformly in the family as
`t → t₀` (`TauCeti.ParabolicC2HolderSpace.exists_forall_abs_sub_lt_of_uniformEquicontinuous`).
Since the bound involves only supremum norms and the modulus of continuity of the trace, it passes
to uniform limits of such solutions, as needed for initial data that are merely bounded and
uniformly continuous.

## The argument

Regularize the trace at the time scale of the target time, `G = K_s ⋆ g`. By the heat-kernel
estimates of `TauCeti.Analysis.PDE.HeatKernel.ModulusOfContinuity`, `|G - g| ≤ C η`,
`‖DG‖ ≤ C η s^(-1/2)` and `‖D²G‖ ≤ C η s⁻¹`. The time-independent extension of `G`
(`TauCeti.ParabolicC2HolderSpace.compSlabSpaceL`) has `|P G| ≤ Λ ‖D²G‖ + β ‖DG‖ + γ M`, so
`w = u - G` has initial values at most `C η` and `|P w| ≤ K + C η (Λ s⁻¹ + β s^(-1/2)) + γ M`.
The comparison principle
(`ParabolicC2HolderSpace.abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le`)
bounds `|w|` at time `t₀ + s`, and the factor `s` in front of `|P w|` turns `s⁻¹` and `s^(-1/2)`
into `1` and `√s`.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le`: the
  rate of attainment of the initial trace.
* `TauCeti.ParabolicC2HolderSpace.exists_forall_abs_sub_lt_of_uniformEquicontinuous`: uniform
  attainment for families with uniformly equicontinuous initial traces.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004), Chapter 4.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, Section 8.1
  (the Cauchy problem with continuous initial data).
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open MeasureTheory Real Set ParabolicSpaceTime
open scoped Convolution NNReal ContDiff

/-! ### Heat regularization as a bounded `C^{2,α}` map -/

section Regularization

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For `t > 0`, the heat regularization `K_t ⋆ g` of a bounded `g`, as a bounded `C^{2,α}` map:
its derivatives of every order are bounded, and its Hessian is `α`-Hölder because its third
derivative is bounded. -/
private def regularization (hα : α ≤ 1) {g : E → ℝ} {M t : ℝ} (hM : ∀ y, ‖g y‖ ≤ M)
    (ht : 0 < t) : CkHolderSpace 2 α E ℝ :=
  CkHolderSpace.ofContDiff (heatKernel t ⋆ g)
    (contDiff_infty.1 (contDiff_heatKernel_convolution ht (ae_of_all _ hM)) 2)
    (fun i _ ↦ ⟨_, norm_iteratedFDeriv_heatKernel_convolution_le ht (ae_of_all _ hM) i⟩)
    (holderWith_of_norm_le_of_norm_fderiv_le hα
      ((contDiff_infty.1 (contDiff_heatKernel_convolution ht (ae_of_all _ hM)) 3)
        |>.differentiable_iteratedFDeriv (by norm_num))
      (fun x ↦ (norm_iteratedFDeriv_heatKernel_convolution_le ht (ae_of_all _ hM) 2 x).trans
        (le_coe_toNNReal _))
      (fun x ↦ by
        rw [norm_fderiv_iteratedFDeriv]
        exact (norm_iteratedFDeriv_heatKernel_convolution_le ht (ae_of_all _ hM) 3 x).trans
          (le_coe_toNNReal _))).memHolder

private theorem coe_regularization (hα : α ≤ 1) {g : E → ℝ} {M t : ℝ} (hM : ∀ y, ‖g y‖ ≤ M)
    (ht : 0 < t) : ⇑(regularization hα hM ht) = heatKernel t ⋆ g :=
  CkHolderSpace.coe_ofContDiff ..

end Regularization

/-! ### The rate of attainment -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ℝ≥0} {t₀ t₁ : ℝ} {ht : t₀ < t₁}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ} {Λ β γ : ℝ}

/-- On a time-independent map `G`, the operator `P` reduces to `-(aⁱʲ ∂ᵢ∂ⱼG + bⁱ ∂ᵢG + c G)`, which
is bounded by `Λ ‖D²G‖ + β ‖DG‖ + γ |G|` under the coefficient bounds
`∑ᵢⱼ |aⁱʲ| ≤ Λ`, `∑ᵢ |bⁱ| ≤ β` and `|c| ≤ γ`. -/
private theorem abs_euclideanParabolicOperatorL_compSlabSpaceL_le (hα : α ≤ 1)
    (hΛ : ∀ p, ∑ i, ∑ j, |a i j p| ≤ Λ) (hβ : ∀ p, ∑ i, |b i p| ≤ β) (hγ : ∀ p, |c p| ≤ γ)
    (G : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    |euclideanParabolicOperatorL (ht := ht) hα a b c (compSlabSpaceL G) p| ≤
      Λ * ‖fderiv ℝ (fderiv ℝ G) (p : ParabolicSpaceTime _).space‖ +
        β * ‖fderiv ℝ G (p : ParabolicSpaceTime _).space‖ +
          γ * |G (p : ParabolicSpaceTime _).space| := by
  set x := (p : ParabolicSpaceTime (EuclideanSpace ℝ ι)).space
  set H := fderiv ℝ (fderiv ℝ G) x
  set L := fderiv ℝ G x
  have hH : ∀ i j, |H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ ‖H‖ :=
    fun i j ↦ by
      simpa using H.le_opNorm₂ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1)
  have hL : ∀ i, |L (EuclideanSpace.single i 1)| ≤ ‖L‖ := fun i ↦ by
    simpa using L.le_opNorm (EuclideanSpace.single i (1 : ℝ))
  have h₂ : |∑ i, ∑ j, a i j p * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
      Λ * ‖H‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, ∑ j, |a i j p * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)|
        ≤ ∑ i, ∑ j, |a i j p| * ‖H‖ := Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hH i j) (abs_nonneg _)
      _ = (∑ i, ∑ j, |a i j p|) * ‖H‖ := by simp only [Finset.sum_mul]
      _ ≤ Λ * ‖H‖ := mul_le_mul_of_nonneg_right (hΛ p) (norm_nonneg H)
  have h₁ : |∑ i, b i p * L (EuclideanSpace.single i 1)| ≤ β * ‖L‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |b i p * L (EuclideanSpace.single i 1)| ≤ ∑ i, |b i p| * ‖L‖ :=
          Finset.sum_le_sum fun i _ ↦ by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hL i) (abs_nonneg _)
      _ = (∑ i, |b i p|) * ‖L‖ := by rw [Finset.sum_mul]
      _ ≤ β * ‖L‖ := mul_le_mul_of_nonneg_right (hβ p) (norm_nonneg L)
  have h₀ : |c p * G x| ≤ γ * |G x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hγ p) (abs_nonneg _)
  simp only [euclideanParabolicOperatorL_apply, timeDerivL_compSlabSpaceL,
    HolderSpace.zero_apply, spatialSecondFDerivL_compSlabSpaceL, spatialFDerivL_compSlabSpaceL,
    compSlabSpaceL_apply, zero_sub, abs_neg]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₂ h₁)) h₀)

omit [DecidableEq ι] in
/-- The coefficient bounds are nonnegative as soon as the slab has a point. -/
private theorem nonneg_of_abs_le (hΛ : ∀ p, ∑ i, ∑ j, |a i j p| ≤ Λ)
    (hβ : ∀ p, ∑ i, |b i p| ≤ β) (hγ : ∀ p, |c p| ≤ γ)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) : 0 ≤ Λ ∧ 0 ≤ β ∧ 0 ≤ γ :=
  ⟨(Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _).trans (hΛ p),
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _).trans (hβ p), (abs_nonneg _).trans (hγ p)⟩

/-- **Comparison with a time-independent approximant.** If `G` is within `A₀` of the initial trace
of `u`, with `‖DG‖ ≤ A₁`, `‖D²G‖ ≤ A₂` and `|G| ≤ M`, then `u(x, t)` stays within
`exp (γ s) (A₀ + s (K + Λ A₂ + β A₁ + γ M)) + A₀` of `u(x, t₀)`, where `s = t - t₀`. -/
private theorem abs_sub_le_of_compSlabSpaceL (hα : α ≤ 1)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hΛ : ∀ p, ∑ i, ∑ j, |a i j p| ≤ Λ) (hβ : ∀ p, ∑ i, |b i p| ≤ β) (hγ : ∀ p, |c p| ≤ γ)
    {K M : ℝ} (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ p, |euclideanParabolicOperatorL hα a b c u p| ≤ K)
    (G : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ) {A₀ A₁ A₂ : ℝ}
    (h₀ : ∀ x, |G x - u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ A₀)
    (h₁ : ∀ x, ‖fderiv ℝ G x‖ ≤ A₁) (h₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ A₂)
    (hGM : ∀ x, |G x| ≤ M) (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    |u p - u (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤
      exp (γ * (slabTime p - t₀)) * (A₀ + (slabTime p - t₀) * (K + Λ * A₂ + β * A₁ + γ * M)) +
        A₀ := by
  obtain ⟨hΛ0, hβ0, hγ0⟩ := nonneg_of_abs_le hΛ hβ hγ p
  set w := u - compSlabSpaceL G
  have hPw : ∀ q, |euclideanParabolicOperatorL hα a b c w q| ≤ K + Λ * A₂ + β * A₁ + γ * M := by
    intro q
    rw [map_sub, HolderSpace.sub_apply]
    refine (abs_sub _ _).trans ?_
    have hG := abs_euclideanParabolicOperatorL_compSlabSpaceL_le (ht := ht) hα hΛ hβ hγ G q
    have := hP q
    have := mul_le_mul_of_nonneg_left (h₂ (q : ParabolicSpaceTime _).space) hΛ0
    have := mul_le_mul_of_nonneg_left (h₁ (q : ParabolicSpaceTime _).space) hβ0
    have := mul_le_mul_of_nonneg_left (hGM (q : ParabolicSpaceTime _).space) hγ0
    linarith
  have hw0 : ∀ x, |w (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ A₀ := fun x ↦ by
    rw [sub_apply, compSlabSpaceL_apply, space_slabMk, abs_sub_comm]
    exact h₀ x
  have key := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα ha
    (fun q ↦ (le_abs_self _).trans (hγ q)) hγ0 w hPw hw0 p
  have hsplit : u p - u (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩) =
      w p + (G (p : ParabolicSpaceTime _).space -
        u (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩)) := by
    rw [sub_apply, compSlabSpaceL_apply]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add key (h₀ _))

/-- At a time `t = t₀ + s` with `s > 0`, comparing `u` with the heat regularization `K_s ⋆ g` of its
initial trace `g`, where `g` moves by at most `η` over distances at most `√s`, gives
`|u(x, t) - g(x)| ≤ exp (γ s) (C₀ η + s (K + γ M) + Λ C₂ η + β C₁ η √s) + C₀ η`, with
`C₀ = 1 + M₁` and the constants `C₁`, `C₂` of the derivative bounds for the regularization. -/
private theorem abs_sub_le_of_dist_le_of_pos (hα : α ≤ 1)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    (hΛ : ∀ p, ∑ i, ∑ j, |a i j p| ≤ Λ) (hβ : ∀ p, ∑ i, |b i p| ≤ β) (hγ : ∀ p, |c p| ≤ γ)
    {K M η C₁ C₂ : ℝ} (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hC₁ : ∀ {g : EuclideanSpace ℝ ι → ℝ} {M t η : ℝ}, AEStronglyMeasurable g →
      (∀ᵐ y, ‖g y‖ ≤ M) → 0 < t → (∀ x y, dist x y ≤ √t → dist (g x) (g y) ≤ η) → ∀ x,
        ‖iteratedFDeriv ℝ 1 (heatKernel t ⋆ g) x‖ ≤ C₁ * η * t ^ (-((1 : ℕ) : ℝ) / 2))
    (hC₂ : ∀ {g : EuclideanSpace ℝ ι → ℝ} {M t η : ℝ}, AEStronglyMeasurable g →
      (∀ᵐ y, ‖g y‖ ≤ M) → 0 < t → (∀ x y, dist x y ≤ √t → dist (g x) (g y) ≤ η) → ∀ x,
        ‖iteratedFDeriv ℝ 2 (heatKernel t ⋆ g) x‖ ≤ C₂ * η * t ^ (-((2 : ℕ) : ℝ) / 2))
    (hP : ∀ p, |euclideanParabolicOperatorL hα a b c u p| ≤ K)
    (hM : ∀ x, |u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ M)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) (hs : 0 < (slabTime p : ℝ) - t₀)
    (hη : ∀ x y, dist x y ≤ √(slabTime p - t₀) →
      |u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) - u (slabMk y ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ η) :
    |u p - u (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤
      exp (γ * (slabTime p - t₀)) * ((1 + heatKernelMoment (EuclideanSpace ℝ ι) 1) * η +
        ((slabTime p - t₀) * (K + γ * M) + Λ * C₂ * η + β * C₁ * η * √(slabTime p - t₀))) +
        (1 + heatKernelMoment (EuclideanSpace ℝ ι) 1) * η := by
  set s : ℝ := slabTime p - t₀
  set g : EuclideanSpace ℝ ι → ℝ := fun x ↦ u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)
  have hgc : Continuous g := (valueL u).continuous.comp (continuous_slabMk.comp
    (continuous_id.prodMk continuous_const))
  have hgM : ∀ y, ‖g y‖ ≤ M := fun y ↦ by rw [Real.norm_eq_abs]; exact hM y
  have hgη : ∀ x y, dist x y ≤ √s → dist (g x) (g y) ≤ η := fun x y h ↦ by
    rw [Real.dist_eq]; exact hη x y h
  set G := regularization hα hgM hs
  have hG : ⇑G = heatKernel s ⋆ g := coe_regularization hα hgM hs
  have hGc : ⇑G = heatCauchyPotential g s := by
    rw [hG, heatCauchyPotential_eq_convolution_fun g hs]
  have key := abs_sub_le_of_compSlabSpaceL hα ha hΛ hβ hγ u hP G
    (fun x ↦ by
      rw [hGc, ← Real.norm_eq_abs]
      exact norm_heatCauchyPotential_sub_le_of_dist_le hgc hgM hs hgη x)
    (fun x ↦ by
      rw [← norm_iteratedFDeriv_one, hG]
      exact hC₁ hgc.aestronglyMeasurable (ae_of_all _ hgM) hs hgη x)
    (fun x ↦ by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv, hG]
      exact hC₂ hgc.aestronglyMeasurable (ae_of_all _ hgM) hs hgη x)
    (fun x ↦ by
      rw [hGc, ← Real.norm_eq_abs]
      exact norm_heatCauchyPotential_le hgM _ x) p
  -- The factor `s` cancels the negative powers `s⁻¹` and `s^(-1/2)` of the derivative bounds.
  have e₁ : s ^ (-((1 : ℕ) : ℝ) / 2) = (√s)⁻¹ := by
    rw [sqrt_eq_rpow, ← rpow_neg hs.le]; norm_num
  have e₂ : s ^ (-((2 : ℕ) : ℝ) / 2) = s⁻¹ := by
    rw [← rpow_neg_one]; norm_num
  have hsq : s * (√s)⁻¹ = √s := by rw [← div_eq_mul_inv, div_sqrt]
  have hss : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
  have hexpand : s * (K + Λ * (C₂ * η * s⁻¹) + β * (C₁ * η * (√s)⁻¹) + γ * M) =
      s * (K + γ * M) + Λ * C₂ * η + β * C₁ * η * √s := by
    linear_combination (Λ * C₂ * η) * hss + (β * C₁ * η) * hsq
  rwa [e₁, e₂, hexpand] at key

/-- **The rate of attainment of the initial trace.** There is a constant `C`, depending only on
the dimension, with the following property. Let `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` have
degenerate elliptic Hölder coefficients on the slab `ℝⁿ × [t₀, t₁]` with `∑ᵢⱼ |aⁱʲ| ≤ Λ`,
`∑ᵢ |bⁱ| ≤ β` and `|c| ≤ γ`, and let `u ∈ C_b^{2+α,1+α/2}` satisfy `|P u| ≤ K` and `|u(·, t₀)| ≤ M`.
If, at a point `(x, t)` of the slab with `s = t - t₀`, the initial trace `u(·, t₀)` moves by at
most `η` over distances at most `√s`, then

`|u(x, t) - u(x, t₀)| ≤ exp (γ s) (C (2 + Λ + β √s) η + s (K + γ M))`.

No Hölder norm of the trace or of the coefficients enters the bound. -/
theorem exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le :
    ∃ C ≥ 0, ∀ {t₀ t₁ : ℝ} {ht : t₀ < t₁} {α : ℝ≥0} (hα : α ≤ 1)
      {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
      {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
      {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ} {Λ β γ K M η : ℝ}
      (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht),
      (∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
      (∀ p, ∑ i, ∑ j, |a i j p| ≤ Λ) → (∀ p, ∑ i, |b i p| ≤ β) → (∀ p, |c p| ≤ γ) →
      (∀ p, |euclideanParabolicOperatorL hα a b c u p| ≤ K) →
      (∀ x, |u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ M) →
      ∀ p : slab (E := EuclideanSpace ℝ ι) t₀ t₁, (∀ x y, dist x y ≤ √(slabTime p - t₀) →
        |u (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) - u (slabMk y ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤
          η) →
        |u p - u (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤
          exp (γ * (slabTime p - t₀)) *
            (C * (2 + Λ + β * √(slabTime p - t₀)) * η + (slabTime p - t₀) * (K + γ * M)) := by
  obtain ⟨C₁, -, hC₁⟩ := exists_norm_iteratedFDeriv_heatKernel_convolution_le_of_dist_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) one_ne_zero
  obtain ⟨C₂, -, hC₂⟩ := exists_norm_iteratedFDeriv_heatKernel_convolution_le_of_dist_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) two_ne_zero
  set C₀ : ℝ := 1 + heatKernelMoment (EuclideanSpace ℝ ι) 1
  set C := max C₀ (max C₁ C₂)
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨C, le_max_of_le_left hC₀0, ?_⟩
  intro t₀ t₁ ht α hα a b c Λ β γ K M η u ha hΛ hβ hγ hP hM p hη
  obtain ⟨hΛ0, hβ0, hγ0⟩ := nonneg_of_abs_le hΛ hβ hγ p
  have hη0 : 0 ≤ η := by simpa using hη 0 0 (by simp)
  set s : ℝ := slabTime p - t₀
  have hs0 : 0 ≤ s := sub_nonneg.2 (slabTime p).2.1
  rcases hs0.eq_or_lt with hs | hs
  · -- At the initial time the left side vanishes and the right side is nonnegative.
    have hp : slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩ = p := by
      conv_rhs => rw [← slabMk_space_slabTime p]
      congr 1
      exact Subtype.ext (by linarith)
    rw [hp, sub_self, abs_zero, ← hs]
    have : 0 ≤ C * (2 + Λ + β * √0) * η := by positivity
    simp only [zero_mul, add_zero]
    positivity
  · refine (abs_sub_le_of_dist_le_of_pos hα ha hΛ hβ hγ u hC₁ hC₂ hP hM p hs hη).trans ?_
    have hE := (exp_pos (γ * s)).le
    have h₀ : C₀ * η ≤ exp (γ * s) * (C₀ * η) :=
      le_mul_of_one_le_left (by positivity) (one_le_exp (by positivity))
    have h₁ : Λ * C₂ * η ≤ Λ * C * η := by
      gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
    have h₂ : β * C₁ * η * √s ≤ β * C * η * √s := by
      gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
    have h₃ : C₀ * η ≤ C * η := by gcongr; exact le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_left h₁ hE, mul_le_mul_of_nonneg_left h₂ hE,
      mul_le_mul_of_nonneg_left h₃ hE]

omit [DecidableEq ι] in
/-- The Hölder norms of the coefficients bound them pointwise. -/
private theorem abs_le_norm_coeff
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ) :
    (∀ p, ∑ i, ∑ j, |a i j p| ≤ ∑ i, ∑ j, ‖a i j‖) ∧ (∀ p, ∑ i, |b i p| ≤ ∑ i, ‖b i‖) ∧
      ∀ p, |c p| ≤ ‖c‖ :=
  ⟨fun p ↦ Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ by
      simpa using HolderSpace.norm_apply_le (a i j) p,
    fun p ↦ Finset.sum_le_sum fun i _ ↦ by simpa using HolderSpace.norm_apply_le (b i) p,
    fun p ↦ by simpa using HolderSpace.norm_apply_le c p⟩

/-- `X ε / (2 (X + 1)) < ε / 2` for `X ≥ 0` and `ε > 0`. -/
private theorem mul_div_two_mul_add_one_lt {ε : ℝ} (hε : 0 < ε) (X : ℝ) (hX : 0 ≤ X) :
    X * (ε / (2 * (X + 1))) < ε / 2 := by
  have hX1 : X / (X + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  calc X * (ε / (2 * (X + 1))) = ε / 2 * (X / (X + 1)) := by field_simp
    _ < ε / 2 * 1 := mul_lt_mul_of_pos_left hX1 (by positivity)
    _ = ε / 2 := mul_one _

/-- **Uniform attainment for equicontinuous families.** Let `P` have degenerate elliptic Hölder
coefficients on the slab `ℝⁿ × [t₀, t₁]`, and let `(u_k)` be a family in `C_b^{2+α,1+α/2}` with
`|P u_k| ≤ K` and `|u_k(·, t₀)| ≤ M`, whose initial traces `u_k(·, t₀)` are uniformly
equicontinuous. Then `u_k(x, t) → u_k(x, t₀)` as `t → t₀`, uniformly in `k` and `x`. -/
theorem exists_forall_abs_sub_lt_of_uniformEquicontinuous (hα : α ≤ 1)
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {κ : Type*} {K M : ℝ} (u : κ → ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ k p, |euclideanParabolicOperatorL hα a b c (u k) p| ≤ K)
    (hM : ∀ k x, |u k (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩)| ≤ M)
    (hu : UniformEquicontinuous fun k x ↦ u k (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ k (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁), (slabTime p : ℝ) - t₀ < δ →
      |u k p - u k (slabMk (p : ParabolicSpaceTime _).space ⟨t₀, left_mem_Icc.2 ht.le⟩)| < ε := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sub_le_of_abs_euclideanParabolicOperatorL_le (ι := ι)
  obtain ⟨hΛ, hβ, hγ⟩ := abs_le_norm_coeff a b c
  set Λ := ∑ i, ∑ j, ‖a i j‖
  set β := ∑ i, ‖b i‖
  set T := t₁ - t₀
  set B := exp (‖c‖ * T)
  set D := C * (2 + Λ + β * √T) with hD_def
  set R := B * |K + ‖c‖ * M|
  have hB : 0 < B := exp_pos _
  set η := ε / (2 * (B * D + 1))
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁η⟩ := Metric.uniformEquicontinuous_iff.1 hu η hη
  refine ⟨min (δ₁ ^ 2) (ε / (2 * (R + 1))), by positivity, fun k p hp ↦ ?_⟩
  set s : ℝ := slabTime p - t₀
  have hs0 : 0 ≤ s := sub_nonneg.2 (slabTime p).2.1
  have hsT : s ≤ T := sub_le_sub_right (slabTime p).2.2 _
  have hsδ : √s < δ₁ := by
    rw [← sqrt_sq hδ₁.le]
    exact sqrt_lt_sqrt hs0 (hp.trans_le (min_le_left _ _))
  have key := hC hα (u k) ha hΛ hβ hγ (hP k) (hM k) p fun x y hxy ↦ by
    simpa [Real.dist_eq] using (hδ₁η x y (hxy.trans_lt hsδ) k).le
  refine key.trans_lt ?_
  have hKM : 0 ≤ K + ‖c‖ * M := add_nonneg ((abs_nonneg _).trans (hP k p))
    (mul_nonneg (norm_nonneg c) ((abs_nonneg _).trans (hM k 0)))
  have hE : exp (‖c‖ * s) ≤ B := exp_le_exp.2 (mul_le_mul_of_nonneg_left hsT (norm_nonneg c))
  have hDs : C * (2 + Λ + β * √s) ≤ D := by
    have : √s ≤ √T := sqrt_le_sqrt hsT
    rw [hD_def]
    gcongr
  have hin : C * (2 + Λ + β * √s) * η + s * (K + ‖c‖ * M) ≤ D * η + s * |K + ‖c‖ * M| := by
    rw [abs_of_nonneg hKM]
    gcongr
  have hRs : R * s ≤ R * (ε / (2 * (R + 1))) :=
    mul_le_mul_of_nonneg_left (hp.le.trans (min_le_right _ _)) (by positivity)
  -- Each of the two terms is less than `ε / 2`.
  have h₁ := mul_div_two_mul_add_one_lt hε (B * D) (by positivity)
  have h₂ := mul_div_two_mul_add_one_lt hε R (by positivity)
  calc exp (‖c‖ * s) * (C * (2 + Λ + β * √s) * η + s * (K + ‖c‖ * M))
      ≤ B * (D * η + s * |K + ‖c‖ * M|) :=
        mul_le_mul hE hin (by positivity) hB.le
    _ = B * D * η + R * s := by ring
    _ < ε := by linarith

end Euclidean

end TauCeti.ParabolicC2HolderSpace
