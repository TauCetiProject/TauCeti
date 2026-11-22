/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Schauder
public import TauCeti.Analysis.PDE.Parabolic.Holder.Restriction

/-!
# Parabolic Schauder estimates at positive times

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in the bounded parabolic Hölder space `C_b^{α,α/2}`, with `0 < α < 1`, and let
`a` be uniformly elliptic. The global Schauder estimate bounds the norm of `u` in the order-two
space `C_b^{2+α,1+α/2}` by `‖P u‖_{α,par}` and the `C^{2,α}` norm of the initial values `u(·, 0)`.
Away from the initial time no regularity of the initial values is needed: there is a constant `C`,
depending only on `n`, `α`, the ellipticity constants, a bound on the Hölder norms of the
coefficients and a bound on the horizon, such that for every `0 < δ < T`

`δ^(1 + α/2) ‖u‖_{2+α,par;[δ,T]} ≤ C (‖P u‖_{α,par} + ‖u(·, 0)‖_∞)`,

where `‖u‖_{2+α,par;[δ,T]}` is the order-two norm of the restriction of `u` to `ℝⁿ × [δ, T]`
(`TauCeti.ParabolicC2HolderSpace.exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL`).
The weight `δ^(1 + α/2)` is the parabolic scaling of the top-order Hölder seminorms. The constant
is uniform in `u` and only the supremum of the initial values enters, as needed to pass to limits
of smooth approximations of bounded uniformly continuous initial data at positive times
(`TauCeti.ParabolicC2HolderSpace.exists_rpow_mul_norm_euclideanCauchySolutionBUCRestrictL_le`).

## The argument

Fix a scale `s` with `2 s < T` and a time cutoff `χ` vanishing up to time `s` and equal to one
from time `2 s` on (`TauCeti.ParabolicC2HolderSpace.exists_timeCutoff`). The map `χ u` vanishes
at the initial time and `P (χ u) = χ P u + (∂ₜχ) u`
(`TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_mul_eq_of_spatialFDerivL_eq_zero`), so the
global Schauder estimate bounds `‖u‖_{2+α,par;[2s,T]}` by `‖χ P u‖ + ‖(∂ₜχ) u‖`. The derivative
`∂ₜχ` vanishes before time `s`, has size `s⁻¹` and seminorm `s^(-(1 + α/2))`, so
`‖(∂ₜχ) u‖ ≲ s⁻¹ ‖u‖_{α,par;[s,T]} + s^(-(1 + α/2)) ‖u‖_∞`. The interpolation inequality at the
time step `η s` (`TauCeti.ParabolicC2HolderSpace.norm_valueHolderL_le`) bounds
`‖u‖_{α,par;[s,T]}` by `2 η s ‖u‖_{2+α,par;[s,T]}` plus a multiple of `‖u‖_∞`. After
multiplication by `(2 s)^(1 + α/2)`, the weighted norm at the scale `2 s` is therefore at most a
multiple of `η` times the weighted norm at the scale `s`, plus a multiple of
`‖P u‖_{α,par} + ‖u‖_∞`. For `η` small, the supremum over all scales, which is finite for `u` in
the closed-slab space, absorbs the first term. Finally the comparison principle bounds `‖u‖_∞`
by `‖u(·, 0)‖_∞` and `‖P u‖_∞`.

## Main declarations

All declarations are in the `TauCeti.ParabolicC2HolderSpace` namespace.

* `exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL_add_norm_valueL`: the weighted
  estimate with `‖u‖_∞` on the right.
* `exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL`: the weighted estimate with the
  supremum of the initial values on the right.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Prentice-Hall, 1964, Chapter 3
  (Schauder estimates with weights vanishing at the boundary of the domain).
* A. Lunardi, *Analytic semigroups and optimal regularity in parabolic problems*, Birkhäuser,
  1995, Chapter 5 (Hölder estimates with weights in time near `t = 0`).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Metric ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section TimeCutoff

variable {a b : ℝ} {hab : a < b}

-- Reuse the operator module's Hessian shortcuts for instance search in coefficient types.
attribute [local instance] instNormedAddCommGroupContinuousLinearMapRealId
  instNormedSpaceRealContinuousLinearMapId

/-- **Products with a factor vanishing before time `s`.** If `g` vanishes before time `s` and
`|g| ≤ G`, then `‖g u‖_{α,par} ≤ G ‖u‖_{α,par;[s,b]} + [g]_{α,par} ‖u‖_∞`: the value of `u`
enters through its parabolic Hölder norm on `E × [s, b]` only. -/
private theorem norm_mul_valueHolderL_le (hα : α ≤ 1) (g : HolderSpace α (slab (E := E) a b) ℝ)
    (u : ParabolicC2HolderSpace α E ℝ hab) {s G : ℝ} (has : a ≤ s) (hsb : s < b)
    (hg : ∀ p : slab (E := E) a b, (p : ParabolicSpaceTime E).time < s → g p = 0)
    (hG : ∀ p, |g p| ≤ G) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).compHolder₂ g (valueHolderL hα u)‖ ≤
      G * ‖valueHolderL hα (restrictL has le_rfl hsb u)‖ +
        nnHolderNorm α (g : slab (E := E) a b → ℝ) * ‖valueL u‖ := by
  have hG₀ : 0 ≤ G := (abs_nonneg _).trans (hG (slabMk 0 ⟨a, left_mem_Icc.2 hab.le⟩))
  have hgG : ‖g.toBoundedContinuousFunction‖ ≤ G :=
    (BoundedContinuousFunction.norm_le hG₀).2 fun p ↦ by simpa using hG p
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_compHolder₂_valueHolderL_le_of_eq_zero hα has hsb hg
    u).trans ?_
  refine (mul_le_of_le_one_left (by positivity) (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans ?_
  gcongr

/-- **The estimate at one scale.** Let `C_S` be a Schauder constant for `P` on `E × [0, T]`, and
let `χ` be a time cutoff vanishing up to time `s`, equal to one from time `δ` on, with
`[χ]_{α,par} ≤ K₀`, with time derivative vanishing before `s`, bounded by `K₁` and with
`[∂ₜχ]_{α,par} ≤ K₂`. Then for every time step `τ > 0` with `2 τ ≤ T - s`,

`‖u‖_{2+α,par;[δ,T]} ≤ C_S ((1 + K₀) ‖P u‖ + K₁ (2 τ ‖u‖_{2+α,par;[s,T]} +
  (1 + 40 τ^(-α/2)) ‖u‖_∞) + K₂ ‖u‖_∞)`. -/
private theorem norm_restrictL_le_of_timeCutoff (hα : α ≤ 1) {T : ℝ} {hT : 0 < T}
    {A : HolderSpace α (slab (E := E) 0 T) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {B : HolderSpace α (slab (E := E) 0 T) ((E →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {C : HolderSpace α (slab (E := E) 0 T) (ℝ →L[ℝ] ℝ)} {C_S : ℝ}
    (hS : ∀ w : ParabolicC2HolderSpace α E ℝ hT,
      ‖w‖ ≤ C_S * (‖parabolicOperatorL hα A B C w‖ + ‖w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖))
    (hC_S : 0 ≤ C_S) {s δ K₀ K₁ K₂ τ : ℝ} (hs : 0 < s) (hsT : s < T) (hδT : δ < T)
    {χ : ParabolicC2HolderSpace α E ℝ hT}
    (hχ₀ : ∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time ≤ s → χ p = 0)
    (hχ₁ : ∀ p : slab (E := E) 0 T, δ ≤ (p : ParabolicSpaceTime E).time → χ p = 1)
    (hχ : ∀ p, χ p ∈ Icc 0 1) (hD : spatialFDerivL χ = 0)
    (hK₀ : (nnHolderNorm α (valueL χ : slab (E := E) 0 T → ℝ) : ℝ) ≤ K₀)
    (hχt₀ : ∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time < s → timeDerivL χ p = 0)
    (hK₁ : ∀ p, |timeDerivL χ p| ≤ K₁)
    (hK₂ : (nnHolderNorm α (timeDerivL χ : slab (E := E) 0 T → ℝ) : ℝ) ≤ K₂)
    (hτ : 0 < τ) (hτT : 2 * τ ≤ T - s) (u : ParabolicC2HolderSpace α E ℝ hT) (hδ : 0 ≤ δ) :
    ‖restrictL hδ le_rfl hδT u‖ ≤ C_S * ((1 + K₀) * ‖parabolicOperatorL hα A B C u‖ +
      K₁ * (2 * τ * ‖restrictL hs.le le_rfl hsT u‖ + (1 + 40 * τ ^ (-((α : ℝ) / 2))) *
        ‖valueL u‖) + K₂ * ‖valueL u‖) := by
  -- The localization `w = χ u`, kept opaque so that elaboration does not unfold the product.
  obtain ⟨w, hwu⟩ : ∃ w : ParabolicC2HolderSpace α E ℝ hT,
      (ContinuousLinearMap.mul ℝ ℝ).compParabolicC2Holder₂ hα χ u = w :=
    ⟨_, rfl⟩
  -- On `E × [δ, T]` the localization `χ u` is `u`, and it vanishes at the initial time.
  have hw : restrictL hδ le_rfl hδT u = restrictL hδ le_rfl hδT w := by
    ext p
    simp [← hwu, hχ₁ (inclusion (slab_subset_slab hδ le_rfl) p) (mem_slab.1 p.property).1]
  have hw₀ : w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩ = 0 :=
    CkHolderSpace.ext fun x ↦ by
      simp [spatialTrace_apply, ← hwu, hχ₀ (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) (by simp [hs.le])]
  have hR : ‖restrictL hδ le_rfl hδT u‖ ≤ ‖w‖ := hw ▸ norm_restrictL_le _ _ _ w
  -- The two terms of `P (χ u) = χ P u + (∂ₜχ) u`.
  have hmul := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have h₁ : ‖(ContinuousLinearMap.mul ℝ ℝ).compHolder₂ (valueHolderL hα χ)
      (parabolicOperatorL hα A B C u)‖ ≤ (1 + K₀) * ‖parabolicOperatorL hα A B C u‖ := by
    refine ((ContinuousLinearMap.norm_compHolder₂_apply_le _ _ _).trans
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hmul)
        (norm_nonneg _))).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [HolderSpace.norm_def, toBoundedContinuousFunction_valueHolderL]
    refine add_le_add ((BoundedContinuousFunction.norm_le zero_le_one).2 fun p ↦ ?_) hK₀
    rw [valueL_apply, Real.norm_eq_abs, abs_of_nonneg (hχ p).1]
    exact (hχ p).2
  have hK₁₀ : 0 ≤ K₁ := (abs_nonneg _).trans (hK₁ (slabMk 0 ⟨0, left_mem_Icc.2 hT.le⟩))
  have h₂ := (norm_mul_valueHolderL_le hα (timeDerivL χ) u hs.le hsT hχt₀ hK₁).trans
    (add_le_add (mul_le_mul_of_nonneg_left ((norm_valueHolderL_le hα _ hτ hτT).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_valueL_restrictL_le u)
        (by positivity)))) hK₁₀)
      (mul_le_mul_of_nonneg_right hK₂ (norm_nonneg _)))
  refine hR.trans ((hS w).trans (mul_le_mul_of_nonneg_left ?_ hC_S))
  rw [hw₀, norm_zero, add_zero, ← hwu,
    parabolicOperatorL_mul_eq_of_spatialFDerivL_eq_zero hα A B C χ u hD]
  exact (norm_add_le _ _).trans (by linarith)

/-- The arithmetic of the weighted absorption at one scale `s`, with `ρ = s^(α/2)`,
`ζ = η^(-α/2)`, `X = ‖u‖_{2+α,par;[2s,T]}`, `Y = ‖u‖_{2+α,par;[s,T]}` and the weight
`W = (2 s)^(1 + α/2) ≤ 4 s ρ`. -/
private theorem weighted_arith {s ρ ζ η C_S Cχ f M₀ X Y N W T₀ : ℝ} (hs : 0 < s) (hρ : 0 < ρ)
    (hζ : 0 ≤ ζ) (hη : 0 ≤ η) (hC_S : 0 ≤ C_S) (hCχ : 0 ≤ Cχ) (hf : 0 ≤ f) (hM₀ : 0 ≤ M₀)
    (hX₀ : 0 ≤ X) (hY₀ : 0 ≤ Y) (hW : W ≤ 4 * (s * ρ)) (hsT : s ≤ T₀) (hρT : ρ ≤ 1 + T₀)
    (hX : X ≤ C_S * ((1 + Cχ * ρ⁻¹) * f + Cχ / s * (2 * (η * s) * Y + (1 + 40 * (ζ * ρ⁻¹)) * M₀) +
      Cχ * (s * ρ)⁻¹ * M₀))
    (hY : s * ρ * Y ≤ N) (hηC : 8 * C_S * Cχ * η ≤ 1 / 2) :
    W * X ≤ N / 2 + 4 * C_S * (T₀ * (1 + T₀) + Cχ * T₀ + Cχ * (2 + T₀ + 40 * ζ)) * (f + M₀) := by
  have hN : 0 ≤ N := (by positivity : 0 ≤ s * ρ * Y).trans hY
  have hsρ : s * ρ ≤ T₀ * (1 + T₀) := mul_le_mul hsT hρT hρ.le (hs.le.trans hsT)
  have hT₀ : 0 ≤ T₀ := hs.le.trans hsT
  calc W * X ≤ 4 * (s * ρ) * X := mul_le_mul_of_nonneg_right hW hX₀
    _ ≤ 4 * (s * ρ) * (C_S * ((1 + Cχ * ρ⁻¹) * f +
          Cχ / s * (2 * (η * s) * Y + (1 + 40 * (ζ * ρ⁻¹)) * M₀) + Cχ * (s * ρ)⁻¹ * M₀)) := by
        gcongr
    _ = 4 * C_S * ((s * ρ + Cχ * s) * f + 2 * Cχ * η * (s * ρ * Y) +
          Cχ * (ρ + 40 * ζ + 1) * M₀) := by
        field_simp
        ring
    _ ≤ 4 * C_S * ((T₀ * (1 + T₀) + Cχ * T₀) * f + 2 * Cχ * η * N +
          Cχ * (2 + T₀ + 40 * ζ) * M₀) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add ?_ ?_) ?_) (by positivity)
        · exact mul_le_mul_of_nonneg_right
            (add_le_add hsρ (mul_le_mul_of_nonneg_left hsT hCχ)) hf
        · exact mul_le_mul_of_nonneg_left hY (by positivity)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCχ) hM₀
    _ ≤ _ := by
        have ha : 0 ≤ T₀ * (1 + T₀) + Cχ * T₀ := by positivity
        have hb : 0 ≤ Cχ * (2 + T₀ + 40 * ζ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hηC hN, mul_nonneg (mul_nonneg hC_S ha) hM₀,
          mul_nonneg (mul_nonneg hC_S hb) hf]

/-- The powers of a scale `s > 0` met in the weighted estimate, written through `s^(α/2)`. -/
private theorem rpow_scale_eqs {s η : ℝ} (hs : 0 < s) (hη : 0 ≤ η) :
    s ^ (1 + (α : ℝ) / 2) = s * s ^ ((α : ℝ) / 2) ∧
      s ^ (-((α : ℝ) / 2)) = (s ^ ((α : ℝ) / 2))⁻¹ ∧
      s ^ (-(1 + (α : ℝ) / 2)) = (s * s ^ ((α : ℝ) / 2))⁻¹ ∧
      (η * s) ^ (-((α : ℝ) / 2)) = η ^ (-((α : ℝ) / 2)) * (s ^ ((α : ℝ) / 2))⁻¹ := by
  have h₁ : s ^ (1 + (α : ℝ) / 2) = s * s ^ ((α : ℝ) / 2) := by
    rw [Real.rpow_add hs, Real.rpow_one]
  refine ⟨h₁, Real.rpow_neg hs.le _, by rw [Real.rpow_neg hs.le, h₁], ?_⟩
  rw [Real.mul_rpow hη hs.le, Real.rpow_neg hs.le]

/-- The weight `(2 s)^(1 + α/2)` is at most `4 s^(1 + α/2)`, and `s^(α/2) ≤ 1 + s`. -/
private theorem rpow_two_mul_le {s : ℝ} (hs : 0 < s) (hα : α ≤ 1) :
    (2 * s) ^ (1 + (α : ℝ) / 2) ≤ 4 * (s * s ^ ((α : ℝ) / 2)) ∧ s ^ ((α : ℝ) / 2) ≤ 1 + s := by
  have hα' : (α : ℝ) ≤ 1 := hα
  constructor
  · rw [Real.mul_rpow zero_le_two hs.le, Real.rpow_add hs, Real.rpow_one]
    gcongr
    calc (2 : ℝ) ^ (1 + (α : ℝ) / 2) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 4 := by norm_num
  · rcases le_total s 1 with h | h
    · exact (Real.rpow_le_one hs.le h (by positivity)).trans (by linarith)
    · calc s ^ ((α : ℝ) / 2) ≤ s ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h (by linarith)
        _ ≤ 1 + s := by rw [Real.rpow_one]; linarith

/-- **The weighted estimate at one scale.** With the cutoff `χ` of `exists_timeCutoff` at the
scale `s` and the time step `η s` for the interpolation, where `8 C_S Cχ η ≤ 1/2`, the weighted
norm on `E × [2 s, T]` is at most half of any bound `N` for the weighted norm on `E × [s, T]`,
plus a multiple of `‖P u‖ + ‖u‖_∞`. The two restrictions of `u` enter as named elements `r` and
`r'`: stating the norms of restrictions directly makes unification unfold the order-two norm. -/
private theorem rpow_mul_norm_restrictL_le_of_timeCutoff (hα : α ≤ 1) {T : ℝ} {hT : 0 < T}
    {A : HolderSpace α (slab (E := E) 0 T) ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {B : HolderSpace α (slab (E := E) 0 T) ((E →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {C : HolderSpace α (slab (E := E) 0 T) (ℝ →L[ℝ] ℝ)} {C_S : ℝ}
    (hS : ∀ w : ParabolicC2HolderSpace α E ℝ hT,
      ‖w‖ ≤ C_S * (‖parabolicOperatorL hα A B C w‖ + ‖w.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩‖))
    (hC_S : 0 ≤ C_S) {Cχ η T₀ N s d : ℝ} (hCχ : 0 ≤ Cχ) (hη₀ : 0 < η) (hη₂ : η ≤ 1 / 2)
    (hηC : 8 * C_S * Cχ * η ≤ 1 / 2) (hs : 0 < s) (hsd : d = 2 * s) (hd : 0 < d) (hdT : d < T)
    (hsT : s < T) (hsT₀ : s ≤ T₀) {χ : ParabolicC2HolderSpace α E ℝ hT}
    (hχ₀ : ∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time ≤ s → χ p = 0)
    (hχ₁ : ∀ p : slab (E := E) 0 T, 2 * s ≤ (p : ParabolicSpaceTime E).time → χ p = 1)
    (hχ : ∀ p, χ p ∈ Icc 0 1) (hD : spatialFDerivL χ = 0)
    (hK₀ : (nnHolderNorm α (valueL χ : slab (E := E) 0 T → ℝ) : ℝ) ≤
      Cχ * s ^ (-((α : ℝ) / 2)))
    (hχt₀ : ∀ p : slab (E := E) 0 T, (p : ParabolicSpaceTime E).time < s → timeDerivL χ p = 0)
    (hK₁ : ∀ p, |timeDerivL χ p| ≤ Cχ / s)
    (hK₂ : (nnHolderNorm α (timeDerivL χ : slab (E := E) 0 T → ℝ) : ℝ) ≤
      Cχ * s ^ (-(1 + (α : ℝ) / 2)))
    (u : ParabolicC2HolderSpace α E ℝ hT) {r : ParabolicC2HolderSpace α E ℝ hdT}
    {r' : ParabolicC2HolderSpace α E ℝ hsT} (hr : restrictL hd.le le_rfl hdT u = r)
    (hr' : restrictL hs.le le_rfl hsT u = r') (hN : s ^ (1 + (α : ℝ) / 2) * ‖r'‖ ≤ N) :
    d ^ (1 + (α : ℝ) / 2) * ‖r‖ ≤ N / 2 +
      4 * C_S * (T₀ * (1 + T₀) + Cχ * T₀ + Cχ * (2 + T₀ + 40 * η ^ (-((α : ℝ) / 2)))) *
        (‖parabolicOperatorL hα A B C u‖ + ‖valueL u‖) := by
  have hτT : 2 * (η * s) ≤ T - s := by nlinarith
  have hest := norm_restrictL_le_of_timeCutoff hα hS hC_S hs hsT hdT hχ₀
    (fun p hp ↦ hχ₁ p (hsd ▸ hp)) hχ hD hK₀ hχt₀ hK₁ hK₂ (mul_pos hη₀ hs) hτT u hd.le
  rw [hr, hr'] at hest
  -- Express the powers of `s` through `ρ = s^(α/2)`.
  obtain ⟨e₁, e₂, e₃, e₄⟩ := rpow_scale_eqs (α := α) hs hη₀.le
  obtain ⟨hW, hρs⟩ := rpow_two_mul_le (α := α) hs hα
  rw [e₂, e₃, e₄] at hest
  rw [e₁] at hN
  exact weighted_arith hs (Real.rpow_pos_of_pos hs _) (by positivity) hη₀.le hC_S hCχ
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hsd ▸ hW) hsT₀
    (by linarith) hest hN hηC

/-- **Absorption over the scales.** If at every scale `d = 2 s < T` the weighted norm
`d^(1 + α/2) ‖u‖_{2+α,par;[d,T]}` is at most half of any bound for the weighted norm at the scale
`s`, plus `A`, then every weighted norm is at most `2 A`. The supremum of the weighted norms is
finite, since each is at most `T^(1 + α/2) ‖u‖`, and it absorbs half of itself. As in
`rpow_mul_norm_restrictL_le_of_timeCutoff`, the restrictions enter as named elements. -/
private theorem rpow_mul_norm_le_of_forall_two_mul {T : ℝ} {hT : 0 < T}
    (u : ParabolicC2HolderSpace α E ℝ hT) {A : ℝ} (hA : 0 ≤ A)
    (hstep : ∀ (s d N : ℝ) (hs : 0 < s) (hsT : s < T) (hd : 0 < d) (hdT : d < T), d = 2 * s →
      ∀ {r : ParabolicC2HolderSpace α E ℝ hdT} {r' : ParabolicC2HolderSpace α E ℝ hsT},
        restrictL hd.le le_rfl hdT u = r → restrictL hs.le le_rfl hsT u = r' →
        s ^ (1 + (α : ℝ) / 2) * ‖r'‖ ≤ N → d ^ (1 + (α : ℝ) / 2) * ‖r‖ ≤ N / 2 + A)
    {δ : ℝ} (hδ : 0 < δ) (hδT : δ < T) {r : ParabolicC2HolderSpace α E ℝ hδT}
    (hr : restrictL hδ.le le_rfl hδT u = r) : δ ^ (1 + (α : ℝ) / 2) * ‖r‖ ≤ 2 * A := by
  -- The weighted norms `N d` for `0 < d < T`, and `0` otherwise.
  let N : ℝ → ℝ := fun d ↦ if h₀ : 0 < d then if h₁ : d < T then
    d ^ (1 + (α : ℝ) / 2) * ‖restrictL h₀.le le_rfl h₁ u‖ else 0 else 0
  have hN (d : ℝ) (h₀ : 0 < d) (h₁ : d < T) :
      N d = d ^ (1 + (α : ℝ) / 2) * ‖restrictL h₀.le le_rfl h₁ u‖ := by
    simp [N, h₀, h₁]
  have hN' (d : ℝ) (h : ¬(0 < d ∧ d < T)) : N d = 0 := by
    by_cases h₀ : 0 < d
    · simp [N, h₀, show ¬d < T from fun h₁ ↦ h ⟨h₀, h₁⟩]
    · simp [N, h₀]
  have hbdd : BddAbove (Set.range N) := by
    refine ⟨T ^ (1 + (α : ℝ) / 2) * ‖u‖, ?_⟩
    rintro _ ⟨d, rfl⟩
    by_cases h : 0 < d ∧ d < T
    · rw [hN d h.1 h.2]
      exact mul_le_mul (Real.rpow_le_rpow h.1.le h.2.le (by positivity))
        (norm_restrictL_le _ _ _ u) (norm_nonneg _) (by positivity)
    · rw [hN' d h]
      positivity
  have hN₀ (d : ℝ) : 0 ≤ N d := by
    by_cases h : 0 < d ∧ d < T
    · rw [hN d h.1 h.2]
      exact mul_nonneg (Real.rpow_nonneg h.1.le _) (norm_nonneg _)
    · exact (hN' d h).ge
  -- Each weighted norm is at most half of the weighted norm at half the scale, plus `A`.
  have key (d : ℝ) : N d ≤ A + 1 / 2 * N (d / 2) := by
    by_cases h : 0 < d ∧ d < T
    · have hs : 0 < d / 2 := by linarith [h.1]
      have hsT : d / 2 < T := by linarith [h.1, h.2]
      -- Name the restrictions, so that unification does not unfold the order-two norm.
      obtain ⟨r, hr⟩ : ∃ r, restrictL h.1.le le_rfl h.2 u = r := ⟨_, rfl⟩
      obtain ⟨r', hr'⟩ : ∃ r', restrictL hs.le le_rfl hsT u = r' := ⟨_, rfl⟩
      have hY : (d / 2) ^ (1 + (α : ℝ) / 2) * ‖r'‖ ≤ N (d / 2) :=
        le_of_eq (by rw [hN _ hs hsT, hr'])
      rw [hN d h.1 h.2, hr]
      linarith [hstep (d / 2) d _ hs hsT h.1 h.2 (by ring) hr hr' hY]
    · rw [hN' d h]
      linarith [hN₀ (d / 2)]
  have hsup := ciSup_le_two_mul_of_le_add_mul hbdd hN₀ le_rfl (· / 2) key
  have h := le_ciSup hbdd δ
  rw [hN δ hδ hδT, hr] at h
  linarith

end TimeCutoff

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {lam Lam : ℝ}

/-- **Interior Schauder estimate at positive times.** For `0 < α < 1`, ellipticity constants
`λ > 0` and `Λ`, a bound `K` on the Hölder norms of the coefficients and a bound `T₀` on the
horizon, there is a constant `C` such that on `ℝⁿ × [0, T]`, `T ≤ T₀`, every
`u ∈ C_b^{2+α,1+α/2}` and every `0 < δ < T` satisfy

`δ^(1 + α/2) ‖u‖_{2+α,par;[δ,T]} ≤ C (‖P u‖_{α,par} + ‖u‖_∞)`,

where `‖u‖_{2+α,par;[δ,T]}` is the norm of the restriction of `u` to `ℝⁿ × [δ, T]` and
`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. Unlike the global Schauder estimate, the right side
does not involve the `C^{2,α}` norm of the initial values. -/
theorem exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL_add_norm_valueL (hα₀ : 0 < α)
    (hα₁ : α < 1) (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {δ : ℝ} (hδ : 0 < δ)
          (hδT : δ < T), δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤
            C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ + ‖valueL u‖) := by
  obtain ⟨C_S, hC_S, hS⟩ :=
    exists_norm_le_euclideanParabolicOperatorL (ι := ι) hα₀ hα₁ (Lam := Lam) hlam K T₀
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_timeCutoff (E := EuclideanSpace ℝ ι) (hα₁.le.trans one_le_two)
  -- The time step of the interpolation is `η s`, with `η` small enough to absorb.
  obtain ⟨η, hη₀, hη⟩ : ∃ η : ℝ, 0 < η ∧ η = 1 / (16 * C_S * Cχ + 2) :=
    ⟨_, by positivity, rfl⟩
  have hηC : 8 * C_S * Cχ * η ≤ 1 / 2 := by
    rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) two_pos]
    linarith
  have hη₂ : η ≤ 1 / 2 := by
    rw [hη]
    exact one_div_le_one_div_of_le two_pos (by nlinarith)
  set C' := 4 * C_S * (T₀ * (1 + T₀) + Cχ * T₀ + Cχ * (2 + T₀ + 40 * η ^ (-((α : ℝ) / 2))))
  refine ⟨2 * C', by positivity, fun T hT hTT₀ a b c ha ha' hak hbk hck u δ hδ hδT ↦ ?_⟩
  -- Name the restriction, so that unification does not unfold the order-two norm.
  obtain ⟨r, hr⟩ : ∃ r, restrictL hδ.le le_rfl hδT u = r := ⟨_, rfl⟩
  rw [hr, mul_assoc]
  -- At each scale `d = 2 s`, localize with the time cutoff at the scale `s`.
  refine rpow_mul_norm_le_of_forall_two_mul u (by positivity)
    (fun s d N hs hsT hd hdT hsd r r' hr hr' hN ↦ ?_) hδ hδT hr
  obtain ⟨χ, hχ₀, hχ₁, hχ01, hD, hK₀, hχt₀, hK₁, hK₂⟩ := hχ hT hs
  have h := rpow_mul_norm_restrictL_le_of_timeCutoff hα₁.le (fun w ↦ by
      rw [← euclideanParabolicOperatorL_def]
      exact hS T hT hTT₀ a b c ha ha' hak hbk hck w) hC_S hCχ hη₀ hη₂ hηC hs hsd hd hdT
    hsT (hsT.le.trans (by exact_mod_cast hTT₀)) hχ₀ hχ₁ hχ01 hD hK₀ hχt₀ hK₁ hK₂ u hr hr' hN
  rwa [← euclideanParabolicOperatorL_def] at h

/-- **Interior Schauder estimate at positive times, from the initial values.** For `0 < α < 1`,
ellipticity constants `λ > 0` and `Λ`, a bound `K` on the Hölder norms of the coefficients and a
bound `T₀` on the horizon, there is a constant `C` such that on `ℝⁿ × [0, T]`, `T ≤ T₀`, every
`u ∈ C_b^{2+α,1+α/2}` with `|u(·, 0)| ≤ M` and every `0 < δ < T` satisfy

`δ^(1 + α/2) ‖u‖_{2+α,par;[δ,T]} ≤ C (‖P u‖_{α,par} + M)`,

where `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`. Only the supremum of the initial values enters,
not their `C^{2,α}` norm. -/
theorem exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL (hα₀ : 0 < α) (hα₁ : α < 1)
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
        (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ),
        (∀ p (ξ : EuclideanSpace ℝ ι),
          lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ) →
        (∀ p (ξ : EuclideanSpace ℝ ι),
          (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
        (∀ i j, ‖a i j‖ ≤ K) → (∀ i, ‖b i‖ ≤ K) → ‖c‖ ≤ K →
        ∀ (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hT) {M : ℝ},
          (∀ x, |u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩)| ≤ M) → ∀ {δ : ℝ} (hδ : 0 < δ)
          (hδT : δ < T), δ ^ (1 + (α : ℝ) / 2) * ‖restrictL hδ.le le_rfl hδT u‖ ≤
            C * (‖euclideanParabolicOperatorL hα₁.le a b c u‖ + M) := by
  obtain ⟨C₁, hC₁, hest⟩ :=
    exists_rpow_mul_norm_restrictL_le_euclideanParabolicOperatorL_add_norm_valueL (ι := ι)
    hα₀ hα₁ (Lam := Lam) hlam K T₀
  obtain ⟨E₀, hE₀, hE⟩ : ∃ E₀ : ℝ, 0 ≤ E₀ ∧ E₀ = Real.exp (K * T₀) * (1 + T₀) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨C₁ * (1 + E₀), by positivity,
    fun T hT hTT₀ a b c ha ha' hak hbk hck u M hM δ hδ hδT ↦ ?_⟩
  set P := ‖euclideanParabolicOperatorL hα₁.le a b c u‖
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- The comparison principle bounds the supremum of `u` by its initial values and `P u`.
  have hV : ‖valueL u‖ ≤ E₀ * (P + M) := hE ▸
    norm_valueL_le_euclideanParabolicOperatorL_add_of_abs_le hα₁.le hTT₀ (b := b)
      (fun q ξ ↦ (mul_nonneg hlam.le (sq_nonneg ‖ξ‖)).trans (ha q ξ)) hck u hM
  have h := hest T hT hTT₀ a b c ha ha' hak hbk hck u hδ hδT
  -- Name the restriction, so that unification does not unfold the order-two norm.
  obtain ⟨r, hr⟩ : ∃ r, restrictL hδ.le le_rfl hδT u = r := ⟨_, rfl⟩
  rw [hr] at h ⊢
  calc _ ≤ C₁ * (P + ‖valueL u‖) := h
    _ ≤ C₁ * (P + E₀ * (P + M)) := by gcongr
    _ ≤ C₁ * (1 + E₀) * (P + M) := by nlinarith [mul_nonneg hC₁ (mul_nonneg hE₀ hM₀)]

end Euclidean

end TauCeti.ParabolicC2HolderSpace
