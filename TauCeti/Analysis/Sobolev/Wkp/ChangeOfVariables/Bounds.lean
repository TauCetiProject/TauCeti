/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Restrictions and `Lᵖ` bounds for changes of variables in `W^{k,p}`

This file collects consequences of the change-of-variables theory of
`TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables` used to straighten a curved boundary: restricting
a pair of mutually inverse changes of variables to the two sides of a boundary, `Lᵖ` bounds for
precomposition with a change of variables, the resulting bounds for the value, weak gradient
and weak Hessian of `u ∘ Φ`, and the transfer of local `W^{k,p}` regularity of `u ∘ Φ` back to
`u`.

## Main declarations

* `TauCeti.Wkp.IsChangeOfVariables.smul_add_const`: a homothety is a change of variables.
* `TauCeti.Wkp.IsChangeOfVariables.mono_const` and
  `TauCeti.Wkp.IsChangeOfVariables.norm_fderiv_fderiv_le`: weakening the constants of a change of
  variables, and the bound `L` on its second derivative.
* `TauCeti.Wkp.IsChangeOfVariables.inf_of_image_eq` and
  `TauCeti.Wkp.IsChangeOfVariables.exists_inf_of_image_eq`: a pair of mutually inverse changes of
  variables mapping `H ∩ U` onto `Ω ∩ V` restricts to the two sides, and to `V ∩ W` for any open
  `W`.
* `TauCeti.Wkp.IsChangeOfVariables.memLp_comp` and
  `TauCeti.Wkp.IsChangeOfVariables.lpNorm_comp_le`: precomposition with a change of variables is
  bounded on `Lᵖ`, between measurable subsets of its domain and of its target, and
  `TauCeti.Wkp.IsChangeOfVariables.lpNorm_le_of_ae_le_mul_comp` the resulting bound for a function
  dominated pointwise by such a composition.
* `TauCeti.Wkp.norm_value_compL_le` and `TauCeti.Wkp.norm_gradient_firstOrder_compL_le`: the
  `Lᵖ` bounds for the value and the weak gradient of `u ∘ Φ`, and
  `TauCeti.Wkp.IsChangeOfVariables.memLp_value_compL` and
  `TauCeti.Wkp.IsChangeOfVariables.memLp_gradient_firstOrder_compL` their `L^q` membership for any
  exponent `q`.
* `TauCeti.Wkp.norm_iteratedGradient_compL_le_ae`: the pointwise bound
  `‖D²(u ∘ Φ)‖ ≤ L² ‖D²u(Φ ·)‖ + L ‖∇u(Φ ·)‖` for the weak Hessian.
* `TauCeti.Wkp.exists_value_eq_value_restrictL_of_w1pCompL`: if `u ∘ Φ` is `W^{k,p}` near a
  point, then so is `u` near its image.
* `TauCeti.Wkp.IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_compL`: zero boundary values
  of `u ∈ W^{2,p}(Ω)` on a boundary portion carry over to `u ∘ Φ`.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace ENNReal ContDiff

namespace TauCeti.Wkp

namespace IsChangeOfVariables

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {U V : Opens E} {Φ : E → E} {k : ℕ} {L c : ℝ}

/-- A change of variables with constants `L` and `c` is one with any larger derivative bound
`L' ≥ L` and any smaller positive Jacobian bound `c' ≤ c`. -/
theorem mono_const {L' c' : ℝ} (h : IsChangeOfVariables k U V Φ L c) (hL : L ≤ L')
    (hc : 0 < c') (hc' : c' ≤ c) : IsChangeOfVariables k U V Φ L' c' where
  contDiffOn := h.contDiffOn
  differentiableOn := h.differentiableOn
  injOn := h.injOn
  mapsTo := h.mapsTo
  norm_iteratedFDeriv_le i hi hik x hx := (h.norm_iteratedFDeriv_le i hi hik x hx).trans hL
  pos := hc
  le_abs_det x hx := hc'.trans (h.le_abs_det x hx)

/-- The second derivative of a change of variables of order at least two is bounded by `L`. -/
theorem norm_fderiv_fderiv_le (h : IsChangeOfVariables (k + 2) U V Φ L c) :
    ∀ x ∈ (U : Set E), ‖fderiv ℝ (fderiv ℝ Φ) x‖ ≤ L := fun x hx => by
  rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  exact h.norm_iteratedFDeriv_le 2 one_le_two (by omega) x hx

/-- A homothety `x ↦ ε x + a` with `ε > 0` mapping `U` into `V` is a change of variables of every
order, with constants `ε` and `ε ^ finrank ℝ E`. -/
theorem smul_add_const {ε : ℝ} (hε : 0 < ε) (a : E) (hA : MapsTo (fun x : E => ε • x + a) U V) :
    IsChangeOfVariables k U V (fun x : E => ε • x + a) ε (ε ^ Module.finrank ℝ E) := by
  have hd : fderiv ℝ (fun x : E => ε • x + a) = fun _ => ε • ContinuousLinearMap.id ℝ E :=
    funext fun x => (((hasFDerivAt_id x).const_smul ε).add_const a).fderiv
  exact
    { contDiffOn := ((contDiff_id.const_smul ε).add contDiff_const).contDiffOn
      differentiableOn := ((differentiable_id.const_smul ε).add_const a).differentiableOn
      injOn := fun _ _ _ _ h => smul_right_injective E hε.ne' (add_right_cancel h)
      mapsTo := hA
      norm_iteratedFDeriv_le := fun i hi _ x _ => by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hi
        rw [← norm_iteratedFDeriv_fderiv]
        rcases n with _ | n
        · simpa [hd, norm_smul, abs_of_pos hε] using
            mul_le_of_le_one_right hε.le ContinuousLinearMap.norm_id_le
        · rw [hd, iteratedFDeriv_const_of_ne n.succ_ne_zero]
          simpa using hε.le
      pos := pow_pos hε _
      le_abs_det := fun x _ => by
        rw [hd, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
          ContinuousLinearMap.coe_id, LinearMap.det_smul, LinearMap.det_id, mul_one,
          abs_of_pos (pow_pos hε _)] }

/-- **The chart between the two sides.** If mutually inverse changes of variables `Φ` and `Ψ`
between `U` and `V` satisfy `Φ '' (H ∩ U) = Ω ∩ V`, then `Φ` restricts to a change of variables
from `H ∩ U` into `Ω ∩ V` and `Ψ` to one from `Ω ∩ V` into `H ∩ U`, with the same constants. -/
theorem inf_of_image_eq {Omega H : Opens E} {Ψ : E → E} {L' c' : ℝ}
    (hΦ : IsChangeOfVariables k U V Φ L c) (hΨ : IsChangeOfVariables k V U Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U) (himage : Φ '' ((H : Set E) ∩ U) = (Omega : Set E) ∩ V) :
    IsChangeOfVariables k (H ⊓ U) (Omega ⊓ V) Φ L c ∧
      IsChangeOfVariables k (Omega ⊓ V) (H ⊓ U) Ψ L' c' := by
  refine ⟨hΦ.mono_set inf_le_right fun x hx => ?_, hΨ.mono_set inf_le_right fun y hy => ?_⟩
  · have h : Φ x ∈ Φ '' ((H : Set E) ∩ U) := mem_image_of_mem Φ hx
    rw [himage] at h
    exact h
  · have h : y ∈ (Omega : Set E) ∩ V := hy
    rw [← himage] at h
    obtain ⟨x, hx, rfl⟩ := h
    rw [hΨΦ hx.2]
    exact hx

/-- **Restricting a straightening chart.** If mutually inverse changes of variables `Φ` and `Ψ`
between `U` and `V` satisfy `Φ '' (H ∩ U) = Ω ∩ V`, then for every open `W` they restrict to
mutually inverse changes of variables between `U₁ = U ∩ Φ⁻¹(W)` and `V ∩ W`, with the same
constants, and `Φ '' (H ∩ U₁) = Ω ∩ V ∩ W`. -/
theorem exists_inf_of_image_eq {Omega H : Set E} {Ψ : E → E} {L' c' : ℝ}
    (hΦ : IsChangeOfVariables k U V Φ L c) (hΨ : IsChangeOfVariables k V U Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U) (hΦΨ : RightInvOn Ψ Φ V) (himage : Φ '' (H ∩ U) = Omega ∩ V)
    (W : Opens E) :
    ∃ U₁ : Opens E, IsChangeOfVariables k U₁ (V ⊓ W) Φ L c ∧
      IsChangeOfVariables k (V ⊓ W) U₁ Ψ L' c' ∧ LeftInvOn Ψ Φ U₁ ∧
        RightInvOn Ψ Φ (V ⊓ W : Opens E) ∧ Φ '' (H ∩ U₁) = Omega ∩ (V ⊓ W : Opens E) := by
  let U₁ : Opens E := ⟨U ∩ Φ ⁻¹' W,
    hΦ.differentiableOn.continuousOn.isOpen_inter_preimage U.isOpen W.isOpen⟩
  have hU₁ : U₁ ≤ U := fun x hx => hx.1
  refine ⟨U₁, hΦ.mono_set hU₁ fun x hx => ⟨hΦ.mapsTo hx.1, hx.2⟩,
    hΨ.mono_set inf_le_left fun y hy => ⟨hΨ.mapsTo hy.1, ?_⟩, hΨΦ.mono hU₁,
    hΦΨ.mono inf_le_left, ?_⟩
  · rw [mem_preimage, hΦΨ hy.1]
    exact hy.2
  · ext y
    constructor
    · rintro ⟨x, ⟨hxH, hxU, hxW⟩, rfl⟩
      have hx : Φ x ∈ Omega ∩ V := himage ▸ mem_image_of_mem Φ ⟨hxH, hxU⟩
      exact ⟨hx.1, hx.2, hxW⟩
    · rintro ⟨hyΩ, hyV, hyW⟩
      obtain ⟨x, ⟨hxH, hxU⟩, rfl⟩ : y ∈ Φ '' (H ∩ U) := himage ▸ ⟨hyΩ, hyV⟩
      exact ⟨x, ⟨hxH, hxU, hyW⟩, rfl⟩

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {mu : Measure E}

/-- Precomposition with a change of variables preserves `Lᵖ`: if `g ∈ Lᵖ(T)` and `Φ` maps a
measurable `S ⊆ U` into `T`, then `g ∘ Φ ∈ Lᵖ(S)`. -/
theorem memLp_comp [mu.IsAddHaarMeasure] {p : ℝ≥0∞} (h : IsChangeOfVariables k U V Φ L c)
    {S T : Set E} (hS : MeasurableSet S) (hSU : S ⊆ U) (hST : MapsTo Φ S T) {G : Type*}
    [NormedAddCommGroup G] {g : E → G} (hg : MemLp g p (mu.restrict T)) :
    MemLp (fun x => g (Φ x)) p (mu.restrict S) :=
  (hg.mono_measure (Measure.restrict_mono hST.image_subset le_rfl)).comp_restrict_of_le_abs_det
    U.isOpen h.differentiableOn (h.injOn.mono hSU) hSU hS h.pos fun x hx => h.le_abs_det x (hSU hx)

/-- Precomposition with a change of variables is bounded on `Lᵖ`: if `Φ` maps a measurable
`S ⊆ U` into `T`, then `‖g ∘ Φ‖_{Lᵖ(S)} ≤ c^(-1/p) ‖g‖_{Lᵖ(T)}`. -/
theorem lpNorm_comp_le [mu.IsAddHaarMeasure] {p : ℝ≥0∞} (h : IsChangeOfVariables k U V Φ L c)
    {S T : Set E} (hS : MeasurableSet S) (hSU : S ⊆ U) (hST : MapsTo Φ S T) {G : Type*}
    [NormedAddCommGroup G] {g : E → G} (hg : MemLp g p (mu.restrict T)) :
    lpNorm (fun x => g (Φ x)) p (mu.restrict S) ≤
      c⁻¹ ^ (1 / p).toReal * lpNorm g p (mu.restrict T) := by
  have hle : eLpNorm (fun x => g (Φ x)) p (mu.restrict S) ≤
      (ENNReal.ofReal c)⁻¹ ^ (1 / p).toReal * eLpNorm g p (mu.restrict T) :=
    (eLpNorm_comp_restrict_le U.isOpen h.differentiableOn (h.injOn.mono hSU) hSU hS h.pos
      (fun x hx => h.le_abs_det x (hSU hx)) g).trans (by gcongr; exact hST.image_subset)
  rw [← toReal_eLpNorm, ← toReal_eLpNorm]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (by simp [h.pos])) hg.eLpNorm_ne_top) hle).trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal h.pos.le]

/-- **`Lᵖ` bound from a pointwise bound by a composition.** If `Φ` maps a measurable `S ⊆ U`
into `T`, `g ∈ Lᵖ(T)` and `‖F x‖ ≤ K ‖g (Φ x)‖` almost everywhere on `S` with `K ≥ 0`, then
`‖F‖_{Lᵖ(S)} ≤ K c^(-1/p) ‖g‖_{Lᵖ(T)}`. -/
theorem lpNorm_le_of_ae_le_mul_comp [mu.IsAddHaarMeasure] {p : ℝ≥0∞}
    (h : IsChangeOfVariables k U V Φ L c) {S T : Set E} (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hST : MapsTo Φ S T) {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    {F : E → H} {g : E → G} {K : ℝ} (hK : 0 ≤ K) (hF : AEStronglyMeasurable F (mu.restrict S))
    (hg : MemLp g p (mu.restrict T)) (hFg : ∀ᵐ x ∂mu.restrict S, ‖F x‖ ≤ K * ‖g (Φ x)‖) :
    lpNorm F p (mu.restrict S) ≤ K * (c⁻¹ ^ (1 / p).toReal * lpNorm g p (mu.restrict T)) :=
  (lpNorm_le_mul_lpNorm_of_ae_le_mul hF (h.memLp_comp hS hSU hST hg) hFg).trans
    (mul_le_mul_of_nonneg_left (h.lpNorm_comp_le hS hSU hST hg) hK)

end IsChangeOfVariables

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {U V : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : E → E} {k : ℕ} {L c : ℝ}

/-- The value of `compL h u` has `Lᵖ(U)` norm at most `c^(-1/p) ‖u‖_{Lᵖ(V)}`. -/
theorem norm_value_compL_le (h : IsChangeOfVariables k U V Φ L c) (u : Wkp mu V p k) :
    ‖value k (compL h u)‖ ≤ c⁻¹ ^ (1 / p).toReal * ‖value k u‖ := by
  have hval : ∀ᵐ x ∂mu.restrict U, ‖value k (compL h u) x‖ ≤ 1 * ‖value k u (Φ x)‖ := by
    filter_upwards [value_compL_ae h u] with x hx
    rw [hx, one_mul]
  rw [Lp.norm_def, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm, ← one_mul (_ * _)]
  exact h.lpNorm_le_of_ae_le_mul_comp U.isOpen.measurableSet subset_rfl h.mapsTo zero_le_one
    (Lp.aestronglyMeasurable _) (Lp.memLp _) hval

/-- For `L ≥ 0`, the weak gradient of the first-order part of `compL h u` has `Lᵖ(U)` norm at
most `L c^(-1/p) ‖∇u‖_{Lᵖ(V)}`. -/
theorem norm_gradient_firstOrder_compL_le (h : IsChangeOfVariables (k + 1) U V Φ L c)
    (hL : 0 ≤ L) (u : Wkp mu V p (k + 1)) :
    ‖W1p.gradient (firstOrder k (compL h u))‖ ≤
      L * (c⁻¹ ^ (1 / p).toReal * ‖W1p.gradient (firstOrder k u)‖) := by
  have hU : MeasurableSet (U : Set E) := U.isOpen.measurableSet
  have hgr : ∀ᵐ x ∂mu.restrict U, ‖W1p.gradient (firstOrder k (compL h u)) x‖ ≤
      L * ‖W1p.gradient (firstOrder k u) (Φ x)‖ := by
    filter_upwards [gradient_firstOrder_compL_ae h u, ae_restrict_mem hU] with x h1 hx
    rw [h1]
    refine ((fderiv ℝ Φ x).adjoint.le_opNorm _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    gcongr
    exact h.norm_fderiv_le x hx
  rw [Lp.norm_def, toReal_eLpNorm, Lp.norm_def, toReal_eLpNorm]
  exact h.lpNorm_le_of_ae_le_mul_comp hU subset_rfl h.mapsTo hL (Lp.aestronglyMeasurable _)
    (Lp.memLp _) hgr

/-- If the value of `u ∈ W^{k,p}(V)` lies in `L^q(V)`, so does the value of `compL h u` in
`L^q(U)`, for any exponent `q`. -/
theorem IsChangeOfVariables.memLp_value_compL (h : IsChangeOfVariables k U V Φ L c)
    (u : Wkp mu V p k) {q : ℝ≥0∞} (hu : MemLp (value k u) q (mu.restrict V)) :
    MemLp (value k (compL h u)) q (mu.restrict U) :=
  (h.memLp_comp U.isOpen.measurableSet subset_rfl h.mapsTo hu).ae_eq (value_compL_ae h u).symm

/-- If the weak gradient of the first-order part of `u ∈ W^{k+1,p}(V)` lies in `L^q(V)`, so does
that of `compL h u` in `L^q(U)`, for any exponent `q`. -/
theorem IsChangeOfVariables.memLp_gradient_firstOrder_compL
    (h : IsChangeOfVariables (k + 1) U V Φ L c) (u : Wkp mu V p (k + 1)) {q : ℝ≥0∞}
    (hu : MemLp (W1p.gradient (firstOrder k u)) q (mu.restrict V)) :
    MemLp (W1p.gradient (firstOrder k (compL h u))) q (mu.restrict U) := by
  have hU : MeasurableSet (U : Set E) := U.isOpen.measurableSet
  refine (h.memLp_comp hU subset_rfl h.mapsTo hu).of_le_mul (c := L)
    (Lp.aestronglyMeasurable _) ?_
  filter_upwards [gradient_firstOrder_compL_ae h u, ae_restrict_mem hU] with x h1 hx
  rw [h1]
  refine ((fderiv ℝ Φ x).adjoint.le_opNorm _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_right (h.norm_fderiv_le x hx) (norm_nonneg _)

/-- **The Hessian under a change of variables.** Let `Φ` be a change of variables of order two
from `U` into `V` with constant `L`, and `1 ≤ p < ∞`. For `u ∈ W^{2,p}(V)`, the weak Hessian of
`u ∘ Φ` satisfies `‖D²(u ∘ Φ)(x)‖ ≤ L² ‖D²u(Φ x)‖ + L ‖∇u(Φ x)‖` for almost every `x ∈ U`. -/
theorem norm_iteratedGradient_compL_le_ae (h : IsChangeOfVariables 2 U V Φ L c) (hp : p ≠ ⊤)
    (u : Wkp mu V p 2) :
    ∀ᵐ x ∂mu.restrict U, ‖iteratedGradient 1 (compL h u) x‖ ≤
      L ^ 2 * ‖iteratedGradient 1 u (Φ x)‖ + L * ‖iteratedGradient 0 (lowerOrder 1 u) (Φ x)‖ := by
  filter_upwards [inner_iteratedGradient_compL_ae h hp u, ae_restrict_mem U.isOpen.measurableSet]
    with x hx hxU
  have hD := h.norm_fderiv_le x hxU
  have hL : 0 ≤ L := (norm_nonneg _).trans hD
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity) fun f g hf hg => ?_
  rw [RCLike.re_to_real, hx f g]
  set H := iteratedGradient 1 u (Φ x)
  set G := iteratedGradient 0 (lowerOrder 1 u) (Φ x)
  have hDv (w : E) (hw : ‖w‖ = 1) : ‖fderiv ℝ Φ x w‖ ≤ L :=
    ((fderiv ℝ Φ x).le_opNorm w).trans (by rw [hw, mul_one]; exact hD)
  have h1 : ⟪H (fderiv ℝ Φ x f), fderiv ℝ Φ x g⟫_ℝ ≤ L ^ 2 * ‖H‖ :=
    calc _ ≤ ‖H (fderiv ℝ Φ x f)‖ * ‖fderiv ℝ Φ x g‖ := real_inner_le_norm _ _
      _ ≤ (‖H‖ * L) * L := by
        gcongr
        · exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hDv f hf) (norm_nonneg _))
        · exact hDv g hg
      _ = L ^ 2 * ‖H‖ := by ring
  have h2 : ⟪G, fderiv ℝ (fderiv ℝ Φ) x f g⟫_ℝ ≤ L * ‖G‖ :=
    calc _ ≤ ‖G‖ * ‖fderiv ℝ (fderiv ℝ Φ) x f g‖ := real_inner_le_norm _ _
      _ ≤ ‖G‖ * L := by
        gcongr
        refine ((fderiv ℝ (fderiv ℝ Φ) x).le_opNorm₂ f g).trans ?_
        rw [hf, hg, mul_one, mul_one]
        exact h.norm_fderiv_fderiv_le (k := 0) x hxU
      _ = L * ‖G‖ := mul_comm _ _
  linarith

/-- **Pushing `W^{k,p}` forward along a change of variables.** Let `Φ` be a change of variables
from `Ω'` into `D ⊆ Ω`, and `Ψ` one of order `k` from `Ω ∩ V ⊆ D` into `Ω' ∩ V''` with
`Φ ∘ Ψ = id` on `Ω ∩ V`. If `u ∘ Φ` is the value of an element of `W^{k,p}(Ω' ∩ V'')`, then `u` is
the value of an element of `W^{k,p}(Ω ∩ V)`. -/
theorem exists_value_eq_value_restrictL_of_w1pCompL {Omega D V Ω' V'' : Opens E} {Ψ : E → E}
    {L' c' : ℝ} (hp : p ≠ ⊤) (hD : D ≤ Omega) (hVD : Omega ⊓ V ≤ D)
    (hΦ : IsChangeOfVariables 1 Ω' D Φ L c)
    (hΨ : IsChangeOfVariables k (Omega ⊓ V) (Ω' ⊓ V'') Ψ L' c')
    (hΦΨ : RightInvOn Ψ Φ (Omega ⊓ V : Opens E)) {u : W1p mu Omega p}
    {w : Wkp mu (Ω' ⊓ V'') p k}
    (hw : value k w =
      W1p.value (W1p.restrictL inf_le_left (hΦ.w1pCompL hp (W1p.restrictL hD u)))) :
    ∃ w' : Wkp mu (Omega ⊓ V) p k, value k w' = W1p.value (W1p.restrictL inf_le_left u) := by
  refine ⟨compL hΨ w, Lp.ext ?_⟩
  have hΩ'V : ((Ω' ⊓ V'' : Opens E) : Set E) ⊆ Ω' := fun x hx => hx.1
  filter_upwards [value_compL_ae hΨ w,
    hΨ.ae_comp (W1p.value_restrictL_ae (mu := mu) (p := p) inf_le_left _),
    hΨ.ae_comp (ae_restrict_of_ae_restrict_of_subset hΩ'V
      (hΦ.value_w1pCompL_ae hp (W1p.restrictL hD u))),
    ae_restrict_of_ae_restrict_of_subset hVD (W1p.value_restrictL_ae hD u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h1 h2 h3 h4 h5 hx
  rw [h1, hw, h2, h3, hΦΨ hx, h4, h5]

/-- **Zero boundary values along a straightening chart.** Let `Φ` be a change of variables of order
two from `Ω'` into `Ω ∩ O`, with continuous left inverse `Ψ` mapping `Ω ∩ O` into `Ω'`, and let
`Φ` be continuous on an open `U''` that it maps into `O`. If `χ u ∈ W₀^{1,p}(Ω)` for every smooth
`χ` compactly supported in `O`, then `ψ (u ∘ Φ) ∈ W₀^{1,p}(Ω')` for every smooth `ψ` compactly
supported in `U''`. This is
`TauCeti.Wkp.IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_w1pCompL` for the first-order
part of `u ∈ W^{2,p}(Ω)`. -/
theorem IsChangeOfVariables.exists_w1p0_value_ae_eq_mul_value_compL {Omega O Ω' U'' : Opens E}
    {Ψ : E → E} (hΦ : IsChangeOfVariables 2 Ω' (Omega ⊓ O) Φ L c) (hp : p ≠ ⊤)
    (hΦc : ContinuousOn Φ U'') (hΦU'' : MapsTo Φ U'' O) (hΨc : ContinuousOn Ψ (Omega ⊓ O : Opens E))
    (hΨmaps : MapsTo Ψ (Omega ⊓ O : Opens E) Ω') (hΨΦ : LeftInvOn Ψ Φ Ω') {u : Wkp mu Omega p 2}
    (hu0 : ∀ χ : E → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ O →
      ∃ w : W1p0 mu Omega p,
        W1p.value (w : W1p mu Omega p) =ᵐ[mu.restrict Omega] fun x => χ x * value 2 u x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U'') :
    ∃ w : W1p0 mu Ω' p, W1p.value (w : W1p mu Ω' p) =ᵐ[mu.restrict Ω']
      fun x => ψ x * value 2 (compL hΦ (restrictL inf_le_left 2 u)) x := by
  have hΦ1 : IsChangeOfVariables 1 Ω' (Omega ⊓ O) Φ L c := hΦ.mono one_le_two
  obtain ⟨w, hw⟩ := hΦ1.exists_w1p0_value_ae_eq_mul_value_w1pCompL hp hΦc hΨc hΨmaps hΨΦ hΦU''
    (u := lowerOrder 1 u) (fun χ hχ hχc hχs => by
      simpa only [value_lowerOrder_one] using hu0 χ hχ hχc hχs) ψ hψ hψc hψs
  refine ⟨w, hw.trans ?_⟩
  filter_upwards [hΦ1.value_w1pCompL_ae hp (W1p.restrictL inf_le_left (lowerOrder 1 u)),
    hΦ.ae_comp (W1p.value_restrictL_ae inf_le_left (lowerOrder 1 u)),
    value_compL_ae hΦ (restrictL inf_le_left 2 u),
    hΦ.ae_comp (value_restrictL_ae inf_le_left 2 u)] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4, value_lowerOrder_one]

end TauCeti.Wkp
