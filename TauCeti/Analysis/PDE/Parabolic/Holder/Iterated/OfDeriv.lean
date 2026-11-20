/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import TauCeti.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Parabolic Hölder maps from their first derivatives

A bounded continuous map `u` on the slab `E × [a, b]` whose spatial derivative `D_x u` lies in the
parabolic Hölder space `C_{par,b}^{(k+1)+α}` and whose time derivative `∂ₜu` within `[a, b]` lies
in `C_{par,b}^{k+α}` lies in `C_{par,b}^{(k+2)+α}`
(`TauCeti.ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv`), with

`‖u‖_{(k+2)+α} ≤ 4 (k + 3)² (‖u‖_∞ + ‖D_x u‖_{(k+1)+α} + ‖∂ₜu‖_{k+α})`

(`TauCeti.ParabolicCkHolderSpace.norm_ofSpatialFDerivTimeDeriv_le`). In the parabolic scaling a
spatial derivative lowers the order by one and a time derivative by two, so this is the converse of
differentiation. It is the step that raises the order in the higher regularity theory of parabolic
equations: for a solution of `∂ₜu = aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u + f`, regularity of `D_x u` one
order up makes the right-hand side, hence `∂ₜu`, regular two orders below the target, and the
construction here then places `u` itself at the target order.

## The argument

The fields `D_t^r D_x^m u` of the new map are read off its derivatives: `D_x^(m+1) u` from the
field `D_x^m` of `G = D_x u` with its last variable uncurried, and `D_t^(r+1) D_x^m u` from the
field `D_t^r D_x^m` of `H = ∂ₜu`. The spatial and time derivative identities required by
`TauCeti.ParabolicCkHolderSpace.mk` hold within each of the two families. Across them, the time
derivative of `D_x^(m+1) u`, read off `G`, must be the field `D_x^(m+1) ∂ₜu` read off `H`. By
uniqueness of Fréchet derivatives this reduces to `m = 0`, which is the symmetry
`∂ₜ D_x u = D_x ∂ₜu` of the mixed derivatives
(`TauCeti.eq_of_hasFDerivAt_of_hasDerivWithinAt_slab`). Tested against a functional `ℓ` and a
direction `v`, the fundamental theorem of calculus in time, differentiated along `x + s v` under
the integral sign, gives

`ℓ (D_x u (x, t) v) - ℓ (D_x u (x, a) v) = ∫_a^t ℓ (D_x ∂ₜu (x, τ) v) dτ`,

and differentiating in `t` within `[a, b]` identifies the two mixed derivatives, since one-sided
derivatives at the ends of `[a, b]` are unique. The Hölder conditions at the top two orders are
those of `G` and `H`.

## Main declarations

* `TauCeti.eq_of_hasFDerivAt_of_hasDerivWithinAt_slab`: the mixed space-time derivatives of a
  map on a slab agree.
* `TauCeti.ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv`: the element of
  `C_{par,b}^{(k+2)+α}` with value `u`, spatial derivative `G` and time derivative `H`.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivL_zero_succ_ofSpatialFDerivTimeDeriv` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_succ_ofSpatialFDerivTimeDeriv`: its fields.
* `TauCeti.ParabolicCkHolderSpace.norm_ofSpatialFDerivTimeDeriv_le`: its norm estimate.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

open Set Filter Topology MeasureTheory ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

section MixedDerivatives

variable {φ : slab (E := E) a b → F} {ψ ψ₁ χ₁ : slab (E := E) a b → E →L[ℝ] F}
  {χ : slab (E := E) a b → F}

omit [NormedSpace ℝ E] in
/-- **The fundamental theorem of calculus in time.** Tested against a functional `ℓ`, the
increment of `φ` in time at a point `y` is the integral of its time derivative `χ`. -/
private theorem integral_timeExtension_eq_sub (hab : a < b) (hχ : Continuous χ)
    (hφt : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
      (timeExtension hab.le φ x) (χ (slabMk x t)) (Icc a b) t)
    (ℓ : StrongDual ℝ F) (y : E) (t : Icc a b) :
    ∫ τ in a..t, ℓ (timeExtension hab.le χ y τ) =
      ℓ (φ (slabMk y t)) - ℓ (φ (slabMk y ⟨a, left_mem_Icc.2 hab.le⟩)) := by
  have hcont : ContinuousOn (fun τ ↦ ℓ (timeExtension hab.le φ y τ)) (Icc a b) := fun τ hτ ↦
    ℓ.continuous.continuousAt.comp_continuousWithinAt (hφt y ⟨τ, hτ⟩).continuousWithinAt
  have hint : Continuous fun τ ↦ ℓ (timeExtension hab.le χ y τ) :=
    ℓ.continuous.comp (continuous_timeExtension_slice hab.le hχ y)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.2.1
    (hcont.mono (Icc_subset_Icc_right t.2.2)) (fun τ hτ ↦ ?_) (hint.intervalIntegrable _ _)]
  · have ha := timeExtension_of_mem hab.le φ y ⟨a, left_mem_Icc.2 hab.le⟩
    rw [timeExtension_of_mem]
    exact congrArg (fun z ↦ ℓ (φ (slabMk y t)) - ℓ z) ha
  · have hτ' : τ ∈ Icc a b := ⟨hτ.1.le, hτ.2.le.trans t.2.2⟩
    have hd := (hφt y ⟨τ, hτ'⟩).hasDerivAt (Icc_mem_nhds hτ.1 (hτ.2.trans_le t.2.2))
    have he : timeExtension hab.le χ y τ = χ (slabMk y ⟨τ, hτ'⟩) :=
      timeExtension_of_mem hab.le χ y ⟨τ, hτ'⟩
    rw [he]
    exact ℓ.hasFDerivAt.comp_hasDerivAt τ hd

/-- Differentiating `integral_timeExtension_eq_sub` along the line `x + s v` at `s = 0`: the
increment in time of `D_x φ (·) v` at `x` is the integral of `∂_x ∂ₜφ (·) v`. -/
private theorem sub_eq_integral_timeExtension (hab : a < b) (hχ : Continuous χ)
    (hχ₁ : Continuous χ₁)
    (hφx : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ φ (slabMk y t)) (ψ (slabMk x t)) x)
    (hφt : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
      (timeExtension hab.le φ x) (χ (slabMk x t)) (Icc a b) t)
    (hχx : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ χ (slabMk y t)) (χ₁ (slabMk x t)) x)
    (ℓ : StrongDual ℝ F) (x v : E) (t : Icc a b) :
    ℓ (ψ (slabMk x t) v) - ℓ (ψ (slabMk x ⟨a, left_mem_Icc.2 hab.le⟩) v) =
      ∫ τ in a..t, ℓ (timeExtension hab.le χ₁ x τ v) := by
  have hline (s : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  -- The time integrand along the line `x + s v` and its derivative in `s`.
  let g : ℝ → ℝ → ℝ := fun s τ ↦ ℓ (timeExtension hab.le χ (x + s • v) τ)
  let g' : ℝ → ℝ → ℝ := fun s τ ↦ ℓ (timeExtension hab.le χ₁ (x + s • v) τ v)
  have hgs (s : ℝ) : Continuous (g s) :=
    ℓ.continuous.comp (continuous_timeExtension_slice hab.le hχ _)
  have hg's (s : ℝ) : Continuous (g' s) :=
    (ℓ.comp (ContinuousLinearMap.apply ℝ F v)).continuous.comp
      (continuous_timeExtension_slice hab.le hχ₁ _)
  -- A bound for `χ₁` on the compact set swept by `x + s v`, `|s| ≤ 1`, `t ∈ [a, b]`.
  obtain ⟨M, hM⟩ :=
    ((isCompact_closedBall (0 : ℝ) 1).prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun q : ℝ × ℝ ↦ timeExtension hab.le χ₁ (x + q.1 • v) q.2)
    ((continuous_timeExtension hab.le hχ₁).comp (continuous_snd.prodMk
      (continuous_const.add (continuous_fst.smul continuous_const)))).continuousOn
  have hφs (t' : Icc a b) : HasDerivAt (fun s : ℝ ↦ ℓ (φ (slabMk (x + s • v) t')))
      (ℓ (ψ (slabMk x t') v)) 0 := by
    have hd := (hφx t' (x + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) (hline 0)
    have h := ℓ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    simp only [zero_smul, add_zero, Function.comp_def] at h
    exact h
  -- Differentiation under the integral sign, dominated by `‖ℓ‖ ‖χ₁‖ ‖v‖`.
  have hint := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := g) (F' := g') (x₀ := 0) (a := a) (b := t)
    (bound := fun _ ↦ ‖ℓ‖ * M * ‖v‖)
    (Metric.ball_mem_nhds 0 one_pos) (Eventually.of_forall fun s ↦ (hgs s).aestronglyMeasurable)
    ((hgs 0).intervalIntegrable _ _) (hg's 0).aestronglyMeasurable
    (ae_of_all _ fun τ hτ s hs ↦ ?_) intervalIntegrable_const
    (ae_of_all _ fun τ _ s _ ↦ ?_)).2
  · have h := (hφs t).sub (hφs ⟨a, left_mem_Icc.2 hab.le⟩)
    have hfun : (fun s ↦ ∫ τ in a..t, g s τ) = (fun s ↦ ℓ (φ (slabMk (x + s • v) t))) -
        fun s ↦ ℓ (φ (slabMk (x + s • v) ⟨a, left_mem_Icc.2 hab.le⟩)) :=
      funext fun s ↦ integral_timeExtension_eq_sub hab hχ hφt ℓ _ t
    rw [← hfun] at h
    simpa only [g', zero_smul, add_zero] using h.unique hint
  · refine (ℓ.le_opNorm _).trans ?_
    rw [mul_assoc]
    gcongr
    have hτ' : τ ∈ Icc a b := by
      rw [uIoc_of_le t.2.1] at hτ
      exact ⟨hτ.1.le, hτ.2.trans t.2.2⟩
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (hM (s, τ) ⟨Metric.ball_subset_closedBall hs, hτ'⟩) (norm_nonneg v))
  · have hd := (hχx (projIcc a b hab.le τ) (x + s • v)).comp_hasDerivAt s (hline s)
    simp only [g, g', timeExtension_def]
    exact ℓ.hasFDerivAt.comp_hasDerivAt s hd

/-- **Symmetry of the mixed space-time derivatives on a slab.** Let `φ` have spatial Fréchet
derivative `ψ` and time derivative `χ` within `[a, b]` at every point of the slab `E × [a, b]`.
If `χ` is continuous with a continuous spatial derivative `χ₁`, and `ψ` has a time derivative `ψ₁`
within `[a, b]`, then `ψ₁ = χ₁`: the time derivative of `D_x φ` is the spatial derivative of
`∂ₜφ`. -/
theorem eq_of_hasFDerivAt_of_hasDerivWithinAt_slab (hab : a < b) (hχ : Continuous χ)
    (hχ₁ : Continuous χ₁)
    (hφx : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ φ (slabMk y t)) (ψ (slabMk x t)) x)
    (hφt : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
      (timeExtension hab.le φ x) (χ (slabMk x t)) (Icc a b) t)
    (hψt : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
      (timeExtension hab.le ψ x) (ψ₁ (slabMk x t)) (Icc a b) t)
    (hχx : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ χ (slabMk y t)) (χ₁ (slabMk x t)) x) :
    ψ₁ = χ₁ := by
  -- Test against a direction `v` and a functional `ℓ`, reducing to real-valued functions.
  suffices key : ∀ (x v : E) (ℓ : StrongDual ℝ F) (t : Icc a b),
      ℓ (ψ₁ (slabMk x t) v) = ℓ (χ₁ (slabMk x t) v) by
    ext p v
    rw [← slabMk_space_slabTime p]
    exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun ℓ ↦ key _ v ℓ _
  intro x v ℓ t
  have hc₂ : Continuous fun τ ↦ ℓ (timeExtension hab.le χ₁ x τ v) :=
    (ℓ.comp (ContinuousLinearMap.apply ℝ F v)).continuous.comp
      (continuous_timeExtension_slice hab.le hχ₁ x)
  -- Within `[a, b]`, `τ ↦ D_x φ (x, τ) v` has derivative `ψ₁ (x, t) v` at `t`, and on `[a, b]` it
  -- is an integral of `χ₁ (x, ·) v` by `sub_eq_integral_timeExtension`, with derivative
  -- `χ₁ (x, t) v`. Derivatives within `[a, b]` are unique, also at its ends.
  let A : ℝ → ℝ := fun τ ↦ ℓ (timeExtension hab.le ψ x τ v)
  have hd₁ : HasDerivWithinAt A (ℓ (ψ₁ (slabMk x t) v)) (Icc a b) t :=
    (ℓ.comp (ContinuousLinearMap.apply ℝ F v)).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
      (hψt x t)
  have hd₂ := ((intervalIntegral.integral_hasDerivAt_right (hc₂.intervalIntegrable a t)
    (hc₂.stronglyMeasurableAtFilter _ _) hc₂.continuousAt).const_add (A a)).hasDerivWithinAt
    (s := Icc a b)
  have heq : ∀ u ∈ Icc a b, A u = A a + ∫ τ in a..u, ℓ (timeExtension hab.le χ₁ x τ v) := by
    intro u hu
    have h := sub_eq_integral_timeExtension hab hχ hχ₁ hφx hφt hχx ℓ x v ⟨u, hu⟩
    have h₁ : timeExtension hab.le ψ x u = ψ (slabMk x ⟨u, hu⟩) :=
      timeExtension_of_mem hab.le ψ x ⟨u, hu⟩
    have h₂ : timeExtension hab.le ψ x a = ψ (slabMk x ⟨a, left_mem_Icc.2 hab.le⟩) :=
      timeExtension_of_mem hab.le ψ x ⟨a, left_mem_Icc.2 hab.le⟩
    simp only [A, h₁, h₂]
    linarith
  have hd := hd₂.congr_of_mem heq t.2
  rw [timeExtension_of_mem] at hd
  exact (uniqueDiffOn_Icc hab t t.2).eq_deriv _ hd₁ hd

end MixedDerivatives

namespace ParabolicCkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {hab : a < b}

/-! ### Currying the last variable -/

variable (E F) in
/-- Separating the last of `m + 1` variables, as a continuous linear map: an `m`-multilinear map
with values in `E →L[ℝ] F` read as an `(m + 1)`-multilinear map. -/
private abbrev uncurryRightL (m : ℕ) : (E [×m]→L[ℝ] (E →L[ℝ] F)) →L[ℝ] E [×(m + 1)]→L[ℝ] F :=
  (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.toLinearIsometry.toContinuousLinearMap

/-- Separating the first variable commutes with `uncurryRightL`. -/
private theorem curryLeft_uncurryRightL_succ {m : ℕ} (M : E [×(m + 1)]→L[ℝ] (E →L[ℝ] F)) :
    (uncurryRightL E F (m + 1) M).curryLeft = (uncurryRightL E F m).comp M.curryLeft :=
  ContinuousLinearMap.ext M.curryLeft_continuousMultilinearCurryRightEquiv'_symm

/-! ### The fields -/

/-- The fields of the map with value `u`, spatial derivative `G` and time derivative `H`: the
spatial derivatives `D_x^(m+1) u` are read off `G`, and the fields with a time derivative off
`H`. -/
private def ofDerivFields (u : slab (E := E) a b →ᵇ F)
    (G : ParabolicCkHolderSpace (k + 1) α E (E →L[ℝ] F) hab)
    (H : ParabolicCkHolderSpace k α E F hab) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.compLeftContinuousBounded _ u
  | 0, m + 1 => (uncurryRightL E F m).compLeftContinuousBounded _ (mixedDerivL 0 m G)
  | r + 1, m => mixedDerivL r m H

variable {u : slab (E := E) a b →ᵇ F} {G : ParabolicCkHolderSpace (k + 1) α E (E →L[ℝ] F) hab}
  {H : ParabolicCkHolderSpace k α E F hab}

private theorem ofDerivFields_zero_zero_apply (p : slab (E := E) a b) :
    ofDerivFields u G H 0 0 p = (continuousMultilinearCurryFin0 ℝ E F).symm (u p) :=
  (rfl)

private theorem ofDerivFields_zero_succ_apply (m : ℕ) (p : slab (E := E) a b) :
    ofDerivFields u G H 0 (m + 1) p = uncurryRightL E F m (mixedDerivL 0 m G p) :=
  (rfl)

private theorem ofDerivFields_succ (r m : ℕ) :
    ofDerivFields u G H (r + 1) m = mixedDerivL r m H :=
  (rfl)

/-- **The mixed derivatives commute.** The time derivatives of the spatial derivatives in `G`
are the spatial derivatives of the time derivative `H`. -/
private theorem uncurryRightL_mixedDerivL_one
    (hG : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ u (slabMk y t)) (G (slabMk x t)) x)
    (hH : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
      (ParabolicC2HolderSpace.timeExtension hab.le u x) (H (slabMk x t)) (Icc a b) t)
    {m : ℕ} (hm : m + 1 ≤ k) (p : slab (E := E) a b) :
    uncurryRightL E F m (mixedDerivL 1 m G p) = mixedDerivL 0 (m + 1) H p := by
  induction m generalizing p with
  | zero =>
    -- The classical symmetry of the mixed derivatives of `u` itself.
    have hsymm := eq_of_hasFDerivAt_of_hasDerivWithinAt_slab hab (φ := u) (ψ := G)
      (χ := ⇑((continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
        |>.compLeftContinuousBounded _ (mixedDerivL 0 0 H)))
      (ψ₁ := ⇑((continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).toLinearIsometry
        |>.toContinuousLinearMap.compLeftContinuousBounded _ (mixedDerivL 1 0 G)))
      (χ₁ := ⇑((continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry.toContinuousLinearMap
        |>.compLeftContinuousBounded _ (mixedDerivL 0 1 H)))
      (BoundedContinuousFunction.continuous _) (BoundedContinuousFunction.continuous _) hG
      (fun x t ↦ ?_) (fun x t ↦ ?_) (fun t x ↦ ?_)
    · have h := congrFun hsymm p
      simp only [ContinuousLinearMap.compLeftContinuousBounded_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry] at h
      rw [uncurryRightL, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry,
        continuousMultilinearCurryRightEquiv'_zero_symm_apply, h,
        LinearIsometryEquiv.symm_apply_apply]
    · simpa [mixedDerivL_zero_zero_eq] using hH x t
    · have hG₀ : ⇑G = continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F) ∘ mixedDerivL 0 0 G :=
        funext fun p ↦ by
          rw [Function.comp_apply, mixedDerivL_zero_zero_eq, LinearIsometryEquiv.apply_symm_apply]
      rw [hG₀, ParabolicC2HolderSpace.timeExtension_comp]
      exact (continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).toLinearIsometry.toContinuousLinearMap
        |>.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
          (hasDerivWithinAt_mixedDerivL G (r := 0) (m := 0) (by omega) x t)
    · have hd := (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
        |>.hasFDerivAt.comp x (hasFDerivAt_mixedDerivL H (r := 0) (m := 0) (by omega) t x)
      convert hd using 1
      · -- Postcomposing with the currying isometry, as a bounded map or pointwise, agrees.
        rfl
      · exact ContinuousLinearMap.ext fun v ↦ by simp
  | succ m ih =>
    -- Both sides are spatial derivatives of the two sides of the previous identity.
    rw [← slabMk_space_slabTime p]
    set t := slabTime p
    set x := (p : ParabolicSpaceTime E).space
    have h₁ := (uncurryRightL E F m).hasFDerivAt.comp x
      (hasFDerivAt_mixedDerivL G (r := 1) (m := m) (by omega) t x)
    have h₂ := hasFDerivAt_mixedDerivL H (r := 0) (m := m + 1) (by omega) t x
    have hfun : (fun y ↦ mixedDerivL 0 (m + 1) H (slabMk y t)) =
        (uncurryRightL E F m) ∘ fun y ↦ mixedDerivL 1 m G (slabMk y t) :=
      funext fun y ↦ (ih (by omega) (slabMk y t)).symm
    rw [hfun] at h₂
    refine Function.LeftInverse.injective ContinuousMultilinearMap.uncurry_curryLeft ?_
    rw [curryLeft_uncurryRightL_succ]
    exact h₁.unique h₂

/-! ### The norm -/

/-- The contribution of the pair `(r, m)` to the norm is at most `2 B + C`, where `B` bounds the
field and `C` is a Hölder constant of its time slices (order `n - 1`) or of the field itself
(order `n`). -/
private theorem norm_add_norm_add_norm_le {n : ℕ} (f : ParabolicCkHolderSpace n α E F hab)
    {r m : ℕ} {B : ℝ} {C : ℝ≥0} (hB : ‖mixedDerivL r m f‖ ≤ B)
    (hs : 2 * r + m + 1 = n → ∀ x : E,
      HolderWith C ((1 + α) / 2) fun t : Icc a b ↦ mixedDerivL r m f (slabMk x t))
    (hh : 2 * r + m = n → HolderWith C α (mixedDerivL r m f : slab (E := E) a b → _)) :
    ‖mixedDerivL r m f‖ + (‖timeSliceL r m f‖ + ‖mixedDerivHolderL r m f‖) ≤ 2 * B + C := by
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  by_cases h₁ : 2 * r + m + 1 = n
  · rw [mixedDerivHolderL_of_ne (by omega), _root_.zero_apply, norm_zero]
    have := norm_timeSliceL_le_of_holderWith f h₁ (hs h₁)
    linarith
  · rw [timeSliceL_of_ne h₁, _root_.zero_apply, norm_zero]
    by_cases h₂ : 2 * r + m = n
    · have hc : ⇑(mixedDerivHolderL r m f) = ⇑(mixedDerivL r m f) :=
        funext (mixedDerivHolderL_apply f h₂)
      have := HolderSpace.norm_le_of_norm_le_of_holderWith (norm_nonneg (mixedDerivL r m f))
        (f := mixedDerivHolderL r m f)
        (fun p ↦ by rw [mixedDerivHolderL_apply f h₂]; exact (mixedDerivL r m f).norm_coe_le_norm p)
        (by rw [hc]; exact hh h₂)
      linarith
    · rw [mixedDerivHolderL_of_ne h₂, _root_.zero_apply, norm_zero]
      linarith [C.coe_nonneg]

section Construction

variable (hG : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ u (slabMk y t)) (G (slabMk x t)) x)
  (hH : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
    (ParabolicC2HolderSpace.timeExtension hab.le u x) (H (slabMk x t)) (Icc a b) t)
include hG hH

omit hH in
private theorem hasFDerivAt_ofDerivFields (r m : ℕ) (h : 2 * r + m + 1 ≤ k + 2) (t : Icc a b)
    (x : E) : HasFDerivAt (fun y ↦ ofDerivFields u G H r m (slabMk y t))
      (ofDerivFields u G H r (m + 1) (slabMk x t)).curryLeft x := by
  rcases r with _ | r
  · rcases m with _ | m
    · have hL (L : E →L[ℝ] F) : (uncurryRightL E F 0
          ((continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).symm L)).curryLeft =
          (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap.comp
            L :=
        ContinuousLinearMap.ext fun v ↦ ContinuousMultilinearMap.ext fun w ↦ by simp
      rw [ofDerivFields_zero_succ_apply, mixedDerivL_zero_zero_eq, hL]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
        |>.hasFDerivAt.comp x (hG t x)
    · rw [ofDerivFields_zero_succ_apply, curryLeft_uncurryRightL_succ]
      exact (uncurryRightL E F m).hasFDerivAt.comp x
        (hasFDerivAt_mixedDerivL G (r := 0) (m := m) (by omega) t x)
  · exact hasFDerivAt_mixedDerivL H (r := r) (m := m) (by omega) t x

private theorem hasDerivWithinAt_ofDerivFields (r m : ℕ) (h : 2 * r + m + 2 ≤ k + 2) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (ofDerivFields u G H r m) x)
      (ofDerivFields u G H (r + 1) m (slabMk x t)) (Icc a b) t := by
  rcases r with _ | r
  · rcases m with _ | m
    · rw [show ⇑(ofDerivFields u G H 0 0) = (continuousMultilinearCurryFin0 ℝ E F).symm ∘ u from
          funext ofDerivFields_zero_zero_apply, ParabolicC2HolderSpace.timeExtension_comp,
        ofDerivFields_succ, mixedDerivL_zero_zero_eq]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
        |>.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hH x t)
    · rw [show ⇑(ofDerivFields u G H 0 (m + 1)) = uncurryRightL E F m ∘ mixedDerivL 0 m G from
          funext (ofDerivFields_zero_succ_apply m), ParabolicC2HolderSpace.timeExtension_comp,
        ofDerivFields_succ, ← uncurryRightL_mixedDerivL_one hG hH (by omega)]
      exact (uncurryRightL E F m).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
        (hasDerivWithinAt_mixedDerivL G (r := 0) (m := m) (by omega) x t)
  · exact hasDerivWithinAt_mixedDerivL H (r := r) (m := m) (by omega) x t

omit hG hH in
private theorem holderWith_ofDerivFields_slabMk (r m : ℕ) (h : 2 * r + m + 1 = k + 2) :
    ∃ C, ∀ x : E, HolderWith C ((1 + α) / 2)
      fun t : Icc a b ↦ ofDerivFields u G H r m (slabMk x t) := by
  rcases r with _ | r
  · rcases m with _ | m
    · omega
    · exact ⟨_, fun x ↦
        (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.comp_holderWith
        (holderWith_mixedDerivL_slabMk G (r := 0) (m := m) (by omega) x)⟩
  · exact ⟨_, holderWith_mixedDerivL_slabMk H (r := r) (m := m) (by omega)⟩

omit hG hH in
private theorem memHolder_ofDerivFields (r m : ℕ) (h : 2 * r + m = k + 2) :
    MemHolder α (ofDerivFields u G H r m : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  rcases r with _ | r
  · rcases m with _ | m
    · omega
    · exact ⟨_, (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.comp_holderWith
        (holderWith_mixedDerivL G (r := 0) (m := m) (by omega))⟩
  · exact ⟨_, holderWith_mixedDerivL H (r := r) (m := m) (by omega)⟩

omit hG hH in
variable (u G H) in
/-- **A parabolic Hölder map from its first derivatives.** A bounded continuous map `u` on the
slab `E × [a, b]` whose spatial derivative `G = D_x u` lies in `C_{par,b}^{(k+1)+α}` and whose time
derivative `H = ∂ₜu` within `[a, b]` lies in `C_{par,b}^{k+α}` lies in `C_{par,b}^{(k+2)+α}`.
Spatial differentiation lowers the parabolic order by one and time differentiation by two, so this
is the converse of differentiating. Its fields are read off `G` and `H`
(`ParabolicCkHolderSpace.mixedDerivL_zero_succ_ofSpatialFDerivTimeDeriv`,
`ParabolicCkHolderSpace.mixedDerivL_succ_ofSpatialFDerivTimeDeriv`). -/
def ofSpatialFDerivTimeDeriv
    (hG : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ u (slabMk y t)) (G (slabMk x t)) x)
    (hH : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
      (ParabolicC2HolderSpace.timeExtension hab.le u x) (H (slabMk x t)) (Icc a b) t) :
    ParabolicCkHolderSpace (k + 2) α E F hab :=
  mk (ofDerivFields u G H) (hasFDerivAt_ofDerivFields hG)
    (hasDerivWithinAt_ofDerivFields hG hH) holderWith_ofDerivFields_slabMk memHolder_ofDerivFields

/-- The map built from its first derivatives is the map. -/
@[simp]
theorem ofSpatialFDerivTimeDeriv_apply (p : slab (E := E) a b) :
    ofSpatialFDerivTimeDeriv u G H hG hH p = u p := by
  rw [ofSpatialFDerivTimeDeriv, mk_apply, ofDerivFields_zero_zero_apply]
  exact (continuousMultilinearCurryFin0 ℝ E F).apply_symm_apply (u p)

/-- The spatial derivatives `D_x^(m+1) u` of the map built from its first derivatives are the
fields `D_x^m G` of its spatial derivative `G`, with the last variable uncurried. -/
theorem mixedDerivL_zero_succ_ofSpatialFDerivTimeDeriv {m : ℕ} (hm : m ≤ k + 1)
    (p : slab (E := E) a b) :
    mixedDerivL 0 (m + 1) (ofSpatialFDerivTimeDeriv u G H hG hH) p =
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm (mixedDerivL 0 m G p) := by
  rw [ofSpatialFDerivTimeDeriv, mixedDerivL_mk _ _ _ _ (by omega), ofDerivFields_zero_succ_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]

/-- The fields `D_t^(r+1) D_x^m u` of the map built from its first derivatives are the fields
`D_t^r D_x^m H` of its time derivative `H`. -/
theorem mixedDerivL_succ_ofSpatialFDerivTimeDeriv {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL (r + 1) m (ofSpatialFDerivTimeDeriv u G H hG hH) = mixedDerivL r m H := by
  rw [ofSpatialFDerivTimeDeriv, mixedDerivL_mk _ _ _ _ (by omega), ofDerivFields_succ]

/-- The contribution of each pair `(r, m)` to the norm of the map built from its first
derivatives is at most `4 (‖u‖ + ‖G‖ + ‖H‖)`. -/
private theorem norm_add_norm_add_norm_ofSpatialFDerivTimeDeriv_le :
    ∀ p ∈ parabolicDerivPairs (k + 2),
      ‖mixedDerivL p.1 p.2 (ofSpatialFDerivTimeDeriv u G H hG hH)‖ +
        (‖timeSliceL p.1 p.2 (ofSpatialFDerivTimeDeriv u G H hG hH)‖ +
          ‖mixedDerivHolderL p.1 p.2 (ofSpatialFDerivTimeDeriv u G H hG hH)‖) ≤
        4 * (‖u‖ + ‖G‖ + ‖H‖) := by
  set f := ofSpatialFDerivTimeDeriv u G H hG hH
  rintro ⟨r, m⟩ hp
  have hp' := mem_parabolicDerivPairs.1 hp
  have hfield : mixedDerivL r m f = ofDerivFields u G H r m := mixedDerivL_mk _ _ _ _ hp'
  rcases r with _ | r
  · rcases m with _ | m
    · refine (norm_add_norm_add_norm_le f (B := ‖u‖) (C := 0) ?_ (fun h ↦ by omega)
        (fun h ↦ by omega)).trans
        (by rw [NNReal.coe_zero]; linarith [norm_nonneg u, norm_nonneg G, norm_nonneg H])
      rw [hfield]
      refine (BoundedContinuousFunction.norm_le (norm_nonneg u)).2 fun p ↦ ?_
      rw [ofDerivFields_zero_zero_apply, LinearIsometryEquiv.norm_map]
      exact u.norm_coe_le_norm p
    · have hC : ((‖timeSliceL 0 m G‖₊ + ‖mixedDerivHolderL 0 m G‖₊ : ℝ≥0) : ℝ) ≤ 2 * ‖G‖ := by
        push_cast
        linarith [norm_timeSliceL_le G 0 m, norm_mixedDerivHolderL_le G 0 m]
      refine (norm_add_norm_add_norm_le f (B := ‖G‖)
        (C := ‖timeSliceL 0 m G‖₊ + ‖mixedDerivHolderL 0 m G‖₊) ?_ (fun h x ↦ ?_)
        (fun h ↦ ?_)).trans (by linarith [norm_nonneg u, norm_nonneg H])
      · rw [hfield]
        refine (BoundedContinuousFunction.norm_le (norm_nonneg G)).2 fun p ↦ ?_
        rw [ofDerivFields_zero_succ_apply, LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
        exact ((mixedDerivL 0 m G).norm_coe_le_norm p).trans (norm_mixedDerivL_le G 0 m)
      · rw [hfield]
        exact ((continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.comp_holderWith
          (holderWith_mixedDerivL_slabMk G (r := 0) (m := m) (by omega) x)).mono le_self_add
      · rw [hfield]
        exact ((continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.comp_holderWith
          (holderWith_mixedDerivL G (r := 0) (m := m) (by omega))).mono le_add_self
  · have hC : ((‖timeSliceL r m H‖₊ + ‖mixedDerivHolderL r m H‖₊ : ℝ≥0) : ℝ) ≤ 2 * ‖H‖ := by
      push_cast
      linarith [norm_timeSliceL_le H r m, norm_mixedDerivHolderL_le H r m]
    refine (norm_add_norm_add_norm_le f (B := ‖H‖)
      (C := ‖timeSliceL r m H‖₊ + ‖mixedDerivHolderL r m H‖₊) ?_ (fun h x ↦ ?_)
      (fun h ↦ ?_)).trans (by linarith [norm_nonneg u, norm_nonneg G])
    · rw [hfield, ofDerivFields_succ]
      exact norm_mixedDerivL_le H r m
    · rw [hfield, ofDerivFields_succ]
      exact (holderWith_mixedDerivL_slabMk H (r := r) (m := m) (by omega) x).mono le_self_add
    · rw [hfield, ofDerivFields_succ]
      exact (holderWith_mixedDerivL H (r := r) (m := m) (by omega)).mono le_add_self

/-- **The norm estimate.** The order-`(k + 2)` norm of the map built from its first derivatives is
controlled by the supremum of the map and the norms of its spatial and time derivatives in the
spaces of orders `k + 1` and `k`. -/
theorem norm_ofSpatialFDerivTimeDeriv_le :
    ‖ofSpatialFDerivTimeDeriv u G H hG hH‖ ≤ 4 * (k + 3) ^ 2 * (‖u‖ + ‖G‖ + ‖H‖) := by
  have hc : ((parabolicDerivPairs (k + 2)).card : ℝ) ≤ (k + 3) ^ 2 := by
    exact_mod_cast card_parabolicDerivPairs_le (k + 2)
  have h4 := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 4 * (‖u‖ + ‖G‖ + ‖H‖))
  rw [norm_eq]
  refine (Finset.sum_le_sum (norm_add_norm_add_norm_ofSpatialFDerivTimeDeriv_le hG hH)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  linarith

end Construction

end ParabolicCkHolderSpace

end TauCeti
