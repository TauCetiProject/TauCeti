/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator
public import TauCeti.Analysis.PDE.Parabolic.Holder.Restriction
public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace

/-!
# Backward parabolic operators and time reversal

For coefficient fields `A`, `B`, `C` in the bounded parabolic Hölder space `C_b^{α,α/2}` on the
slab `E × [a, b]`, the *backward* parabolic operator is

`P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u`,

a bounded linear map from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. A backward equation
`P_back u = g` is posed with *terminal* data `u(·, b)`.

Time reversal `R (x, s) = (x, T - s)` maps the slab `E × [T - b, T - a]` isometrically onto
`E × [a, b]`. For `v = u ∘ R` and reversed coefficients `Ã = A ∘ R`, `B̃ = B ∘ R`, `C̃ = C ∘ R`,
the time derivative changes sign while the spatial derivatives do not, so

`P̃ v = -(P_back u) ∘ R`,

where `P̃ = ∂ₜ - Ã·D_x² - B̃·D_x - C̃` is the forward operator with the reversed coefficients.
Hence `P_back u = g` exactly when `P̃ v = -g ∘ R`, and the initial trace `v(·, T - b)` is the
terminal trace `u(·, b)`. Terminal-value problems for backward equations are thereby initial-value
problems for forward equations. Here this gives the a priori bounds and uniqueness for the
terminal-value problem on `ℝⁿ` from the whole-space comparison principle for the forward
operator.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.backwardOperatorL`: the backward operator `∂ₜ + L`, with its
  operator bound and Lipschitz dependence on the coefficients.
* `TauCeti.ParabolicC2HolderSpace.parabolicOperatorL_timeReverseLIE` and
  `TauCeti.ParabolicC2HolderSpace.backwardOperatorL_eq_iff`: time reversal exchanges the
  backward operator and the forward operator with reversed coefficients.
* `TauCeti.ParabolicC2HolderSpace.spatialTrace_timeReverseLIE_left`: the initial trace of the
  reversed map is the terminal trace of the original one.
* `TauCeti.ParabolicC2HolderSpace.euclideanBackwardOperatorL`: the backward operator
  `∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` with scalar coefficients on `ℝⁿ`.
* `TauCeti.ParabolicC2HolderSpace.abs_le_exp_mul_mul_add_mul_of_abs_euclideanBackwardOperatorL_le`
  and `TauCeti.ParabolicC2HolderSpace.eq_of_euclideanBackwardOperatorL_eq`: the a priori bound
  and uniqueness for the terminal-value problem.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapters 3 and 4.
* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local shortcut for the norm on Hessians, needed for the coefficient space of the
second-order term for the reason explained in `TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-! ### The backward operator -/

section General

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The backward parabolic operator `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` with coefficient
fields in `C_b^{α,α/2}`, as a continuous linear map from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. -/
def backwardOperatorL (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
    (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)) :
    ParabolicC2HolderSpace α E F ht →L[ℝ] HolderSpace α (slab (E := E) t₀ t₁) F :=
  timeDerivL + spatialOperatorL hα A B C

variable (hα : α ≤ 1)
  {A A' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B B' : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F)}
  {C C' : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)}

theorem backwardOperatorL_def :
    backwardOperatorL (ht := ht) hα A B C = timeDerivL + spatialOperatorL hα A B C := (rfl)

@[simp]
theorem backwardOperatorL_apply (u : ParabolicC2HolderSpace α E F ht)
    (p : slab (E := E) t₀ t₁) :
    backwardOperatorL hα A B C u p =
      timeDerivL u p + (A p (spatialSecondFDerivL u p) + B p (spatialFDerivL u p) +
        C p (u p)) := by
  simp [backwardOperatorL]

/-- The difference of two backward operators is the spatial operator of the difference of their
coefficients. -/
theorem backwardOperatorL_sub_backwardOperatorL :
    backwardOperatorL (ht := ht) hα A B C - backwardOperatorL hα A' B' C' =
      spatialOperatorL hα (A - A') (B - B') (C - C') := by
  rw [spatialOperatorL_sub, backwardOperatorL_def, backwardOperatorL_def]
  abel

/-- **The operator bound for the backward operator.**
`‖P_back‖ ≤ 1 + ‖A‖ + 24 (‖B‖ + ‖C‖)`, uniformly over the spaces and the slab. -/
theorem norm_backwardOperatorL_le :
    ‖backwardOperatorL (ht := ht) hα A B C‖ ≤ 1 + ‖A‖ + 24 * (‖B‖ + ‖C‖) := by
  rw [backwardOperatorL_def, add_assoc]
  exact (norm_add_le _ _).trans (add_le_add norm_timeDerivL_le_one (norm_spatialOperatorL_le hα))

/-- **Lipschitz dependence on the coefficients.** In operator norm,
`‖P_back_{A,B,C} - P_back_{A',B',C'}‖ ≤ ‖A - A'‖ + 24 (‖B - B'‖ + ‖C - C'‖)`. -/
theorem norm_backwardOperatorL_sub_le :
    ‖backwardOperatorL (ht := ht) hα A B C - backwardOperatorL hα A' B' C'‖ ≤
      ‖A - A'‖ + 24 * (‖B - B'‖ + ‖C - C'‖) := by
  rw [backwardOperatorL_sub_backwardOperatorL]
  exact norm_spatialOperatorL_le hα

end General

/-! ### Time reversal -/

section TimeReversal

variable {a b a' b' T : ℝ} {hab : a < b} {ha : a' = T - b} {hb : b' = T - a} (hα : α ≤ 1)
  {A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)}
  {B : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] F) →L[ℝ] F)}
  {C : HolderSpace α (slab (E := E) a b) (F →L[ℝ] F)}

omit [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- Reversing the time of a Hölder field is injective: evaluate at `R⁻¹ q`. -/
private theorem compLipschitzL_slabTimeReverse_injective {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] :
    Function.Injective (HolderSpace.compLipschitzL (α := α) (Y := G) _
      (slabTimeReverse (E := E) T ha hb).isometry.lipschitzWith) := fun f g h ↦
  HolderSpace.ext fun q ↦ by
    simpa only [HolderSpace.compLipschitzL_apply, IsometryEquiv.apply_symm_apply] using
      congrArg (fun f ↦ f ((slabTimeReverse T ha hb).symm q)) h

/-- **Time reversal turns the backward operator into a forward one.** For `v = u ∘ R` with
`R (x, s) = (x, T - s)`, the forward operator with the reversed coefficients `A ∘ R`, `B ∘ R`,
`C ∘ R` satisfies `P̃ v = -(P_back u) ∘ R`. -/
theorem parabolicOperatorL_timeReverseLIE (u : ParabolicC2HolderSpace α E F hab) :
    parabolicOperatorL hα
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith A)
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith B)
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
        (timeReverseLIE T ha hb u) =
      -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (backwardOperatorL hα A B C u) := by
  ext p
  simp only [parabolicOperatorL_apply, backwardOperatorL_apply, timeDerivL_timeReverseLIE,
    spatialSecondFDerivL_timeReverseLIE, spatialFDerivL_timeReverseLIE, timeReverseLIE_apply,
    HolderSpace.compLipschitzL_apply, HolderSpace.neg_apply]
  abel

/-- **Time reversal turns a forward operator into a backward one.** For `v = u ∘ R` with
`R (x, s) = (x, T - s)`, the backward operator with the reversed coefficients `A ∘ R`, `B ∘ R`,
`C ∘ R` satisfies `P̃_back v = -(P u) ∘ R`. -/
theorem backwardOperatorL_timeReverseLIE (u : ParabolicC2HolderSpace α E F hab) :
    backwardOperatorL hα
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith A)
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith B)
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
        (timeReverseLIE T ha hb u) =
      -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (parabolicOperatorL hα A B C u) := by
  ext p
  simp only [parabolicOperatorL_apply, backwardOperatorL_apply, timeDerivL_timeReverseLIE,
    spatialSecondFDerivL_timeReverseLIE, spatialFDerivL_timeReverseLIE, timeReverseLIE_apply,
    HolderSpace.compLipschitzL_apply, HolderSpace.neg_apply]
  abel

/-- **The backward equation is a reversed forward equation.** `P_back u = g` exactly when
`P̃ (u ∘ R) = -g ∘ R`, where `P̃` is the forward operator with the reversed coefficients. -/
theorem backwardOperatorL_eq_iff (u : ParabolicC2HolderSpace α E F hab)
    (g : HolderSpace α (slab (E := E) a b) F) :
    backwardOperatorL hα A B C u = g ↔
      parabolicOperatorL hα
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith A)
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith B)
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
          (timeReverseLIE T ha hb u) =
        -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith g := by
  rw [parabolicOperatorL_timeReverseLIE, neg_inj, compLipschitzL_slabTimeReverse_injective.eq_iff]

/-- The time slice of the reversed map at time `t` is the time slice of the original map at
time `T - t`. -/
@[simp]
theorem spatialTrace_timeReverseLIE (u : ParabolicC2HolderSpace α E F hab) (t : Icc a' b') :
    (timeReverseLIE T ha hb u).spatialTrace t = u.spatialTrace ⟨T - t, by
      obtain ⟨h₁, h₂⟩ := t.2
      subst ha hb
      constructor <;> linarith⟩ := by
  ext x
  simp

/-- **Initial trace of the reversed map.** The initial trace `v(·, T - b)` of `v = u ∘ R` is the
terminal trace `u(·, b)`. -/
theorem spatialTrace_timeReverseLIE_left (u : ParabolicC2HolderSpace α E F hab) :
    (timeReverseLIE T ha hb u).spatialTrace
        ⟨a', left_mem_Icc.2 (ha ▸ hb ▸ sub_lt_sub_left hab T).le⟩ =
      u.spatialTrace ⟨b, right_mem_Icc.2 hab.le⟩ := by
  rw [spatialTrace_timeReverseLIE]
  congr
  simp [ha]

end TimeReversal

/-! ### Reversal of time about the midpoint of a slab -/

section Midpoint

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The left endpoint relation under which reversal of time about `t₀ + t₁` maps the slab
`E × [t₀, t₁]` onto itself. -/
private theorem left_eq_add_sub : t₀ = t₀ + t₁ - t₁ := (add_sub_cancel_right t₀ t₁).symm

/-- The right endpoint relation under which reversal of time about `t₀ + t₁` maps the slab
`E × [t₀, t₁]` onto itself. -/
private theorem right_eq_add_sub : t₁ = t₀ + t₁ - t₀ := (add_sub_cancel_left t₀ t₁).symm

omit [NormedSpace ℝ E] in
/-- Under reversal of time about `t₀ + t₁`, the elapsed time from `t₀` becomes the remaining time
to `t₁`. -/
private theorem slabTime_slabTimeReverse_sub (p : slab (E := E) t₀ t₁) :
    (slabTime ((slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).symm p) : ℝ) - t₀ =
      t₁ - slabTime p := by
  simp only [slabTimeReverse_symm, coe_slabTime, coe_slabTimeReverse, time_timeReverse]
  ring

/-- Under reversal of time about `t₀ + t₁`, the initial slice of the reversed map is the
terminal slice of the original one. -/
private theorem timeReverseLIE_slabMk_left (u : ParabolicC2HolderSpace α E F ht) (x : E) :
    timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub u
        (slabMk x ⟨t₀, left_mem_Icc.2 ht.le⟩) =
      u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  rw [timeReverseLIE_apply, slabTimeReverse_slabMk]
  congr
  exact add_sub_cancel_left t₀ t₁

end Midpoint

/-! ### Coordinate coefficients on Euclidean space -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Operator

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- The backward parabolic operator `P_back u = ∂ₜu + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` on
`ℝⁿ = EuclideanSpace ℝ ι` with scalar coefficients `aⁱʲ`, `bⁱ`, `c` in `C_b^{α,α/2}`, as a
continuous linear map from `C_b^{2+α,1+α/2}` to `C_b^{α,α/2}`. It is `∂ₜ + L`, where
`L = ∂ₜ - P` is the spatial part of the forward operator `P = euclideanParabolicOperatorL`. -/
def euclideanBackwardOperatorL (hα : α ≤ 1)
    (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
    (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ) :
    ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht →L[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ :=
  timeDerivL + (timeDerivL - euclideanParabolicOperatorL hα a b c)

variable (hα : α ≤ 1) {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}

theorem euclideanBackwardOperatorL_def :
    euclideanBackwardOperatorL (ht := ht) hα a b c =
      timeDerivL + (timeDerivL - euclideanParabolicOperatorL hα a b c) := (rfl)

@[simp]
theorem euclideanBackwardOperatorL_apply
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    euclideanBackwardOperatorL hα a b c u p = timeDerivL u p +
      (∑ i, ∑ j, a i j p * spatialSecondFDerivL u p (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + ∑ i, b i p * spatialFDerivL u p (EuclideanSpace.single i 1) +
        c p * u p) := by
  simp only [euclideanBackwardOperatorL, _root_.add_apply, _root_.sub_apply,
    HolderSpace.add_apply, HolderSpace.sub_apply, euclideanParabolicOperatorL_apply]
  ring

end Operator

section TimeReversal

variable {a b a' b' T : ℝ} {hab : a < b} {ha : a' = T - b} {hb : b' = T - a} (hα : α ≤ 1)
  {A : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) a b) ℝ}
  {B : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) a b) ℝ}
  {C : HolderSpace α (slab (E := EuclideanSpace ℝ ι) a b) ℝ}

/-- **Time reversal turns the backward operator into a forward one**, for scalar coefficients on
`ℝⁿ`: with the reversed coefficients `aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`, the forward operator of
`v = u ∘ R` is `-(P_back u) ∘ R`. -/
theorem euclideanParabolicOperatorL_timeReverseLIE
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab) :
    euclideanParabolicOperatorL hα
        (fun i j ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (A i j))
        (fun i ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (B i))
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
        (timeReverseLIE T ha hb u) =
      -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (euclideanBackwardOperatorL hα A B C u) := by
  ext p
  simp only [euclideanParabolicOperatorL_apply, euclideanBackwardOperatorL_apply,
    timeDerivL_timeReverseLIE, spatialSecondFDerivL_timeReverseLIE,
    spatialFDerivL_timeReverseLIE, timeReverseLIE_apply, HolderSpace.compLipschitzL_apply,
    HolderSpace.neg_apply]
  ring

/-- **Time reversal turns a forward operator into a backward one**, for scalar coefficients on
`ℝⁿ`: with the reversed coefficients `aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`, the backward operator of
`v = u ∘ R` is `-(P u) ∘ R`. -/
theorem euclideanBackwardOperatorL_timeReverseLIE
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab) :
    euclideanBackwardOperatorL hα
        (fun i j ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (A i j))
        (fun i ↦ HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
          (B i))
        (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
        (timeReverseLIE T ha hb u) =
      -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith
        (euclideanParabolicOperatorL hα A B C u) := by
  ext p
  simp only [euclideanParabolicOperatorL_apply, euclideanBackwardOperatorL_apply,
    timeDerivL_timeReverseLIE, spatialSecondFDerivL_timeReverseLIE,
    spatialFDerivL_timeReverseLIE, timeReverseLIE_apply, HolderSpace.compLipschitzL_apply,
    HolderSpace.neg_apply]
  ring

/-- **The backward equation is a reversed forward equation**, for scalar coefficients on `ℝⁿ`:
`P_back u = g` exactly when `P̃ (u ∘ R) = -g ∘ R`, where `P̃` is the forward operator with the
reversed coefficients `aⁱʲ ∘ R`, `bⁱ ∘ R`, `c ∘ R`. -/
theorem euclideanBackwardOperatorL_eq_iff
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ hab)
    (g : HolderSpace α (slab (E := EuclideanSpace ℝ ι) a b) ℝ) :
    euclideanBackwardOperatorL hα A B C u = g ↔
      euclideanParabolicOperatorL hα
          (fun i j ↦ HolderSpace.compLipschitzL _
            (slabTimeReverse T ha hb).isometry.lipschitzWith (A i j))
          (fun i ↦ HolderSpace.compLipschitzL _
            (slabTimeReverse T ha hb).isometry.lipschitzWith (B i))
          (HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith C)
          (timeReverseLIE T ha hb u) =
        -HolderSpace.compLipschitzL _ (slabTimeReverse T ha hb).isometry.lipschitzWith g := by
  rw [euclideanParabolicOperatorL_timeReverseLIE, neg_inj,
    compLipschitzL_slabTimeReverse_injective.eq_iff]

end TimeReversal

/-! ### The terminal-value problem on `ℝⁿ` -/

section Terminal

variable {t₀ t₁ : ℝ} {ht : t₀ < t₁} (hα : α ≤ 1)
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ}

/-- **The one-sided a priori bound for the terminal-value problem.** Let `a` be degenerate
elliptic and `c ≤ γ` with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` satisfies
`-K ≤ P_back u` and `u(·, t₁) ≤ M` with `0 ≤ M` and `0 ≤ K`, then
`u(x, t) ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. -/
theorem le_exp_mul_mul_add_mul_of_neg_le_euclideanBackwardOperatorL
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ) {M K : ℝ} (hM : 0 ≤ M) (hK : 0 ≤ K)
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ p, -K ≤ euclideanBackwardOperatorL hα a b c u p)
    (hterm : ∀ x, u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) ≤ M)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    u p ≤ Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  -- Apply the forward bound to the reversal of `u` about `t₀ + t₁`, at the reversed point.
  have key := le_exp_mul_mul_add_mul_of_euclideanParabolicOperatorL_le hα
      (a := fun i j ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (a i j))
      (b := fun i ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (b i))
      (c := HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith c)
    (fun q ξ ↦ by simpa using ha _ ξ) (fun q ↦ by simpa using hc _) hγ hM hK
    (timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub u)
    (fun q ↦ by
      rw [euclideanParabolicOperatorL_timeReverseLIE, HolderSpace.neg_apply,
        HolderSpace.compLipschitzL_apply]
      exact neg_le.1 (hP _))
    (fun x ↦ (timeReverseLIE_slabMk_left u x).trans_le (hterm x))
    ((slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).symm p)
  rwa [slabTime_slabTimeReverse_sub, timeReverseLIE_apply, IsometryEquiv.apply_symm_apply]
    at key

/-- **The a priori bound for the terminal-value problem.** Let `a` be degenerate elliptic and
`c ≤ γ` with `0 ≤ γ`. If `u ∈ C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` satisfies `|P_back u| ≤ K` and
`|u(·, t₁)| ≤ M`, then `|u(x, t)| ≤ exp (γ (t₁ - t)) (M + (t₁ - t) K)`. -/
theorem abs_le_exp_mul_mul_add_mul_of_abs_euclideanBackwardOperatorL_le
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {γ : ℝ} (hc : ∀ p, c p ≤ γ) (hγ : 0 ≤ γ) {M K : ℝ}
    (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
    (hP : ∀ p, |euclideanBackwardOperatorL hα a b c u p| ≤ K)
    (hterm : ∀ x, |u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩)| ≤ M)
    (p : slab (E := EuclideanSpace ℝ ι) t₀ t₁) :
    |u p| ≤ Real.exp (γ * (t₁ - slabTime p)) * (M + (t₁ - slabTime p) * K) := by
  -- Apply the forward bound to the reversal of `u` about `t₀ + t₁`, at the reversed point.
  have key := abs_le_exp_mul_mul_add_mul_of_abs_euclideanParabolicOperatorL_le hα
      (a := fun i j ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (a i j))
      (b := fun i ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (b i))
      (c := HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith c)
    (fun q ξ ↦ by simpa using ha _ ξ) (fun q ↦ by simpa using hc _) hγ
    (timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub u)
    (fun q ↦ by
      rw [euclideanParabolicOperatorL_timeReverseLIE, HolderSpace.neg_apply,
        HolderSpace.compLipschitzL_apply, abs_neg]
      exact hP _)
    (fun x ↦ (timeReverseLIE_slabMk_left u x).symm ▸ hterm x)
    ((slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).symm p)
  rwa [slabTime_slabTimeReverse_sub, timeReverseLIE_apply, IsometryEquiv.apply_symm_apply]
    at key

/-- **Uniqueness for the terminal-value problem.** For degenerate elliptic `a`, an element of
`C_b^{2+α,1+α/2}` on `ℝⁿ × [t₀, t₁]` is determined by `P_back u` and its terminal trace
`u(·, t₁)`. -/
theorem eq_of_euclideanBackwardOperatorL_eq
    (ha : ∀ p (ξ : EuclideanSpace ℝ ι), 0 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ)
    {u v : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht}
    (hP : euclideanBackwardOperatorL hα a b c u = euclideanBackwardOperatorL hα a b c v)
    (hterm : ∀ x, u (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) =
      v (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩)) :
    u = v :=
  (timeReverseLIE (t₀ + t₁) left_eq_add_sub right_eq_add_sub).injective <|
    eq_of_euclideanParabolicOperatorL_eq hα
      (a := fun i j ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (a i j))
      (b := fun i ↦ HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith (b i))
      (c := HolderSpace.compLipschitzL _
        (slabTimeReverse (t₀ + t₁) left_eq_add_sub right_eq_add_sub).isometry.lipschitzWith c)
      (fun q ξ ↦ by simpa using ha _ ξ)
      (by rw [euclideanParabolicOperatorL_timeReverseLIE,
        euclideanParabolicOperatorL_timeReverseLIE, hP])
      (fun x ↦ by rw [timeReverseLIE_slabMk_left, timeReverseLIE_slabMk_left, hterm])

end Terminal

end Euclidean

end TauCeti.ParabolicC2HolderSpace
