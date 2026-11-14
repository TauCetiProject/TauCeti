/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedGradient.Contraction
public import Mathlib.Analysis.InnerProductSpace.Adjoint
-- Private: the Fréchet derivative rules for translations and linear equivalences are used only
-- inside the chain-rule proofs.
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Pullback of iterated gradients along continuous linear maps

A continuous linear map `B : E →L[ℝ] E'` between real Hilbert spaces pulls back iterated gradients
contravariantly in every derivative slot:

* at index `0`, where `TauCeti.IteratedGradient E' 0 = E'` represents a linear functional through
  the inner product, the pullback is the Hilbert-space adjoint `B† : E' →L[ℝ] E`;
* at index `j + 1`, a map `G : E' →L[ℝ] IteratedGradient E' j` is sent to `Pⱼ ∘L G ∘L B`, where
  `Pⱼ` is the pullback at index `j`.

Because `IteratedGradient E' j` represents a derivative of order `j + 1`, its pullback along `B` is
homogeneous of degree `j + 1` in `B` and has operator norm at most `‖B‖ ^ (j + 1)`. Full
contraction (`TauCeti.IteratedGradient.fullContractL`) intertwines the pullback with `B`,
expressing the basis-free directional identity
`(D^{j+1}(f ∘ B)(x))[h, …, h] = (D^{j+1}f(B x))[Bh, …, Bh]`.

When `e : E ≃L[ℝ] E'` is a continuous linear equivalence, the pullbacks along `e` and `e.symm` are
mutually inverse (`ContinuousLinearEquiv.iteratedGradientPullbackEquiv`), and the classical chain
`TauCeti.iteratedGradientChain` transforms unconditionally along `y ↦ e y + b` without any
differentiability assumptions.

## Main declarations

* `ContinuousLinearMap.iteratedGradientPullback`: contravariant pullback of iterated gradients
  along `B : E →L[ℝ] E'`.
* `ContinuousLinearMap.opNorm_iteratedGradientPullback_le`:
  `‖B.iteratedGradientPullback j‖ ≤ ‖B‖ ^ (j + 1)`.
* `ContinuousLinearMap.fullContractL_iteratedGradientPullback`: compatibility with full directional
  contraction.
* `LinearIsometryEquiv.iteratedGradientPullback_coe`: for a linear isometry `e`, the pullback agrees
  with `(e.iteratedGradientCongr j).symm`.
* `ContinuousLinearEquiv.iteratedGradientPullbackEquiv`: the induced continuous linear equivalence
  on `IteratedGradient` along `e : E ≃L[ℝ] E'`.
* `ContinuousLinearEquiv.iteratedGradientChain_comp_right`,
  `ContinuousLinearEquiv.iteratedGradientChain_comp_add`: unconditional chain rules for
  `iteratedGradientChain` along `e` and along an invertible affine map `y ↦ e y + b`.
-/

public section

noncomputable section

open scoped InnerProductSpace

section Pullback

variable {E E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']

namespace ContinuousLinearMap

/-- Contravariant pullback of `TauCeti.IteratedGradient` along `B : E →L[ℝ] E'`. At index `0` this
is the Hilbert-space adjoint `B.adjoint`; at index `j + 1` it sends `G` to
`(B.iteratedGradientPullback j) ∘L G ∘L B`. -/
def iteratedGradientPullback (B : E →L[ℝ] E') :
    (j : ℕ) → TauCeti.IteratedGradient E' j →L[ℝ] TauCeti.IteratedGradient E j
  | 0 => B.adjoint
  | j + 1 =>
      (compL ℝ E (TauCeti.IteratedGradient E' j) (TauCeti.IteratedGradient E j)
        (B.iteratedGradientPullback j)).comp
        ((compL ℝ E E' (TauCeti.IteratedGradient E' j)).flip B)

@[simp]
theorem iteratedGradientPullback_zero (B : E →L[ℝ] E') :
    B.iteratedGradientPullback 0 = B.adjoint :=
  (rfl)

/-- At index `j + 1`, the pullback composes `G` on the right with `B` and on the left with the
index-`j` pullback. -/
theorem iteratedGradientPullback_succ_apply (B : E →L[ℝ] E') (j : ℕ)
    (G : TauCeti.IteratedGradient E' (j + 1)) :
    B.iteratedGradientPullback (j + 1) G =
      ((B.iteratedGradientPullback j).comp (G.comp B) : E →L[ℝ] TauCeti.IteratedGradient E j) :=
  (rfl)

/-- Evaluating a pulled-back iterated gradient of index `j + 1` at a direction `v` evaluates at
`B v` and pulls back the resulting index-`j` field. -/
theorem iteratedGradientPullback_succ_apply_apply (B : E →L[ℝ] E') (j : ℕ)
    (G : TauCeti.IteratedGradient E' (j + 1)) (v : E) :
    B.iteratedGradientPullback (j + 1) G v = B.iteratedGradientPullback j (G (B v)) :=
  (rfl)

@[simp]
theorem iteratedGradientPullback_id (j : ℕ) :
    (ContinuousLinearMap.id ℝ E).iteratedGradientPullback j =
      ContinuousLinearMap.id ℝ (TauCeti.IteratedGradient E j) := by
  induction j with
  | zero => exact adjoint_id
  | succ j ih =>
      ext1 G
      rw [iteratedGradientPullback_succ_apply, ih, id_comp, comp_id, id_apply]

/-- Pullback of iterated gradients is contravariant: `(A ∘L B)* = B* ∘L A*`. -/
theorem iteratedGradientPullback_comp {E'' : Type*} [NormedAddCommGroup E'']
    [InnerProductSpace ℝ E''] [CompleteSpace E''] (A : E' →L[ℝ] E'') (B : E →L[ℝ] E') (j : ℕ) :
    (A.comp B).iteratedGradientPullback j =
      (B.iteratedGradientPullback j).comp (A.iteratedGradientPullback j) := by
  induction j with
  | zero => exact adjoint_comp A B
  | succ j ih =>
      ext1 G
      rw [comp_apply, iteratedGradientPullback_succ_apply, iteratedGradientPullback_succ_apply,
        iteratedGradientPullback_succ_apply, ih]
      ext v
      rfl

/-- Scaling the linear map by `c` scales the index-`j` pullback by `c ^ (j + 1)`, matching the
derivative order `j + 1`. -/
theorem iteratedGradientPullback_smul (c : ℝ) (B : E →L[ℝ] E') (j : ℕ) :
    (c • B).iteratedGradientPullback j = c ^ (j + 1) • B.iteratedGradientPullback j := by
  induction j with
  | zero =>
      rw [pow_one, iteratedGradientPullback_zero, iteratedGradientPullback_zero]
      simp
  | succ j ih =>
      ext1 G
      rw [smul_apply, iteratedGradientPullback_succ_apply, iteratedGradientPullback_succ_apply, ih]
      ext v
      simp only [comp_apply, smul_apply, map_smul, smul_smul, ← pow_succ']

@[simp]
theorem iteratedGradientPullback_zero_map (j : ℕ) :
    (0 : E →L[ℝ] E').iteratedGradientPullback j = 0 := by
  simpa [zero_pow (Nat.succ_ne_zero j)] using
    iteratedGradientPullback_smul 0 (0 : E →L[ℝ] E') j

/-- Pointwise operator-norm bound: pulling back an index-`j` iterated gradient along `B` multiplies
its norm by at most `‖B‖ ^ (j + 1)`. -/
theorem norm_iteratedGradientPullback_apply_le (B : E →L[ℝ] E') (j : ℕ)
    (G : TauCeti.IteratedGradient E' j) :
    ‖B.iteratedGradientPullback j G‖ ≤ ‖B‖ ^ (j + 1) * ‖G‖ := by
  induction j with
  | zero =>
      rw [pow_one, iteratedGradientPullback_zero]
      exact (B.adjoint.le_opNorm G).trans_eq (by rw [LinearIsometryEquiv.norm_map])
  | succ j ih =>
      refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
      calc
        ‖B.iteratedGradientPullback (j + 1) G v‖
            = ‖B.iteratedGradientPullback j (G (B v))‖ := rfl
        _ ≤ ‖B‖ ^ (j + 1) * ‖G (B v)‖ := ih (G (B v))
        _ ≤ ‖B‖ ^ (j + 1) * (‖G‖ * (‖B‖ * ‖v‖)) := by
            gcongr
            exact (G.le_opNorm (B v)).trans
              (mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg _))
        _ = ‖B‖ ^ (j + 1 + 1) * ‖G‖ * ‖v‖ := by rw [pow_succ]; ring

/-- Operator-norm bound: `‖B.iteratedGradientPullback j‖ ≤ ‖B‖ ^ (j + 1)`. -/
theorem opNorm_iteratedGradientPullback_le (B : E →L[ℝ] E') (j : ℕ) :
    ‖B.iteratedGradientPullback j‖ ≤ ‖B‖ ^ (j + 1) :=
  opNorm_le_bound _ (by positivity) (norm_iteratedGradientPullback_apply_le B j)

/-- Partial contraction at direction `h` of a pulled-back iterated gradient equals the pullback of
its partial contraction at `B h`. -/
theorem contractL_iteratedGradientPullback (B : E →L[ℝ] E') (j i : ℕ) (h : E)
    (G : TauCeti.IteratedGradient E' (j + i)) :
    TauCeti.IteratedGradient.contractL j i h (B.iteratedGradientPullback (j + i) G) =
      B.iteratedGradientPullback j (TauCeti.IteratedGradient.contractL j i (B h) G) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [TauCeti.IteratedGradient.contractL_succ, TauCeti.IteratedGradient.contractL_succ,
        comp_apply, comp_apply, apply_apply, apply_apply, ← ih]
      exact congrArg (TauCeti.IteratedGradient.contractL j i h)
        (iteratedGradientPullback_succ_apply_apply B (j + i) G h)

/-- Full directional contraction at `h` of a pulled-back iterated gradient equals full directional
contraction at `B h` of the original field. -/
theorem fullContractL_iteratedGradientPullback (B : E →L[ℝ] E') (j : ℕ) (h : E)
    (G : TauCeti.IteratedGradient E' j) :
    TauCeti.IteratedGradient.fullContractL j h (B.iteratedGradientPullback j G) =
      TauCeti.IteratedGradient.fullContractL j (B h) G := by
  induction j with
  | zero =>
      simp only [TauCeti.IteratedGradient.fullContractL_zero, iteratedGradientPullback_zero,
        innerSL_apply_apply, adjoint_inner_right]
  | succ j ih =>
      rw [TauCeti.IteratedGradient.fullContractL_succ, TauCeti.IteratedGradient.fullContractL_succ,
        comp_apply, comp_apply, apply_apply, apply_apply,
        iteratedGradientPullback_succ_apply_apply, ih]

end ContinuousLinearMap

/-- For a linear isometric equivalence `e`, the general pullback `iteratedGradientPullback` agrees
with `(e.iteratedGradientCongr j).symm`. -/
theorem LinearIsometryEquiv.iteratedGradientPullback_coe (e : E ≃ₗᵢ[ℝ] E') (j : ℕ) :
    (e : E →L[ℝ] E').iteratedGradientPullback j =
      ((e.iteratedGradientCongr j).symm :
        TauCeti.IteratedGradient E' j →L[ℝ] TauCeti.IteratedGradient E j) := by
  induction j with
  | zero =>
      rw [ContinuousLinearMap.iteratedGradientPullback_zero, e.iteratedGradientCongr_zero]
      exact e.adjoint_eq_symm
  | succ j ih =>
      ext1 G
      rw [ContinuousLinearMap.iteratedGradientPullback_succ_apply, ih]
      exact (e.iteratedGradientCongr_symm_succ_apply j G).symm

namespace TauCeti

/-- Classical iterated gradients commute with right translation; no differentiability hypothesis is
needed. -/
theorem iteratedGradientChain_comp_add_right (f : E → ℝ) (b : E) (j : ℕ) (x : E) :
    iteratedGradientChain (fun y ↦ f (y + b)) j x = iteratedGradientChain f j (x + b) := by
  induction j generalizing x with
  | zero =>
      simp only [iteratedGradientChain_zero, gradient, fderiv_comp_add_right]
  | succ j ih =>
      simp only [iteratedGradientChain_succ]
      have hfun : iteratedGradientChain (fun y ↦ f (y + b)) j =
          fun y ↦ iteratedGradientChain f j (y + b) :=
        funext ih
      rw [hfun, fderiv_comp_add_right]

end TauCeti

namespace ContinuousLinearEquiv

/-- The continuous linear equivalence on `TauCeti.IteratedGradient` induced by `e : E ≃L[ℝ] E'`,
whose inverse is the pullback along `e.symm`. -/
def iteratedGradientPullbackEquiv (e : E ≃L[ℝ] E') (j : ℕ) :
    TauCeti.IteratedGradient E' j ≃L[ℝ] TauCeti.IteratedGradient E j :=
  equivOfInverse ((e : E →L[ℝ] E').iteratedGradientPullback j)
    ((e.symm : E' →L[ℝ] E).iteratedGradientPullback j)
    (fun G ↦ by
      have h := congrArg (fun T ↦ T G)
        (ContinuousLinearMap.iteratedGradientPullback_comp
          (e : E →L[ℝ] E') (e.symm : E' →L[ℝ] E) j)
      simpa [coe_comp_coe_symm] using h.symm)
    (fun G ↦ by
      have h := congrArg (fun T ↦ T G)
        (ContinuousLinearMap.iteratedGradientPullback_comp
          (e.symm : E' →L[ℝ] E) (e : E →L[ℝ] E') j)
      simpa [coe_symm_comp_coe] using h.symm)

@[simp]
theorem iteratedGradientPullbackEquiv_apply (e : E ≃L[ℝ] E') (j : ℕ)
    (G : TauCeti.IteratedGradient E' j) :
    e.iteratedGradientPullbackEquiv j G = (e : E →L[ℝ] E').iteratedGradientPullback j G :=
  (rfl)

@[simp]
theorem coe_iteratedGradientPullbackEquiv (e : E ≃L[ℝ] E') (j : ℕ) :
    (e.iteratedGradientPullbackEquiv j :
        TauCeti.IteratedGradient E' j →L[ℝ] TauCeti.IteratedGradient E j) =
      (e : E →L[ℝ] E').iteratedGradientPullback j :=
  (rfl)

@[simp]
theorem iteratedGradientPullbackEquiv_symm (e : E ≃L[ℝ] E') (j : ℕ) :
    (e.iteratedGradientPullbackEquiv j).symm = e.symm.iteratedGradientPullbackEquiv j :=
  (rfl)

/-- Pullback of iterated gradients along the identity continuous linear equivalence is the identity
equivalence. -/
@[simp]
theorem iteratedGradientPullbackEquiv_refl (j : ℕ) :
    (ContinuousLinearEquiv.refl ℝ E).iteratedGradientPullbackEquiv j =
      ContinuousLinearEquiv.refl ℝ (TauCeti.IteratedGradient E j) :=
  ext <| funext fun G ↦ by
    rw [iteratedGradientPullbackEquiv_apply, coe_refl,
      ContinuousLinearMap.iteratedGradientPullback_id]
    rfl

/-- Pullback of iterated gradients as a continuous linear equivalence is contravariant:
`(e₁.trans e₂).iteratedGradientPullbackEquiv j =
  (e₂.iteratedGradientPullbackEquiv j).trans (e₁.iteratedGradientPullbackEquiv j)`. -/
theorem iteratedGradientPullbackEquiv_trans {E'' : Type*} [NormedAddCommGroup E'']
    [InnerProductSpace ℝ E''] [CompleteSpace E''] (e₁ : E ≃L[ℝ] E') (e₂ : E' ≃L[ℝ] E'')
    (j : ℕ) :
    (e₁.trans e₂).iteratedGradientPullbackEquiv j =
      (e₂.iteratedGradientPullbackEquiv j).trans (e₁.iteratedGradientPullbackEquiv j) :=
  ext <| funext fun G ↦ by
    simpa [← comp_coe] using congrArg (fun T ↦ T G)
      (ContinuousLinearMap.iteratedGradientPullback_comp
        (e₂ : E' →L[ℝ] E'') (e₁ : E →L[ℝ] E') j)

/-- Classical iterated gradients transform by `ContinuousLinearMap.iteratedGradientPullback` along
a continuous linear equivalence `e : E ≃L[ℝ] E'`, without any differentiability hypothesis. -/
theorem iteratedGradientChain_comp_right (e : E ≃L[ℝ] E') (f : E' → ℝ) (j : ℕ) (x : E) :
    TauCeti.iteratedGradientChain (f ∘ e) j x =
      (e : E →L[ℝ] E').iteratedGradientPullback j (TauCeti.iteratedGradientChain f j (e x)) := by
  induction j generalizing x with
  | zero =>
      simp only [TauCeti.iteratedGradientChain_zero,
        ContinuousLinearMap.iteratedGradientPullback_zero]
      refine ext_inner_right ℝ fun v ↦ ?_
      rw [gradient, gradient, e.comp_right_fderiv, ContinuousLinearMap.adjoint_inner_left,
        InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply,
        ContinuousLinearMap.comp_apply]
  | succ j ih =>
      simp only [TauCeti.iteratedGradientChain_succ]
      have hfun : TauCeti.iteratedGradientChain (f ∘ e) j =
          (e.iteratedGradientPullbackEquiv j) ∘ (TauCeti.iteratedGradientChain f j ∘ e) :=
        funext ih
      rw [hfun, (e.iteratedGradientPullbackEquiv j).comp_fderiv, e.comp_right_fderiv]
      rfl

/-- Classical iterated gradients transform by `ContinuousLinearMap.iteratedGradientPullback` along
an invertible affine map `y ↦ e y + b`, without any differentiability hypothesis. -/
theorem iteratedGradientChain_comp_add (e : E ≃L[ℝ] E') (b : E') (f : E' → ℝ) (j : ℕ) (x : E) :
    TauCeti.iteratedGradientChain (fun y ↦ f (e y + b)) j x =
      (e : E →L[ℝ] E').iteratedGradientPullback j
        (TauCeti.iteratedGradientChain f j (e x + b)) := by
  have hcomp : (fun y ↦ f (e y + b)) = (fun z ↦ f (z + b)) ∘ e := rfl
  rw [hcomp, e.iteratedGradientChain_comp_right, TauCeti.iteratedGradientChain_comp_add_right]

end ContinuousLinearEquiv

end Pullback
