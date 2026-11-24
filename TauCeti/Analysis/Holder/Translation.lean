/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Translations of bounded `C^{k,α}` functions

For `v : E`, precomposition with the translation `x ↦ x + v` maps the space `CkHolderSpace k α E F`
of bounded `C^{k,α}` functions to itself. Every iterated derivative is translated as well, so the
supremum norms of the derivatives through order `k` and the `α`-Hölder seminorm of the derivative
of order `k` are unchanged. This file packages the translation as a linear isometric equivalence
`TauCeti.CkHolderSpace.translateLIE v`, whose inverse is the translation by `-v`. It moves spatial
initial data along with spatial translations of parabolic problems.
-/

public section
noncomputable section

namespace TauCeti.CkHolderSpace

open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem holderWith_iteratedFDeriv_comp_add_right (v : E) (f : CkHolderSpace k α E F) :
    HolderWith (nnHolderNorm α (_root_.iteratedFDeriv ℝ k f)) α
      (_root_.iteratedFDeriv ℝ k fun x ↦ f (x + v)) := by
  have h := f.memHolder_iteratedFDeriv.holderWith.comp
    (holderWith_one.2 (IsometryEquiv.addRight v).isometry.lipschitzWith)
  simpa [iteratedFDeriv_comp_add_right', Function.comp_def] using h

/-- The translate `x ↦ f (x + v)` of a bounded `C^{k,α}` function. -/
private def translate (v : E) (f : CkHolderSpace k α E F) : CkHolderSpace k α E F :=
  ofContDiff (fun x ↦ f (x + v)) (f.contDiff.comp (contDiff_id.add contDiff_const))
    (fun i hi ↦ ⟨‖f.iteratedFDeriv ⟨i, by omega⟩‖, fun x ↦ by
      rw [iteratedFDeriv_comp_add_right, iteratedFDeriv_eq f ⟨i, by omega⟩]
      exact (f.iteratedFDeriv ⟨i, by omega⟩).norm_coe_le_norm (x + v)⟩)
    (holderWith_iteratedFDeriv_comp_add_right v f).memHolder

private theorem translate_apply (v : E) (f : CkHolderSpace k α E F) (x : E) :
    translate v f x = f (x + v) := by
  simp [translate]

private theorem iteratedFDeriv_translate (v : E) (f : CkHolderSpace k α E F) (i : Fin (k + 1))
    (x : E) : (translate v f).iteratedFDeriv i x = f.iteratedFDeriv i (x + v) := by
  rw [← iteratedFDeriv_eq, ← iteratedFDeriv_eq, translate, coe_ofContDiff,
    iteratedFDeriv_comp_add_right]

private theorem norm_translate_le (v : E) (f : CkHolderSpace k α E F) :
    ‖translate v f‖ ≤ ‖f‖ := by
  have hfield (i : Fin (k + 1)) :
      ‖(translate v f).iteratedFDeriv i‖ ≤ ‖f.iteratedFDeriv i‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg (f.iteratedFDeriv i))).2 fun x ↦ by
      rw [iteratedFDeriv_translate]
      exact (f.iteratedFDeriv i).norm_coe_le_norm (x + v)
  have htop : (nnHolderNorm α (_root_.iteratedFDeriv ℝ k (translate v f)) : ℝ) ≤
      nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) := by
    rw [translate, coe_ofContDiff]
    exact_mod_cast (holderWith_iteratedFDeriv_comp_add_right v f).nnholderNorm_le
  rw [norm_eq, norm_eq]
  exact add_le_add (Finset.sum_le_sum fun i _ ↦ hfield i) htop

variable (k α F) in
/-- The translation `f ↦ f (· + v)` of bounded `C^{k,α}` functions, as a linear isometric
equivalence. Its inverse is the translation by `-v`. -/
def translateLIE (v : E) : CkHolderSpace k α E F ≃ₗᵢ[ℝ] CkHolderSpace k α E F :=
  LinearIsometryEquiv.ofBounds
    { toFun := translate v
      invFun := translate (-v)
      map_add' f g := ext fun x ↦ by simp [translate_apply, coe_add]
      map_smul' c f := ext fun x ↦ by simp [translate_apply, coe_smul]
      left_inv f := ext fun x ↦ by simp [translate_apply]
      right_inv f := ext fun x ↦ by simp [translate_apply] }
    (norm_translate_le v) (norm_translate_le (-v))

private theorem translateLIE_eq_translate (v : E) (f : CkHolderSpace k α E F) :
    translateLIE k α F v f = translate v f :=
  (rfl)

@[simp]
theorem translateLIE_apply (v : E) (f : CkHolderSpace k α E F) (x : E) :
    translateLIE k α F v f x = f (x + v) := by
  rw [translateLIE_eq_translate, translate_apply]

/-- The derivative fields of a translate are the translated derivative fields. -/
@[simp]
theorem iteratedFDeriv_translateLIE (v : E) (f : CkHolderSpace k α E F) (i : Fin (k + 1))
    (x : E) : (translateLIE k α F v f).iteratedFDeriv i x = f.iteratedFDeriv i (x + v) := by
  rw [translateLIE_eq_translate, iteratedFDeriv_translate]

@[simp]
theorem translateLIE_symm (v : E) :
    (translateLIE k α F v).symm = translateLIE k α F (-v) := by
  ext f x
  rfl

@[simp]
theorem translateLIE_zero (f : CkHolderSpace k α E F) : translateLIE k α F (0 : E) f = f := by
  ext x
  simp

end TauCeti.CkHolderSpace
