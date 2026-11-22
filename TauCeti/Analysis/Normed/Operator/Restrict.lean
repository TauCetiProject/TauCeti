/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Restricting bounded operators to submodules

The restriction of a bounded operator `T` to a submodule `M` is `T ∘L M.subtypeL`. Its norm
decreases as the submodule shrinks, and passing to the topological closure of `M` does not
change it, since the bound `‖T x‖ ≤ C ‖x‖` cuts out a closed set. Over a densely normed field,
the norm of the restriction is the supremum of `‖T x‖` over the vectors `x ∈ M` with `‖x‖ ≤ 1`.
An operator within distance `1` of one fixing `M` restricts to an injective map on `M`
(`ContinuousLinearMap.injective_comp_subtypeL_of_norm_sub_lt_one`).

A bounded bilinear action preserving a submodule restricts to a bounded action on that
submodule, with operator norm at most that of the original action.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 B E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup B] [NormedSpace 𝕜 B]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

section Subspace

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Restricting to a smaller submodule does not increase the norm of the restriction. -/
theorem nnnorm_comp_subtypeL_mono (T : E →L[𝕜] F) {M N : Submodule 𝕜 E} (h : M ≤ N) :
    ‖T ∘L M.subtypeL‖₊ ≤ ‖T ∘L N.subtypeL‖₊ :=
  opNNNorm_le_bound _ _ fun x ↦ (T ∘L N.subtypeL).le_opNNNorm ⟨x, h x.property⟩

/-- The restriction to the closure of a submodule has the same norm as the restriction to the
submodule itself. -/
theorem nnnorm_comp_subtypeL_topologicalClosure (T : E →L[𝕜] F) (M : Submodule 𝕜 E) :
    ‖T ∘L M.topologicalClosure.subtypeL‖₊ = ‖T ∘L M.subtypeL‖₊ := by
  refine le_antisymm (opNNNorm_le_bound _ _ fun x ↦ ?_)
    (T.nnnorm_comp_subtypeL_mono M.le_topologicalClosure)
  have hclosed : IsClosed {y : E | ‖T y‖₊ ≤ ‖T ∘L M.subtypeL‖₊ * ‖y‖₊} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hx : (x : E) ∈ closure (M : Set E) := M.topologicalClosure_coe ▸ x.property
  exact closure_minimal (fun y hy ↦ (T ∘L M.subtypeL).le_opNNNorm ⟨y, hy⟩) hclosed hx

end Subspace

section Injective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An operator within distance `1` of an operator fixing a submodule `M` is injective on `M`. -/
theorem injective_comp_subtypeL_of_norm_sub_lt_one {P P₀ : E →L[𝕜] E} {M : Submodule 𝕜 E}
    (hP₀ : ∀ v : M, P₀ v = v) (h : ‖P₀ - P‖ < 1) : Function.Injective (P ∘L M.subtypeL) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  rw [comp_apply, Submodule.subtypeL_apply] at hv
  by_contra hv0
  have hv0' : 0 < ‖(v : E)‖ := norm_pos_iff.2 fun h ↦ hv0 (Subtype.ext h)
  have hle : ‖(v : E)‖ ≤ ‖P₀ - P‖ * ‖(v : E)‖ :=
    calc ‖(v : E)‖ = ‖(P₀ - P) v‖ := by rw [sub_apply, hP₀ v, hv, sub_zero]
      _ ≤ ‖P₀ - P‖ * ‖(v : E)‖ := (P₀ - P).le_opNorm _
  exact lt_irrefl _ (hle.trans_lt (mul_lt_of_lt_one_left hv0' h))

end Injective

section DenselyNormed

variable {𝕜 E F : Type*} [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric in
/-- **Closed-unit-ball form of the restricted norm.** Over a densely normed field, the norm of
the restriction of `T` to a submodule `M` is the supremum of `‖T x‖` over the vectors `x ∈ M` with
`‖x‖ ≤ 1`, read in the ambient space. -/
theorem sSup_image_inter_unitClosedBall_eq_nnNorm_comp_subtypeL (T : E →L[𝕜] F)
    (M : Submodule 𝕜 E) :
    sSup ((fun x ↦ ‖T x‖₊) '' ((M : Set E) ∩ closedBall 0 1)) = ‖T ∘L M.subtypeL‖₊ := by
  have hM : (M : Set E) ∩ closedBall 0 1 = (↑) '' closedBall (0 : M) 1 := by
    simp [Set.inter_comm]
  rw [hM, Set.image_image, ← (T ∘L M.subtypeL).sSup_unitClosedBall_eq_nnNorm]
  simp

end DenselyNormed

/-- Restrict a bounded bilinear action to a submodule that it preserves. -/
noncomputable def restrictAction (M : B →L[𝕜] E →L[𝕜] E) (p : Submodule 𝕜 E)
    (hM : ∀ a x, x ∈ p → M a x ∈ p) : B →L[𝕜] p →L[𝕜] p :=
  LinearMap.mkContinuous
    { toFun a := (M a).restrict (hM a)
      map_add' a b := by ext x; exact congrArg (fun f ↦ f x.val) (map_add M a b)
      map_smul' c a := by
        ext x
        exact congrArg (fun f ↦ f x.val) (map_smul M c a) }
    ‖M‖ fun a ↦ by
      apply opNorm_le_bound _ (by positivity)
      intro x
      exact M.le_opNorm₂ a x.val

/-- The restricted action agrees with the original action after inclusion. -/
@[simp]
theorem coe_restrictAction_apply (M : B →L[𝕜] E →L[𝕜] E) (p : Submodule 𝕜 E)
    (hM : ∀ a x, x ∈ p → M a x ∈ p) (a : B) (x : p) :
    (M.restrictAction p hM a x : E) = M a x := (rfl)

/-- Restricting a bounded action to an invariant submodule does not increase its norm. -/
theorem norm_restrictAction_le (M : B →L[𝕜] E →L[𝕜] E) (p : Submodule 𝕜 E)
    (hM : ∀ a x, x ∈ p → M a x ∈ p) : ‖M.restrictAction p hM‖ ≤ ‖M‖ := by
  apply opNorm_le_bound₂ _ (norm_nonneg _)
  intro a x
  exact M.le_opNorm₂ a x.val

/-- Restriction to an invariant submodule preserves the left-action law. -/
theorem restrictAction_mul_apply_of_left [Mul B] {L : B →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (p : Submodule 𝕜 E)
    (hLp : ∀ a x, x ∈ p → L a x ∈ p) (a b : B) (x : p) :
    L.restrictAction p hLp (a * b) x =
      L.restrictAction p hLp a (L.restrictAction p hLp b x) :=
  Subtype.ext (by simp only [coe_restrictAction_apply, hL])

/-- Restriction to an invariant submodule preserves the right-action law. -/
theorem restrictAction_mul_apply_of_right [Mul B] {R : B →L[𝕜] E →L[𝕜] E}
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (p : Submodule 𝕜 E)
    (hRp : ∀ a x, x ∈ p → R a x ∈ p) (a b : B) (x : p) :
    R.restrictAction p hRp (a * b) x =
      R.restrictAction p hRp b (R.restrictAction p hRp a x) :=
  Subtype.ext (by simp only [coe_restrictAction_apply, hR])

/-- Restriction to a jointly invariant submodule preserves commutativity of two actions. -/
theorem restrictAction_apply_comm {L R : B →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (p : Submodule 𝕜 E)
    (hLp : ∀ a x, x ∈ p → L a x ∈ p) (hRp : ∀ a x, x ∈ p → R a x ∈ p) (a b : B) (x : p) :
    L.restrictAction p hLp a (R.restrictAction p hRp b x) =
      R.restrictAction p hRp b (L.restrictAction p hLp a x) :=
  Subtype.ext (by simp only [coe_restrictAction_apply, hLR])

end ContinuousLinearMap
