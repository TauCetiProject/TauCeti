/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Reverse norm bounds for inducing linear maps

Over a nontrivially normed field `𝕜`, a linear map `f : E →ₗ[𝕜] F` between seminormed spaces that
is topologically inducing (`Topology.IsInducing f`) satisfies a reverse norm bound `‖x‖ ≤ C * ‖f x‖`
for some `C > 0` and is antilipschitz, since the identity map from `E` equipped with the
pulled-back seminorm to `E` is continuous. Neither injectivity, completeness, nor Hausdorffness is
needed.

In particular, this applies to any strict injective linear map (`Topology.IsStrictMap f` and
`Function.Injective f`), such as an injective linear map out of a finite module over a complete
Noetherian Tate ring (`LinearMap.isStrictMap_of_module_finite`).

## Main results

* `LinearMap.exists_pos_norm_le_mul_norm_of_isInducing`: if `f : E →ₗ[𝕜] F` is topologically
  inducing, then `∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖f x‖`.
* `LinearMap.exists_antilipschitzWith_of_isInducing`: the corresponding `AntilipschitzWith` bound.
* `LinearMap.exists_pos_norm_le_mul_norm_of_isStrictMap_of_injective`: the same bound for a strict
  injective linear map.
-/

public section

open Topology

namespace LinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

private structure PulledBack (E : Type*) where
  val : E

private instance {E : Type*} [AddCommGroup E] : AddCommGroup (PulledBack E) :=
  letI : Zero (PulledBack E) := ⟨⟨0⟩⟩
  letI : Add (PulledBack E) := ⟨fun x y ↦ ⟨x.val + y.val⟩⟩
  letI : Neg (PulledBack E) := ⟨fun x ↦ ⟨-x.val⟩⟩
  letI : Sub (PulledBack E) := ⟨fun x y ↦ ⟨x.val - y.val⟩⟩
  letI : SMul ℕ (PulledBack E) := ⟨fun n x ↦ ⟨n • x.val⟩⟩
  letI : SMul ℤ (PulledBack E) := ⟨fun n x ↦ ⟨n • x.val⟩⟩
  Function.Injective.addCommGroup PulledBack.val (fun ⟨_⟩ ⟨_⟩ h ↦ congrArg PulledBack.mk h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private instance {𝕜 E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] :
    Module 𝕜 (PulledBack E) :=
  letI : SMul 𝕜 (PulledBack E) := ⟨fun c x ↦ ⟨c • x.val⟩⟩
  Function.Injective.module 𝕜 ⟨⟨PulledBack.val, rfl⟩, fun _ _ ↦ rfl⟩
    (fun ⟨_⟩ ⟨_⟩ h ↦ congrArg PulledBack.mk h) (fun _ _ ↦ rfl)

/-- **An inducing linear map over a nontrivially normed field is bounded below.** If
`f : E →ₗ[𝕜] F` is topologically inducing (`Topology.IsInducing f`), then `‖x‖ ≤ C * ‖f x‖` for a
single constant `C > 0`. Neither injectivity, completeness, nor Hausdorffness is needed. -/
theorem exists_pos_norm_le_mul_norm_of_isInducing (f : E →ₗ[𝕜] F) (hf : IsInducing f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * ‖f x‖ := by
  let p : PulledBack E →ₗ[𝕜] F :=
    { toFun := fun x ↦ f x.val, map_add' := fun _ _ ↦ map_add f _ _,
      map_smul' := fun _ _ ↦ map_smul f _ _ }
  let _ : SeminormedAddCommGroup (PulledBack E) := SeminormedAddCommGroup.induced (PulledBack E) F p
  let _ : NormedSpace 𝕜 (PulledBack E) := NormedSpace.induced 𝕜 (PulledBack E) F p
  let idE : PulledBack E →ₗ[𝕜] E :=
    { toFun := PulledBack.val, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hp_cont : Continuous p := Isometry.continuous (f := p) fun _ _ ↦ rfl
  have hid : Continuous idE := hf.continuous_iff.mpr hp_cont
  obtain ⟨C, hC, hbound⟩ := SemilinearMapClass.bound_of_continuous idE hid
  exact ⟨C, hC, fun x ↦ hbound ⟨x⟩⟩

/-- An inducing linear map over a nontrivially normed field is antilipschitz. -/
theorem exists_antilipschitzWith_of_isInducing (f : E →ₗ[𝕜] F) (hf : IsInducing f) :
    ∃ K : NNReal, 0 < K ∧ AntilipschitzWith K f := by
  obtain ⟨C, hC, hbound⟩ := f.exists_pos_norm_le_mul_norm_of_isInducing hf
  refine ⟨Real.toNNReal C, Real.toNNReal_pos.mpr hC, AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal C hC.le]
  exact hbound (x - y)

/-- **A strict injective linear map over a nontrivially normed field is bounded below.** -/
theorem exists_pos_norm_le_mul_norm_of_isStrictMap_of_injective (f : E →ₗ[𝕜] F)
    (hf : IsStrictMap f) (hinj : Function.Injective f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * ‖f x‖ :=
  f.exists_pos_norm_le_mul_norm_of_isInducing
    (isEmbedding_iff_isStrictMap_injective.mpr ⟨hf, hinj⟩).isInducing

end LinearMap
