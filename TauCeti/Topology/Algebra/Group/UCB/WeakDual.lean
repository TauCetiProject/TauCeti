/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import TauCeti.Topology.Algebra.Group.UCB.Translation

/-!
# Contragredient weak-* action of left translation on `WeakDual ℝ (UCB G)`

For a topological group `G`, left translation `TauCeti.UCB.leftTranslation` acts on `UCB G` by
linear isometries. Precomposing continuous linear functionals with `L_{g⁻¹}` yields the
contragredient left group action

```text
TauCeti.UCB.leftTranslationWeakDual : G →* (WeakDual ℝ (UCB G) ≃L[ℝ] WeakDual ℝ (UCB G))
```

sending `g` to `φ ↦ (f ↦ φ (L_{g⁻¹} f))`. Each operator is weak-* continuous because evaluating at
`f` pulls back to weak-* evaluation at `L_{g⁻¹} f`.

## Main definitions

* `TauCeti.UCB.leftTranslationWeakDual`: the contragredient group action
  `G →* (WeakDual ℝ (UCB G) ≃L[ℝ] WeakDual ℝ (UCB G))` sending `g` to `φ ↦ (f ↦ φ (L_{g⁻¹} f))`.

## Main results

* `TauCeti.UCB.leftTranslationWeakDual_apply`: evaluation formula
  `leftTranslationWeakDual g φ f = φ (leftTranslation g⁻¹ f)`.
* `TauCeti.UCB.leftTranslationWeakDual_symm`: the inverse of `leftTranslationWeakDual g` is
  `leftTranslationWeakDual g⁻¹`.
-/

public section

noncomputable section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace UCB

/-- Auxiliary weak-* continuous linear map precomposing functionals in `WeakDual ℝ (UCB G)` with
`leftTranslation g⁻¹`. -/
private def leftTranslationWeakDualCLM (g : G) : WeakDual ℝ (UCB G) →L[ℝ] WeakDual ℝ (UCB G) where
  toFun φ := StrongDual.toWeakDual
    ((WeakDual.toStrongDual φ).comp
      (leftTranslation g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)
  map_add' _ _ := DFunLike.ext _ _ fun _ => by simp
  map_smul' _ _ := DFunLike.ext _ _ fun _ => by simp
  cont := WeakDual.continuous_of_continuous_eval fun f =>
    WeakDual.eval_continuous (leftTranslation g⁻¹ f)

@[simp]
private theorem leftTranslationWeakDualCLM_apply (g : G) (φ : WeakDual ℝ (UCB G)) (f : UCB G) :
    leftTranslationWeakDualCLM g φ f = φ (leftTranslation g⁻¹ f) := by
  simp [leftTranslationWeakDualCLM, -map_inv]

private theorem leftTranslationWeakDualCLM_one (φ : WeakDual ℝ (UCB G)) :
    leftTranslationWeakDualCLM (1 : G) φ = φ :=
  DFunLike.ext _ _ fun f => by
    rw [leftTranslationWeakDualCLM_apply]
    exact congrArg φ (by ext x; simp)

private theorem leftTranslationWeakDualCLM_comp (g h : G) (φ : WeakDual ℝ (UCB G)) :
    leftTranslationWeakDualCLM g (leftTranslationWeakDualCLM h φ) =
      leftTranslationWeakDualCLM (g * h) φ :=
  DFunLike.ext _ _ fun f => by
    rw [leftTranslationWeakDualCLM_apply, leftTranslationWeakDualCLM_apply,
      leftTranslationWeakDualCLM_apply]
    exact congrArg φ (by ext x; simp)

/-- Contragredient left action of `G` on `WeakDual ℝ (UCB G)`, sending `g` to the weak-* continuous
linear equivalence `φ ↦ (f ↦ φ (L_{g⁻¹} f))`. -/
def leftTranslationWeakDual : G →* (WeakDual ℝ (UCB G) ≃L[ℝ] WeakDual ℝ (UCB G)) where
  toFun g := ContinuousLinearEquiv.ofContinuousLinearMap
    (leftTranslationWeakDualCLM g) (leftTranslationWeakDualCLM g⁻¹)
    (ContinuousLinearMap.ext fun φ => by
      simp [leftTranslationWeakDualCLM_comp, leftTranslationWeakDualCLM_one])
    (ContinuousLinearMap.ext fun φ => by
      simp [leftTranslationWeakDualCLM_comp, leftTranslationWeakDualCLM_one])
  map_one' := by
    ext φ
    exact leftTranslationWeakDualCLM_one φ
  map_mul' g h := by
    ext φ
    exact (leftTranslationWeakDualCLM_comp g h φ).symm

@[simp]
theorem leftTranslationWeakDual_apply (g : G) (φ : WeakDual ℝ (UCB G)) (f : UCB G) :
    leftTranslationWeakDual g φ f = φ (leftTranslation g⁻¹ f) := by
  simp [leftTranslationWeakDual, -map_inv]

/-- The inverse of `leftTranslationWeakDual g` is `leftTranslationWeakDual g⁻¹`. -/
@[simp]
theorem leftTranslationWeakDual_symm (g : G) :
    (leftTranslationWeakDual g).symm = leftTranslationWeakDual g⁻¹ := by
  ext φ
  exact DFunLike.ext _ _ fun f => by simp [leftTranslationWeakDual]

end UCB

end TauCeti
