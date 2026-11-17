/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Normed.Lp.ProdLp

/-!
# Adjoints of block-diagonal operators on `WithLp 2` products

For Hilbert spaces `E₁, E₂, F₁, F₂` and continuous linear maps `f : E₁ →L[𝕜] F₁`,
`g : E₂ →L[𝕜] F₂`, the block-diagonal operator `f.withLpProdMap 2 g` on
`WithLp 2 (E₁ × E₂) →L[𝕜] WithLp 2 (F₁ × F₂)` has Hilbert adjoint
`(adjoint f).withLpProdMap 2 (adjoint g)`, and is self-adjoint whenever both blocks are.

## Main results

* `ContinuousLinearMap.adjoint_withLpProdMap`: `(f ⊕ g)† = f† ⊕ g†` on `WithLp 2`.
* `IsSelfAdjoint.withLpProdMap`: `f ⊕ g` is self-adjoint when `f` and `g` are.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- **Hilbert adjoint of an orthogonal block sum.** `(f ⊕ g)† = f† ⊕ g†` on `WithLp 2`. -/
@[simp]
theorem adjoint_withLpProdMap
    [CompleteSpace E₁] [CompleteSpace E₂] [CompleteSpace F₁] [CompleteSpace F₂]
    (f : E₁ →L[𝕜] F₁) (g : E₂ →L[𝕜] F₂) :
    adjoint (f.withLpProdMap 2 g) = (adjoint f).withLpProdMap 2 (adjoint g) := by
  refine ((eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply, adjoint_inner_left]

/-- An orthogonal block sum `f ⊕ g` on `WithLp 2` is self-adjoint when both blocks are. -/
theorem _root_.IsSelfAdjoint.withLpProdMap [CompleteSpace E₁] [CompleteSpace E₂]
    {f : E₁ →L[𝕜] E₁} {g : E₂ →L[𝕜] E₂} (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (f.withLpProdMap 2 g) := by
  rw [isSelfAdjoint_iff, star_eq_adjoint, adjoint_withLpProdMap,
    ← star_eq_adjoint, ← star_eq_adjoint, hf.star_eq, hg.star_eq]

end ContinuousLinearMap
