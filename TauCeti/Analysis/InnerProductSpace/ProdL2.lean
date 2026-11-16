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
# Adjoints of bounded block sums on `L²` Hilbert products

On the orthogonal direct sum `WithLp 2 (E₁ × E₂)` of Hilbert spaces, the bounded block sum
`f.withLpProdMap 2 g` takes Hilbert-space adjoints and stars componentwise, and is self-adjoint if
and only if both blocks are self-adjoint. This is the infinite-dimensional bounded counterpart of
`LinearMap.adjoint_prodMap_withLpMap`.
-/

public section

open scoped ENNReal InnerProduct InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]

/-- **Adjoint of a Hilbert block sum.** `(f ⊕ g)† = f† ⊕ g†`. -/
@[simp]
theorem adjoint_withLpProdMap (f : E₁ →L[𝕜] F₁) (g : E₂ →L[𝕜] F₂) :
    (f.withLpProdMap 2 g)† = (f†).withLpProdMap 2 (g†) := by
  refine ((eq_adjoint_iff _ _).mpr fun x y ↦ ?_).symm
  simp [WithLp.prod_inner_apply, adjoint_inner_left]

/-- **Star of a Hilbert block sum.** `star (f ⊕ g) = star f ⊕ star g`. -/
@[simp]
theorem star_withLpProdMap (f : E₁ →L[𝕜] E₁) (g : E₂ →L[𝕜] E₂) :
    star (f.withLpProdMap 2 g) = (star f).withLpProdMap 2 (star g) := by
  simp only [star_eq_adjoint, adjoint_withLpProdMap]

/-- A Hilbert block sum is self-adjoint if and only if both blocks are self-adjoint. -/
@[simp]
theorem isSelfAdjoint_withLpProdMap_iff {f : E₁ →L[𝕜] E₁} {g : E₂ →L[𝕜] E₂} :
    IsSelfAdjoint (f.withLpProdMap 2 g) ↔ IsSelfAdjoint f ∧ IsSelfAdjoint g := by
  refine ⟨fun h ↦ ?_, fun ⟨hf, hg⟩ ↦ ?_⟩
  · have h' := h.star_eq
    rw [star_withLpProdMap] at h'
    refine ⟨?_, ?_⟩
    · ext x
      simpa [IsSelfAdjoint] using congrArg WithLp.fst congr($h' (WithLp.toLp 2 (x, 0)))
    · ext y
      simpa [IsSelfAdjoint] using congrArg WithLp.snd congr($h' (WithLp.toLp 2 (0, y)))
  · rw [IsSelfAdjoint, star_withLpProdMap, hf.star_eq, hg.star_eq]

end ContinuousLinearMap
