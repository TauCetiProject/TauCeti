/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Closedness and compactness of orthonormal families

For an inner product space `E` over `𝕜`, `{f : ι → E | Orthonormal 𝕜 f}` is closed in the product
topology (`TauCeti.isClosed_setOfPred_orthonormal`), and compact when `E` is finite-dimensional
(`TauCeti.isCompact_setOfPred_orthonormal`).

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapters 1–5, Springer (1987), Chapter V, §2.
-/

public section

open Set
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 ι E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The set of orthonormal `ι`-tuples is closed in the product topology. -/
theorem isClosed_setOfPred_orthonormal : IsClosed {f : ι → E | Orthonormal 𝕜 f} := by
  have heq : {f : ι → E | Orthonormal 𝕜 f} = (⋂ i : ι, {f : ι → E | ‖f i‖ = 1}) ∩
      (⋂ (i : ι) (j : ι) (_ : i ≠ j), {f : ι → E | ⟪f i, f j⟫_𝕜 = 0}) := by
    ext f; simp only [mem_ofPred_eq, Orthonormal, mem_inter_iff, mem_iInter]; rfl
  rw [heq]
  exact (isClosed_iInter fun i ↦ isClosed_eq (continuous_norm.comp (continuous_apply i))
    continuous_const).inter (isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      isClosed_eq (Continuous.inner (continuous_apply i) (continuous_apply j)) continuous_const)

/-- On a finite-dimensional inner product space, the set of orthonormal `ι`-tuples is compact. -/
theorem isCompact_setOfPred_orthonormal [FiniteDimensional 𝕜 E] :
    IsCompact {f : ι → E | Orthonormal 𝕜 f} := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  exact (isCompact_univ_pi fun _ : ι ↦ isCompact_closedBall (0 : E) 1).of_isClosed_subset
    isClosed_setOfPred_orthonormal fun f hf i _ ↦ by simp [(hf.1 i).le]

end TauCeti
