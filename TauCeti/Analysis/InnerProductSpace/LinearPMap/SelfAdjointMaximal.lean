/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.Shift
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# Maximality of self-adjoint partial operators

Taking the adjoint reverses extension order on densely defined partial linear maps
(`LinearPMap.adjoint_anti`). Consequently, a self-adjoint partial operator on a Hilbert space over
an `RCLike` scalar field has no proper formally self-adjoint extension
(`LinearPMap.eq_of_le_of_isFormalAdjoint`) and in particular no proper self-adjoint extension
(`LinearPMap.eq_of_le_of_isSelfAdjoint`). If a densely defined `A` has a self-adjoint extension,
then the deficiency space `ker (A† - c)` vanishes for a nonreal `c` only if `ker (A† - conj c)`
does (`IsSelfAdjoint.ker_subScalar_adjoint_conj_eq_bot`): an operator with exactly one vanishing
deficiency space has no self-adjoint extension.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointMaximal.lean`,
and generalized from `ℂ` to arbitrary `RCLike` scalars.
-/

public section

namespace LinearPMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Taking the adjoint reverses extension order on densely defined partial linear maps. -/
theorem adjoint_anti {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {A B : H →ₗ.[𝕜] F} (hAB : A ≤ B) (hA : Dense (A.domain : Set H)) : B† ≤ A† :=
  IsFormalAdjoint.le_adjoint hA fun x y => by
    rw [hAB.2 (x := x) (y := ⟨x, hAB.1 x.property⟩) rfl]
    exact (adjoint_isFormalAdjoint (hA.mono hAB.1)).symm ⟨x, hAB.1 x.property⟩ y

/-- A self-adjoint partial operator has no proper formally self-adjoint extension. -/
theorem eq_of_le_of_isFormalAdjoint {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B) (hAB : A ≤ B) : A = B :=
  le_antisymm hAB <|
    (hB.le_adjoint (hA.dense_domain.mono hAB.1)).trans
      ((adjoint_anti hAB hA.dense_domain).trans_eq (isSelfAdjoint_def.mp hA))

/-- A self-adjoint partial operator cannot be properly extended to another
self-adjoint partial operator. -/
theorem eq_of_le_of_isSelfAdjoint {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hAB : A ≤ B) : A = B :=
  eq_of_le_of_isFormalAdjoint hA hB.isFormalAdjoint hAB

open scoped ComplexConjugate in
/-- **Deficiency spaces of an operator with a self-adjoint extension.** Let `B` be a self-adjoint
extension of a densely defined `A` and `c` a nonreal scalar. If `ker (A† - c) = 0`, then
`ker (A† - conj c) = 0`. So an operator whose deficiency spaces `ker (A† - c)` and
`ker (A† - conj c)` do not vanish together has no self-adjoint extension. -/
theorem _root_.IsSelfAdjoint.ker_subScalar_adjoint_conj_eq_bot {A B : H →ₗ.[𝕜] H}
    (hB : IsSelfAdjoint B) (hAB : A ≤ B) (hA : Dense (A.domain : Set H)) {c : 𝕜}
    (hc : RCLike.im c ≠ 0) (h : (A†.subScalar c).ker = ⊥) : (A†.subScalar (conj c)).ker = ⊥ := by
  have hBA : B ≤ A† := (isSelfAdjoint_def.mp hB).ge.trans (adjoint_anti hAB hA)
  rw [Submodule.eq_bot_iff]
  intro e he
  obtain ⟨he, hAe⟩ := mem_ker_subScalar_iff.mp he
  obtain ⟨x, hx⟩ := hB.smul_sub_surjective hc (c • e - A† ⟨e, he⟩)
  have hx : c • (x : H) - B x = c • e - A† ⟨e, he⟩ := hx
  have hxA : A† ⟨x, hBA.1 x.property⟩ = B x := (hBA.2 rfl).symm
  have hy : e - (x : H) ∈ (A†.subScalar c).ker := by
    refine mem_ker_subScalar_iff.mpr ⟨sub_mem he (hBA.1 x.property), ?_⟩
    have hsub : A† ⟨e - x, sub_mem he (hBA.1 x.property)⟩ = A† ⟨e, he⟩ - A† ⟨x, hBA.1 x.property⟩ :=
      (congrArg A† (Subtype.ext (by rw [Submodule.coe_sub]))).trans (A†.map_sub _ _)
    rw [hsub, hxA, smul_sub]
    rw [← sub_eq_zero] at hx ⊢
    rw [← hx]
    abel
  rw [h, Submodule.mem_bot, sub_eq_zero] at hy
  subst hy
  exact hB.isFormalAdjoint.eq_zero_of_apply_eq_smul (by simpa using hc) (hxA.symm.trans hAe)

end LinearPMap
