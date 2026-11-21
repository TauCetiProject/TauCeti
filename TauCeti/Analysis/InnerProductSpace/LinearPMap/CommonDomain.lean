/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Self-adjoint operators on a common domain

Let `H` be an inner product space and `ι, A : D →L H` bounded operators with `ι` injective, so
that `ContinuousLinearMap.domainOperator ι A hι` is the unbounded operator on `H` with domain
`range ι` acting by `ι x ↦ A x`. This file translates the symmetry and self-adjointness of that
operator into conditions on the pair `(ι, A)`.

* It is symmetric exactly when `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all `x, y : D`
  (`ContinuousLinearMap.isFormalAdjoint_domainOperator_iff`), the symmetry hypothesis of the
  common-domain trajectory operators `TauCeti.WeakDerivStep.domainTrajectoryOperator`.
* On a Hilbert space, a symmetric pair for which `c • ι - A` is surjective at one real `c`, for
  instance a pair with `A` invertible, gives a self-adjoint operator
  (`ContinuousLinearMap.isSelfAdjoint_domainOperator`,
  `ContinuousLinearMap.isSelfAdjoint_domainOperator_of_isInvertible`).
* Conversely, for a self-adjoint operator and complete `D`, every nonreal shift `c • ι - A` is
  invertible (`ContinuousLinearMap.isInvertible_smul_sub_of_isSelfAdjoint_domainOperator`).

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Section 4 (paths of self-adjoint operators on a fixed domain `W ⊂ H`).
-/

public section

noncomputable section

open Function

namespace ContinuousLinearMap

section InnerProduct

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Topological

variable [AddCommGroup D] [Module 𝕜 D] [TopologicalSpace D] {ι A : D →L[𝕜] H} {hι : Injective ι}

/-- `domainOperator ι A hι` is symmetric exactly when `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all
`x y : D`. -/
theorem isFormalAdjoint_domainOperator_iff :
    (domainOperator ι A hι).IsFormalAdjoint (domainOperator ι A hι) ↔
      ∀ x y, ⟪A x, ι y⟫ = ⟪ι x, A y⟫ := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ?_⟩
  · convert h ⟨ι x, apply_mem_domain_domainOperator ι A hι x⟩
      ⟨ι y, apply_mem_domain_domainOperator ι A hι y⟩ using 2 <;>
      exact (domainOperator_apply_mk ι A hι _ _).symm
  · rintro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨x, rfl⟩ := (mem_domain_domainOperator_iff ι A hι).1 hx
    obtain ⟨y, rfl⟩ := (mem_domain_domainOperator_iff ι A hι).1 hy
    convert h x y using 2 <;> exact domainOperator_apply_mk ι A hι _ _

/-- **Self-adjointness on a common domain.** On a Hilbert space `H`, if `⟪A x, ι y⟫ = ⟪ι x, A y⟫`
for all `x y : D` and the shift `c • ι - A` is surjective at a real scalar `c`, then
`domainOperator ι A hι` is self-adjoint. -/
theorem isSelfAdjoint_domainOperator [CompleteSpace H] (hsymm : ∀ x y, ⟪A x, ι y⟫ = ⟪ι x, A y⟫)
    {c : 𝕜} (hc : RCLike.im c = 0) (hsurj : Surjective (c • ι - A)) :
    IsSelfAdjoint (domainOperator ι A hι) := by
  refine (isFormalAdjoint_domainOperator_iff.2 hsymm).isSelfAdjoint_of_surjective_smul_sub hc
    fun z ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj z
  exact ⟨⟨ι x, apply_mem_domain_domainOperator ι A hι x⟩, smul_sub_domainOperator_apply rfl⟩

/-- On a Hilbert space `H`, if `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all `x y : D` and `A` is invertible,
then `domainOperator ι A hι` is self-adjoint. -/
theorem isSelfAdjoint_domainOperator_of_isInvertible [CompleteSpace H]
    (hsymm : ∀ x y, ⟪A x, ι y⟫ = ⟪ι x, A y⟫) (h : A.IsInvertible) :
    IsSelfAdjoint (domainOperator ι A hι) :=
  isSelfAdjoint_domainOperator hsymm (c := 0) (map_zero _)
    (isInvertible_zero_smul_sub_iff.2 h).surjective

end Topological

section Normed

variable [NormedAddCommGroup D] [NormedSpace 𝕜 D] {ι A : D →L[𝕜] H} {hι : Injective ι}

/-- If `domainOperator ι A hι` is self-adjoint on a Hilbert space and `D` is complete, then the
shift `c • ι - A` is invertible at every nonreal scalar `c`. -/
theorem isInvertible_smul_sub_of_isSelfAdjoint_domainOperator [CompleteSpace D] [CompleteSpace H]
    (h : IsSelfAdjoint (domainOperator ι A hι)) {c : 𝕜} (hc : RCLike.im c ≠ 0) :
    (c • ι - A).IsInvertible :=
  isInvertible_iff_bijective.2 (bijective_smul_sub_domainOperator_iff.1 (h.smul_sub_bijective hc))

end Normed

end InnerProduct

end ContinuousLinearMap
