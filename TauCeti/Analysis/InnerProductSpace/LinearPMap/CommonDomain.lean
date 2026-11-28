/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint
public import TauCeti.Topology.Algebra.Module.LinearPMap.CommonDomain
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Self-adjoint operators on a common domain

Let `H` be an inner product space and `ι, A : D →L H` bounded operators with `ι` injective, so
that `LinearMap.domainOperator ι A hι` of the underlying linear maps is the unbounded operator on
`H` with domain `range ι` acting by `ι x ↦ A x`. This file translates the symmetry and
self-adjointness of that operator into conditions on the pair `(ι, A)`.

* It is symmetric exactly when `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all `x, y : D`
  (`LinearMap.isFormalAdjoint_domainOperator_iff`), the symmetry hypothesis of the
  common-domain trajectory operators `TauCeti.WeakDerivStep.domainTrajectoryOperator`. Then
  solutions of `A x = c • ι x` for distinct real `c` have orthogonal images under `ι`
  (`ContinuousLinearMap.inner_eq_zero_of_apply_eq_smul`).
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

namespace LinearMap

variable {𝕜 D D' H K : Type*} [RCLike 𝕜] [AddCommMonoid D] [Module 𝕜 D]
  [AddCommMonoid D'] [Module 𝕜 D'] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
  {ι : D →ₗ[𝕜] H} {A : D →ₗ[𝕜] K} {ι' : D' →ₗ[𝕜] K} {B : D' →ₗ[𝕜] H}
  {hι : Injective ι} {hι' : Injective ι'}

/-- Operators on injectively embedded domains are formally adjoint exactly when their values
satisfy the inner product identity on the original domains. -/
theorem isFormalAdjoint_domainOperator_iff :
    (ι.domainOperator A hι).IsFormalAdjoint (ι'.domainOperator B hι') ↔
      ∀ x y, inner 𝕜 (A x) (ι' y) = inner 𝕜 (ι x) (B y) := by
  refine ⟨fun h x y ↦ ?_, fun h ↦ ?_⟩
  · simpa only [domainOperator_apply_mk] using
      h ⟨ι x, apply_mem_domain_domainOperator _ _ hι x⟩
        ⟨ι' y, apply_mem_domain_domainOperator _ _ hι' y⟩
  · rintro ⟨_, hx⟩ ⟨_, hy⟩
    obtain ⟨x, rfl⟩ := (mem_domain_domainOperator_iff _ _ hι).1 hx
    obtain ⟨y, rfl⟩ := (mem_domain_domainOperator_iff _ _ hι').1 hy
    simpa only [domainOperator_apply_mk] using h x y

end LinearMap

namespace ContinuousLinearMap

section InnerProduct

variable {𝕜 D H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Topological

variable [AddCommGroup D] [Module 𝕜 D] [TopologicalSpace D] {ι A : D →L[𝕜] H} {hι : Injective ι}

/-- **Orthogonality of eigenvectors on a common domain.** If `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all
`x y : D`, then solutions of `A x = c • ι x` and `A y = d • ι y` for distinct real scalars `c` and
`d` have orthogonal images under `ι`. -/
theorem inner_eq_zero_of_apply_eq_smul (hsymm : ∀ x y, ⟪A x, ι y⟫ = ⟪ι x, A y⟫) {c d : ℝ}
    (hcd : c ≠ d) {x y : D} (hx : A x = (c : 𝕜) • ι x) (hy : A y = (d : 𝕜) • ι y) :
    ⟪ι x, ι y⟫ = 0 := by
  have h := hsymm x y
  rw [hx, hy, inner_smul_left, inner_smul_right, RCLike.conj_ofReal] at h
  have h' : ((c : 𝕜) - d) * ⟪ι x, ι y⟫ = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 (RCLike.ofReal_injective.ne hcd))

/-- **Self-adjointness on a common domain.** On a Hilbert space `H`, if `⟪A x, ι y⟫ = ⟪ι x, A y⟫`
for all `x y : D` and the shift `c • ι - A` is surjective at a real scalar `c`, then
`LinearMap.domainOperator ι A hι` is self-adjoint. -/
theorem isSelfAdjoint_domainOperator [CompleteSpace H] (hsymm : ∀ x y, ⟪A x, ι y⟫ = ⟪ι x, A y⟫)
    {c : 𝕜} (hc : RCLike.im c = 0) (hsurj : Surjective (c • ι - A)) :
    IsSelfAdjoint (ι.toLinearMap.domainOperator A.toLinearMap hι) := by
  refine (LinearMap.isFormalAdjoint_domainOperator_iff.2 hsymm).isSelfAdjoint_of_surjective_smul_sub
    hc fun z ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj z
  exact ⟨⟨ι x, LinearMap.apply_mem_domain_domainOperator _ _ hι x⟩,
    smul_sub_domainOperator_apply rfl⟩

/-- On a Hilbert space `H`, if `⟪A x, ι y⟫ = ⟪ι x, A y⟫` for all `x y : D` and `A` is invertible,
then `LinearMap.domainOperator ι A hι` is self-adjoint. -/
theorem isSelfAdjoint_domainOperator_of_isInvertible [CompleteSpace H]
    (hsymm : ∀ x y, ⟪A x, ι y⟫ = ⟪ι x, A y⟫) (h : A.IsInvertible) :
    IsSelfAdjoint (ι.toLinearMap.domainOperator A.toLinearMap hι) :=
  isSelfAdjoint_domainOperator hsymm (c := 0) (map_zero _) <| by
    rw [zero_smul, zero_sub]
    exact (isInvertible_neg_iff.2 h).surjective

end Topological

section Normed

variable [NormedAddCommGroup D] [NormedSpace 𝕜 D] {ι A : D →L[𝕜] H} {hι : Injective ι}

/-- If `LinearMap.domainOperator ι A hι` is self-adjoint on a Hilbert space and `D` is complete,
then the shift `c • ι - A` is invertible at every nonreal scalar `c`. -/
theorem isInvertible_smul_sub_of_isSelfAdjoint_domainOperator [CompleteSpace D] [CompleteSpace H]
    (h : IsSelfAdjoint (ι.toLinearMap.domainOperator A.toLinearMap hι)) {c : 𝕜}
    (hc : RCLike.im c ≠ 0) :
    (c • ι - A).IsInvertible :=
  isInvertible_iff_bijective.2 (bijective_smul_sub_domainOperator_iff.1 (h.smul_sub_bijective hc))

end Normed

end InnerProduct

end ContinuousLinearMap
