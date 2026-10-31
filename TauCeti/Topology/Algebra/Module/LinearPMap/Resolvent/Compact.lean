/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Shift

/-!
# Partial linear maps with compact resolvent

A partial linear map `A : X →ₗ.[𝕜] X` has *compact resolvent* when its resolvent
`R(lambda) = (lambda • I - A)⁻¹` is a compact operator at some point `lambda` of its resolvent
set. By the resolvent identity `R(mu) = R(lambda) - (mu - lambda) R(lambda) R(mu)` and the ideal
property of compact operators, the resolvent is then compact at every point of the resolvent
set. So the choice of the point is immaterial, and compactness can be tested at any convenient
one, such as `lambda = i` for a self-adjoint operator.

The inverse `(A - lambda)⁻¹` of the opposite shift is the resolvent of `-A` at `-lambda`, and
`R(-lambda, -A) = -R(lambda, A)` (`LinearPMap.resolvent_neg`). Hence `-A` has compact resolvent
exactly when `A` does, and the convention `(A - lambda)⁻¹` defines the same class of operators as
`(lambda - A)⁻¹`.

Operators with compact resolvent are the unbounded operators with purely discrete spectrum,
such as Dirac and Laplace-type operators on closed manifolds and the Dirac operators of spectral
triples.

## Main definitions

* `LinearPMap.HasCompactResolvent`: some resolvent of `A` is a compact operator.

## Main results

* `LinearPMap.isCompactOperator_resolvent_of_isCompactOperator_resolvent`: compactness of one
  resolvent gives compactness of every resolvent.
* `LinearPMap.hasCompactResolvent_iff_isCompactOperator_resolvent`: compact resolvent can be
  tested at any single point of the resolvent set.
* `LinearPMap.hasCompactResolvent_neg_iff`: `-A` has compact resolvent exactly when `A` does.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Chapter III, §6.8.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
-/

public section

noncomputable section

namespace LinearPMap

/-! ## Compact resolvents -/

section Definition

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜}

variable (A) in
/-- A partial linear map `A` has **compact resolvent** if its resolvent
`R(lambda) = (lambda • I - A)⁻¹` is a compact operator at some point `lambda` of its resolvent
set. It is then compact at every point of the resolvent set
(`LinearPMap.HasCompactResolvent.isCompactOperator_resolvent`). -/
def HasCompactResolvent : Prop :=
  ∃ lambda ∈ A.resolventSet, IsCompactOperator (A.resolvent lambda)

/-- Unfolding of `LinearPMap.HasCompactResolvent`. -/
theorem hasCompactResolvent_def :
    A.HasCompactResolvent ↔ ∃ lambda ∈ A.resolventSet, IsCompactOperator (A.resolvent lambda) :=
  Iff.rfl

/-- A compact resolvent at a single resolvent point gives a compact resolvent. -/
theorem HasCompactResolvent.of_isCompactOperator_resolvent (hl : lambda ∈ A.resolventSet)
    (hc : IsCompactOperator (A.resolvent lambda)) : A.HasCompactResolvent :=
  ⟨lambda, hl, hc⟩

/-- An operator with compact resolvent has a nonempty resolvent set. -/
theorem HasCompactResolvent.nonempty_resolventSet (h : A.HasCompactResolvent) :
    A.resolventSet.Nonempty :=
  let ⟨lambda, hl, _⟩ := h
  ⟨lambda, hl⟩

end Definition

section Compact

variable {𝕜 X : Type*} [CommRing 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable {A : X →ₗ.[𝕜] X} {lambda mu : 𝕜}

/-- If the resolvent of `A` is compact at one point of the resolvent set, then it is compact at
every point of the resolvent set, by the resolvent identity
`R(mu) = R(lambda) - (mu - lambda) R(lambda) R(mu)`. -/
theorem isCompactOperator_resolvent_of_isCompactOperator_resolvent
    (hl : lambda ∈ A.resolventSet) (hm : mu ∈ A.resolventSet)
    (hc : IsCompactOperator (A.resolvent lambda)) :
    IsCompactOperator (A.resolvent mu) := by
  have hR : A.resolvent mu =
      A.resolvent lambda - (mu - lambda) • (A.resolvent lambda ∘L A.resolvent mu) := by
    rw [← resolvent_sub_resolvent hl hm, sub_sub_cancel]
  rw [hR, FunLike.coe_sub, FunLike.coe_smul, ContinuousLinearMap.coe_comp]
  exact hc.sub ((hc.comp_clm (A.resolvent mu)).smul (mu - lambda))

/-- An operator with compact resolvent has a compact resolvent at every resolvent point. -/
theorem HasCompactResolvent.isCompactOperator_resolvent (h : A.HasCompactResolvent)
    (hm : mu ∈ A.resolventSet) : IsCompactOperator (A.resolvent mu) :=
  let ⟨_, hl, hc⟩ := h
  isCompactOperator_resolvent_of_isCompactOperator_resolvent hl hm hc

/-- Compact resolvent can be tested at any single point of the resolvent set. -/
theorem hasCompactResolvent_iff_isCompactOperator_resolvent (hl : lambda ∈ A.resolventSet) :
    A.HasCompactResolvent ↔ IsCompactOperator (A.resolvent lambda) :=
  ⟨fun h => h.isCompactOperator_resolvent hl, HasCompactResolvent.of_isCompactOperator_resolvent hl⟩

/-- An operator has compact resolvent exactly when its resolvent set is nonempty and its
resolvent is compact at each of its points. -/
theorem hasCompactResolvent_iff_forall_isCompactOperator_resolvent :
    A.HasCompactResolvent ↔
      A.resolventSet.Nonempty ∧ ∀ mu ∈ A.resolventSet, IsCompactOperator (A.resolvent mu) :=
  ⟨fun h => ⟨h.nonempty_resolventSet, fun _ hm => h.isCompactOperator_resolvent hm⟩,
    fun ⟨⟨lambda, hl⟩, h⟩ => ⟨lambda, hl, h lambda hl⟩⟩

end Compact

section Neg

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] {A : X →ₗ.[𝕜] X}

/-- `-A` has compact resolvent exactly when `A` does: the inverses `(A - lambda)⁻¹` and
`(lambda - A)⁻¹` differ by a sign. -/
@[simp]
theorem hasCompactResolvent_neg_iff : (-A).HasCompactResolvent ↔ A.HasCompactResolvent := by
  suffices ∀ B : X →ₗ.[𝕜] X, B.HasCompactResolvent → (-B).HasCompactResolvent from
    ⟨fun h => by simpa only [neg_neg] using this _ h, this A⟩
  rintro B ⟨lambda, hl, hc⟩
  refine ⟨-lambda, mem_resolventSet_neg_iff.mpr hl, ?_⟩
  rw [resolvent_neg hl, FunLike.coe_neg]
  exact hc.neg

end Neg

end LinearPMap
