/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Compactness.Compact

/-!
# Torsion and continuous maps in topological groups

Let `A` be a topological abelian group topologically isomorphic to `Multiplicative (M × T)`, where
`M` is a torsion-free additive group and `T` is a torsion additive group. The algebraic
identification of `A ⧸ torsion A` with `M` from `TauCeti.GroupTheory.Torsion` is then a
topological isomorphism for the quotient topology.

Continuous maps from a compact space into a discrete `p`-primary torsion group also form a
`p`-primary torsion group, since each map has finite image.

## Main definitions

* `TauCeti.quotientTorsionContinuousMulEquiv`: the quotient of `A` by its torsion subgroup is
  topologically isomorphic to `M`.
* `TauCeti.IsPPrimaryTorsion.continuousMap`: compact-to-discrete continuous maps preserve
  `p`-primary torsion.
-/

public section

namespace TauCeti

open CommGroup (torsion)
open Multiplicative

variable {A M T : Type*} [CommGroup A] [AddGroup M] [IsAddTorsionFree M] [AddMonoid T]
  [TopologicalSpace A] [TopologicalSpace M] [TopologicalSpace T]

/-- Under a topological isomorphism `A ≃ₜ* Multiplicative (M × T)` with `M` torsion-free and `T`
torsion, the quotient of `A` by its torsion subgroup is topologically isomorphic to `M`. -/
noncomputable def quotientTorsionContinuousMulEquiv (hT : IsAddTorsion T)
    (e : A ≃ₜ* Multiplicative (M × T)) : A ⧸ torsion A ≃ₜ* Multiplicative M where
  toMulEquiv := quotientTorsionMulEquiv hT e.toMulEquiv
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 <|
    (continuous_ofAdd.comp (continuous_fst.comp (continuous_toAdd.comp e.continuous))).congr
      fun x ↦ (quotientTorsionMulEquiv_mk hT e.toMulEquiv x).symm
  continuous_invFun :=
    (QuotientGroup.continuous_mk.comp (e.symm.continuous.comp
      (continuous_ofAdd.comp (continuous_toAdd.prodMk continuous_const)))).congr
      fun v ↦ (quotientTorsionMulEquiv_symm_apply hT e.toMulEquiv v).symm

@[simp]
theorem quotientTorsionContinuousMulEquiv_mk (hT : IsAddTorsion T)
    (e : A ≃ₜ* Multiplicative (M × T)) (x : A) :
    quotientTorsionContinuousMulEquiv hT e (x : A ⧸ torsion A) = ofAdd (e x).toAdd.1 :=
  quotientTorsionMulEquiv_mk hT e.toMulEquiv x

@[simp]
theorem quotientTorsionContinuousMulEquiv_symm_apply (hT : IsAddTorsion T)
    (e : A ≃ₜ* Multiplicative (M × T)) (v : Multiplicative M) :
    (quotientTorsionContinuousMulEquiv hT e).symm v =
      ((e.symm (ofAdd (v.toAdd, 0)) : A) : A ⧸ torsion A) :=
  quotientTorsionMulEquiv_symm_apply hT e.toMulEquiv v

variable {p : ℕ}

/-- The continuous maps from a compact space into a discrete `p`-primary torsion group form a
`p`-primary torsion group: such a map has finite image, so one power of `p` kills all its values
at once. -/
theorem IsPPrimaryTorsion.continuousMap {V : Type*} [AddCommGroup V] [TopologicalSpace V]
    [DiscreteTopology V] (h : IsPPrimaryTorsion p V) (X : Type*)
    [TopologicalSpace X] [CompactSpace X] : IsPPrimaryTorsion p C(X, V) := by
  refine isPPrimaryTorsion_iff.2 fun f ↦ ?_
  choose k hk using isPPrimaryTorsion_iff.1 h
  have hfin : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  refine ⟨hfin.toFinset.sup k, ContinuousMap.ext fun x ↦ ?_⟩
  obtain ⟨c, hc⟩ := pow_dvd_pow p
    (Finset.le_sup (f := k) (hfin.mem_toFinset.2 (Set.mem_range_self x)))
  simp [hc, mul_comm _ c, mul_smul, hk]

end TauCeti
