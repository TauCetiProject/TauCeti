/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Torsion
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The torsion-free quotient under a topological product decomposition

Let `A` be a topological abelian group topologically isomorphic to `Multiplicative (M × T)`, where
`M` is a torsion-free additive group and `T` is a torsion additive group. The algebraic
identification of `A ⧸ torsion A` with `M` from `TauCeti.GroupTheory.Torsion` is then a
topological isomorphism for the quotient topology.

## Main definitions

* `TauCeti.quotientTorsionContinuousMulEquiv`: the quotient of `A` by its torsion subgroup is
  topologically isomorphic to `M`.
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

end TauCeti
