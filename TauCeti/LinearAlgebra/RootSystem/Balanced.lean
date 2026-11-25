/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import Mathlib.LinearAlgebra.RootSystem.Hom
public import TauCeti.LinearAlgebra.RootSystem.RootSpanProj
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Balanced root pairings and coroot-kernel projection lemmas

This file establishes balancedness for finite crystallographic root pairings over
characteristic-zero fields (`RootPairing.instIsBalancedOfIsCrystallographic`), together with
supplementary `simp` and `P.Aut`-equivariance lemmas for `RootPairing.rootSpanProj` (defined in
`TauCeti.LinearAlgebra.RootSystem.RootSpanProj`).

## Main results

* `RootPairing.instIsBalancedOfIsCrystallographic`: finite crystallographic pairings over
  characteristic-zero fields are balanced.
* `RootPairing.rootSpanProj_apply_coe`, `RootPairing.rootSpanProj_eq_zero_iff`,
  `RootPairing.toLinearMap_coe_rootSpanProj_coroot`, `RootPairing.coe_rootSpanProj_smul`, and
  `RootPairing.restrictScalars'_coroot'_rootSpanProj`: supplementary properties, coroot
  preservation, and `P.Aut`-equivariance of `rootSpanProj`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, §§6.1, 6.7.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C, C.53.
-/

public section

open Set

namespace RootPairing

section Balanced

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- Every finite crystallographic root pairing over a characteristic-zero field is balanced. -/
instance instIsBalancedOfIsCrystallographic {K : Type*} [Field K] [CharZero K]
    [Module K M] [Module K N] [Finite ι] (Q : RootPairing ι K M N) [Q.IsCrystallographic] :
    Q.IsBalanced := by cases nonempty_fintype ι; infer_instance

variable [P.IsBalanced]

/-- `P.rootSpanProj` acts as the identity on `P.rootSpan R`. -/
@[simp] theorem rootSpanProj_apply_coe (x : P.rootSpan R) : P.rootSpanProj x = x :=
  P.rootSpanProj_apply_of_mem x.property

/-- `P.rootSpanProj x = 0` if and only if every coroot functional vanishes on `x`. -/
@[simp] theorem rootSpanProj_eq_zero_iff {x : M} :
    P.rootSpanProj x = 0 ↔ ∀ i, P.coroot' i x = 0 := by
  rw [← LinearMap.mem_ker, ker_rootSpanProj, Submodule.mem_iInf]
  exact forall_congr' fun _ ↦ LinearMap.mem_ker

/-- Projecting to `P.rootSpan R` along the common coroot kernel preserves pairing with every
coroot. -/
@[simp] theorem toLinearMap_coe_rootSpanProj_coroot (x : M) (i : ι) :
    P.toLinearMap (P.rootSpanProj x : M) (P.coroot i) = P.toLinearMap x (P.coroot i) :=
  P.coroot'_rootSpanProj i x

/-- `P.rootSpanProj` is equivariant for the weight action of `P.Aut`. -/
theorem coe_rootSpanProj_smul (g : P.Aut) (x : M) :
    (P.rootSpanProj (g • x) : M) = g • (P.rootSpanProj x : M) := by
  have hle : P.rootSpan R ≤ (P.rootSpan R).comap g.weightEquiv.toLinearMap :=
    Submodule.span_le.mpr <| range_subset_iff.mpr fun j ↦ by
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe,
        Equiv.weightEquiv_apply, Hom.root_weightMap_apply]
      exact Submodule.subset_span (mem_range_self _)
  refine sub_eq_zero.mp <| Submodule.disjoint_def.mp P.isCompl_rootSpan_iInf_ker_coroot'.disjoint _
    (sub_mem (P.rootSpanProj (g • x)).property (hle (P.rootSpanProj x).property)) ?_
  exact (Submodule.mem_iInf _).mpr fun i ↦ LinearMap.mem_ker.mpr <| by
    rw [map_sub, coroot', LinearMap.flip_apply, P.toLinearMap_coe_rootSpanProj_coroot]
    change P.coroot' i (g • x) - P.coroot' i (g • (P.rootSpanProj x : M)) = 0
    rw [coroot'_smul, coroot'_smul]
    exact sub_eq_zero.mpr (P.toLinearMap_coe_rootSpanProj_coroot x _).symm

end Balanced

/-- Evaluating a coroot functional of `P.restrictScalars' K` on `P.rootSpanProj x` recovers
`P.coroot' i x`. -/
theorem restrictScalars'_coroot'_rootSpanProj {ι K M N : Type*} [Field K] [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] (P : RootPairing ι K M N) [P.IsBalanced]
    (i : ι) (x : M) : (P.restrictScalars' K).coroot' i (P.rootSpanProj x) = P.coroot' i x := by
  have h := P.restrictScalars_toLinearMap_apply_apply K (P.rootSpanProj x)
    ((P.restrictScalars' K).coroot i)
  rw [Algebra.algebraMap_self, RingHom.id_apply, P.restrictScalars_coe_coroot] at h
  exact h.trans (P.toLinearMap_coe_rootSpanProj_coroot x i)

end RootPairing
