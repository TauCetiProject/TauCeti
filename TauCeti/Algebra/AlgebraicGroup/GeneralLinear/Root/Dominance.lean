/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Base
public import TauCeti.Algebra.Order.BigOperators.Dominance
public import TauCeti.LinearAlgebra.RootSystem.Dominance

/-!
# The dominance order on coweights of the general linear group

A cocharacter of the diagonal torus of `GL_(n+1)` is an integer tuple `μ = (μ₀, …, μₙ)`. For the
standard base `e_i - e_(i+1)` of `TauCeti.GeneralLinear.diagonalRootBase`, the coroot order
`ν ≤ μ` of a general reductive group says that `μ - ν` is a sum of simple coroots with natural
coefficients (`RootPairing.rootLE` for the flipped root datum and base). For `GL_(n+1)` this is
the classical partial-sum order: `μ` and `ν` have the same total degree and every leading partial
sum of `ν` is at most the corresponding one of `μ`, which is `TauCeti.Dominates ν μ` on the
underlying tuples. This identifies the order on coweights that bounds affine Schubert varieties
with the elementary partial-sum test.

For instance `(1, 1) ≤ (2, 0)`, whose difference is the simple coroot `(1, -1)`, while
`(1, 0)` and `(2, 0)` are incomparable since their totals differ. For `GL_1` the order is
equality (`TauCeti.dominates_iff_eq_fin_one`).

## Main results

* `TauCeti.GeneralLinear.dominates_iff_rootLE_flip`: the partial-sum dominance order on the
  coweights of `GL_(n+1)` is the coroot order of the standard base.

## References

* M. Rapoport, *A positivity property of the Satake isomorphism*, Manuscripta Math. 101 (2000),
  153–166, §1.
* L. Fargues and P. Scholze, *Geometrization of the local Langlands correspondence*,
  Section VI.2.
-/

public section

namespace TauCeti.GeneralLinear

open RootPairing

universe u

/-- **The dominance order on the coweights of `GL_(n+1)` is the coroot order.** A coweight `ν` of
the diagonal torus lies below `μ` for the standard base, that is, `μ - ν` is a sum of the simple
coroots `e_i - e_(i+1)` with natural coefficients, exactly when `μ` and `ν` have the same total
degree and every leading partial sum of `ν` is at most that of `μ`. -/
theorem dominates_iff_rootLE_flip {n : ℕ} {ν μ : ULift.{u} (Fin (n + 1)) → ℤ} :
    Dominates (fun i ↦ ν (ULift.up i)) (fun i ↦ μ (ULift.up i)) ↔
      (diagonalRootDatum.{u} (n + 1)).flip.rootLE (diagonalRootBase.{u} n).flip ν μ := by
  rw [dominates_iff_exists_nat_sub_eq_sum, rootLE_iff_sub_mem_posRootCone,
    mem_posRootCone_iff_exists_nat_of_bijOn _ (diagonalRootBase n).flip
      (bijOn_diagonalSimpleRootIndex n)]
  refine exists_congr fun c ↦ ?_
  have hcoroot : ∑ i, c i • (diagonalRootDatum.{u} (n + 1)).flip.root
      (diagonalSimpleRootIndex n i) = fun j ↦ (∑ i, c i •
        (Pi.single i.castSucc 1 - Pi.single i.succ 1 : Fin (n + 1) → ℤ)) j.down := by
    funext ⟨j⟩
    simp only [RootPairing.flip_root, Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun i _ ↦
      congrArg _ (diagonalRootDatum_coroot_diagonalSimpleRootIndex_apply n i j)
  rw [hcoroot]
  exact ⟨fun h ↦ funext fun j ↦ congrFun h j.down, fun h ↦ funext fun j ↦ congrFun h (ULift.up j)⟩

end TauCeti.GeneralLinear
