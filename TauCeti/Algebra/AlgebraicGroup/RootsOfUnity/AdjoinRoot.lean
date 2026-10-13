/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
public import Mathlib.RingTheory.AdjoinRoot
import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# The coordinate ring of `μ_N` as `R[X]/(X ^ N - 1)`

The coordinate ring of `μ_N = D(ℤ/N)` over a commutative ring `R` is the group algebra
`R[Multiplicative (ZMod N)]`. For `N ≠ 0` it is also the classical `R[X]/(X ^ N - 1)`, the standard
generator corresponding to the class of `X`. Both sides are presented by a single `N`th root of
unity: an algebra map out of either is determined by the image of its generator, which may be any
`N`th root of unity.

## Main definitions

* `TauCeti.RootsOfUnityGroup.adjoinRootEquiv`: the `R`-algebra isomorphism
  `R[X]/(X ^ N - 1) ≃ R[Multiplicative (ZMod N)]` taking the class of `X` to the standard
  generator.
-/

public section

open Polynomial WithConv

namespace TauCeti.RootsOfUnityGroup

variable {R : Type*} [CommRing R] (n : ℕ)

-- The standard generator of `R[Multiplicative (ZMod n)]` is an `n`th root of unity.
private theorem single_generator_pow : MonoidAlgebra.single (generator n) (1 : R) ^ n = 1 := by
  rw [MonoidAlgebra.single_pow, one_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
    MonoidAlgebra.one_def]

-- An algebra map out of `R[Multiplicative (ZMod n)]` is determined by its value on the standard
-- generator, because the points of `μ_n` are determined by that value.
private theorem algHom_ext_generator {B : Type*} [CommRing B] [Algebra R B]
    {f₁ f₂ : MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] B}
    (h : f₁ (MonoidAlgebra.single (generator n) 1) = f₂ (MonoidAlgebra.single (generator n) 1)) :
    f₁ = f₂ :=
  congrArg ofConv <| (pointsMulEquiv (R := R) (A := B) n).injective <|
    Subtype.ext <| Units.ext <| by simpa only [pointsMulEquiv_apply] using h

variable [NeZero n]

/-- For `n ≠ 0`, the coordinate ring `R[Multiplicative (ZMod n)]` of `μ_n` is `R[X]/(X ^ n - 1)`,
the class of `X` corresponding to the standard generator (`adjoinRootEquiv_root`). -/
noncomputable def adjoinRootEquiv :
    AdjoinRoot (X ^ n - 1 : R[X]) ≃ₐ[R] MonoidAlgebra R (Multiplicative (ZMod n)) :=
  AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (MonoidAlgebra.single (generator n) 1) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_one, single_generator_pow, sub_self]))
    ((pointsMulEquiv (R := R) n).symm
      (rootsOfUnity.mkOfPowEq _ (AdjoinRoot.root_X_pow_sub_one_pow n))).ofConv
    (algHom_ext_generator n (by
      rw [AlgHom.comp_apply, pointsMulEquiv_symm_apply_single_generator,
        rootsOfUnity.coe_mkOfPowEq, AdjoinRoot.liftAlgHom_root, AlgHom.id_apply]))
    (AdjoinRoot.algHom_ext (by
      rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, pointsMulEquiv_symm_apply_single_generator,
        rootsOfUnity.coe_mkOfPowEq, AlgHom.id_apply]))

@[simp]
theorem adjoinRootEquiv_root :
    adjoinRootEquiv (R := R) n (AdjoinRoot.root _) = MonoidAlgebra.single (generator n) 1 := by
  rw [adjoinRootEquiv, AlgEquiv.ofAlgHom_apply, AdjoinRoot.liftAlgHom_root]

@[simp]
theorem adjoinRootEquiv_symm_single_generator :
    (adjoinRootEquiv (R := R) n).symm (MonoidAlgebra.single (generator n) 1) =
      AdjoinRoot.root _ := by
  rw [AlgEquiv.symm_apply_eq, adjoinRootEquiv_root]

end TauCeti.RootsOfUnityGroup
