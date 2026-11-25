/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.IsApply
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Pointwise algebraic operations on locally constant functions

Zero and addition of locally constant functions are computed pointwise. This file records this
through the `IsZeroApply` and `IsAddApply` classes, so that the generic `FunLike` lemmas, such as
`sum_apply`, apply to `LocallyConstant X M`.
-/

public section

namespace LocallyConstant

/-- Zero of locally constant functions is pointwise, so that the generic `FunLike` lemmas such as
`sum_apply` apply to `LocallyConstant X M`. -/
instance {X M : Type*} [TopologicalSpace X] [Zero M] : IsZeroApply (LocallyConstant X M) where

/-- Addition of locally constant functions is pointwise, so that the generic `FunLike` lemmas such
as `sum_apply` apply to `LocallyConstant X M`. -/
instance {X M : Type*} [TopologicalSpace X] [Add M] : IsAddApply (LocallyConstant X M) where

end LocallyConstant
