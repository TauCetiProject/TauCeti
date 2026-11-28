/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Reductive.Basic
import TauCeti.Algebra.Lie.Killing.Basic

/-!
# Cartan involutions on abelian Lie algebras

Every involutive automorphism of an abelian Lie algebra is a reductive Cartan involution, since
its derived ideal is `⊥` (`LieEquiv.isReductiveCartanInvolution_iff_of_isLieAbelian`), whereas by
`LieEquiv.IsCartanInvolution.not_isLieAbelian` no automorphism of a nontrivial abelian Lie algebra
is a (semisimple) Cartan involution.

In particular, on `ℝ` with the commutator bracket, `LieEquiv.refl` is a reductive Cartan involution
(`LieEquiv.isReductiveCartanInvolution_refl_real`), contrasting with
`TauCeti.not_isCartanInvolution_real`.

## Main results

* `LieEquiv.isReductiveCartanInvolution_iff_of_isLieAbelian`: on an abelian Lie algebra, an
  automorphism is a reductive Cartan involution iff it is involutive.
* `LieEquiv.isReductiveCartanInvolution_refl_real`: `LieEquiv.refl` on `ℝ` is a reductive Cartan
  involution.
-/

public section

open LieAlgebra

namespace LieEquiv

section Abelian

variable {K L : Type*} [Field K] [LinearOrder K] [LieRing L] [LieAlgebra K L]

/-- On an abelian Lie algebra, an automorphism is a reductive Cartan involution if and only if it
is involutive (its derived ideal is `⊥`). -/
theorem isReductiveCartanInvolution_iff_of_isLieAbelian [IsLieAbelian L] (θ : L ≃ₗ⁅K⁆ L) :
    θ.IsReductiveCartanInvolution ↔ Function.Involutive θ := by
  have hbot : derivedSeries K L 1 = ⊥ :=
    (LieAlgebra.abelian_iff_derived_one_eq_bot (⊤ : LieIdeal K L)).mp
      ((lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv).mpr inferInstance)
  rw [isReductiveCartanInvolution_iff]
  refine ⟨And.left, fun hinv ↦ ⟨hinv, ⟨θ.involutive_derivedSeriesCongr hinv 1, fun x hx ↦ ?_⟩⟩⟩
  have hx' : (x : L) ∈ (⊥ : LieIdeal K L) := hbot ▸ x.property
  exact False.elim (hx (Subtype.ext hx'))

end Abelian

section Real

attribute [local instance 100] LieRing.ofAssociativeRing

local instance : IsLieAbelian ℝ := isMulCommutative_iff_isLieAbelian.mp inferInstance

/-- On `ℝ` with the commutator bracket, the identity is a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_refl_real :
    (LieEquiv.refl : ℝ ≃ₗ⁅ℝ⁆ ℝ).IsReductiveCartanInvolution :=
  (isReductiveCartanInvolution_iff_of_isLieAbelian LieEquiv.refl).mpr fun _ ↦ rfl

end Real

end LieEquiv
