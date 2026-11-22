/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Algebra.Lie.CartanInvolution.Reductive
import TauCeti.Algebra.Lie.Killing.Basic

/-!
# Cartan involutions on abelian Lie algebras

Every involutive automorphism of an abelian Lie algebra is a reductive Cartan involution, since
its derived ideal is `⊥` (`LieEquiv.isReductiveCartanInvolution_iff_of_isLieAbelian`), whereas no
automorphism of a nontrivial abelian Lie algebra is a (semisimple) Cartan involution, because its
Killing form vanishes identically (`LieEquiv.not_isCartanInvolution_of_isLieAbelian`).

In particular, on `ℝ` with the commutator bracket, `LieEquiv.refl` is a reductive Cartan involution
(`LieEquiv.isReductiveCartanInvolution_refl_real`) but not a Cartan involution
(`LieEquiv.not_isCartanInvolution_refl_real`).

## Main results

* `LieEquiv.isReductiveCartanInvolution_iff_of_isLieAbelian`: on an abelian Lie algebra, an
  automorphism is a reductive Cartan involution iff it is involutive.
* `LieEquiv.not_isCartanInvolution_of_isLieAbelian`: no automorphism of a nontrivial abelian Lie
  algebra is a Cartan involution.
* `LieEquiv.isReductiveCartanInvolution_refl_real` and `LieEquiv.not_isCartanInvolution_refl_real`:
  `LieEquiv.refl` on `ℝ` is a reductive Cartan involution but not a Cartan involution.
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

/-- No automorphism of a nontrivial abelian Lie algebra is a (semisimple) Cartan involution, since
the Killing form vanishes identically. -/
theorem not_isCartanInvolution_of_isLieAbelian [Nontrivial L] [IsLieAbelian L] (θ : L ≃ₗ⁅K⁆ L) :
    ¬ θ.IsCartanInvolution := fun hθ ↦
  have := hθ.isKilling
  not_subsingleton L (TauCeti.subsingleton_of_isKilling_of_isLieAbelian K L)

end Abelian

section Real

attribute [local instance 100] LieRing.ofAssociativeRing

/-- On `ℝ` with the commutator bracket, the identity is a reductive Cartan involution. -/
theorem isReductiveCartanInvolution_refl_real :
    (LieEquiv.refl : ℝ ≃ₗ⁅ℝ⁆ ℝ).IsReductiveCartanInvolution := by
  have : IsLieAbelian ℝ :=
    ⟨fun x y ↦ by rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self]⟩
  exact (isReductiveCartanInvolution_iff_of_isLieAbelian LieEquiv.refl).mpr fun _ ↦ rfl

/-- On `ℝ` with the commutator bracket, the identity is not a (semisimple) Cartan involution. -/
theorem not_isCartanInvolution_refl_real :
    ¬ (LieEquiv.refl : ℝ ≃ₗ⁅ℝ⁆ ℝ).IsCartanInvolution := by
  have : IsLieAbelian ℝ :=
    ⟨fun x y ↦ by rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self]⟩
  exact not_isCartanInvolution_of_isLieAbelian LieEquiv.refl

end Real

end LieEquiv
