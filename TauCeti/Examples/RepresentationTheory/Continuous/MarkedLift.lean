/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.MarkedLift
public import Mathlib.RingTheory.DualNumber
public import Mathlib.Algebra.Field.ZMod

/-!
# Checks for marked residual lifts

* The identity marking makes the trivial representation on `A^n` a lift of the trivial
  representation on `k^n`; in fact every marking does.
* Over `𝔽₃[ε]`, multiplying a basis vector by `1 + ε` does not change its residual class, so the
  new basis lifts the same marked residual basis.
* A marking matters: if `ρbar g` is `diag(1, -1)` in a basis `e₀, e₁` of a residual
  representation in which `e₁ ≠ -e₁` (for instance over `𝔽₃`), then `ρ` cannot be a lift of
  `ρbar` both for a marking `ι` and for `ι` followed by the swap `e₀ ↔ e₁`.
-/

open IsLocalRing TauCeti.ContinuousRep
open scoped TensorProduct DualNumber

namespace TauCeti.Examples.MarkedLift

variable {Γ A : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [IsLocalRing A]

/-- The identity marking makes the trivial representation on `M` a lift of the trivial
representation on `k ⊗[A] M`. -/
example {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
    [TopologicalSpace (ResidueField A ⊗[A] M)] :
    IsLiftOf (trivial Γ A M) (trivial Γ (ResidueField A) (ResidueField A ⊗[A] M))
      (LinearEquiv.refl _ _) :=
  isLiftOf_trivial Γ _

/-- Over `𝔽₃[ε]`, multiplying a vector by `1 + ε` does not change its residual class. -/
example {M : Type*} [AddCommGroup M] [Module (ZMod 3)[ε] M] (m : M) :
    (1 : ResidueField (ZMod 3)[ε]) ⊗ₜ[(ZMod 3)[ε]] ((1 + ε : (ZMod 3)[ε]) • m) = 1 ⊗ₜ m := by
  have hε : residue (ZMod 3)[ε] ε = 0 := by
    rw [residue_eq_zero_iff, DualNumber.maximalIdeal_eq_span_singleton_eps]
    exact Ideal.subset_span rfl
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq, map_add,
    map_one, hε, add_zero]

/-- A swap of the residual basis of `diag(1, -1)` is not a second marking of the same lift. -/
example {M V : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M] [AddCommGroup V]
    [Module (ResidueField A) V] [TopologicalSpace V] (ρ : ContinuousRep Γ A M)
    (ρbar : ContinuousRep Γ (ResidueField A) V) (ι : ResidueField A ⊗[A] M ≃ₗ[ResidueField A] V)
    (s : V ≃ₗ[ResidueField A] V) (g : Γ) (e₀ e₁ : V) (hs : s e₀ = e₁) (h₀ : ρbar g e₀ = e₀)
    (h₁ : ρbar g e₁ = -e₁) (he : e₁ ≠ -e₁) :
    ¬ (IsLiftOf ρ ρbar ι ∧ IsLiftOf ρ ρbar (ι.trans s)) := by
  rintro ⟨h, h'⟩
  have := h.apply_comm h' g e₀
  rw [h₀, hs, h₁] at this
  exact he this

end TauCeti.Examples.MarkedLift
