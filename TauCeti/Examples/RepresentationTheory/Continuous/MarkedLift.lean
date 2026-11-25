/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.MarkedLift
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.DualNumber
public import Mathlib.Algebra.Field.ZMod

/-!
# Checks for marked residual lifts

* The identity marking makes the trivial representation on `A^n` a lift of the trivial
  representation on `k^n`; in fact every marking does.
* Over `𝔽₃[ε]`, multiplying a basis vector by `1 + ε` does not change its residual class, so the
  new basis lifts the same marked residual basis.
* Two bases lifting the same residual basis differ by a matrix reducing to `1`.
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
  rw [← TensorProduct.smul_tmul]
  simp [Algebra.smul_def, hε]

/-- Two bases of `M` lifting the same residual basis differ by a matrix reducing to `1`. -/
example {M n : Type*} [AddCommGroup M] [Module A M] [DecidableEq n] (b b' : Module.Basis n A M)
    (h : ∀ i, (1 : ResidueField A) ⊗ₜ[A] b i = 1 ⊗ₜ b' i) :
    (b.toMatrix b').map (residue A) = 1 := by
  simpa [ResidueField.algebraMap_eq] using b.toMatrix_map_algebraMap_eq_one b' h

/-- A swap of the residual basis of `diag(1, -1)` is not a second marking of the same lift. -/
example {M V : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M] [AddCommGroup V]
    [Module (ResidueField A) V] [TopologicalSpace V] (ρ : ContinuousRep Γ A M)
    (ρbar : ContinuousRep Γ (ResidueField A) V) (ι : ResidueField A ⊗[A] M ≃ₗ[ResidueField A] V)
    (s : V ≃ₗ[ResidueField A] V) (g : Γ) (e₀ e₁ : V) (hs : s e₀ = e₁) (h₀ : ρbar g e₀ = e₀)
    (h₁ : ρbar g e₁ = -e₁) (he : e₁ ≠ -e₁) :
    ¬ (IsLiftOf ρ ρbar ι ∧ IsLiftOf ρ ρbar (ι.trans s)) := by
  rintro ⟨h, h'⟩
  have := (h.trans_iff.1 h').isIntertwining g e₀
  simp only [coe_toRepresentation, LinearEquiv.coe_coe, h₀, hs, h₁] at this
  exact he this

end TauCeti.Examples.MarkedLift
