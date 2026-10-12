/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.GroupAlgebra.Cancellation
public import TauCeti.NumberTheory.Padics.GroupAlgebra.Swan
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Finiteness.Prod
import TauCeti.RingTheory.KrullSchmidt.FractionRing

/-!
# From a stable isomorphism to an isomorphism over `ℤ_p[G]`

Let `G` be a finite group. If two `ℤ_p[G]`-modules become isomorphic after adding finitely
generated projective modules, `M ⊕ P ≃ N ⊕ Q`, and their rationalizations differ by the
rationalization of a finitely generated projective module `F`, `M ⊗ ℚ_p ≃ (N ⊕ F) ⊗ ℚ_p`, then
already `M ≃ N ⊕ F` (NSW (5.6.11)). For `F = ℤ_p[G]^m` this turns a stable isomorphism into an
isomorphism `M ≃ N ⊕ ℤ_p[G]^m` once the rational representations are known.

The proof has three steps. Rationalizing the stable isomorphism and cancelling the rational
representation `N ⊗ ℚ_p` gives `(F ⊕ P) ⊗ ℚ_p ≃ Q ⊗ ℚ_p`. Swan's theorem then gives
`F ⊕ P ≃ Q`, since both are finitely generated projective. Finally `M ⊕ P ≃ N ⊕ F ⊕ P`, and
Krull-Schmidt cancellation of `P` over `ℤ_p[G]` gives `M ≃ N ⊕ F`.

## Main results

* `TauCeti.nonempty_linearEquiv_prod_of_stable`: a stable isomorphism `M ⊕ P ≃ N ⊕ Q` together with
  `M ⊗ ℚ_p ≃ (N ⊕ F) ⊗ ℚ_p` for a finitely generated projective `F` gives `M ≃ N ⊕ F`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.11).
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

local notation "A" => MonoidAlgebra ℤ_[p] G

/-- **From a stable isomorphism to an isomorphism** (NSW (5.6.11)). Let `G` be a finite group and
let `M`, `N` be `ℤ_p[G]`-modules with `N` finitely generated over `ℤ_p`. Suppose that
`M ⊕ P ≃ N ⊕ Q` for finitely generated projective `ℤ_p[G]`-modules `P` and `Q`, and that
`M ⊗ ℚ_p ≃ (N ⊕ F) ⊗ ℚ_p` for a finitely generated projective `ℤ_p[G]`-module `F`. Then
`M ≃ N ⊕ F` as `ℤ_p[G]`-modules. The case of interest is the free module `F = ℤ_p[G]^m`. -/
theorem nonempty_linearEquiv_prod_of_stable
    {M N F P Q : Type*}
    [AddCommGroup M] [Module ℤ_[p] M] [Module A M] [IsScalarTower ℤ_[p] A M]
    [AddCommGroup N] [Module ℤ_[p] N] [Module A N] [IsScalarTower ℤ_[p] A N]
    [Module.Finite ℤ_[p] N]
    [AddCommGroup F] [Module ℤ_[p] F] [Module A F] [IsScalarTower ℤ_[p] A F]
    [Module.Finite A F] [Module.Projective A F]
    [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P]
    [AddCommGroup Q] [Module A Q] [Module.Finite A Q] [Module.Projective A Q]
    (h : Nonempty ((M × P) ≃ₗ[A] (N × Q)))
    (hrat : Nonempty ((M ⊗[ℤ_[p]] ℚ_[p]) ≃ₗ[A] ((N × F) ⊗[ℤ_[p]] ℚ_[p]))) :
    Nonempty (M ≃ₗ[A] (N × F)) := by
  obtain ⟨e⟩ := h
  obtain ⟨φ⟩ := hrat
  -- Restrict the scalars of `P` and `Q` to `ℤ_p`, so that they can be rationalized.
  let _ : Module ℤ_[p] P := .compHom P (algebraMap ℤ_[p] A)
  have : IsScalarTower ℤ_[p] A P := .of_compHom _ _ _
  let _ : Module ℤ_[p] Q := .compHom Q (algebraMap ℤ_[p] A)
  have : IsScalarTower ℤ_[p] A Q := .of_compHom _ _ _
  -- Rationally, `(F × P) × N ≃ (N × F) × P ≃ M × P ≃ N × Q ≃ Q × N`; cancel `N ⊗ ℚ_p`.
  obtain ⟨g⟩ := IsFractionRing.nonempty_tensor_linearEquiv_of_prod_tensor_linearEquiv ℚ_[p]
    (M := F × P) (N := Q) (P := N)
    ⟨TensorProduct.AlgebraTensorModule.congr
        ((LinearEquiv.prodComm A (F × P) N).trans (LinearEquiv.prodAssoc A N F P).symm)
        (LinearEquiv.refl ℤ_[p] ℚ_[p]) ≪≫ₗ
      TensorProduct.prodLeft ℤ_[p] A (N × F) P ℚ_[p] ≪≫ₗ
      φ.symm.prodCongr (LinearEquiv.refl A _) ≪≫ₗ
      (TensorProduct.prodLeft ℤ_[p] A M P ℚ_[p]).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (e.trans (LinearEquiv.prodComm A N Q))
        (LinearEquiv.refl ℤ_[p] ℚ_[p])⟩
  -- Swan's theorem identifies the projective modules `F × P` and `Q`.
  obtain ⟨ψ⟩ := nonempty_linearEquiv_of_projective_of_tensorRat p (F × P) Q ⟨g⟩
  -- Now `M × P ≃ N × Q ≃ (N × F) × P`, and `P` cancels.
  exact nonempty_linearEquiv_of_prod_linearEquiv p G M (N × F) P
    ⟨e ≪≫ₗ (LinearEquiv.refl A N).prodCongr ψ.symm ≪≫ₗ (LinearEquiv.prodAssoc A N F P).symm⟩

end TauCeti
