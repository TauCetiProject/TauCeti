/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.FixedBasis

/-!
# Scalar extension of the pinned shell fixed lattice

For a pinned diagram action on the signed shell Lie algebra, the canonical map from the
scalar extension of its integral fixed lattice into the scalar-extended fixed module is always
injective. It is surjective exactly when there are no negative root cycles or the coefficient
ring has no `2`-torsion. Thus it is an equivalence over every ring without `2`-torsion, without
requiring flatness over `ℤ`. When negative cycles occur, the criterion also detects the extra
fixed vectors in characteristic two.

The comparison is the existing `LinearMap.fixedSubmoduleBaseChange`, not an independently
chosen map. The signed-permutation description of the Cartan/root basis identifies the obstruction
via `Module.Basis.fixedSubmoduleBaseChange_signedPerm_surjective_iff`: the Cartan cycles all have
positive signs, so only root cycles contribute. This compares the actual integral fixed lattice,
not a normalized folded Chevalley lattice.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.
-/

public section

open TensorProduct

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
  (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B) [Finite B.normTwoShell]
  (A : Type*) [CommRing A]

/-- Scalar extension embeds the integral fixed lattice of the pinned shell action. No
flatness or torsion hypothesis on the coefficient ring is needed. -/
theorem fixedSubmoduleBaseChange_injective :
    Function.Injective ((reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A) :=
  (basis B).fixedSubmoduleBaseChange_signedPerm_injective
    (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ))
    (Sum.elim (1 : I → ℤˣ) (fun a ↦ inversionSign B σ a))
    (reindex σ hσ).toLinearMap (reindex_basis σ hσ) A

/-- Negative root cycles are the only obstruction to surjectivity of scalar extension of
the integral fixed lattice: each such cycle contributes the coefficient ring's `2`-torsion. -/
theorem fixedSubmoduleBaseChange_surjective_iff :
    Function.Surjective ((reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A) ↔
      IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
        monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥ := by
  rw [(basis B).fixedSubmoduleBaseChange_signedPerm_surjective_iff
    (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ))
    (Sum.elim (1 : I → ℤˣ) (fun a ↦ inversionSign B σ a))
    (reindex σ hσ).toLinearMap (reindex_basis σ hσ)
    (Sum.map Quotient.out Quotient.out) (existsUnique_sameCycle_basis σ hσ) A]
  exact or_congr_left (negativeCycleEquiv σ hσ).isEmpty_congr

/-- If there are no negative root cycles or the coefficient ring has no `2`-torsion, the
actual scalar-extension comparison for the integral fixed lattice is an equivalence. -/
noncomputable def fixedSubmoduleBaseChangeEquiv
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥) :
    A ⊗[ℤ] (reindex σ hσ).toLinearMap.fixedSubmodule ≃ₗ[A]
      ((reindex σ hσ).toLinearMap.baseChange A).fixedSubmodule :=
  LinearEquiv.ofBijective ((reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A)
    ⟨fixedSubmoduleBaseChange_injective σ hσ A,
      (fixedSubmoduleBaseChange_surjective_iff σ hσ A).mpr hA⟩

/-- The equivalence is the canonical scalar extension of the fixed-lattice inclusion. -/
@[simp]
theorem fixedSubmoduleBaseChangeEquiv_apply
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥)
    (x : A ⊗[ℤ] (reindex σ hσ).toLinearMap.fixedSubmodule) :
    fixedSubmoduleBaseChangeEquiv σ hσ A hA x =
      (reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A x := by
  rfl

end Matrix.ShellLieAlgebra
