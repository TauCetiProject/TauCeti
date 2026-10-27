/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Module.Dual
public import TauCeti.QuantumGroups.UqSl2.Antipode

/-!
# Double contragredients of `U_q(sl₂)`-modules

The square of the antipode is conjugation by `K⁻¹`. Consequently the map
`v ↦ (φ ↦ φ(K⁻¹v))` identifies a finite-dimensional module with its double contragredient.
This file constructs that linear equivalence and proves that it intertwines the actual
representations and is natural in module maps. It applies to every nonzero parameter,
without a genericity or type-1 assumption.

These are the underlying representation maps for the pivotal comparison. No categorical
rigidity or monoidal structure is asserted here. The construction specializes
`AlgHom.hopfPivotEquiv` using the antipode square proved in `UqSl2.Antipode`.

## References

* C. Kassel, *Quantum Groups*, Chapter XIV, for dual and pivotal conventions.
* A. Virelizier, *Quantum groups*, Section 2.3, for the rank-one Hopf convention.
-/

public noncomputable section

open Module

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]
  (V : Type*) [AddCommGroup V] [Module ℂ V]
  [Module (UqSl2 q) V] [IsScalarTower ℂ (UqSl2 q) V] [FiniteDimensional ℂ V]

/-- The double-contragredient comparison `v ↦ (φ ↦ φ(K⁻¹v))`. -/
def doubleDualEquiv : V ≃ₗ[ℂ] Dual ℂ (Dual ℂ V) :=
  (Algebra.lsmul ℂ ℂ V).hopfPivotEquiv (kUnit q)⁻¹

/-- The comparison evaluates a functional at `K⁻¹v`. -/
@[simp]
theorem doubleDualEquiv_apply (v : V) (φ : Dual ℂ V) :
    doubleDualEquiv q V v φ = φ (kInv q • v) := by
  simp [doubleDualEquiv]

/-- Its inverse acts by `K` after ordinary double-dual evaluation. -/
@[simp]
theorem doubleDualEquiv_symm_apply (Φ : Dual ℂ (Dual ℂ V)) :
    (doubleDualEquiv q V).symm Φ = k q • (Module.evalEquiv ℂ V).symm Φ := by
  simp [doubleDualEquiv]

/-- The comparison intertwines the original action with the double contragredient action. -/
theorem doubleDualEquiv_smul (a : UqSl2 q) (v : V) :
    doubleDualEquiv q V (a • v) =
      (Algebra.lsmul ℂ ℂ V).hopfDual.hopfDual a (doubleDualEquiv q V v) :=
  (Algebra.lsmul ℂ ℂ V).hopfPivotEquiv_intertwines (kUnit q)⁻¹
    (fun a => by simpa using antipode_antipode q a) a v

end TauCeti.UqSl2

namespace LinearMap

open TauCeti.UqSl2

variable {q : ℂ} [Fact (q ≠ 0)] {V W : Type*}
  [AddCommGroup V] [Module ℂ V] [Module (TauCeti.UqSl2 q) V]
  [IsScalarTower ℂ (TauCeti.UqSl2 q) V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [Module (TauCeti.UqSl2 q) W]
  [IsScalarTower ℂ (TauCeti.UqSl2 q) W] [FiniteDimensional ℂ W]

/-- The `K⁻¹` double-dual comparison is natural in module homomorphisms. -/
theorem uqSl2_doubleDualEquiv_natural (f : V →ₗ[TauCeti.UqSl2 q] W) (v : V) :
    (f.restrictScalars ℂ).dualMap.dualMap (doubleDualEquiv q V v) =
      doubleDualEquiv q W (f v) := by
  exact (f.restrictScalars ℂ).hopfPivotEquiv_natural
    (ρ := Algebra.lsmul ℂ ℂ V) (σ := Algebra.lsmul ℂ ℂ W)
    (fun a v => f.map_smul a v) (kUnit q)⁻¹ v

end LinearMap
