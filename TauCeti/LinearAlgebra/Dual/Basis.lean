/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Duals of modules with a basis

For a left module `M` over a possibly noncommutative semiring `R`, the dual
`Hom_R(M, R)` is a left `Rᵐᵒᵖ`-module, with scalars acting on the values on the right.
A basis of `M` indexed by `ι` identifies this dual with the coordinate module `ι → Rᵐᵒᵖ`,
by evaluating a functional at the basis vectors. No finiteness is assumed.

The linear dual of a finite free module over a commutative ring has the same rank as the module,
since a finite basis identifies the module with its dual (`Module.Basis.toDualEquiv`). Over a
field this is Mathlib's `Subspace.dual_finrank_eq`.

## Main definitions

* `Module.Basis.oppositeDualEquiv`: a basis indexed by `ι` identifies the dual, as a module over
  the opposite semiring, with `ι → Rᵐᵒᵖ`.

## Main results

* `TauCeti.Module.dual_finrank_eq`: `finrank R (Dual R M) = finrank R M` for a finite free
  module `M`.
-/

public section

namespace Module.Basis

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- The construction is Mathlib's `Module.Basis.constr` with values in `R`, viewed as an
-- `Rᵐᵒᵖ`-linear map, followed by `MulOpposite.opLinearEquiv` in each coordinate.

/-- A basis `b` of `M` identifies the dual `Hom_R(M, R)`, as a left `Rᵐᵒᵖ`-module, with the
coordinate module `ι → Rᵐᵒᵖ`, by evaluating a functional at the basis vectors. -/
noncomputable def oppositeDualEquiv (b : Basis ι R M) :
    Module.Dual R M ≃ₗ[Rᵐᵒᵖ] (ι → Rᵐᵒᵖ) :=
  (b.constr Rᵐᵒᵖ (M' := R)).symm ≪≫ₗ .piCongrRight fun _ => MulOpposite.opLinearEquiv Rᵐᵒᵖ

/-- The coordinates of a functional are its values at the basis vectors. -/
@[simp]
theorem oppositeDualEquiv_apply (b : Basis ι R M) (φ : Module.Dual R M) (i : ι) :
    b.oppositeDualEquiv φ i = MulOpposite.op (φ (b i)) := (rfl)

/-- The functional with given coordinates takes those values at the basis vectors. -/
@[simp]
theorem oppositeDualEquiv_symm_apply_self (b : Basis ι R M) (v : ι → Rᵐᵒᵖ) (i : ι) :
    b.oppositeDualEquiv.symm v (b i) = (v i).unop := by
  simp [oppositeDualEquiv]

end Module.Basis

namespace TauCeti.Module

/-- A finite free module and its linear dual have the same rank. Over a field this is
`Subspace.dual_finrank_eq`. -/
@[simp]
theorem dual_finrank_eq (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (Module.Dual R M) = Module.finrank R M := by
  classical
  exact (Module.Free.chooseBasis R M).toDualEquiv.finrank_eq.symm

end TauCeti.Module
