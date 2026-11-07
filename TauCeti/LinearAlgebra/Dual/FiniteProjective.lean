/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Opposite duals of finite projective modules

For a left module `M` over a possibly noncommutative semiring `R`, the dual
`Hom_R(M, R)` is a left `Rᵐᵒᵖ`-module, with scalars acting on the values on the right.
This file proves that this dual is finite projective when `M` is finite projective.
In particular, the duals of the projectives in a finite projective presentation are again
finite projectives, as required when forming the Auslander–Bridger transpose.

## Main results

* `Module.Basis.oppositeDualEquiv`: a basis indexed by `ι` identifies the dual, as a module over
  the opposite semiring, with `ι → Rᵐᵒᵖ`.
* `TauCeti.oppositeDual_free`: the opposite dual of a finite free module is free.
* `TauCeti.oppositeDual_projective`: the opposite dual of a finite projective module is projective.
* `TauCeti.oppositeDual_finite`: the opposite dual of a finite projective module is finite.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- The constructions use Mathlib's `Module.Basis.constr` and
-- `Module.Finite.exists_comp_eq_id_of_projective`, following the retract argument of
-- `Module.dual_projective` and `Module.dual_finite` for commutative scalars.

/-- A basis `b` of `M` identifies the dual `Hom_R(M, R)`, as a left `Rᵐᵒᵖ`-module, with the
coordinate module `ι → Rᵐᵒᵖ`, by evaluating a functional at the basis vectors. -/
noncomputable def _root_.Module.Basis.oppositeDualEquiv {ι : Type*} (b : Module.Basis ι R M) :
    Module.Dual R M ≃ₗ[Rᵐᵒᵖ] (ι → Rᵐᵒᵖ) :=
  (b.constr Rᵐᵒᵖ (M' := R)).symm ≪≫ₗ .piCongrRight fun _ => MulOpposite.opLinearEquiv Rᵐᵒᵖ

/-- The coordinates of a functional are its values at the basis vectors. -/
@[simp]
theorem _root_.Module.Basis.oppositeDualEquiv_apply {ι : Type*} (b : Module.Basis ι R M)
    (φ : Module.Dual R M) (i : ι) : b.oppositeDualEquiv φ i = MulOpposite.op (φ (b i)) := (rfl)

/-- The functional with given coordinates takes those values at the basis vectors. -/
@[simp]
theorem _root_.Module.Basis.oppositeDualEquiv_symm_apply_self {ι : Type*}
    (b : Module.Basis ι R M) (v : ι → Rᵐᵒᵖ) (i : ι) :
    b.oppositeDualEquiv.symm v (b i) = (v i).unop := by
  simp [Module.Basis.oppositeDualEquiv]

variable [Module.Finite R M]

/-- The dual of a finite free left module is free over the opposite semiring. -/
instance oppositeDual_free [Module.Free R M] :
    Module.Free Rᵐᵒᵖ (Module.Dual R M) :=
  .of_equiv (Module.Free.chooseBasis R M).oppositeDualEquiv.symm

/-- The opposite dual of a finite projective module is a retract of the opposite dual of a
finite free module. -/
private theorem exists_oppositeDual_retract [Module.Projective R M] :
    ∃ (n : ℕ) (i : Module.Dual R M →ₗ[Rᵐᵒᵖ] Module.Dual R (Fin n → R))
      (s : Module.Dual R (Fin n → R) →ₗ[Rᵐᵒᵖ] Module.Dual R M), s ∘ₗ i = .id := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨n, f.lcomp Rᵐᵒᵖ R, g.lcomp Rᵐᵒᵖ R, ?_⟩
  ext φ x
  simp [← LinearMap.comp_apply f g, hfg]

/-- The dual of a finite projective left module is projective over the opposite semiring. -/
instance oppositeDual_projective [Module.Projective R M] :
    Module.Projective Rᵐᵒᵖ (Module.Dual R M) :=
  have ⟨_, i, s, hsi⟩ := exists_oppositeDual_retract (R := R) (M := M)
  .of_split i s hsi

/-- The dual of a finite projective left module is finitely generated over the opposite semiring. -/
instance oppositeDual_finite [Module.Projective R M] :
    Module.Finite Rᵐᵒᵖ (Module.Dual R M) :=
  have ⟨n, i, s, hsi⟩ := exists_oppositeDual_retract (R := R) (M := M)
  have := Module.Finite.equiv (Pi.basisFun R (Fin n)).oppositeDualEquiv.symm
  .of_surjective s (LinearMap.surjective_of_comp_eq_id i s hsi)

end TauCeti
