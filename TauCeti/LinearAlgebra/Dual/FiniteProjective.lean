/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.LinearAlgebra.Dual.Basis

/-!
# Opposite duals of finite projective modules

For a left module `M` over a possibly noncommutative semiring `R`, the dual
`Hom_R(M, R)` is a left `Rᵐᵒᵖ`-module, with scalars acting on the values on the right.
This file proves that this dual is finite projective when `M` is finite projective.
In particular, the duals of the projectives in a finite projective presentation are again
finite projectives, as required when forming the Auslander–Bridger transpose.

## Main results

* `TauCeti.oppositeDual_free`: the opposite dual of a finite free module is free.
* `TauCeti.oppositeDual_projective`: the opposite dual of a finite projective module is projective.
* `TauCeti.oppositeDual_finite`: the opposite dual of a finite projective module is finite.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

-- The free case transports the coordinates `Module.Basis.oppositeDualEquiv`. The other cases use
-- `Module.Finite.exists_comp_eq_id_of_projective`, following the retract argument of
-- `Module.dual_projective` and `Module.dual_finite` for commutative scalars.

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
