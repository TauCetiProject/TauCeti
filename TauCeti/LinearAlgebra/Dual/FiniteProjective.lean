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

* `TauCeti.oppositeDual_free`: the opposite dual of a finite free module is free.
* `TauCeti.oppositeDual_projective`: the opposite dual of a finite projective module is projective.
* `TauCeti.oppositeDual_finite`: the opposite dual of a finite projective module is finite.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
-/

public section

namespace TauCeti

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]

-- The constructions use Mathlib's `Module.Basis.constr` and
-- `Module.Finite.exists_comp_eq_id_of_projective`, following the retract argument of
-- `Module.dual_projective` and `Module.dual_finite` for commutative scalars.

/-- The dual of a finite free left module is free over the opposite semiring. -/
noncomputable instance oppositeDual_free [Module.Free R M] :
    Module.Free Rᵐᵒᵖ (Module.Dual R M) := by
  let b := Module.Free.chooseBasis R M
  let e := (b.constr Rᵐᵒᵖ (M' := R)).symm.trans
    (LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Rᵐᵒᵖ)
  exact Module.Free.of_equiv e.symm

/-- The dual of a finite projective left module is projective over the opposite semiring. -/
instance oppositeDual_projective [Module.Projective R M] :
    Module.Projective Rᵐᵒᵖ (Module.Dual R M) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  apply Module.Projective.of_split (f.lcomp Rᵐᵒᵖ R) (g.lcomp Rᵐᵒᵖ R)
  ext φ x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.lcomp_apply] using
    congrArg φ (LinearMap.congr_fun hfg x)

/-- The dual of a finite projective left module is finitely generated over the opposite semiring. -/
instance oppositeDual_finite [Module.Projective R M] :
    Module.Finite Rᵐᵒᵖ (Module.Dual R M) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let e := ((Pi.basisFun R (Fin n)).constr Rᵐᵒᵖ (M' := R)).symm.trans
    (LinearEquiv.piCongrRight fun _ => MulOpposite.opLinearEquiv Rᵐᵒᵖ)
  have : Module.Finite Rᵐᵒᵖ (Module.Dual R (Fin n → R)) := Module.Finite.equiv e.symm
  apply Module.Finite.of_surjective (g.lcomp Rᵐᵒᵖ R)
  intro φ
  refine ⟨f.lcomp Rᵐᵒᵖ R φ, ?_⟩
  ext x
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.lcomp_apply] using
    congrArg φ (LinearMap.congr_fun hfg x)

end TauCeti
