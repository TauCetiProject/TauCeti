/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Semiconjugacy and intertwining for multiplicative equivalences

An isomorphism `ψ : M ≃* M'` intertwines two endomorphisms `F : M →* M` and `F' : M' →* M'`
when `(ψ : M →* M').comp F = F'.comp (ψ : M →* M')`. This is `Function.Semiconj ψ F F'` packaged
for bundled monoid homomorphisms.

This file provides the inversion and composition laws for such intertwining relations, which
show that intertwining by an isomorphism is symmetric and transitive.

## Main results

* `MulEquiv.symm_comp_eq_comp_symm_of_comp_eq_comp`: an intertwining relation inverts along
  `ψ.symm`.
* `TauCeti.trans_comp_eq_comp_trans_of_comp_eq_comp`: intertwining relations compose along
  `ψ.trans χ`.
-/

public section

namespace MulEquiv

variable {M M' : Type*} [MulOneClass M] [MulOneClass M']
  {F : M →* M} {F' : M' →* M'}

/-- An isomorphism intertwining two endomorphisms has an inverse intertwining them the other way.

The equation is not symmetric in `ψ` and `ψ.symm`, so this provides the symmetry direction for
intertwining relations. -/
theorem symm_comp_eq_comp_symm_of_comp_eq_comp (ψ : M ≃* M')
    (hψ : (ψ : M →* M').comp F = F'.comp (ψ : M →* M')) :
    (ψ.symm : M' →* M).comp F' = F.comp (ψ.symm : M' →* M) :=
  have h : Function.Semiconj ψ F F' := fun x => DFunLike.congr_fun hψ x
  MonoidHom.ext (h.inverse_left ψ.symm_apply_apply ψ.apply_symm_apply)

end MulEquiv

namespace TauCeti

variable {M M' M'' : Type*} [MulOneClass M] [MulOneClass M'] [MulOneClass M'']
  {F : M →* M} {F' : M' →* M'} {F'' : M'' →* M''}

/-- Intertwining relations compose. -/
theorem trans_comp_eq_comp_trans_of_comp_eq_comp {ψ : M ≃* M'} {χ : M' ≃* M''}
    (hψ : (ψ : M →* M').comp F = F'.comp (ψ : M →* M'))
    (hχ : (χ : M' →* M'').comp F' = F''.comp (χ : M' →* M'')) :
    ((ψ.trans χ : M ≃* M'') : M →* M'').comp F = F''.comp ((ψ.trans χ : M ≃* M'') : M →* M'') :=
  have h₁ : Function.Semiconj ψ F F' := fun x => DFunLike.congr_fun hψ x
  have h₂ : Function.Semiconj χ F' F'' := fun x => DFunLike.congr_fun hχ x
  MonoidHom.ext (h₁.trans h₂)

end TauCeti
