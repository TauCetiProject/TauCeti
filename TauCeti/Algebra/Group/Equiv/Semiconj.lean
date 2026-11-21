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

* `MulEquiv.symm_comp_eq_comp_symm_iff`: `ψ.symm` intertwines `F'` with `F` exactly when `ψ`
  intertwines `F` with `F'`.
* `TauCeti.trans_comp_eq_comp_trans_of_comp_eq_comp`: intertwining relations compose along
  `ψ.trans χ`.
-/

public section

namespace MulEquiv

variable {M M' : Type*} [MulOneClass M] [MulOneClass M']
  {F : M →* M} {F' : M' →* M'}

/-- An isomorphism intertwines two endomorphisms exactly when its inverse intertwines them the
other way.

The equation is not symmetric in `ψ` and `ψ.symm`, so this provides the symmetry law for
intertwining relations. -/
@[simp]
theorem symm_comp_eq_comp_symm_iff (ψ : M ≃* M') :
    (ψ.symm : M' →* M).comp F' = F.comp (ψ.symm : M' →* M) ↔
      (ψ : M →* M').comp F = F'.comp (ψ : M →* M') :=
  ⟨fun h => MonoidHom.ext <| Function.Semiconj.inverse_left (f := ψ.symm) (DFunLike.congr_fun h)
      ψ.apply_symm_apply ψ.symm_apply_apply,
    fun h => MonoidHom.ext <| Function.Semiconj.inverse_left (f := ψ) (DFunLike.congr_fun h)
      ψ.symm_apply_apply ψ.apply_symm_apply⟩

end MulEquiv

namespace TauCeti

variable {M M' M'' : Type*} [MulOneClass M] [MulOneClass M'] [MulOneClass M'']
  {F : M →* M} {F' : M' →* M'} {F'' : M'' →* M''}

/-- Intertwining relations compose. -/
theorem trans_comp_eq_comp_trans_of_comp_eq_comp {ψ : M ≃* M'} {χ : M' ≃* M''}
    (hψ : (ψ : M →* M').comp F = F'.comp (ψ : M →* M'))
    (hχ : (χ : M' →* M'').comp F' = F''.comp (χ : M' →* M'')) :
    ((ψ.trans χ : M ≃* M'') : M →* M'').comp F = F''.comp ((ψ.trans χ : M ≃* M'') : M →* M'') :=
  MonoidHom.ext <| Function.Semiconj.trans (fab := ψ) (fbc := χ) (DFunLike.congr_fun hψ)
    (DFunLike.congr_fun hχ)

end TauCeti
