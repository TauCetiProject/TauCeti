/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Affine equivalences

This file records computations with affine equivalences. In particular, identifying the
commutator of two homotheties as a translation supports affine representations that detect
infinite-order elements, such as those used for Euclidean triangle groups.

## Main results

* `TauCeti.AffineEquiv.commutatorElement_homothetyUnitsMulHom_zero_one`: the commutator of
  homotheties about `0` and `1` is a translation.
-/

public section

open scoped commutatorElement

namespace TauCeti

namespace AffineEquiv

variable {K : Type*} [Field K]

/-- The commutator of homotheties with ratios `ω` and `η` about `0` and `1`, respectively, is
translation by `(ω - 1) * (1 - η)`. -/
@[simp]
theorem commutatorElement_homothetyUnitsMulHom_zero_one (ω η : Kˣ) :
    ⁅_root_.AffineEquiv.homothetyUnitsMulHom (0 : K) ω,
        _root_.AffineEquiv.homothetyUnitsMulHom (1 : K) η⁆ =
      _root_.AffineEquiv.constVAdd K K (((ω : K) - 1) * (1 - η)) := by
  rw [commutatorElement_def, ← map_inv, ← map_inv]
  ext z
  simp only [_root_.AffineEquiv.coe_mul, Function.comp_apply,
    _root_.AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply, vsub_eq_sub,
    vadd_eq_add, smul_eq_mul, Units.val_inv_eq_inv_val, _root_.AffineEquiv.constVAdd_apply]
  field_simp
  ring

end AffineEquiv

end TauCeti
