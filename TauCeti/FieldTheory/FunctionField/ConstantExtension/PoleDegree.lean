/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula
import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint.Basic

/-!
# Pole divisor degrees under linearly disjoint constant extensions

For a function field `F / k`, a linearly disjoint constant field extension `F' = F · k'` preserves
the degree `[F : k(x)]` over any element `x : F`, and therefore preserves the degree of the pole
divisor `(x)_∞` of a transcendental element `x : F`.

## Main results

* `TauCeti.Divisor.degree_poles_eq_of_linearDisjoint`: under linear disjointness, the pole divisor
  of a transcendental element `x : F` retains degree `[F : k(x)]` in `F' = F · k'`.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Under linear disjointness, the pole divisor of a transcendental element `x : F` retains degree
`[F : k(x)]` in `F' = F · k'`. -/
theorem Divisor.degree_poles_eq_of_linearDisjoint (hF : IsFunctionField k F)
    (h : constantCompositum F k' F' = ⊤)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hF' : IsFunctionField k' F') {x : F} (hx : Transcendental k x) :
    Divisor.degree (Divisor.poles hF'
      (Units.map (algebraMap F F' : F →* F') (Units.mk0 x hx.ne_zero))) =
      Module.finrank k⟮x⟯ F := by
  have := hF.finiteDimensional_adjoin hx
  have hx' : Transcendental k' (algebraMap F F' x) := H.transcendental_algebraMap hx
  have := hF'.finiteDimensional_adjoin hx'
  exact (Divisor.degree_poles hF' _ (by simpa [Transcendental] using hx')).trans
    (by exact_mod_cast finrank_over_adjoin_simple_eq_of_linearDisjoint H h x)

end TauCeti
