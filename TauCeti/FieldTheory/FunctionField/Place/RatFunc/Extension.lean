/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# Places over a finite place of the rational function field

In any algebraic extension of `k(X)`, a place lies over the place of an irreducible polynomial
exactly when that polynomial vanishes there.

## Main results

* `TauCeti.Place.restrict_eq_adicOfIrreducible_iff`: a place of an algebraic extension of `k(X)`
  lies over the place of an irreducible polynomial `q` exactly when `q` vanishes there.
-/

public section

namespace TauCeti

namespace Place

variable {k k' F' : Type*} [Field k] [Field k'] [Field F'] [Algebra k k'] [Algebra k' F']
variable [Algebra (RatFunc k) F'] [Algebra k F'] [IsScalarTower k k' F']
variable [IsScalarTower k (RatFunc k) F'] [Algebra.IsIntegral (RatFunc k) F']

open Polynomial in
/-- **A place lies over the place of an irreducible polynomial `q` of `k(X)` exactly when `q`
vanishes there**, in any algebraic extension of `k(X)`. -/
theorem restrict_eq_adicOfIrreducible_iff {q : k[X]} (hq : Irreducible q) (Q : Place k' F') :
    Q.restrict k (RatFunc k) = adicOfIrreducible hq ↔
      0 < Q.ord (algebraMap (RatFunc k) F' (algebraMap k[X] (RatFunc k) q)) := by
  rw [← ord_algebraMap_pos_iff hq, ord_algebraMap_restrict k (RatFunc k) Q]
  have he : (0 : ℤ) < ramificationIdx (RatFunc k) Q := by
    exact_mod_cast ramificationIdx_pos (RatFunc k) Q
  exact ⟨fun h ↦ mul_pos he h, fun h ↦ pos_of_mul_pos_right h he.le⟩

end Place

end TauCeti
