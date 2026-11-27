/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.LaurentSeries
import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Laurent expansions of rational functions

The Laurent expansion at `0` of a nonconstant rational function `p ∈ K(X)` is transcendental over
`K` in `K⸨X⸩`: the embedding `K(X) → K⸨X⸩` is an injective `K`-algebra map, and `p` itself is
transcendental over `K` by `RatFunc.transcendental_of_ne_C`.
The scalar tower `K → K(X) → K⸨X⸩` lets linear maps and derivations over `K(X)` be
restricted to `K`.

## Main results

* `RatFunc.isScalarTower_laurentSeries_algebra`, `RatFunc.isScalarTower_laurentSeries`:
  the scalar tower for the algebra-map and coefficientwise actions of `K` on `K⸨X⸩`.
* `RatFunc.transcendental_coe`: the Laurent expansion of a nonconstant rational function is
  transcendental over the constants.
-/

public section

open scoped LaurentSeries

namespace RatFunc

variable {K : Type*} [Field K]

/-- The scalar tower for the action of `K` on `K⸨X⸩` by multiplication by its image under
`algebraMap`. Algebraic lemmas such as `transcendental_algebraMap_iff` use this action.
The coefficientwise Hahn series action is definitionally distinct. -/
instance isScalarTower_laurentSeries_algebra :
    @IsScalarTower K (RatFunc K) K⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq (R := K) (S := RatFunc K) (A := K⸨X⸩) fun c ↦ by
    simp [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply,
      HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply']

/-- The scalar tower for the coefficientwise action of `K` on Laurent series, used by
`Derivation.restrictScalars` when the target is the Laurent series field. -/
instance isScalarTower_laurentSeries : IsScalarTower K (RatFunc K) K⸨X⸩ :=
  .of_algebraMap_smul fun c f ↦ by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
      TauCeti.laurentSeries_algebraMap_mul_eq_smul]

/-- The Laurent expansion at `0` of a nonconstant rational function is transcendental over the
field of constants. -/
theorem transcendental_coe {p : RatFunc K} (hp : ¬∃ c, p = C c) :
    Transcendental K (p : K⸨X⸩) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) K⸨X⸩).injective).mpr
    (p.transcendental_of_ne_C hp)

end RatFunc
