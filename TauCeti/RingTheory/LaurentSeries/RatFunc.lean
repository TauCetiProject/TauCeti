/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.FieldTheory.RatFunc.PowerTower
public import TauCeti.RingTheory.LaurentSeries.Ramified
import TauCeti.RingTheory.LaurentSeries.Basic

/-!
# Laurent expansions of rational functions

The Laurent expansion at `0` of a nonconstant rational function `p ∈ K(X)` is transcendental over
`K` in `K⸨X⸩`: the embedding `K(X) → K⸨X⸩` is an injective `K`-algebra map, and `p` itself is
transcendental over `K` by `RatFunc.transcendental_of_ne_C`.
The scalar tower `K → K(X) → K⸨X⸩` lets linear maps and derivations over `K(X)` be
restricted to `K`.

Moreover, substituting `X ↦ X ^ N` on rational functions (`RatFunc.expand K N`) is compatible with
Laurent-series expansion `LaurentSeries.expand K N` via the embedding `K(X) → K⸨X⸩`.

## Main results

* `RatFunc.coe_C`: the Laurent expansion of `RatFunc.C c` is `HahnSeries.C c`.
* `RatFunc.isScalarTower_laurentSeries_algebra`, `RatFunc.isScalarTower_laurentSeries`:
  the scalar tower for the algebra-map and coefficientwise actions of `K` on `K⸨X⸩`.
* `RatFunc.transcendental_coe`: the Laurent expansion of a nonconstant rational function is
  transcendental over the constants.
* `LaurentSeries.expand_algebraMap_ratFunc` and `LaurentSeries.expand_comp_algebraMap_ratFunc`:
  evaluating `r(X ^ N)` in `K⸨X⸩` agrees with applying `LaurentSeries.expand K N` to `r`.
* `LaurentSeries.isAlgebraic_powerSeriesPart`: `g.powerSeriesPart` is algebraic over `K(X)`
  whenever `g` is.
-/

public section

open scoped LaurentSeries

namespace RatFunc

variable {K : Type*} [Field K]

/-- The constant rational function `RatFunc.C c` embeds into `K⸨X⸩` as `HahnSeries.C c`. -/
@[simp]
theorem coe_C (c : K) : algebraMap (RatFunc K) K⸨X⸩ (C c) = HahnSeries.C c := by
  rw [← RatFunc.algebraMap_C, ← RatFunc.coePolynomial_eq_algebraMap, ← RatFunc.coe_coe,
    Polynomial.coe_C, PowerSeries.coe_C]

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

namespace LaurentSeries

open scoped Polynomial RatFunc nonZeroDivisors

/-- Composition form of `LaurentSeries.expand_algebraMap_ratFunc`. -/
theorem expand_comp_algebraMap_ratFunc {K : Type*} [Field K] (N : ℕ+) :
    (expand K N).toRingHom.comp (algebraMap K⟮X⟯ K⸨X⸩) =
      (algebraMap K⟮X⟯ K⸨X⸩).comp (RatFunc.expand K N).toRingHom := by
  refine IsLocalization.ringHom_ext (K[X])⁰ (Polynomial.ringHom_ext' ?_ ?_)
  · refine RingHom.ext fun a ↦ ?_
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RatFunc.algebraMap_C, RatFunc.expand_C, RatFunc.coe_C, ← algebraMap_apply,
      AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RatFunc.algebraMap_X, RatFunc.expand_X, map_pow, RatFunc.coe_X, expand_single,
      HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

/-- Evaluating `r(X ^ N)` in `K⸨X⸩` agrees with applying `LaurentSeries.expand K N` to `r`. -/
@[simp]
theorem expand_algebraMap_ratFunc {K : Type*} [Field K] (N : ℕ+) (r : K⟮X⟯) :
    expand K N (algebraMap K⟮X⟯ K⸨X⸩ r) = algebraMap K⟮X⟯ K⸨X⸩ (RatFunc.expand K N r) :=
  RingHom.congr_fun (expand_comp_algebraMap_ratFunc N) r

/-- The power series part `g.powerSeriesPart` of a Laurent series `g` algebraic over `K(X)` is
again algebraic over `K(X)`. -/
theorem isAlgebraic_powerSeriesPart {K : Type*} [Field K] {g : K⸨X⸩} (hg : IsAlgebraic K⟮X⟯ g) :
    IsAlgebraic K⟮X⟯ (g.powerSeriesPart : K⸨X⸩) := by
  have hsingle : (HahnSeries.single (-g.order) (1 : K) : K⸨X⸩) =
      algebraMap K⟮X⟯ K⸨X⸩ (RatFunc.X ^ (-g.order)) := by
    rw [RatFunc.single_zpow, map_zpow₀, RatFunc.coe_X]
  have halg_X : IsAlgebraic K⟮X⟯ (HahnSeries.single (-g.order) (1 : K) : K⸨X⸩) := by
    rw [hsingle]
    exact isAlgebraic_algebraMap _
  rw [LaurentSeries.ofPowerSeries_powerSeriesPart g]
  exact halg_X.mul hg

end LaurentSeries
