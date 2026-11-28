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

/-!
# Transcendence and substitution of Laurent expansions of rational functions

The Laurent expansion at `0` of a nonconstant rational function `p ∈ K(X)` is transcendental over
`K` in `K⸨X⸩`: the embedding `K(X) → K⸨X⸩` is an injective `K`-algebra map, and `p` itself is
transcendental over `K` by `RatFunc.transcendental_of_ne_C`.

Moreover, substituting `X ↦ X ^ N` on rational functions (`RatFunc.expand K N`) is compatible with
Laurent-series expansion `LaurentSeries.expand K N` via the embedding `K(X) → K⸨X⸩`.

## Main results

* `RatFunc.coe_C`: the Laurent expansion of `RatFunc.C c` is `HahnSeries.C c`.
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
theorem coe_C (c : K) : algebraMap (RatFunc K) K⸨X⸩ (C c) = HahnSeries.C c := by
  rw [← RatFunc.algebraMap_C, ← RatFunc.coePolynomial_eq_algebraMap, ← RatFunc.coe_coe,
    Polynomial.coe_C, PowerSeries.coe_C]

/-- The Laurent expansion at `0` of a nonconstant rational function is transcendental over the
field of constants. -/
theorem transcendental_coe {p : RatFunc K} (hp : ¬∃ c, p = C c) :
    Transcendental K (p : K⸨X⸩) := by
  -- The embedding `K(X) → K⸨X⸩` is a `K`-algebra map, so it preserves algebraicity.
  let φ : RatFunc K →ₐ[K] K⸨X⸩ :=
    { algebraMap (RatFunc K) K⸨X⸩ with
      commutes' := fun c ↦ by
        simp [← RatFunc.algebraMap_C, ← IsScalarTower.algebraMap_apply,
          HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply'] }
  exact fun h ↦ p.transcendental_of_ne_C hp
    ((isAlgebraic_algHom_iff φ φ.toRingHom.injective).mp h)

end RatFunc

namespace LaurentSeries

open scoped Polynomial RatFunc

/-- Evaluating `r(X ^ N)` in `K⸨X⸩` agrees with applying `LaurentSeries.expand K N` to `r`. -/
@[simp]
theorem expand_algebraMap_ratFunc {K : Type*} [Field K] (N : ℕ+) (r : K⟮X⟯) :
    expand K N (algebraMap K⟮X⟯ K⸨X⸩ r) = algebraMap K⟮X⟯ K⸨X⸩ (RatFunc.expand K N r) := by
  have hpoly : ∀ p : K[X],
      expand K N (algebraMap K⟮X⟯ K⸨X⸩ (algebraMap K[X] K⟮X⟯ p)) =
        algebraMap K⟮X⟯ K⸨X⸩ (RatFunc.expand K N (algebraMap K[X] K⟮X⟯ p)) := by
    have hring :
        ((expand K N).toRingHom.comp (algebraMap K⟮X⟯ K⸨X⸩)).comp
            (algebraMap K[X] K⟮X⟯) =
          ((algebraMap K⟮X⟯ K⸨X⸩).comp (RatFunc.expand K N).toRingHom).comp
            (algebraMap K[X] K⟮X⟯) := by
      refine Polynomial.ringHom_ext' ?_ ?_
      · refine RingHom.ext fun a ↦ ?_
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          RatFunc.algebraMap_C, RatFunc.expand_C, RatFunc.coe_C, ← algebraMap_apply,
          AlgHom.commutes]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          RatFunc.algebraMap_X, RatFunc.expand_X, map_pow, RatFunc.coe_X, expand_single,
          HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
    exact RingHom.congr_fun hring
  induction r using RatFunc.induction_on with | _ p q _ =>
    simp only [map_div₀, hpoly p, hpoly q]

/-- Composition form of `LaurentSeries.expand_algebraMap_ratFunc`. -/
theorem expand_comp_algebraMap_ratFunc {K : Type*} [Field K] (N : ℕ+) :
    (expand K N).toRingHom.comp (algebraMap K⟮X⟯ K⸨X⸩) =
      (algebraMap K⟮X⟯ K⸨X⸩).comp (RatFunc.expand K N).toRingHom :=
  RingHom.ext (expand_algebraMap_ratFunc N)

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
