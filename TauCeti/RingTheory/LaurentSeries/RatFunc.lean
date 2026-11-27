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

Moreover, substituting `X ↦ X ^ N` on rational functions (`TauCeti.expandRatFunc K N`) is
compatible with Laurent-series expansion `LaurentSeries.expand K N` via the embedding `K(X) → K⸨X⸩`.

## Main results

* `RatFunc.transcendental_coe`: the Laurent expansion of a nonconstant rational function is
  transcendental over the constants.
* `LaurentSeries.expand_comp_algebraMap_ratFunc`: evaluating `r(X ^ N)` in `K⸨X⸩` agrees with
  applying `LaurentSeries.expand K N` to `r`.
-/

public section

open scoped LaurentSeries

namespace RatFunc

variable {K : Type*} [Field K]

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
theorem expand_comp_algebraMap_ratFunc {K : Type*} [Field K] (N : ℕ+) :
    (expand K N).toRingHom.comp (algebraMap K⟮X⟯ K⸨X⸩) =
      (algebraMap K⟮X⟯ K⸨X⸩).comp (TauCeti.expandRatFunc K N) := by
  have hpoly : ∀ p : K[X],
      expand K N (algebraMap K⟮X⟯ K⸨X⸩ (algebraMap K[X] K⟮X⟯ p)) =
        algebraMap K⟮X⟯ K⸨X⸩ (TauCeti.expandRatFunc K N (algebraMap K[X] K⟮X⟯ p)) := by
    have hring :
        ((expand K N).toRingHom.comp (algebraMap K⟮X⟯ K⸨X⸩)).comp
            (algebraMap K[X] K⟮X⟯) =
          ((algebraMap K⟮X⟯ K⸨X⸩).comp (TauCeti.expandRatFunc K N)).comp
            (algebraMap K[X] K⟮X⟯) := by
      refine Polynomial.ringHom_ext' ?_ ?_
      · refine RingHom.ext fun a ↦ ?_
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [TauCeti.expandRatFunc_algebraMap, Polynomial.C_comp,
          ← RatFunc.coePolynomial_eq_algebraMap, ← RatFunc.coe_coe, Polynomial.coe_C,
          PowerSeries.coe_C, ← algebraMap_apply, AlgHom.commutes]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [TauCeti.expandRatFunc_algebraMap, Polynomial.X_comp, map_pow, map_pow,
          ← RatFunc.coePolynomial_eq_algebraMap, ← RatFunc.coe_coe, Polynomial.coe_X,
          PowerSeries.coe_X, expand_single, HahnSeries.single_pow, one_pow, nsmul_eq_mul,
          mul_one]
    exact RingHom.congr_fun hring
  refine RingHom.ext fun r ↦ ?_
  induction r using RatFunc.induction_on with | _ p q _ =>
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_div₀]
    rw [hpoly p, hpoly q]

end LaurentSeries
