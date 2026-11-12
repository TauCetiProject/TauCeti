/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Minimal polynomials fixed by a compatible pair of ring endomorphisms

Let `L` be a `K`-algebra, `σ` a ring endomorphism of `K` and `τ` a ring endomorphism of `L` with
`algebraMap K L ∘ σ = τ ∘ algebraMap K L`. If `τ` fixes `x : L`, then applying `σ` to the
coefficients of `minpoly K x` gives a monic polynomial of the same degree that still has `x` as a
root, so it is `minpoly K x` again: the coefficients of `minpoly K x` are fixed by `σ`.

The motivating instance is complex conjugation: for a subfield `K` of `ℂ` stable under complex
conjugation and a real number `x`, the coefficients of `minpoly K x` are fixed by the conjugation
of `K`. On a CM field this puts them in the maximal real subfield
(`NumberField.IsCMField.coeff_minpoly_mem_maximalRealSubfield`).

## Main results

* `minpoly.map_eq_self`: `(minpoly K x).map σ = minpoly K x` when `τ x = x`.
-/

public section

open Polynomial

namespace minpoly

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

/-- **The minimal polynomial is fixed by a compatible endomorphism fixing the element.** If
`τ : L →+* L` lies over `σ : K →+* K`, in the sense that
`algebraMap K L ∘ σ = τ ∘ algebraMap K L`, and `τ x = x`, then `σ` fixes every coefficient of
`minpoly K x`. No integrality hypothesis is needed: for `x` not integral over `K` both sides are
`0`. Compare `minpoly.map_eq_of_equiv_equiv`, which needs ring isomorphisms and an integral
algebra `L` over `K`; here `L` may be transcendental over `K`, as `ℂ` is over a number field. -/
theorem map_eq_self {σ : K →+* K} {τ : L →+* L}
    (hcomp : (algebraMap K L).comp σ = τ.comp (algebraMap K L)) {x : L} (hx : τ x = x) :
    (minpoly K x).map σ = minpoly K x := by
  by_cases hint : IsIntegral K x
  · refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) ((minpoly.monic hint).map σ)
      (minpoly.dvd K x ?_) (natDegree_map σ).le
    simpa [hx] using (map_aeval_eq_aeval_map hcomp (minpoly K x) x).symm
  · simp [minpoly.eq_zero hint]

end minpoly
