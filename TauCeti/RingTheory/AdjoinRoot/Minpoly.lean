/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Minimal polynomials of classes in `AdjoinRoot`

For polynomials `f` and `g` over a field `K`, the class `AdjoinRoot.mk f g` is the value `g(α)` at
the root `α` of `f`. Its minimal polynomial over `K` is the polynomial whose roots are the images
under `g` of the roots of `f` when `f` is irreducible: it divides `p` exactly when
`f ∣ p.comp g`, which for squarefree `f` says that `g` maps the roots of `f` into the roots of
`p`. It is irreducible of degree at most `deg f`.

## Main results

* `AdjoinRoot.minpoly_mk_dvd_iff`: `minpoly K (mk f g) ∣ p ↔ f ∣ p.comp g`.
* `AdjoinRoot.natDegree_minpoly_mk_le`: for `f ≠ 0`, the minimal polynomial has degree at most
  `f.natDegree`.
* `AdjoinRoot.irreducible_minpoly_mk`: for `f` irreducible, the minimal polynomial is irreducible.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K]

/-- The minimal polynomial of `g(α)`, for the root `α` of `f`, divides `p` exactly when
`f ∣ p.comp g`, that is, when `p(g(α)) = 0` in `AdjoinRoot f`. For squarefree `f` this says that
`g` maps the roots of `f` into the roots of `p`. -/
theorem minpoly_mk_dvd_iff {f g p : K[X]} : minpoly K (mk f g) ∣ p ↔ f ∣ p.comp g := by
  rw [minpoly.dvd_iff, ← aeval_eq, ← aeval_comp, aeval_eq, mk_eq_zero]

/-- `g` maps the roots of `f` into the roots of the minimal polynomial of `g(α)`. -/
theorem dvd_minpoly_mk_comp (f g : K[X]) : f ∣ (minpoly K (mk f g)).comp g :=
  minpoly_mk_dvd_iff.1 dvd_rfl

/-- The minimal polynomial of an element of `AdjoinRoot f` has degree at most that of `f`. -/
theorem natDegree_minpoly_mk_le {f : K[X]} (g : K[X]) (hf : f ≠ 0) :
    (minpoly K (mk f g)).natDegree ≤ f.natDegree :=
  have := (powerBasis hf).finite
  (minpoly.natDegree_le _).trans_eq ((powerBasis hf).finrank.trans (powerBasis_dim hf))

/-- For `f` irreducible, the minimal polynomial of an element of `AdjoinRoot f` is irreducible. -/
theorem irreducible_minpoly_mk {f : K[X]} (g : K[X]) (hf : Irreducible f) :
    Irreducible (minpoly K (mk f g)) := by
  have := Fact.mk hf
  have := (powerBasis hf.ne_zero).finite
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)

end AdjoinRoot
