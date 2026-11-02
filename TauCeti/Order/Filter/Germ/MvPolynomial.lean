/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Polynomial relations on germs of functions of several variables

Polynomials in the coordinates act on germs of functions `f : (σ → R) → R` along a filter `l` as
polynomial functions: `p : MvPolynomial σ R` acts as the germ of `y ↦ MvPolynomial.eval y p`. This
algebra structure (`Filter.Germ.mvPolynomialAlgebra`) is not an instance; activate it locally with
`attribute [local instance] Filter.Germ.mvPolynomialAlgebra`.

With this structure, a polynomial `P : (MvPolynomial σ R)[X]` evaluated at the germ of `f` is the
germ of `y ↦ P (y, f y)` (`Filter.Germ.aeval_coe`). Consequently the germ of `f` is algebraic over
the coordinate polynomials exactly when `f` satisfies a nonzero polynomial relation `P (y, f y) = 0`
eventually along `l` (`Filter.Germ.isAlgebraic_coe_iff`). This turns closure properties of functions
satisfying polynomial relations, such as Nash germs, into Mathlib's closure properties of algebraic
elements.

## Main declarations

* `Filter.Germ.mvPolynomialAlgebra`: coordinate polynomials acting on germs as polynomial functions.
* `Filter.Germ.aeval_coe`: evaluating a polynomial relation at the germ of a function.
* `Filter.Germ.isAlgebraic_coe_iff`: algebraic germs are germs of functions satisfying a nonzero
  polynomial relation.
-/

public section

open Polynomial

namespace Filter.Germ

variable {σ R : Type*}

/-- Polynomials in the coordinates act on germs along `l` of functions `(σ → R) → R` as
polynomial functions: `p` acts as the germ of `y ↦ MvPolynomial.eval y p`. -/
@[instance_reducible]
noncomputable def mvPolynomialAlgebra [CommSemiring R] (l : Filter (σ → R)) :
    Algebra (MvPolynomial σ R) (Germ l R) :=
  ((coeRingHom l).comp (RingHom.pi fun y ↦ MvPolynomial.eval y)).toAlgebra

attribute [local instance] mvPolynomialAlgebra

/-- A coordinate polynomial acts on germs as the germ of its polynomial function. -/
theorem mvPolynomialAlgebra_algebraMap_apply [CommSemiring R] (l : Filter (σ → R))
    (p : MvPolynomial σ R) :
    algebraMap (MvPolynomial σ R) (Germ l R) p =
      ((fun y ↦ MvPolynomial.eval y p : (σ → R) → R) : Germ l R) := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, coe_coeRingHom]
  congr 1 with y

/-- Evaluating `P : (MvPolynomial σ R)[X]` at the germ of `f` gives the germ of
`y ↦ P (y, f y)`, where `P (y, t)` is `(P.map (MvPolynomial.eval y)).eval t`. -/
theorem aeval_coe [CommSemiring R] {l : Filter (σ → R)} (P : (MvPolynomial σ R)[X])
    (f : (σ → R) → R) :
    aeval (f : Germ l R) P =
      ((fun y ↦ (P.map (MvPolynomial.eval y)).eval (f y) : (σ → R) → R) : Germ l R) := by
  have key : (fun y ↦ (P.map (MvPolynomial.eval y)).eval (f y)) =
      P.eval₂ (RingHom.pi fun y ↦ MvPolynomial.eval y) f := by
    ext y
    rw [eval_map]
    -- `Pi.evalRingHom _ y` composed with `RingHom.pi` is `MvPolynomial.eval y` by definition.
    exact (hom_eval₂ P (RingHom.pi fun y ↦ MvPolynomial.eval y)
      (Pi.evalRingHom (fun _ : σ → R ↦ R) y) f).symm
  rw [key, aeval_def, RingHom.algebraMap_toAlgebra]
  -- `Germ.coeRingHom` is the coercion to germs by definition (`Germ.coe_coeRingHom`).
  exact (hom_eval₂ (p := P) (g := coeRingHom (R := R) l) ..).symm

/-- The germ of `f` is algebraic over the coordinate polynomials exactly when `f` satisfies a
nonzero polynomial relation `P (y, f y) = 0` eventually along `l`. -/
theorem isAlgebraic_coe_iff [CommRing R] {l : Filter (σ → R)} {f : (σ → R) → R} :
    IsAlgebraic (MvPolynomial σ R) (f : Germ l R) ↔ ∃ P : (MvPolynomial σ R)[X], P ≠ 0 ∧
      ∀ᶠ y in l, (P.map (MvPolynomial.eval y)).eval (f y) = 0 := by
  simp only [IsAlgebraic, aeval_coe, ← coe_zero, coe_eq, EventuallyEq, Pi.zero_apply]

end Filter.Germ
