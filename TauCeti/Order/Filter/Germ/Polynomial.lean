/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Evaluating polynomials at germs of functions

A polynomial with coefficients in `S` evaluated at the germ of a function `f : α → T`, where the
coefficients act on germs through a ring homomorphism `S →+* (α → T)` followed by the coercion to
germs, is the germ of the pointwise evaluations (`Filter.Germ.eval₂_coeRingHom_comp_coe`).
-/

public section

open Polynomial

namespace Filter.Germ

/-- Evaluating a polynomial with coefficients in `S` at the germ of `f : α → T`, where the
coefficients act on germs through `u : S →+* (α → T)` followed by the coercion to germs, gives the
germ of the pointwise evaluations: at `y`, the coefficients are evaluated by `u · y`. -/
theorem eval₂_coeRingHom_comp_coe {α S T : Type*} [Semiring S] [Semiring T]
    (l : Filter α) (u : S →+* (α → T)) (P : S[X]) (f : α → T) :
    P.eval₂ ((coeRingHom l).comp u) (f : Germ l T) =
      ((fun y ↦ (P.map ((Pi.evalRingHom (fun _ : α ↦ T) y).comp u)).eval (f y) : α → T) :
        Germ l T) := by
  have heval : P.eval₂ u f =
      (fun y ↦ (P.map ((Pi.evalRingHom (fun _ : α ↦ T) y).comp u)).eval (f y)) := by
    funext y
    rw [eval_map]
    exact hom_eval₂ P u (Pi.evalRingHom (fun _ : α ↦ T) y) f
  rw [← heval, ← coe_coeRingHom, hom_eval₂]

end Filter.Germ
