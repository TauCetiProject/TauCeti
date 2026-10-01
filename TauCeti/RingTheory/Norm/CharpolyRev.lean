/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Norm.Defs

/-!
# The norm along a line and the reversed characteristic polynomial

For an `R`-algebra `S` with a finite basis `b` and an element `w : S`, the norm of `1 - t w` is
the reversed characteristic polynomial `det (1 - X M)` of the matrix `M` of multiplication by
`w`, evaluated at `t`. This turns the norm restricted to the line `t ↦ 1 - t w` into a polynomial
in `t` whose low-degree coefficients are known: its constant term is `1` and its linear
coefficient is `-tr M`.

## Main results

* `TauCeti.Algebra.eval_charpolyRev_leftMulMatrix`: along the line `t ↦ 1 - t w`, the norm is
  the reversed characteristic polynomial of multiplication by `w`.
-/

public section

open Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The norm along the line `t ↦ 1 - t w` is the reversed characteristic polynomial
`det (1 - X M)` of the matrix `M` of multiplication by `w`, evaluated at `t`. -/
theorem Algebra.eval_charpolyRev_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R S) (w : S) (t : R) :
    (Algebra.leftMulMatrix b w).charpolyRev.eval t = Algebra.norm R (1 - t • w) := by
  rw [Algebra.norm_eq_matrix_det b, map_sub, map_one, map_smul, Matrix.charpolyRev,
    ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij] <;> ring

end TauCeti
