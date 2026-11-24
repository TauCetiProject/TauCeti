/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.NumberTheory.Padics.Complex.GaloisAction

import TauCeti.FieldTheory.Galois.AxSen
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# The Ax–Sen–Tate theorem

Let `L` be a field between `ℚ_p` and its algebraic closure `PadicAlgCl p`, and let
`G_L = Gal(PadicAlgCl p / L)` act on `ℂ_p = PadicComplex p` by the continuous extensions of its
elements (`TauCeti.NumberTheory.Padics.Complex.GaloisAction`). The **Ax–Sen–Tate theorem**
computes the fixed points: the elements of `ℂ_p` fixed by `G_L` are the closure of `L` in `ℂ_p`,
that is the completion of `L`.

The closure cannot be dropped: for the field `ℚ_p(μ_{p^∞})` the fixed points form its completion,
which is strictly larger. When `L` is finite over `ℚ_p` it is complete, hence closed in `ℂ_p`, and
the fixed points are exactly `L`; in particular the elements of `ℂ_p` fixed by `G_{ℚ_p}` are
`ℚ_p`, so that `ℂ_p` has no transcendental Galois invariants.

By infinite Galois theory the closure of a subgroup `H` of `G_{ℚ_p}` is the group `G_L`, with `L`
the fixed field of `H`, and `H` has the same fixed points as its closure, so the theorem also
computes the fixed points of every subgroup.

These are the specializations to `E = PadicAlgCl p`, whose completion is `ℂ_p`, of the general
Ax–Sen–Tate theorems `TauCeti.fixedPoints_algEquiv_completion_eq_closure`,
`TauCeti.fixedPoints_completion_eq_closure_fixedField` and
`TauCeti.fixedPoints_algEquiv_completion_eq_range` (`TauCeti.FieldTheory.Galois.AxSen`), which
deduce them from the Ax–Sen lemma: a fixed point is approximated by algebraic elements whose
conjugates are close to them, hence by elements of `L`.

## Main results

* `PadicComplex.fixedPoints_algEquiv_eq_closure`: the fixed points of `G_L` in `ℂ_p` are the
  closure of `L`.
* `PadicComplex.fixedPoints_eq_closure_fixedField`: the fixed points of a subgroup `H` of
  `G_{ℚ_p}` are the closure of the fixed field of `H`.
* `PadicComplex.fixedPoints_algEquiv_eq_range`: for `K` finite over `ℚ_p`, the fixed points of
  `G_K` in `ℂ_p` are `K`.

## References

* J. Ax, *Zeros of polynomials over local fields — the Galois action*, J. Algebra 15 (1970),
  417–428.
* J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966),
  Springer, 1967, §3.
* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §4.1.2, Proposition
  4.9.
* O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), §2.1,
  Proposition 2.1.2.
-/

public section

open UniformSpace.Completion

namespace PadicComplex

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The Ax–Sen–Tate theorem.** For every field `L` between `ℚ_p` and `PadicAlgCl p`, the
elements of `ℂ_p` fixed by `Gal(PadicAlgCl p / L)` are the closure of `L` in `ℂ_p`. -/
theorem fixedPoints_algEquiv_eq_closure (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    MulAction.fixedPoints (PadicAlgCl p ≃ₐ[L] PadicAlgCl p) ℂ_[p] =
      closure (Set.range fun a : L ↦ ((a : PadicAlgCl p) : ℂ_[p])) :=
  TauCeti.fixedPoints_algEquiv_completion_eq_closure hp.out (PadicAlgCl.norm_p_lt_one p)

/-- **The Ax–Sen–Tate theorem for subgroups.** For a subgroup `H` of `Gal(PadicAlgCl p / ℚ_p)`,
the elements of `ℂ_p` fixed by `H` are the closure in `ℂ_p` of the fixed field of `H`. -/
theorem fixedPoints_eq_closure_fixedField (H : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :
    MulAction.fixedPoints H ℂ_[p] =
      closure (Set.range fun a : IntermediateField.fixedField H ↦
        ((a : PadicAlgCl p) : ℂ_[p])) :=
  TauCeti.fixedPoints_completion_eq_closure_fixedField hp.out (PadicAlgCl.norm_p_lt_one p) H

/-- **The Ax–Sen–Tate theorem for finite extensions.** For a finite extension `K` of `ℚ_p` inside
`PadicAlgCl p`, the elements of `ℂ_p` fixed by `Gal(PadicAlgCl p / K)` are the elements of `K`. -/
theorem fixedPoints_algEquiv_eq_range (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    MulAction.fixedPoints (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) ℂ_[p] =
      Set.range fun a : K ↦ ((a : PadicAlgCl p) : ℂ_[p]) :=
  TauCeti.fixedPoints_algEquiv_completion_eq_range ℚ_[p] hp.out (PadicAlgCl.norm_p_lt_one p)

end PadicComplex
