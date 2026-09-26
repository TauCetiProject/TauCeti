/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Series.Basic
public import TauCeti.Algebra.AlgebraicGroup.Derived.PointClosure

/-!
# Rational points and the scheme-theoretic derived series

When rational points are schematically dense, the `n`th derived defining ideal is the
vanishing ideal of the `n`th abstract derived subgroup of rational points. In particular,
this holds for reduced finite-type affine groups over algebraically closed fields.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat WithConv

variable {k : Type*} [Field k] (H : CommHopfAlgCat k)

/-- For an affine group with schematically dense rational points, each scheme-theoretic
derived subgroup is the reduced closure of the corresponding abstract derived subgroup. -/
theorem derivedSeriesDefiningIdeal_eq_vanishingIdeal_derivedSeries_of_dense_points
    (h : HopfIdeal.vanishingIdeal (⊤ : Subgroup (WithConv (H →ₐ[k] k))) = ⊥) (n : ℕ) :
    derivedSeriesDefiningIdeal H n =
      HopfIdeal.vanishingIdeal (derivedSeries (WithConv (H →ₐ[k] k)) n) := by
  induction n with
  | zero => simpa only [derivedSeriesDefiningIdeal_zero, derivedSeries_zero] using h.symm
  | succ n ih =>
      rw [derivedSeriesDefiningIdeal_succ, ih,
        comapOfSurjective_derivedDefiningIdeal_quotient_vanishingIdeal_eq_vanishingIdeal_commutator,
        derivedSeries_succ]

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]

/-- Each scheme-theoretic derived subgroup of a reduced finite-type affine group over an
algebraically closed field is the reduced closure of the corresponding abstract derived subgroup
of rational points. -/
theorem derivedSeriesDefiningIdeal_eq_vanishingIdeal_derivedSeries (n : ℕ) :
    derivedSeriesDefiningIdeal H n =
      HopfIdeal.vanishingIdeal (derivedSeries (WithConv (H →ₐ[k] k)) n) :=
  H.derivedSeriesDefiningIdeal_eq_vanishingIdeal_derivedSeries_of_dense_points
    HopfIdeal.vanishingIdeal_top n

end CommHopfAlgCat
