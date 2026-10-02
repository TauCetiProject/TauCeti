/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Analysis.Complex.Conformal.SquareRoots
public import TauCeti.Topology.FilledHull
import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Existence
import TauCeti.Analysis.Contour.Primitive

/-!
# Plane domains without holes are simply connected

An open set `U ⊆ ℂ` *has no holes* when every connected component of `ℂ \ U` is unbounded, that
is, when `TauCeti.filledHull U ⊆ U`. This file proves that a connected open set without holes is
simply connected, and that an open set whose frontier is connected, and whose complement is
unbounded, has no holes. In particular a bounded domain whose frontier is a Jordan curve is simply
connected, a Jordan curve being connected; this is `TauCeti.IsJordanDomain.isSimplyConnected`, in
`Conformal/Jordan/Domain.lean`.

The proof is analytic. On a set without holes every closed curve is null-homologous, so by the
homology form of Cauchy's theorem every nowhere-zero holomorphic function has a holomorphic square
root (`TauCeti.Contour.exists_differentiableOn_pow_eq_of_filledHull_subset`). A connected open set
with holomorphic square roots is either `ℂ` or, by the Koebe argument of the Riemann mapping
theorem, homeomorphic to the unit disc (`TauCeti.HasHolomorphicSquareRoots.isSimplyConnected`).
Together these are the implications (d) ⇒ (i) ⇒ (a) ⇒ (b) of Rudin's characterisation of simply
connected plane domains, where (d) is connectedness of the complement in the Riemann sphere and (i)
the existence of holomorphic square roots. The topological input,
that the complement of an open set with preconnected frontier is preconnected, is
`TauCeti.isPreconnected_compl_of_isPreconnected_frontier`.

## Main results

* `TauCeti.hasHolomorphicSquareRoots_of_filledHull_subset` — an open set without holes has
  holomorphic square roots.
* `TauCeti.isSimplyConnected_of_filledHull_subset` — a connected open set without holes is simply
  connected.
* `TauCeti.isSimplyConnected_of_isPreconnected_frontier` — a connected open set with preconnected
  frontier and unbounded complement is simply connected.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.11.
* L. Ahlfors, *Complex Analysis*, Ch. 4, §4.2.
-/

public section

namespace TauCeti

open Bornology Set

variable {U : Set ℂ}

/-- **An open set without holes has holomorphic square roots.** If every connected component of
the complement of the open set `U` is unbounded, every nowhere-zero holomorphic function on `U` is
the square of a holomorphic function: this is the case `n = 2` of
`TauCeti.Contour.exists_differentiableOn_pow_eq_of_filledHull_subset`. -/
theorem hasHolomorphicSquareRoots_of_filledHull_subset (hUo : IsOpen U)
    (hUf : filledHull U ⊆ U) : HasHolomorphicSquareRoots U :=
  ⟨fun _ hg hg₀ =>
    Contour.exists_differentiableOn_pow_eq_of_filledHull_subset hUo hUf hg hg₀ two_ne_zero⟩

/-- **A plane domain without holes is simply connected.** If `U ⊆ ℂ` is open and connected and
every connected component of `ℂ \ U` is unbounded, then `U` is simply connected. -/
theorem isSimplyConnected_of_filledHull_subset (hUo : IsOpen U) (hUc : IsConnected U)
    (hUf : filledHull U ⊆ U) : IsSimplyConnected U :=
  (hasHolomorphicSquareRoots_of_filledHull_subset hUo hUf).isSimplyConnected hUo hUc

/-- **A plane domain with connected frontier is simply connected**, provided its complement is
unbounded. Such a domain has no holes (`TauCeti.filledHull_eq_self_of_isPreconnected_frontier`).
This covers every bounded domain whose frontier is a Jordan curve, and also unbounded domains such
as a half-plane. -/
theorem isSimplyConnected_of_isPreconnected_frontier (hUo : IsOpen U) (hUc : IsConnected U)
    (hf : IsPreconnected (frontier U)) (hu : ¬ IsBounded Uᶜ) : IsSimplyConnected U :=
  isSimplyConnected_of_filledHull_subset hUo hUc
    (filledHull_eq_self_of_isPreconnected_frontier hUo hf hu).le

end TauCeti
