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
import TauCeti.Analysis.Complex.PlaneSeparation.Basic
import TauCeti.Topology.ConnectedComponents
import Mathlib.Analysis.Complex.BranchLogRoot

/-!
# Plane domains are simply connected exactly when they have no holes

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

Conversely, a simply connected open set has no holes. On a simply connected open set `U` every
zero-free continuous function has a continuous logarithm, by Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp`. For `a` in a bounded component of `Uᶜ`, that component
is cut out by an open set whose frontier is a compact subset of `U` enclosing `a`, so `z ↦ z - a`
would have a continuous logarithm on a compact set enclosing `a`, contradicting
`TauCeti.hasContinuousLogOn_sub_iff_notMem_filledHull`. So a connected open set is simply connected
exactly when it has no holes.

## Main results

* `TauCeti.hasHolomorphicSquareRoots_of_filledHull_subset` — an open set without holes has
  holomorphic square roots.
* `TauCeti.isSimplyConnected_of_filledHull_subset` — a connected open set without holes is simply
  connected.
* `IsSimplyConnected.filledHull_subset` — a simply connected open subset of the plane has no holes.
* `TauCeti.isSimplyConnected_iff_filledHull_subset` — a connected open set is simply connected
  exactly when it has no holes.
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

/-- **A simply connected open subset of the plane has no holes**: it contains its filled hull, that
is, every connected component of its complement is unbounded. Consequently `filledHull K ⊆ U`
for every `K ⊆ U`, by `TauCeti.filledHull_mono`. -/
theorem _root_.IsSimplyConnected.filledHull_subset (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) : filledHull U ⊆ U := by
  intro a ha
  by_contra haU
  -- `z ↦ z - a` has a continuous logarithm on the simply connected set `U`
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc hUo
    (g := fun z => z - a) (by fun_prop) (by rintro ⟨z, hz, h0⟩; exact haU (sub_eq_zero.mp h0 ▸ hz))
  -- the bounded component of `Uᶜ` through `a` is cut out by an open set `V` with frontier in `U`
  obtain ⟨V, -, haV, hVc, hVU⟩ :=
    hUo.isClosed_compl.exists_isOpen_isCompact_closure_disjoint_frontier
      (Metric.isCompact_of_isClosed_isBounded hUo.isClosed_compl.connectedComponentIn
        (mem_filledHull_iff.mp ha))
  have hKU : frontier V ⊆ U := fun z hz => by
    by_contra hzU
    exact disjoint_left.mp hVU hz hzU
  -- so `frontier V` encloses `a` while carrying a logarithm of `z ↦ z - a`
  refine (hasContinuousLogOn_sub_iff_notMem_filledHull isClosed_frontier
    (hVc.isBounded.subset frontier_subset_closure)).mp
      (hasContinuousLogOn_iff.mpr ⟨L, hLc.mono hKU, fun z hz => hL (hKU hz)⟩) ?_
  exact subset_filledHull_of_frontier_subset (hVc.isBounded.subset subset_closure) subset_rfl
    (haV (mem_connectedComponentIn haU))

/-- **A plane domain is simply connected exactly when it has no holes**: a connected open set
`U ⊆ ℂ` is simply connected if and only if every connected component of `ℂ \ U` is unbounded. -/
theorem isSimplyConnected_iff_filledHull_subset (hUo : IsOpen U) (hUc : IsConnected U) :
    IsSimplyConnected U ↔ filledHull U ⊆ U :=
  ⟨fun h => h.filledHull_subset hUo, isSimplyConnected_of_filledHull_subset hUo hUc⟩

/-- **A plane domain with connected frontier is simply connected**, provided its complement is
unbounded. Such a domain has no holes (`TauCeti.filledHull_eq_self_of_isPreconnected_frontier`).
This covers every bounded domain whose frontier is a Jordan curve, and also unbounded domains such
as a half-plane. -/
theorem isSimplyConnected_of_isPreconnected_frontier (hUo : IsOpen U) (hUc : IsConnected U)
    (hf : IsPreconnected (frontier U)) (hu : ¬ IsBounded Uᶜ) : IsSimplyConnected U :=
  isSimplyConnected_of_filledHull_subset hUo hUc
    (filledHull_eq_self_of_isPreconnected_frontier hUo hf hu).le

end TauCeti
