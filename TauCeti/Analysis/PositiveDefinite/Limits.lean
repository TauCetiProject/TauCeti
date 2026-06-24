/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.OrderClosed

/-!
# Pointwise limits of positive-definite functions

This file records the pointwise-limit closure of `TauCeti.IsPositiveDefinite`, the
positive-definite function predicate on an involutive additive monoid. If a net of
positive-definite functions converges pointwise to `F`, then `F` is positive definite.

This is the limit-closure item from Part C of the `OneParameterSemigroups` roadmap. The result is
deliberately only about positive-definiteness: as the roadmap notes, pointwise limits preserve
positive-definiteness but do not preserve continuity without an additional locally uniform
convergence hypothesis. Continuity is therefore not bundled into the statement here.

## Main declarations

* `TauCeti.IsPositiveDefinite.of_tendsto`: filter-level pointwise-limit closure.
* `TauCeti.IsPositiveDefinite.of_forall_tendsto`: the same result when every function in the
  family is positive definite.
* `TauCeti.IsPositiveDefinite.of_seq_tendsto`: the sequential `atTop` specialization.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open Filter
open ComplexConjugate
open scoped Topology
open scoped ComplexOrder

namespace TauCeti

namespace IsPositiveDefinite

variable {M : Type*} [AddMonoid M] [StarAddMonoid M]

/-- Positive-definiteness is preserved under pointwise limits along a nontrivial filter. The
hypothesis on positive-definiteness is eventual, so this applies equally to nets that are
eventually positive definite. -/
theorem of_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ᶠ i in l, IsPositiveDefinite (F i))
    (hlim : ∀ x : M, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    IsPositiveDefinite G := by
  intro n c v
  have hquad :
      Tendsto
        (fun i => ∑ j, ∑ k, c j * conj (c k) * F i (v j + star (v k))) l
        (𝓝 (∑ j, ∑ k, c j * conj (c k) * G (v j + star (v k)))) := by
    refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => ?_
    exact ((tendsto_const_nhds.mul tendsto_const_nhds).mul (hlim (v j + star (v k))))
  refine ge_of_tendsto hquad ?_
  filter_upwards [hF] with i hi
  exact hi n c v

/-- A pointwise limit of a family of positive-definite functions is positive definite. This is the
non-eventual form of `TauCeti.IsPositiveDefinite.of_tendsto`. -/
theorem of_forall_tendsto {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}
    (hF : ∀ i, IsPositiveDefinite (F i))
    (hlim : ∀ x : M, Tendsto (fun i => F i x) l (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_tendsto (Eventually.of_forall hF) hlim

/-- Sequential pointwise limits of positive-definite functions are positive definite. -/
theorem of_seq_tendsto {F : ℕ → M → ℂ} {G : M → ℂ}
    (hF : ∀ n, IsPositiveDefinite (F n))
    (hlim : ∀ x : M, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    IsPositiveDefinite G :=
  of_forall_tendsto hF hlim

end IsPositiveDefinite

end TauCeti
