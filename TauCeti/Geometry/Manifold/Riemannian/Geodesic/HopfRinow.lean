/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing
public import TauCeti.Topology.MetricSpace.ProperSpace
import TauCeti.Geometry.Manifold.Riemannian.Basic

/-!
# The Hopf–Rinow theorem

Let `M` be a Riemannian manifold whose distance is the Riemannian distance, and let `p ∈ M`.
The **Hopf–Rinow theorem** says that the following assertions are equivalent:

* **(a)** the exponential map `exp_p` is defined on all of `T_p M`;
* **(b)** `M` is a proper metric space: its closed bounded subsets are compact;
* **(c)** `M` is complete as a metric space;
* **(d)** `M` is geodesically complete: every maximal geodesic is defined for all time;
* **(e)** there is an increasing sequence of compact sets `K n` covering `M` such that
  `dist p (q n) → ∞` along every sequence `q` with `q n ∉ K n`.

Each of them moreover implies that every point is joined to `p` by a minimizing geodesic
segment, which is `exists_isGeodesicCurveOn_Icc_pathELength_eq_edist`.

The individual implications are proved elsewhere: (a) ⇒ (b) is `properSpace_of_expDomain_eq_univ`,
(b) ⇒ (c) is Mathlib's `complete_of_proper`, (c) ⇒ (d) is
`isGeodesicallyCompleteAt_of_completeSpace`, (d) ⇒ (a) is `expDomain_eq_univ_iff`, and (b) ⇔ (e)
holds in every pseudometric space
(`TauCeti.properSpace_iff_exists_isCompact_monotone_iUnion_eq_univ_tendsto_dist`).  This file
assembles them into a single `List.TFAE` statement and draws the consequence that completeness of
the exponential map, or of the geodesics, at one point propagates to every point.

The statements are about an ordinary metric space `M` compatible with the Riemannian structure,
`[IsRiemannianManifold I M]`.  The finiteness of the Riemannian distance, which is what do Carmo's
standing connectedness assumption supplies, is part of that structure, so no separate
`[ConnectedSpace M]` hypothesis appears.

## Main results

In the namespace `TauCeti.Manifold`:

* `tfae_expDomain_eq_univ`: **the Hopf–Rinow theorem**, the equivalence of (a)–(e).
* `completeSpace_iff_isGeodesicallyCompleteAt`: `M` is complete exactly when every geodesic
  leaving one given point is defined for all time.
* `isGeodesicallyCompleteAt_iff_forall` and `expDomain_eq_univ_iff_forall`: geodesic completeness
  at one point, equivalently an everywhere-defined exponential map at one point, propagates to
  every point.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7, §2, Thm. 2.8.
* J. M. Lee, *Introduction to Riemannian Manifolds*, Springer, 2018, Ch. 6, Thm. 6.19.
-/

public section

open Bundle Filter Manifold Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

variable [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [T2Space (TangentBundle I M)] [IsRiemannianManifold I M]

/-- **The Hopf–Rinow theorem.**  For a point `p` of a Riemannian manifold `M` whose distance is
the Riemannian distance, the following are equivalent:
the exponential map at `p` is defined on all of `T_p M`; `M` is proper; `M` is complete;
every maximal geodesic of `M` is defined for all time; and `M` has an increasing exhaustion by
compact sets `K n` such that `dist p (q n) → ∞` whenever `q n ∉ K n` for every `n`. -/
theorem tfae_expDomain_eq_univ (p : M) :
    List.TFAE [expDomain I M p = univ, ProperSpace M, CompleteSpace M,
      ∀ q : M, IsGeodesicallyCompleteAt I M q,
      ∃ K : ℕ → Set M, (∀ n, IsCompact (K n)) ∧ Monotone K ∧ (⋃ n, K n) = univ ∧
        ∀ q : ℕ → M, (∀ n, q n ∉ K n) → Tendsto (fun n ↦ dist p (q n)) atTop atTop] := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  tfae_have 1 → 2 := properSpace_of_expDomain_eq_univ
  tfae_have 2 → 3 := fun _ ↦ complete_of_proper
  tfae_have 3 → 4 := fun _ q ↦ isGeodesicallyCompleteAt_of_completeSpace q
  tfae_have 4 → 1 := fun h ↦ expDomain_eq_univ_iff.2 (h p)
  tfae_have 2 ↔ 5 := TauCeti.properSpace_iff_exists_isCompact_monotone_iUnion_eq_univ_tendsto_dist p
  tfae_finish

/-- **Geodesic completeness at one point is metric completeness.**  A Riemannian manifold `M` is
complete exactly when every maximal geodesic leaving a given point `p` is defined for all time. -/
theorem completeSpace_iff_isGeodesicallyCompleteAt (p : M) :
    CompleteSpace M ↔ IsGeodesicallyCompleteAt I M p := by
  rw [← expDomain_eq_univ_iff]
  exact ((tfae_expDomain_eq_univ (I := I) p).out 1 3).symm

/-- **Geodesic completeness propagates from one point to every point.**  If every maximal geodesic
leaving `p` is defined for all time, then so is every maximal geodesic of `M`. -/
theorem isGeodesicallyCompleteAt_iff_forall (p : M) :
    IsGeodesicallyCompleteAt I M p ↔ ∀ q : M, IsGeodesicallyCompleteAt I M q := by
  rw [← expDomain_eq_univ_iff]
  exact (tfae_expDomain_eq_univ (I := I) p).out 1 4

/-- **An everywhere-defined exponential map at one point makes every exponential map everywhere
defined.**  If `exp_p` is defined on all of `T_p M`, then `exp_q` is defined on all of `T_q M`
for every point `q`. -/
theorem expDomain_eq_univ_iff_forall (p : M) :
    expDomain I M p = univ ↔ ∀ q : M, expDomain I M q = univ := by
  simp_rw [expDomain_eq_univ_iff]
  exact isGeodesicallyCompleteAt_iff_forall p

end TauCeti.Manifold

end
