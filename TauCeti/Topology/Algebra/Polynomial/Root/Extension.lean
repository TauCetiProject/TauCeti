/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Connected.TotallyDisconnected
public import TauCeti.Topology.ClusterSet

/-!
# Continuous extension of bounded polynomial roots

A bounded continuous root section extends across the closure of its base if the
specialized polynomial is nonzero there and the base has preconnected approach regions.
Indeed, each cluster set is preconnected and is contained in the finite root set of the
specialization, hence is a singleton. No simplicity or constant multiplicity of the roots
is required: roots may merge at the boundary.

The coefficients lie in a commutative ring `R`, an integral domain wherever root sets must be
finite. The cluster-set lemmas need only a `T1` topology on `R` and continuity of polynomial
evaluation at the approach point; the extension theorem takes `R` to be a proper metric space,
so that a bounded root section has compact closure. Both the real and the complex case are
covered.

The extension is Mathlib's `extendFrom`. Joint continuity of polynomial evaluation is the
only continuity assumption on the polynomial family; this allows families restricted to
closed parameter sets as well as bounded-degree families with continuous coefficients.

This is the bounded-section extension argument used in semialgebraic triangulation;
see Bochnak, Coste and Roy, *Real Algebraic Geometry*, §9.2.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {X R : Type*} [TopologicalSpace X] [CommRing R] {U : Set X}
  {p : X → Polynomial R} {f : X → R} {x : X} {t : R}

section T1Space

variable [TopologicalSpace R] [T1Space R]

/-- A cluster value of a polynomial root section is a root of the specialization at the
approach point, provided evaluation is continuous there along the graph over the base. -/
theorem eval_eq_zero_of_mem_clusterSetOn
    (hp : ContinuousWithinAt (fun z : X × R ↦ (p z.1).eval z.2) (U ×ˢ univ) (x, t))
    (hf : ∀ y ∈ U, (p y).eval (f y) = 0) (ht : t ∈ clusterSetOn f U x) :
    (p x).eval t = 0 := by
  have hpair : MapClusterPt (x, t) (𝓝[U] x) (fun y ↦ (y, f y)) := by
    rw [mapClusterPt_iff_frequently]
    intro s hs
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hs
    exact (((mem_clusterSetOn_iff.mp ht).frequently hW).and_eventually (nhdsWithin_le_nhds hV)).mono
      fun y hy ↦ hVW ⟨hy.2, hy.1⟩
  -- the graph of `f` over `U` lies in `U ×ˢ univ`, so evaluation along it clusters at
  -- `(p x).eval t`; but it is identically zero
  have hgraph : map (fun y ↦ (y, f y)) (𝓝[U] x) ≤ 𝓟 (U ×ˢ univ) :=
    tendsto_principal.2 (eventually_nhdsWithin_of_forall fun y hy ↦ ⟨hy, mem_univ _⟩)
  have hval : MapClusterPt ((p x).eval t) (𝓝[U] x) fun y ↦ (p y).eval (f y) :=
    hpair.tendsto_comp' (hp.tendsto.mono_left (inf_le_inf_left _ hgraph))
  rw [Filter.EventuallyEq.mapClusterPt_iff (v := fun _ ↦ (0 : R))
    (eventually_nhdsWithin_of_forall hf), mapClusterPt_iff_frequently] at hval
  refine (specializes_iff_pure.2 (pure_le_iff.2 fun s hs ↦ ?_)).eq.symm
  obtain ⟨-, h0⟩ := (hval s hs).exists
  exact h0

/-- A preconnected cluster set of a root section is a subsingleton when the specialized
polynomial is nonzero. In particular, repeated roots at the boundary cause no obstruction. -/
theorem subsingleton_clusterSetOn_of_polynomial_root [IsDomain R]
    (hp : ∀ t, ContinuousWithinAt (fun z : X × R ↦ (p z.1).eval z.2) (U ×ˢ univ) (x, t))
    (hf : ∀ y ∈ U, (p y).eval (f y) = 0) (hx : p x ≠ 0)
    (hconn : IsPreconnected (clusterSetOn f U x)) :
    (clusterSetOn f U x).Subsingleton := by
  have hfinite : (clusterSetOn f U x).Finite :=
    (Polynomial.finite_setOfPred_isRoot hx).subset fun t ht ↦
      eval_eq_zero_of_mem_clusterSetOn (hp t) hf ht
  exact hconn.isDiscrete_iff_subsingleton.mp hfinite.isDiscrete

end T1Space

/-- A bounded continuous root section extends continuously to the closure of its base when
all specializations there are nonzero and the base has preconnected approach regions.
The base need not be open or full-dimensional. -/
theorem continuousOn_extendFrom_of_polynomial_root [IsDomain R] [MetricSpace R] [ProperSpace R]
    (hp : ContinuousOn (fun z : X × R ↦ (p z.1).eval z.2) (closure U ×ˢ univ))
    (hf : ContinuousOn f U) (hroot : ∀ y ∈ U, (p y).eval (f y) = 0)
    (hbdd : Bornology.IsBounded (f '' U)) (hne : ∀ x ∈ closure U, p x ≠ 0)
    (hconn : ∀ x ∈ closure U, IsPreconnectedApproachAt U x) :
    ContinuousOn (extendFrom U f) (closure U) := by
  refine continuousOn_extendFrom subset_rfl fun x hx ↦ ?_
  refine exists_tendsto_of_clusterSetOn_subsingleton hbdd.isCompact_closure
    (fun y hy ↦ subset_closure (mem_image_of_mem f hy)) hx ?_
  exact subsingleton_clusterSetOn_of_polynomial_root
    (fun t ↦ (hp (x, t) ⟨hx, mem_univ t⟩).mono (prod_mono subset_closure subset_rfl)) hroot
    (hne x hx) (isPreconnected_clusterSetOn hbdd.isCompact_closure
      (fun y hy ↦ subset_closure (mem_image_of_mem f hy)) hf (hconn x hx))

/-- The continuous extension of a root section still solves the same polynomial equation
on the closure, even where distinct roots coalesce. -/
theorem eval_extendFrom_eq_zero [TopologicalSpace R] [T2Space R]
    (hp : ContinuousOn (fun z : X × R ↦ (p z.1).eval z.2) (closure U ×ˢ univ))
    (hf : ContinuousOn f U) (hroot : ∀ y ∈ U, (p y).eval (f y) = 0)
    (hF : ContinuousOn (extendFrom U f) (closure U)) (hx : x ∈ closure U) :
    (p x).eval (extendFrom U f x) = 0 := by
  have hlim := (hF x hx).mono (subset_closure : U ⊆ closure U)
  have heq := extendFrom_extends hf
  have hlim' : Tendsto f (𝓝[U] x) (𝓝 (extendFrom U f x)) :=
    hlim.congr' (eventually_nhdsWithin_of_forall fun y hy ↦ heq y hy)
  exact eval_eq_zero_of_mem_clusterSetOn
    ((hp (x, _) ⟨hx, mem_univ _⟩).mono (prod_mono subset_closure subset_rfl)) hroot (by
      rw [clusterSetOn_eq_singleton_of_tendsto hx hlim']
      exact mem_singleton _)

end TauCeti
