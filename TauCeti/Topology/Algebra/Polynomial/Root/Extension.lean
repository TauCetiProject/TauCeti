/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import TauCeti.Topology.ClusterSet
import Mathlib.Analysis.Normed.Ring.Lemmas
import TauCeti.Analysis.Polynomial.CauchyBound

/-!
# Continuous extension of polynomial root sections

A bounded continuous root section extends across the closure of its base if the specialized
polynomial is nonzero there and the base has preconnected approach regions. Indeed, each cluster
set is preconnected and is contained in the finite root set of the specialization, hence is a
singleton. No simplicity or constant multiplicity of the roots is required: roots may merge at the
boundary.

Over any proper normed field `K` (such as `ℝ` or `ℂ`), the same argument applies locally at an
individual frontier point `x ∈ closure U`, or along any subset `B ⊆ closure U`, using only
coefficient convergence and a degree bound along `𝓝[U] x` together with local boundedness of the
root section near `x`. When the nearby degrees along `U` do not exceed `(p x).natDegree` (in
particular for monic or constant-degree families), `TauCeti.eventually_norm_le_of_isRoot` supplies
local boundedness automatically from Cauchy's root bound without any bounded-image assumption on
the section.

The extension is Mathlib's `extendFrom`. In the global bounded case, joint continuity of
polynomial evaluation is the only continuity assumption on the polynomial family; this allows
families restricted to closed parameter sets as well as bounded-degree families with continuous
coefficients.

This supplies both the bounded-section extension argument used in semialgebraic triangulation
(Bochnak, Coste and Roy, *Real Algebraic Geometry*, §9.2) and the frontier root-matching step
for polynomial stacks over open decompositions where ambient polynomial data are only defined on
an open neighborhood of the strata.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- A cluster value of an eventual polynomial root section at `x` along `U` is a root of `p x`
whenever the coefficients up to a local degree bound `d` converge along `𝓝[U] x` to those of
`p x`. Unlike `TauCeti.eval_eq_zero_of_mem_clusterSetOn`, no global continuity on `closure U`
is required. -/
theorem eval_eq_zero_of_mem_clusterSetOn_of_tendsto_coeff
    {X R : Type*} [TopologicalSpace X] [Semiring R] [TopologicalSpace R]
    [IsTopologicalSemiring R] [T2Space R] {U : Set X}
    {p : X → Polynomial R} {f : X → R} {x : X} {t : R} {d : ℕ}
    (hcoeff : ∀ i ≤ d, Tendsto (fun y ↦ (p y).coeff i) (𝓝[U] x) (𝓝 ((p x).coeff i)))
    (hdeg : ∀ᶠ y in 𝓝[U] x, (p y).natDegree ≤ d) (hdeg₀ : (p x).natDegree ≤ d)
    (hf : ∀ᶠ y in 𝓝[U] x, (p y).eval (f y) = 0) (ht : t ∈ clusterSetOn f U x) :
    (p x).eval t = 0 := by
  let l : Filter X := comap f (𝓝 t) ⊓ 𝓝[U] x
  have hl : l.NeBot :=
    (Filter.map_neBot_iff f).mp (by
      rw [Filter.push_pull']
      exact (mem_clusterSetOn_iff.mp ht).clusterPt)
  have hsum : Tendsto (fun y ↦ ∑ i ∈ Finset.range (d + 1), (p y).coeff i * f y ^ i)
      l (𝓝 (∑ i ∈ Finset.range (d + 1), (p x).coeff i * t ^ i)) :=
    tendsto_finsetSum _ fun i hi ↦
      ((hcoeff i (Finset.mem_range_succ_iff.1 hi)).mono_left inf_le_right).mul
        ((tendsto_comap.mono_left inf_le_left).pow i)
  have heq : (fun y ↦ ∑ i ∈ Finset.range (d + 1), (p y).coeff i * f y ^ i) =ᶠ[l] 0 := by
    filter_upwards [hdeg.filter_mono inf_le_right, hf.filter_mono inf_le_right] with y hyd hy0
    rw [← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hyd), hy0, Pi.zero_apply]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg₀)]
  exact tendsto_nhds_unique hsum (tendsto_const_nhds.congr' heq.symm)

section NormedField

variable {X K : Type*} [TopologicalSpace X] [NormedField K] [ProperSpace K]
  {U : Set X} {p : X → Polynomial K} {f : X → K} {x : X}

/-- Over a proper normed field `K`, a continuous root section on `U` that is eventually bounded
along `𝓝[U] x` converges along `𝓝[U] x` to a root of `p x`, provided `x ∈ closure U`, `U` has
preconnected approach regions at `x`, `p x ≠ 0`, and the coefficients of `p` up to a local degree
bound converge along `𝓝[U] x` to those of `p x`. -/
theorem exists_tendsto_nhdsWithin_of_isRoot_of_eventually_norm_le {d : ℕ}
    (hx : x ∈ closure U) (hconn : IsPreconnectedApproachAt U x)
    (hf : ContinuousOn f U) (hroot : ∀ᶠ y in 𝓝[U] x, (p y).eval (f y) = 0)
    (hcoeff : ∀ i ≤ d, Tendsto (fun y ↦ (p y).coeff i) (𝓝[U] x) (𝓝 ((p x).coeff i)))
    (hdeg : ∀ᶠ y in 𝓝[U] x, (p y).natDegree ≤ d) (hdeg₀ : (p x).natDegree ≤ d)
    (hne : p x ≠ 0) (hbdd : ∃ M : ℝ, ∀ᶠ y in 𝓝[U] x, ‖f y‖ ≤ M) :
    ∃ t, (p x).eval t = 0 ∧ Tendsto f (𝓝[U] x) (𝓝 t) := by
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨V, hV, hVM⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hM
  let U' := U ∩ V
  have hnhds : 𝓝[U'] x = 𝓝[U] x := by
    dsimp only [U']
    rw [inter_comm]
    exact nhdsWithin_inter_of_mem (nhdsWithin_le_nhds hV)
  have hx' : x ∈ closure U' :=
    mem_closure_iff_nhdsWithin_neBot.mpr (hnhds ▸ mem_closure_iff_nhdsWithin_neBot.mp hx)
  have hfK : MapsTo f U' (Metric.closedBall (0 : K) M) :=
    fun y hy ↦ mem_closedBall_zero_iff.mpr (hVM ⟨hy.2, hy.1⟩)
  have hconn' : IsPreconnectedApproachAt U' x :=
    (isPreconnectedApproachAt_inter_of_mem_nhds hV).mpr hconn
  have hpre : IsPreconnected (clusterSetOn f U' x) :=
    isPreconnected_clusterSetOn (isCompact_closedBall (0 : K) M) hfK (hf.mono inter_subset_left)
      hconn'
  have hfin : (clusterSetOn f U' x).Finite :=
    (Polynomial.finite_setOfPred_isRoot hne).subset fun z hz ↦
      eval_eq_zero_of_mem_clusterSetOn_of_tendsto_coeff hcoeff hdeg hdeg₀ hroot
        (by rwa [clusterSetOn_inter_of_mem_nhds hV] at hz)
  obtain ⟨t, ht⟩ := exists_tendsto_of_clusterSetOn_subsingleton (isCompact_closedBall (0 : K) M)
    hfK hx' (hpre.isDiscrete_iff_subsingleton.mp hfin.isDiscrete)
  have htU : Tendsto f (𝓝[U] x) (𝓝 t) := hnhds ▸ ht
  have ht_mem : t ∈ clusterSetOn f U x := by
    rw [clusterSetOn_eq_singleton_of_tendsto hx htU]
    exact mem_singleton t
  exact ⟨t, eval_eq_zero_of_mem_clusterSetOn_of_tendsto_coeff hcoeff hdeg hdeg₀ hroot ht_mem, htU⟩

/-- Over a proper normed field `K`, a continuous root section on `U` converges along `𝓝[U] x` to a
root of `p x` whenever `x ∈ closure U`, `U` has preconnected approach regions at `x`, `p x ≠ 0`,
the coefficients of `p` up to `(p x).natDegree` converge along `𝓝[U] x` to those of `p x`, and the
nearby degrees along `U` do not exceed `(p x).natDegree`. No boundedness assumption on the root
section is needed. -/
theorem exists_tendsto_nhdsWithin_of_isRoot
    (hx : x ∈ closure U) (hconn : IsPreconnectedApproachAt U x)
    (hf : ContinuousOn f U) (hroot : ∀ᶠ y in 𝓝[U] x, (p y).eval (f y) = 0)
    (hcoeff : ∀ i ≤ (p x).natDegree, Tendsto (fun y ↦ (p y).coeff i) (𝓝[U] x) (𝓝 ((p x).coeff i)))
    (hdeg : ∀ᶠ y in 𝓝[U] x, (p y).natDegree ≤ (p x).natDegree) (hne : p x ≠ 0) :
    ∃ t, (p x).eval t = 0 ∧ Tendsto f (𝓝[U] x) (𝓝 t) :=
  exists_tendsto_nhdsWithin_of_isRoot_of_eventually_norm_le hx hconn hf hroot hcoeff hdeg le_rfl
    hne (eventually_norm_le_of_isRoot hne hcoeff hdeg hroot)

/-- Over a proper normed field `K`, under local coefficient convergence without degree increase at
`x ∈ closure U` where `p x ≠ 0` and `U` has preconnected approach regions, a continuous root
section `f` on `U` tends along `𝓝[U] x` to `extendFrom U f x`. -/
theorem tendsto_extendFrom_of_isRoot
    (hx : x ∈ closure U) (hconn : IsPreconnectedApproachAt U x)
    (hf : ContinuousOn f U) (hroot : ∀ᶠ y in 𝓝[U] x, (p y).eval (f y) = 0)
    (hcoeff : ∀ i ≤ (p x).natDegree, Tendsto (fun y ↦ (p y).coeff i) (𝓝[U] x) (𝓝 ((p x).coeff i)))
    (hdeg : ∀ᶠ y in 𝓝[U] x, (p y).natDegree ≤ (p x).natDegree) (hne : p x ≠ 0) :
    Tendsto f (𝓝[U] x) (𝓝 (extendFrom U f x)) := by
  obtain ⟨t, _, ht⟩ := exists_tendsto_nhdsWithin_of_isRoot hx hconn hf hroot hcoeff hdeg hne
  exact tendsto_extendFrom ⟨t, ht⟩

/-- Over a proper normed field `K`, under local coefficient convergence without degree increase at
`x ∈ closure U` where `p x ≠ 0` and `U` has preconnected approach regions, `extendFrom U f x` is a
root of `p x`. -/
theorem eval_extendFrom_eq_zero_of_isRoot
    (hx : x ∈ closure U) (hconn : IsPreconnectedApproachAt U x)
    (hf : ContinuousOn f U) (hroot : ∀ᶠ y in 𝓝[U] x, (p y).eval (f y) = 0)
    (hcoeff : ∀ i ≤ (p x).natDegree, Tendsto (fun y ↦ (p y).coeff i) (𝓝[U] x) (𝓝 ((p x).coeff i)))
    (hdeg : ∀ᶠ y in 𝓝[U] x, (p y).natDegree ≤ (p x).natDegree) (hne : p x ≠ 0) :
    (p x).eval (extendFrom U f x) = 0 := by
  obtain ⟨t, ht0, ht⟩ := exists_tendsto_nhdsWithin_of_isRoot hx hconn hf hroot hcoeff hdeg hne
  rwa [extendFrom_eq hx ht]

/-- Over a proper normed field `K`, along any subset `B ⊆ closure U` where `U` has preconnected
approach regions, `p` is nonzero, and the coefficients up to `(p x).natDegree` converge along
`𝓝[U] x` without degree increase, `extendFrom U f` is continuous on `B`. -/
theorem continuousOn_extendFrom_of_isRoot_of_subset_closure {B : Set X} (hB : B ⊆ closure U)
    (hconn : ∀ x ∈ B, IsPreconnectedApproachAt U x)
    (hf : ContinuousOn f U) (hroot : ∀ y ∈ U, (p y).eval (f y) = 0)
    (hcoeff : ∀ x ∈ B, ∀ i ≤ (p x).natDegree,
      Tendsto (fun y ↦ (p y).coeff i) (𝓝[U] x) (𝓝 ((p x).coeff i)))
    (hdeg : ∀ x ∈ B, ∀ᶠ y in 𝓝[U] x, (p y).natDegree ≤ (p x).natDegree)
    (hne : ∀ x ∈ B, p x ≠ 0) :
    ContinuousOn (extendFrom U f) B :=
  continuousOn_extendFrom hB fun x hx ↦
    let ⟨t, _, ht⟩ := exists_tendsto_nhdsWithin_of_isRoot (hB hx) (hconn x hx) hf
      (eventually_nhdsWithin_of_forall hroot) (hcoeff x hx) (hdeg x hx) (hne x hx)
    ⟨t, ht⟩

end NormedField

variable {X : Type*} [TopologicalSpace X] {U : Set X} {p : X → Polynomial ℝ}
  {f : X → ℝ} {x : X} {t : ℝ}

/-- A cluster value of a polynomial root section is a root of the specialization at the
approach point, provided evaluation is continuous on the closure of the base. -/
theorem eval_eq_zero_of_mem_clusterSetOn
    (hp : ContinuousOn (fun z : X × ℝ ↦ (p z.1).eval z.2) (closure U ×ˢ univ))
    (hf : ∀ y ∈ U, (p y).eval (f y) = 0) (ht : t ∈ clusterSetOn f U x) :
    (p x).eval t = 0 := by
  have hpair : MapClusterPt (x, t) (𝓝[U] x) (fun y ↦ (y, f y)) := by
    rw [mapClusterPt_iff_frequently]
    intro s hs
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hs
    exact (((mem_clusterSetOn_iff.mp ht).frequently hW).and_eventually (nhdsWithin_le_nhds hV)).mono
      fun y hy ↦ hVW ⟨hy.2, hy.1⟩
  have hclosed : IsClosed {z : X × ℝ | z.1 ∈ closure U ∧ (p z.1).eval z.2 = 0} := by
    simpa only [mem_prod, mem_univ, and_true, mem_ofPred_eq] using
      (isClosed_closure.prod isClosed_univ).isClosed_eq hp continuousOn_const
  exact (hclosed.mem_of_mapClusterPt hpair
    (eventually_nhdsWithin_of_forall fun y hy ↦ ⟨subset_closure hy, hf y hy⟩)).2

/-- A preconnected cluster set of a root section is a subsingleton when the specialized
polynomial is nonzero. In particular, repeated roots at the boundary cause no obstruction. -/
theorem subsingleton_clusterSetOn_of_polynomial_root
    (hp : ContinuousOn (fun z : X × ℝ ↦ (p z.1).eval z.2) (closure U ×ˢ univ))
    (hf : ∀ y ∈ U, (p y).eval (f y) = 0) (hx : p x ≠ 0)
    (hconn : IsPreconnected (clusterSetOn f U x)) :
    (clusterSetOn f U x).Subsingleton := by
  have hfinite : (clusterSetOn f U x).Finite :=
    (Polynomial.finite_setOfPred_isRoot hx).subset fun t ht ↦
      eval_eq_zero_of_mem_clusterSetOn hp hf ht
  exact hconn.isDiscrete_iff_subsingleton.mp hfinite.isDiscrete

/-- A bounded continuous root section extends continuously to the closure of its base when
all specializations there are nonzero and the base has preconnected approach regions.
The base need not be open or full-dimensional. -/
theorem continuousOn_extendFrom_of_polynomial_root
    (hp : ContinuousOn (fun z : X × ℝ ↦ (p z.1).eval z.2) (closure U ×ˢ univ))
    (hf : ContinuousOn f U) (hroot : ∀ y ∈ U, (p y).eval (f y) = 0)
    (hbdd : Bornology.IsBounded (f '' U)) (hne : ∀ x ∈ closure U, p x ≠ 0)
    (hconn : ∀ x ∈ closure U, IsPreconnectedApproachAt U x) :
    ContinuousOn (extendFrom U f) (closure U) := by
  refine continuousOn_extendFrom subset_rfl fun x hx ↦ ?_
  refine exists_tendsto_of_clusterSetOn_subsingleton hbdd.isCompact_closure
    (fun y hy ↦ subset_closure (mem_image_of_mem f hy)) hx ?_
  exact subsingleton_clusterSetOn_of_polynomial_root hp hroot (hne x hx)
    (isPreconnected_clusterSetOn hbdd.isCompact_closure
      (fun y hy ↦ subset_closure (mem_image_of_mem f hy)) hf (hconn x hx))

/-- The continuous extension of a root section still solves the same polynomial equation
on the closure, even where distinct roots coalesce. -/
theorem eval_extendFrom_eq_zero
    (hp : ContinuousOn (fun z : X × ℝ ↦ (p z.1).eval z.2) (closure U ×ˢ univ))
    (hf : ContinuousOn f U) (hroot : ∀ y ∈ U, (p y).eval (f y) = 0)
    (hF : ContinuousOn (extendFrom U f) (closure U)) (hx : x ∈ closure U) :
    (p x).eval (extendFrom U f x) = 0 := by
  have hlim := (hF x hx).mono (subset_closure : U ⊆ closure U)
  have heq := extendFrom_extends hf
  have hlim' : Tendsto f (𝓝[U] x) (𝓝 (extendFrom U f x)) :=
    hlim.congr' (eventually_nhdsWithin_of_forall fun y hy ↦ heq y hy)
  exact eval_eq_zero_of_mem_clusterSetOn hp hroot (by
    rw [clusterSetOn_eq_singleton_of_tendsto hx hlim']
    exact mem_singleton _)

end TauCeti
