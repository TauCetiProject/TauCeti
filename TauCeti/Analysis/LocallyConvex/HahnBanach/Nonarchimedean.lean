/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Topology.MetricSpace.SphericallyComplete
import Mathlib.LinearAlgebra.LinearPMap
import TauCeti.Analysis.Normed.Module.Seminorm.Nonarchimedean

/-!
# Nonarchimedean Hahn–Banach theorem for seminorms and locally convex spaces

Over a normed field, Ingleton's nonarchimedean Hahn–Banach theorem extends any linear map
`f : U →ₗ[K] W` dominated by a nonarchimedean seminorm `p` on `V` to all of `V` while preserving
the bound `‖g x‖ ≤ p x`, provided that the codomain `W` is ultrapseudometric and spherically
complete. In contrast to the real and complex Hahn–Banach theorem, the codomain `W` need not be
one-dimensional: spherical completeness supplies a common point in the pairwise-intersecting family
of closed balls `closedBall (f u) (p (u - v))` needed for the one-step extension, and Zorn's lemma
completes the proof.

In a locally convex space whose topology is induced by a family of nonarchimedean seminorms, every
continuous linear map from a subspace into a spherically complete ultrapseudometric space extends
continuously to the whole space. When the scalar field `K` is itself ultrametric and spherically
complete, continuous linear functionals separate points from closed subspaces, characterize
subspace closures, and separate points in every `T₀` space.

## Main results

* `LinearMap.exists_extension_norm_le_of_isNonarchimedean`: Ingleton's nonarchimedean
  Hahn–Banach theorem for a linear map dominated by a nonarchimedean seminorm.
* `LinearMap.exists_continuous_extension_norm_le_of_isNonarchimedean`: continuous version when the
  dominating nonarchimedean seminorm is continuous.
* `Submodule.exists_strongDual_eq_zero_apply_eq_one_norm_le_of_isNonarchimedean`: quantitative
  separation of a vector from a submodule with respect to a continuous nonarchimedean seminorm.
* `WithSeminorms.exists_extension_of_isNonarchimedean`: continuous extension of a linear map from
  a subspace of a nonarchimedean locally convex space into a spherically complete ultrapseudometric
  space.
* `WithSeminorms.exists_strongDual_eq_zero_of_notMem_closure_of_isNonarchimedean`: separation of a
  vector from a closed subspace by a continuous linear functional.
* `WithSeminorms.mem_closure_iff_forall_strongDual_eq_zero_of_isNonarchimedean`: closure of a
  subspace coincides with the intersection of kernels of continuous linear functionals vanishing
  on it.
* `WithSeminorms.separatingDual_of_isNonarchimedean`: a `T₀` locally convex space defined by
  nonarchimedean seminorms over a spherically complete ultrametric field has separating dual.

## References

* A. W. Ingleton, *The Hahn–Banach theorem for non-Archimedean-valued fields*,
  Proc. Cambridge Philos. Soc. 48 (1952), 41–45.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §9.
* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*,
  Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010, Chapter 4.
-/

public section

open Metric Set Submodule Topology
open scoped NNReal

namespace LinearMap

section Algebraic

variable {K V W : Type*} [NormedField K] [AddCommGroup V] [Module K V]
  [SeminormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]
  [TauCeti.SphericallyCompleteSpace W]

/-- One-step extension of a partially defined linear map dominated by a nonarchimedean seminorm
onto `q.domain ⊔ K ∙ v`. -/
private theorem exists_supSpanSingleton_norm_le {p : Seminorm K V} (hp : IsNonarchimedean p)
    (q : V →ₗ.[K] W) (hq : ∀ u : q.domain, ‖q u‖ ≤ p u) {v : V} (hv : v ∉ q.domain) :
    ∃ q' : V →ₗ.[K] W, q < q' ∧ ∀ u : q'.domain, ‖q' u‖ ≤ p u := by
  have hdist (u₁ u₂ : q.domain) : dist (q u₁) (q u₂) ≤ max (p (u₁ - v)) (p (u₂ - v)) := by
    rw [dist_eq_norm, ← q.map_sub]
    calc ‖q (u₁ - u₂)‖ ≤ p ((u₁ : V) - u₂) := hq (u₁ - u₂)
      _ = p (((u₁ : V) - v) + -((u₂ : V) - v)) := by abel_nf
      _ ≤ max (p ((u₁ : V) - v)) (p (-((u₂ : V) - v))) := hp _ _
      _ = max (p ((u₁ : V) - v)) (p ((u₂ : V) - v)) := by rw [map_neg_eq_map]
  obtain ⟨w, hw⟩ :=
    TauCeti.SphericallyCompleteSpace.nonempty_iInter_closedBall_of_dist_le_max hdist
  have hw' (u : q.domain) : ‖w - q u‖ ≤ p ((u : V) - v) := by
    simpa [mem_closedBall, dist_eq_norm] using Set.mem_iInter.1 hw u
  refine ⟨q.supSpanSingleton v w hv, ?_, ?_⟩
  · refine lt_iff_le_not_ge.2 ⟨q.left_le_sup _ _, fun hle ↦ ?_⟩
    have hdom := LinearPMap.domain_mono.monotone hle
    rw [LinearPMap.domain_supSpanSingleton, sup_le_iff, span_le, singleton_subset_iff] at hdom
    exact hv hdom.2
  · rintro ⟨z, hz⟩
    rcases mem_sup.1 hz with ⟨u, hu, y, hy, rfl⟩
    rcases mem_span_singleton.1 hy with ⟨a, rfl⟩
    rw [LinearPMap.supSpanSingleton_apply_mk q v w hv u hu a, RingHom.id_apply]
    by_cases ha : a = 0
    · simpa [ha] using hq ⟨u, hu⟩
    · let u' : q.domain := (-a⁻¹) • ⟨u, hu⟩
      have hqu' : q u' = (-a⁻¹) • q ⟨u, hu⟩ := q.map_smul (-a⁻¹) ⟨u, hu⟩
      have hu' : (u' : V) = (-a⁻¹) • u := rfl
      have hrewrite : q ⟨u, hu⟩ + a • w = a • (w - q u') := by
        rw [smul_sub, hqu', neg_smul, smul_neg, sub_neg_eq_add, smul_smul,
          mul_inv_cancel₀ ha, one_smul, add_comm]
      have harg : a • ((u' : V) - v) = -(u + a • v) := by
        rw [hu', smul_sub, neg_smul, smul_neg, smul_smul, mul_inv_cancel₀ ha, one_smul]
        abel
      calc ‖q ⟨u, hu⟩ + a • w‖ = ‖a • (w - q u')‖ := by rw [hrewrite]
        _ = ‖a‖ * ‖w - q u'‖ := norm_smul a (w - q u')
        _ ≤ ‖a‖ * p ((u' : V) - v) := mul_le_mul_of_nonneg_left (hw' u') (norm_nonneg a)
        _ = p (a • ((u' : V) - v)) := (map_smul_eq_mul p a _).symm
        _ = p (-(u + a • v)) := by rw [harg]
        _ = p (u + a • v) := map_neg_eq_map p _

/-- **Ingleton's nonarchimedean Hahn–Banach theorem** (seminorm form): a linear map `f : U →ₗ[K] W`
from a submodule `U` into a spherically complete ultrapseudometric space `W`, dominated by a
nonarchimedean seminorm `p` on `V`, extends to a linear map `g : V →ₗ[K] W` satisfying
`‖g x‖ ≤ p x` for all `x : V`. -/
theorem exists_extension_norm_le_of_isNonarchimedean {U : Submodule K V} (f : U →ₗ[K] W)
    {p : Seminorm K V} (hp : IsNonarchimedean p) (hfp : ∀ u : U, ‖f u‖ ≤ p u) :
    ∃ g : V →ₗ[K] W, (∀ u : U, g u = f u) ∧ ∀ x, ‖g x‖ ≤ p x := by
  let S : Set (V →ₗ.[K] W) := {q | ∀ u : q.domain, ‖q u‖ ≤ p u}
  have hSc : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hchain y hy
    have hcd : DirectedOn (· ≤ ·) c := hchain.directedOn
    refine ⟨LinearPMap.sSup c hcd, ?_, fun _ ↦ LinearPMap.le_sSup hcd⟩
    intro x
    obtain ⟨q, hqc, hxq⟩ := (LinearPMap.mem_domain_sSup_iff ⟨y, hy⟩ hcd).1 x.property
    have heq : LinearPMap.sSup c hcd x = q ⟨x, hxq⟩ :=
      LinearPMap.sSup_apply hcd hqc ⟨x, hxq⟩
    rw [heq]
    exact hcS hqc ⟨x, hxq⟩
  obtain ⟨q, hfq, hqS, hqmax⟩ := zorn_le_nonempty₀ S hSc ⟨U, f⟩ hfp
  have htop : q.domain = ⊤ := by
    by_contra hne
    obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hne)
    obtain ⟨q', hqq', hq'S⟩ := exists_supSpanSingleton_norm_le hp q hqS hv
    exact hqq'.ne' ((hqmax hq'S hqq'.le).antisymm hqq'.le)
  rcases q with ⟨qdom, qfun⟩
  subst htop
  refine ⟨qfun.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial), fun u ↦ ?_,
    fun x ↦ hqS ⟨x, trivial⟩⟩
  exact (hfq.2 (x := u) (y := ⟨u, trivial⟩) rfl).symm

/-- Continuous version of Ingleton's nonarchimedean Hahn–Banach theorem: if the dominating
nonarchimedean seminorm `p` is continuous on a topological additive group `V`, then the extended
linear map is continuous. -/
theorem exists_continuous_extension_norm_le_of_isNonarchimedean [TopologicalSpace V]
    [IsTopologicalAddGroup V] {U : Submodule K V} (f : U →ₗ[K] W) {p : Seminorm K V}
    (hp_na : IsNonarchimedean p) (hp_cont : Continuous p) (hfp : ∀ u : U, ‖f u‖ ≤ p u) :
    ∃ g : V →L[K] W, (∀ u : U, g u = f u) ∧ ∀ x, ‖g x‖ ≤ p x := by
  obtain ⟨g, hgf, hgp⟩ := f.exists_extension_norm_le_of_isNonarchimedean hp_na hfp
  have hcont : Continuous g := by
    refine continuous_of_continuousAt_zero g ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hgp (by simpa using hp_cont.tendsto 0)
  exact ⟨⟨g, hcont⟩, hgf, hgp⟩

end Algebraic

end LinearMap

namespace Submodule

section SeminormSeparation

variable {K V : Type*} [NormedField K] [IsUltrametricDist K]
  [TauCeti.SphericallyCompleteSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V]

/-- Given a continuous nonarchimedean seminorm `q`, a submodule `U`, a vector `v`, and `0 < r`
with `r ≤ q (u - v)` for all `u ∈ U`, there exists a continuous linear functional vanishing on
`U`, taking the value `1` at `v`, and bounded by `r⁻¹ * q x` everywhere. -/
theorem exists_strongDual_eq_zero_apply_eq_one_norm_le_of_isNonarchimedean (U : Submodule K V)
    {q : Seminorm K V} (hq_na : IsNonarchimedean q) (hq_cont : Continuous q)
    {v : V} {r : ℝ} (hr : 0 < r) (hdist : ∀ u ∈ U, r ≤ q (u - v)) :
    ∃ ℓ : StrongDual K V, (∀ u ∈ U, ℓ u = 0) ∧ ℓ v = 1 ∧ ∀ x, ‖ℓ x‖ ≤ r⁻¹ * q x := by
  have hvU : v ∉ U := fun hv ↦ by
    have h := hdist v hv
    rw [sub_self, map_zero] at h
    exact hr.not_ge h
  let f : V →ₗ.[K] K := LinearPMap.supSpanSingleton ⟨U, 0⟩ v 1 hvU
  let rInv : ℝ≥0 := ⟨r⁻¹, inv_nonneg.2 hr.le⟩
  have hf_le : ∀ z : f.domain, ‖f z‖ ≤ (rInv • q) z := by
    rintro ⟨z, hz⟩
    rcases mem_sup.1 hz with ⟨u, hu, y, hy, rfl⟩
    rcases mem_span_singleton.1 hy with ⟨a, rfl⟩
    rw [LinearPMap.supSpanSingleton_apply_mk ⟨U, 0⟩ v 1 hvU u hu a]
    simp only [LinearPMap.mk_apply, LinearMap.zero_apply, RingHom.id_apply, smul_eq_mul, mul_one,
      zero_add, FunLike.coe_smul, Pi.smul_apply, NNReal.smul_def]
    by_cases ha : a = 0
    · simpa [ha] using mul_nonneg rInv.property (apply_nonneg q u)
    · have hmem : -(a⁻¹ • u) ∈ U := U.neg_mem (U.smul_mem a⁻¹ hu)
      have hle : r * ‖a‖ ≤ q (u + a • v) := by
        calc r * ‖a‖ ≤ q (-(a⁻¹ • u) - v) * ‖a‖ :=
              mul_le_mul_of_nonneg_right (hdist _ hmem) (norm_nonneg a)
          _ = ‖a‖ * q (-(a⁻¹ • u) - v) := mul_comm _ _
          _ = q (a • (-(a⁻¹ • u) - v)) := (map_smul_eq_mul q a _).symm
          _ = q (-(u + a • v)) := by
              congr 1
              simp only [smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ ha, one_smul]
              abel
          _ = q (u + a • v) := map_neg_eq_map q _
      have hrInv : (rInv : ℝ) = r⁻¹ := rfl
      rw [hrInv, inv_mul_eq_div]
      exact (le_div_iff₀' hr).2 hle
  obtain ⟨ℓ, hℓ, hℓ_le⟩ := f.toFun.exists_continuous_extension_norm_le_of_isNonarchimedean
    (hq_na.smul_seminorm rInv) (hq_cont.const_smul rInv) hf_le
  refine ⟨ℓ, fun u hu ↦ ?_, ?_, hℓ_le⟩
  · exact (hℓ ⟨u, mem_sup_left hu⟩).trans (LinearPMap.supSpanSingleton_apply_mk_of_mem _ _ _ hu)
  · exact (hℓ ⟨v, mem_sup_right (mem_span_singleton_self v)⟩).trans
      (LinearPMap.supSpanSingleton_apply_self _ _ _)

end SeminormSeparation

end Submodule

namespace WithSeminorms

section Extension

variable {K V W ι : Type*} [NontriviallyNormedField K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V] {p : SeminormFamily K V ι}
  [SeminormedAddCommGroup W] [NormedSpace K W] [IsUltrametricDist W]
  [TauCeti.SphericallyCompleteSpace W]

/-- **Nonarchimedean Hahn–Banach theorem** for locally convex spaces: in a space whose topology is
induced by a family of nonarchimedean seminorms, every continuous linear map from a subspace into
a spherically complete ultrapseudometric space extends continuously to the whole space. -/
theorem exists_extension_of_isNonarchimedean (hp : WithSeminorms p)
    (hp_na : ∀ i, IsNonarchimedean (p i)) {U : Submodule K V} (f : U →L[K] W) :
    ∃ g : V →L[K] W, ∀ u : U, g u = f u := by
  have : IsTopologicalAddGroup V := hp.isTopologicalAddGroup
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_comp_of_isInducing (f := U.subtype)
    (p := (normSeminorm K W).comp f.toLinearMap) f.continuous.norm hp IsInducing.subtypeVal
  have hna : IsNonarchimedean (C • s.sup p) :=
    (TauCeti.isNonarchimedean_finsetSup fun i _ ↦ hp_na i).smul_seminorm C
  have hcont : Continuous (C • s.sup p) := (hp.continuous_finsetSup_seminorm s).const_smul C
  obtain ⟨g, hg, -⟩ :=
    f.toLinearMap.exists_continuous_extension_norm_le_of_isNonarchimedean hna hcont hC
  exact ⟨g, hg⟩

end Extension

section Separation

variable {K V ι : Type*} [NormedField K] [IsUltrametricDist K]
  [TauCeti.SphericallyCompleteSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] {p : SeminormFamily K V ι}

/-- In a locally convex space defined by a family of nonarchimedean seminorms over a spherically
complete ultrametric field, any vector outside the closure of a submodule `U` can be separated from
`U` by a continuous linear functional vanishing on `U` and taking the value `1` at `v`. -/
theorem exists_strongDual_eq_zero_of_notMem_closure_of_isNonarchimedean (hp : WithSeminorms p)
    (hp_na : ∀ i, IsNonarchimedean (p i)) (U : Submodule K V) {v : V}
    (hv : v ∉ closure (U : Set V)) :
    ∃ ℓ : StrongDual K V, (∀ u ∈ U, ℓ u = 0) ∧ ℓ v = 1 := by
  have : IsTopologicalAddGroup V := hp.isTopologicalAddGroup
  obtain ⟨s, r, hr, hball⟩ :=
    (hp.mem_nhds_iff v _).1 (isClosed_closure.isOpen_compl.mem_nhds hv)
  have hq_dist (u : V) (hu : u ∈ U) : r ≤ (s.sup p : Seminorm K V) (u - v) := by
    by_contra! hlt
    exact hball ((Seminorm.mem_ball _).2 hlt) (subset_closure hu)
  obtain ⟨ℓ, hℓU, hℓv, -⟩ :=
    U.exists_strongDual_eq_zero_apply_eq_one_norm_le_of_isNonarchimedean
      (TauCeti.isNonarchimedean_finsetSup fun i _ ↦ hp_na i)
      (hp.continuous_finsetSup_seminorm s) hr hq_dist
  exact ⟨ℓ, hℓU, hℓv⟩

/-- In a locally convex space defined by a family of nonarchimedean seminorms over a spherically
complete ultrametric field, a vector lies in the closure of a submodule `U` iff every continuous
linear functional vanishing on `U` also vanishes at `v`. -/
theorem mem_closure_iff_forall_strongDual_eq_zero_of_isNonarchimedean (hp : WithSeminorms p)
    (hp_na : ∀ i, IsNonarchimedean (p i)) (U : Submodule K V) {v : V} :
    v ∈ closure (U : Set V) ↔ ∀ ℓ : StrongDual K V, (∀ u ∈ U, ℓ u = 0) → ℓ v = 0 := by
  refine ⟨fun hv ℓ hℓ ↦ ?_, fun h ↦ ?_⟩
  · have hsub : (U : Set V) ⊆ ℓ ⁻¹' {0} := fun u hu ↦ hℓ u hu
    exact closure_minimal hsub (isClosed_singleton.preimage ℓ.continuous) hv
  · by_contra hv
    obtain ⟨ℓ, hℓU, hℓv⟩ :=
      hp.exists_strongDual_eq_zero_of_notMem_closure_of_isNonarchimedean hp_na U hv
    exact one_ne_zero (hℓv.symm.trans (h ℓ hℓU))

/-- A `T₀` locally convex space defined by a family of nonarchimedean seminorms over a spherically
complete ultrametric field has separating continuous dual. -/
theorem separatingDual_of_isNonarchimedean [T0Space V] (hp : WithSeminorms p)
    (hp_na : ∀ i, IsNonarchimedean (p i)) : SeparatingDual K V := by
  have : IsTopologicalAddGroup V := hp.isTopologicalAddGroup
  refine ⟨fun x hx ↦ ?_⟩
  have hxcl : x ∉ closure ((⊥ : Submodule K V) : Set V) := by
    simpa [Submodule.bot_coe, isClosed_singleton.closure_eq] using hx
  obtain ⟨ℓ, -, hℓx⟩ :=
    hp.exists_strongDual_eq_zero_of_notMem_closure_of_isNonarchimedean hp_na ⊥ hxcl
  exact ⟨ℓ, hℓx.symm ▸ one_ne_zero⟩

end Separation

end WithSeminorms
