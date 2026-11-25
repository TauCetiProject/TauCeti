/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Analysis.Normed.Operator.Compact.Spectrum
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Discreteness of the spectrum over a compactly embedded common domain

Let `ι : D →L H` be a compact operator from a Banach space `D` to a normed space `H` and
`A : D →L H` a bounded operator, and suppose that one shift `c₀ • ι - A` is invertible. In the
analysis of Floer trajectories `ι` is the compact inclusion `H¹ → L²` of a common domain and `A`
the asymptotic operator `J₀ ∂ₜ + S`. This file shows that the scalars `c` at which the shift
`c • ι - A` fails to be invertible form a discrete set, consisting of eigenvalues of the pencil.

Write `K = (c₀ • ι - A)⁻¹ ∘ ι`, a compact operator on `D`. For `c ≠ c₀`, a vector `x` solves
`A x = c • ι x` exactly when `K x = (c₀ - c)⁻¹ • x`, and `c • ι - A` is `c₀ • ι - A` composed with
`(c₀ - c) • ((c₀ - c)⁻¹ - K)`. So the Fredholm alternative for `K` and the finiteness of its
eigenvalues away from `0` transfer to the shifts:

* `c • ι - A` is invertible exactly when it is injective
  (`ContinuousLinearMap.isInvertible_smul_sub_iff_injective`);
* only finitely many shifts in a bounded set fail to be invertible
  (`ContinuousLinearMap.finite_inter_setOf_not_isInvertible_smul_sub`), so near every scalar all
  other shifts are invertible (`ContinuousLinearMap.eventually_isInvertible_smul_sub`).

Neither injectivity of `ι` nor completeness of `H` is assumed. When `ι` is injective and `H` is
complete these are statements about the partial operator
`ContinuousLinearMap.domainOperator ι A hι` with domain `range ι`: its spectrum meets every bounded
set in finitely many points (`ContinuousLinearMap.finite_inter_spectrum_domainOperator`).

Over `ℝ` or `ℂ`, the admissible real shifts, the real `c` at which `(c : 𝕜) • ι - A` is
invertible, are dense (`ContinuousLinearMap.eventually_isInvertible_ofReal_smul_sub`,
`ContinuousLinearMap.exists_mem_Ioo_isInvertible_ofReal_smul_sub`). For a continuous family
`A t`, an admissible shift at one time stays admissible nearby
(`ContinuousLinearMap.exists_mem_Ioo_eventually_isInvertible_ofReal_smul_sub`), and over a compact
set `s` of times, given a nonempty open interval, there is a radius `δ > 0` such that every
`δ`-ball of times in `s` carries a common admissible shift from that interval
(`ContinuousLinearMap.exists_pos_forall_exists_mem_Ioo_isInvertible_ofReal_smul_sub`). These are
the local choices from which constructions along a path of unbounded self-adjoint operators,
such as the spectral flow of the bounded transforms `c A (c ι - A)⁻¹`, are glued.

## Main results

* `ContinuousLinearMap.isInvertible_smul_sub_iff_injective`: a shift is invertible exactly when
  it is injective.
* `ContinuousLinearMap.finite_inter_setOf_not_isInvertible_smul_sub`: the non-invertible shifts
  in a bounded set are finitely many.
* `ContinuousLinearMap.eventually_isInvertible_smul_sub`: the non-invertible shifts are isolated.
* `ContinuousLinearMap.finite_inter_spectrum_domainOperator`: the spectrum of the partial operator
  meets every bounded set in a finite set.
* `ContinuousLinearMap.exists_mem_Ioo_isInvertible_ofReal_smul_sub`: every open interval contains
  an admissible real shift.
* `ContinuousLinearMap.exists_pos_forall_exists_mem_Ioo_isInvertible_ofReal_smul_sub`: uniformly
  local admissible real shifts along a compact family.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Theorem III.6.29 (operators with compact
  resolvent have discrete spectrum).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, Section 4 (paths of self-adjoint operators on a compactly embedded common
  domain).
-/

public section

open Filter Function Metric Set Topology

namespace ContinuousLinearMap

section Field

variable {𝕜 D H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {ι A : D →L[𝕜] H} {c₀ c : 𝕜}

/-- A shift `c • ι - A` differs from the shift `c₀ • ι - A` by `(c₀ - c) • ι`. -/
private theorem smul_sub_eq_smul_sub_sub (c₀ c : 𝕜) (ι A : D →L[𝕜] H) :
    c • ι - A = (c₀ • ι - A) - (c₀ - c) • ι := by
  rw [sub_smul]
  abel

/-- Away from an invertible shift `c₀ • ι - A`, a vector is killed by the shift `c • ι - A` exactly
when it is an eigenvector of `(c₀ • ι - A)⁻¹ ∘ ι` with eigenvalue `(c₀ - c)⁻¹`. -/
private theorem smul_sub_apply_eq_zero_iff (h₀ : (c₀ • ι - A).IsInvertible) (hc : c ≠ c₀)
    (x : D) :
    (c • ι - A) x = 0 ↔ ((c₀ • ι - A).inverse ∘L ι) x = (c₀ - c)⁻¹ • x := by
  have hc' : c₀ - c ≠ 0 := sub_ne_zero.2 hc.symm
  rw [smul_sub_eq_smul_sub_sub c₀, sub_apply, sub_eq_zero, comp_apply, eq_inv_smul_iff₀ hc',
    ← map_smul, smul_apply, h₀.inverse_apply_eq, eq_comm (a := (c₀ • ι - A) x)]

/-- **Fredholm alternative for shifts.** If `ι` is compact and one shift `c₀ • ι - A` is
invertible, a shift `c • ι - A` is invertible exactly when it is injective. -/
theorem isInvertible_smul_sub_iff_injective [CompleteSpace D] (hcpt : IsCompactOperator ι)
    (h₀ : (c₀ • ι - A).IsInvertible) :
    (c • ι - A).IsInvertible ↔ Injective (c • ι - A) := by
  refine ⟨fun h ↦ h.bijective.1, fun hinj ↦ ?_⟩
  rcases eq_or_ne c c₀ with rfl | hc
  · exact h₀
  set K : D →L[𝕜] D := (c₀ • ι - A).inverse ∘L ι
  have hK : IsCompactOperator K := hcpt.clm_comp _
  have hc' : c₀ - c ≠ 0 := sub_ne_zero.2 hc.symm
  -- `(c₀ - c)⁻¹` is not an eigenvalue of the compact operator `K`, so it is a resolvent point.
  have hnot : ¬Module.End.HasEigenvalue (K : Module.End 𝕜 D) (c₀ - c)⁻¹ := fun he ↦ by
    obtain ⟨x, hx⟩ := he.exists_hasEigenvector
    refine hx.2 (hinj ?_)
    rw [map_zero, smul_sub_apply_eq_zero_iff h₀ hc]
    exact Module.End.mem_eigenspace_iff.1 hx.1
  have hres := (hK.hasEigenvalue_or_mem_resolventSet (inv_ne_zero hc')).resolve_left hnot
  rw [spectrum.mem_resolventSet_iff] at hres
  -- `c • ι - A = (c₀ • ι - A) ∘ ((c₀ - c) • ((c₀ - c)⁻¹ - K))`, a composition of invertible maps.
  have hfac : c • ι - A = (c₀ • ι - A) ∘L (algebraMap 𝕜 (D →L[𝕜] D) (c₀ - c) *
      (algebraMap 𝕜 (D →L[𝕜] D) (c₀ - c)⁻¹ - K)) := by
    ext x
    have hKx : (c₀ • ι - A) (K x) = ι x := h₀.self_apply_inverse (ι x)
    have hu : (algebraMap 𝕜 (D →L[𝕜] D) (c₀ - c) *
        (algebraMap 𝕜 (D →L[𝕜] D) (c₀ - c)⁻¹ - K)) x = x - (c₀ - c) • K x := by
      simp [smul_sub, smul_smul, hc', -map_sub]
    rw [comp_apply, hu]
    simp only [map_sub, map_smul, hKx, sub_apply, smul_apply, sub_smul]
    abel
  rw [hfac]
  exact h₀.comp (isInvertible_iff_isUnit.2 ((isUnit_iff_ne_zero.2 hc').map _ |>.mul hres))

/-- **Discreteness of the spectrum over a compactly embedded domain.** If `ι` is compact and one
shift `c₀ • ι - A` is invertible, only finitely many shifts `c • ι - A` with `c` in a bounded set
fail to be invertible. -/
theorem finite_inter_setOf_not_isInvertible_smul_sub [CompleteSpace D]
    (hcpt : IsCompactOperator ι) (h₀ : (c₀ • ι - A).IsInvertible) {s : Set 𝕜}
    (hs : Bornology.IsBounded s) :
    (s ∩ {c | ¬(c • ι - A).IsInvertible}).Finite := by
  obtain ⟨r, hr⟩ := hs.subset_closedBall c₀
  set K : D →L[𝕜] D := (c₀ • ι - A).inverse ∘L ι
  have hK : IsCompactOperator K := hcpt.clm_comp _
  have hR : 0 < max r 1 := lt_max_of_lt_right one_pos
  -- The shifts `c` correspond injectively to eigenvalues `(c₀ - c)⁻¹` of `K` of norm at least
  -- `(max r 1)⁻¹`, which are finitely many.
  have hinj : Injective fun c : 𝕜 ↦ (c₀ - c)⁻¹ :=
    inv_injective.comp fun _ _ h ↦ sub_right_injective h
  refine (hK.finite_eigenvalues_norm_ge (inv_pos.2 hR)).preimage hinj.injOn |>.subset ?_
  rintro c ⟨hcs, hcA⟩
  have hc : c ≠ c₀ := by rintro rfl; exact hcA h₀
  have hc' : 0 < ‖c₀ - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hc.symm)
  obtain ⟨x, hx, hx0⟩ : ∃ x, (c • ι - A) x = 0 ∧ x ≠ 0 := by
    by_contra! h
    exact hcA ((isInvertible_smul_sub_iff_injective hcpt h₀).2
      ((injective_iff_map_eq_zero _).2 h))
  refine ⟨Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 ((smul_sub_apply_eq_zero_iff h₀ hc x).1 hx), hx0⟩, ?_⟩
  rw [norm_inv]
  refine inv_anti₀ hc' ?_
  rw [norm_sub_rev, ← dist_eq_norm]
  exact (mem_closedBall.1 (hr hcs)).trans (le_max_left _ _)

/-- **Isolation of the non-invertible shifts.** If `ι` is compact and one shift `c₀ • ι - A` is
invertible, then near every scalar `c₁`, every other shift `c • ι - A` is invertible. -/
theorem eventually_isInvertible_smul_sub [CompleteSpace D] (hcpt : IsCompactOperator ι)
    (h₀ : (c₀ • ι - A).IsInvertible) (c₁ : 𝕜) :
    ∀ᶠ c in 𝓝[≠] c₁, (c • ι - A).IsInvertible := by
  have hF := finite_inter_setOf_not_isInvertible_smul_sub hcpt h₀ (isBounded_closedBall (x := c₁)
    (r := 1))
  have hnhds : ((closedBall c₁ 1 ∩ {c | ¬(c • ι - A).IsInvertible}) \ {c₁})ᶜ ∈ 𝓝 c₁ :=
    hF.sdiff.isClosed.compl_mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hnhds, nhdsWithin_le_nhds (closedBall_mem_nhds c₁ one_pos),
    self_mem_nhdsWithin] with c hc hball hne
  by_contra h
  exact hc ⟨⟨hball, h⟩, hne⟩

/-- **Discreteness of the spectrum of an operator on a compactly embedded domain.** If `ι` is
compact and injective and `domainOperator ι A hι` has a resolvent point, its spectrum meets every
bounded set in finitely many points. -/
theorem finite_inter_spectrum_domainOperator [CompleteSpace D] [CompleteSpace H]
    (hcpt : IsCompactOperator ι) {hι : Injective ι}
    (h₀ : (domainOperator ι A hι).resolventSet.Nonempty) {s : Set 𝕜}
    (hs : Bornology.IsBounded s) : (s ∩ (domainOperator ι A hι).spectrum).Finite := by
  obtain ⟨c₀, hc₀⟩ := h₀
  refine (finite_inter_setOf_not_isInvertible_smul_sub hcpt
    (mem_resolventSet_domainOperator_iff.1 hc₀) hs).subset fun c ⟨hcs, hc⟩ ↦ ⟨hcs, fun h ↦ ?_⟩
  exact (LinearPMap.mem_spectrum_iff _ c).1 hc (mem_resolventSet_domainOperator_iff.2 h)

end Field

section RCLike

variable {𝕜 D H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D] [CompleteSpace D] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] {ι A : D →L[𝕜] H} {c₀ : 𝕜}

/-- **Density of the admissible real shifts.** If `ι` is compact and one shift `c₀ • ι - A` is
invertible, then near every real `c₁`, every other real shift `(c : 𝕜) • ι - A` is invertible. -/
theorem eventually_isInvertible_ofReal_smul_sub (hcpt : IsCompactOperator ι)
    (h₀ : (c₀ • ι - A).IsInvertible) (c₁ : ℝ) :
    ∀ᶠ c : ℝ in 𝓝[≠] c₁, ((c : 𝕜) • ι - A).IsInvertible :=
  (RCLike.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ hc ↦
    (RCLike.ofReal_injective (K := 𝕜)).ne hc).eventually
    (eventually_isInvertible_smul_sub hcpt h₀ (c₁ : 𝕜))

/-- If `ι` is compact and one shift `c₀ • ι - A` is invertible, every nonempty open interval
contains a real `c` at which the shift `(c : 𝕜) • ι - A` is invertible. -/
theorem exists_mem_Ioo_isInvertible_ofReal_smul_sub (hcpt : IsCompactOperator ι)
    (h₀ : (c₀ • ι - A).IsInvertible) {p q : ℝ} (hpq : p < q) :
    ∃ c ∈ Ioo p q, ((c : 𝕜) • ι - A).IsInvertible := by
  have hmem : Ioo p q ∈ 𝓝[≠] ((p + q) / 2) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨c, hc, hcq⟩ := ((eventually_isInvertible_ofReal_smul_sub hcpt h₀ ((p + q) / 2)).and
    hmem).exists
  exact ⟨c, hcq, hc⟩

/-- **Locally admissible real shifts.** Let `ι` be compact and `A` a family of operators continuous
within `s` at `t`, such that some shift `c₀ • ι - A t` is invertible. Every nonempty open interval
contains a real `c` such that `(c : 𝕜) • ι - A u` is invertible for all `u` in `s` near `t`. -/
theorem exists_mem_Ioo_eventually_isInvertible_ofReal_smul_sub {X : Type*} [TopologicalSpace X]
    (hcpt : IsCompactOperator ι) {A : X → D →L[𝕜] H} {s : Set X} {t : X}
    (hA : ContinuousWithinAt A s t) (h₀ : (c₀ • ι - A t).IsInvertible) {p q : ℝ} (hpq : p < q) :
    ∃ c ∈ Ioo p q, ∀ᶠ u in 𝓝[s] t, ((c : 𝕜) • ι - A u).IsInvertible := by
  obtain ⟨c, hc, hinv⟩ := exists_mem_Ioo_isInvertible_ofReal_smul_sub hcpt h₀ hpq
  exact ⟨c, hc, (continuousWithinAt_const.sub hA).eventually hinv.eventually_nhds⟩

/-- **Uniformly local admissible real shifts.** Let `ι` be compact and `A` a family of operators
continuous on a compact set `s`, such that every `A t` with `t ∈ s` has some invertible shift
`c₀ • ι - A t`. Given a nonempty open interval, there is a radius `δ > 0` such that for every
`t ∈ s` some real `c` in the interval makes `(c : 𝕜) • ι - A u` invertible for all `u ∈ s` within
`δ` of `t`. -/
theorem exists_pos_forall_exists_mem_Ioo_isInvertible_ofReal_smul_sub {X : Type*}
    [PseudoMetricSpace X] (hcpt : IsCompactOperator ι) {A : X → D →L[𝕜] H} {s : Set X}
    (hs : IsCompact s) (hA : ContinuousOn A s)
    (h₀ : ∀ t ∈ s, ∃ c₀ : 𝕜, (c₀ • ι - A t).IsInvertible) {p q : ℝ} (hpq : p < q) :
    ∃ δ > 0, ∀ t ∈ s, ∃ c ∈ Ioo p q, ∀ u ∈ s, dist u t < δ →
      ((c : 𝕜) • ι - A u).IsInvertible := by
  -- Each time `t` has an admissible shift `c t` on `V t ∩ s` for an open neighbourhood `V t`.
  have key : ∀ t : s, ∃ c ∈ Ioo p q, ∃ V : Set X, IsOpen V ∧ (t : X) ∈ V ∧
      ∀ u ∈ V ∩ s, ((c : 𝕜) • ι - A u).IsInvertible := fun t ↦ by
    obtain ⟨c₀, hc₀⟩ := h₀ t t.property
    obtain ⟨c, hc, hev⟩ :=
      exists_mem_Ioo_eventually_isInvertible_ofReal_smul_sub hcpt (hA t t.property) hc₀ hpq
    obtain ⟨V, hVo, htV, hV⟩ := mem_nhdsWithin.1 hev
    exact ⟨c, hc, V, hVo, htV, hV⟩
  choose c hc V hVo htV hV using key
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hs hVo
    fun t ht ↦ mem_iUnion.2 ⟨⟨t, ht⟩, htV _⟩
  refine ⟨δ, hδ, fun t ht ↦ ?_⟩
  obtain ⟨i, hi⟩ := hball t ht
  exact ⟨c i, hc i, fun u hu hut ↦ hV i u ⟨hi (mem_ball.2 hut), hu⟩⟩

end RCLike

end ContinuousLinearMap
