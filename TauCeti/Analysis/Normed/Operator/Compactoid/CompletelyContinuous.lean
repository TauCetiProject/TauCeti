/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compactoid
public import TauCeti.Analysis.Normed.Module.Bases.ModelSpace
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Compactoid

/-!
# Operators with compactoid image are completely continuous

Let `K` be a complete nontrivially normed field and `F` an ultrametric Banach space over `K`. A
continuous linear map `u : E →L[K] F` maps the closed unit ball to a compactoid set exactly when it
is a limit in operator norm of continuous linear maps of finite rank
(`ContinuousLinearMap.hasCompactoidImage_iff_isCompletelyContinuous`). This is the comparison of
Schikhof's compact operators with Serre's completely continuous operators on arbitrary Banach
spaces; neither a discrete valuation nor spherical completeness of `K` is assumed.

The direction from complete continuity to compactoid image is
`ContinuousLinearMap.IsCompletelyContinuous.hasCompactoidImage`. For the converse, a compactoid
set is approximated by the initial pieces of a single sequence
(`TauCeti.IsCompactoidSet.exists_seq_forall_exists_finset`), so the image of `u` lies in the closed
subspace `D` spanned by a sequence. This subspace is of countable type, hence continuously
linearly equivalent to a model space `C₀(I, K)` (`TauCeti.isPotentiallyONable_of_dense_span`).
In such coordinates a compactoid set has uniformly decaying coordinates, so the coordinate
projections onto finite sets of indices approximate `u` in operator norm
(`ContinuousLinearMap.HasCompactoidImage.isCompletelyContinuous_of_zeroAtInfty`). The
argument never projects onto a finite-dimensional subspace of the ambient space `F`, which over a
field that is not spherically complete need not be complemented.

Consequently every topologically compact operator is completely continuous
(`IsCompactOperator.isCompletelyContinuous`), and over a locally compact field the two notions
agree (`ContinuousLinearMap.isCompactOperator_iff_isCompletelyContinuous`). Over `ℂ_p` they
differ: the identity of a line has finite rank but is not a compact operator
(`isCompactOperator_id_iff_locallyCompactSpace`).

## Main results

* `ContinuousLinearMap.HasCompactoidImage.isCompletelyContinuous_of_zeroAtInfty`: a map into a
  model space with compactoid image is completely continuous.
* `ContinuousLinearMap.HasCompactoidImage.isCompletelyContinuous`,
  `ContinuousLinearMap.hasCompactoidImage_iff_isCompletelyContinuous`: the comparison on ultrametric
  Banach spaces.
* `IsCompactOperator.isCompletelyContinuous`,
  `ContinuousLinearMap.isCompactOperator_iff_isCompletelyContinuous`: the comparison with
  topologically compact operators.

## References

* W. H. Schikhof, *Banach spaces over nonarchimedean valued fields*, Topology Proceedings **24**
  (1999), 547–581, §§2.7, 2.15.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§1–3.
* C. Perez-Garcia and W. H. Schikhof, *Locally Convex Spaces over Non-Archimedean Valued
  Fields*, Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010,
  Chapter 2.
-/

public section

open Filter Metric Set Submodule ZeroAtInftyContinuousMap TauCeti
open scoped ZeroAtInfty

variable {K E F : Type*}

namespace ContinuousLinearMap

section ZeroAtInfty

variable [NontriviallyNormedField K] [SeminormedAddCommGroup E] [NormedSpace K E]
  {I : Type*} [TopologicalSpace I] [DiscreteTopology I]

/-- **A map into a model space with compactoid image is completely continuous**: since the
coordinates of a compactoid subset of `C₀(I, K)` decay uniformly, the coordinate projections onto
finite sets of indices approximate the map in operator norm. Neither completeness of `K` nor the
ultrametric inequality is needed. -/
theorem HasCompactoidImage.isCompletelyContinuous_of_zeroAtInfty {u : E →L[K] C₀(I, K)}
    (hu : u.HasCompactoidImage) : u.IsCompletelyContinuous := by
  refine isCompletelyContinuous_iff.2 fun ε hε ↦ ?_
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hc₀ : 0 < ‖c‖ := one_pos.trans hc
  obtain ⟨T, hT⟩ := (hasCompactoidImage_iff.1 hu).exists_finset_forall_norm_lt (div_pos hε hc₀)
  refine ⟨(indicatorCLM K (T : Set I)).comp u,
    (isFiniteRank_indicatorCLM T).comp_right (u : E →ₗ[K] C₀(I, K)), fun x ↦ ?_⟩
  -- On the shell `1 / ‖c‖ ≤ ‖x‖ < 1` the remainder only sees the small coordinates outside `T`.
  have hnorm : ‖u - (indicatorCLM K (T : Set I)).comp u‖ ≤ ε := by
    refine opNorm_le_of_shell one_pos hε.le hc fun x hx₁ hx₂ ↦ ?_
    refine (norm_le (div_pos hε hc₀).le).2 (fun i ↦ ?_) |>.trans ?_
    · by_cases hi : i ∈ T
      · simpa [hi] using (div_pos hε hc₀).le
      · simpa [hi] using (hT _ ⟨x, mem_closedBall_zero_iff.2 hx₂.le, rfl⟩ i hi).le
    · calc ε / ‖c‖ = ε * (1 / ‖c‖) := by ring
        _ ≤ ε * ‖x‖ := by gcongr
  simpa using (u - (indicatorCLM K (T : Set I)).comp u).le_of_opNorm_le hnorm x

end ZeroAtInfty

section Banach

variable [NontriviallyNormedField K] [CompleteSpace K] [SeminormedAddCommGroup E]
  [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]
  [CompleteSpace F]

/-- **Compactoid image implies complete continuity.** Over a complete nontrivially normed field,
a continuous linear map into an ultrametric Banach space that maps the closed unit ball to a
compactoid set is a limit in operator norm of continuous linear maps of finite rank. The image lies
in a closed subspace of countable type, which has a model space `C₀(I, K)` as coordinates. -/
theorem HasCompactoidImage.isCompletelyContinuous {u : E →L[K] F} (hu : u.HasCompactoidImage) :
    u.IsCompletelyContinuous := by
  obtain ⟨v, hv⟩ := (hasCompactoidImage_iff.1 hu).exists_seq_forall_exists_finset
  set D := (span K (range v)).topologicalClosure
  have hvD (n : ℕ) : v n ∈ D := le_topologicalClosure _ (subset_span (mem_range_self n))
  -- The image of the closed unit ball lies in `D`, hence so does the whole range of `u`.
  have hball {x : E} (hx : ‖x‖ ≤ 1) : u x ∈ D := by
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    obtain ⟨t, ht⟩ := hv ε hε
    obtain ⟨a, -, hxa⟩ := ht _ ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩
    exact ⟨_, sum_mem fun i _ ↦ smul_mem _ _ (subset_span (mem_range_self i)),
      by rwa [dist_eq_norm]⟩
  have huD (x : E) : u x ∈ D := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K ‖x‖
    have hc₀ : c ≠ 0 := norm_pos_iff.1 ((norm_nonneg x).trans_lt hc)
    have hx : ‖c⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, norm_inv, inv_mul_le_iff₀ ((norm_nonneg x).trans_lt hc), mul_one]
      exact hc.le
    simpa [smul_smul, mul_inv_cancel₀ hc₀] using D.smul_mem c (hball hx)
  let w : E →L[K] D := u.codRestrict D huD
  let v' : ℕ → D := fun n ↦ ⟨v n, hvD n⟩
  -- `D` is of countable type, so it has a model space as coordinates.
  have hdense : Dense (span K (range v') : Set D) := by
    have hspan : ((↑) '' (span K (range v') : Set D) : Set F) = span K (range v) := by
      -- `D.subtype ∘ v'` is `v` by the definition of `v'`.
      rw [← D.coe_subtype, ← Submodule.map_coe, Submodule.map_span, ← range_comp]
      rfl
    exact Subtype.dense_iff.2 (hspan ▸ subset_refl _)
  obtain ⟨I, _, _, ⟨Φ⟩⟩ :=
    (isPotentiallyONable_def K D).1 (isPotentiallyONable_of_dense_span hdense)
  -- In `D`, the image of the closed unit ball is still approximated by the terms of `v`.
  have hw : IsCompactoidSet K (w '' closedBall 0 1) := by
    refine isCompactoidSet_of_forall_exists_finset v' fun ε hε ↦ ?_
    obtain ⟨t, ht⟩ := hv ε hε
    refine ⟨t, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hxa⟩ := ht _ ⟨x, hx, rfl⟩
    refine ⟨a, ha, ?_⟩
    simpa [w, v', ← Submodule.norm_coe] using hxa
  have hΦw : ((Φ : D →L[K] C₀(I, K)).comp w).HasCompactoidImage := by
    rw [hasCompactoidImage_iff, coe_comp, image_comp]
    exact hw.image _
  convert hΦw.isCompletelyContinuous_of_zeroAtInfty.clm_comp
    (D.subtypeL.comp (Φ.symm : C₀(I, K) →L[K] D)) using 1
  ext x
  simp [w]

/-- **Compactoid image is complete continuity** for maps into an ultrametric Banach space over a
complete nontrivially normed field. -/
theorem hasCompactoidImage_iff_isCompletelyContinuous {u : E →L[K] F} :
    u.HasCompactoidImage ↔ u.IsCompletelyContinuous :=
  ⟨HasCompactoidImage.isCompletelyContinuous, IsCompletelyContinuous.hasCompactoidImage⟩

/-- Over a locally compact nontrivially normed field, such as `ℚ_p`, a continuous linear map into an
ultrametric Banach space is a compact operator exactly when it is completely continuous. -/
theorem isCompactOperator_iff_isCompletelyContinuous [ProperSpace K] {u : E →L[K] F} :
    IsCompactOperator u ↔ u.IsCompletelyContinuous :=
  ⟨fun hu ↦ hu.hasCompactoidImage.isCompletelyContinuous,
    IsCompletelyContinuous.isCompactOperator⟩

end Banach

end ContinuousLinearMap

/-- **Compact operators are completely continuous.** Over a complete nontrivially normed field,
every compact operator into an ultrametric Banach space is a limit in operator norm of continuous
linear maps of finite rank. -/
theorem IsCompactOperator.isCompletelyContinuous [NontriviallyNormedField K] [CompleteSpace K]
    [SeminormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F]
    [IsUltrametricDist F] [CompleteSpace F] {u : E →L[K] F} (hu : IsCompactOperator u) :
    u.IsCompletelyContinuous :=
  hu.hasCompactoidImage.isCompletelyContinuous
