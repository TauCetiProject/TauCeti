/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
public import TauCeti.Analysis.Normed.Operator.ApproximatePointSpectrum
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Spectral projections of self-adjoint Fredholm operators

Let `T` be a self-adjoint operator on a complex Hilbert space `H`. For a set `Ω ⊆ ℝ` whose frontier
avoids the spectrum of `T`, the indicator of `Ω` is continuous on the spectrum, so the continuous
functional calculus gives the spectral projection `cfc (Ω.indicator 1) T` onto the part of the
spectrum in `Ω`. This file proves the facts about these projections from which the spectral flow
of a path of self-adjoint Fredholm operators is built:

* **Spectral gap.** A self-adjoint operator with closed range, such as a self-adjoint Fredholm
  operator, has a gap in its spectrum around `0`: some interval `(-c, c)` meets the spectrum at
  most in `0`. The operator is bounded below on the orthogonal complement of its kernel, and a
  self-adjoint operator bounded below at a real number does not have that number in its spectrum.
* **The kernel projection.** If `0 ∈ Ω`, the spectrum meets `Ω` at most in `0` and the frontier of
  `Ω` avoids the spectrum, then the spectral projection for `Ω` is the orthogonal projection onto
  the kernel of `T`.
* **Stability.** Under the frontier condition, the spectral projection for `Ω` depends
  continuously on the self-adjoint operator, so the rank of its range is locally constant, and it
  is constant along a continuous path of self-adjoint operators over a preconnected parameter space
  as long as the frontier of `Ω` avoids every spectrum along the path.

Combining these, a self-adjoint Fredholm operator `T` has some `a > 0` such that for every
self-adjoint `S` near `T` the numbers `±a` are not in the spectrum of `S` and the spectral
projection of `S` for `[-a, a]` has finite rank equal to the dimension of the kernel of `T`. This
is the local input in Phillips' construction of the spectral flow: the spectral flow of a path
counts, along a partition, the changes of the ranks of the spectral projections for `[0, a]`.

## Main results

* `IsSelfAdjoint.notMem_spectrum_of_forall_mul_norm_le`: a real number at which a self-adjoint
  operator is bounded below is not in its spectrum.
* `IsSelfAdjoint.exists_pos_spectrum_inter_Ioo_subset_of_isClosed_range`: the spectral gap at `0`
  of a self-adjoint operator with closed range, in particular of a self-adjoint Fredholm operator.
* `IsSelfAdjoint.cfc_indicator_eq_starProjection_ker`: the spectral projection for a set meeting the
  spectrum only at `0` is the projection onto the kernel.
* `IsSelfAdjoint.continuousWithinAt_cfc_indicator`: the spectral projection depends continuously on
  the self-adjoint operator when the frontier of the set avoids the spectrum.
* `IsSelfAdjoint.eventually_rank_range_cfc_indicator_eq` and
  `IsPreconnected.rank_range_cfc_indicator_eq`: the rank of the spectral projection is locally
  constant, and constant along paths.
* `IsSelfAdjoint.exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm`: near a
  self-adjoint Fredholm operator the spectral projections for a fixed interval `[-a, a]` have rank
  equal to the dimension of its kernel.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Filter Set Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If a closed set avoids the spectrum of an element of a complete normed algebra, it avoids the
spectra of all nearby elements: the spectrum is upper hemicontinuous. -/
theorem spectrum.eventually_disjoint_of_isClosed {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [ProperSpace 𝕜] {F : Set 𝕜}
    (hF : IsClosed F) {a : A} (h : Disjoint F (spectrum 𝕜 a)) :
    ∀ᶠ b in 𝓝 a, Disjoint F (spectrum 𝕜 b) := by
  have hmem : Fᶜ ∈ 𝓝ˢ (spectrum 𝕜 a) := hF.isOpen_compl.mem_nhdsSet.2 h.subset_compl_left
  filter_upwards [(upperHemicontinuous_spectrum 𝕜 A).upperHemicontinuousAt a _ hmem] with b hb
  exact subset_compl_iff_disjoint_left.mp (subset_of_mem_nhdsSet hb)

namespace IsSelfAdjoint

variable {T : H →L[ℂ] H}

/-! ### The spectral gap at `0` -/

/-- A real number at which a self-adjoint operator is bounded below is not in its spectrum. The
complex spectrum of a self-adjoint operator lies on the real line, so it has empty interior and
consists of approximate eigenvalues. -/
theorem notMem_spectrum_of_forall_mul_norm_le (hT : IsSelfAdjoint T) {r c : ℝ} (hc : 0 < c)
    (h : ∀ x, c * ‖x‖ ≤ ‖T x - (r : ℂ) • x‖) : r ∉ spectrum ℝ T := by
  intro hr
  have hr' : (r : ℂ) ∈ spectrum ℂ T := spectrum.algebraMap_mem ℂ hr
  have hint : interior (spectrum ℂ T) = ∅ := by
    refine eq_empty_of_subset_empty ?_
    calc interior (spectrum ℂ T) ⊆ interior (Complex.im ⁻¹' {0}) :=
          interior_mono fun z hz ↦ by
            rw [mem_preimage, mem_singleton_iff, IsSelfAdjoint.mem_spectrum_eq_re hT hz,
              Complex.ofReal_im]
      _ = ∅ := by rw [Complex.interior_preimage_im, interior_singleton, preimage_empty]
  have hfr : (r : ℂ) ∈ frontier (spectrum ℂ T) := by
    rw [frontier, (spectrum.isClosed T).closure_eq, hint, sdiff_empty]
    exact hr'
  exact (T.notMem_approximatePointSpectrum_iff _).2 ⟨c, hc, h⟩
    (T.frontier_spectrum_subset_approximatePointSpectrum hfr)

/-- A self-adjoint operator bounded below by `c` on the orthogonal complement of its kernel is
bounded below at every real `r` with `|r| ≤ c`, with constant `min (c - |r|) |r|`: write a vector as
the sum of its components in the kernel and in its orthogonal complement. -/
private theorem min_mul_norm_le_norm_sub (hT : IsSelfAdjoint T) {c : ℝ}
    (hc : ∀ x ∈ T.kerᗮ, c * ‖x‖ ≤ ‖T x‖) {r : ℝ} (hrc : |r| ≤ c) (x : H) :
    min (c - |r|) |r| * ‖x‖ ≤ ‖T x - (r : ℂ) • x‖ := by
  set K := T.ker
  set x₀ := K.starProjection x
  set x₁ := x - x₀
  have hx₀ : x₀ ∈ K := K.starProjection_apply_mem x
  have hx₁ : x₁ ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
  have hTx₀ : T x₀ = 0 := hx₀
  set u := T x₁ - (r : ℂ) • x₁
  set w := -((r : ℂ) • x₀)
  have hdecomp : T x - (r : ℂ) • x = u + w := by
    have : x = x₁ + x₀ := (sub_add_cancel x x₀).symm
    conv_lhs => rw [this]
    rw [map_add, hTx₀, smul_add]
    simp only [u, w]
    abel
  -- The range of a self-adjoint operator is orthogonal to its kernel.
  have hTx₁ : T x₁ ∈ Kᗮ := by
    simp only [K, ← ContinuousLinearMap.IsStarNormal.orthogonal_range hT.isStarNormal]
    exact Submodule.le_orthogonal_orthogonal _ (LinearMap.mem_range_self _ x₁)
  have hu : u ∈ Kᗮ := Kᗮ.sub_mem hTx₁ (Kᗮ.smul_mem _ hx₁)
  have hw : w ∈ K := K.neg_mem (K.smul_mem _ hx₀)
  -- Pythagoras for the two components of `T x - r x` and of `x`.
  have hpyth : ‖T x - (r : ℂ) • x‖ * ‖T x - (r : ℂ) • x‖ = ‖u‖ * ‖u‖ + ‖w‖ * ‖w‖ := by
    rw [hdecomp]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u w
      (Submodule.inner_left_of_mem_orthogonal hw hu)
  have hpyth' : ‖x‖ * ‖x‖ = ‖x₁‖ * ‖x₁‖ + ‖x₀‖ * ‖x₀‖ := by
    have : x = x₁ + x₀ := (sub_add_cancel x x₀).symm
    conv_lhs => rw [this]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x₁ x₀
      (Submodule.inner_left_of_mem_orthogonal hx₀ hx₁)
  -- Each component is bounded below.
  set m := min (c - |r|) |r|
  have hm : 0 ≤ m := le_min (sub_nonneg.2 hrc) (abs_nonneg r)
  have hu' : m * ‖x₁‖ ≤ ‖u‖ := by
    have h₁ := hc x₁ hx₁
    have h₂ : ‖T x₁‖ ≤ ‖u‖ + |r| * ‖x₁‖ := by
      calc ‖T x₁‖ = ‖u + (r : ℂ) • x₁‖ := by rw [sub_add_cancel]
        _ ≤ ‖u‖ + ‖(r : ℂ) • x₁‖ := norm_add_le _ _
        _ = ‖u‖ + |r| * ‖x₁‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [min_le_left (c - |r|) |r|, norm_nonneg x₁]
  have hw' : m * ‖x₀‖ ≤ ‖w‖ := by
    rw [norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
  rw [mul_self_le_mul_self_iff (mul_nonneg hm (norm_nonneg x)) (norm_nonneg _), hpyth]
  have hsplit : m * ‖x‖ * (m * ‖x‖) = m * ‖x₁‖ * (m * ‖x₁‖) + m * ‖x₀‖ * (m * ‖x₀‖) := by
    linear_combination m * m * hpyth'
  rw [hsplit]
  exact add_le_add (mul_self_le_mul_self (mul_nonneg hm (norm_nonneg _)) hu')
    (mul_self_le_mul_self (mul_nonneg hm (norm_nonneg _)) hw')

/-- **The spectral gap at `0`.** Some interval `(-c, c)` meets the spectrum of a self-adjoint
operator with closed range, such as a self-adjoint Fredholm operator, at most in `0`. -/
theorem exists_pos_spectrum_inter_Ioo_subset_of_isClosed_range (hT : IsSelfAdjoint T)
    (hR : IsClosed (T.range : Set H)) : ∃ c > 0, spectrum ℝ T ∩ Ioo (-c) c ⊆ {0} := by
  -- The operator is bounded below on the orthogonal complement of its kernel.
  set e := T.orthogonalKerEquivRange hR
  set c := (‖e.symm.toContinuousLinearMap‖ + 1)⁻¹
  have hc : 0 < c := by positivity
  have hbound : ∀ x ∈ T.kerᗮ, c * ‖x‖ ≤ ‖T x‖ := by
    intro x hx
    have h₁ : ‖(⟨x, hx⟩ : T.kerᗮ)‖ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e ⟨x, hx⟩‖ := by
      simpa using e.symm.toContinuousLinearMap.le_opNorm (e ⟨x, hx⟩)
    have h₂ : ‖e ⟨x, hx⟩‖ = ‖T x‖ := by
      rw [← Submodule.norm_coe, ContinuousLinearMap.orthogonalKerEquivRange_apply]
    rw [← Submodule.norm_coe, h₂] at h₁
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (T x)]
  refine ⟨c, hc, fun r ⟨hr, hrc⟩ ↦ ?_⟩
  rw [mem_singleton_iff]
  by_contra hr0
  have hrc' : |r| < c := abs_lt.2 hrc
  refine hT.notMem_spectrum_of_forall_mul_norm_le (lt_min (sub_pos.2 hrc') (abs_pos.2 hr0))
    (min_mul_norm_le_norm_sub hT hbound hrc'.le) hr

/-! ### The spectral projection onto the kernel -/

/-- If `0 ∈ Ω`, the spectrum of a self-adjoint operator `T` meets `Ω` at most in `0`, and the
frontier of `Ω` avoids the spectrum, then the spectral projection of `T` for `Ω` is the orthogonal
projection onto the kernel of `T`. -/
theorem cfc_indicator_eq_starProjection_ker (hT : IsSelfAdjoint T) {Ω : Set ℝ} (h0 : (0 : ℝ) ∈ Ω)
    (hΩ : spectrum ℝ T ∩ Ω ⊆ {0}) (hfr : Disjoint (frontier Ω) (spectrum ℝ T)) :
    cfc (Ω.indicator (1 : ℝ → ℝ)) T = T.ker.starProjection := by
  set f := Ω.indicator (1 : ℝ → ℝ)
  have hf : ContinuousOn f (spectrum ℝ T) := fun x hx ↦
    (continuousOn_const.continuousAt_indicator (hfr.notMem_of_mem_right hx)).continuousWithinAt
  set P := cfc f T
  obtain ⟨_, hPeq⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp (TauCeti.isStarProjection_cfc_indicator T Ω)
  -- `T P = 0`, since `x f(x) = 0` on the spectrum.
  have hTP : T * P = 0 := by
    calc T * P = cfc (fun x ↦ x * f x) T := by rw [cfc_mul (fun x ↦ x) f T, cfc_id' ℝ T]
      _ = cfc (0 : ℝ → ℝ) T := cfc_congr fun x hx ↦ by
          by_cases hxΩ : x ∈ Ω
          · rw [mem_singleton_iff.1 (hΩ ⟨hx, hxΩ⟩), zero_mul, Pi.zero_apply]
          · simp only [f, indicator_of_notMem hxΩ, mul_zero, Pi.zero_apply]
      _ = 0 := cfc_zero ℝ T
  -- `1 - P = g(T) T` with `g(x) = (1 - f(x)) / x`, which is continuous on the spectrum because `0`
  -- is either not in the spectrum or isolated in it.
  set g : ℝ → ℝ := fun x ↦ (1 - f x) / x
  have hg : ContinuousOn g (spectrum ℝ T) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      have hint : (0 : ℝ) ∈ interior Ω := by
        by_contra hni
        exact hfr.notMem_of_mem_left ⟨subset_closure h0, hni⟩ hx
      refine (continuousWithinAt_const : ContinuousWithinAt (fun _ ↦ g 0) _ _).congr_of_eventuallyEq
        ?_ rfl
      filter_upwards [nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.1 hint), self_mem_nhdsWithin]
        with y hy hys
      rw [mem_singleton_iff.1 (hΩ ⟨hys, hy⟩)]
    · exact (continuousWithinAt_const.sub (hf x hx)).div continuousWithinAt_id hx0
  have hsub : 1 - P = cfc g T * T := by
    calc 1 - P = cfc (fun x ↦ 1 - f x) T := by rw [cfc_sub (fun _ ↦ 1) f T, cfc_const_one ℝ T]
      _ = cfc (fun x ↦ g x * x) T := cfc_congr fun x hx ↦ by
          by_cases hx0 : x = 0
          · simp [hx0, f, h0]
          · exact (div_mul_cancel₀ _ hx0).symm
      _ = cfc g T * T := by rw [cfc_mul g (fun x ↦ x) T, cfc_id' ℝ T]
  -- Hence the range of `P` is the kernel of `T`.
  have hrange : P.range = T.ker := by
    refine le_antisymm ?_ fun v hv ↦ ⟨v, ?_⟩
    · rintro _ ⟨v, rfl⟩
      exact congr($hTP v)
    · have hTv : T v = 0 := hv
      have h : v - P v = 0 := by simpa [hTv] using congr($hsub v)
      exact (sub_eq_zero.1 h).symm
  exact hPeq.trans (Submodule.starProjection_inj.2 hrange)

/-! ### Continuity and rank of spectral projections -/

/-- The spectral projection for a set `Ω` depends continuously on the self-adjoint operator at an
operator whose spectrum avoids the frontier of `Ω`. -/
theorem continuousWithinAt_cfc_indicator (hT : IsSelfAdjoint T) {Ω : Set ℝ}
    (hΩ : Disjoint (frontier Ω) (spectrum ℝ T)) :
    ContinuousWithinAt (cfc (Ω.indicator (1 : ℝ → ℝ))) {S | IsSelfAdjoint S} T := by
  set t := {S : H →L[ℂ] H | IsSelfAdjoint S ∧ spectrum ℝ S ⊆ (frontier Ω)ᶜ}
  have hcont : ContinuousOn (cfc (Ω.indicator (1 : ℝ → ℝ))) t :=
    ContinuousOn.cfc_of_mem_nhdsSet (a := id) _
      (isClosed_frontier.isOpen_compl.mem_nhdsSet.2 (iUnion₂_subset fun S hS ↦ hS.2))
      continuousOn_id (fun S hS ↦ hS.1)
      fun x hx ↦ (continuousOn_const.continuousAt_indicator hx).continuousWithinAt
  refine (hcont.continuousWithinAt ⟨hT, hΩ.subset_compl_left⟩).mono_of_mem_nhdsWithin ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (spectrum.eventually_disjoint_of_isClosed isClosed_frontier hΩ)]
    with S hS hS'
  exact ⟨hS, hS'.subset_compl_left⟩

/-- The rank of the spectral projection for a set `Ω` is locally constant on the self-adjoint
operators whose spectrum avoids the frontier of `Ω`: nearby spectral projections are at distance
less than `1`. -/
theorem eventually_rank_range_cfc_indicator_eq (hT : IsSelfAdjoint T) {Ω : Set ℝ}
    (hΩ : Disjoint (frontier Ω) (spectrum ℝ T)) :
    ∀ᶠ S in 𝓝[{S | IsSelfAdjoint S}] T,
      Module.rank ℂ (cfc (Ω.indicator (1 : ℝ → ℝ)) S).range =
        Module.rank ℂ (cfc (Ω.indicator (1 : ℝ → ℝ)) T).range := by
  filter_upwards [hT.continuousWithinAt_cfc_indicator hΩ (Metric.ball_mem_nhds _ one_pos)]
    with S hS
  obtain ⟨_, hPS⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp (TauCeti.isStarProjection_cfc_indicator S Ω)
  obtain ⟨_, hPT⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp (TauCeti.isStarProjection_cfc_indicator T Ω)
  refine Submodule.rank_eq_of_projectionGap_lt_one _ _ ?_
  rw [Submodule.projectionGap_def, ← hPS, ← hPT, ← dist_eq_norm]
  exact hS

end IsSelfAdjoint

/-- The rank of the spectral projection for a set `Ω` is constant along a continuous path of
self-adjoint operators over a preconnected parameter set, as long as no spectrum along the path
meets the frontier of `Ω`. -/
theorem IsPreconnected.rank_range_cfc_indicator_eq {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s) {A : X → H →L[ℂ] H} (hA : ContinuousOn A s)
    (hsa : ∀ x ∈ s, IsSelfAdjoint (A x)) {Ω : Set ℝ}
    (hΩ : ∀ x ∈ s, Disjoint (frontier Ω) (spectrum ℝ (A x))) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) :
    Module.rank ℂ (cfc (Ω.indicator (1 : ℝ → ℝ)) (A x)).range =
      Module.rank ℂ (cfc (Ω.indicator (1 : ℝ → ℝ)) (A y)).range := by
  have := isPreconnected_iff_preconnectedSpace.mp hs
  let g : s → Cardinal := fun z ↦ Module.rank ℂ (cfc (Ω.indicator (1 : ℝ → ℝ)) (A z)).range
  have hg : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    have hz : Tendsto (fun w : s ↦ A w) (𝓝 z) (𝓝[{S | IsSelfAdjoint S}] (A z)) :=
      tendsto_nhdsWithin_iff.2 ⟨(continuousOn_iff_continuous_domRestrict.1 hA).tendsto z,
        Eventually.of_forall fun w ↦ hsa w w.2⟩
    exact hz.eventually ((hsa z z.2).eventually_rank_range_cfc_indicator_eq (hΩ z z.2))
  exact hg.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩

namespace IsSelfAdjoint

variable {T : H →L[ℂ] H}

/-- **Finite spectral projections near a self-adjoint Fredholm operator.** For a self-adjoint
Fredholm operator `T` there is `a > 0` such that every self-adjoint `S` near `T` has neither `-a`
nor `a` in its spectrum, and its spectral projection for `[-a, a]` has finite rank equal to the
dimension of the kernel of `T`. -/
theorem exists_pos_eventually_finrank_range_cfc_indicator_Icc_eq_of_isFredholm
    (hT : IsSelfAdjoint T) (hF : T.IsFredholm) :
    ∃ a > 0, ∀ᶠ S in 𝓝[{S | IsSelfAdjoint S}] T,
      -a ∉ spectrum ℝ S ∧ a ∉ spectrum ℝ S ∧
        FiniteDimensional ℂ (cfc ((Icc (-a) a).indicator (1 : ℝ → ℝ)) S).range ∧
        Module.finrank ℂ (cfc ((Icc (-a) a).indicator (1 : ℝ → ℝ)) S).range =
          Module.finrank ℂ T.ker := by
  obtain ⟨c, hc, hgap⟩ :=
    hT.exists_pos_spectrum_inter_Ioo_subset_of_isClosed_range hF.isClosed_range
  refine ⟨c / 2, by positivity, ?_⟩
  have hfr : frontier (Icc (-(c / 2)) (c / 2)) = {-(c / 2), c / 2} := frontier_Icc (by linarith)
  have hsub : spectrum ℝ T ∩ Icc (-(c / 2)) (c / 2) ⊆ {0} := fun r hr ↦
    hgap ⟨hr.1, by linarith [hr.2.1], by linarith [hr.2.2]⟩
  have hdisj : Disjoint (frontier (Icc (-(c / 2)) (c / 2))) (spectrum ℝ T) := by
    rw [hfr, Set.disjoint_left]
    intro r hr hrs
    have hr0 : r ≠ 0 := by
      rcases hr with rfl | rfl <;> simp [hc.ne']
    refine hr0 (hsub ⟨hrs, ?_⟩)
    rcases hr with rfl | rfl <;> constructor <;> linarith
  have hker := hT.cfc_indicator_eq_starProjection_ker
    (by rw [mem_Icc]; constructor <;> linarith) hsub hdisj
  have : FiniteDimensional ℂ T.ker := hF.finite_ker
  filter_upwards [hT.eventually_rank_range_cfc_indicator_eq hdisj,
    nhdsWithin_le_nhds (spectrum.eventually_disjoint_of_isClosed isClosed_frontier hdisj)]
    with S hrank hS
  rw [hker, Submodule.range_starProjection] at hrank
  rw [hfr] at hS
  refine ⟨hS.notMem_of_mem_left (by simp), hS.notMem_of_mem_left (by simp), ?_,
    congr_arg Cardinal.toNat hrank⟩
  exact Module.rank_lt_aleph0_iff.1 (hrank ▸ Module.rank_lt_aleph0 ℂ T.ker)

end IsSelfAdjoint
