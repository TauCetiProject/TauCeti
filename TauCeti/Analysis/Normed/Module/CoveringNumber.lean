/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Covering.PackingNumber

import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional

/-!
# Volumetric bounds on covering and packing numbers

In a real normed space `E` of finite dimension `n`, a set of points of a closed ball of radius `r`
any two of which are more than `ε > 0` apart has at most `(1 + 2 r / ε) ^ n` elements. Indeed,
the closed balls of radius `ε / 2` around these points are pairwise disjoint and lie in the closed
ball of radius `r + ε / 2` around the centre
(`Metric.IsSeparated.card_mul_le_measure_cthickening`), and a Haar measure scales the volume of a
ball of radius `ρ` by `ρ ^ n`. Hence the packing number, and with it the covering number, of a
subset of a ball is at most `(1 + 2 r / ε) ^ n`.

In particular the unit sphere of `E` has an `η`-net of at most `(1 + 2 / η) ^ n` points, for every
`η > 0`. Nets of this size on the Euclidean sphere `Sⁿ⁻¹` drive the passage from concentration of
measure at single points to uniform estimates on whole subspaces, as in the proof of Dvoretzky's
theorem on almost Euclidean sections of finite-dimensional normed spaces.

The same bound holds for the image of an abelian group of rank at most `r` under an additive map
`f` to a real vector space with a seminorm `p`, with `r` in place of the dimension: if
`p (f x) ≤ C` for `x ∈ s` and `p (f x - f y) ≥ δ > 0` for distinct `x, y ∈ s`, then `s` has at
most `(1 + 2 C / δ) ^ r` elements. Indeed the real span of the image of `f` has dimension at most
`r`, and its separation quotient for `p` is a normed space. The group need not be finitely
generated, `p` need not be a norm, and the separation `δ` may be attained. A typical instance is a
multiplicative group of finite rank whose logarithmic height is a seminorm of its logarithms.

## Main results

* `TauCeti.card_le_of_isSeparated_of_subset_closedBall`: an `ε`-separated finite subset of a closed
  ball of radius `r` has at most `(1 + 2 r / ε) ^ n` elements.
* `TauCeti.card_le_of_le_dist_of_subset_closedBall`: the same bound when distinct points are at
  distance at least `ε`.
* `TauCeti.packingNumber_le_of_subset_closedBall`,
  `TauCeti.coveringNumber_le_of_subset_closedBall`: the corresponding bounds on the packing and
  covering numbers of a subset of a closed ball.
* `TauCeti.exists_finset_isCover_of_subset_closedBall`: a subset of a closed ball of radius `r`
  has an `ε`-net consisting of at most `(1 + 2 r / ε) ^ n` of its points.
* `TauCeti.exists_finset_isCover_sphere`: the unit sphere has an `η`-net consisting of at most
  `(1 + 2 / η) ^ n` of its points.
* `TauCeti.pow_finrank_le_card_mul_pow_of_isCover_closedBall` and
  `TauCeti.div_pow_finrank_le_externalCoveringNumber_closedBall`: volumetric lower bounds
  `r ^ n ≤ N.card * ε ^ n` and `(r / ε) ^ n ≤ externalCoveringNumber ε (closedBall x r)` on covers
  of a closed ball.
* `Seminorm.card_le_of_rank_le`: a finite subset of an abelian group of rank at most `r`, whose
  image under `f` lies in the `p`-ball of radius `C` and is `δ`-separated for `p`, has at most
  `(1 + 2 C / δ) ^ r` elements.
* `Seminorm.exists_finset_card_le_of_rank_le`: a subset of such a group whose image lies in the
  `p`-ball of radius `C` contains at most `(1 + 2 C / δ) ^ r` points such that every point of the
  subset lies at `p`-distance less than `δ` from one of them.

## References

* R. Vershynin, *High-Dimensional Probability*, §4.2, Proposition 4.2.12 and Corollary 4.2.13.
* The volume argument follows Mathlib's `Besicovitch.card_le_of_separated`, which treats
  `1`-separated subsets of the ball of radius `2`.
-/

public section

open Filter Metric MeasureTheory Module Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {A : Set E} {x : E} {r ε : ℝ≥0}

/-- **Volumetric packing bound.** In a finite-dimensional real normed space, a finite subset of a
closed ball of radius `r` whose points are pairwise more than `ε > 0` apart has at most
`(1 + 2 r / ε) ^ dim E` elements. -/
theorem card_le_of_isSeparated_of_subset_closedBall {s : Finset E} (hε : ε ≠ 0)
    (hs : IsSeparated ε (s : Set E)) (hsx : (s : Set E) ⊆ closedBall x r) :
    (s.card : ℝ) ≤ (1 + 2 * r / ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  set δ : ℝ := ε / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hρ : 0 < r + δ := by positivity
  -- The closed balls of radius `δ = ε / 2` around the points of `s` are disjoint and lie in the
  -- closed ball of radius `r + δ` around `x`.
  have hsub : cthickening δ (s : Set E) ⊆ closedBall x (r + δ) := by
    rw [add_comm]
    exact (cthickening_subset_of_subset δ hsx).trans (cthickening_closedBall hδ.le r.property x).le
  have key : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((r + δ) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1)
        ≤ μ (cthickening δ (s : Set E)) := by
          rw [mul_assoc]
          exact hs.card_mul_le_measure_cthickening subset_rfl fun _ _ ↦
            (μ.addHaar_closedBall _ hδ.le).ge
      _ ≤ μ (closedBall x (r + δ)) := measure_mono hsub
      _ = ENNReal.ofReal ((r + δ) ^ finrank ℝ E) * μ (ball 0 1) :=
          μ.addHaar_closedBall _ hρ.le
  have hcard : (s.card : ℝ) * δ ^ finrank ℝ E ≤ (r + δ) ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
        measure_ball_lt_top.ne).1 key)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_natCast] at h
  have hratio : (1 + 2 * r / ε : ℝ) = (r + δ) / δ := by
    rw [hδ_def]
    field_simp
    ring
  rw [hratio, div_pow, le_div_iff₀ (by positivity)]
  exact hcard

/-- **Volumetric packing bound, attained separation.** In a finite-dimensional real normed space,
a finite subset of a closed ball of radius `C ≥ 0` whose distinct points are at distance at least
`δ > 0` has at most `(1 + 2 C / δ) ^ dim E` elements. -/
theorem card_le_of_le_dist_of_subset_closedBall {s : Finset E} {C δ : ℝ} (hC : 0 ≤ C)
    (hδ : 0 < δ) (hs : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → δ ≤ dist y z)
    (hsx : (s : Set E) ⊆ closedBall x C) :
    (s.card : ℝ) ≤ (1 + 2 * C / δ) ^ finrank ℝ E := by
  -- The strict bound at every separation scale `ε < δ`.
  have hcard (ε : ℝ≥0) (hε0 : ε ≠ 0) (hε : (ε : ℝ) < δ) :
      (s.card : ℝ) ≤ (1 + 2 * C / ε) ^ finrank ℝ E := by
    refine card_le_of_isSeparated_of_subset_closedBall (r := ⟨C, hC⟩) hε0
      (fun y hy z hz hyz ↦ ?_) hsx
    beta_reduce
    rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nndist]
    exact hε.trans_le (hs y hy z hz hyz)
  -- Let `ε` tend to `δ` from below.
  refine ge_of_tendsto (x := 𝓝[<] δ) (f := fun ε ↦ (1 + 2 * C / ε) ^ finrank ℝ E) ?_ ?_
  · exact ((continuousAt_const.add (continuousAt_const.div continuousAt_id hδ.ne')).pow
      _).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT hδ] with ε hε using
      hcard ⟨ε, hε.1.le⟩ (fun h ↦ hε.1.ne' (congrArg NNReal.toReal h)) hε.2

/-- The packing number at scale `ε > 0` of a subset of a closed ball of radius `r` in a
finite-dimensional real normed space is at most `(1 + 2 r / ε) ^ dim E`. -/
theorem packingNumber_le_of_subset_closedBall (hε : ε ≠ 0) (hA : A ⊆ closedBall x r) :
    (packingNumber ε A : ℝ≥0∞) ≤ (1 + 2 * r / ε) ^ finrank ℝ E := by
  -- The bound, as an extended real number, on the size of a finite separated subset of `A`.
  have hB : ENNReal.ofReal ((1 + 2 * r / ε) ^ finrank ℝ E) =
      (1 + 2 * (r : ℝ≥0∞) / ε) ^ finrank ℝ E := by
    have h : (1 + 2 * r / ε : ℝ) = ((1 + 2 * r / ε : ℝ≥0) : ℝ) := by simp
    rw [ENNReal.ofReal_pow (by positivity), h, ENNReal.ofReal_coe_nnreal]
    simp [ENNReal.coe_div hε]
  refine packingNumber_le_of_forall_finset_card_le (hB ▸ ENNReal.ofReal_ne_top)
    fun s hsA hs ↦ ?_
  rw [← hB, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal
    (card_le_of_isSeparated_of_subset_closedBall hε hs (hsA.trans hA))

/-- The covering number at scale `ε > 0` of a subset of a closed ball of radius `r` in a
finite-dimensional real normed space is at most `(1 + 2 r / ε) ^ dim E`. -/
theorem coveringNumber_le_of_subset_closedBall (hε : ε ≠ 0) (hA : A ⊆ closedBall x r) :
    (coveringNumber ε A : ℝ≥0∞) ≤ (1 + 2 * r / ε) ^ finrank ℝ E :=
  (ENat.toENNReal_le.2 (coveringNumber_le_packingNumber ε A)).trans
    (packingNumber_le_of_subset_closedBall hε hA)

/-- A subset `A` of a closed ball of radius `r` in a finite-dimensional real normed space has an
`ε`-net, for `ε > 0`, consisting of at most `(1 + 2 r / ε) ^ dim E` points of `A`. -/
theorem exists_finset_isCover_of_subset_closedBall (hε : ε ≠ 0) (hA : A ⊆ closedBall x r) :
    ∃ N : Finset E, (N : Set E) ⊆ A ∧ IsCover ε A N ∧
      (N.card : ℝ) ≤ (1 + 2 * r / ε) ^ finrank ℝ E := by
  have hA_top : packingNumber ε A ≠ ⊤ :=
    ENat.toENNReal_ne_top.1 <| ne_top_of_le_ne_top
      (ENNReal.pow_ne_top (by simp [ENNReal.div_eq_top, ENNReal.mul_eq_top, hε]))
      (packingNumber_le_of_subset_closedBall hε hA)
  have hNf : (maximalSeparatedSet ε A).Finite := by
    rw [← Set.encard_ne_top_iff, encard_maximalSeparatedSet hA_top]
    exact hA_top
  refine ⟨hNf.toFinset, by simpa using maximalSeparatedSet_subset, by
    simpa using isCover_maximalSeparatedSet hA_top, ?_⟩
  exact card_le_of_isSeparated_of_subset_closedBall hε
    (by simpa using isSeparated_maximalSeparatedSet)
    (by simpa using maximalSeparatedSet_subset.trans hA)

/-- The unit sphere of a finite-dimensional real normed space `E` has an `η`-net, for `η > 0`,
consisting of at most `(1 + 2 / η) ^ dim E` points of the sphere. -/
theorem exists_finset_isCover_sphere {η : ℝ≥0} (hη : η ≠ 0) :
    ∃ N : Finset E, (N : Set E) ⊆ sphere 0 1 ∧ IsCover η (sphere (0 : E) 1) N ∧
      (N.card : ℝ) ≤ (1 + 2 / η) ^ finrank ℝ E := by
  simpa using exists_finset_isCover_of_subset_closedBall (r := 1) hη
    (sphere_subset_closedBall (x := (0 : E)))

/-- **Volumetric covering lower bound.** If a closed ball of radius `r` in a finite-dimensional
real normed space is covered by a finite `ε`-net `N`, then `r ^ dim E ≤ N.card * ε ^ dim E`. -/
theorem pow_finrank_le_card_mul_pow_of_isCover_closedBall {N : Finset E}
    (hcov : IsCover ε (closedBall x r) N) :
    (r : ℝ) ^ finrank ℝ E ≤ N.card * (ε : ℝ) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have key : ENNReal.ofReal ((r : ℝ) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((N.card : ℝ) * (ε : ℝ) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc ENNReal.ofReal ((r : ℝ) ^ finrank ℝ E) * μ (ball 0 1)
        = μ (closedBall x r) := (μ.addHaar_closedBall x r.property).symm
      _ ≤ μ (⋃ y ∈ (N : Set E), closedBall y ε) := measure_mono hcov.subset_iUnion_closedBall
      _ ≤ ∑ y ∈ N, μ (closedBall y ε) := measure_biUnion_finset_le N fun y ↦ closedBall y ε
      _ = ∑ _y ∈ N, ENNReal.ofReal ((ε : ℝ) ^ finrank ℝ E) * μ (ball 0 1) :=
          Finset.sum_congr rfl fun y _ ↦ μ.addHaar_closedBall y ε.property
      _ = ENNReal.ofReal ((N.card : ℝ) * (ε : ℝ) ^ finrank ℝ E) * μ (ball 0 1) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 key)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

/-- **Volumetric external covering lower bound.** At scale `ε`, the external covering number of a
closed ball of radius `r` in a finite-dimensional real normed space is at least
`(r / ε) ^ dim E`. -/
theorem div_pow_finrank_le_externalCoveringNumber_closedBall (x : E) (r ε : ℝ≥0) :
    ((r : ℝ≥0∞) / ε) ^ finrank ℝ E ≤ externalCoveringNumber ε (closedBall x r) := by
  rcases eq_top_or_lt_top (externalCoveringNumber ε (closedBall x r)) with htop | hlt
  · simp [htop]
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
  rw [← hk]
  obtain ⟨N, hNk, hcov⟩ := externalCoveringNumber_le_natCast_iff.mp hk.ge
  have hcard := pow_finrank_le_card_mul_pow_of_isCover_closedBall hcov
  rcases eq_or_ne ε 0 with rfl | hε
  · rcases eq_or_ne (finrank ℝ E) 0 with hd | hd
    · obtain ⟨y, hy, -⟩ := mem_iUnion₂.mp
        (hcov.subset_iUnion_closedBall (mem_closedBall_self r.property))
      have hk1 : 1 ≤ k := (Finset.card_pos.mpr ⟨y, hy⟩).trans_le hNk
      simpa [hd] using hk1
    · have hr0 : (r : ℝ) = 0 :=
        eq_zero_of_pow_eq_zero (le_antisymm (by simpa [zero_pow hd] using hcard) (by positivity))
      simp [NNReal.coe_eq_zero.mp hr0, hd]
  · have hdiv : ((r / ε : ℝ) ^ finrank ℝ E) ≤ k := by
      refine ((div_pow (r : ℝ) (ε : ℝ) (finrank ℝ E)).trans_le ?_).trans (Nat.cast_le.mpr hNk)
      rwa [div_le_iff₀ (by positivity)]
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine (le_of_eq ?_).trans (ENNReal.ofReal_le_ofReal hdiv)
    rw [ENNReal.ofReal_pow (by positivity), ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_div hε]

end TauCeti

namespace Seminorm

variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]

/-- **Packing in an abelian group of finite rank.** Let `f` be an additive map from an abelian
group `M` of rank at most `r` to a real vector space with a seminorm `p`. A finite subset of `M`
whose image lies in the `p`-ball of radius `C ≥ 0` and whose distinct points have images at
`p`-distance at least `δ > 0` has at most `(1 + 2 C / δ) ^ r` elements. -/
theorem card_le_of_rank_le (p : Seminorm ℝ E) (f : M →+ E) {r : ℕ} (hr : Module.rank ℤ M ≤ r)
    {s : Finset M} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) (hsC : ∀ x ∈ s, p (f x) ≤ C)
    (hsδ : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ p (f x - f y)) :
    (s.card : ℝ) ≤ (1 + 2 * C / δ) ^ r := by
  classical
  -- The real span `V` of the image of `f` has dimension at most `r`.
  let N := LinearMap.range f.toIntLinearMap
  let V := Submodule.span ℝ (N : Set E)
  have hVr : Module.rank ℝ V ≤ r := by
    simpa using (Cardinal.lift_le.2 (Submodule.rank_span_le_rank (K := ℝ) N)).trans
      ((lift_rank_range_le f.toIntLinearMap).trans (Cardinal.lift_le.2 hr))
  have : FiniteDimensional ℝ V :=
    Module.rank_lt_aleph0_iff.1 (hVr.trans_lt (Cardinal.natCast_lt_aleph0))
  -- Restrict `p` to `V` and pass to the separation quotient `Q`, a normed space.
  let q : Seminorm ℝ V := p.comp V.subtype
  let _ : SeminormedAddCommGroup V := q.toAddGroupSeminorm.toSeminormedAddCommGroup
  let _ : NormedSpace ℝ V := ⟨fun c v ↦ (map_smul_eq_mul q c v).le⟩
  let Q := SeparationQuotient V
  have hQ : finrank ℝ Q ≤ r :=
    ((LinearMap.finrank_range_le (SeparationQuotient.mkCLM ℝ V).toLinearMap).trans'
      (by rw [LinearMap.range_eq_top.2 SeparationQuotient.surjective_mk, finrank_top])).trans
      (Module.finrank_le_of_rank_le hVr)
  let g : M → Q := fun x ↦ SeparationQuotient.mk (⟨f x, Submodule.subset_span ⟨x, rfl⟩⟩ : V)
  -- The norm on `Q` is `p` by construction.
  have hg (x : M) : ‖g x‖ = p (f x) := rfl
  have hgsub (x y : M) : ‖g x - g y‖ = p (f x - f y) := by
    rw [← SeparationQuotient.mk_sub]
    rfl
  have hinj : Set.InjOn g s := by
    intro x hx y hy hxy
    by_contra hne
    have h := hsδ x hx y hy hne
    rw [← hgsub, hxy, sub_self, norm_zero] at h
    linarith
  have hlim : (s.card : ℝ) ≤ (1 + 2 * C / δ) ^ finrank ℝ Q := by
    rw [← Finset.card_image_of_injOn hinj]
    refine TauCeti.card_le_of_le_dist_of_subset_closedBall (x := 0) hC hδ ?_ ?_
    · simp only [Finset.mem_image]
      rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
      rw [dist_eq_norm, hgsub]
      exact hsδ y hy z hz fun h ↦ hyz (h ▸ rfl)
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simpa [hg] using hsC y hy
  refine hlim.trans (pow_le_pow_right₀ ?_ hQ)
  have := div_nonneg (mul_nonneg zero_le_two hC) hδ.le
  linarith

/-- **Centres in an abelian group of finite rank.** Let `f` be an additive map from an abelian
group `M` of rank at most `r` to a real vector space with a seminorm `p`. If the image of
`A ⊆ M` lies in the `p`-ball of radius `C ≥ 0`, then for every `δ > 0` there are at most
`(1 + 2 C / δ) ^ r` points of `A` such that every point of `A` has image at `p`-distance less
than `δ` from the image of one of them. -/
theorem exists_finset_card_le_of_rank_le (p : Seminorm ℝ E) (f : M →+ E) {r : ℕ}
    (hr : Module.rank ℤ M ≤ r) {A : Set M} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hAC : ∀ x ∈ A, p (f x) ≤ C) :
    ∃ B : Finset M, (B : Set M) ⊆ A ∧ (B.card : ℝ) ≤ (1 + 2 * C / δ) ^ r ∧
      ∀ x ∈ A, ∃ b ∈ B, p (f x - f b) < δ := by
  classical
  -- A `δ`-separated finite subset of `A` of maximal cardinality is the required set.
  let P : Finset M → Prop := fun B ↦
    (B : Set M) ⊆ A ∧ ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ p (f x - f y)
  have hcard (B : Finset M) (hB : P B) : (B.card : ℝ) ≤ (1 + 2 * C / δ) ^ r :=
    card_le_of_rank_le p f hr hC hδ (fun x hx ↦ hAC x (hB.1 hx)) hB.2
  let n := Nat.findGreatest (fun n ↦ ∃ B, P B ∧ B.card = n) ⌊(1 + 2 * C / δ) ^ r⌋₊
  obtain ⟨B, hB, hBn⟩ : ∃ B, P B ∧ B.card = n :=
    Nat.findGreatest_spec (P := fun n ↦ ∃ B, P B ∧ B.card = n) (m := 0) (Nat.zero_le _)
      ⟨∅, by simp [P], rfl⟩
  refine ⟨B, hB.1, hcard B hB, fun x hx ↦ ?_⟩
  by_contra! hfar
  have hxB : x ∉ B := fun h ↦ hδ.not_ge (by simpa using hfar x h)
  have hP : P (insert x B) := by
    refine ⟨by simpa [Set.insert_subset_iff] using ⟨hx, hB.1⟩, ?_⟩
    simp only [Finset.mem_insert]
    rintro y (rfl | hy) z (rfl | hz) hyz
    · exact absurd rfl hyz
    · exact hfar z hz
    · rw [← map_neg_eq_map, neg_sub]
      exact hfar y hy
    · exact hB.2 y hy z hz hyz
  have hle : (insert x B).card ≤ n :=
    Nat.le_findGreatest (Nat.le_floor (hcard _ hP)) ⟨_, hP, rfl⟩
  rw [Finset.card_insert_of_notMem hxB, hBn] at hle
  omega

end Seminorm
