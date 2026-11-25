/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import TauCeti.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Analysis.Normed.Group.CompatibleNorm

/-!
# The translation-invariant metric of a countable family of seminorms

Let `p : ℕ → Seminorm 𝕜 E` be a countable family of seminorms. The function
`x ↦ ∑' n, 2⁻¹ ^ n * min 1 (p n x)` is a group seminorm on `E`, the *Fréchet group seminorm*
`SeminormFamily.frechetSeminorm p`. It is not homogeneous, but it is subadditive and symmetric,
so `(x, y) ↦ p.frechetSeminorm (x - y)` is a translation-invariant pseudometric bounded by `2`.

When the topology of `E` is induced by `p` (`WithSeminorms p`) and `E` carries its additive
uniform structure, the small sublevel sets of `p.frechetSeminorm` form a basis of the
neighbourhoods of `0` (`WithSeminorms.hasBasis_frechetSeminorm_lt`), and the corresponding
entourages form a basis of the uniformity. Hence `p.frechetSeminorm` is the norm of a seminormed
additive group structure on `E` whose uniformity *is* the given one
(`WithSeminorms.toSeminormedAddCommGroup`), and a normed one when `E` is T₀
(`WithSeminorms.toNormedAddCommGroup`). Mathlib's `WithSeminorms.firstCountableTopology` and
`UniformSpace.pseudoMetricSpace` already give some compatible pseudometric, but not a
translation-invariant one or an explicit formula in terms of the seminorms.

Since the uniformity of `WithSeminorms.toSeminormedAddCommGroup` is the given one, the
completeness criterion `WithSeminorms.completeSpace_iff` (a countable family: the space is
complete if and only if every sequence that is Cauchy for each seminorm converges) is equally
the completeness criterion of the Fréchet metric.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., McGraw-Hill (1991), §1.38, which builds a
  compatible translation-invariant metric from a countable separating family of seminorms by
  an equivalent formula.
-/

public section

noncomputable section

open Filter Topology Uniformity

namespace SeminormFamily

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable (p : SeminormFamily 𝕜 E ℕ)

/-- The terms `2⁻¹ ^ n * min 1 (p n x)` are dominated by the geometric series `2⁻¹ ^ n`. -/
private theorem summable_frechetTerm (x : E) :
    Summable fun n ↦ (2⁻¹ : ℝ) ^ n * min 1 (p n x) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).of_nonneg_of_le
    (fun n ↦ by positivity) fun n ↦ mul_le_of_le_one_right (by positivity) (min_le_left _ _)

/-- The **Fréchet group seminorm** `x ↦ ∑' n, 2⁻¹ ^ n * min 1 (p n x)` of a countable family of
seminorms. Each term is truncated at `1` and weighted by `2⁻¹ ^ n`, so the series converges and
is bounded by `2`. It is subadditive and invariant under negation, but not homogeneous. -/
def frechetSeminorm : AddGroupSeminorm E where
  toFun x := ∑' n, (2⁻¹ : ℝ) ^ n * min 1 (p n x)
  map_zero' := by simp
  add_le' x y := by
    rw [← (summable_frechetTerm p x).tsum_add (summable_frechetTerm p y)]
    refine (summable_frechetTerm p (x + y)).tsum_le_tsum (fun n ↦ ?_)
      ((summable_frechetTerm p x).add (summable_frechetTerm p y))
    rw [← mul_add]
    gcongr
    -- Truncation at `1` preserves subadditivity of nonnegative quantities.
    have := map_add_le_add (p n) x y
    have := apply_nonneg (p n) x
    have := apply_nonneg (p n) y
    grind
  neg' x := by simp

theorem frechetSeminorm_apply (x : E) :
    p.frechetSeminorm x = ∑' n, (2⁻¹ : ℝ) ^ n * min 1 (p n x) :=
  (rfl)

/-- The Fréchet group seminorm is bounded by `2`. -/
theorem frechetSeminorm_le_two (x : E) : p.frechetSeminorm x ≤ 2 := by
  rw [frechetSeminorm_apply]
  refine le_trans ?_ tsum_geometric_inv_two.le
  exact (summable_frechetTerm p x).tsum_le_tsum
    (fun n ↦ mul_le_of_le_one_right (by positivity) (min_le_left _ _))
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- Each weighted truncated seminorm is bounded by the Fréchet group seminorm. -/
theorem pow_mul_min_le_frechetSeminorm (x : E) (n : ℕ) :
    (2⁻¹ : ℝ) ^ n * min 1 (p n x) ≤ p.frechetSeminorm x :=
  (summable_frechetTerm p x).le_tsum n fun m _ ↦ by positivity

/-- A bound on the Fréchet group seminorm controls each seminorm of the family: if
`p.frechetSeminorm x < 2⁻¹ ^ n * min 1 ε`, then `p n x < ε`. -/
theorem lt_of_frechetSeminorm_lt {x : E} {n : ℕ} {ε : ℝ}
    (h : p.frechetSeminorm x < 2⁻¹ ^ n * min 1 ε) : p n x < ε := by
  have hmin : min 1 (p n x) < min 1 ε :=
    lt_of_mul_lt_mul_left ((p.pow_mul_min_le_frechetSeminorm x n).trans_lt h) (by positivity)
  by_contra! hle
  exact hmin.not_ge (min_le_min_left 1 hle)

/-- Finitely many seminorms of the family control the Fréchet group seminorm up to the tail of
the geometric series: `p.frechetSeminorm x ≤ 2 * (range N).sup p x + 2 * 2⁻¹ ^ N`. -/
theorem frechetSeminorm_le (x : E) (N : ℕ) :
    p.frechetSeminorm x ≤ 2 * (Finset.range N).sup p x + 2 * 2⁻¹ ^ N := by
  set s := (Finset.range N).sup p x
  have hs : 0 ≤ s := apply_nonneg _ _
  have hgeom : Summable fun n : ℕ ↦ (2⁻¹ : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have htail : Summable fun n : ℕ ↦ if N ≤ n then (2⁻¹ : ℝ) ^ n else 0 :=
    hgeom.of_nonneg_of_le (fun n ↦ by split_ifs <;> positivity)
      fun n ↦ by split_ifs <;> simp
  calc p.frechetSeminorm x
      ≤ ∑' n, ((2⁻¹ : ℝ) ^ n * s + if N ≤ n then (2⁻¹ : ℝ) ^ n else 0) := by
        refine (summable_frechetTerm p x).tsum_le_tsum (fun n ↦ ?_) ((hgeom.mul_right s).add htail)
        split_ifs with hn
        · nlinarith [min_le_left 1 (p n x), pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n]
        · have hle : p n x ≤ s :=
            Seminorm.le_finset_sup_apply (Finset.mem_range.2 (not_le.1 hn))
          nlinarith [min_le_right 1 (p n x), pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) n]
    _ = 2 * s + 2 * 2⁻¹ ^ N := by
        rw [(hgeom.mul_right s).tsum_add htail, tsum_mul_right, tsum_geometric_inv_two,
          tsum_geometric_inv_two_ge]

/-- The Fréchet group seminorm vanishes exactly where every seminorm of the family vanishes. -/
theorem frechetSeminorm_eq_zero_iff {x : E} : p.frechetSeminorm x = 0 ↔ ∀ n, p n x = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ by simp [frechetSeminorm_apply, h]⟩
  have hle := p.pow_mul_min_le_frechetSeminorm x n
  rw [h] at hle
  have hmin : min 1 (p n x) ≤ 0 := nonpos_of_mul_nonpos_right hle (by positivity)
  exact le_antisymm ((min_le_iff.1 hmin).resolve_left (by norm_num)) (apply_nonneg _ _)

end SeminormFamily

namespace WithSeminorms

section FrechetMetric

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  {p : SeminormFamily 𝕜 E ℕ}

/-- If the topology is induced by a countable family of seminorms `p`, the sublevel sets
`{x | p.frechetSeminorm x < ε}`, `0 < ε`, form a basis of the neighbourhoods of `0`. -/
theorem hasBasis_frechetSeminorm_lt [TopologicalSpace E] (hp : WithSeminorms p) :
    (𝓝 (0 : E)).HasBasis (fun ε : ℝ ↦ 0 < ε) fun ε ↦ {x | p.frechetSeminorm x < ε} := by
  refine hp.hasBasis_zero_ball.to_hasBasis ?_ fun ε hε ↦ ?_
  · rintro ⟨s, r⟩ (hr : 0 < r)
    -- `s ⊆ range N`, and a Fréchet bound `2⁻¹ ^ N * min 1 r` controls each `p n`, `n < N`.
    obtain ⟨N, hN⟩ := s.exists_nat_subset_range
    refine ⟨2⁻¹ ^ N * min 1 r, by positivity, fun x (hx : p.frechetSeminorm x < _) ↦ ?_⟩
    rw [Seminorm.mem_ball_zero]
    refine Seminorm.finset_sup_apply_lt hr fun n hn ↦ p.lt_of_frechetSeminorm_lt (hx.trans_le ?_)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Finset.mem_range.1 (hN hn)).le) (by positivity)
  · -- The tail of the geometric series beyond `N` is less than `ε / 2`.
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε / 4)
      (by norm_num : (2⁻¹ : ℝ) < 1)
    refine ⟨(Finset.range N, ε / 4), by positivity, fun x hx ↦ ?_⟩
    rw [Seminorm.mem_ball_zero] at hx
    exact (p.frechetSeminorm_le x N).trans_lt (by linarith)

/-- If the topology of a uniform additive group is induced by a countable family of seminorms
`p`, the entourages `{(x, y) | p.frechetSeminorm (x - y) < ε}`, `0 < ε`, form a basis of the
uniformity. -/
theorem hasBasis_uniformity_frechetSeminorm [UniformSpace E] [IsUniformAddGroup E]
    (hp : WithSeminorms p) :
    (𝓤 E).HasBasis (fun ε : ℝ ↦ 0 < ε) fun ε ↦
      {xy : E × E | p.frechetSeminorm (xy.1 - xy.2) < ε} := by
  rw [uniformity_eq_comap_nhds_zero]
  convert hp.hasBasis_frechetSeminorm_lt.comap (fun xy : E × E ↦ xy.2 - xy.1) using 3 with ε
  ext xy
  simp [map_sub_rev]

/-- If the topology of a uniform additive group `E` is induced by a countable family of
seminorms `p`, the uniformity of `E` is the uniformity of the pseudometric
`(x, y) ↦ p.frechetSeminorm (-x + y)` of `AddGroupSeminorm.toSeminormedAddCommGroup`. -/
theorem uniformity_eq_frechetSeminorm [UniformSpace E] [IsUniformAddGroup E]
    (hp : WithSeminorms p) :
    𝓤 E = @uniformity E p.frechetSeminorm.toSeminormedAddCommGroup.toUniformSpace := by
  refine hp.hasBasis_uniformity_frechetSeminorm.eq_of_same_basis ?_
  let := p.frechetSeminorm.toSeminormedAddCommGroup
  convert Metric.uniformity_basis_dist (α := E) using 3 with ε
  ext xy
  -- The norm of `AddGroupSeminorm.toSeminormedAddCommGroup` is the seminorm itself.
  rw [dist_eq_norm]
  rfl

/-- The **Fréchet metric** of a countable family of seminorms inducing the topology of a uniform
additive group `E`: the seminormed additive group structure on `E` with norm
`p.frechetSeminorm`, hence distance `p.frechetSeminorm (x - y)`. Its uniformity is
definitionally the given one, so it is compatible with the topology and the uniform structure
of `E`. This is not an instance, since it depends on the choice of `p`. -/
abbrev toSeminormedAddCommGroup [UniformSpace E] [IsUniformAddGroup E] (hp : WithSeminorms p) :
    SeminormedAddCommGroup E :=
  p.frechetSeminorm.toSeminormedAddCommGroupOfUniformity (uniformity_eq_frechetSeminorm hp)

variable [UniformSpace E] [IsUniformAddGroup E] (hp : WithSeminorms p)

/-- The norm of the Fréchet metric is the Fréchet group seminorm. -/
theorem toSeminormedAddCommGroup_norm_eq (x : E) :
    @norm E hp.toSeminormedAddCommGroup.toNorm x = p.frechetSeminorm x :=
  (rfl)

/-- The distance of the Fréchet metric is `p.frechetSeminorm (x - y)`. -/
theorem toSeminormedAddCommGroup_dist_eq (x y : E) :
    @dist E hp.toSeminormedAddCommGroup.toDist x y = p.frechetSeminorm (x - y) :=
  @dist_eq_norm E hp.toSeminormedAddCommGroup x y

/-- The uniform structure of the Fréchet metric is the given uniform structure of `E`. -/
theorem toSeminormedAddCommGroup_toUniformSpace :
    @PseudoMetricSpace.toUniformSpace E hp.toSeminormedAddCommGroup.toPseudoMetricSpace =
      ‹UniformSpace E› :=
  (rfl)

/-- The **Fréchet metric** of a countable family of seminorms inducing the topology of a T₀
uniform additive group `E` is a metric: the normed additive group structure on `E` with norm
`p.frechetSeminorm`, whose uniformity is definitionally the given one. -/
abbrev toNormedAddCommGroup [T0Space E] : NormedAddCommGroup E :=
  letI := hp.toSeminormedAddCommGroup
  NormedAddCommGroup.ofSeparation fun x hx ↦ by
    have : Inseparable x 0 := Metric.inseparable_iff.2 (by rwa [dist_zero_right])
    exact this.eq

/-- The norm of the normed Fréchet metric is the Fréchet group seminorm. -/
theorem toNormedAddCommGroup_norm_eq [T0Space E] (x : E) :
    @norm E hp.toNormedAddCommGroup.toNorm x = p.frechetSeminorm x :=
  (rfl)

/-- The distance of the normed Fréchet metric is `p.frechetSeminorm (x - y)`. -/
theorem toNormedAddCommGroup_dist_eq [T0Space E] (x y : E) :
    @dist E hp.toNormedAddCommGroup.toDist x y = p.frechetSeminorm (x - y) :=
  @dist_eq_norm E hp.toNormedAddCommGroup.toSeminormedAddCommGroup x y

/-- The uniform structure of the normed Fréchet metric is the given uniform structure of `E`. -/
theorem toNormedAddCommGroup_toUniformSpace [T0Space E] :
    @PseudoMetricSpace.toUniformSpace E
        hp.toNormedAddCommGroup.toMetricSpace.toPseudoMetricSpace =
      ‹UniformSpace E› :=
  (rfl)

end FrechetMetric

end WithSeminorms
