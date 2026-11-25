/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.Monotone
public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness

/-!
# Von Neumann's alternating projection theorem

For closed subspaces `K` and `L` of a complete real or complex inner product space, with
orthogonal projections `p` and `q`, the alternating products converge in the strong operator
topology to the orthogonal projection onto `K ⊓ L`:
`(p q p)ⁿ → P_(K ⊓ L)` (`Submodule.tendsto_toPointwiseConvergenceCLM_starProjection_mul_mul_pow`)
and `(p q)ⁿ → P_(K ⊓ L)` (`Submodule.tendsto_toPointwiseConvergenceCLM_starProjection_mul_pow`).
In the projection lattice this expresses the meet `p ⊓ q` as a strong limit of products. For
two lines in `ℝ²` at angle `θ` one has `p q p = cos² θ • p`, so the rate of convergence depends
on the angle between the subspaces.

Both statements follow from the strong convergence of the powers of a positive contraction
`0 ≤ T ≤ 1` to the orthogonal projection onto its fixed vectors, the kernel of `1 - T`
(`ContinuousLinearMap.tendsto_toPointwiseConvergenceCLM_pow`). The powers decrease in the
Loewner order, so Vigier's theorem gives a strong limit, which is identified by testing it
against the fixed vectors.

## References

* J. von Neumann, *Functional Operators, Vol. II: The Geometry of Orthogonal Spaces*,
  Annals of Mathematics Studies 22 (1950), Theorem 13.7.
-/

public section

open Filter Topology Set
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The powers of a positive contraction converge strongly to the orthogonal projection onto any
closed subspace consisting exactly of its fixed vectors. -/
private theorem tendsto_pow_of_forall_mem_iff {T : E →L[𝕜] E} (h0 : 0 ≤ T) (h1 : T ≤ 1)
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (hK : ∀ v, v ∈ K ↔ T v = v) :
    Tendsto (fun n => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (T ^ n)) atTop
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E K.starProjection)) := by
  have hsa : IsSelfAdjoint T := (nonneg_iff_isPositive.mp h0).isSelfAdjoint
  set P := ⨅ n, T ^ n
  have hlim : ∀ x, Tendsto (fun n => (T ^ n) x) atTop (𝓝 (P x)) := by
    have h := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp
      (tendsto_toPointwiseConvergenceCLM_ciInf (fun _ _ => pow_le_pow_of_le_one h0 h1)
        ⟨0, by
          rintro _ ⟨n, rfl⟩
          exact nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp h0).pow n)⟩)
    simp only [toPointwiseConvergenceCLM_apply] at h
    exact h
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  simp only [toPointwiseConvergenceCLM_apply]
  intro x
  -- The strong limit `P x` is fixed by `T` and has the same inner products with fixed vectors
  -- as `x`, which characterises the orthogonal projection of `x` onto `K`.
  have hP : K.starProjection x = P x := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · refine (hK _).mpr (tendsto_nhds_unique ((T.continuous.tendsto _).comp (hlim x)) ?_)
      exact ((hlim x).comp (tendsto_add_atTop_nat 1)).congr fun n => by
        simp [pow_succ']
    · have hpow : ∀ n, ⟪(T ^ n) x, w⟫_𝕜 = ⟪x, w⟫_𝕜 := fun n => by
        calc ⟪(T ^ n) x, w⟫_𝕜 = ⟪x, (T ^ n) w⟫_𝕜 := (hsa.pow n).isSymmetric x w
          _ = ⟪x, w⟫_𝕜 := by rw [pow_apply_eq_iterate, Function.iterate_fixed ((hK w).mp hw)]
      rw [inner_sub_left, sub_eq_zero]
      exact (tendsto_nhds_unique ((hlim x).inner tendsto_const_nhds)
        (by simp [hpow])).symm
  exact hP ▸ hlim x

/-- The powers of a positive contraction `0 ≤ T ≤ 1` converge in the strong operator topology to
the orthogonal projection onto the fixed vectors of `T`, the kernel of `1 - T`. -/
theorem tendsto_toPointwiseConvergenceCLM_pow {T : E →L[𝕜] E} (h0 : 0 ≤ T) (h1 : T ≤ 1) :
    Tendsto (fun n => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (T ^ n)) atTop
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E
        (1 - T).ker.starProjection)) :=
  tendsto_pow_of_forall_mem_iff h0 h1 _ fun v => by
    simp [sub_eq_zero, eq_comm (a := T v)]

end ContinuousLinearMap

namespace Submodule

open ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]

/-- **Von Neumann's alternating projection theorem**, symmetric form: if `p` and `q` are the
orthogonal projections onto closed subspaces `K` and `L`, then `(p q p)ⁿ` converges in the strong
operator topology to the orthogonal projection onto `K ⊓ L`. -/
theorem tendsto_toPointwiseConvergenceCLM_starProjection_mul_mul_pow :
    Tendsto (fun n => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E
      ((K.starProjection * L.starProjection * K.starProjection) ^ n)) atTop
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (K ⊓ L).starProjection)) := by
  have hp : IsStarProjection K.starProjection := isStarProjection_starProjection
  have hq : IsStarProjection L.starProjection := isStarProjection_starProjection
  have hconj {A : E →L[𝕜] E} (hA : A.IsPositive) :
      (K.starProjection * A * K.starProjection).IsPositive :=
    hA.conj_starProjection K
  -- `0 ≤ p q p ≤ 1`, since `1 - p q p = (1 - p) + p (1 - q) p`.
  have h0 : 0 ≤ K.starProjection * L.starProjection * K.starProjection :=
    nonneg_iff_isPositive.mpr (hconj (IsPositive.of_isStarProjection hq))
  have h1 : K.starProjection * L.starProjection * K.starProjection ≤ 1 := by
    have h : 1 - K.starProjection * L.starProjection * K.starProjection =
        (1 - K.starProjection) + K.starProjection * (1 - L.starProjection) * K.starProjection := by
      rw [mul_sub, sub_mul, mul_one, hp.isIdempotentElem.eq]
      abel
    rw [ContinuousLinearMap.le_def, h]
    exact (IsPositive.of_isStarProjection hp.one_sub).add
      (hconj (IsPositive.of_isStarProjection hq.one_sub))
  refine tendsto_pow_of_forall_mem_iff h0 h1 _ fun v => ⟨fun hv => ?_, fun hv => ?_⟩
  · rw [mem_inf, ← starProjection_eq_self_iff, ← starProjection_eq_self_iff] at hv
    simp [hv.1, hv.2]
  -- A fixed vector `v = p (q (p v))` lies in `K`, so `v = p (q v)` and `‖q v‖ = ‖v‖`, which puts
  -- it in `L`.
  simp only [_root_.mul_apply_eq_comp] at hv
  have hK : v ∈ K := hv ▸ K.starProjection_apply_mem _
  rw [starProjection_eq_self_iff.mpr hK] at hv
  refine mem_inf.mpr ⟨hK, (L.mem_iff_norm_starProjection v).mpr (le_antisymm
    (L.norm_starProjection_apply_le v) ?_)⟩
  calc ‖v‖ = ‖K.starProjection (L.starProjection v)‖ := by rw [hv]
    _ ≤ ‖L.starProjection v‖ := K.norm_starProjection_apply_le _

/-- **Von Neumann's alternating projection theorem**: if `p` and `q` are the orthogonal
projections onto closed subspaces `K` and `L`, then `(p q)ⁿ` converges in the strong operator
topology to the orthogonal projection onto `K ⊓ L`. -/
theorem tendsto_toPointwiseConvergenceCLM_starProjection_mul_pow :
    Tendsto (fun n => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E
      ((K.starProjection * L.starProjection) ^ n)) atTop
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E E (K ⊓ L).starProjection)) := by
  have hpp := (isStarProjection_starProjection (U := K)).isIdempotentElem.eq
  -- `(p q)ⁿ⁺¹ = (p q p)ⁿ (p q)`.
  have hpow : ∀ n, (K.starProjection * L.starProjection) ^ (n + 1) =
      (K.starProjection * L.starProjection * K.starProjection) ^ n *
        (K.starProjection * L.starProjection) := fun n => by
    rw [mul_pow_mul, ← mul_assoc K.starProjection K.starProjection, hpp, ← pow_succ']
  -- The projection onto `K ⊓ L` absorbs `p` and `q` on the right.
  have hR : ∀ x, (K ⊓ L).starProjection (K.starProjection (L.starProjection x)) =
      (K ⊓ L).starProjection x := fun x => by
    rw [← comp_apply, starProjection_comp_starProjection_of_le inf_le_left, ← comp_apply,
      starProjection_comp_starProjection_of_le inf_le_right]
  have hlim : ∀ y, Tendsto
      (fun n => ((K.starProjection * L.starProjection * K.starProjection) ^ n) y) atTop
      (𝓝 ((K ⊓ L).starProjection y)) := by
    have h := PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp
      (tendsto_toPointwiseConvergenceCLM_starProjection_mul_mul_pow K L)
    simp only [toPointwiseConvergenceCLM_apply] at h
    exact h
  have key : ∀ x, Tendsto (fun n => ((K.starProjection * L.starProjection) ^ n) x) atTop
      (𝓝 ((K ⊓ L).starProjection x)) := fun x => by
    have h := hlim (K.starProjection (L.starProjection x))
    rw [hR] at h
    refine (tendsto_add_atTop_iff_nat 1).mp (h.congr fun n => ?_)
    rw [hpow, _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp]
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
  simp only [toPointwiseConvergenceCLM_apply]
  exact key

end Submodule
