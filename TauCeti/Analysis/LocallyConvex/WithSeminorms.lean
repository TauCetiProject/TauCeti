/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Composition of seminorm-bounded maps and absolutely summable series

Semilinear maps bounded with respect to families of seminorms are closed under composition.
This supplies composite bounds without requiring topologies on the modules or directedness of
the seminorm families.

In a complete space whose topology is given by a family of seminorms, a series converges as soon
as it is absolutely summable for every seminorm of the family
(`WithSeminorms.summable_of_summable_seminorm`), and a continuous seminorm of its sum is at most
the sum of the seminorms of its terms (`Seminorm.map_tsum_le`). These are the locally convex
analogues of `Summable.of_norm` and `norm_tsum_le_tsum_norm`.
-/

public section

open Filter

namespace Seminorm

variable {𝕜 𝕜₂ 𝕜₃ E F G ι ι' ι'' : Type*}
variable [SeminormedRing 𝕜] [SeminormedRing 𝕜₂] [SeminormedRing 𝕜₃]
variable [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-- The composite of seminorm-bounded semilinear maps is seminorm-bounded. -/
theorem IsBounded.comp {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜₂ F}
    {r : ι'' → Seminorm 𝕜₃ G} {f : E →ₛₗ[σ₁₂] F} {g : F →ₛₗ[σ₂₃] G}
    (hg : IsBounded q r g) (hf : IsBounded p q f) : IsBounded p r (g.comp f) := by
  intro i
  obtain ⟨s, C, hs⟩ := hg i
  obtain ⟨D, t, ht⟩ := isBounded_sup hf s
  refine ⟨t, C * D, ?_⟩
  rw [comp_comp]
  calc
    _ ≤ (C • s.sup q).comp f := comp_mono f hs
    _ = C • (s.sup q).comp f := smul_comp _ _ _
    _ ≤ C • (D • t.sup p) := IsOrderedSMul.smul_le_smul_left _ _ ht C
    _ = _ := (mul_smul C D (t.sup p)).symm

/-- A continuous seminorm of the sum of a series is at most the sum of the seminorms of its
terms, provided that both series converge. -/
theorem map_tsum_le {𝕜 E β : Type*} [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] {q : Seminorm 𝕜 E} (hq : Continuous q) {f : β → E} (hf : Summable f)
    (hqf : Summable fun b ↦ q (f b)) : q (∑' b, f b) ≤ ∑' b, q (f b) :=
  le_of_tendsto' ((hq.tendsto _).comp hf.hasSum) fun s ↦
    (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) s f).trans
      (hqf.sum_le_tsum s fun b _ ↦ apply_nonneg q (f b))

end Seminorm

namespace WithSeminorms

variable {𝕜 E ι β : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] {p : SeminormFamily 𝕜 E ι}

/-- In a complete space whose topology is given by the seminorm family `p`, a series that is
absolutely summable for every seminorm `p i` is summable. -/
theorem summable_of_summable_seminorm (hp : WithSeminorms p) {f : β → E}
    (hf : ∀ i, Summable fun b ↦ p i (f b)) : Summable f := by
  classical
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
  intro U hU
  obtain ⟨⟨S, r⟩, hr, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.1 hU
  -- One tail estimate for the finite sum of the seminorms in `S` controls all of them.
  have hg : Summable fun b ↦ ∑ i ∈ S, p i (f b) := summable_sum fun i _ ↦ hf i
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hg r hr
  refine ⟨s, fun t ht ↦ hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine Seminorm.finset_sup_apply_lt hr fun i hi ↦ ?_
  calc p i (∑ b ∈ t, f b) ≤ ∑ b ∈ t, p i (f b) :=
        Finset.le_sum_of_subadditive (p i) (map_zero _).le (map_add_le_add _) t f
    _ ≤ ∑ b ∈ t, ∑ j ∈ S, p j (f b) := Finset.sum_le_sum fun b _ ↦
        Finset.single_le_sum (f := fun j ↦ p j (f b)) (fun j _ ↦ apply_nonneg _ _) hi
    _ ≤ ‖∑ b ∈ t, ∑ j ∈ S, p j (f b)‖ := Real.le_norm_self _
    _ < r := hs t ht

end WithSeminorms
