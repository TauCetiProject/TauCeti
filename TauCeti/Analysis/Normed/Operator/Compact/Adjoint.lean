/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Module.Dual.Functoriality

/-!
# Schauder's theorem: compactness of the adjoint

The adjoint of a bounded operator `T : E →L[𝕜] F` between normed spaces is precomposition
`ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`, `f ↦ f ∘ T`.
**Schauder's theorem** says that an operator into a Banach space is compact if and only if its
adjoint is compact (`ContinuousLinearMap.isCompactOperator_precomp_iff`).

The theorem is first proved for total boundedness of the image of the closed unit ball, where no
completeness is needed (`ContinuousLinearMap.totallyBounded_precomp_image_closedBall_iff`).

* If `T` maps the unit ball to a totally bounded set, cover that image by finitely many balls
  `ball yᵢ δ`. Functionals of norm at most `1` that are close at the finitely many centres `yᵢ`
  are uniformly close on the image of the unit ball. The values at the centres range over a
  bounded subset of the finite-dimensional space `𝕜ⁿ`, which is totally bounded because `𝕜` is
  proper. Hence the adjoint maps the dual unit ball to a totally bounded set. This direction holds
  over every proper nontrivially normed field.
* Conversely, applying this to the adjoint shows that the bidual operator maps the unit ball of the
  bidual to a totally bounded set. The canonical maps into the biduals intertwine `T` with its
  bidual operator, send the unit ball into the unit ball, and over `ℝ` or `ℂ` the map into the
  bidual of `F` is an isometry by Hahn–Banach, so `T` maps the unit ball to a totally bounded set.

The dual of a normed space is complete, so the forward implication of Schauder's theorem,
`IsCompactOperator.precomp`, needs no completeness hypothesis. The reverse implication
`IsCompactOperator.of_precomp` needs `F` to be complete.

## Main declarations

* `ContinuousLinearMap.totallyBounded_precomp_image_closedBall`: if `T` maps the unit ball to a
  totally bounded set, so does its adjoint.
* `ContinuousLinearMap.totallyBounded_precomp_image_closedBall_iff`: over `ℝ` or `ℂ`, the converse
  also holds.
* `IsCompactOperator.precomp`: the adjoint of a compact operator is compact.
* `IsCompactOperator.of_precomp`: an operator into a Banach space with compact adjoint is compact.
* `ContinuousLinearMap.isCompactOperator_precomp_iff`: Schauder's theorem.

## References

* J. Schauder, *Über lineare, vollstetige Funktionaloperationen*, Studia Math. **2** (1930),
  183–196.
* W. Rudin, *Functional Analysis*, 2nd ed., Theorem 4.19.
* R. E. Megginson, *An Introduction to Banach Space Theory*, Theorem 3.4.15.
-/

public section

open Metric Set

namespace ContinuousLinearMap

variable {𝕜 E F : Type*}

section Proper

variable [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Two functionals of norm at most one that are `δ`-close at the points of a `δ`-net `t` of a set
`s` are `3 δ`-close on `s`. -/
private theorem norm_apply_sub_apply_lt_of_subset_iUnion_ball {f g : StrongDual 𝕜 F}
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) {s t : Set F} {δ : ℝ} (hst : s ⊆ ⋃ y ∈ t, ball y δ)
    (hfg : ∀ y ∈ t, ‖f y - g y‖ < δ) {z : F} (hz : z ∈ s) : ‖f z - g z‖ < 3 * δ := by
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hst hz)
  rw [mem_ball, dist_eq_norm] at hy
  have h₁ : ‖f (z - y)‖ < δ :=
    (f.le_opNorm _).trans_lt (by nlinarith [norm_nonneg (z - y)])
  have h₂ : ‖g (z - y)‖ < δ :=
    (g.le_opNorm _).trans_lt (by nlinarith [norm_nonneg (z - y)])
  calc ‖f z - g z‖ = ‖f (z - y) + (f y - g y) - g (z - y)‖ := by
        congr 1
        simp only [map_sub]
        abel
    _ ≤ ‖f (z - y)‖ + ‖f y - g y‖ + ‖g (z - y)‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < 3 * δ := by linarith [hfg y hyt]

variable [ProperSpace 𝕜]

/-- If a bounded operator maps the closed unit ball to a totally bounded set, so does its adjoint.
This is the forward direction of Schauder's theorem; it holds over every proper nontrivially
normed field and needs no completeness. -/
theorem totallyBounded_precomp_image_closedBall {T : E →L[𝕜] F}
    (hT : TotallyBounded (T '' closedBall 0 1)) :
    TotallyBounded
      ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) '' closedBall 0 1) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hc₀ : 0 < ‖c‖ := one_pos.trans hc
  rw [totallyBounded_iff]
  intro ε hε
  set δ := ε / (4 * ‖c‖) with hδ_def
  have hδ : 0 < δ := by positivity
  -- A finite `δ`-net `t` of the image of the unit ball under `T`.
  obtain ⟨t, ht, hTt⟩ := totallyBounded_iff.mp hT δ hδ
  have : Finite t := ht.to_subtype
  have : Fintype t := Fintype.ofFinite t
  -- Evaluation at the points of the net, a bounded operator into the proper space `t → 𝕜`.
  let Φ : StrongDual 𝕜 F →L[𝕜] t → 𝕜 := pi fun y ↦ apply 𝕜 𝕜 (y : F)
  have hΦ : TotallyBounded (Φ '' closedBall 0 1) :=
    (Φ.lipschitzWith.isBounded_image isBounded_closedBall).isCompact_closure.totallyBounded.subset
      subset_closure
  -- Functionals of norm at most one that are `δ`-close on the net, chosen from the dual ball.
  obtain ⟨u, huΦ, hu, hcover⟩ := finite_approx_of_totallyBounded hΦ δ hδ
  choose! g hgB hgΦ using fun p (hp : p ∈ u) ↦ huΦ hp
  refine ⟨(fun p ↦ precomp 𝕜 T (g p)) '' u, hu.image _, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨p, hpu, hp⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem Φ hf))
  refine mem_iUnion₂.mpr ⟨_, mem_image_of_mem _ hpu, ?_⟩
  rw [mem_closedBall_zero_iff] at hf
  have hg : ‖g p‖ ≤ 1 := mem_closedBall_zero_iff.mp (hgB p hpu)
  rw [← hgΦ p hpu, mem_ball, dist_eq_norm, ← map_sub] at hp
  -- On the image of the unit ball, `f` and `g p` differ by less than `3 δ`.
  have key (x : E) (hx : x ∈ closedBall (0 : E) 1) : ‖f (T x) - g p (T x)‖ < 3 * δ :=
    norm_apply_sub_apply_lt_of_subset_iUnion_ball hf hg hTt
      (fun y hy ↦ by simpa [Φ] using (norm_le_pi_norm (Φ (f - g p)) ⟨y, hy⟩).trans_lt hp)
      (mem_image_of_mem T hx)
  rw [mem_ball, dist_eq_norm, ← map_sub]
  calc ‖precomp 𝕜 T (f - g p)‖ ≤ 3 * δ * ‖c‖ := by
        refine opNorm_le_of_shell one_pos (by positivity) hc fun x hx₁ hx₂ ↦ ?_
        have hx : x ∈ closedBall (0 : E) 1 := mem_closedBall_zero_iff.mpr hx₂.le
        have : 1 ≤ ‖c‖ * ‖x‖ := by rwa [div_le_iff₀' hc₀] at hx₁
        calc ‖precomp 𝕜 T (f - g p) x‖ = ‖f (T x) - g p (T x)‖ := by simp
          _ ≤ 3 * δ := (key x hx).le
          _ ≤ 3 * δ * ‖c‖ * ‖x‖ := by nlinarith
    _ < ε := by
        rw [hδ_def]
        field_simp
        linarith

end Proper

section RCLike

variable [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over `ℝ` or `ℂ`, a bounded operator maps the closed unit ball to a totally bounded set if and
only if its adjoint does. -/
theorem totallyBounded_precomp_image_closedBall_iff {T : E →L[𝕜] F} :
    TotallyBounded
        ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) '' closedBall 0 1) ↔
      TotallyBounded (T '' closedBall 0 1) := by
  refine ⟨fun hT ↦ ?_, totallyBounded_precomp_image_closedBall⟩
  -- The bidual operator maps the unit ball of the bidual to a totally bounded set, and the
  -- isometric embedding of `F` into its bidual carries the image of the unit ball under `T` into
  -- that set.
  refine (totallyBounded_preimage
    (NormedSpace.inclusionInDoubleDualLi (E := F) 𝕜).isometry.isUniformInducing
    (totallyBounded_precomp_image_closedBall hT)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨NormedSpace.inclusionInDoubleDual 𝕜 E x, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff] at hx ⊢
    exact (NormedSpace.double_dual_bound 𝕜 E x).trans hx
  · exact precomp_precomp_inclusionInDoubleDual T x

end RCLike

end ContinuousLinearMap

open ContinuousLinearMap

variable {𝕜 E F : Type*}

/-- **Schauder's theorem**, forward direction: the adjoint of a compact operator is compact. It
holds over every proper nontrivially normed field, without completeness hypotheses, because the
dual of a normed space is complete. -/
theorem IsCompactOperator.precomp [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    IsCompactOperator (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) := by
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact (σ₁₂ := RingHom.id 𝕜) 1
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    ((ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) :
      StrongDual 𝕜 F →ₗ[𝕜] StrongDual 𝕜 E) one_pos).mpr <|
    (totallyBounded_precomp_image_closedBall (hK.totallyBounded.subset hTK)).closure
      |>.isCompact_of_isClosed isClosed_closure

/-- **Schauder's theorem**, reverse direction: an operator into a Banach space over `ℝ` or `ℂ`
whose adjoint is compact is itself compact. -/
theorem IsCompactOperator.of_precomp [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] {T : E →L[𝕜] F}
    (hT : IsCompactOperator
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E)) :
    IsCompactOperator T := by
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact (σ₁₂ := RingHom.id 𝕜) 1
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[𝕜] F) one_pos).mpr <|
    (totallyBounded_precomp_image_closedBall_iff.mp (hK.totallyBounded.subset hTK)).closure
      |>.isCompact_of_isClosed isClosed_closure

namespace ContinuousLinearMap

/-- **Schauder's theorem**: an operator into a Banach space over `ℝ` or `ℂ` is compact if and only
if its adjoint is compact. -/
theorem isCompactOperator_precomp_iff [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F] {T : E →L[𝕜] F} :
    IsCompactOperator (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) ↔
      IsCompactOperator T :=
  ⟨.of_precomp, .precomp⟩

end ContinuousLinearMap
