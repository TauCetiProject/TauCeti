/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.CCHypersurface.Basic
import TauCeti.Analysis.Convex.SubgradientImage

/-!
# Local convex Lipschitz corner potentials along a `c - c` hypersurface

Given a `c - c` hypersurface `s ⊆ E` and a radius `R : ℝ`, there exist a unit vector `e : E` and
globally Lipschitz convex branches `f', g' : ↥(ℝ ∙ e)ᗮ → ℝ` whose maximum
`x ↦ max (f' (P x)) (g' (P x) + ⟪x, e⟫)` (with `P` the orthogonal projection onto `(ℝ ∙ e)ᗮ`) is
convex and globally Lipschitz on `E`, with the two branches matching on `s ∩ closedBall 0 R`.
Normalizing by the value at `0` produces a Lipschitz convex potential with unit symmetric second
difference along `e` on `s ∩ closedBall 0 R`, shared by Zajíček's covering theorem
(`TauCeti/Analysis/Convex/CCHypersurface/Zajicek.lean`) and measurable subgradient splitting
(`TauCeti/Analysis/Convex/CCHypersurface/MeasurableSplitting.lean`).

## Main declarations

* `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_max_add_inner_eq` — globally Lipschitz
  convex two-branch representation of a `c - c` hypersurface on a closed ball;
* `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_add_sub_two_mul_eq` — Lipschitz convex
  potential with unit second-difference slope along a `c - c` hypersurface on a closed ball.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Theorems 1.24 and 1.26.
-/

public section

noncomputable section

open Set Metric Submodule
open scoped NNReal

namespace TauCeti

section Corner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Lipschitz branch representation of a `c - c` hypersurface on a ball.** Given a `c - c`
hypersurface `s ⊆ E` and `R : ℝ`, there exist a unit vector `e : E` and globally Lipschitz convex
branches `f', g' : ↥(ℝ ∙ e)ᗮ → ℝ` such that `x ↦ max (f' (P x)) (g' (P x) + ⟪x, e⟫)` (where `P`
is orthogonal projection onto `(ℝ ∙ e)ᗮ`) is convex and Lipschitz on `E`, and the two branches agree
on `s ∩ closedBall 0 R`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_max_add_inner_eq {s : Set E}
    (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (e : E) (_ : ‖e‖ = 1) (Lf Lg : ℝ≥0) (f' g' : ↥(ℝ ∙ e)ᗮ → ℝ),
      ConvexOn ℝ univ f' ∧ ConvexOn ℝ univ g' ∧ LipschitzWith Lf f' ∧ LipschitzWith Lg g' ∧
      ConvexOn ℝ univ (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
        (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) ∧
      LipschitzWith (max Lf (Lg + 1)) (fun x : E => max (f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x))
        (g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e)) ∧
      ∀ x ∈ s ∩ closedBall 0 R, g' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) + inner ℝ x e =
        f' ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) := by
  obtain ⟨e, he, f, g, -, -, hf, hg, hs_eq⟩ := isCCHypersurface_def.1 hs
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Lf, f', hf', hLf', hff'⟩ := hf.exists_convexOn_lipschitzWith_eqOn isOpen_univ
    (isCompact_closedBall 0 (max R 0)) (subset_univ _)
  obtain ⟨Lg, g', hg', hLg', hgg'⟩ := hg.exists_convexOn_lipschitzWith_eqOn isOpen_univ
    (isCompact_closedBall 0 (max R 0)) (subset_univ _)
  have hlip_in : LipschitzWith 1 (fun x : E => inner ℝ x e) := LipschitzWith.mk_one fun _ _ => by
    rw [Real.dist_eq, ← inner_sub_left, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans_eq (by rw [he, mul_one])
  refine ⟨e, he, Lf, Lg, f', g', hf', hg', hLf', hLg',
    (hf'.comp_linearMap P.toLinearMap).sup ((hg'.comp_linearMap P.toLinearMap).add
      ⟨convex_univ, fun _ _ _ _ _ _ _ _ _ => by simp [inner_add_left, real_inner_smul_left]⟩),
    ((hLf'.comp (Submodule.lipschitzWith_orthogonalProjectionOnto _)).weaken (by simp)).max
      (((hLg'.comp (Submodule.lipschitzWith_orthogonalProjectionOnto _)).weaken (by simp) :
        LipschitzWith Lg (fun x => g' (P x))).add hlip_in),
    fun x ⟨hxs, hxR⟩ => ?_⟩
  have hPx : P x ∈ closedBall (0 : ↥(ℝ ∙ e)ᗮ) (max R 0) := mem_closedBall_zero_iff.2 <|
    (norm_orthogonalProjectionOnto_apply_le _ x).trans <|
      (mem_closedBall_zero_iff.1 hxR).trans (le_max_left R 0)
  rw [hs_eq, mem_ofPred_eq] at hxs
  rw [← hff' hPx, ← hgg' hPx, hxs]
  ring

/-- **Lipschitz convex potential with unit second-difference slope along a `c - c` hypersurface.**
Given a `c - c` hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a unit vector `e : E`, and
a `K`-Lipschitz convex `ψ : E → ℝ` with `ψ 0 = 0` and
`ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t` for every `x ∈ s ∩ closedBall 0 R` and `t ≥ 0`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_add_sub_two_mul_eq {s : Set E}
    (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (e : E) (_ : ‖e‖ = 1) (ψ : E → ℝ),
      ConvexOn ℝ univ ψ ∧ ψ 0 = 0 ∧ LipschitzWith K ψ ∧
      ∀ x ∈ s ∩ closedBall 0 R, ∀ t : ℝ, 0 ≤ t →
        ψ (x + t • e) + ψ (x - t • e) - 2 * ψ x = t := by
  obtain ⟨e, he, Lf, Lg, f', g', -, -, -, -, hconv₀, hlip₀, heq_on⟩ :=
    hs.exists_convexOn_lipschitzWith_max_add_inner_eq R
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  let ψ : E → ℝ := fun x => max (f' (P x)) (g' (P x) + inner ℝ x e) - max (f' 0) (g' 0)
  refine ⟨max Lf (Lg + 1), e, he, ψ, hconv₀.add_const (-max (f' 0) (g' 0)), by simp [ψ, P],
    (hlip₀.sub (.const _)).weaken (by simp), fun x hx t ht => ?_⟩
  have hin (s : ℝ) : inner ℝ (x + s • e) e = inner ℝ x e + s := by
    simp [inner_add_left, real_inner_smul_left, he]
  have hin_sub : inner ℝ (x - t • e) e = inner ℝ x e - t := by
    simpa [sub_eq_add_neg, neg_smul] using hin (-t)
  simp only [ψ, P, map_add, map_sub, map_smul,
    orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero, sub_zero, hin t, hin_sub]
  rw [← add_assoc, ← add_sub_assoc (g' _), heq_on x hx,
    max_eq_right (le_add_of_nonneg_right ht),
    max_eq_left (sub_le_self _ ht), max_self]
  ring

end Corner

end TauCeti
