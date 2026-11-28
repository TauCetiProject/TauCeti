/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Analysis.Convex.CCHypersurface.Basic
import TauCeti.Analysis.Convex.CCHypersurface.Corner
import TauCeti.Analysis.Convex.MeasurableSubgradient

/-!
# Borel measurable subgradient splitting on `c - c` hypersurfaces

On a finite-dimensional real inner product space `E`, every `c - c` hypersurface `s ⊆ E` carries
locally (on each closed ball `closedBall 0 R`) a globally Lipschitz convex potential `ψ : E → ℝ`
together with two Borel measurable subgradient selections `T₁, T₂ : E → E` that remain bounded
everywhere and split (`T₁ x ≠ T₂ x`) at every point of `s ∩ closedBall 0 R`. This is the
measurable splitting lemma used in the converse direction of Ambrosio–Gigli Theorem 1.26
(`TauCeti/MeasureTheory/OptimalTransport/Brenier/RegularSource.lean`).

## Main statements

* `TauCeti.IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne` —
  Borel measurable subgradient splitting along a `c - c` hypersurface.

## References

* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Theorem 1.26.
-/

public section

noncomputable section

open Set Metric Submodule
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Borel measurable subgradient splitting along a `c - c` hypersurface.** Given a `c - c`
hypersurface `s ⊆ E` and `R : ℝ`, there exist `K : ℝ≥0`, a `K`-Lipschitz convex `ψ : E → ℝ`, and
Borel measurable maps `T₁, T₂ : E → E` bounded by `K` that are subgradients of `ψ` everywhere and
satisfy `T₁ x ≠ T₂ x` at every `x ∈ s ∩ closedBall 0 R`. -/
theorem IsCCHypersurface.exists_convexOn_lipschitzWith_measurable_forall_add_inner_le_ne
    [MeasurableSpace E] [BorelSpace E] {s : Set E} (hs : IsCCHypersurface s) (R : ℝ) :
    ∃ (K : ℝ≥0) (ψ : E → ℝ) (T₁ T₂ : E → E),
      ConvexOn ℝ univ ψ ∧ LipschitzWith K ψ ∧ Measurable T₁ ∧ Measurable T₂ ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₁ x) ≤ ψ z) ∧
      (∀ x z, ψ x + inner ℝ (z - x) (T₂ x) ≤ ψ z) ∧
      (∀ x, ‖T₁ x‖ ≤ K) ∧ (∀ x, ‖T₂ x‖ ≤ K) ∧
      (∀ x ∈ s ∩ closedBall 0 R, T₁ x ≠ T₂ x) := by
  obtain ⟨e, he, Lf, Lg, f', g', hf', hg', hLf', hLg', hconv, hlip, heq_on⟩ :=
    hs.exists_convexOn_lipschitzWith_max_add_inner_eq R
  let P := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  obtain ⟨Gf, hGf_meas, hGf⟩ := hf'.exists_measurable_forall_add_inner_le isOpen_univ
  obtain ⟨Gg, hGg_meas, hGg⟩ := hg'.exists_measurable_forall_add_inner_le isOpen_univ
  have hsub₁ (x z : E) (hx : g' (P x) + inner ℝ x e ≤ f' (P x)) :
      max (f' (P x)) (g' (P x) + inner ℝ x e) + inner ℝ (z - x) (Gf (P x) : E) ≤
        max (f' (P z)) (g' (P z) + inner ℝ z e) := by
    rw [max_eq_left hx, ← inner_orthogonalProjectionOnto_eq_of_mem_right, map_sub]
    exact (hGf (P x) (mem_univ _) (P z) (mem_univ _)).trans (le_max_left _ _)
  have hsub₂ (x z : E) (hx : f' (P x) ≤ g' (P x) + inner ℝ x e) :
      max (f' (P x)) (g' (P x) + inner ℝ x e) + inner ℝ (z - x) ((Gg (P x) : E) + e) ≤
        max (f' (P z)) (g' (P z) + inner ℝ z e) := by
    rw [max_eq_right hx, inner_add_right, ← inner_orthogonalProjectionOnto_eq_of_mem_right,
      map_sub, inner_sub_left z x e]
    linarith [(add_le_add_left (hGg (P x) (mem_univ _) (P z) (mem_univ _)) (inner ℝ z e)).trans
      (le_max_right (f' (P z)) _)]
  obtain ⟨T₁, T₂, hT₁m, hT₂m, hT₁, hT₂, hTeq⟩ := exists_measurable_piecewise_subgradient_max
    (hLf'.continuous.comp P.continuous).measurable
    ((hLg'.continuous.comp P.continuous).add (by fun_prop)).measurable
    (measurable_subtypeVal.comp (hGf_meas.comp P.measurable))
    ((measurable_subtypeVal.comp (hGg_meas.comp P.measurable)).add measurable_const) hsub₁ hsub₂
  refine ⟨max Lf (Lg + 1), _, T₁, T₂, hconv, hlip, hT₁m, hT₂m, hT₁, hT₂,
    fun x => hlip.norm_le_of_forall_add_inner_le (hT₁ x),
    fun x => hlip.norm_le_of_forall_add_inner_le (hT₂ x), fun x hx hEq => ?_⟩
  obtain ⟨h₁, h₂⟩ := hTeq x (heq_on x hx).symm
  have hin₁ : inner ℝ (T₁ x) e = 0 :=
    h₁ ▸ Submodule.mem_orthogonal_singleton_iff_inner_left.mp (Gf (P x)).property
  have hin₂ : inner ℝ (T₂ x) e = 1 := by
    simp [h₂, inner_add_left,
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (Gg (P x)).property, he]
  linarith [congrArg (inner ℝ · e) hEq]

end TauCeti
