/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.NormedSpace
import TauCeti.Geometry.MeasureTheory.Rectifiable.Subspace

/-!
# Cone criteria for countable rectifiability

A subset of an extended metric space on which a map to a countably `k`-rectifiable image is
antilipschitz is itself countably `k`-rectifiable
(`TauCeti.CountablyRectifiable.of_antilipschitzWith_domRestrict`), since the inverse map on the
image is Lipschitz. In a real inner product space, a subset `s` lying locally inside a cone around a
`k`-plane `W` — meaning `‖Wᗮ.starProjection (y - x)‖ ≤ c ‖y - x‖` for some `c < 1` — projects
antilipschitzly onto `W` by the Pythagorean theorem, and is therefore countably `k`-rectifiable
(`TauCeti.CountablyRectifiable.of_norm_starProjection_orthogonal_le`).

When the plane `W`, the opening `c < 1` and the radius `r > 0` are allowed to vary from point to
point in a finite-dimensional real inner product space, countably many approximating `k`-planes and
balls cover the space, decomposing `s` into countably many pieces each satisfying a uniform cone
condition around a single `k`-plane
(`TauCeti.CountablyRectifiable.of_forall_exists_submodule_norm_starProjection_orthogonal_le`).
Specializing to hyperplanes `W = (ℝ ∙ ν)ᗮ` gives the codimension-one criterion in terms of unit
normal vectors (`TauCeti.CountablyRectifiable.of_forall_exists_unit_abs_inner_le`), which is used
to prove countable `(n - 1)`-rectifiability of the reduced boundary in De Giorgi's structure
theorem.

## References

* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Lemma 15.13 (cone criterion for
  rectifiability).
* H. Federer, *Geometric Measure Theory*, 3.2.29.
* L. Simon, *Lectures on Geometric Measure Theory*, §11.
-/

public section

open Function Metric MeasureTheory Module Set
open scoped NNReal RealInnerProductSpace

namespace TauCeti.CountablyRectifiable

section EMetricSpace

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {k : ℕ} {s : Set X}

/-- If a map `f : X → Y` is antilipschitz on `s` and `f '' s` is countably `k`-rectifiable, then
`s` is countably `k`-rectifiable. -/
theorem of_antilipschitzWith_domRestrict {f : X → Y} {K : ℝ≥0}
    (hf : AntilipschitzWith K (s.domRestrict f)) (hfs : CountablyRectifiable k (f '' s)) :
    CountablyRectifiable k s := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact empty
  have : Nonempty s := ⟨⟨x₀, hx₀⟩⟩
  let g : Y → s := invFun (s.domRestrict f)
  have hinv : RightInvOn g (s.domRestrict f) (range (s.domRestrict f)) :=
    fun _ hy => invFun_eq hy
  have hrange : range (s.domRestrict f) = f '' s := range_domRestrict f s
  have hLip : LipschitzOnWith K (Subtype.val ∘ g) (f '' s) := by
    rw [← hrange]
    simpa only [one_mul] using (LipschitzWith.subtype_val s).comp_lipschitzOnWith
      (lipschitzOnWith_iff_restrict.2 (hf.to_rightInvOn hinv))
  have himg : (Subtype.val ∘ g) '' (f '' s) = s := by
    ext x
    refine ⟨?_, fun hx => ?_⟩
    · rintro ⟨_, _, rfl⟩
      exact (g _).2
    · refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
      exact congrArg Subtype.val (leftInverse_invFun hf.injective ⟨x, hx⟩)
  rw [← himg]
  exact hfs.image hLip

end EMetricSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Global cone criterion for countable rectifiability.** If a subset `s` of a real inner product
space satisfies `‖Wᗮ.starProjection (y - x)‖ ≤ c ‖y - x‖` for all `x, y ∈ s`, where `W` is a
finite-dimensional subspace and `c < 1`, then `s` is countably `(dim W)`-rectifiable. The ambient
space need not be finite-dimensional. -/
theorem of_norm_starProjection_orthogonal_le {W : Submodule ℝ E} [FiniteDimensional ℝ W]
    {s : Set E} {c : ℝ} (hc : c < 1)
    (hcone : ∀ x ∈ s, ∀ y ∈ s, ‖Wᗮ.starProjection (y - x)‖ ≤ c * ‖y - x‖) :
    CountablyRectifiable (finrank ℝ W) s := by
  set c₀ : ℝ := max c 0
  have hc₀0 : 0 ≤ c₀ := le_max_right c 0
  have hc₀1 : c₀ < 1 := max_lt hc zero_lt_one
  have hpos : 0 < 1 - c₀ ^ 2 := by nlinarith
  let K : ℝ≥0 := ⟨(Real.sqrt (1 - c₀ ^ 2))⁻¹, by positivity⟩
  have hK : (K : ℝ) = (Real.sqrt (1 - c₀ ^ 2))⁻¹ := rfl
  have hanti : AntilipschitzWith K (s.domRestrict W.starProjection) := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hpyth := W.norm_sq_eq_add_norm_sq_starProjection ((y : E) - x)
    have hle : ‖Wᗮ.starProjection ((y : E) - x)‖ ≤ c₀ * ‖(y : E) - x‖ :=
      (hcone x x.2 y y.2).trans (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg _))
    have hsq : (1 - c₀ ^ 2) * ‖(y : E) - x‖ ^ 2 ≤ ‖W.starProjection ((y : E) - x)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Wᗮ.starProjection ((y : E) - x)‖),
        mul_le_mul hle hle (norm_nonneg _) (mul_nonneg hc₀0 (norm_nonneg _))]
    have hsqrt : Real.sqrt (1 - c₀ ^ 2) * ‖(y : E) - x‖ ≤ ‖W.starProjection ((y : E) - x)‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_mul hpos.le,
        ← Real.sqrt_sq (norm_nonneg (W.starProjection ((y : E) - x)))]
      exact Real.sqrt_le_sqrt hsq
    have hdist : dist (x : E) y ≤ K * dist (W.starProjection x) (W.starProjection y) := by
      rw [dist_comm (x : E) y, dist_eq_norm, dist_comm, dist_eq_norm, ← map_sub, hK,
        inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 hpos), mul_comm]
      exact hsqrt
    simpa only [Subtype.dist_eq, domRestrict_apply] using hdist
  refine of_antilipschitzWith_domRestrict hanti (W.countablyRectifiable.mono ?_)
  rintro _ ⟨x, -, rfl⟩
  exact Submodule.starProjection_apply_mem W x

variable [FiniteDimensional ℝ E]

/-- **Local cone criterion for countable rectifiability.** If at every point `x` of a subset `s` of
a finite-dimensional real inner product space there exist a `k`-dimensional subspace `W`, a
constant `c < 1` and a radius `r > 0` such that `‖Wᗮ.starProjection (y - x)‖ ≤ c ‖y - x‖` for all
`y ∈ s ∩ ball x r`, then `s` is countably `k`-rectifiable. -/
theorem of_forall_exists_submodule_norm_starProjection_orthogonal_le {k : ℕ} {s : Set E}
    (h : ∀ x ∈ s, ∃ W : Submodule ℝ E, finrank ℝ W = k ∧ ∃ c < (1 : ℝ), ∃ r > (0 : ℝ),
      ∀ y ∈ s ∩ ball x r, ‖Wᗮ.starProjection (y - x)‖ ≤ c * ‖y - x‖) :
    CountablyRectifiable k s := by
  classical
  -- A countable family of `k`-planes whose orthogonal-complement projections are dense.
  let T : Set (E →L[ℝ] E) := {P | ∃ W : Submodule ℝ E, finrank ℝ W = k ∧ P = Wᗮ.starProjection}
  obtain ⟨Dₚ, hDₚc, hDₚ⟩ := TopologicalSpace.exists_countable_dense T
  let W : Dₚ → Submodule ℝ E := fun p => p.1.2.choose
  have hWdim (p : Dₚ) : finrank ℝ (W p) = k := p.1.2.choose_spec.1
  have hWproj (p : Dₚ) : (W p)ᗮ.starProjection = (p.1 : E →L[ℝ] E) :=
    p.1.2.choose_spec.2.symm
  -- A countable dense set of ball centres in `E`.
  obtain ⟨Dₓ, hDₓc, hDₓ⟩ := TopologicalSpace.exists_countable_dense E
  have : Countable Dₚ := hDₚc.to_subtype
  have : Countable Dₓ := hDₓc.to_subtype
  -- Decompose `s` by approximating plane `W p`, centre `d`, cone opening `1 - 1 / (2 (m + 2))`
  -- and radius `1 / (n + 1)`.
  let A (p : Dₚ) (d : Dₓ) (m n : ℕ) : Set E :=
    {x ∈ s ∩ ball (d : E) (1 / (2 * ((n : ℝ) + 1))) |
      ∀ y ∈ s ∩ ball x (1 / ((n : ℝ) + 1)),
        ‖(W p)ᗮ.starProjection (y - x)‖ ≤ (1 - 1 / (2 * ((m : ℝ) + 2))) * ‖y - x‖}
  -- Each piece satisfies a uniform cone condition around `W p`.
  have hArect (p : Dₚ) (d : Dₓ) (m n : ℕ) : CountablyRectifiable k (A p d m n) := by
    rw [← hWdim p]
    refine of_norm_starProjection_orthogonal_le (c := 1 - 1 / (2 * ((m : ℝ) + 2)))
      (sub_lt_self 1 (by positivity)) fun x hx y hy => ?_
    have hdist : y ∈ ball x (1 / ((n : ℝ) + 1)) := by
      rw [mem_ball]
      have hxd : dist x (d : E) < 1 / (2 * ((n : ℝ) + 1)) := hx.1.2
      have hyd : dist y (d : E) < 1 / (2 * ((n : ℝ) + 1)) := hy.1.2
      have hsum : 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
        field_simp
        ring
      linarith [dist_triangle_right y x (d : E)]
    exact hx.2 y ⟨hy.1.1, hdist⟩
  -- The countable union of the pieces covers `s`.
  have hcov : s ⊆ ⋃ (p : Dₚ) (d : Dₓ) (m : ℕ) (n : ℕ), A p d m n := by
    intro x hx
    obtain ⟨V, hVdim, c, hc, r, hr, hV⟩ := h x hx
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hc)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
    have hε : (0 : ℝ) < 1 / (2 * ((m : ℝ) + 2)) := by positivity
    -- Pick `p ∈ Dₚ` with `‖(W p)ᗮ.starProjection - Vᗮ.starProjection‖ < 1 / (2 (m + 2))`.
    have hVT : Vᗮ.starProjection ∈ T := ⟨V, hVdim, rfl⟩
    obtain ⟨q, hqD, hqdist⟩ := Metric.mem_closure_iff.1 (hDₚ ⟨Vᗮ.starProjection, hVT⟩) _ hε
    -- Pick `d ∈ Dₓ` within `1 / (2 (n + 1))` of `x`.
    obtain ⟨d, hdD, hddist⟩ := Metric.mem_closure_iff.1 (hDₓ x) _ (by positivity :
      (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)))
    refine mem_iUnion.2 ⟨⟨q, hqD⟩, mem_iUnion.2 ⟨⟨d, hdD⟩, mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨n, ?_⟩⟩⟩⟩
    refine ⟨⟨hx, by simpa [mem_ball] using hddist⟩, fun y hy => ?_⟩
    have hyr : y ∈ s ∩ ball x r :=
      ⟨hy.1, ball_subset_ball (le_of_lt (by simpa using hn)) hy.2⟩
    have hcm : c ≤ 1 - 1 / ((m : ℝ) + 2) := by
      have : 1 / ((m : ℝ) + 2) < 1 / ((m : ℝ) + 1) :=
        one_div_lt_one_div_of_lt (by positivity) (by linarith)
      linarith
    have hdiff : ‖(W ⟨q, hqD⟩)ᗮ.starProjection - Vᗮ.starProjection‖ ≤ 1 / (2 * ((m : ℝ) + 2)) := by
      rw [hWproj, ← dist_eq_norm, dist_comm]
      exact le_of_lt (by simpa only [Subtype.dist_eq] using hqdist)
    have hsum : 1 / (2 * ((m : ℝ) + 2)) + 1 / (2 * ((m : ℝ) + 2)) = 1 / ((m : ℝ) + 2) := by
      field_simp
      ring
    calc ‖(W ⟨q, hqD⟩)ᗮ.starProjection (y - x)‖
        = ‖Vᗮ.starProjection (y - x) +
            ((W ⟨q, hqD⟩)ᗮ.starProjection - Vᗮ.starProjection) (y - x)‖ := by
          simp only [sub_apply, add_sub_cancel]
      _ ≤ ‖Vᗮ.starProjection (y - x)‖ +
            ‖((W ⟨q, hqD⟩)ᗮ.starProjection - Vᗮ.starProjection) (y - x)‖ := norm_add_le _ _
      _ ≤ c * ‖y - x‖ + (1 / (2 * ((m : ℝ) + 2))) * ‖y - x‖ := by
          gcongr
          · exact hV y hyr
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
      _ ≤ (1 - 1 / (2 * ((m : ℝ) + 2))) * ‖y - x‖ := by
          have : c + 1 / (2 * ((m : ℝ) + 2)) ≤ 1 - 1 / (2 * ((m : ℝ) + 2)) := by linarith
          nlinarith [norm_nonneg (y - x)]
  exact (iUnion fun p => iUnion fun d => iUnion fun m => iUnion fun n => hArect p d m n).mono hcov

/-- **Codimension-one local cone criterion for countable rectifiability.** If at every point `x`
of a subset `s` of a finite-dimensional real inner product space `E` there exist a unit vector `ν`,
a constant `c < 1` and a radius `r > 0` such that `|⟪y - x, ν⟫| ≤ c ‖y - x‖` for all
`y ∈ s ∩ ball x r`, then `s` is countably `(dim E - 1)`-rectifiable. -/
theorem of_forall_exists_unit_abs_inner_le {s : Set E}
    (h : ∀ x ∈ s, ∃ ν : E, ‖ν‖ = 1 ∧ ∃ c < (1 : ℝ), ∃ r > (0 : ℝ),
      ∀ y ∈ s ∩ ball x r, |⟪y - x, ν⟫| ≤ c * ‖y - x‖) :
    CountablyRectifiable (finrank ℝ E - 1) s := by
  refine of_forall_exists_submodule_norm_starProjection_orthogonal_le fun x hx => ?_
  obtain ⟨ν, hν1, c, hc, r, hr, hball⟩ := h x hx
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (hν1 ▸ one_ne_zero)
  have : Nontrivial E := ⟨⟨ν, 0, hν0⟩⟩
  have : Fact (finrank ℝ E = finrank ℝ E - 1 + 1) := ⟨(Nat.sub_add_cancel finrank_pos).symm⟩
  refine ⟨(ℝ ∙ ν)ᗮ, Submodule.finrank_orthogonal_span_singleton hν0, c, hc, r, hr, fun y hy => ?_⟩
  rw [Submodule.starProjection_orthogonal', Submodule.starProjection_orthogonal', sub_sub_cancel,
    Submodule.starProjection_singleton]
  simpa [norm_smul, Real.norm_eq_abs, hν1, real_inner_comm] using hball y hy

end InnerProductSpace

end TauCeti.CountablyRectifiable
