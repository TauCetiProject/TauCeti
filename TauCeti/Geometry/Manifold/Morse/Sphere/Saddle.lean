/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
public import TauCeti.Geometry.Manifold.Morse.Sphere.Restriction
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

/-!
# A Morse function on the sphere with a saddle

Let `u` and `v` be orthogonal unit vectors of a real inner product space of dimension `n + 1`,
write `hᵤ` and `hᵥ` for the height functions of the unit sphere `Sⁿ` in their directions
(`TauCeti.sphereHeight`), and let `0 < t < 2`. The function

`f = hᵤ² + t hᵥ`

is a Morse function on `Sⁿ` (`TauCeti.isMorse_sphereHeight_sq_add_smul_sphereHeight`) with exactly
four critical points (`TauCeti.criticalPoints_sphereHeight_sq_add_smul_sphereHeight`):

* the south pole `-v`, the minimum, of index `0`;
* the north pole `v`, of index `n - 1`, a saddle when `n ≥ 2`: along `u` the square `hᵤ²` wins
  over the tilt `t hᵥ`, since `t < 2`, and in the other directions the height `hᵥ` decreases;
* the two maxima `±√(1 - t² / 4) u + (t / 2) v`, of index `n`, the points with `hᵥ = t / 2` and
  `hᵤ² = 1 - t² / 4`.

Replacing `v` and `t` by `-v` and `-t` does not change `f`, so for `-2 < t < 0` the same holds
with the roles of the poles exchanged. So for `0 < |t| < 2` and `n ≥ 2` the numbers of critical
points of `f` of index `0`, `n - 1` and `n` are `1`, `1` and `2`
(`TauCeti.criticalCount_sphereHeight_sq_add_smul_sphereHeight`), and `-f` has two minima, one
critical point of index `1` and one maximum
(`TauCeti.criticalCount_neg_sphereHeight_sq_add_smul_sphereHeight`). On `S²` the critical counts of
`f` in indices `0, 1, 2` are `(1, 1, 2)` and those of `-f` are `(2, 1, 1)`: the counts of a single
Morse function need not be symmetric under `j ↦ dim M - j`, although those of `f` and `-f` are
exchanged by it (`TauCeti.IsMorse.criticalCount_neg`). Both alternating sums are `2`, the Euler
characteristic of `S²`.

The Morse data are computed by Lagrange multipliers
(`TauCeti.mem_criticalPoints_comp_coe_sphere_iff_mem_span` and
`TauCeti.criticalHessian_comp_coe_sphere_apply`). The gradient of
`F(x) = ⟪x, u⟫² + t ⟪x, v⟫` on the ambient space is `2 ⟪x, u⟫ u + t v`, so a point `p` of the
sphere is critical exactly when this is a multiple `μ p` of `p`; then either `⟪p, u⟫ = 0` and
`p = ±v`, or `μ = 2`. The critical Hessian at `p` is `2 ⟪a, u⟫ ⟪b, u⟫ - μ ⟪a, b⟫` on the
tangent hyperplane `pᗮ`, with `μ = -t` at `-v`, `μ = t` at `v` and `μ = 2` at the two maxima.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §§2 and 6.
-/

public section

noncomputable section

open Function Metric Module Set
open scoped ContDiff InnerProductSpace Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {u v p : sphere (0 : E) 1} {t : ℝ}

/-! ### The ambient function and its derivatives -/

/-- The function `x ↦ ⟪x, u⟫² + t ⟪x, v⟫` on the ambient space, whose restriction to the sphere is
`hᵤ² + t hᵥ`. -/
private def ambient (u v : sphere (0 : E) 1) (t : ℝ) (x : E) : ℝ :=
  ⟪x, (u : E)⟫ ^ 2 + t * ⟪x, (v : E)⟫

omit [Fact (finrank ℝ E = n + 1)] in
private theorem sphereHeight_sq_add_smul_sphereHeight_eq :
    sphereHeight u ^ 2 + t • sphereHeight v = ambient u v t ∘ ((↑) : sphere (0 : E) 1 → E) := by
  funext x
  simp [ambient]

omit [Fact (finrank ℝ E = n + 1)] in
private theorem hasFDerivAt_ambient (x : E) :
    HasFDerivAt (ambient u v t) (innerSL ℝ ((2 * ⟪x, (u : E)⟫) • (u : E) + t • (v : E))) x := by
  have h := (((innerSL ℝ (u : E)).hasFDerivAt (x := x)).pow 2).add
    (((innerSL ℝ (v : E)).hasFDerivAt (x := x)).const_mul t)
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  · ext w
    simp [real_inner_comm]
  · simp [ambient, real_inner_comm]

omit [Fact (finrank ℝ E = n + 1)] in
private theorem contDiff_ambient : ContDiff ℝ ∞ (ambient u v t) := by
  have h : ambient u v t = fun x ↦ innerSL ℝ (u : E) x ^ 2 + t * innerSL ℝ (v : E) x := by
    funext x
    simp [ambient, real_inner_comm]
  rw [h]
  fun_prop

omit [Fact (finrank ℝ E = n + 1)] in
private theorem fderiv_fderiv_ambient (x a b : E) :
    fderiv ℝ (fderiv ℝ (ambient u v t)) x a b = 2 * ⟪a, (u : E)⟫ * ⟪b, (u : E)⟫ := by
  have hD : fderiv ℝ (ambient u v t) =
      fun y ↦ (2 * ⟪y, (u : E)⟫) • innerSL ℝ (u : E) + t • innerSL ℝ (v : E) := by
    funext y
    rw [(hasFDerivAt_ambient y).fderiv]
    ext w
    simp
  have hc : HasFDerivAt (fun y : E ↦ 2 * ⟪y, (u : E)⟫) ((2 : ℝ) • innerSL ℝ (u : E)) x := by
    refine (((innerSL ℝ (u : E)).hasFDerivAt (x := x)).const_mul 2).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ ?_)
    simp [real_inner_comm]
  rw [hD, ((hc.smul_const (innerSL ℝ (u : E))).add_const _).fderiv]
  simp [real_inner_comm]

/-! ### The critical points -/

omit [Fact (finrank ℝ E = n + 1)] in
/-- At a point with `hᵥ = t / 2` and `hᵤ² = 1 - t² / 4` the ambient gradient `2 ⟪p, u⟫ u + t v` is
`2 p`. -/
private theorem mem_span_of_sphereHeight_eq (huv : ⟪(u : E), (v : E)⟫ = 0)
    (h1 : sphereHeight v p = t / 2) (h2 : sphereHeight u p ^ 2 = 1 - t ^ 2 / 4) :
    (2 * ⟪(p : E), (u : E)⟫) • (u : E) + t • (v : E) ∈ ℝ ∙ (p : E) := by
  refine Submodule.mem_span_singleton.2 ⟨2, ?_⟩
  have hx := coe_eq_sphereHeight_smul_add_sphereHeight_smul huv (x := p) (by rw [h1, h2]; ring)
  rw [h1, sphereHeight_apply] at hx
  nth_rewrite 1 [hx]
  rw [smul_add, smul_smul, smul_smul]
  congr 2
  ring

/-- A point with `hᵥ = t / 2` and `hᵤ² = 1 - t² / 4` is a critical point of `hᵤ² + t hᵥ`. -/
private theorem mem_criticalPoints_of_sphereHeight_eq (huv : ⟪(u : E), (v : E)⟫ = 0)
    (h1 : sphereHeight v p = t / 2) (h2 : sphereHeight u p ^ 2 = 1 - t ^ 2 / 4) :
    p ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) := by
  rw [sphereHeight_sq_add_smul_sphereHeight_eq,
    mem_criticalPoints_comp_coe_sphere_iff_mem_span (hasFDerivAt_ambient (p : E))]
  exact mem_span_of_sphereHeight_eq huv h1 h2

/-- **The critical points of `hᵤ² + t hᵥ`.** For orthogonal unit vectors `u`, `v` and `t ≠ 0`, the
critical points of `hᵤ² + t hᵥ` on the sphere are the poles `±v` and the points with `hᵥ = t / 2`
and `hᵤ² = 1 - t² / 4`. -/
theorem mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht : t ≠ 0) :
    p ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) ↔
      p = v ∨ p = -v ∨ (sphereHeight v p = t / 2 ∧ sphereHeight u p ^ 2 = 1 - t ^ 2 / 4) := by
  have hu : ⟪(u : E), (u : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere u)
  have hv : ⟪(v : E), (v : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere v)
  have hp : ⟪(p : E), (p : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
  have hvu : ⟪(v : E), (u : E)⟫ = 0 := by rw [real_inner_comm, huv]
  rw [sphereHeight_sq_add_smul_sphereHeight_eq,
    mem_criticalPoints_comp_coe_sphere_iff_mem_span (hasFDerivAt_ambient (p : E))]
  constructor
  · rintro hc
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hc
    -- Pair `c p = 2 ⟪p, u⟫ u + t v` with `u`, `v` and `p`.
    have h1 := congrArg (fun y ↦ ⟪y, (u : E)⟫) hc
    have h2 := congrArg (fun y ↦ ⟪y, (v : E)⟫) hc
    have h3 := congrArg (fun y ↦ ⟪(p : E), y⟫) hc
    simp only [inner_smul_left, inner_add_left, hu, hvu, huv, hv, RCLike.conj_to_real] at h1 h2
    simp only [inner_smul_right, inner_add_right, hp] at h3
    simp only [sphereHeight_apply]
    by_cases hpu : ⟪(p : E), (u : E)⟫ = 0
    · -- Then `t ⟪p, v⟫² = t`, so `⟪p, v⟫ = ±1` and `p = ±v`.
      have hsq : ⟪(p : E), (v : E)⟫ ^ 2 = 1 := by
        rw [hpu] at h3
        apply mul_left_cancel₀ ht
        linear_combination h2 - ⟪(p : E), (v : E)⟫ * h3
      rcases sq_eq_one_iff.1 hsq with h | h
      · exact Or.inl (sphereHeight_eq_one_iff.1 (by simpa using h))
      · exact Or.inr (Or.inl (sphereHeight_eq_neg_one_iff.1 (by simpa using h)))
    · -- Otherwise the multiplier is `2`.
      have hc2 : c = 2 := mul_right_cancel₀ hpu (by linarith)
      subst hc2
      exact Or.inr (Or.inr ⟨by linarith, by linear_combination (-1 / 2 : ℝ) * h3 - (t / 4) * h2⟩)
  · rintro (rfl | rfl | ⟨h1, h2⟩)
    · refine Submodule.mem_span_singleton.2 ⟨t, ?_⟩
      simp [huv, real_inner_comm]
    · refine Submodule.mem_span_singleton.2 ⟨-t, ?_⟩
      simp [huv, real_inner_comm, inner_neg_left]
    · exact mem_span_of_sphereHeight_eq huv h1 h2

/-- **The critical set of `hᵤ² + t hᵥ`.** For orthogonal unit vectors `u`, `v` and `t ≠ 0`, the
critical points are the poles `±v` and the points with `hᵥ = t / 2` and `hᵤ² = 1 - t² / 4`. -/
theorem criticalPoints_sphereHeight_sq_add_smul_sphereHeight (huv : ⟪(u : E), (v : E)⟫ = 0)
    (ht : t ≠ 0) :
    criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) =
      {v, -v} ∪ {x | sphereHeight v x = t / 2 ∧ sphereHeight u x ^ 2 = 1 - t ^ 2 / 4} := by
  ext x
  rw [mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht]
  simp [or_assoc]

/-! ### The critical Hessian and the Morse indices -/

private theorem contMDiff_sphereHeight_sq_add_smul_sphereHeight :
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (sphereHeight u ^ 2 + t • sphereHeight v) := by
  rw [sphereHeight_sq_add_smul_sphereHeight_eq]
  exact contDiff_ambient.contMDiff.comp contMDiff_coe_sphere

/-- **The critical Hessian of `hᵤ² + t hᵥ`.** At a critical point `p`, with `ι` the differential of
the inclusion of the sphere, the critical Hessian is
`2 ⟪ι a, u⟫ ⟪ι b, u⟫ - μ ⟪ι a, ι b⟫`, where `μ = 2 hᵤ(p)² + t hᵥ(p)` is the Lagrange multiplier. -/
theorem criticalHessian_sphereHeight_sq_add_smul_sphereHeight_apply
    (hp : p ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v))
    (a b : TangentSpace (𝓡 n) p) :
    criticalHessian (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) p a b =
      2 * ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p a, (u : E)⟫ *
          ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p b, (u : E)⟫ -
        (2 * sphereHeight u p ^ 2 + t * sphereHeight v p) *
          ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p a,
            mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p b⟫ := by
  rw [sphereHeight_sq_add_smul_sphereHeight_eq] at hp ⊢
  rw [criticalHessian_comp_coe_sphere_apply (contDiff_ambient.contDiffAt.of_le (by simp)) hp,
    fderiv_fderiv_ambient, (hasFDerivAt_ambient (p : E)).fderiv]
  simp only [innerSL_apply_apply, inner_add_left, inner_smul_left, RCLike.conj_to_real,
    sphereHeight_apply, real_inner_comm (p : E) (u : E), real_inner_comm (p : E) (v : E)]
  ring

/-- The tangent vector at the north pole `v` which the inclusion sends to `u`. -/
private theorem exists_mvfderiv_coe_sphere_eq (huv : ⟪(u : E), (v : E)⟫ = 0) :
    ∃ b : TangentSpace (𝓡 n) v, mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v b = u := by
  have h : (u : E) ∈ (ℝ ∙ (v : E))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by rw [real_inner_comm, huv])
  rw [← range_mvfderiv_subtypeVal (n := n) v] at h
  exact LinearMap.mem_range.1 h

/-- At the north pole the critical Hessian is `2 ⟪ι a, u⟫ ⟪ι b, u⟫ - t ⟪ι a, ι b⟫`. -/
private theorem criticalHessian_sphereHeight_sq_add_smul_sphereHeight_self
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht : t ≠ 0) (a b : TangentSpace (𝓡 n) v) :
    criticalHessian (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) v a b =
      2 * ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v a, (u : E)⟫ *
          ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v b, (u : E)⟫ -
        t * ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v a,
          mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v b⟫ := by
  rw [criticalHessian_sphereHeight_sq_add_smul_sphereHeight_apply
    ((mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht).2 (Or.inl rfl)),
    sphereHeight_eq_zero_of_inner_eq_zero huv, sphereHeight_self]
  ring

/-- **The north pole of `hᵤ² + t hᵥ`.** For `t ≠ 0, 2`, the north pole `v` is a nondegenerate
critical point. -/
theorem isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_self
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : t ≠ 0) (ht₂ : t ≠ 2) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) v := by
  refine .of_nondegenerate_criticalHessian
    ((contMDiff_sphereHeight_sq_add_smul_sphereHeight v).of_le (by simp))
    ((mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀).2 (Or.inl rfl))
    fun a h ↦ ?_
  obtain ⟨b, hb⟩ := exists_mvfderiv_coe_sphere_eq (n := n) huv
  have hu : ⟪(u : E), (u : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere u)
  set x := mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v a
  -- Pairing with `b` gives `(2 - t) ⟪x, u⟫ = 0`; then pairing with `a` gives `-t ‖x‖² = 0`.
  have h1 := h b
  rw [criticalHessian_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀, hb, hu] at h1
  have hxu : ⟪x, (u : E)⟫ = 0 := by
    have : (2 - t) * ⟪x, (u : E)⟫ = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht₂.symm)
  have h2 := h a
  rw [criticalHessian_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀, hxu,
    real_inner_self_eq_norm_sq] at h2
  have hx : x = 0 := by
    have : t * ‖x‖ ^ 2 = 0 := by linear_combination -h2
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this).resolve_left ht₀))
  exact injective_mvfderiv_subtypeVal_sphere v (hx.trans (map_zero _).symm)

/-- **The saddle of `hᵤ² + t hᵥ`.** For `0 < t < 2`, the north pole `v` has Morse index `n - 1`, so
it is a saddle when `n ≥ 2`: the critical Hessian is positive along the tangent vector `u` and
negative definite on the tangent vectors orthogonal to `u`. -/
theorem manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : 0 < t) (ht₂ : t < 2) :
    manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) v = n - 1 := by
  obtain ⟨b, hb⟩ := exists_mvfderiv_coe_sphere_eq (n := n) huv
  have hu : ⟪(u : E), (u : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere u)
  have hb0 : b ≠ 0 := by
    rintro rfl
    simpa using congrArg norm hb
  have hfin : finrank ℝ (TangentSpace (𝓡 n) v) = n := finrank_euclideanSpace_fin
  -- The Hessian is positive definite on the line through `b`.
  have hpos := finrank_add_manifoldMorseIndex_le_of_posDef_criticalHessian
    (f := sphereHeight u ^ 2 + t • sphereHeight v) (W := ℝ ∙ b) fun z hz ↦ by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 z.property
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hz (Subtype.ext (by simpa using hc.symm))
      simp only [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply,
        ContinuousLinearMap.toBilinForm_apply]
      rw [← hc, criticalHessian_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀.ne', map_smul,
        hb]
      simp only [inner_smul_left, inner_smul_right, hu, RCLike.conj_to_real]
      nlinarith [mul_pos (pow_pos (abs_pos.2 hc0) 2) (sub_pos.2 ht₂), sq_abs c]
  rw [finrank_span_singleton hb0, finrank_euclideanSpace_fin] at hpos
  -- The Hessian is negative definite on the tangent vectors orthogonal to `u`.
  let ℓ : Module.Dual ℝ (TangentSpace (𝓡 n) v) :=
    (innerSL ℝ (u : E)).toLinearMap ∘ₗ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v).toLinearMap
  have hℓ : ℓ ≠ 0 := fun h ↦ by
    have := congrArg (fun L : Module.Dual ℝ _ ↦ L b) h
    simp [ℓ, hb] at this
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
  have hneg := finrank_le_manifoldMorseIndex_of_negDef_criticalHessian
    (f := sphereHeight u ^ 2 + t • sphereHeight v) (W := LinearMap.ker ℓ) fun z hz ↦ by
      have hzu : ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v z, (u : E)⟫ = 0 := by
        rw [real_inner_comm]
        simpa [ℓ, LinearMap.mem_ker] using z.property
      have hx := (map_ne_zero_iff _ (injective_mvfderiv_subtypeVal_sphere v)).2
        fun h : (z : TangentSpace (𝓡 n) v) = 0 ↦ hz (Subtype.ext h)
      simp only [QuadraticMap.restrict_apply, neg_apply,
        LinearMap.BilinMap.toQuadraticMap_apply, ContinuousLinearMap.toBilinForm_apply,
        criticalHessian_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀.ne', hzu,
        real_inner_self_eq_norm_sq]
      nlinarith [mul_pos ht₀ (pow_pos (norm_pos_iff.2 hx) 2)]
  rw [hfin] at hker
  omega

/-- The south pole is a critical point with Hessian `2 ⟪ι a, u⟫² + t ‖ι a‖²`, positive definite for
`0 < t`. -/
private theorem criticalHessian_sphereHeight_sq_add_smul_sphereHeight_neg_self_pos
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht : 0 < t) {a : TangentSpace (𝓡 n) (-v)} (ha : a ≠ 0) :
    0 < criticalHessian (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) (-v) a a := by
  have hcrit : -v ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) :=
    (mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht.ne').2
      (Or.inr (Or.inl rfl))
  have hx := (map_ne_zero_iff _ (injective_mvfderiv_subtypeVal_sphere (-v))).2 ha
  rw [criticalHessian_sphereHeight_sq_add_smul_sphereHeight_apply hcrit, sphereHeight_neg_self]
  have hvu : sphereHeight u (-v) = 0 := by simp [inner_neg_left, real_inner_comm, huv]
  rw [hvu, real_inner_self_eq_norm_sq]
  nlinarith [mul_pos ht (pow_pos (norm_pos_iff.2 hx) 2),
    mul_self_nonneg ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (-v) a, (u : E)⟫]

omit [Fact (finrank ℝ E = n + 1)] in
/-- Replacing `v` and `t` by `-v` and `-t` does not change `hᵤ² + t hᵥ`. -/
private theorem sphereHeight_sq_add_neg_smul_sphereHeight_neg :
    sphereHeight u ^ 2 + (-t) • sphereHeight (-v) = sphereHeight u ^ 2 + t • sphereHeight v := by
  rw [sphereHeight_neg, neg_smul_neg]

/-- **The south pole of `hᵤ² + t hᵥ`.** For orthogonal unit vectors `u`, `v` and `t ≠ 0, -2`, the
south pole `-v` is a nondegenerate critical point. -/
theorem isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_neg_self
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht₀ : t ≠ 0) (ht₂ : t ≠ -2) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) (-v) := by
  have h := isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_self
    (n := n) (u := u) (v := -v) (t := -t) (by simpa [inner_neg_right] using huv)
    (neg_ne_zero.2 ht₀) fun h ↦ ht₂ (by linarith)
  rwa [sphereHeight_sq_add_neg_smul_sphereHeight_neg] at h

/-- **The minimum of `hᵤ² + t hᵥ`.** For `0 < t`, the south pole `-v` has Morse index `0`. -/
theorem manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self
    (huv : ⟪(u : E), (v : E)⟫ = 0) (ht : 0 < t) :
    manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) (-v) = 0 :=
  (isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_neg_self huv
    ht.ne' (by linarith)).manifoldMorseIndex_eq_zero_iff.2 fun _ ha ↦
      criticalHessian_sphereHeight_sq_add_smul_sphereHeight_neg_self_pos huv ht ha

/-- At a point with `hᵥ = t / 2` and `hᵤ² = 1 - t² / 4`, where `t² ≠ 4`, the critical Hessian is
negative definite: it is `2 ⟪ι a, u⟫² - 2 ‖ι a‖²`, and `ι a` is orthogonal to `p`, which has a
nonzero component along `u`. -/
private theorem criticalHessian_sphereHeight_sq_add_smul_sphereHeight_neg
    (huv : ⟪(u : E), (v : E)⟫ = 0) (h1 : sphereHeight v p = t / 2)
    (h2 : sphereHeight u p ^ 2 = 1 - t ^ 2 / 4) (ht : t ^ 2 ≠ 4) {a : TangentSpace (𝓡 n) p}
    (ha : a ≠ 0) :
    criticalHessian (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) p a a < 0 := by
  have hcrit := mem_criticalPoints_of_sphereHeight_eq (n := n) huv h1 h2
  have hpu : ⟪(p : E), (u : E)⟫ ≠ 0 := fun h ↦ ht (by
    rw [sphereHeight_apply, h] at h2
    linarith)
  have hu : ‖(u : E)‖ = 1 := norm_eq_of_mem_sphere u
  have hpx := inner_coe_mvfderiv_subtypeVal_sphere p a
  rw [criticalHessian_sphereHeight_sq_add_smul_sphereHeight_apply hcrit, h1, h2,
    real_inner_self_eq_norm_sq, show 2 * (1 - t ^ 2 / 4) + t * (t / 2) = 2 by ring]
  set x := mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p a
  -- The component of `x` orthogonal to `u` is nonzero, since `x ⊥ p` and `⟪p, u⟫ ≠ 0`.
  have hy : ‖x - ⟪x, (u : E)⟫ • (u : E)‖ ^ 2 = ‖x‖ ^ 2 - ⟪x, (u : E)⟫ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, hu, Real.norm_eq_abs, sq_abs,
      one_pow]
    ring
  have hy0 : x - ⟪x, (u : E)⟫ • (u : E) ≠ 0 := fun h0 ↦ by
    have hx : x = ⟪x, (u : E)⟫ • (u : E) := sub_eq_zero.1 h0
    rw [hx, inner_smul_right] at hpx
    have hxu : ⟪x, (u : E)⟫ = 0 := (mul_eq_zero.1 hpx).resolve_right hpu
    exact (map_ne_zero_iff _ (injective_mvfderiv_subtypeVal_sphere p)).2 ha
      (hx.trans (by rw [hxu, zero_smul]))
  nlinarith [pow_pos (norm_pos_iff.2 hy0) 2]

/-- **The maxima of `hᵤ² + t hᵥ`.** For `t² ≠ 4`, a point with `hᵥ = t / 2` and
`hᵤ² = 1 - t² / 4` is a nondegenerate critical point. -/
theorem isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_of_eq
    (huv : ⟪(u : E), (v : E)⟫ = 0) (h1 : sphereHeight v p = t / 2)
    (h2 : sphereHeight u p ^ 2 = 1 - t ^ 2 / 4) (ht : t ^ 2 ≠ 4) :
    IsManifoldNondegenerateCriticalPoint (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) p := by
  refine .of_nondegenerate_criticalHessian
    ((contMDiff_sphereHeight_sq_add_smul_sphereHeight p).of_le (by simp))
    (mem_criticalPoints_of_sphereHeight_eq huv h1 h2) fun a h ↦ by_contra fun ha ↦
      (criticalHessian_sphereHeight_sq_add_smul_sphereHeight_neg huv h1 h2 ht ha).ne (h a)

/-- **The maxima of `hᵤ² + t hᵥ`.** For `t² ≠ 4`, a point with `hᵥ = t / 2` and
`hᵤ² = 1 - t² / 4` has Morse index `n`. -/
theorem manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_of_eq
    (huv : ⟪(u : E), (v : E)⟫ = 0) (h1 : sphereHeight v p = t / 2)
    (h2 : sphereHeight u p ^ 2 = 1 - t ^ 2 / 4) (ht : t ^ 2 ≠ 4) :
    manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) p = n := by
  rw [manifoldMorseIndex_eq_finrank_iff.2 fun _ ha ↦
    criticalHessian_sphereHeight_sq_add_smul_sphereHeight_neg huv h1 h2 ht ha,
    finrank_euclideanSpace_fin]

/-- **`hᵤ² + t hᵥ` is a Morse function** on the sphere, for orthogonal unit vectors `u`, `v` and
`t ≠ 0, ±2`. -/
theorem isMorse_sphereHeight_sq_add_smul_sphereHeight (huv : ⟪(u : E), (v : E)⟫ = 0)
    (ht₀ : t ≠ 0) (ht₂ : t ^ 2 ≠ 4) :
    IsMorse (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) := by
  rw [← isMorseOn_univ, isMorseOn_iff_criticalPoints]
  refine ⟨contMDiff_sphereHeight_sq_add_smul_sphereHeight.contMDiffOn, fun x _ hx ↦ ?_⟩
  rcases (mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀).1 hx with
    rfl | rfl | ⟨h1, h2⟩
  · exact isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_self huv
      ht₀ (by rintro rfl; norm_num at ht₂)
  · exact isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_neg_self huv
      ht₀ (by rintro rfl; norm_num at ht₂)
  · exact isManifoldNondegenerateCriticalPoint_sphereHeight_sq_add_smul_sphereHeight_of_eq huv h1
      h2 ht₂

/-! ### The critical counts -/

omit [Fact (finrank ℝ E = n + 1)] in
/-- For `t² < 4` there are exactly two points of the sphere with `hᵥ = t / 2` and
`hᵤ² = 1 - t² / 4`, namely `±√(1 - t² / 4) u + (t / 2) v`. -/
private theorem encard_setOf_sphereHeight_eq (huv : ⟪(u : E), (v : E)⟫ = 0) (ht : t ^ 2 < 4) :
    {x : sphere (0 : E) 1 | sphereHeight v x = t / 2 ∧ sphereHeight u x ^ 2 = 1 - t ^ 2 / 4}.encard
      = 2 := by
  have hu : ⟪(u : E), (u : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere u)
  have hv : ⟪(v : E), (v : E)⟫ = 1 := inner_self_eq_one_of_norm_eq_one (norm_eq_of_mem_sphere v)
  have hvu : ⟪(v : E), (u : E)⟫ = 0 := by rw [real_inner_comm, huv]
  set s := √(1 - t ^ 2 / 4)
  have hs : s ^ 2 = 1 - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  -- The points `c u + (t / 2) v` with `c² = 1 - t² / 4` lie on the sphere.
  have hmem (c : ℝ) (hc : c ^ 2 = 1 - t ^ 2 / 4) :
      c • (u : E) + (t / 2) • (v : E) ∈ sphere (0 : E) 1 := by
    have hn : ‖c • (u : E) + (t / 2) • (v : E)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hu, hv, huv,
        hvu, RCLike.conj_to_real]
      linear_combination hc
    rw [mem_sphere_zero_iff_norm]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [hn, one_pow])
  let P (c : ℝ) (hc : c ^ 2 = 1 - t ^ 2 / 4) : sphere (0 : E) 1 := ⟨_, hmem c hc⟩
  have hneg : (-s) ^ 2 = 1 - t ^ 2 / 4 := by rw [neg_sq, hs]
  rw [encard_eq_two]
  refine ⟨P s hs, P (-s) hneg, fun h ↦ ?_, ?_⟩
  · have := congrArg (fun x : sphere (0 : E) 1 ↦ ⟪(x : E), (u : E)⟫) h
    simp only [P, inner_add_left, inner_smul_left, hu, hvu, RCLike.conj_to_real] at this
    linarith
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have hx := coe_eq_sphereHeight_smul_add_sphereHeight_smul huv (x := x) (by rw [h1, h2]; ring)
    rw [h1] at hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h2.trans hs.symm) with h | h
    · exact Or.inl (Subtype.ext (by rw [hx, h]))
    · exact Or.inr (Subtype.ext (by rw [hx, h]))
  · rintro (rfl | rfl) <;>
      simp [P, sphereHeight_apply, inner_add_left, inner_smul_left, huv, hvu, hs]

/-- **The critical counts of `hᵤ² + t hᵥ`.** For orthogonal unit vectors `u`, `v`,
`0 < |t| < 2` and `n ≥ 2`, the function `hᵤ² + t hᵥ` on `Sⁿ` has one critical point of index `0`,
one of index `n - 1` and two of index `n`. -/
theorem criticalCount_sphereHeight_sq_add_smul_sphereHeight (huv : ⟪(u : E), (v : E)⟫ = 0)
    (hn : 2 ≤ n) (ht : t ≠ 0) (ht₂ : t ^ 2 < 4) (j : ℕ) :
    criticalCount (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) j =
      if j = n then 2 else if j = 0 ∨ j = n - 1 then 1 else 0 := by
  -- Replacing `v` and `t` by `-v` and `-t` reduces to `0 < t`.
  wlog ht₀ : 0 < t generalizing v t
  · rw [← sphereHeight_sq_add_neg_smul_sphereHeight_neg]
    exact this (by simpa [inner_neg_right] using huv) (neg_ne_zero.2 ht) (by rwa [neg_sq])
      (by have := ht.lt_or_gt; grind)
  replace ht₂ : t < 2 := by nlinarith
  -- The critical points of index `j`, read off the classification and the three index formulas.
  have hmem (x : sphere (0 : E) 1) :
      (x ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) ∧
          manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = j) ↔
        (x = v ∧ j = n - 1) ∨ (x = -v ∧ j = 0) ∨
          ((sphereHeight v x = t / 2 ∧ sphereHeight u x ^ 2 = 1 - t ^ 2 / 4) ∧ j = n) := by
    rw [mem_criticalPoints_sphereHeight_sq_add_smul_sphereHeight_iff huv ht₀.ne']
    constructor
    · rintro ⟨rfl | rfl | hx, rfl⟩
      · exact Or.inl ⟨rfl, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀
          ht₂⟩
      · exact Or.inr (Or.inl ⟨rfl,
          manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self huv ht₀⟩)
      · exact Or.inr (Or.inr ⟨hx, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_of_eq
          huv hx.1 hx.2 (by nlinarith)⟩)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hx, rfl⟩)
      · exact ⟨Or.inl rfl, manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_self huv ht₀
          ht₂⟩
      · exact ⟨Or.inr (Or.inl rfl),
          manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_neg_self huv ht₀⟩
      · exact ⟨Or.inr (Or.inr hx), manifoldMorseIndex_sphereHeight_sq_add_smul_sphereHeight_of_eq
          huv hx.1 hx.2 (by nlinarith)⟩
  rw [criticalCount_def, show {x ∈ criticalPoints (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v)
    | manifoldMorseIndex (𝓡 n) (sphereHeight u ^ 2 + t • sphereHeight v) x = j} =
      {x | (x = v ∧ j = n - 1) ∨ (x = -v ∧ j = 0) ∨
        ((sphereHeight v x = t / 2 ∧ sphereHeight u x ^ 2 = 1 - t ^ 2 / 4) ∧ j = n)} from
      Set.ext hmem]
  split_ifs with hj hj'
  · subst hj
    have h1 : j ≠ j - 1 := by omega
    have h2 : j ≠ 0 := by omega
    simpa [h1, h2] using encard_setOf_sphereHeight_eq huv (by nlinarith)
  · rcases hj' with rfl | rfl
    · have h1 : 0 ≠ n - 1 := by omega
      simp [h1, hj]
    · have h1 : n - 1 ≠ 0 := by omega
      simp [h1, hj]
  · simp only [not_or] at hj'
    simp [hj, hj'.1, hj'.2]

/-- **Two minima, a saddle and a maximum.** For orthogonal unit vectors `u`, `v`, `0 < |t| < 2`
and `n ≥ 2`, the function `-(hᵤ² + t hᵥ)` on `Sⁿ` has two critical points of index `0`, one of
index `1` and one of index `n`. On `S²` its critical counts are `(2, 1, 1)`, while those of
`hᵤ² + t hᵥ` are `(1, 1, 2)`. -/
theorem criticalCount_neg_sphereHeight_sq_add_smul_sphereHeight (huv : ⟪(u : E), (v : E)⟫ = 0)
    (hn : 2 ≤ n) (ht₀ : t ≠ 0) (ht₂ : t ^ 2 < 4) (j : ℕ) :
    criticalCount (𝓡 n) (-(sphereHeight u ^ 2 + t • sphereHeight v)) j =
      if j = 0 then 2 else if j = 1 ∨ j = n then 1 else 0 := by
  rcases le_or_gt j n with hj | hj
  · rw [(isMorse_sphereHeight_sq_add_smul_sphereHeight huv ht₀ ht₂.ne).criticalCount_neg
      (by rwa [finrank_euclideanSpace_fin]), finrank_euclideanSpace_fin,
      criticalCount_sphereHeight_sq_add_smul_sphereHeight huv hn ht₀ ht₂]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [criticalCount_eq_zero_of_finrank_lt (by rwa [finrank_euclideanSpace_fin])]
    split_ifs <;> first | rfl | (exfalso; omega)

end TauCeti
