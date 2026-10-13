/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Semisimple
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap
public import TauCeti.Analysis.InnerProductSpace.Sylvester

/-!
# The dimension-free Davis–Kahan `sin Θ` theorem

Let `A` and `B` be bounded operators on an inner product space `E`, let `U` be invariant under `A`
and `W` invariant under `B`, with `B` symmetric. If the quadratic form of `A` on `U` lies above
that of `B` on `W` with a margin `g`,

  `(c + g) ‖u‖² ≤ re ⟪A u, u⟫` for `u ∈ U` and `re ⟪B w, w⟫ ≤ c ‖w‖²` for `w ∈ W`,

then `g ‖P_W P_U‖ ≤ ‖B - A‖`. Taking `W = Vᗮ` for a `B`-invariant subspace `V` bounds the directed
gap `‖P_{Vᗮ} P_U‖`, the operator norm of the directed sine from `U` towards `V`: for `g > 0`, the
`A`-invariant subspace `U` sticks out of the `B`-invariant subspace `V` by at most `‖B - A‖ / g`,
as long as the part of `A` on `U` stays separated by `g` from the part of `B` on `Vᗮ`. With the
separation hypotheses in both orientations, the sharp gap identity
`Submodule.projectionGap_eq_max` turns the two directed bounds into the bound
`g ‖P_U - P_V‖ ≤ ‖B - A‖` on the gap between `U` and `V`.

No completeness, finite dimension, or spectral theorem is used; the hypotheses are quadratic-form
bounds, which on invariant subspaces of symmetric operators on finite-dimensional spaces are
equivalent to spectral containment (`LinearMap.IsSymmetric.pointSpectrumIn_Iic_iff`,
`LinearMap.IsSymmetric.pointSpectrumIn_Ici_iff`). The theorem is a consequence of the separated
Sylvester bound
`ContinuousLinearMap.mul_norm_le_norm_sylvester_apply_of_re_inner_le_of_le_re_inner`.

## Main results

* `Submodule.le_re_inner_comp_starProjection_add_smul_apply_self`,
  `Submodule.re_inner_comp_starProjection_add_smul_apply_self_le`: extending an operator from an
  invariant subspace `U` by the scalar `r` on `Uᗮ` preserves a lower (upper) bound `r` on its
  quadratic form.
* `Submodule.mul_norm_starProjection_comp_starProjection_le_norm_sub`: the directed `sin Θ` bound
  `g ‖P_W P_U‖ ≤ ‖B - A‖`.
* `Submodule.mul_directedProjectionGap_le_norm_sub`: the same bound for the directed gap
  `‖P_{Vᗮ} P_U‖` between an `A`-invariant subspace `U` and a `B`-invariant subspace `V`.
* `Submodule.mul_projectionGap_le_norm_sub`: under the separation hypotheses in both orientations,
  `g ‖P_U - P_V‖ ≤ ‖B - A‖`.
* `Submodule.norm_starProjection_comp_starProjection_le_norm_sub_div`,
  `Submodule.directedProjectionGap_le_norm_sub_div`, `Submodule.projectionGap_le_norm_sub_div`:
  for `g > 0`, the same bounds in the form `‖·‖ ≤ ‖B - A‖ / g`.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.3.

## Acknowledgements

Material in the Sylvester and `sin Θ` lineage was adapted from the
[Spectra Formalization Project](https://github.com/adambornemann-glitch/Spectra)
(Adam Bornemann; Apache-2.0) at upstream revision `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
-/

public section

namespace Submodule

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- If `U` is invariant under `A` and the quadratic form of `A` on `U` is bounded below by `r`, then
the quadratic form of `A P_U + r P_{Uᗮ}` is bounded below by `r` on all of `E`. -/
theorem le_re_inner_comp_starProjection_add_smul_apply_self {A : E →L[𝕜] E}
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (hU : ∀ x ∈ U, A x ∈ U) {r : ℝ}
    (hA : ∀ x ∈ U, r * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) (x : E) :
    r * ‖x‖ ^ 2 ≤
      RCLike.re ⟪(A ∘L U.starProjection + (r : 𝕜) • Uᗮ.starProjection) x, x⟫_𝕜 := by
  set u := U.starProjection x
  set v := Uᗮ.starProjection x
  have hu : u ∈ U := U.starProjection_apply_mem x
  have hv : v ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  -- Split `x = u + v` along `U ⊕ Uᗮ`; the cross terms vanish because `A u ∈ U`.
  have hx : x = u + v := (U.starProjection_add_starProjection_orthogonal x).symm
  have hAuv : ⟪A u, v⟫_𝕜 = 0 := inner_right_of_mem_orthogonal (hU u hu) hv
  have hvu : ⟪v, u⟫_𝕜 = 0 := inner_left_of_mem_orthogonal hu hv
  have hre : RCLike.re ⟪(A ∘L U.starProjection + (r : 𝕜) • Uᗮ.starProjection) x, x⟫_𝕜 =
      RCLike.re ⟪A u, u⟫_𝕜 + r * ‖v‖ ^ 2 := by
    have happ : (A ∘L U.starProjection + (r : 𝕜) • Uᗮ.starProjection) x = A u + (r : 𝕜) • v := by
      simp only [add_apply, comp_apply, smul_apply, u, v]
    rw [happ]
    conv_lhs => rw [hx]
    simp [inner_add_left, inner_add_right, inner_smul_left, hAuv, hvu, inner_self_eq_norm_sq_to_K]
  rw [hre, norm_sq_eq_add_norm_sq_starProjection x U, mul_add]
  exact add_le_add_left (hA u hu) _

/-- If `W` is invariant under `B` and the quadratic form of `B` on `W` is bounded above by `r`, then
the quadratic form of `B P_W + r P_{Wᗮ}` is bounded above by `r` on all of `E`. -/
theorem re_inner_comp_starProjection_add_smul_apply_self_le {B : E →L[𝕜] E}
    (W : Submodule 𝕜 E) [W.HasOrthogonalProjection] (hW : ∀ x ∈ W, B x ∈ W) {r : ℝ}
    (hB : ∀ x ∈ W, RCLike.re ⟪B x, x⟫_𝕜 ≤ r * ‖x‖ ^ 2) (x : E) :
    RCLike.re ⟪(B ∘L W.starProjection + (r : 𝕜) • Wᗮ.starProjection) x, x⟫_𝕜 ≤
      r * ‖x‖ ^ 2 := by
  -- Apply the lower bound to `-B` and the bound `-r`.
  have h := W.le_re_inner_comp_starProjection_add_smul_apply_self (A := -B) (r := -r)
    (fun x hx ↦ by simpa using W.neg_mem (hW x hx))
    (fun x hx ↦ by simpa [inner_neg_left] using hB x hx) x
  have heq : (-B) ∘L W.starProjection + ((-r : ℝ) : 𝕜) • Wᗮ.starProjection =
      -(B ∘L W.starProjection + (r : 𝕜) • Wᗮ.starProjection) := by
    rw [neg_comp, RCLike.ofReal_neg, neg_smul, neg_add]
  rw [heq, neg_apply, inner_neg_left, map_neg] at h
  linarith

/-- **The dimension-free directed Davis–Kahan `sin Θ` theorem.** Let `U` be invariant under `A`
and `W` invariant under the symmetric operator `B`. If the quadratic form of `A` on `U` is at
least `c + g` and that of `B` on `W` is at most `c`, then `g ‖P_W P_U‖ ≤ ‖B - A‖`. For `g > 0`
this bounds `‖P_W P_U‖` by `‖B - A‖ / g`. Neither completeness nor finite dimension is assumed. -/
theorem mul_norm_starProjection_comp_starProjection_le_norm_sub {A B : E →L[𝕜] E}
    (U W : Submodule 𝕜 E) [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U) (hW : ∀ x ∈ W, B x ∈ W) {c g : ℝ}
    (hAU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBW : ∀ x ∈ W, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    g * ‖W.starProjection ∘L U.starProjection‖ ≤ ‖B - A‖ := by
  -- Reduce to the separated Sylvester bound. The extensions `A' = A P_U + (c + g) P_{Uᗮ}` and
  -- `B' = B P_W + c P_{Wᗮ}` have quadratic forms bounded below by `c + g` and above by `c` on all
  -- of `E`, and `X = P_W P_U` satisfies `B' X - X A' = P_W (B - A) P_U`.
  -- `Wᗮ` is invariant under the symmetric operator `B`, so `B` commutes with `P_W`.
  have hW' : ∀ x ∈ Wᗮ, B x ∈ Wᗮ := fun x hx ↦
    LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hB (p := W)
      (fun y hy ↦ hW y hy) hx
  have hcomm (y : E) : B (W.starProjection y) = W.starProjection (B y) := by
    have h := (IsIdempotentElem.commute_iff W.isIdempotentElem_starProjection (T := B)).mpr
      ⟨by rw [range_starProjection]; exact fun y hy ↦ hW y hy,
        by rw [ker_starProjection]; exact fun y hy ↦ hW' y hy⟩
    simpa using congr($(h.eq) y).symm
  -- On `X = P_W P_U`, the Sylvester operator of the extensions `B P_W + c P_{Wᗮ}` and
  -- `A P_U + (c + g) P_{Uᗮ}` is `P_W (B - A) P_U`.
  set A' := A ∘L U.starProjection + ((c + g : ℝ) : 𝕜) • Uᗮ.starProjection
  set B' := B ∘L W.starProjection + (c : 𝕜) • Wᗮ.starProjection
  set X := W.starProjection ∘L U.starProjection
  have hsyl (x : E) :
      B'.sylvester A' X x = W.starProjection ((B - A) (U.starProjection x)) := by
    have hmem : W.starProjection (U.starProjection x) ∈ W := W.starProjection_apply_mem _
    simp only [B', A', X, sylvester_apply, sub_apply, comp_apply, add_apply, smul_apply, map_add,
      map_smul]
    rw [starProjection_eq_self_iff.mpr hmem, starProjection_orthogonal_apply_eq_zero hmem,
      starProjection_eq_self_iff.mpr (hU _ (U.starProjection_apply_mem x)),
      (U.starProjection_apply_eq_zero_iff).mpr (Uᗮ.starProjection_apply_mem x)]
    simp only [map_zero, smul_zero, add_zero]
    rw [hcomm, map_sub]
  have hbound : ‖B'.sylvester A' X‖ ≤ ‖B - A‖ := by
    refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    rw [hsyl]
    calc ‖W.starProjection ((B - A) (U.starProjection x))‖
        ≤ ‖(B - A) (U.starProjection x)‖ := W.norm_starProjection_apply_le _
      _ ≤ ‖B - A‖ * ‖U.starProjection x‖ := (B - A).le_opNorm _
      _ ≤ ‖B - A‖ * ‖x‖ := by gcongr; exact U.norm_starProjection_apply_le x
  exact (mul_norm_le_norm_sylvester_apply_of_re_inner_le_of_le_re_inner
    (W.re_inner_comp_starProjection_add_smul_apply_self_le hW hBW)
    (U.le_re_inner_comp_starProjection_add_smul_apply_self hU hAU) X).trans hbound

/-- The directed Davis–Kahan `sin Θ` theorem in division form: for `g > 0`, under the hypotheses
of `mul_norm_starProjection_comp_starProjection_le_norm_sub`, `‖P_W P_U‖ ≤ ‖B - A‖ / g`. -/
theorem norm_starProjection_comp_starProjection_le_norm_sub_div {A B : E →L[𝕜] E}
    (U W : Submodule 𝕜 E) [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U) (hW : ∀ x ∈ W, B x ∈ W) {c g : ℝ}
    (hg : 0 < g) (hAU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBW : ∀ x ∈ W, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    ‖W.starProjection ∘L U.starProjection‖ ≤ ‖B - A‖ / g :=
  (le_div_iff₀' hg).mpr
    (U.mul_norm_starProjection_comp_starProjection_le_norm_sub W hB hU hW hAU hBW)

/-- **The directed Davis–Kahan `sin Θ` theorem for the directed gap.** Let `U` be invariant
under `A` and `V` invariant under the symmetric operator `B`. If the quadratic form of `A` on `U`
is at least `c + g` and that of `B` on `Vᗮ` is at most `c`, then the directed gap
`‖P_{Vᗮ} P_U‖` from `U` to `V` satisfies `g ‖P_{Vᗮ} P_U‖ ≤ ‖B - A‖`. -/
theorem mul_directedProjectionGap_le_norm_sub {A B : E →L[𝕜] E}
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {c g : ℝ}
    (hAU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBV : ∀ x ∈ Vᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    g * directedProjectionGap U V ≤ ‖B - A‖ := by
  have hV' : ∀ x ∈ Vᗮ, B x ∈ Vᗮ := fun x hx ↦
    LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule hB (p := V)
      (fun y hy ↦ hV y hy) hx
  rw [directedProjectionGap_def]
  exact U.mul_norm_starProjection_comp_starProjection_le_norm_sub Vᗮ hB hU hV' hAU hBV

/-- The directed Davis–Kahan `sin Θ` theorem for the directed gap in division form: for `g > 0`,
under the hypotheses of `mul_directedProjectionGap_le_norm_sub`, the directed gap from `U` to `V`
is at most `‖B - A‖ / g`. -/
theorem directedProjectionGap_le_norm_sub_div {A B : E →L[𝕜] E}
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {c g : ℝ}
    (hg : 0 < g) (hAU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBV : ∀ x ∈ Vᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    directedProjectionGap U V ≤ ‖B - A‖ / g :=
  (le_div_iff₀' hg).mpr (U.mul_directedProjectionGap_le_norm_sub V hB hU hV hAU hBV)

/-- **The dimension-free Davis–Kahan `sin Θ` theorem for the gap.** Let `U` be invariant under
the symmetric operator `A` and `V` invariant under the symmetric operator `B`. Suppose that the
quadratic form of `A` on `U` is at least `c + g` while that of `B` on `Vᗮ` is at most `c`, and
that the quadratic form of `B` on `V` is at least `c' + g` while that of `A` on `Uᗮ` is at
most `c'`. Then the gap between `U` and `V` satisfies `g ‖P_U - P_V‖ ≤ ‖B - A‖`. -/
theorem mul_projectionGap_le_norm_sub {A B : E →L[𝕜] E}
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {c c' g : ℝ}
    (hAU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBV : ∀ x ∈ Vᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hBV' : ∀ x ∈ V, (c' + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hAU' : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ c' * ‖x‖ ^ 2) :
    g * projectionGap U V ≤ ‖B - A‖ := by
  have h₁ := U.mul_directedProjectionGap_le_norm_sub V hB hU hV hAU hBV
  have h₂ := V.mul_directedProjectionGap_le_norm_sub U hA hV hU hBV' hAU'
  rw [norm_sub_rev] at h₂
  rw [projectionGap_eq_max]
  rcases le_total (directedProjectionGap U V) (directedProjectionGap V U) with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

/-- The Davis–Kahan `sin Θ` theorem for the gap in division form: for `g > 0`, under the
hypotheses of `mul_projectionGap_le_norm_sub`, `‖P_U - P_V‖ ≤ ‖B - A‖ / g`. -/
theorem projectionGap_le_norm_sub_div {A B : E →L[𝕜] E}
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {c c' g : ℝ}
    (hg : 0 < g) (hAU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBV : ∀ x ∈ Vᗮ, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hBV' : ∀ x ∈ V, (c' + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hAU' : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ c' * ‖x‖ ^ 2) :
    projectionGap U V ≤ ‖B - A‖ / g :=
  (le_div_iff₀' hg).mpr (U.mul_projectionGap_le_norm_sub V hA hB hU hV hAU hBV hBV' hAU')

end Submodule
