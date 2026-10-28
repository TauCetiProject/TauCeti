/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Semisimple
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.Block
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
  -- `W` is invariant under the symmetric operator `B`, so `B` commutes with `P_W`.
  have hcomm (y : E) : B (W.starProjection y) = W.starProjection (B y) :=
    (hB.starProjection_apply_comm (fun y hy ↦ hW y hy) y).symm
  -- On `X = P_W P_U`, the Sylvester operator of the extensions `B P_W + c P_{Wᗮ}` and
  -- `A P_U + (c + g) P_{Uᗮ}` is `P_W (B - A) P_U`.
  set A' := A.reducedExtension U (c + g)
  set B' := B.reducedExtension W c
  set X := W.starProjection ∘L U.starProjection
  have hsyl (x : E) :
      B'.sylvester A' X x = W.starProjection ((B - A) (U.starProjection x)) := by
    have hmem : W.starProjection (U.starProjection x) ∈ W := W.starProjection_apply_mem _
    have hBapp : B' (W.starProjection (U.starProjection x)) =
        B (W.starProjection (U.starProjection x)) :=
      B.reducedExtension_apply_of_mem W c hmem
    have hAapp : A' x =
        A (U.starProjection x) + ((c + g : ℝ) : 𝕜) • Uᗮ.starProjection x :=
      A.reducedExtension_apply U (c + g) x
    simp only [sylvester_apply, sub_apply, X, comp_apply]
    rw [hBapp, hAapp]
    simp only [map_add, map_smul,
      starProjection_eq_self_iff.mpr (hU _ (U.starProjection_apply_mem x)),
      (U.starProjection_apply_eq_zero_iff).mpr (Uᗮ.starProjection_apply_mem x),
      smul_zero, add_zero]
    rw [hcomm, map_sub]
  have hbound : ‖B'.sylvester A' X‖ ≤ ‖B - A‖ := by
    refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    rw [hsyl]
    calc ‖W.starProjection ((B - A) (U.starProjection x))‖
        ≤ ‖(B - A) (U.starProjection x)‖ := W.norm_starProjection_apply_le _
      _ ≤ ‖B - A‖ * ‖U.starProjection x‖ := (B - A).le_opNorm _
      _ ≤ ‖B - A‖ * ‖x‖ := by gcongr; exact U.norm_starProjection_apply_le x
  exact (mul_norm_le_norm_sylvester_apply_of_re_inner_le_of_le_re_inner
    (B.re_inner_reducedExtension_self_le W hW
      (r := c) (κ := c) le_rfl hBW)
    (A.le_re_inner_reducedExtension_self U hU
      (r := c + g) (κ := c + g) le_rfl hAU) X).trans hbound

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
