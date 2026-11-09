/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Basic
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Projection

/-!
# The Davis–Kahan `sin 2Θ` theorem in unitarily invariant seminorms

Let `A` and `B` be symmetric operators on a finite-dimensional inner product space `E`, let `U` be
invariant under `A` and `V` invariant under `B`. Suppose that `A` has two ordered quadratic-form
bounds relative to `E = U ⊕ Uᗮ`:

  `re ⟪A z, z⟫ ≤ a ‖z‖²` on `Uᗮ`  and  `b ‖y‖² ≤ re ⟪A y, y⟫` on `U`.

Then the double-angle operator `2 P_{Uᗮ} P_V P_U` (`Submodule.sinTwoAngleOperator U V`), the
off-diagonal `U → Uᗮ` block of `2 P_V`, satisfies

  `(b - a) N(2 P_{Uᗮ} P_V P_U) ≤ 2 N(B - A)`

for every unitarily invariant seminorm `N`. When `U` and `V` have the same dimension, the
singular values of `2 P_{Uᗮ} P_V P_U` are the sines `sin 2θᵢ` of the doubled principal angles
between `U` and `V`, so this is Davis's `sin 2Θ` theorem. Only `A` is assumed to have a gap; no
spectral hypothesis is placed on `B`, and `V` is an arbitrary `B`-invariant subspace. The bound is
trivial when `b ≤ a`. For a one-dimensional `V` spanned by a unit eigenvector `x` of `B`, the
double-angle operator has rank at most one and operator norm `2 ‖P_U x‖ ‖P_{Uᗮ} x‖`, and the
operator-norm case recovers, in finite dimension, the per-eigenvector bound
`LinearMap.IsSymmetric.sin_two_theta_le`.

The argument compares the two Sylvester operators of `A` and `B`. Since `P_U` commutes with `A`
and `P_V` commutes with `B`, the operator `X = P_{Uᗮ} P_V P_U` satisfies

  `A X - X A = P_{Uᗮ} (P_V H - H P_V) P_U`,  where `H = B - A`.

The values of `X` lie in `Uᗮ`, where the eigenvalues of `A` lie in `[-‖A‖, a]`, and `X` vanishes
on `Uᗮ`, so it only sees the eigenvalues of `A` on `U`, which are at least `b`. The
interval/exterior Sylvester bound on invariant subspaces gives `(b - a) N(X) ≤ N(A X - X A)`, and
the checkerboard contraction `N(H P_V - P_V H) ≤ N(H)` bounds the right-hand side by `N(H)`.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.mul_map_sinTwoAngleOperator_le_two_mul_map_sub`: the
  `sin 2Θ` theorem `(b - a) N(2 P_{Uᗮ} P_V P_U) ≤ 2 N(B - A)`.

## References

* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl. **6** (1963),
  159–173.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
-/

public section

open Module
open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **The Davis–Kahan `sin 2Θ` theorem.** Let `A` and `B` be symmetric operators on a
finite-dimensional inner product space, let `U` be invariant under `A` and `V` invariant under
`B`. If `re ⟪A z, z⟫ ≤ a ‖z‖²` on `Uᗮ` and `b ‖y‖² ≤ re ⟪A y, y⟫` on `U`, then the double-angle
operator `2 P_{Uᗮ} P_V P_U` satisfies `(b - a) N(2 P_{Uᗮ} P_V P_U) ≤ 2 N(B - A)` for every
unitarily invariant seminorm `N`. No spectral hypothesis is placed on `B`. -/
theorem mul_map_sinTwoAngleOperator_le_two_mul_map_sub (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V) {a b : ℝ}
    (ha : ∀ z ∈ Uᗮ, RCLike.re ⟪A z, z⟫_𝕜 ≤ a * ‖z‖ ^ 2)
    (hb : ∀ y ∈ U, b * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜) :
    (b - a) * N (U.sinTwoAngleOperator V) ≤ 2 * N (B - A) := by
  have hU' : ∀ x ∈ Uᗮ, A x ∈ Uᗮ := fun _ hx ↦
    hA.orthogonalComplement_mem_invtSubmodule (p := U) (fun y hy ↦ hU y hy) hx
  have hcommU : ∀ y, U.starProjection (A y) = A (U.starProjection y) :=
    hA.starProjection_apply_comm fun y hy ↦ hU y hy
  have hcommU' : ∀ y, Uᗮ.starProjection (A y) = A (Uᗮ.starProjection y) :=
    hA.starProjection_apply_comm fun y hy ↦ hU' y hy
  have hcommV : ∀ y, V.starProjection (B y) = B (V.starProjection y) :=
    hB.starProjection_apply_comm fun y hy ↦ hV y hy
  set X := Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection with hX
  -- `X` solves `A X - X A = P_{Uᗮ} (P_V H - H P_V) P_U` with `H = B - A`.
  have hsyl : A.sylvester A X = Uᗮ.starProjection ∘L
      (V.starProjection ∘L (B - A) - (B - A) ∘L V.starProjection) ∘L U.starProjection := by
    ext x
    simp only [hX, ContinuousLinearMap.sylvester_apply, sub_apply,
      ContinuousLinearMap.comp_apply, map_sub, hcommU, ← hcommU', hcommV]
    abel
  have hX_le : (b - a) * N X ≤ N (B - A) :=
    calc (b - a) * N X ≤ N (A.sylvester A X) :=
          N.mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_of_mem hA hA hU' hU
            (End.PointIntervalExteriorGap.of_re_inner_apply_self ha hb)
            (fun _ ↦ Uᗮ.starProjection_apply_mem _)
            fun x hx ↦ by simp [hX, U.starProjection_apply_eq_zero_iff.mpr hx]
      _ ≤ N ((V.starProjection ∘L (B - A) - (B - A) ∘L V.starProjection) ∘L
            U.starProjection) := hsyl ▸ N.map_starProjection_comp_le Uᗮ _
      _ ≤ N (V.starProjection ∘L (B - A) - (B - A) ∘L V.starProjection) :=
          N.map_comp_starProjection_le U _
      _ = N (((B - A : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ (V.starProjection : E →ₗ[𝕜] E) -
            (V.starProjection : E →ₗ[𝕜] E) ∘ₗ ((B - A : E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
          rw [← map_neg_eq_map N]
          congr 1
          ext x
          simp
      _ ≤ N (B - A) := N.map_comp_starProjection_sub_starProjection_comp_le V V _
  rw [Submodule.sinTwoAngleOperator_def, ← hX, ContinuousLinearMap.toLinearMap_smul,
    map_smul_eq_mul, RCLike.norm_ofNat]
  linarith

end TauCeti.UnitarilyInvariantSeminorm
