/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Basic

/-!
# The Davis–Kahan `sin Θ` theorems in unitarily invariant seminorms

Let `A` be a symmetric operator on a finite-dimensional inner product space `E` and `U` an
`A`-invariant subspace. This file bounds, in every unitarily invariant seminorm `N`, how far a
second subspace sticks out of `U`, under an interval/exterior separation of spectra. The bounds
have constant `1`.

## The residual form

Let `M` be a symmetric operator on a second finite-dimensional space `F` and `X : F → E` any
linear map, with residual `R = A X - X M`. If the eigenvalues of `M` lie in `[a, b]` and those of
`A` on `Uᗮ` lie outside `(a - δ, b + δ)`, then

  `δ N(P_{Uᗮ} X) ≤ N(R)`.

The projection `P_{Uᗮ}` commutes with `A`, so `Y = P_{Uᗮ} X` solves the Sylvester equation
`A Y - Y M = P_{Uᗮ} R`. Since `Y` takes values in `Uᗮ`, the interval/exterior Sylvester bound on
invariant subspaces gives `δ N(Y) ≤ N(P_{Uᗮ} R) ≤ N(R)`. When `X` is an isometry with range `Z`,
`P_{Uᗮ} X` is the directed sine map from `Z` towards `U`; when moreover `M = X† A X` is the
compression of `A` to `Z`, `R` is the Ritz residual.

## The perturbation form

Let `B` be a second symmetric operator on `E` and `V` a `B`-invariant subspace. If the eigenvalues
of `A` on `U` lie in `[a, b]` and those of `B` on `Vᗮ` lie outside `(a - δ, b + δ)`, then the
directed sine map `P_{Vᗮ} P_U` from `U` towards `V` satisfies

  `δ N(P_{Vᗮ} P_U) ≤ N(B - A)`,

and the same holds with the roles of the interval and its exterior exchanged. Here
`Y = P_{Vᗮ} P_U` takes values in `Vᗮ`, vanishes on `Uᗮ`, and solves
`B Y - Y A = P_{Vᗮ} (B - A) P_U`, so the interval/exterior Sylvester bound on invariant subspaces
gives `δ N(Y) ≤ N(P_{Vᗮ} (B - A) P_U) ≤ N(B - A)`. The dimension-free operator-norm form under
quadratic-form separation is `Submodule.mul_norm_starProjection_comp_starProjection_le_norm_sub`.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_le_map_sylvester_apply`: the
  residual `sin Θ` theorem `δ N(P_{Uᗮ} X) ≤ N(A X - X M)`.
* `TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_starProjection_le_map_sub`,
  `TauCeti.UnitarilyInvariantSeminorm.mul_map_starProjection_comp_starProjection_le_map_sub_swap`:
  the perturbation `sin Θ` theorem `δ N(P_{Vᗮ} P_U) ≤ N(B - A)`, in both orientations of the
  interval/exterior separation.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.3.
-/

public section

open Module

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {a b δ : ℝ}

omit [FiniteDimensional 𝕜 E] in
/-- The orthogonal complement of a subspace invariant under a symmetric operator is invariant. -/
private theorem apply_mem_orthogonal_of_isSymmetric {A : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U) :
    ∀ x ∈ Uᗮ, A x ∈ Uᗮ := fun _ hx ↦
  hA.orthogonalComplement_mem_invtSubmodule (p := U) (fun y hy ↦ hU y hy) hx

/-- **The residual Davis–Kahan `sin Θ` theorem.** Let `A` and `M` be symmetric operators on
finite-dimensional inner product spaces `E` and `F`, let `U` be invariant under `A`, and let
`X : F → E` be linear. If the eigenvalues of `M` lie in `[a, b]` and those of `A` on `Uᗮ` lie
outside `(a - δ, b + δ)`, then `δ N(P_{Uᗮ} X) ≤ N(A X - X M)` for every unitarily invariant
seminorm `N`. -/
theorem mul_map_starProjection_comp_le_map_sylvester_apply (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →L[𝕜] E} {M : F →L[𝕜] F} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hM : (M : F →ₗ[𝕜] F).IsSymmetric) {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (h : End.PointIntervalExteriorGap (M : F →ₗ[𝕜] F) ⊤ (A : E →ₗ[𝕜] E) Uᗮ a b δ)
    (X : F →L[𝕜] E) :
    δ * N (Uᗮ.starProjection ∘L X) ≤ N (A.sylvester M X) := by
  have hU' := apply_mem_orthogonal_of_isSymmetric hA hU
  -- `Y = P_{Uᗮ} X` solves `A Y - Y M = P_{Uᗮ} (A X - X M)`.
  have hsyl : A.sylvester M (Uᗮ.starProjection ∘L X) = Uᗮ.starProjection ∘L A.sylvester M X := by
    have hcomm : ∀ y, Uᗮ.starProjection (A y) = A (Uᗮ.starProjection y) :=
      hA.starProjection_apply_comm fun y hy ↦ hU' y hy
    ext y
    simp only [ContinuousLinearMap.sylvester_apply, sub_apply, ContinuousLinearMap.comp_apply,
      map_sub, hcomm]
  calc δ * N (Uᗮ.starProjection ∘L X) ≤ N (A.sylvester M (Uᗮ.starProjection ∘L X)) :=
        N.mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_swap_of_mem hA hM hU'
          (fun _ _ ↦ Submodule.mem_top) h (fun y ↦ Uᗮ.starProjection_apply_mem (X y))
          fun y hy ↦ by simp_all [Submodule.top_orthogonal_eq_bot]
    _ ≤ N (A.sylvester M X) := hsyl ▸ N.map_starProjection_comp_le Uᗮ _

/-- On the directed sine map `P_{Vᗮ} P_U` from an `A`-invariant subspace `U` towards a
`B`-invariant subspace `V`, the Sylvester operator `Y ↦ B Y - Y A` is `P_{Vᗮ} (B - A) P_U`, so
its unitarily invariant seminorm is at most `N(B - A)`. -/
private theorem map_sylvester_starProjection_comp_starProjection_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (hV : ∀ x ∈ V, B x ∈ V) :
    N (B.sylvester A (Vᗮ.starProjection ∘L U.starProjection)) ≤ N (B - A) := by
  have hcommA : ∀ y, U.starProjection (A y) = A (U.starProjection y) :=
    hA.starProjection_apply_comm fun y hy ↦ hU y hy
  have hcommB : ∀ y, Vᗮ.starProjection (B y) = B (Vᗮ.starProjection y) :=
    hB.starProjection_apply_comm fun y hy ↦ apply_mem_orthogonal_of_isSymmetric hB hV y hy
  have hsyl : B.sylvester A (Vᗮ.starProjection ∘L U.starProjection) =
      Vᗮ.starProjection ∘L (B - A) ∘L U.starProjection := by
    ext x
    simp only [ContinuousLinearMap.sylvester_apply, sub_apply, ContinuousLinearMap.comp_apply,
      map_sub, hcommA, hcommB]
  calc N (B.sylvester A (Vᗮ.starProjection ∘L U.starProjection))
      ≤ N ((B - A) ∘L U.starProjection) := hsyl ▸ N.map_starProjection_comp_le Vᗮ _
    _ ≤ N (B - A) := N.map_comp_starProjection_le U _

/-- **The perturbation Davis–Kahan `sin Θ` theorem.** Let `A` and `B` be symmetric operators on a
finite-dimensional inner product space, let `U` be invariant under `A` and `V` invariant under
`B`. If the eigenvalues of `A` on `U` lie in `[a, b]` and those of `B` on `Vᗮ` lie outside
`(a - δ, b + δ)`, then the directed sine map `P_{Vᗮ} P_U` from `U` towards `V` satisfies
`δ N(P_{Vᗮ} P_U) ≤ N(B - A)` for every unitarily invariant seminorm `N`. -/
theorem mul_map_starProjection_comp_starProjection_le_map_sub
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (hV : ∀ x ∈ V, B x ∈ V)
    (h : End.PointIntervalExteriorGap (A : E →ₗ[𝕜] E) U (B : E →ₗ[𝕜] E) Vᗮ a b δ) :
    δ * N (Vᗮ.starProjection ∘L U.starProjection) ≤ N (B - A) :=
  calc δ * N (Vᗮ.starProjection ∘L U.starProjection)
      ≤ N (B.sylvester A (Vᗮ.starProjection ∘L U.starProjection)) :=
        N.mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_swap_of_mem hB hA
          (apply_mem_orthogonal_of_isSymmetric hB hV) hU h (fun x ↦ Vᗮ.starProjection_apply_mem _)
          fun x hx ↦ by simp [U.starProjection_apply_eq_zero_iff.mpr hx]
    _ ≤ N (B - A) := N.map_sylvester_starProjection_comp_starProjection_le hA hB hU hV

/-- **The perturbation Davis–Kahan `sin Θ` theorem, reversed orientation.** Let `A` and `B` be
symmetric operators on a finite-dimensional inner product space, let `U` be invariant under `A`
and `V` invariant under `B`. If the eigenvalues of `B` on `Vᗮ` lie in `[a, b]` and those of `A`
on `U` lie outside `(a - δ, b + δ)`, then the directed sine map `P_{Vᗮ} P_U` from `U` towards `V`
satisfies `δ N(P_{Vᗮ} P_U) ≤ N(B - A)` for every unitarily invariant seminorm `N`. -/
theorem mul_map_starProjection_comp_starProjection_le_map_sub_swap
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {A B : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric) {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (hV : ∀ x ∈ V, B x ∈ V)
    (h : End.PointIntervalExteriorGap (B : E →ₗ[𝕜] E) Vᗮ (A : E →ₗ[𝕜] E) U a b δ) :
    δ * N (Vᗮ.starProjection ∘L U.starProjection) ≤ N (B - A) :=
  calc δ * N (Vᗮ.starProjection ∘L U.starProjection)
      ≤ N (B.sylvester A (Vᗮ.starProjection ∘L U.starProjection)) :=
        N.mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_of_mem hB hA
          (apply_mem_orthogonal_of_isSymmetric hB hV) hU h (fun x ↦ Vᗮ.starProjection_apply_mem _)
          fun x hx ↦ by simp [U.starProjection_apply_eq_zero_iff.mpr hx]
    _ ≤ N (B - A) := N.map_sylvester_starProjection_comp_starProjection_le hA hB hU hV

end TauCeti.UnitarilyInvariantSeminorm
