/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.FanDominance
public import TauCeti.Analysis.InnerProductSpace.Sylvester
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Frobenius

/-!
# Unitarily invariant bounds for the Sylvester equation

This file bounds solutions of the Sylvester equation `A X - X B = C` in unitarily invariant
seminorms, for operators on finite-dimensional inner product spaces.

## The Frobenius bound

Let `A` and `B` be symmetric operators on finite-dimensional inner product spaces `E` and `F`, with
orthonormal eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`. The Sylvester operator
`X ↦ A X - X B` multiplies the matrix coefficient `Xᵢⱼ = ⟪uᵢ, X vⱼ⟫` by `αᵢ - βⱼ`, so the Frobenius
seminorm of `A X - X B` is

`‖A X - X B‖_F² = ∑ᵢ ∑ⱼ (αᵢ - βⱼ)² ‖Xᵢⱼ‖²`.

If the spectra of `A` and `B` are at distance at least `δ`, every factor `(αᵢ - βⱼ)²` is at least
`δ²`, and therefore `δ ‖X‖_F ≤ ‖A X - X B‖_F`. Equivalently, every solution of the Sylvester
equation `A X - X B = C` satisfies `δ ‖X‖_F ≤ ‖C‖_F`. For the Frobenius seminorm the constant is
`1`; the corresponding bound for a general unitarily invariant seminorm under the same pairwise
separation hypothesis carries the constant `π / 2`.

## The interval/exterior bound

If the spectrum of `A` lies in the interval `[a, b]` and that of `B` outside `(a - δ, b + δ)`, then
`δ N(X) ≤ N(A X - X B)` for every unitarily invariant seminorm `N`, again with constant `1`; the
same holds with the roles of `A` and `B` exchanged. With centre `c = (a + b) / 2` and radius
`r = (b - a) / 2`, for symmetric `A` and `B` the hypothesis gives `‖(A - c) x‖ ≤ r ‖x‖` and
`(r + δ) ‖y‖ ≤ ‖(B - c) y‖`. Since
`A X - X B = (A - c) X - X (B - c)`, the ideal inequality `N((A - c) X) ≤ r N(X)` and its reverse
`(r + δ) N(X) ≤ N(X (B - c))` give `(r + δ) N(X) ≤ r N(X) + N(A X - X B)`. This argument needs
neither symmetry nor a real centre, so it is stated first for an arbitrary centre `c : 𝕜` and
norm bounds of this shape.

## Main statements

* `ContinuousLinearMap.sq_frobenius_sylvester_apply`: the exact formula for `‖A X - X B‖_F²` in
  orthonormal eigenbases of `A` and `B`.
* `ContinuousLinearMap.mul_frobenius_le_frobenius_sylvester_apply`: if the point spectra of `A`
  and `B` are at distance at least `δ`, then `δ ‖X‖_F ≤ ‖A X - X B‖_F`.

In the namespace `TauCeti.UnitarilyInvariantSeminorm`:

* `mul_map_le_map_sylvester_apply_of_norm_sub_smul_le_of_le_norm_sub_smul`,
  `mul_map_le_map_sylvester_apply_of_le_norm_sub_smul_of_norm_sub_smul_le`: if `A - c` is
  bounded by `r` and `B - c` bounded below by `r + δ`, or the other way round, then
  `δ N(X) ≤ N(A X - X B)`.
* `mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap`,
  `mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_swap`: under an interval/exterior
  gap between the spectra of symmetric `A` and `B`, in either orientation,
  `δ N(X) ≤ N(A X - X B)`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.2.
* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1–46.
* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
-/

public section

open Module TauCeti.UnitarilyInvariantSeminorm
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F} {n m : ℕ} {δ : ℝ}

/-- **The Frobenius seminorm of `A X - X B` in eigenbases.** For symmetric `A` and `B` with
ordered orthonormal eigenbases `(uᵢ)`, `(vⱼ)` and eigenvalues `(αᵢ)`, `(βⱼ)`,
`‖A X - X B‖_F² = ∑ᵢ ∑ⱼ (αᵢ - βⱼ)² ‖⟪uᵢ, X vⱼ⟫‖²`. -/
theorem sq_frobenius_sylvester_apply (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (X : F →L[𝕜] E) :
    frobenius 𝕜 F E (A.sylvester B X) ^ 2 =
      ∑ i, ∑ j, (hA.eigenvalues hn i - hB.eigenvalues hm j) ^ 2 *
        ‖⟪hA.eigenvectorBasis hn i, X (hB.eigenvectorBasis hm j)⟫_𝕜‖ ^ 2 := by
  rw [sq_frobenius_apply_eq_sum_norm_inner_sq (hB.eigenvectorBasis hm) (hA.eigenvectorBasis hn),
    Finset.sum_comm]
  simp_rw [coe_coe, inner_sylvester_apply_eigenvectorBasis hA hB hn hm, norm_mul,
    RCLike.norm_ofReal, mul_pow, sq_abs]

/-- **The Frobenius Sylvester bound.** In finite dimension, if `A` and `B` are symmetric and every
eigenvalue of `A` is at distance at least `δ` from every eigenvalue of `B`, then
`δ ‖X‖_F ≤ ‖A X - X B‖_F` for every `X`. In particular every solution of the Sylvester equation
`A X - X B = C` satisfies `δ ‖X‖_F ≤ ‖C‖_F`. -/
theorem mul_frobenius_le_frobenius_sylvester_apply (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointSpectraSeparated (A : E →ₗ[𝕜] E) ⊤ (B : F →ₗ[𝕜] F) ⊤ δ) (X : F →L[𝕜] E) :
    δ * frobenius 𝕜 F E X ≤ frobenius 𝕜 F E (A.sylvester B X) := by
  rcases lt_or_ge δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ.le (apply_nonneg _ _)).trans (apply_nonneg _ _)
  rw [← pow_le_pow_iff_left₀ (by positivity) (apply_nonneg _ _) two_ne_zero, mul_pow,
    sq_frobenius_sylvester_apply hA hB rfl rfl,
    sq_frobenius_apply_eq_sum_norm_inner_sq (hB.eigenvectorBasis rfl) (hA.eigenvectorBasis rfl),
    Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_right ?_ (by positivity)
  -- Each eigenvalue difference is at least `δ` in absolute value.
  have hij := h.le_abs_sub
    (by simpa using hA.hasEigenvalue_eigenvalues rfl i)
    (by simpa using hB.hasEigenvalue_eigenvalues rfl j)
  simpa using pow_le_pow_left₀ hδ hij 2

end ContinuousLinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F} {c : 𝕜} {a b r δ : ℝ}

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- As a linear map, `A X - X B` equals `(A - c) X - X (B - c)` for every scalar `c`. -/
private theorem coe_sylvester_apply_eq_sub_smul_one (A : E →L[𝕜] E) (B : F →L[𝕜] F) (c : 𝕜)
    (X : F →L[𝕜] E) :
    ((A.sylvester B X : F →L[𝕜] E) : F →ₗ[𝕜] E) =
      ((A - c • 1 : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ (X : F →ₗ[𝕜] E) -
        (X : F →ₗ[𝕜] E) ∘ₗ ((B - c • 1 : F →L[𝕜] F) : F →ₗ[𝕜] F) := by
  rw [← ContinuousLinearMap.sub_smul_one_sylvester_sub_smul_one A B c,
    ContinuousLinearMap.sylvester_apply, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp]

/-- **Sylvester bound from a disc and the exterior of a larger disc.** If `‖A x - c x‖ ≤ r ‖x‖`
for every `x` and `(r + δ) ‖y‖ ≤ ‖B y - c y‖` for every `y`, then `δ N(X) ≤ N(A X - X B)` for
every unitarily invariant seminorm `N`. -/
theorem mul_map_le_map_sylvester_apply_of_norm_sub_smul_le_of_le_norm_sub_smul
    (N : UnitarilyInvariantSeminorm 𝕜 F E) (hA : ∀ x, ‖A x - c • x‖ ≤ r * ‖x‖)
    (hB : ∀ y, (r + δ) * ‖y‖ ≤ ‖B y - c • y‖) (X : F →L[𝕜] E) :
    δ * N X ≤ N (A.sylvester B X) := by
  have hsyl := coe_sylvester_apply_eq_sub_smul_one A B c X
  set A' : E →L[𝕜] E := A - c • 1
  set B' : F →L[𝕜] F := B - c • 1
  have h₁ : (r + δ) * N X ≤ N ((X : F →ₗ[𝕜] E) ∘ₗ (B' : F →ₗ[𝕜] F)) :=
    N.mul_map_le_map_comp_right _ _ (by simpa [B'] using hB)
  have h₂ : N ((A' : E →ₗ[𝕜] E) ∘ₗ (X : F →ₗ[𝕜] E)) ≤ r * N X :=
    N.map_comp_le_left _ _ (by simpa [A'] using hA)
  -- `X (B - c) = (A - c) X - (A X - X B)`.
  have h₃ := map_sub_le_add N ((A' : E →ₗ[𝕜] E) ∘ₗ (X : F →ₗ[𝕜] E))
    ((A' : E →ₗ[𝕜] E) ∘ₗ X - X ∘ₗ (B' : F →ₗ[𝕜] F))
  rw [sub_sub_cancel, ← hsyl] at h₃
  linarith

/-- **Sylvester bound from the exterior of a disc and a smaller disc.** If
`(r + δ) ‖x‖ ≤ ‖A x - c x‖` for every `x` and `‖B y - c y‖ ≤ r ‖y‖` for every `y`, then
`δ N(X) ≤ N(A X - X B)` for every unitarily invariant seminorm `N`. -/
theorem mul_map_le_map_sylvester_apply_of_le_norm_sub_smul_of_norm_sub_smul_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E) (hA : ∀ x, (r + δ) * ‖x‖ ≤ ‖A x - c • x‖)
    (hB : ∀ y, ‖B y - c • y‖ ≤ r * ‖y‖) (X : F →L[𝕜] E) :
    δ * N X ≤ N (A.sylvester B X) := by
  have hsyl := coe_sylvester_apply_eq_sub_smul_one A B c X
  set A' : E →L[𝕜] E := A - c • 1
  set B' : F →L[𝕜] F := B - c • 1
  have h₁ : (r + δ) * N X ≤ N ((A' : E →ₗ[𝕜] E) ∘ₗ (X : F →ₗ[𝕜] E)) :=
    N.mul_map_le_map_comp_left _ _ (by simpa [A'] using hA)
  have h₂ : N ((X : F →ₗ[𝕜] E) ∘ₗ (B' : F →ₗ[𝕜] F)) ≤ r * N X :=
    N.map_comp_le_right _ _ (by simpa [B'] using hB)
  -- `(A - c) X = X (B - c) + (A X - X B)`.
  have h₃ := map_add_le_add N ((X : F →ₗ[𝕜] E) ∘ₗ (B' : F →ₗ[𝕜] F))
    ((A' : E →ₗ[𝕜] E) ∘ₗ X - X ∘ₗ (B' : F →ₗ[𝕜] F))
  rw [add_sub_cancel, ← hsyl] at h₃
  linarith

/-- The interval `(a - δ, b + δ)` is the open ball about `(a + b) / 2` of radius
`(b - a) / 2 + δ`. -/
private theorem ball_eq_Ioo_sub_add :
    Metric.ball ((a + b) / 2) ((b - a) / 2 + δ) = Set.Ioo (a - δ) (b + δ) := by
  rw [Real.Ioo_eq_ball]
  congr 1 <;> ring

/-- **The interval/exterior Sylvester bound.** Let `A` and `B` be symmetric operators on
finite-dimensional inner product spaces. If the eigenvalues of `A` lie in `[a, b]` and those of `B`
outside `(a - δ, b + δ)`, then `δ N(X) ≤ N(A X - X B)` for every unitarily invariant seminorm `N`.
In particular every solution of the Sylvester equation `A X - X B = C` satisfies
`δ N(X) ≤ N(C)`. -/
theorem mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap
    (N : UnitarilyInvariantSeminorm 𝕜 F E) (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointIntervalExteriorGap (A : E →ₗ[𝕜] E) ⊤ (B : F →ₗ[𝕜] F) ⊤ a b δ)
    (X : F →L[𝕜] E) :
    δ * N X ≤ N (A.sylvester B X) := by
  have hA' (x : E) := hA.norm_apply_sub_smul_le_of_pointSpectrumIn (fun _ _ ↦ Submodule.mem_top)
    (h.pointSpectrumIn_Icc.mono le_rfl (Real.Icc_eq_closedBall a b).subset)
    (Submodule.mem_top (x := x))
  have hB' (y : F) := hB.mul_norm_le_norm_apply_sub_smul_of_pointSpectrumIn
    (fun _ _ ↦ Submodule.mem_top) (h.pointSpectrumIn_compl_Ioo.mono le_rfl
      (Set.compl_subset_compl.mpr ball_eq_Ioo_sub_add.subset)) (Submodule.mem_top (x := y))
  exact N.mul_map_le_map_sylvester_apply_of_norm_sub_smul_le_of_le_norm_sub_smul
    (c := (((a + b) / 2 : ℝ) : 𝕜))
    (fun x ↦ by simpa using hA' x) (fun y ↦ by simpa using hB' y) X

/-- **The interval/exterior Sylvester bound, reversed orientation.** Let `A` and `B` be symmetric
operators on finite-dimensional inner product spaces. If the eigenvalues of `B` lie in `[a, b]`
and those of `A` outside `(a - δ, b + δ)`, then `δ N(X) ≤ N(A X - X B)` for every unitarily
invariant seminorm `N`. In particular every solution of the Sylvester equation `A X - X B = C`
satisfies `δ N(X) ≤ N(C)`. -/
theorem mul_map_le_map_sylvester_apply_of_pointIntervalExteriorGap_swap
    (N : UnitarilyInvariantSeminorm 𝕜 F E) (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointIntervalExteriorGap (B : F →ₗ[𝕜] F) ⊤ (A : E →ₗ[𝕜] E) ⊤ a b δ)
    (X : F →L[𝕜] E) :
    δ * N X ≤ N (A.sylvester B X) := by
  have hA' (x : E) := hA.mul_norm_le_norm_apply_sub_smul_of_pointSpectrumIn
    (fun _ _ ↦ Submodule.mem_top) (h.pointSpectrumIn_compl_Ioo.mono le_rfl
      (Set.compl_subset_compl.mpr ball_eq_Ioo_sub_add.subset)) (Submodule.mem_top (x := x))
  have hB' (y : F) := hB.norm_apply_sub_smul_le_of_pointSpectrumIn (fun _ _ ↦ Submodule.mem_top)
    (h.pointSpectrumIn_Icc.mono le_rfl (Real.Icc_eq_closedBall a b).subset)
    (Submodule.mem_top (x := y))
  exact N.mul_map_le_map_sylvester_apply_of_le_norm_sub_smul_of_norm_sub_smul_le
    (c := (((a + b) / 2 : ℝ) : 𝕜))
    (fun x ↦ by simpa using hA' x) (fun y ↦ by simpa using hB' y) X

end TauCeti.UnitarilyInvariantSeminorm
