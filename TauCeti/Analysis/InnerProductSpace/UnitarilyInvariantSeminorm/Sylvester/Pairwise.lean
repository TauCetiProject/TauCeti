/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Basic
import TauCeti.Analysis.Fourier.HaagerupZsido.Fourier
import TauCeti.Analysis.Fourier.HaagerupZsido.Mass
import TauCeti.Analysis.InnerProductSpace.Symmetric.FunctionalCalculus

/-!
# The pairwise Sylvester bound in unitarily invariant seminorms

Let `A` and `B` be symmetric operators on finite-dimensional inner product spaces `E` and `F`, over
`ℝ` or `ℂ`, and suppose that every eigenvalue of `A` is at distance at least `δ > 0` from every
eigenvalue of `B`. No ordering or interval structure of the two spectra is assumed. This file
proves that every solution of the Sylvester equation `A X - X B = C` satisfies

`δ N(X) ≤ (π / 2) N(C)`

for every unitarily invariant seminorm `N`. The estimate is first proved simultaneously for all
Ky Fan sums, `δ Kₖ(X) ≤ (π / 2) Kₖ(C)`; equivalently, `(2 δ / π) X` lies in the convex hull of
the two-sided unitary orbit of `C`, and Fan dominance turns this into the bound for every `N`.

## The integral representation

The constant `π / 2` is the mass `∫ |r| = π / 2` of the real Haagerup–Zsidó kernel `r`, which
inverts the variable outside the unit interval: `∫ r(t) sin (x t) dt = 1 / x` for `|x| ≥ 1`
(`TauCeti.HaagerupZsido.integral_realKernel_mul_sin`). In orthonormal eigenbases with
`A eᵢ = αᵢ eᵢ` and `B fⱼ = βⱼ fⱼ`, the coefficients of the solution are
`⟪eᵢ, X fⱼ⟫ = ⟪eᵢ, C fⱼ⟫ / (αᵢ - βⱼ)`, and `|αᵢ - βⱼ| ≥ δ`, so

`⟪eᵢ, X fⱼ⟫ = δ⁻¹ ∫ r(t) sin ((αᵢ - βⱼ) t / δ) ⟪eᵢ, C fⱼ⟫ dt`.

Expanding `sin (a - b) = sin a cos b - cos a sin b`, for orthonormal families `(uₗ)` and `(vₗ)` the
sum `∑ₗ ⟪uₗ, X vₗ⟫` becomes `δ⁻¹ ∫ r(t) g(t) dt`, where

`g(t) = ∑ₗ (⟪sin (t A / δ) uₗ, C cos (t B / δ) vₗ⟫ - ⟪cos (t A / δ) uₗ, C sin (t B / δ) vₗ⟫)`

is built from the functional calculi of `A` and `B`. Since `sin² + cos² = 1`, Ky Fan's maximum
principle for pairs of contractions (`LinearMap.norm_sum_inner_add_inner_le_kyFanSum`) gives
`‖g(t)‖ ≤ Kₖ(C)` whenever there are at most `k` vectors in each family, and the variational
characterization of the Ky Fan sums yields `δ Kₖ(X) ≤ (π / 2) Kₖ(C)`. Working with the real kernel
and the sine and cosine of `A` and `B` keeps the argument inside the scalar field, so no
complexification is needed over `ℝ`.

## Main statements

* `ContinuousLinearMap.mul_kyFanSum_le_pi_div_two_mul_kyFanSum_sylvester_apply`: under pairwise
  separation by `δ`, `δ Kₖ(X) ≤ (π / 2) Kₖ(A X - X B)` for every `k`.
* `ContinuousLinearMap.smul_mem_twoSidedUnitaryOrbitHull_sylvester_apply`: the scaled solution
  `(2 δ / π) X` lies in the convex hull of the two-sided unitary orbit of `A X - X B`.
* `TauCeti.UnitarilyInvariantSeminorm.mul_map_le_pi_div_two_mul_map_sylvester_apply`: under
  pairwise separation by `δ`, `δ N(X) ≤ (π / 2) N(A X - X B)` for every unitarily invariant
  seminorm `N`.

## References

* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), §VII.2.
* U. Haagerup, L. Zsidó, the extremal kernel attaining the constant `π / 2`; see the account in
  S. Albeverio, K. A. Makarov, A. K. Motovilov, *Graph subspaces and the spectral shift function*,
  Canad. J. Math. **55** (2003), 449–503.
-/

public section

open Module MeasureTheory Finset TauCeti.HaagerupZsido
open scoped InnerProductSpace Real

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F} {δ : ℝ}

/-- The phase-twisted coefficient sum of `C : F →ₗ[𝕜] E` against families `(uₗ)` and `(vₗ)`,
written through the functional calculi of symmetric `A` and `B`: with `A eᵢ = αᵢ eᵢ` and
`B fⱼ = βⱼ fⱼ`, the sum `∑ₗ (⟪sin (τA) uₗ, C cos (τB) vₗ⟫ + ⟪cos (τA) uₗ, C (-sin (τB)) vₗ⟫)` is
`∑ₗ ∑ᵢ ∑ⱼ ⟪uₗ, eᵢ⟫ ⟪eᵢ, C fⱼ⟫ ⟪fⱼ, vₗ⟫ sin ((αᵢ - βⱼ) τ)`. -/
private theorem sum_inner_cfc_add_inner_cfc {n m p : ℕ} {A : E →ₗ[𝕜] E} {B : F →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hn : finrank 𝕜 E = n) (hm : finrank 𝕜 F = m)
    (C : F →ₗ[𝕜] E) (u : Fin p → E) (v : Fin p → F) (τ : ℝ) :
    ∑ l, (⟪hA.cfc (fun μ ↦ Real.sin (μ * τ)) (u l),
        C (hB.cfc (fun ν ↦ Real.cos (ν * τ)) (v l))⟫_𝕜 +
      ⟪hA.cfc (fun μ ↦ Real.cos (μ * τ)) (u l),
        C (hB.cfc (fun ν ↦ -Real.sin (ν * τ)) (v l))⟫_𝕜) =
      ∑ l, ∑ i, ∑ j, ⟪u l, hA.eigenvectorBasis hn i⟫_𝕜 *
        ⟪hA.eigenvectorBasis hn i, C (hB.eigenvectorBasis hm j)⟫_𝕜 *
          ⟪hB.eigenvectorBasis hm j, v l⟫_𝕜 *
            (Real.sin ((hA.eigenvalues hn i - hB.eigenvalues hm j) * τ) : 𝕜) := by
  set e := hA.eigenvectorBasis hn
  set f := hB.eigenvectorBasis hm
  refine sum_congr rfl fun l _ ↦ ?_
  rw [← e.sum_sum_inner_mul_inner_mul_inner f C, ← e.sum_sum_inner_mul_inner_mul_inner f C]
  simp only [← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  -- Move the functional calculi onto the eigenvectors, where they act by scalars.
  rw [hA.isSymmetric_cfc _ (u l), hA.isSymmetric_cfc _ (u l), ← hB.isSymmetric_cfc _ _ (v l),
    ← hB.isSymmetric_cfc _ _ (v l)]
  simp only [e, f, hA.cfc_apply_eigenvectorBasis, hB.cfc_apply_eigenvectorBasis,
    inner_smul_right, inner_smul_left, RCLike.conj_ofReal]
  rw [sub_mul, Real.sin_sub]
  push_cast
  ring

/-- The phase-twisted coefficient sums of `C : F →ₗ[𝕜] E` against orthonormal families of `p`
vectors are bounded by the Ky Fan `p`-sum of `C`, since `sin² + cos² = 1`. -/
private theorem norm_sum_inner_cfc_add_inner_cfc_le_kyFanSum {p : ℕ} {A : E →ₗ[𝕜] E}
    {B : F →ₗ[𝕜] F} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (C : F →ₗ[𝕜] E) {u : Fin p → E}
    {v : Fin p → F} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) (τ : ℝ) :
    ‖∑ l, (⟪hA.cfc (fun μ ↦ Real.sin (μ * τ)) (u l),
        C (hB.cfc (fun ν ↦ Real.cos (ν * τ)) (v l))⟫_𝕜 +
      ⟪hA.cfc (fun μ ↦ Real.cos (μ * τ)) (u l),
        C (hB.cfc (fun ν ↦ -Real.sin (ν * τ)) (v l))⟫_𝕜)‖ ≤ C.kyFanSum p := by
  simpa using C.norm_sum_inner_add_inner_le_kyFanSum (hA.isSymmetric_cfc _)
    (hA.isSymmetric_cfc _) (hB.isSymmetric_cfc _) (hB.isSymmetric_cfc _)
    (fun y ↦ (hA.norm_cfc_apply_sq_add_norm_cfc_apply_sq
      (fun μ _ ↦ Real.sin_sq_add_cos_sq (μ * τ)) y).le)
    (fun x ↦ (hB.norm_cfc_apply_sq_add_norm_cfc_apply_sq (f := fun ν ↦ Real.cos (ν * τ))
      (g := fun ν ↦ -Real.sin (ν * τ))
      (fun ν _ ↦ by rw [neg_sq, add_comm, Real.sin_sq_add_cos_sq]) x).le) hu hv

/-- **The integral representation of the Sylvester solution.** If every eigenvalue of `A` is at
distance at least `δ > 0` from every eigenvalue of `B`, then for families `(uₗ)` and `(vₗ)` the
coefficient sum `∑ₗ ⟪uₗ, X vₗ⟫` is `δ⁻¹` times the integral, against the real Haagerup–Zsidó
kernel, of the phase-twisted coefficient sums of `A X - X B` at `τ = t / δ`. -/
private theorem sum_inner_eq_inv_mul_integral_realKernel_mul {p : ℕ}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointSpectraSeparated (A : E →ₗ[𝕜] E) ⊤ (B : F →ₗ[𝕜] F) ⊤ δ) (hδ : 0 < δ)
    (X : F →L[𝕜] E) (u : Fin p → E) (v : Fin p → F) :
    ∑ l, ⟪u l, (X : F →ₗ[𝕜] E) (v l)⟫_𝕜 = (δ⁻¹ : 𝕜) * ∫ t, (realKernel t : 𝕜) *
      ∑ l, (⟪hA.cfc (fun μ ↦ Real.sin (μ * (t / δ))) (u l),
          (A.sylvester B X) (hB.cfc (fun ν ↦ Real.cos (ν * (t / δ))) (v l))⟫_𝕜 +
        ⟪hA.cfc (fun μ ↦ Real.cos (μ * (t / δ))) (u l),
          (A.sylvester B X) (hB.cfc (fun ν ↦ -Real.sin (ν * (t / δ))) (v l))⟫_𝕜) := by
  -- Expand the phase-twisted sums in the eigenbases.
  rw [← coe_coe (A.sylvester B X)]
  simp only [sum_inner_cfc_add_inner_cfc hA hB rfl rfl]
  set C : F →ₗ[𝕜] E := ((A.sylvester B X : F →L[𝕜] E) : F →ₗ[𝕜] E) with hC
  set e := hA.eigenvectorBasis rfl
  set f := hB.eigenvectorBasis rfl
  set α := hA.eigenvalues rfl
  set β := hB.eigenvalues rfl
  have hgap (i j) : δ ≤ |α i - β j| :=
    h.le_abs_sub (by simpa using hA.hasEigenvalue_eigenvalues rfl i)
      (by simpa using hB.hasEigenvalue_eigenvalues rfl j)
  -- The real Haagerup–Zsidó kernel inverts every eigenvalue difference:
  -- `∫ r(t) sin ((αᵢ - βⱼ) t / δ) dt = δ / (αᵢ - βⱼ)`.
  have hinv (i j) :
      ∫ t, realKernel t * Real.sin ((α i - β j) * (t / δ)) = δ * (α i - β j)⁻¹ := by
    have h1 : 1 ≤ |(α i - β j) / δ| := by
      rw [abs_div, abs_of_pos hδ, one_le_div hδ]
      exact hgap i j
    calc _ = ∫ t, realKernel t * Real.sin ((α i - β j) / δ * t) :=
          integral_congr_ae (.of_forall fun t ↦ by ring_nf)
      _ = δ * (α i - β j)⁻¹ := by rw [integral_realKernel_mul_sin h1, inv_div, div_eq_mul_inv]
  -- The eigenbasis coefficients of `X` are those of `C` divided by the eigenvalue differences.
  have hX (i j) : ⟪e i, X (f j)⟫_𝕜 = ((α i - β j)⁻¹ : ℝ) * ⟪e i, C (f j)⟫_𝕜 := by
    have hij : (α i : 𝕜) - β j ≠ 0 := by exact_mod_cast abs_pos.mp (hδ.trans_le (hgap i j))
    rw [hC, coe_coe, inner_sylvester_apply_eigenvectorBasis hA hB rfl rfl X i j]
    push_cast
    field_simp
    ring
  -- Integrate the expanded sums term by term.
  set c : Fin p → Fin (finrank 𝕜 E) → Fin (finrank 𝕜 F) → 𝕜 :=
    fun l i j ↦ ⟪u l, e i⟫_𝕜 * ⟪e i, C (f j)⟫_𝕜 * ⟪f j, v l⟫_𝕜
  have hint (l i j) : Integrable fun t ↦
      (realKernel t : 𝕜) * (c l i j * (Real.sin ((α i - β j) * (t / δ)) : 𝕜)) := by
    have hr : Integrable fun t ↦ Real.sin ((α i - β j) * (t / δ)) * realKernel t :=
      integrable_realKernel.bdd_mul (c := 1) (by fun_prop)
        (.of_forall fun t ↦ by simpa using Real.abs_sin_le_one _)
    refine (hr.ofReal (𝕜 := 𝕜)).const_mul (c l i j) |>.congr (.of_forall fun t ↦ ?_)
    push_cast
    ring
  have hterm (l i j) :
      ∫ t, (realKernel t : 𝕜) * (c l i j * (Real.sin ((α i - β j) * (t / δ)) : 𝕜)) =
        c l i j * ((δ * (α i - β j)⁻¹ : ℝ) : 𝕜) := by
    rw [← hinv i j, ← integral_ofReal, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun t ↦ by push_cast; ring)
  simp only [mul_sum]
  rw [integral_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun i _ ↦
    integrable_finsetSum _ fun j _ ↦ hint l i j, mul_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint l i j,
    ← e.sum_sum_inner_mul_inner_mul_inner f, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ hint l i j, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  have hδ' : (δ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
  rw [hterm, coe_coe, hX]
  simp only [c]
  push_cast
  field_simp

/-- **The simultaneous Ky Fan estimate for the Sylvester equation.** Let `A` and `B` be symmetric
operators on finite-dimensional inner product spaces. If every eigenvalue of `A` is at distance at
least `δ` from every eigenvalue of `B`, then for every `k` the Ky Fan `k`-sums satisfy
`δ Kₖ(X) ≤ (π / 2) Kₖ(A X - X B)`. In particular every solution of the Sylvester equation
`A X - X B = C` satisfies `δ Kₖ(X) ≤ (π / 2) Kₖ(C)` for all `k` at once. -/
theorem mul_kyFanSum_le_pi_div_two_mul_kyFanSum_sylvester_apply
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointSpectraSeparated (A : E →ₗ[𝕜] E) ⊤ (B : F →ₗ[𝕜] F) ⊤ δ) (X : F →L[𝕜] E)
    (k : ℕ) :
    δ * (X : F →ₗ[𝕜] E).kyFanSum k ≤
      π / 2 * ((A.sylvester B X : F →L[𝕜] E) : F →ₗ[𝕜] E).kyFanSum k := by
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ (LinearMap.kyFanSum_nonneg _ _)).trans
      (mul_nonneg (by positivity) (LinearMap.kyFanSum_nonneg _ _))
  set C : F →ₗ[𝕜] E := ((A.sylvester B X : F →L[𝕜] E) : F →ₗ[𝕜] E)
  rw [mul_comm, ← le_div_iff₀ hδ]
  refine (LinearMap.kyFanSum_le_iff _).mpr fun p hp u v hu hv ↦ ?_
  rw [sum_inner_eq_inv_mul_integral_realKernel_mul hA hB h hδ X u v, norm_mul,
    norm_inv, RCLike.norm_ofReal, abs_of_pos hδ, div_eq_inv_mul]
  gcongr
  calc _ ≤ ∫ t, |realKernel t| * C.kyFanSum k :=
        norm_integral_le_of_norm_le (integrable_realKernel.abs.mul_const _)
          (.of_forall fun t ↦ by
            rw [norm_mul, RCLike.norm_ofReal]
            exact mul_le_mul_of_nonneg_left
              ((norm_sum_inner_cfc_add_inner_cfc_le_kyFanSum hA hB C hu hv _).trans
                (C.kyFanSum_mono hp)) (abs_nonneg _))
    _ = π / 2 * C.kyFanSum k := by rw [integral_mul_const, integral_abs_realKernel]

/-- **The unitary-orbit form of the pairwise Sylvester bound.** Let `A` and `B` be symmetric
operators on finite-dimensional inner product spaces. If every eigenvalue of `A` is at distance at
least `δ ≥ 0` from every eigenvalue of `B`, then `(2 δ / π) X` lies in the convex hull of the
two-sided unitary orbit `{U (A X - X B) V}` of `A X - X B`. -/
theorem smul_mem_twoSidedUnitaryOrbitHull_sylvester_apply (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointSpectraSeparated (A : E →ₗ[𝕜] E) ⊤ (B : F →ₗ[𝕜] F) ⊤ δ) (hδ : 0 ≤ δ)
    (X : F →L[𝕜] E) :
    ((2 * δ / π : ℝ) : 𝕜) • (X : F →ₗ[𝕜] E) ∈
      ((A.sylvester B X : F →L[𝕜] E) : F →ₗ[𝕜] E).twoSidedUnitaryOrbitHull := by
  refine LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le.mpr fun k ↦ ?_
  rw [LinearMap.kyFanSum_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
  have hk := mul_kyFanSum_le_pi_div_two_mul_kyFanSum_sylvester_apply hA hB h X k
  calc 2 * δ / π * (X : F →ₗ[𝕜] E).kyFanSum k = 2 / π * (δ * (X : F →ₗ[𝕜] E).kyFanSum k) := by
        ring
    _ ≤ 2 / π * (π / 2 * ((A.sylvester B X : F →L[𝕜] E) : F →ₗ[𝕜] E).kyFanSum k) := by gcongr
    _ = _ := by field_simp

end ContinuousLinearMap

namespace TauCeti.UnitarilyInvariantSeminorm

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F} {δ : ℝ}

/-- **The pairwise Sylvester bound.** Let `A` and `B` be symmetric operators on finite-dimensional
inner product spaces. If every eigenvalue of `A` is at distance at least `δ` from every eigenvalue
of `B`, then `δ N(X) ≤ (π / 2) N(A X - X B)` for every unitarily invariant seminorm `N`. In
particular every solution of the Sylvester equation `A X - X B = C` satisfies
`δ N(X) ≤ (π / 2) N(C)`. -/
theorem mul_map_le_pi_div_two_mul_map_sylvester_apply (N : UnitarilyInvariantSeminorm 𝕜 F E)
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    (h : End.PointSpectraSeparated (A : E →ₗ[𝕜] E) ⊤ (B : F →ₗ[𝕜] F) ⊤ δ) (X : F →L[𝕜] E) :
    δ * N X ≤ π / 2 * N (A.sylvester B X) := by
  rcases lt_or_ge δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ.le (apply_nonneg _ _)).trans
      (mul_nonneg (by positivity) (apply_nonneg _ _))
  have hN := N.map_le_of_mem_twoSidedUnitaryOrbitHull
    (ContinuousLinearMap.smul_mem_twoSidedUnitaryOrbitHull_sylvester_apply hA hB h hδ X)
  rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at hN
  calc δ * N X = π / 2 * (2 * δ / π * N X) := by field_simp
    _ ≤ π / 2 * N (A.sylvester B X) := by gcongr

end TauCeti.UnitarilyInvariantSeminorm
