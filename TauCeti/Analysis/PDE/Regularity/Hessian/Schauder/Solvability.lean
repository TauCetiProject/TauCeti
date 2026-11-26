/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.BoundedDomain
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Operator
import TauCeti.Analysis.Holder.C2HolderBoundary.Extension
import TauCeti.Analysis.Holder.Coefficient
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity

/-!
# The Dirichlet problem in `C^{2,α}(Ω)` by the method of continuity

Let `0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary
(`Set.HasC2HolderBoundary`). For coefficients `aⁱʲ`, `bⁱ`, `c` in the bounded `α`-Hölder functions
on `Ω`, let

`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u`

be the operator `TauCeti.CkHolderSpaceOn.nonDivergenceOperatorL` from `C^{2,α}(Ω)` to `C^{0,α}(Ω)`,
with `a` uniformly elliptic and `c ≤ 0`. This file reduces the solvability of the Dirichlet problem
`L u = f` in `Ω`, `u = 0` on `∂Ω`, in the Banach space of the elements of `C^{2,α}(Ω)` vanishing on
the frontier (`TauCeti.CkHolderSpaceOn.vanishingOnFrontierSubmodule`), to that of Poisson's
equation.

* **The a priori estimate**
  (`TauCeti.CkHolderSpaceOn.exists_norm_le_mul_norm_nonDivergenceOperatorL`). There is a constant
  `C`, depending only on `Ω`, `α`, the ellipticity constant `λ` and a bound `M` on the norms of
  the coefficients, with

  `‖u‖_{C^{2,α}(Ω)} ≤ C ‖L u‖_{C^{0,α}(Ω)}`

  for every `u ∈ C^{2,α}(Ω)` vanishing on `∂Ω` (Gilbarg–Trudinger, Theorem 6.6, with `sup |u|`
  bounded by the maximum principle, Theorem 3.7). It does not depend on the coefficients beyond
  `λ` and `M`.
* **The method of continuity**
  (`TauCeti.CkHolderSpaceOn.forall_exists_nonDivergenceOperatorL_eq_iff`). For two such operators
  `L₀` and `L₁`, with ellipticity constants `λ₀` and `λ₁`, the Dirichlet problem for `L₀` is
  solvable for every `f ∈ C^{0,α}(Ω)` if and only if the one for `L₁` is. Along the segment
  `L_t = (1 - t) L₀ + t L₁`, whose coefficients are the convex combinations of those of `L₀` and
  `L₁` and so satisfy the same bounds, with ellipticity constant `min λ₀ λ₁`, the a priori
  estimate holds with one constant, and the
  abstract method of continuity (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`)
  applies on the Banach space of the elements vanishing on `∂Ω`.
* **Reduction to the Laplacian**
  (`TauCeti.CkHolderSpaceOn.forall_exists_nonDivergenceOperatorL_eq_iff_laplacianL`). Taking
  `L₀ = Δ`, the Dirichlet problem for `L` is solvable in `C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)`
  exactly when Poisson's equation `Δu = f`, `u = 0` on `∂Ω` is (Gilbarg–Trudinger, Theorem 6.8
  for zero boundary values). The solution is then unique, by the maximum principle
  (`TauCeti.CkHolderSpaceOn.injOn_nonDivergenceOperatorL`). Solvability of Poisson's equation in
  `C^{2,α}(Ω)` on a domain with `C^{2,α}` boundary is Kellogg's theorem, which with this reduction
  gives Gilbarg–Trudinger, Theorem 6.14, for zero boundary values. Nonzero boundary values
  `φ ∈ C^{2,α}` follow by subtracting an extension of `φ`, which this file does not treat.

## The a priori estimate

The global estimate
`exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos`, in the
`TauCeti.PDE` namespace, is stated for functions that are `C²` on an open set containing
`closure Ω`, with coefficients defined up to the boundary. An element of `C^{2,α}(Ω)` vanishing on
`∂Ω` is the restriction of a `C²` function `w` on the whole space that vanishes on `∂Ω` and whose
second derivative is Hölder on `closure Ω`
(`TauCeti.CkHolderSpaceOn.exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule`). The
coefficients, Hölder on `Ω`, extend to Hölder functions on `closure Ω`
(`TauCeti.HolderSpace.exists_holderOnWith_closure`), and ellipticity and the bounds pass to the
closure by continuity; a bound on the entries bounds the quadratic form from above
(`Matrix.toQuadraticForm'_le_of_forall_abs_le`). The estimate then bounds the values, the first
and second derivatives of `w` and the Hölder constant of the second derivative on `closure Ω`,
which bound the norm of `u`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 3.7, Theorem 5.2 (the method of continuity), Theorem 6.6 (the global estimate),
  Theorem 6.8 (solvability by the method of continuity) and Theorem 6.14.
-/

public section

namespace TauCeti.CkHolderSpaceOn

open Set Filter Topology TopologicalSpace
open scoped NNReal

variable {n : ℕ} {α : ℝ≥0} {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  (hΩ : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).IsLipschitzDomain E')
  (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))

/-- The principal coefficients, Hölder on `Ω` with norms at most `M` and uniformly elliptic with
constant `λ` there, extend to a matrix field on the whole space whose entries are `α`-Hölder on
`closure Ω` with constant `M` and bounded there by `M`, and which is uniformly elliptic with
constant `λ` on `closure Ω`. -/
private theorem exists_matrix_eq_and_holderOnWith_closure (hα0 : 0 < α) {lam : ℝ} {M : ℝ≥0}
    {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (haM : ∀ i j, ‖a i j‖ ≤ M) :
    ∃ A : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      (∀ (x : Ω) (i j), A x i j = a i j x) ∧
      (∀ z ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
        ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ (A z).toQuadraticForm' ξ) ∧
      (∀ i j, HolderOnWith M α (fun z ↦ A z i j) (closure Ω)) ∧
      ∀ z ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ∀ i j, |A z i j| ≤ M := by
  choose A hAΩ hAH using fun i j ↦
    (a i j).exists_holderOnWith_closure (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) hα0
  have hAc (i j) : ContinuousOn (A i j) (closure Ω) := (hAH i j).continuousOn hα0
  refine ⟨fun z ↦ Matrix.of fun i j ↦ A i j z, fun x i j ↦ hAΩ i j x, fun z hz ξ ↦ ?_,
    fun i j ↦ (hAH i j).mono_const (by exact_mod_cast haM i j), fun z hz i j ↦ ?_⟩
  · -- Ellipticity passes to `closure Ω` by continuity of the quadratic form.
    have hq : ContinuousOn (fun z ↦ (Matrix.of fun i j ↦ A i j z).toQuadraticForm' ξ)
        (closure Ω) := by
      simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
    refine ContinuousWithinAt.closure_le hz continuousWithinAt_const
      ((hq z hz).mono subset_closure) fun y hy ↦ ?_
    have h := ha ⟨y, hy⟩ ξ
    simp only [← hAΩ _ _ ⟨y, hy⟩] at h
    exact h
  · -- So do the bounds on the entries.
    refine ContinuousWithinAt.closure_le hz
      (((hAc i j).continuousWithinAt hz).mono subset_closure).abs continuousWithinAt_const
      fun y hy ↦ ?_
    rw [hAΩ i j ⟨y, hy⟩]
    exact (HolderSpace.abs_apply_le_norm _ _).trans (haM i j)

/-- The drift coefficients, Hölder on `Ω`, are the coordinates on `Ω` of a vector field that is
`α`-Hölder on `Ω` with constant the sum of their norms. -/
private theorem exists_vectorField_eq_and_holderOnWith (hα0 : 0 < α)
    (b : Fin (n + 1) → HolderSpace α Ω ℝ) :
    ∃ B : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (∀ x : Ω, B x = ∑ i, b i x • EuclideanSpace.single i (1 : ℝ)) ∧
      HolderOnWith (∑ i, ‖b i‖₊) α B Ω := by
  choose B hBΩ hBH using fun i ↦
    (b i).exists_holderOnWith_closure (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) hα0
  -- Multiplying a scalar by a unit vector is an isometry.
  have hiso (i : Fin (n + 1)) : Isometry fun t : ℝ ↦ t • EuclideanSpace.single i (1 : ℝ) :=
    (LinearIsometry.toSpanSingleton ℝ _ ((EuclideanSpace.orthonormal_single (𝕜 := ℝ)).1 i)).isometry
  exact ⟨fun z ↦ ∑ i, B i z • EuclideanSpace.single i (1 : ℝ),
    fun x ↦ by simp only [hBΩ], HolderOnWith.sum (s := Finset.univ) fun i _ ↦
      (hiso i).comp_holderOnWith ((hBH i).mono subset_closure)⟩

/-- An element of `C^{2,α}(Ω)` agreeing on `Ω` with `w`, whose value, first and second derivatives
are bounded by `N` on `Ω` and whose second derivative is `α`-Hölder on `Ω` with constant `K`, has
norm at most `3 N + K`. -/
private theorem norm_le_of_forall_abs_le_of_holderOnWith (u : CkHolderSpaceOn 2 α Ω ℝ)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hwu : ∀ x : Ω, w x = u x) {N : ℝ} {K : ℝ≥0}
    (hN : 0 ≤ N) (h0 : ∀ x : Ω, |w x| ≤ N) (h1 : ∀ x : Ω, ‖fderiv ℝ w x‖ ≤ N)
    (h2 : ∀ x : Ω, ‖_root_.iteratedFDeriv ℝ 2 w x‖ ≤ N)
    (hK : HolderOnWith K α (_root_.iteratedFDeriv ℝ 2 w) Ω) : ‖u‖ ≤ 3 * N + K := by
  have hfield (i : Fin 3) (x : Ω) : ‖u.iteratedFDeriv i x‖ ≤ N := by
    rw [← u.iteratedFDeriv_eq hwu i x]
    fin_cases i
    · simpa only [Fin.zero_eta, Fin.val_zero, _root_.norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        using h0 x
    · simpa only [Fin.mk_one, Fin.val_one, norm_iteratedFDeriv_one] using h1 x
    · exact h2 x
  have hholder : HolderWith K α
      (u.iteratedFDeriv (Fin.last 2) : Ω → EuclideanSpace ℝ (Fin (n + 1)) [×2]→L[ℝ] ℝ) := by
    have h := hK.holderWith
    have he : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).domRestrict
        (_root_.iteratedFDeriv ℝ 2 w) = (u.iteratedFDeriv (Fin.last 2) : Ω → _) :=
      funext fun x ↦ u.iteratedFDeriv_eq hwu (Fin.last 2) x
    rwa [he] at h
  calc ‖u‖ ≤ ∑ _i : Fin 3, N + K :=
        norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith (fun _ ↦ hN) hfield hholder
    _ = 3 * N + K := by simp

/-- **The Schauder a priori estimate for the Dirichlet problem in `C^{2,α}(Ω)`.** Let
`0 < α < 1` and let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary. Given `λ > 0`
and `M ≥ 0`, there is a constant `C` with the following property. Let the coefficients `aⁱʲ`,
`bⁱ` and `c` of `L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u` lie in the bounded `α`-Hölder functions on
`Ω`, with norms at most `M`, let `a` be uniformly elliptic with constant `λ` on `Ω` and let
`c ≤ 0`. Then every `u ∈ C^{2,α}(Ω)` vanishing on the frontier of `Ω` satisfies
`‖u‖_{C^{2,α}(Ω)} ≤ C ‖L u‖_{C^{0,α}(Ω)}`.

The constant depends only on `Ω`, `α`, `λ` and `M` (Gilbarg–Trudinger, Theorem 6.6 with the
maximum principle, Theorem 3.7). The sign condition `c ≤ 0` cannot be dropped: `u = sin x` on
`(0, π)` vanishes on the boundary and solves `u'' + u = 0`. -/
theorem exists_norm_le_mul_norm_nonDivergenceOperatorL (hα0 : 0 < α) (hα1 : α < 1)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α) {lam : ℝ}
    (hlam : 0 < lam) (M : ℝ≥0) :
    ∃ C : ℝ, ∀ {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
      {b : Fin (n + 1) → HolderSpace α Ω ℝ} {c : HolderSpace α Ω ℝ},
      (∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
        lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ) →
      (∀ i j, ‖a i j‖ ≤ M) → (∀ i, ‖b i‖ ≤ M) → ‖c‖ ≤ M → (∀ x : Ω, c x ≤ 0) →
      ∀ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        ‖u‖ ≤ C * ‖nonDivergenceOperatorL hΩ hb hα1.le a b c u‖ := by
  -- The global estimate, for coefficients whose bounds are given by `M`.
  set B : ℝ≥0 := (n + 2) * M
  obtain ⟨C₀, hC₀⟩ :=
    PDE.exists_abs_le_and_holderOnWith_iteratedFDeriv_two_closure_of_add_fderiv_add_mul_of_nonpos
      hα0 hα1 hb hbdry (∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), (M : ℝ)) M M B hlam
  refine ⟨8 * C₀, fun {a b c} ha haM hbM hcM hc0 u hu ↦ ?_⟩
  have hMB : (M : ℝ) ≤ B := by
    simp only [B]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) M.coe_nonneg, M.coe_nonneg]
  have hbB : ∑ i, ‖b i‖ ≤ B := (Finset.sum_le_sum fun i _ ↦ hbM i).trans (by
    simp only [B, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast
    nlinarith [M.coe_nonneg])
  -- The coefficients on `closure Ω`, and a `C²` representative of `u` vanishing on `∂Ω`.
  obtain ⟨A, hAΩ, hEll, hAH, hAb⟩ := exists_matrix_eq_and_holderOnWith_closure hα0 ha haM
  obtain ⟨V, hVΩ, hVH⟩ := exists_vectorField_eq_and_holderOnWith hα0 b
  obtain ⟨γ, hγΩ, hγH⟩ :=
    c.exists_holderOnWith_closure (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) hα0
  obtain ⟨w, hw, hwu, hw0, hwH⟩ :=
    exists_contDiff_eq_of_mem_vanishingOnFrontierSubmodule hbdry hb hα0 hu
  -- `L u`, read through `w` and the extended coefficients.
  set f := nonDivergenceOperatorL hΩ hb hα1.le a b c u
  have hf (x : Ω) : f x = ∑ i, ∑ j, A x i j •
      fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        fderiv ℝ w x (V x) + γ x * w x := by
    rw [nonDivergenceOperatorL_apply hΩ hb hα1.le u hwu, hVΩ]
    simp only [hAΩ, hγΩ, smul_eq_mul, map_sum, map_smul]
  obtain ⟨h0, h2, h1, h2'⟩ := hC₀ (a := A) (b := V) (c := γ) hEll
    (fun z hz ξ ↦ Matrix.toQuadraticForm'_le_of_forall_abs_le (hAb z hz) ξ) hAH hAb
    (hVH.mono_const (by rw [← NNReal.coe_le_coe]; push_cast; exact hbB))
    (fun z hz ↦ (hVΩ ⟨z, hz⟩ ▸ HolderSpace.norm_sum_apply_smul_single_le_sum_norm b ⟨z, hz⟩).trans
      hbB)
    ((hγH.mono subset_closure).mono_const (by exact_mod_cast hcM.trans hMB))
    (fun z hz ↦ hγΩ ⟨z, hz⟩ ▸ ((HolderSpace.abs_apply_le_norm c ⟨z, hz⟩).trans hcM).trans hMB)
    (fun z hz ↦ hγΩ ⟨z, hz⟩ ▸ hc0 ⟨z, hz⟩) isOpen_univ (subset_univ _) hw.contDiffOn hw0 hwH
    (K := ‖f‖₊) (F := ‖f‖₊) (f.holderOnWith_of_apply_eq fun x ↦ hf x) (fun z hz ↦ by
      have h := HolderSpace.abs_apply_le_norm f ⟨z, hz⟩
      rw [hf ⟨z, hz⟩] at h
      exact h)
  -- The bounds on `closure Ω` bound the norm of `u`.
  calc ‖u‖ ≤ 3 * (C₀ * (‖f‖₊ + ‖f‖₊) : ℝ) + (C₀ * (‖f‖₊ + ‖f‖₊) : ℝ≥0) :=
        norm_le_of_forall_abs_le_of_holderOnWith u hwu (by positivity)
          (fun x ↦ (h0 x (subset_closure x.property)).trans
            (by gcongr; exact le_add_of_nonneg_left (NNReal.coe_nonneg _)))
          (fun x ↦ h1 x (subset_closure x.property)) (fun x ↦ h2' x (subset_closure x.property))
          (h2.mono subset_closure)
    _ = 8 * C₀ * ‖f‖ := by
        simp only [NNReal.coe_mul, NNReal.coe_add, coe_nnNorm]
        ring

/-- **The method of continuity for the Dirichlet problem in `C^{2,α}(Ω)`.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary, and let
`L₀ u = ∑ᵢⱼ a₀ⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ b₀ⁱ ∂ᵢu + c₀ u` and `L₁ u = ∑ᵢⱼ a₁ⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ b₁ⁱ ∂ᵢu + c₁ u` have
coefficients in the bounded `α`-Hölder functions on `Ω`, with `a₀` and `a₁` uniformly elliptic
with constants `λ₀ > 0` and `λ₁ > 0` and `c₀, c₁ ≤ 0`. Then the Dirichlet problem `L₀ u = f` in `Ω`,
`u = 0` on `∂Ω`, has a solution `u ∈ C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)` if and only if the
Dirichlet problem for `L₁` does (Gilbarg–Trudinger, Theorems 5.2 and 6.8). -/
theorem forall_exists_nonDivergenceOperatorL_eq_iff (hα0 : 0 < α) (hα1 : α < 1)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α) {lam₀ lam₁ : ℝ}
    (hlam₀ : 0 < lam₀) (hlam₁ : 0 < lam₁) {a₀ a₁ : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
    {b₀ b₁ : Fin (n + 1) → HolderSpace α Ω ℝ} {c₀ c₁ : HolderSpace α Ω ℝ}
    (ha₀ : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam₀ * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a₀ i j x).toQuadraticForm' ξ)
    (ha₁ : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam₁ * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a₁ i j x).toQuadraticForm' ξ)
    (hc₀ : ∀ x : Ω, c₀ x ≤ 0) (hc₁ : ∀ x : Ω, c₁ x ≤ 0) :
    (∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        nonDivergenceOperatorL hΩ hb hα1.le a₀ b₀ c₀ u = f) ↔
      ∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        nonDivergenceOperatorL hΩ hb hα1.le a₁ b₁ c₁ u = f := by
  set V := vanishingOnFrontierSubmodule 2 α Ω ℝ
  -- A common bound `M` on the norms of all the coefficients.
  set S : Set (HolderSpace α Ω ℝ) :=
    range (Function.uncurry a₀) ∪ range (Function.uncurry a₁) ∪ range b₀ ∪ range b₁ ∪ {c₀, c₁}
  obtain ⟨M, hM⟩ : BddAbove (norm '' S) :=
    ((((((finite_range _).union (finite_range _)).union (finite_range _)).union
      (finite_range _)).union (toFinite _)).image _).bddAbove
  have hS {f} (hf : f ∈ S) : ‖f‖ ≤ M := hM (mem_image_of_mem _ hf)
  have hM0 : 0 ≤ M := (norm_nonneg c₀).trans (hS (by simp [S]))
  obtain ⟨C, hC⟩ := exists_norm_le_mul_norm_nonDivergenceOperatorL hΩ hb hα0 hα1 hbdry
    (lt_min hlam₀ hlam₁) ⟨M, hM0⟩
  -- The convex combinations of the coefficients satisfy the same bounds.
  have hnorm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {f₀ f₁ : HolderSpace α Ω ℝ} (h₀ : f₀ ∈ S)
      (h₁ : f₁ ∈ S) : ‖AffineMap.lineMap f₀ f₁ t‖ ≤ M := by
    simpa using (convex_closedBall (0 : HolderSpace α Ω ℝ) M).lineMap_mem
      (by simpa using hS h₀) (by simpa using hS h₁) ht
  -- The operators restricted to the elements vanishing on `∂Ω`.
  set T : (Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ) → (Fin (n + 1) → HolderSpace α Ω ℝ) →
      HolderSpace α Ω ℝ → V →L[ℝ] HolderSpace α Ω ℝ :=
    fun a b c ↦ nonDivergenceOperatorL hΩ hb hα1.le a b c ∘L V.subtypeL
  have hsurj (a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ)
      (b : Fin (n + 1) → HolderSpace α Ω ℝ) (c : HolderSpace α Ω ℝ) :
      Function.Surjective (T a b c) ↔
        ∀ f, ∃ u ∈ V, nonDivergenceOperatorL hΩ hb hα1.le a b c u = f :=
    ⟨fun h f ↦ let ⟨u, hu⟩ := h f; ⟨u, u.property, hu⟩,
      fun h f ↦ let ⟨u, hu, huf⟩ := h f; ⟨⟨u, hu⟩, huf⟩⟩
  rw [← hsurj, ← hsurj]
  refine ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap (C := C) fun t ht u ↦ ?_
  -- Along the segment, the operators are those of the convex combinations of the coefficients.
  have hT : AffineMap.lineMap (T a₀ b₀ c₀) (T a₁ b₁ c₁) t u =
      nonDivergenceOperatorL hΩ hb hα1.le (AffineMap.lineMap a₀ a₁ t) (AffineMap.lineMap b₀ b₁ t)
        (AffineMap.lineMap c₀ c₁ t) u := by
    rw [nonDivergenceOperatorL_lineMap]
    simp only [T, AffineMap.lineMap_apply_module, _root_.add_apply,
      _root_.smul_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [hT, ← Submodule.norm_coe]
  refine hC (fun x ξ ↦ ?_) (fun i j ↦ hnorm ht (by simp [S]) (by simp [S]))
    (fun i ↦ hnorm ht (by simp [S]) (by simp [S])) (hnorm ht (by simp [S]) (by simp [S]))
    (fun x ↦ ?_) u u.property
  · -- The matrix is the convex combination of the two matrices, and so is its quadratic form.
    have hA : (Matrix.of fun i j ↦ AffineMap.lineMap (a₀ i j) (a₁ i j) t x) =
        (1 - t) • (Matrix.of fun i j ↦ a₀ i j x) + t • Matrix.of fun i j ↦ a₁ i j x := by
      ext i j
      simp [AffineMap.lineMap_apply_module, HolderSpace.add_apply, HolderSpace.smul_apply]
    rw [hA, Matrix.toQuadraticForm'_add, Matrix.toQuadraticForm'_smul,
      Matrix.toQuadraticForm'_smul]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    nlinarith [(mul_le_mul_of_nonneg_right (min_le_left lam₀ lam₁) (sq_nonneg ‖ξ‖)).trans
      (ha₀ x ξ), (mul_le_mul_of_nonneg_right (min_le_right lam₀ lam₁) (sq_nonneg ‖ξ‖)).trans
      (ha₁ x ξ), ht.1, ht.2]
  · simp only [AffineMap.lineMap_apply_module, HolderSpace.add_apply, HolderSpace.smul_apply,
      smul_eq_mul]
    nlinarith [hc₀ x, hc₁ x, ht.1, ht.2]

/-- **Reduction of the Dirichlet problem to Poisson's equation.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{2,α}` boundary, and let
`L u = ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu + ∑ᵢ bⁱ ∂ᵢu + c u` have coefficients in the bounded `α`-Hölder functions on
`Ω`, with `a` uniformly elliptic and `c ≤ 0`. Then the Dirichlet problem `L u = f` in `Ω`, `u = 0`
on `∂Ω`, has a solution `u ∈ C^{2,α}(Ω)` for every `f ∈ C^{0,α}(Ω)` if and only if the Dirichlet
problem for Poisson's equation `Δu = f` does (Gilbarg–Trudinger, Theorem 6.8, for zero boundary
values). The solution is unique (`TauCeti.CkHolderSpaceOn.injOn_nonDivergenceOperatorL`). -/
theorem forall_exists_nonDivergenceOperatorL_eq_iff_laplacianL (hα0 : 0 < α) (hα1 : α < 1)
    (hbdry : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))).HasC2HolderBoundary α) {lam : ℝ}
    (hlam : 0 < lam) {a : Fin (n + 1) → Fin (n + 1) → HolderSpace α Ω ℝ}
    {b : Fin (n + 1) → HolderSpace α Ω ℝ} {c : HolderSpace α Ω ℝ}
    (ha : ∀ (x : Ω) (ξ : EuclideanSpace ℝ (Fin (n + 1))),
      lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j x).toQuadraticForm' ξ)
    (hc : ∀ x : Ω, c x ≤ 0) :
    (∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        nonDivergenceOperatorL hΩ hb hα1.le a b c u = f) ↔
      ∀ f : HolderSpace α Ω ℝ, ∃ u ∈ vanishingOnFrontierSubmodule 2 α Ω ℝ,
        laplacianL α Ω ℝ u = f := by
  rw [← nonDivergenceOperatorL_eq_laplacianL hΩ hb hα1.le]
  refine forall_exists_nonDivergenceOperatorL_eq_iff hΩ hb hα0 hα1 hbdry hlam one_pos ha
    (fun x ξ ↦ ?_) hc fun _ ↦ le_rfl
  -- The identity matrix has quadratic form `‖ξ‖²`.
  have hI : (Matrix.of fun i j ↦ (if i = j then (1 : HolderSpace α Ω ℝ) else 0) x) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, HolderSpace.one_apply,
      HolderSpace.zero_apply]
  rw [hI, PDE.toQuadraticForm'_one, one_mul]

end TauCeti.CkHolderSpaceOn
