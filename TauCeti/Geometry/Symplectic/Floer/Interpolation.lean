/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import TauCeti.Algebra.BigOperators.Finset.WeightedVariance
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Convex combinations of Hamiltonian perturbation data

Floer-theoretic constructions do not depend on the choice of Hamiltonian perturbation data
`K = K_s ds + K_t dt`. The comparison between two choices `K⁰`, `K¹` with the same ends uses the
path `(1 - λ) K⁰ + λ K¹`, and comparisons between several choices use families parametrized by a
simplex, `∑ λᵢ Kⁱ` with `λᵢ ≥ 0` and `∑ λᵢ = 1`. Patching local data by a partition of unity
`βᵢ` on the domain produces the same kind of combination with domain-dependent weights. Since the
energy identity turns curvature bounds into energy bounds, compactness for such a family needs a
bound on the curvature of the combination that is uniform in the weights.

The target is a manifold `M` with a smooth two-form `ω`, such as a closed symplectic manifold, and
the Hamiltonian vector fields and Poisson brackets are the intrinsic ones of
`TauCeti.Geometry.Symplectic.Hamiltonian.Manifold`. The curvature
`R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` (`TauCeti.SmoothTwoForm.hamiltonianCurvature`) is linear in
`K` up to the quadratic Poisson bracket term. If the weights `βᵢ` sum to `1` at the domain point,
the defect of this quadratic term is a variance:

`R_{∑ βᵢ Kⁱ} = ∑ βᵢ R_{Kⁱ} + ½ ∑ᵢ ∑ⱼ βᵢ βⱼ {Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}`
`  + ∑ ((∂_s βᵢ) Kⁱ_t - (∂_t βᵢ) Kⁱ_s)`

(`SmoothTwoForm.hamiltonianCurvature_sum_mul`). The middle term only involves the differences of
the data, so it vanishes wherever the data agree, and the last term vanishes for constant weights.
Consequently:

* for constant weights in the standard simplex, `|R_{∑ λᵢ Kⁱ}|` is at most `M₀ + P / 2` whenever
  `M₀` bounds every `|R_{Kⁱ}|` and `P` bounds every `|{Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}|`
  (`SmoothTwoForm.abs_hamiltonianCurvature_sum_const_mul_le`), and the same holds after
  integration along a map (`SmoothTwoForm.integral_abs_hamiltonianCurvature_sum_const_mul_le`)
  and, for a nondegenerate form, for the difference between the Floer energy over a rectangle and
  its topological part
  (`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_sum_const_mul_sub_le`);
* where all the data agree near a point, so does every combination with weights summing to `1`,
  and its curvature is the common curvature
  (`SmoothTwoForm.hamiltonianCurvature_sum_mul_of_eventuallyEq`). On cylindrical ends where the
  data all equal `H_t dt`, the curvature of every member of the family therefore vanishes.

For two data, `SmoothTwoForm.hamiltonianCurvature_one_sub_mul_add_mul` is the formula for
`(1 - β) K⁰ + β K¹`, with cross term `(β - β²) {K¹_s - K⁰_s, K¹_t - K⁰_t}`. The case `K⁰ = 0` is
the cutoff formula `TauCeti.SymplecticForm.hamiltonianCurvature_mul` for a vector space target,
which holds without the target differentiability needed here to expand the Poisson bracket of a
sum.

A symplectic vector space `(V, ω)` is the case of the constant form
`TauCeti.SymplecticForm.constSmooth`; the corresponding `TauCeti.SymplecticForm` statements are
derived from the manifold ones. For a vector space target the energy estimate needs no
integrability hypotheses (`SymplecticForm.abs_integral_floerEnergyDensity_sum_const_mul_sub_le`),
since the energy identity `TauCeti.SymplecticForm.integral_floerEnergyDensity` provides them.

These are statements about the perturbation data and the energy identity; no moduli space,
compactness theorem or transversality is asserted.

## Main results

* `SmoothTwoForm.hamiltonianCurvature_sum_mul`: the curvature of `∑ βᵢ Kⁱ` with weights summing
  to `1`.
* `SmoothTwoForm.hamiltonianCurvature_one_sub_mul_add_mul`: the case of two data.
* `SmoothTwoForm.abs_hamiltonianCurvature_sum_const_mul_le`: the pointwise bound, uniform over the
  simplex of constant weights.
* `SmoothTwoForm.integral_abs_hamiltonianCurvature_sum_const_mul_le`,
  `SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_sum_const_mul_sub_le`: the
  integrated curvature and energy bounds, uniform over the simplex.
* `SmoothTwoForm.hamiltonianCurvature_sum_mul_of_eventuallyEq`: where the data agree, the
  combination has their common curvature.
* `SymplecticForm.hamiltonianCurvature_sum_mul` and the other `TauCeti.SymplecticForm` statements:
  the same for a symplectic vector space.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9, on the contractibility
  of the spaces of perturbation data and the families comparing different choices.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped Manifold

/-! ### Manifold targets -/

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ι : Type*} {s : Finset ι} {Ks Kt : ι → ℝ × ℝ → M → ℝ}

/-- **Curvature of a convex combination of perturbation data.** Let `βᵢ` be weights on the domain
summing to `1` at `z`. For a smooth two-form `ω` on a manifold, the curvature of the combination
`∑ βᵢ Kⁱ` of the perturbations `Kⁱ = Kⁱ_s ds + Kⁱ_t dt` is

`∑ βᵢ R_{Kⁱ} + ½ ∑ᵢ ∑ⱼ βᵢ βⱼ {Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t} + ∑ ((∂_s βᵢ) Kⁱ_t - (∂_t βᵢ) Kⁱ_s)`.

The weights and data are assumed differentiable in the domain variable at `z`, and the data in
the target variable at `x`. -/
theorem hamiltonianCurvature_sum_mul (ω : SmoothTwoForm I M) {β : ι → ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    {x : M} (hβ : ∀ i ∈ s, DifferentiableAt ℝ (β i) z)
    (hKs : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w x) z)
    (hKt : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w x) z)
    (hKs' : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Ks i z) x)
    (hKt' : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Kt i z) x) (hsum : ∑ i ∈ s, β i z = 1) :
    ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, β i w * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, β i w * Kt i w y) z x =
      ∑ i ∈ s, β i z * ω.hamiltonianCurvature (Ks i) (Kt i) z x +
        (∑ i ∈ s, ∑ j ∈ s, β i z * β j z *
          ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x) / 2 +
        ∑ i ∈ s, (fderiv ℝ (β i) z stdComplexLineReal * Kt i z x -
          fderiv ℝ (β i) z stdComplexLineImag * Ks i z x) := by
  -- The Poisson bracket terms, in terms of `Bᵢⱼ = {Kⁱ_s, Kʲ_t}`: the bracket of the combination is
  -- `∑ᵢ ∑ⱼ βᵢ βⱼ Bᵢⱼ`, and its defect from `∑ βᵢ Bᵢᵢ` is the variance term.
  have hvar := Finset.sum_sum_mul_smul_sub_sub_add_eq s hsum
    (fun i j ↦ ω.poissonBracket (Ks i z) (Kt j z) x)
  simp only [smul_eq_mul] at hvar
  have hmul {f : M → ℝ} (hf : MDifferentiableAt I 𝓘(ℝ) f x) (c : ℝ) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ c * f y) x := by
    simpa only [Pi.smul_def, smul_eq_mul] using hf.const_smul c
  have hsmul (c : ℝ) (f : M → ℝ) : (fun y ↦ c * f y) = c • f := by
    simp only [Pi.smul_def, smul_eq_mul]
  have hcomb : ω.poissonBracket (fun y ↦ ∑ i ∈ s, β i z * Ks i z y)
      (fun y ↦ ∑ i ∈ s, β i z * Kt i z y) x =
        ∑ i ∈ s, ∑ j ∈ s, β i z * β j z * ω.poissonBracket (Ks i z) (Kt j z) x := by
    rw [poissonBracket_fun_sum_left (F := fun i y ↦ β i z * Ks i z y)
      fun i hi ↦ hmul (hKs' i hi) _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hsmul (β i z) (Ks i z),
      poissonBracket_const_smul_left, smul_eq_mul, poissonBracket_fun_sum_right
      (G := fun j y ↦ β j z * Kt j z y) fun j hj ↦ hmul (hKt' j hj) _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hsmul (β j z) (Kt j z),
      poissonBracket_const_smul_right, smul_eq_mul]
    ring
  have hbracket : ∑ i ∈ s, ∑ j ∈ s, β i z * β j z *
      ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x =
        ∑ i ∈ s, ∑ j ∈ s, β i z * β j z *
          (ω.poissonBracket (Ks i z) (Kt i z) x - ω.poissonBracket (Ks i z) (Kt j z) x -
            ω.poissonBracket (Ks j z) (Kt i z) x + ω.poissonBracket (Ks j z) (Kt j z) x) :=
    Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ by
      rw [poissonBracket_sub_left (hKs' i hi) (hKs' j hj),
        poissonBracket_sub_right (hKt' i hi) (hKt' j hj),
        poissonBracket_sub_right (hKt' i hi) (hKt' j hj)]
      ring
  -- The derivative of each component of the combination, by the product rule.
  have hderiv (K : ι → ℝ × ℝ → M → ℝ) (hK : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ K i w x) z)
      (v : ℝ × ℝ) :
      fderiv ℝ (fun w ↦ ∑ i ∈ s, β i w * K i w x) z v =
        ∑ i ∈ s, (β i z * fderiv ℝ (fun w ↦ K i w x) z v + fderiv ℝ (β i) z v * K i z x) := by
    rw [fderiv_fun_sum (A := fun i w ↦ β i w * K i w x) fun i hi ↦ (hβ i hi).mul (hK i hi)]
    simp only [sum_apply]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [fderiv_fun_mul (hβ i hi) (hK i hi)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hamiltonianCurvature_def, hderiv Ks hKs, hderiv Kt hKt, hcomb, hbracket, hvar]
  simp only [hamiltonianCurvature_def, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- **Curvature of an interpolation between two perturbation data.** For a smooth two-form on a
manifold and a weight `β` on the domain, the curvature of `(1 - β) K⁰ + β K¹` is

`(1 - β) R_{K⁰} + β R_{K¹} + (β - β²) {K¹_s - K⁰_s, K¹_t - K⁰_t}`

plus the terms `(∂_s β) (K¹_t - K⁰_t) - (∂_t β) (K¹_s - K⁰_s)` from the derivative of `β`. -/
theorem hamiltonianCurvature_one_sub_mul_add_mul (ω : SmoothTwoForm I M)
    {Ks₀ Kt₀ Ks₁ Kt₁ : ℝ × ℝ → M → ℝ} {β : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {x : M}
    (hβ : DifferentiableAt ℝ β z) (hKs₀ : DifferentiableAt ℝ (fun w ↦ Ks₀ w x) z)
    (hKt₀ : DifferentiableAt ℝ (fun w ↦ Kt₀ w x) z)
    (hKs₁ : DifferentiableAt ℝ (fun w ↦ Ks₁ w x) z)
    (hKt₁ : DifferentiableAt ℝ (fun w ↦ Kt₁ w x) z)
    (hKs₀' : MDifferentiableAt I 𝓘(ℝ) (Ks₀ z) x) (hKt₀' : MDifferentiableAt I 𝓘(ℝ) (Kt₀ z) x)
    (hKs₁' : MDifferentiableAt I 𝓘(ℝ) (Ks₁ z) x) (hKt₁' : MDifferentiableAt I 𝓘(ℝ) (Kt₁ z) x) :
    ω.hamiltonianCurvature (fun w y ↦ (1 - β w) * Ks₀ w y + β w * Ks₁ w y)
        (fun w y ↦ (1 - β w) * Kt₀ w y + β w * Kt₁ w y) z x =
      (1 - β z) * ω.hamiltonianCurvature Ks₀ Kt₀ z x + β z * ω.hamiltonianCurvature Ks₁ Kt₁ z x +
        (β z - β z ^ 2) * ω.poissonBracket (Ks₁ z - Ks₀ z) (Kt₁ z - Kt₀ z) x +
        fderiv ℝ β z stdComplexLineReal * (Kt₁ z x - Kt₀ z x) -
        fderiv ℝ β z stdComplexLineImag * (Ks₁ z x - Ks₀ z x) := by
  have h := ω.hamiltonianCurvature_sum_mul (s := Finset.univ) (β := ![fun w ↦ 1 - β w, β])
    (Ks := ![Ks₀, Ks₁]) (Kt := ![Kt₀, Kt₁]) (z := z) (x := x)
    (by simp [Fin.forall_fin_two, hβ])
    (by simp [Fin.forall_fin_two, hKs₀, hKs₁]) (by simp [Fin.forall_fin_two, hKt₀, hKt₁])
    (by simp [Fin.forall_fin_two, hKs₀', hKs₁']) (by simp [Fin.forall_fin_two, hKt₀', hKt₁'])
    (by simp)
  have hneg : Ks₀ z - Ks₁ z = -(Ks₁ z - Ks₀ z) ∧ Kt₀ z - Kt₁ z = -(Kt₁ z - Kt₀ z) :=
    ⟨(neg_sub _ _).symm, (neg_sub _ _).symm⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self,
    poissonBracket_self, hneg.1, hneg.2, poissonBracket_neg_left, poissonBracket_neg_right,
    neg_neg, fderiv_const_sub, neg_apply] at h
  rw [h]
  ring

/-- **Curvature of a convex combination with constant weights.** For a smooth two-form on a
manifold and constant weights `cᵢ` with `∑ cᵢ = 1`, the curvature of `∑ cᵢ Kⁱ` is
`∑ cᵢ R_{Kⁱ} + ½ ∑ᵢ ∑ⱼ cᵢ cⱼ {Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}`. -/
theorem hamiltonianCurvature_sum_const_mul (ω : SmoothTwoForm I M) (c : ι → ℝ) {z : ℝ × ℝ}
    {x : M} (hKs : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w x) z)
    (hKt : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w x) z)
    (hKs' : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Ks i z) x)
    (hKt' : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Kt i z) x) (hc : ∑ i ∈ s, c i = 1) :
    ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) z x =
      ∑ i ∈ s, c i * ω.hamiltonianCurvature (Ks i) (Kt i) z x +
        (∑ i ∈ s, ∑ j ∈ s, c i * c j *
          ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x) / 2 := by
  simpa using ω.hamiltonianCurvature_sum_mul (β := fun i _ ↦ c i)
    (fun _ _ ↦ differentiableAt_const _) hKs hKt hKs' hKt' hc

/-- **Uniform pointwise curvature bound over the simplex.** For a smooth two-form on a manifold,
let `M₀` bound the curvatures `|R_{Kⁱ}|` and `P` bound the Poisson brackets
`|{Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}|` of the differences at `(z, x)`. Then for all nonnegative constant
weights `cᵢ` with `∑ cᵢ = 1`, the curvature of `∑ cᵢ Kⁱ` is bounded by `M₀ + P / 2`. -/
theorem abs_hamiltonianCurvature_sum_const_mul_le (ω : SmoothTwoForm I M) {c : ι → ℝ}
    (hc₀ : ∀ i ∈ s, 0 ≤ c i) (hc : ∑ i ∈ s, c i = 1) {z : ℝ × ℝ} {x : M}
    (hKs : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w x) z)
    (hKt : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w x) z)
    (hKs' : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Ks i z) x)
    (hKt' : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Kt i z) x) {M₀ P : ℝ}
    (hM : ∀ i ∈ s, |ω.hamiltonianCurvature (Ks i) (Kt i) z x| ≤ M₀)
    (hP : ∀ i ∈ s, ∀ j ∈ s, |ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x| ≤ P) :
    |ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) z x| ≤ M₀ + P / 2 := by
  rw [ω.hamiltonianCurvature_sum_const_mul c hKs hKt hKs' hKt' hc]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- The convex combination of the curvatures.
    calc |∑ i ∈ s, c i * ω.hamiltonianCurvature (Ks i) (Kt i) z x|
        ≤ ∑ i ∈ s, c i * M₀ := (Finset.abs_sum_le_sum_abs _ _).trans <|
          Finset.sum_le_sum fun i hi ↦ by
            rw [abs_mul, abs_of_nonneg (hc₀ i hi)]
            exact mul_le_mul_of_nonneg_left (hM i hi) (hc₀ i hi)
      _ = M₀ := by rw [← Finset.sum_mul, hc, one_mul]
  · -- The variance term.
    rw [abs_div, abs_two]
    gcongr
    calc |∑ i ∈ s, ∑ j ∈ s, c i * c j *
          ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x|
        ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * P :=
          (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun i hi ↦
            (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum fun j hj ↦ by
              rw [abs_mul, abs_of_nonneg (mul_nonneg (hc₀ i hi) (hc₀ j hj))]
              exact mul_le_mul_of_nonneg_left (hP i hi j hj) (mul_nonneg (hc₀ i hi) (hc₀ j hj))
      _ = P := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum, hc, mul_one, one_mul]

/-- **Uniform integrated curvature bound over the simplex.** For a smooth two-form on a manifold,
let the data be differentiable in the domain variable at the points `z` of a measurable set `D` of
the domain, and in the target variable at `u z`. Let `M₀` and `P` bound the curvatures `|R_{Kⁱ}|`
and the Poisson brackets of the differences `|{Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}|` along the map `u` over
`D`. Then for all nonnegative constant weights `cᵢ` with `∑ cᵢ = 1`, the integrated curvature of
`∑ cᵢ Kⁱ` along `u` over `D` is at most `∫ (M₀ + P / 2)`. -/
theorem integral_abs_hamiltonianCurvature_sum_const_mul_le (ω : SmoothTwoForm I M) {c : ι → ℝ}
    (hc₀ : ∀ i ∈ s, 0 ≤ c i) (hc : ∑ i ∈ s, c i = 1) (u : ℝ × ℝ → M) {D : Set (ℝ × ℝ)}
    (hD : MeasurableSet D)
    (hKs : ∀ z ∈ D, ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w (u z)) z)
    (hKt : ∀ z ∈ D, ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w (u z)) z)
    (hKs' : ∀ z ∈ D, ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Ks i z) (u z))
    (hKt' : ∀ z ∈ D, ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (Kt i z) (u z))
    {M₀ P : ℝ × ℝ → ℝ}
    (hM : ∀ z ∈ D, ∀ i ∈ s, |ω.hamiltonianCurvature (Ks i) (Kt i) z (u z)| ≤ M₀ z)
    (hP : ∀ z ∈ D, ∀ i ∈ s, ∀ j ∈ s,
      |ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) (u z)| ≤ P z)
    (hMi : IntegrableOn M₀ D) (hPi : IntegrableOn P D) :
    ∫ z in D, |ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) z (u z)| ≤ ∫ z in D, (M₀ z + P z / 2) :=
  integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (hMi.add (hPi.div_const 2))
    (ae_restrict_of_forall_mem hD fun z hz ↦
      ω.abs_hamiltonianCurvature_sum_const_mul_le hc₀ hc (hKs z hz) (hKt z hz) (hKs' z hz)
        (hKt' z hz) (hM z hz) (hP z hz))

/-- **Uniform energy estimate over the simplex.** For a nondegenerate two-form on a
finite-dimensional manifold, let the map `u` and the data `Kⁱ` be `C¹` over an open neighbourhood
`U` of the rectangle `[a₁, b₁] × [a₂, b₂]`, and let `M₀` and `P` bound the curvatures `|R_{Kⁱ}|`
and the Poisson brackets of the differences `|{Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}|` along `u` over the
rectangle. Let `K = ∑ cᵢ Kⁱ` for nonnegative constant weights `cᵢ` with `∑ cᵢ = 1`, and suppose
that the energy density of `u` for `K` and the curvature `R_K(u)` are integrable over the
rectangle. Then the Floer energy of `u` over the rectangle for `K` differs from its symplectic area
`∫ u^* ω` plus the boundary integral of the pulled-back one-form `K(u)` by at most
`∫ (M₀ + P / 2)` over the rectangle. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_sum_const_mul_sub_le
    [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate) {c : ι → ℝ}
    (hc₀ : ∀ i ∈ s, 0 ≤ c i) (hc : ∑ i ∈ s, c i = 1) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hKs : ∀ i ∈ s, ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Ks i)) (U ×ˢ univ))
    (hKt : ∀ i ∈ s, ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Kt i)) (U ×ˢ univ))
    {a b : ℝ × ℝ} (hab : a ≤ b) (habU : Icc a b ⊆ U)
    (hE : IntegrableOn (ω.floerEnergyDensity (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
      (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) u) (Icc a b))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
      (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) z (u z)) (Icc a b))
    {M₀ P : ℝ × ℝ → ℝ}
    (hM : ∀ z ∈ Icc a b, ∀ i ∈ s, |ω.hamiltonianCurvature (Ks i) (Kt i) z (u z)| ≤ M₀ z)
    (hP : ∀ z ∈ Icc a b, ∀ i ∈ s, ∀ j ∈ s,
      |ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) (u z)| ≤ P z)
    (hMi : IntegrableOn M₀ (Icc a b)) (hPi : IntegrableOn P (Icc a b)) :
    |(∫ z in Icc a b, ω.floerEnergyDensity (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) u z) -
      ((∫ z in Icc a b, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ σ in a.1..b.1, ∑ i ∈ s, c i * Ks i (σ, a.2) (u (σ, a.2))) +
          (∫ τ in a.2..b.2, ∑ i ∈ s, c i * Kt i (b.1, τ) (u (b.1, τ))) -
          (∫ σ in a.1..b.1, ∑ i ∈ s, c i * Ks i (σ, b.2) (u (σ, b.2))) -
          ∫ τ in a.2..b.2, ∑ i ∈ s, c i * Kt i (a.1, τ) (u (a.1, τ))))| ≤
      ∫ z in Icc a b, (M₀ z + P z / 2) := by
  have hcomb {K : ι → ℝ × ℝ → M → ℝ}
      (hK : ∀ i ∈ s, ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry (K i)) (U ×ˢ univ)) :
      ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry fun w y ↦ ∑ i ∈ s, c i * K i w y)
        (U ×ˢ univ) :=
    contMDiffOn_finsetSum fun i hi ↦ contMDiffOn_const.mul (hK i hi)
  have hdiff {K : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ Icc a b) : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry K) (z, u z) :=
    (hK.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨habU hz, mem_univ _⟩)).mdifferentiableAt
      one_ne_zero
  -- Joint differentiability gives differentiability in each variable separately.
  have hleft {K : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ Icc a b) : DifferentiableAt ℝ (fun w ↦ K w (u z)) z :=
    mdifferentiableAt_iff_differentiableAt.1
      ((hdiff hK hz).comp z (mdifferentiableAt_id.prodMk mdifferentiableAt_const))
  have hright {K : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ Icc a b) : MDifferentiableAt I 𝓘(ℝ) (K z) (u z) :=
    (hdiff hK hz).comp (u z) (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [hω.integral_floerEnergyDensity hU hu (hcomb hKs) (hcomb hKt) hab habU hE hR,
    sub_sub_cancel_left, abs_neg]
  exact abs_integral_le_integral_abs.trans
    (ω.integral_abs_hamiltonianCurvature_sum_const_mul_le hc₀ hc u measurableSet_Icc
      (fun z hz i hi ↦ hleft (hKs i hi) hz) (fun z hz i hi ↦ hleft (hKt i hi) hz)
      (fun z hz i hi ↦ hright (hKs i hi) hz) (fun z hz i hi ↦ hright (hKt i hi) hz) hM hP hMi hPi)

/-- **Combinations of agreeing data.** For a smooth two-form on a manifold, if the data `Kⁱ` all
agree with `K⁰` near `z` and the weights `βᵢ` sum to `1` near `z`, then `∑ βᵢ Kⁱ` has the curvature
of `K⁰` at `z`. In particular every member of a family of data with common cylindrical ends
`H_t dt` has zero curvature there (`TauCeti.SmoothTwoForm.hamiltonianCurvature_cylindrical`). No
differentiability is assumed. -/
theorem hamiltonianCurvature_sum_mul_of_eventuallyEq (ω : SmoothTwoForm I M)
    {β : ι → ℝ × ℝ → ℝ} {Ks₀ Kt₀ : ℝ × ℝ → M → ℝ} {z : ℝ × ℝ}
    (hs : ∀ i ∈ s, Ks i =ᶠ[𝓝 z] Ks₀) (ht : ∀ i ∈ s, Kt i =ᶠ[𝓝 z] Kt₀)
    (hsum : ∀ᶠ w in 𝓝 z, ∑ i ∈ s, β i w = 1) :
    ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, β i w * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, β i w * Kt i w y) z =
      ω.hamiltonianCurvature Ks₀ Kt₀ z := by
  have key {K : ι → ℝ × ℝ → M → ℝ} {K₀ : ℝ × ℝ → M → ℝ} (hK : ∀ i ∈ s, K i =ᶠ[𝓝 z] K₀) :
      (fun w y ↦ ∑ i ∈ s, β i w * K i w y) =ᶠ[𝓝 z] K₀ := by
    filter_upwards [(eventually_all_finset s).2 hK, hsum] with w hw hw₁
    funext y
    rw [Finset.sum_congr rfl fun i hi ↦ by rw [hw i hi], ← Finset.sum_mul, hw₁, one_mul]
  exact ω.hamiltonianCurvature_congr_of_eventuallyEq (key hs) (key ht)

end TauCeti.SmoothTwoForm

/-! ### Symplectic vector spaces

The statements for a symplectic vector space are the case of the constant form
`TauCeti.SymplecticForm.constSmooth`. -/

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} {s : Finset ι} {Ks Kt : ι → ℝ × ℝ → V → ℝ}

/-- **Curvature of a convex combination of perturbation data.** Let `βᵢ` be weights on the domain
summing to `1` at `z`. The curvature of the combination `∑ βᵢ Kⁱ` of the perturbations
`Kⁱ = Kⁱ_s ds + Kⁱ_t dt` is

`∑ βᵢ R_{Kⁱ} + ½ ∑ᵢ ∑ⱼ βᵢ βⱼ {Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t} + ∑ ((∂_s βᵢ) Kⁱ_t - (∂_t βᵢ) Kⁱ_s)`.

The weights and data are assumed differentiable in the domain variable at `z`, and the data in
the target variable at `x`. -/
theorem hamiltonianCurvature_sum_mul (ω : SymplecticForm V) {β : ι → ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    {x : V} (hβ : ∀ i ∈ s, DifferentiableAt ℝ (β i) z)
    (hKs : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w x) z)
    (hKt : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w x) z)
    (hKs' : ∀ i ∈ s, DifferentiableAt ℝ (Ks i z) x)
    (hKt' : ∀ i ∈ s, DifferentiableAt ℝ (Kt i z) x) (hsum : ∑ i ∈ s, β i z = 1) :
    ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, β i w * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, β i w * Kt i w y) z x =
      ∑ i ∈ s, β i z * ω.hamiltonianCurvature (Ks i) (Kt i) z x +
        (∑ i ∈ s, ∑ j ∈ s, β i z * β j z *
          ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x) / 2 +
        ∑ i ∈ s, (fderiv ℝ (β i) z stdComplexLineReal * Kt i z x -
          fderiv ℝ (β i) z stdComplexLineImag * Ks i z x) := by
  simpa only [hamiltonianCurvature_constSmooth, poissonBracket_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_sum_mul hβ hKs hKt
      (fun i hi ↦ (hKs' i hi).mdifferentiableAt) (fun i hi ↦ (hKt' i hi).mdifferentiableAt) hsum

/-- **Curvature of an interpolation between two perturbation data.** For a weight `β` on the
domain, the curvature of `(1 - β) K⁰ + β K¹` is

`(1 - β) R_{K⁰} + β R_{K¹} + (β - β²) {K¹_s - K⁰_s, K¹_t - K⁰_t}`

plus the terms `(∂_s β) (K¹_t - K⁰_t) - (∂_t β) (K¹_s - K⁰_s)` from the derivative of `β`.

For `K⁰ = 0` this is `TauCeti.SymplecticForm.hamiltonianCurvature_mul`. -/
theorem hamiltonianCurvature_one_sub_mul_add_mul (ω : SymplecticForm V)
    {Ks₀ Kt₀ Ks₁ Kt₁ : ℝ × ℝ → V → ℝ} {β : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {x : V}
    (hβ : DifferentiableAt ℝ β z) (hKs₀ : DifferentiableAt ℝ (fun w ↦ Ks₀ w x) z)
    (hKt₀ : DifferentiableAt ℝ (fun w ↦ Kt₀ w x) z)
    (hKs₁ : DifferentiableAt ℝ (fun w ↦ Ks₁ w x) z)
    (hKt₁ : DifferentiableAt ℝ (fun w ↦ Kt₁ w x) z) (hKs₀' : DifferentiableAt ℝ (Ks₀ z) x)
    (hKt₀' : DifferentiableAt ℝ (Kt₀ z) x) (hKs₁' : DifferentiableAt ℝ (Ks₁ z) x)
    (hKt₁' : DifferentiableAt ℝ (Kt₁ z) x) :
    ω.hamiltonianCurvature (fun w y ↦ (1 - β w) * Ks₀ w y + β w * Ks₁ w y)
        (fun w y ↦ (1 - β w) * Kt₀ w y + β w * Kt₁ w y) z x =
      (1 - β z) * ω.hamiltonianCurvature Ks₀ Kt₀ z x + β z * ω.hamiltonianCurvature Ks₁ Kt₁ z x +
        (β z - β z ^ 2) * ω.poissonBracket (Ks₁ z - Ks₀ z) (Kt₁ z - Kt₀ z) x +
        fderiv ℝ β z stdComplexLineReal * (Kt₁ z x - Kt₀ z x) -
        fderiv ℝ β z stdComplexLineImag * (Ks₁ z x - Ks₀ z x) := by
  simpa only [hamiltonianCurvature_constSmooth, poissonBracket_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_one_sub_mul_add_mul hβ hKs₀ hKt₀ hKs₁ hKt₁
      hKs₀'.mdifferentiableAt hKt₀'.mdifferentiableAt hKs₁'.mdifferentiableAt
      hKt₁'.mdifferentiableAt

/-- **Curvature of a convex combination with constant weights.** For constant weights `cᵢ` with
`∑ cᵢ = 1`, the curvature of `∑ cᵢ Kⁱ` is
`∑ cᵢ R_{Kⁱ} + ½ ∑ᵢ ∑ⱼ cᵢ cⱼ {Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}`. -/
theorem hamiltonianCurvature_sum_const_mul (ω : SymplecticForm V) (c : ι → ℝ) {z : ℝ × ℝ}
    {x : V} (hKs : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w x) z)
    (hKt : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w x) z)
    (hKs' : ∀ i ∈ s, DifferentiableAt ℝ (Ks i z) x)
    (hKt' : ∀ i ∈ s, DifferentiableAt ℝ (Kt i z) x) (hc : ∑ i ∈ s, c i = 1) :
    ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) z x =
      ∑ i ∈ s, c i * ω.hamiltonianCurvature (Ks i) (Kt i) z x +
        (∑ i ∈ s, ∑ j ∈ s, c i * c j *
          ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x) / 2 := by
  simpa only [hamiltonianCurvature_constSmooth, poissonBracket_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_sum_const_mul c hKs hKt
      (fun i hi ↦ (hKs' i hi).mdifferentiableAt) (fun i hi ↦ (hKt' i hi).mdifferentiableAt) hc

/-- **Uniform pointwise curvature bound over the simplex.** Let `M` bound the curvatures
`|R_{Kⁱ}|` and `P` bound the Poisson brackets `|{Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}|` of the differences
at `(z, x)`. Then for all nonnegative constant weights `cᵢ` with `∑ cᵢ = 1`, the curvature of
`∑ cᵢ Kⁱ` is bounded by `M + P / 2`. -/
theorem abs_hamiltonianCurvature_sum_const_mul_le (ω : SymplecticForm V) {c : ι → ℝ}
    (hc₀ : ∀ i ∈ s, 0 ≤ c i) (hc : ∑ i ∈ s, c i = 1) {z : ℝ × ℝ} {x : V}
    (hKs : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w x) z)
    (hKt : ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w x) z)
    (hKs' : ∀ i ∈ s, DifferentiableAt ℝ (Ks i z) x)
    (hKt' : ∀ i ∈ s, DifferentiableAt ℝ (Kt i z) x) {M P : ℝ}
    (hM : ∀ i ∈ s, |ω.hamiltonianCurvature (Ks i) (Kt i) z x| ≤ M)
    (hP : ∀ i ∈ s, ∀ j ∈ s, |ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) x| ≤ P) :
    |ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) z x| ≤ M + P / 2 := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.abs_hamiltonianCurvature_sum_const_mul_le hc₀ hc hKs hKt
      (fun i hi ↦ (hKs' i hi).mdifferentiableAt) (fun i hi ↦ (hKt' i hi).mdifferentiableAt)
      (by simpa only [hamiltonianCurvature_constSmooth] using hM)
      (by simpa only [poissonBracket_constSmooth] using hP)

/-- **Uniform integrated curvature bound over the simplex.** Let the data be differentiable in
the domain variable at the points `z` of a measurable set `D` of the domain, and in the target
variable at `u z`. Let `M` and `P` bound the curvatures `|R_{Kⁱ}|` and the Poisson brackets of the
differences `|{Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}|` along the map `u` over `D`. Then for all nonnegative
constant weights `cᵢ` with `∑ cᵢ = 1`, the integrated curvature of `∑ cᵢ Kⁱ` along `u` over `D` is
at most `∫ (M + P / 2)`. -/
theorem integral_abs_hamiltonianCurvature_sum_const_mul_le (ω : SymplecticForm V) {c : ι → ℝ}
    (hc₀ : ∀ i ∈ s, 0 ≤ c i) (hc : ∑ i ∈ s, c i = 1) (u : ℝ × ℝ → V) {D : Set (ℝ × ℝ)}
    (hD : MeasurableSet D)
    (hKs : ∀ z ∈ D, ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Ks i w (u z)) z)
    (hKt : ∀ z ∈ D, ∀ i ∈ s, DifferentiableAt ℝ (fun w ↦ Kt i w (u z)) z)
    (hKs' : ∀ z ∈ D, ∀ i ∈ s, DifferentiableAt ℝ (Ks i z) (u z))
    (hKt' : ∀ z ∈ D, ∀ i ∈ s, DifferentiableAt ℝ (Kt i z) (u z))
    {M P : ℝ × ℝ → ℝ}
    (hM : ∀ z ∈ D, ∀ i ∈ s, |ω.hamiltonianCurvature (Ks i) (Kt i) z (u z)| ≤ M z)
    (hP : ∀ z ∈ D, ∀ i ∈ s, ∀ j ∈ s,
      |ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) (u z)| ≤ P z)
    (hMi : IntegrableOn M D) (hPi : IntegrableOn P D) :
    ∫ z in D, |ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) z (u z)| ≤ ∫ z in D, (M z + P z / 2) := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.integral_abs_hamiltonianCurvature_sum_const_mul_le hc₀ hc u hD hKs hKt
      (fun z hz i hi ↦ (hKs' z hz i hi).mdifferentiableAt)
      (fun z hz i hi ↦ (hKt' z hz i hi).mdifferentiableAt)
      (by simpa only [hamiltonianCurvature_constSmooth] using hM)
      (by simpa only [poissonBracket_constSmooth] using hP) hMi hPi

/-- **Uniform energy estimate over the simplex.** Let the map `u` and the data `Kⁱ` be `C¹` over
an open neighbourhood `U` of the rectangle `[a₁, b₁] × [a₂, b₂]`, and let `M` and `P` bound the
curvatures `|R_{Kⁱ}|` and the Poisson brackets of the differences `|{Kⁱ_s - Kʲ_s, Kⁱ_t - Kʲ_t}|`
along `u` over the rectangle. Then for all nonnegative constant weights `cᵢ` with `∑ cᵢ = 1`, the
Floer energy of `u` over the rectangle for the perturbation `K = ∑ cᵢ Kⁱ` differs from its
symplectic area plus the boundary integral of the pulled-back one-form `K(u)` by at most
`∫ (M + P / 2)` over the rectangle. -/
theorem abs_integral_floerEnergyDensity_sum_const_mul_sub_le (ω : SymplecticForm V)
    {c : ι → ℝ} (hc₀ : ∀ i ∈ s, 0 ≤ c i) (hc : ∑ i ∈ s, c i = 1) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 1 u U)
    (hKs : ∀ i ∈ s, ContDiffOn ℝ 1 (uncurry (Ks i)) (U ×ˢ univ))
    (hKt : ∀ i ∈ s, ContDiffOn ℝ 1 (uncurry (Kt i)) (U ×ˢ univ)) {a b : ℝ × ℝ} (hab : a ≤ b)
    (habU : Icc a b ⊆ U) {M P : ℝ × ℝ → ℝ}
    (hM : ∀ z ∈ Icc a b, ∀ i ∈ s, |ω.hamiltonianCurvature (Ks i) (Kt i) z (u z)| ≤ M z)
    (hP : ∀ z ∈ Icc a b, ∀ i ∈ s, ∀ j ∈ s,
      |ω.poissonBracket (Ks i z - Ks j z) (Kt i z - Kt j z) (u z)| ≤ P z)
    (hMi : IntegrableOn M (Icc a b)) (hPi : IntegrableOn P (Icc a b)) :
    |(∫ z in Icc a b, ω.floerEnergyDensity (fun w y ↦ ∑ i ∈ s, c i * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, c i * Kt i w y) u z) -
      ((∫ z in Icc a b,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ((∫ σ in a.1..b.1, ∑ i ∈ s, c i * Ks i (σ, a.2) (u (σ, a.2))) +
          (∫ τ in a.2..b.2, ∑ i ∈ s, c i * Kt i (b.1, τ) (u (b.1, τ))) -
          (∫ σ in a.1..b.1, ∑ i ∈ s, c i * Ks i (σ, b.2) (u (σ, b.2))) -
          ∫ τ in a.2..b.2, ∑ i ∈ s, c i * Kt i (a.1, τ) (u (a.1, τ))))| ≤
      ∫ z in Icc a b, (M z + P z / 2) := by
  have hcomb {K : ι → ℝ × ℝ → V → ℝ} (hK : ∀ i ∈ s, ContDiffOn ℝ 1 (uncurry (K i)) (U ×ˢ univ)) :
      ContDiffOn ℝ 1 (uncurry fun w y ↦ ∑ i ∈ s, c i * K i w y) (U ×ˢ univ) :=
    ContDiffOn.sum fun i hi ↦ contDiffOn_const.mul (hK i hi)
  have hdiff {K : ℝ × ℝ → V → ℝ} (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ Icc a b) : DifferentiableAt ℝ (uncurry K) (z, u z) :=
    (hK.differentiableOn one_ne_zero _ ⟨habU hz, mem_univ _⟩).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds ⟨habU hz, mem_univ _⟩)
  -- Joint differentiability gives differentiability in each variable separately.
  have hleft {K : ℝ × ℝ → V → ℝ} (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ Icc a b) : DifferentiableAt ℝ (fun w ↦ K w (u z)) z := by
    have h := (hdiff hK hz).hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℝ) z (u z))
    exact h.differentiableAt
  have hright {K : ℝ × ℝ → V → ℝ} (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) {z : ℝ × ℝ}
      (hz : z ∈ Icc a b) : DifferentiableAt ℝ (K z) (u z) := by
    have h := (hdiff hK hz).hasFDerivAt.comp (u z) (hasFDerivAt_prodMk_right (𝕜 := ℝ) z (u z))
    exact h.differentiableAt
  rw [ω.integral_floerEnergyDensity hU hu (hcomb hKs) (hcomb hKt) hab habU, sub_sub_cancel_left,
    abs_neg]
  exact abs_integral_le_integral_abs.trans
    (ω.integral_abs_hamiltonianCurvature_sum_const_mul_le hc₀ hc u measurableSet_Icc
      (fun z hz i hi ↦ hleft (hKs i hi) hz) (fun z hz i hi ↦ hleft (hKt i hi) hz)
      (fun z hz i hi ↦ hright (hKs i hi) hz) (fun z hz i hi ↦ hright (hKt i hi) hz) hM hP hMi hPi)

/-- **Combinations of agreeing data.** If the data `Kⁱ` all agree with `K⁰` near `z` and the
weights `βᵢ` sum to `1` near `z`, then `∑ βᵢ Kⁱ` has the curvature of `K⁰` at `z`. In particular
every member of a family of data with common cylindrical ends `H_t dt` has zero curvature there
(`TauCeti.SymplecticForm.hamiltonianCurvature_cylindrical`). No differentiability is assumed. -/
theorem hamiltonianCurvature_sum_mul_of_eventuallyEq (ω : SymplecticForm V)
    {β : ι → ℝ × ℝ → ℝ} {Ks₀ Kt₀ : ℝ × ℝ → V → ℝ} {z : ℝ × ℝ}
    (hs : ∀ i ∈ s, Ks i =ᶠ[𝓝 z] Ks₀) (ht : ∀ i ∈ s, Kt i =ᶠ[𝓝 z] Kt₀)
    (hsum : ∀ᶠ w in 𝓝 z, ∑ i ∈ s, β i w = 1) :
    ω.hamiltonianCurvature (fun w y ↦ ∑ i ∈ s, β i w * Ks i w y)
        (fun w y ↦ ∑ i ∈ s, β i w * Kt i w y) z =
      ω.hamiltonianCurvature Ks₀ Kt₀ z := by
  funext x
  simpa only [hamiltonianCurvature_constSmooth] using
    congrFun (ω.constSmooth.hamiltonianCurvature_sum_mul_of_eventuallyEq hs ht hsum) x

end TauCeti.SymplecticForm
