/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Cutting off Hamiltonian perturbation data

Comparison arguments in Floer theory deform an inhomogeneous Floer equation to an unperturbed
(pseudoholomorphic) one by multiplying the Hamiltonian perturbation one-form
`K = K_s ds + K_t dt` by a cutoff: either a domain-dependent function `β`, as on the planes of the
Piunikhin–Salamon–Schwarz maps, or a constant `ρ ∈ [0, 1]`, as in a one-parameter family
`K_R = ρ(R) K` interpolating between `K` and the zero perturbation. The energy identity
`TauCeti.SymplecticForm.integral_floerEnergyDensity` turns curvature bounds into energy bounds,
so such a family needs a curvature bound that is uniform in the cutoff.

The curvature `R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` is not linear in `K`: its derivative part is
linear and its Poisson bracket part is quadratic. For a cutoff `β` this gives

`R_{βK} = β R_K + (β - β²) {K_s, K_t} + (∂_s β) K_t - (∂_t β) K_s`

(`SymplecticForm.hamiltonianCurvature_mul`), and for a constant `ρ` the last two terms vanish
(`SymplecticForm.hamiltonianCurvature_const_mul`). Since `0 ≤ ρ - ρ² ≤ 1/4` for `ρ ∈ [0, 1]`, the
curvature of `ρ K` is bounded by `|R_K| + |{K_s, K_t}| / 4` for every `ρ ∈ [0, 1]`, including the
cutoff-zero end `ρ = 0` where the perturbation and its curvature vanish. Hence the integrated
curvature and the defect between the Floer energy of `ρ K` and its topological part (symplectic
area plus `ρ` times the boundary integral of `K(u)`) are bounded uniformly along the whole family.

## Main results

* `SymplecticForm.hamiltonianCurvature_mul`: the curvature of the cut-off perturbation `β K`.
* `SymplecticForm.abs_hamiltonianCurvature_mul_le`: its pointwise bound for `0 ≤ β ≤ 1`.
* `SymplecticForm.hamiltonianCurvature_const_mul`: the curvature of the scaled perturbation `ρ K`.
* `SymplecticForm.abs_hamiltonianCurvature_const_mul_le`,
  `SymplecticForm.integral_abs_hamiltonianCurvature_const_mul_le`: the pointwise and integrated
  curvature bounds for `ρ K`, uniform in `ρ ∈ [0, 1]`.
* `SymplecticForm.abs_integral_floerEnergyDensity_const_mul_sub_le`: the Floer energy for `ρ K`
  over a rectangle differs from its topological part by at most the same constant, for every
  `ρ ∈ [0, 1]`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  cut-off Hamiltonian perturbations and the comparison with the unperturbed equation.
-/

public section

open Function MeasureTheory Set

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ}

section Scaling

/-- **Curvature of a scaled perturbation.** Scaling the perturbation `K = K_s ds + K_t dt` by a
constant `ρ` gives curvature `R_{ρK} = ρ R_K + (ρ - ρ²) {K_s, K_t}`. -/
theorem hamiltonianCurvature_const_mul (ω : SymplecticForm V) (ρ : ℝ) (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature (fun w y ↦ ρ * Ks w y) (fun w y ↦ ρ * Kt w y) z x =
      ρ * ω.hamiltonianCurvature Ks Kt z x + (ρ - ρ ^ 2) * ω.poissonBracket (Ks z) (Kt z) x := by
  have h (K : ℝ × ℝ → V → ℝ) : (fun w ↦ ρ * K w x) = ρ • fun w ↦ K w x := by
    ext
    simp
  simp only [hamiltonianCurvature_def, h, fderiv_const_smul_field, poissonBracket_const_mul_left,
    poissonBracket_const_mul_right, Pi.smul_apply, smul_apply, smul_eq_mul]
  ring

/-- **Uniform pointwise curvature bound for scaled perturbations.** For every `ρ ∈ [0, 1]`, the
curvature of `ρ K` is bounded by `|R_K| + |{K_s, K_t}| / 4`. -/
theorem abs_hamiltonianCurvature_const_mul_le (ω : SymplecticForm V) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) 1) (z : ℝ × ℝ) (x : V) :
    |ω.hamiltonianCurvature (fun w y ↦ ρ * Ks w y) (fun w y ↦ ρ * Kt w y) z x| ≤
      |ω.hamiltonianCurvature Ks Kt z x| + |ω.poissonBracket (Ks z) (Kt z) x| / 4 := by
  obtain ⟨h₀, h₁⟩ := hρ
  rw [hamiltonianCurvature_const_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg h₀]
    exact mul_le_of_le_one_left (abs_nonneg _) h₁
  · rw [abs_mul, abs_of_nonneg (by nlinarith)]
    nlinarith [abs_nonneg (ω.poissonBracket (Ks z) (Kt z) x), sq_nonneg (ρ - 1 / 2)]

/-- **Uniform integrated curvature bound for scaled perturbations.** Let `M` and `P` bound the
curvature `R_K` and the Poisson bracket `{K_s, K_t}` along a map `u` over a measurable set `s` of
the domain. Then for every `ρ ∈ [0, 1]`, the integrated curvature of `ρ K` along `u` over `s` is
at most `∫ (M + P / 4)`. -/
theorem integral_abs_hamiltonianCurvature_const_mul_le (ω : SymplecticForm V) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) 1) (u : ℝ × ℝ → V) {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    {M P : ℝ × ℝ → ℝ} (hM : ∀ z ∈ s, |ω.hamiltonianCurvature Ks Kt z (u z)| ≤ M z)
    (hP : ∀ z ∈ s, |ω.poissonBracket (Ks z) (Kt z) (u z)| ≤ P z) (hMi : IntegrableOn M s)
    (hPi : IntegrableOn P s) :
    ∫ z in s, |ω.hamiltonianCurvature (fun w y ↦ ρ * Ks w y) (fun w y ↦ ρ * Kt w y) z (u z)| ≤
      ∫ z in s, (M z + P z / 4) :=
  integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (hMi.add (hPi.div_const 4))
    (ae_restrict_of_forall_mem hs fun z hz ↦
      (ω.abs_hamiltonianCurvature_const_mul_le hρ z (u z)).trans
        (add_le_add (hM z hz) (div_le_div_of_nonneg_right (hP z hz) (by norm_num))))

/-- **Uniform energy estimate for scaled perturbations.** Let `K` and the map `u` be `C¹` over an
open neighbourhood `U` of the rectangle `[a₁, b₁] × [a₂, b₂]`, and let `M` and `P` bound `|R_K|`
and `|{K_s, K_t}|` along `u` over the rectangle. Then for every `ρ ∈ [0, 1]`, the Floer energy of
`u` for the perturbation `ρ K` differs from its symplectic area plus `ρ` times the boundary
integral of the pulled-back one-form `K(u)` by at most `∫ (M + P / 4)` over the rectangle. -/
theorem abs_integral_floerEnergyDensity_const_mul_sub_le (ω : SymplecticForm V) {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) 1) {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 1 u U) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ)) {a b : ℝ × ℝ} (hab : a ≤ b)
    (habU : Icc a b ⊆ U) {M P : ℝ × ℝ → ℝ}
    (hM : ∀ z ∈ Icc a b, |ω.hamiltonianCurvature Ks Kt z (u z)| ≤ M z)
    (hP : ∀ z ∈ Icc a b, |ω.poissonBracket (Ks z) (Kt z) (u z)| ≤ P z)
    (hMi : IntegrableOn M (Icc a b)) (hPi : IntegrableOn P (Icc a b)) :
    |(∫ z in Icc a b,
        ω.floerEnergyDensity (fun w y ↦ ρ * Ks w y) (fun w y ↦ ρ * Kt w y) u z) -
      ((∫ z in Icc a b,
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        ρ * ((∫ s in a.1..b.1, Ks (s, a.2) (u (s, a.2))) +
          (∫ t in a.2..b.2, Kt (b.1, t) (u (b.1, t))) -
          (∫ s in a.1..b.1, Ks (s, b.2) (u (s, b.2))) -
          ∫ t in a.2..b.2, Kt (a.1, t) (u (a.1, t))))| ≤
      ∫ z in Icc a b, (M z + P z / 4) := by
  rw [ω.integral_floerEnergyDensity hU hu (contDiffOn_const.mul hKs) (contDiffOn_const.mul hKt) hab
    habU]
  simp only [intervalIntegral.integral_const_mul]
  rw [show ∀ A B₁ B₂ B₃ B₄ I : ℝ, A + (ρ * B₁ + ρ * B₂ - ρ * B₃ - ρ * B₄) - I -
      (A + ρ * (B₁ + B₂ - B₃ - B₄)) = -I by intros; ring, abs_neg]
  exact abs_integral_le_integral_abs.trans
    (ω.integral_abs_hamiltonianCurvature_const_mul_le hρ u measurableSet_Icc hM hP hMi hPi)

end Scaling

section Cutoff

/-- **Curvature of a cut-off perturbation.** Multiplying the perturbation `K = K_s ds + K_t dt` by
a function `β` on the domain gives curvature
`R_{βK} = β R_K + (β - β²) {K_s, K_t} + (∂_s β) K_t - (∂_t β) K_s`. -/
theorem hamiltonianCurvature_mul (ω : SymplecticForm V) {β : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {x : V}
    (hβ : DifferentiableAt ℝ β z) (hKs : DifferentiableAt ℝ (fun w ↦ Ks w x) z)
    (hKt : DifferentiableAt ℝ (fun w ↦ Kt w x) z) :
    ω.hamiltonianCurvature (fun w y ↦ β w * Ks w y) (fun w y ↦ β w * Kt w y) z x =
      β z * ω.hamiltonianCurvature Ks Kt z x +
          (β z - β z ^ 2) * ω.poissonBracket (Ks z) (Kt z) x +
        fderiv ℝ β z stdComplexLineReal * Kt z x - fderiv ℝ β z stdComplexLineImag * Ks z x := by
  simp only [hamiltonianCurvature_def, fderiv_fun_mul hβ hKs, fderiv_fun_mul hβ hKt,
    poissonBracket_const_mul_left, poissonBracket_const_mul_right, add_apply, smul_apply,
    smul_eq_mul]
  ring

/-- **Curvature bound for a cut-off perturbation.** Where the cutoff `β` takes values in `[0, 1]`,
the curvature of `β K` is bounded by `|R_K| + |{K_s, K_t}| / 4`, the bound
`TauCeti.SymplecticForm.abs_hamiltonianCurvature_const_mul_le` for the constant `β z`, plus the
terms `|∂_s β| |K_t| + |∂_t β| |K_s|` coming from the derivative of the cutoff. -/
theorem abs_hamiltonianCurvature_mul_le (ω : SymplecticForm V) {β : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    {x : V} (hβ : DifferentiableAt ℝ β z) (hβz : β z ∈ Icc (0 : ℝ) 1)
    (hKs : DifferentiableAt ℝ (fun w ↦ Ks w x) z) (hKt : DifferentiableAt ℝ (fun w ↦ Kt w x) z) :
    |ω.hamiltonianCurvature (fun w y ↦ β w * Ks w y) (fun w y ↦ β w * Kt w y) z x| ≤
      |ω.hamiltonianCurvature Ks Kt z x| + |ω.poissonBracket (Ks z) (Kt z) x| / 4 +
        |fderiv ℝ β z stdComplexLineReal| * |Kt z x| +
        |fderiv ℝ β z stdComplexLineImag| * |Ks z x| := by
  have h := ω.abs_hamiltonianCurvature_const_mul_le (Ks := Ks) (Kt := Kt) hβz z x
  rw [hamiltonianCurvature_const_mul] at h
  rw [ω.hamiltonianCurvature_mul hβ hKs hKt, ← abs_mul, ← abs_mul]
  have h₁ := abs_add_le (β z * ω.hamiltonianCurvature Ks Kt z x +
    (β z - β z ^ 2) * ω.poissonBracket (Ks z) (Kt z) x) (fderiv ℝ β z stdComplexLineReal * Kt z x)
  have h₂ := abs_sub (β z * ω.hamiltonianCurvature Ks Kt z x +
    (β z - β z ^ 2) * ω.poissonBracket (Ks z) (Kt z) x + fderiv ℝ β z stdComplexLineReal * Kt z x)
    (fderiv ℝ β z stdComplexLineImag * Ks z x)
  linarith

end Cutoff

end TauCeti.SymplecticForm
