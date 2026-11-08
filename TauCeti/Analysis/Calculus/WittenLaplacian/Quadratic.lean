/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.WittenLaplacian.Basic
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Basic
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Calculus.Morse.Pi
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator

/-!
# The harmonic-oscillator model of the Witten Laplacian

Near a nondegenerate critical point a Morse function is, in suitable coordinates, a diagonal
quadratic function, and the Witten Laplacian of a diagonal quadratic function is a sum of
harmonic oscillators. This file computes that local model exactly.

Let `f = ∑ᵢ aᵢ xᵢ² / 2` on `ℝ^ι` (`TauCeti.diagonalQuadratic`), whose Hessian is diagonal with
eigenvalues `aᵢ`. It has a nondegenerate critical point at the origin exactly when every `aᵢ` is
nonzero, and then its Morse index is the number of negative `aᵢ`. By the frame formula
`TauCeti.euclideanWittenLaplacian_apply`, the Witten Laplacian acts on the coefficient of
`dx^s` as the operator

`∑ᵢ (-∂ᵢ² + t² aᵢ² xᵢ²) + t ∑ᵢ ±aᵢ`,

with `+aᵢ` when `i ∈ s` and `-aᵢ` otherwise
(`TauCeti.euclideanWittenLaplacian_diagonalQuadratic_apply`):
a sum of one-dimensional harmonic oscillators of frequencies `ωᵢ = t |aᵢ|`, shifted by a constant
that depends on the degree of the form. For `f = x²` on the line (`a = 2`) the coefficient of a
function is acted on by `-∂² + 4t² x² - 2t` and that of `dx` by `-∂² + 4t² x² + 2t`.

The oscillator `-∂² + ω² x²` has the eigenfunctions `ψₖ(√ω x)`, with `ψₖ` the Hermite functions,
and eigenvalues `ω (2k + 1)`. Hence for `t ≥ 0`, every multi-index `k : ι → ℕ` and every index set
`s`, the form

`Ψ_{k,s}(x) = ∏ᵢ ψ_{kᵢ}(√(t |aᵢ|) xᵢ) dx^s`

(`TauCeti.hermiteEigenform`) is an eigenform of the Witten Laplacian
(`TauCeti.euclideanWittenLaplacian_hermiteEigenform`), with eigenvalue

`μ(k, s) = t ∑ᵢ (|aᵢ| (2kᵢ + 1) ± aᵢ)` (`TauCeti.hermiteEigenvalue`).

Each summand `|aᵢ| (2kᵢ + 1) ± aᵢ` is `0` or at least `2 |aᵢ|`. So `μ ≥ 0`, and when every `aᵢ` is
nonzero and `t > 0`, `μ(k, s) = 0` exactly when `k = 0` and `s` is the set of indices with
`aᵢ < 0` (`TauCeti.hermiteEigenvalue_eq_zero_iff`): the ground state is a multiple of the
Gaussian `e^{-t ∑ᵢ |aᵢ| xᵢ² / 2} dx^s` (`TauCeti.hermiteEigenform_zero_apply`), a form whose degree
is the Morse index. Every other Hermite eigenform has eigenvalue at least `2t minᵢ |aᵢ|`
(`TauCeti.two_mul_mul_le_hermiteEigenvalue`), a gap growing linearly in `t`. For the standard model
`f = -|x⁻|² + |x⁺|²` all `|aᵢ|` are `2`, the ground state is a multiple of `e^{-t |x|²} dx^{I⁻}`
and the gap is `4t`.

In each degree `s`, the coefficients of the Hermite eigenforms are, after the dilation
`xᵢ ↦ √(t |aᵢ|) xᵢ`, the multi-index Hermite functions, which form the Hilbert basis
`TauCeti.hermiteFunctionPiBasis` of `L²(ℝ^ι)`. This is the computation behind Witten's proof of
the Morse inequalities, in which the low-lying spectrum of `Δ_t` is modelled near each critical
point by the ground state of this oscillator. The diagonal quadratic function is the normal form
of the Morse lemma, whose derivative also appears as `TauCeti.hasFDerivAt_diagonalQuadratic`.

## Main definitions

* `TauCeti.diagonalQuadratic`: the diagonal quadratic function `∑ᵢ aᵢ xᵢ² / 2`.
* `TauCeti.hermiteEigenform`: the Hermite eigenforms `Ψ_{k,s}` of its Witten Laplacian.
* `TauCeti.hermiteEigenvalue`: their eigenvalues `μ(k, s)`.

## Main results

* `TauCeti.isNondegenerateCriticalPoint_diagonalQuadratic_zero_iff`,
  `TauCeti.morseIndex_diagonalQuadratic`: the origin is a nondegenerate critical point exactly when
  every `aᵢ` is nonzero, of Morse index the number of negative `aᵢ`.
* `TauCeti.euclideanWittenLaplacian_diagonalQuadratic_apply`: the Witten Laplacian of a diagonal
  quadratic function is a sum of shifted harmonic oscillators.
* `TauCeti.euclideanWittenLaplacian_hermiteEigenform`: the Hermite eigenforms are eigenforms.
* `TauCeti.hermiteEigenvalue_nonneg`, `TauCeti.hermiteEigenvalue_eq_zero_iff`,
  `TauCeti.two_mul_mul_le_hermiteEigenvalue`: the eigenvalues are nonnegative, vanish exactly at
  the Gaussian ground state in the degree of the Morse index, and are otherwise bounded below by
  `2t minᵢ |aᵢ|`.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340, §2.
-/

public section

noncomputable section

namespace TauCeti

open Function

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

section DiagonalQuadratic

/-- The **diagonal quadratic function** `∑ᵢ aᵢ xᵢ² / 2` on `ℝ^ι`, whose Hessian is diagonal with
eigenvalues `aᵢ`. -/
def diagonalQuadratic (a : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, a i * x i ^ 2 / 2

omit [LinearOrder ι] in
theorem diagonalQuadratic_apply (a x : ι → ℝ) :
    diagonalQuadratic a x = ∑ i, a i * x i ^ 2 / 2 :=
  (rfl)

omit [LinearOrder ι] in
theorem contDiff_diagonalQuadratic (a : ι → ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (diagonalQuadratic a) := by
  unfold diagonalQuadratic
  fun_prop

omit [LinearOrder ι] in
/-- The summands of a diagonal quadratic function, as functions of one variable. -/
private theorem deriv_mul_sq_div_two (c y : ℝ) : deriv (fun y : ℝ ↦ c * y ^ 2 / 2) y = c * y := by
  have h := ((hasDerivAt_pow 2 y).const_mul c).div_const 2
  rw [h.deriv]
  ring

omit [LinearOrder ι] in
private theorem deriv_deriv_mul_sq_div_two (c y : ℝ) :
    deriv (deriv fun y : ℝ ↦ c * y ^ 2 / 2) y = c := by
  rw [funext (deriv_mul_sq_div_two c)]
  simp

omit [LinearOrder ι] in
/-- The partial derivatives of `∑ᵢ aᵢ xᵢ² / 2` are `aᵢ xᵢ`. -/
@[simp]
theorem fderiv_diagonalQuadratic_apply_single [DecidableEq ι] (a x : ι → ℝ) (i : ι) :
    fderiv ℝ (diagonalQuadratic a) x (Pi.single i 1) = a i * x i := by
  unfold diagonalQuadratic
  rw [fderiv_sum_comp_eval (φ := fun i y ↦ a i * y ^ 2 / 2) fun i ↦ by fun_prop]
  simp only [deriv_mul_sq_div_two, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [LinearOrder ι] in
/-- The Hessian of `∑ᵢ aᵢ xᵢ² / 2` is the diagonal form `∑ᵢ aᵢ vᵢ wᵢ`. -/
@[simp]
theorem fderiv_fderiv_diagonalQuadratic_apply (a x v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (diagonalQuadratic a)) x v w = ∑ i, a i * v i * w i := by
  unfold diagonalQuadratic
  rw [fderiv_fderiv_sum_comp_eval_apply (φ := fun i y ↦ a i * y ^ 2 / 2) fun i ↦ by fun_prop]
  simp [deriv_deriv_mul_sq_div_two]

omit [LinearOrder ι] in
/-- The origin is a nondegenerate critical point of `∑ᵢ aᵢ xᵢ² / 2` exactly when every `aᵢ` is
nonzero. -/
theorem isNondegenerateCriticalPoint_diagonalQuadratic_zero_iff (a : ι → ℝ) :
    IsNondegenerateCriticalPoint (diagonalQuadratic a) 0 ↔ ∀ i, a i ≠ 0 := by
  unfold diagonalQuadratic
  rw [isNondegenerateCriticalPoint_sum_comp_eval_iff (φ := fun i y ↦ a i * y ^ 2 / 2)
    fun i ↦ by fun_prop]
  simp [deriv_deriv_mul_sq_div_two]

omit [LinearOrder ι] in
/-- The Morse index of `∑ᵢ aᵢ xᵢ² / 2` is the number of negative `aᵢ`. -/
@[simp]
theorem morseIndex_diagonalQuadratic (a x : ι → ℝ) :
    morseIndex (diagonalQuadratic a) x = (Finset.univ.filter fun i ↦ a i < 0).card := by
  classical
  unfold diagonalQuadratic
  rw [morseIndex_sum_comp_eval (φ := fun i y ↦ a i * y ^ 2 / 2) fun i ↦ by fun_prop]
  simp [deriv_deriv_mul_sq_div_two, ← Set.ncard_coe_finset]

end DiagonalQuadratic

section Model

variable {a : ι → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ}

/-- **The Witten Laplacian of a diagonal quadratic function** acts on the coefficient of `dx^s` as
the sum of harmonic oscillators `∑ᵢ (-∂ᵢ² + t² aᵢ² xᵢ²)` shifted by `t ∑ᵢ ±aᵢ`, with `+aᵢ` when
`i ∈ s` and `-aᵢ` otherwise. -/
theorem euclideanWittenLaplacian_diagonalQuadratic_apply {x : ι → ℝ} (hφ : ContDiffAt ℝ 2 φ x)
    (t : ℝ) (s : Finset ι) :
    euclideanWittenLaplacian (diagonalQuadratic a) t φ x s =
      ∑ i, (-fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (Pi.single i 1) s +
          t ^ 2 * a i ^ 2 * x i ^ 2 * φ x s) +
        t * (∑ i, if i ∈ s then a i else -a i) * φ x s := by
  rw [euclideanWittenLaplacian_apply (contDiff_diagonalQuadratic a).contDiffAt hφ]
  simp only [fderiv_fderiv_diagonalQuadratic_apply, fderiv_diagonalQuadratic_apply_single,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_smul, zero_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Pi.neg_apply, Module.Basis.lie_exteriorCreation_exteriorContraction_self_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  · rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring

/-- The **Hermite eigenforms** of the Witten Laplacian of `∑ᵢ aᵢ xᵢ² / 2`: for a multi-index
`k : ι → ℕ` and an index set `s`, the form `∏ᵢ ψ_{kᵢ}(√(t |aᵢ|) xᵢ) dx^s`, with `ψₖ` the Hermite
functions. -/
def hermiteEigenform (a : ι → ℝ) (t : ℝ) (k : ι → ℕ) (s : Finset ι) :
    (ι → ℝ) → Finset ι → ℝ :=
  fun x ↦ (∏ i, hermiteFunction (k i) (√(t * |a i|) * x i)) • Pi.single s 1

theorem hermiteEigenform_apply (a : ι → ℝ) (t : ℝ) (k : ι → ℕ) (s : Finset ι) (x : ι → ℝ) :
    hermiteEigenform a t k s x =
      (∏ i, hermiteFunction (k i) (√(t * |a i|) * x i)) • Pi.single s 1 :=
  (rfl)

/-- The eigenvalue `t ∑ᵢ (|aᵢ| (2kᵢ + 1) ± aᵢ)` of the Hermite eigenform `Ψ_{k,s}`, with `+aᵢ`
when `i ∈ s` and `-aᵢ` otherwise. -/
def hermiteEigenvalue (a : ι → ℝ) (t : ℝ) (k : ι → ℕ) (s : Finset ι) : ℝ :=
  t * ∑ i, (|a i| * (2 * k i + 1) + if i ∈ s then a i else -a i)

theorem hermiteEigenvalue_def (a : ι → ℝ) (t : ℝ) (k : ι → ℕ) (s : Finset ι) :
    hermiteEigenvalue a t k s = t * ∑ i, (|a i| * (2 * k i + 1) + if i ∈ s then a i else -a i) :=
  (rfl)

omit [LinearOrder ι] in
/-- The product of dilated Hermite functions underlying a Hermite eigenform. -/
private theorem contDiff_hermiteProduct (c : ι → ℝ) (k : ι → ℕ) :
    ContDiff ℝ 2 (fun x : ι → ℝ ↦ ∏ i, hermiteFunction (k i) (c i * x i)) :=
  contDiff_prod fun i _ ↦ (contDiff_hermiteFunction (k i)).of_le le_top |>.comp
    (contDiff_const.mul (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i))

omit [LinearOrder ι] in
/-- The second derivative of `x ↦ P x • v` is that of `P`, times `v`. -/
private theorem fderiv_fderiv_smul_const_apply {P : (ι → ℝ) → ℝ} (hP : ContDiff ℝ 2 P)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (v : F) (x u w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ fun y ↦ P y • v) x u w = fderiv ℝ (fderiv ℝ P) x u w • v := by
  have hP' : Differentiable ℝ P := hP.differentiable (by norm_num)
  have hfd : fderiv ℝ (fun y ↦ P y • v) =
      fun y ↦ (ContinuousLinearMap.smulRightL ℝ (ι → ℝ) F).flip v (fderiv ℝ P y) :=
    funext fun y ↦ fderiv_smul_const (hP' y) v
  have hd : DifferentiableAt ℝ (fderiv ℝ P) x :=
    (hP.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [hfd, fderiv_fun_comp x ((ContinuousLinearMap.smulRightL ℝ (ι → ℝ) F).flip v).differentiableAt
    hd]
  simp

omit [LinearOrder ι] in
/-- The second partial derivatives of a product of dilated Hermite functions: differentiating
twice in `xᵢ` multiplies it by `cᵢ² ((cᵢ xᵢ)² - (2kᵢ + 1))`. -/
private theorem fderiv_fderiv_hermiteProduct_apply_single_single [DecidableEq ι] (c : ι → ℝ)
    (k : ι → ℕ) (x : ι → ℝ) (i : ι) :
    fderiv ℝ (fderiv ℝ fun x : ι → ℝ ↦ ∏ j, hermiteFunction (k j) (c j * x j)) x
        (Pi.single i 1) (Pi.single i 1) =
      c i ^ 2 * ((c i * x i) ^ 2 - (2 * k i + 1)) *
        ∏ j, hermiteFunction (k j) (c j * x j) := by
  rw [fderiv_fderiv_prod_comp_eval_apply_single_single
      (φ := fun j y ↦ hermiteFunction (k j) (c j * y))
      (fun j ↦ (contDiff_hermiteFunction (k j)).of_le le_top |>.comp
        (contDiff_const.mul contDiff_id)) x i,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j ↦ hermiteFunction (k j) (c j * x j)) (Finset.mem_univ i),
    update_self, deriv_deriv_hermiteFunction_comp_mul, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj ↦ by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **The Hermite eigenforms are eigenforms of the Witten Laplacian.** For `t ≥ 0`, the form
`∏ᵢ ψ_{kᵢ}(√(t |aᵢ|) xᵢ) dx^s` is an eigenform of the Witten Laplacian of `∑ᵢ aᵢ xᵢ² / 2`, with
eigenvalue `t ∑ᵢ (|aᵢ| (2kᵢ + 1) ± aᵢ)`. -/
theorem euclideanWittenLaplacian_hermiteEigenform (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (k : ι → ℕ) (s : Finset ι) :
    euclideanWittenLaplacian (diagonalQuadratic a) t (hermiteEigenform a t k s) =
      hermiteEigenvalue a t k s • hermiteEigenform a t k s := by
  set c : ι → ℝ := fun i ↦ √(t * |a i|) with hc_def
  have hc : ∀ i, c i ^ 2 = t * |a i| := fun i ↦ Real.sq_sqrt (mul_nonneg ht (abs_nonneg _))
  set P : (ι → ℝ) → ℝ := fun x ↦ ∏ i, hermiteFunction (k i) (c i * x i) with hP_def
  have hP : ContDiff ℝ 2 P := contDiff_hermiteProduct c k
  have hΨ : hermiteEigenform a t k s = fun x ↦ P x • Pi.single s 1 := rfl
  have hΨ2 : ContDiff ℝ 2 (hermiteEigenform a t k s) := hΨ ▸ hP.smul contDiff_const
  funext x r
  rw [euclideanWittenLaplacian_diagonalQuadratic_apply hΨ2.contDiffAt, hΨ]
  simp only [fderiv_fderiv_smul_const_apply hP, Pi.smul_apply, smul_eq_mul]
  simp only [hP_def, fderiv_fderiv_hermiteProduct_apply_single_single]
  by_cases hrs : r = s
  · subst hrs
    simp only [Pi.single_eq_same, mul_one, hermiteEigenvalue_def, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have habs : |a i| ^ 2 = a i ^ 2 := sq_abs _
    rw [mul_pow, hc i]
    linear_combination (-(t ^ 2 * x i ^ 2 * ∏ j, hermiteFunction (k j) (c j * x j))) * habs
  · simp [Pi.single_eq_of_ne hrs]

section Eigenvalue

/-! ### The eigenvalues

Each summand `|aᵢ| (2kᵢ + 1) ± aᵢ` of an eigenvalue equals `2kᵢ |aᵢ| + (|aᵢ| ± aᵢ)`, and
`|aᵢ| ± aᵢ` is `0` or `2 |aᵢ|`. -/

omit [Fintype ι] [LinearOrder ι] in
private theorem hermiteSummand_eq (x : ℝ) (n : ℕ) (b : Prop) [Decidable b] :
    (|x| * (2 * n + 1) + if b then x else -x) =
      2 * |x| * n + if (b ↔ x < 0) then 0 else 2 * |x| := by
  rcases lt_or_ge x 0 with hx | hx
  · by_cases hb : b <;> simp [hb, hx, abs_of_neg hx] <;> ring
  · have : ¬x < 0 := not_lt.2 hx
    by_cases hb : b <;> simp [hb, this, abs_of_nonneg hx] <;> ring

omit [Fintype ι] [LinearOrder ι] in
private theorem hermiteSummand_nonneg (x : ℝ) (n : ℕ) (b : Prop) [Decidable b] :
    0 ≤ |x| * (2 * n + 1) + if b then x else -x := by
  rw [hermiteSummand_eq]
  split_ifs <;> positivity

omit [Fintype ι] [LinearOrder ι] in
private theorem hermiteSummand_eq_zero_iff {x : ℝ} (hx : x ≠ 0) (n : ℕ) (b : Prop)
    [Decidable b] : (|x| * (2 * n + 1) + if b then x else -x) = 0 ↔ n = 0 ∧ (b ↔ x < 0) := by
  have hx' : 0 < |x| := abs_pos.2 hx
  rw [hermiteSummand_eq]
  split_ifs with h
  · simp [h, hx'.ne']
  · simp only [h, and_false, iff_false]
    positivity

omit [Fintype ι] [LinearOrder ι] in
private theorem two_mul_abs_le_hermiteSummand {x : ℝ} {n : ℕ} {b : Prop} [Decidable b]
    (h : ¬(n = 0 ∧ (b ↔ x < 0))) : 2 * |x| ≤ |x| * (2 * n + 1) + if b then x else -x := by
  rw [hermiteSummand_eq]
  have h₀ : 0 ≤ 2 * |x| := by positivity
  split_ifs with hc
  · have hn : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 fun hn ↦ h ⟨hn, hc⟩
    nlinarith
  · have : 0 ≤ 2 * |x| * n := by positivity
    linarith

/-- The eigenvalues of the Hermite eigenforms are nonnegative. -/
theorem hermiteEigenvalue_nonneg (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (k : ι → ℕ) (s : Finset ι) :
    0 ≤ hermiteEigenvalue a t k s :=
  mul_nonneg ht (Finset.sum_nonneg fun _ _ ↦ hermiteSummand_nonneg _ _ _)

/-- The ground state `k = 0` in the degree `s = {i | aᵢ < 0}` has eigenvalue zero. -/
@[simp]
theorem hermiteEigenvalue_zero_filter_neg (a : ι → ℝ) (t : ℝ) :
    hermiteEigenvalue a t 0 (Finset.univ.filter fun i ↦ a i < 0) = 0 := by
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ ↦ ?_)
  rcases lt_or_ge (a i) 0 with h | h
  · simp [h, abs_of_neg h]
  · simp [not_lt.2 h, abs_of_nonneg h]

/-- **The kernel of the harmonic-oscillator model.** If every `aᵢ` is nonzero and `t > 0`, the
eigenvalue of `Ψ_{k,s}` vanishes exactly for the Gaussian ground state `k = 0` in the degree
`s = {i | aᵢ < 0}`, whose cardinality is the Morse index. -/
theorem hermiteEigenvalue_eq_zero_iff {a : ι → ℝ} (ha : ∀ i, a i ≠ 0) {t : ℝ} (ht : 0 < t)
    (k : ι → ℕ) (s : Finset ι) :
    hermiteEigenvalue a t k s = 0 ↔ k = 0 ∧ s = Finset.univ.filter fun i ↦ a i < 0 := by
  rw [hermiteEigenvalue_def, mul_eq_zero, or_iff_right ht.ne',
    Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hermiteSummand_nonneg _ _ _]
  simp only [Finset.mem_univ, true_implies, hermiteSummand_eq_zero_iff (ha _), forall_and,
    funext_iff, Pi.zero_apply, Finset.ext_iff, Finset.mem_filter, true_and]

/-- **The spectral gap of the harmonic-oscillator model.** If `c ≤ |aᵢ|` for every `i`, every
Hermite eigenform other than the ground state has eigenvalue at least `2 t c`. -/
theorem two_mul_mul_le_hermiteEigenvalue {a : ι → ℝ} {t : ℝ} (ht : 0 ≤ t) {c : ℝ}
    (hc : ∀ i, c ≤ |a i|) {k : ι → ℕ} {s : Finset ι}
    (hks : ¬(k = 0 ∧ s = Finset.univ.filter fun i ↦ a i < 0)) :
    2 * t * c ≤ hermiteEigenvalue a t k s := by
  have : ∃ i, ¬(k i = 0 ∧ (i ∈ s ↔ a i < 0)) := by
    by_contra! h
    refine hks ⟨funext fun i ↦ (h i).1, Finset.ext fun i ↦ ?_⟩
    simpa using (h i).2
  obtain ⟨i, hi⟩ := this
  rw [hermiteEigenvalue_def]
  calc 2 * t * c ≤ t * (2 * |a i|) := by nlinarith [hc i]
    _ ≤ t * (|a i| * (2 * k i + 1) + if i ∈ s then a i else -a i) :=
        mul_le_mul_of_nonneg_left (two_mul_abs_le_hermiteSummand hi) ht
    _ ≤ t * ∑ j, (|a j| * (2 * k j + 1) + if j ∈ s then a j else -a j) :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ ↦ hermiteSummand_nonneg _ _ _)
          (Finset.mem_univ i)) ht

/-- **The ground state is a Gaussian**: for `t ≥ 0`, the Hermite eigenform with `k = 0` is
`π^{-n/4} e^{-t ∑ᵢ |aᵢ| xᵢ² / 2} dx^s`, with `n` the dimension. -/
theorem hermiteEigenform_zero_apply (a : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (s : Finset ι)
    (x : ι → ℝ) :
    hermiteEigenform a t 0 s x =
      (Real.exp (-(t * ∑ i, |a i| * x i ^ 2) / 2) / √(√Real.pi) ^ Fintype.card ι) •
        Pi.single s 1 := by
  rw [hermiteEigenform_apply]
  congr 1
  simp only [Pi.zero_apply, hermiteFunction_def, Polynomial.hermite_zero, map_one, one_mul,
    Nat.factorial_zero, Nat.cast_one, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, ← Real.exp_sum, mul_pow, Real.sq_sqrt (mul_nonneg ht (abs_nonneg _))]
  congr 2
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end Eigenvalue

end Model

end TauCeti
