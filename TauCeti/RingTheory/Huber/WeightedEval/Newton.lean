/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.PDeriv
public import TauCeti.RingTheory.AdicCompletion.Newton
public import TauCeti.RingTheory.Huber.Basic
public import TauCeti.RingTheory.Huber.WeightedEval.Map
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PDeriv
public import TauCeti.RingTheory.MvPowerSeries.Derivative

/-!
# Newton's method for restricted power series with integral coefficients

Let `C` be a complete topological ring with a pair of definition whose ring of definition `A₀`
contains an element `ϖ` that is a unit of `C`, such as a pseudouniformiser. Let `F` be a
restricted power series in `N` variables with coefficients in `A₀`, evaluated at points of `A₀^N`
by `TauCeti.Huber.weightedEval`. This file proves the multivariable Newton–Hensel lemma for such
series, with a Jacobian matrix that is only invertible up to a power of `ϖ`.

The values of `F` at points of `A₀^N` lie in `A₀`, because `A₀` is open, hence closed, and
contains every term of the evaluation. More precisely, Taylor's estimate holds termwise: if
`x ≡ t mod ϖᵃ` and `x' ≡ x mod ϖᵇ` with `a ≤ b`, then
`F(x') - F(x) - ∑ⱼ ∂ⱼF(t) (x'ⱼ - xⱼ)` lies in `ϖ^(a + b) A₀`. Each term of this sum is a
coefficient of `F` times the corresponding estimate for a monomial
(`MvPolynomial.mul_dvd_eval_sub_eval_sub_sum_pderiv`), and `ϖ^(a + b) A₀` is closed. Partial
derivatives are the formal ones, `MvPowerSeries.pderiv`; no division by integers occurs, so the
results hold in every characteristic.

With `a = k + 1` this is the linearisation hypothesis of the quantitative Newton method
`TauCeti.IsAdicComplete.existsUnique_eq_zero_of_mul_eq_pow_smul`, applied to `A₀`, which is
`ϖ`-adically complete when `ϖ` is a pseudouniformiser and `C` is Hausdorff. Writing `J(t)` for
the Jacobian matrix `(∂ⱼFᵢ(t))`, if `M J(t) = ϖᵏ` for an integral matrix `M` and
`F(t) ∈ ϖ^(2k + 1) A₀^N`, then `F` has exactly one zero in `t + ϖ^(k + 1) A₀^N`, and
`F(t) ∈ ϖᵉ A₀^N` puts that zero in `t + ϖ^(e - k) A₀^N`.

## Main results

* `TauCeti.Huber.weightedEval_mem_ringOfDefinition`: a restricted series with coefficients in
  `A₀` takes values in `A₀` on `A₀^N`.
* `TauCeti.Huber.weightedEval_sub_weightedEval_sub_sum_mem_pow_smul`: Taylor's estimate
  `F(x') - F(x) - ∑ⱼ ∂ⱼF(t) (x'ⱼ - xⱼ) ∈ ϖ^(a + b) A₀`.
* `TauCeti.Huber.existsUnique_weightedEval_eq_zero`: Newton's method, the existence and
  uniqueness of a zero in `t + ϖ^(k + 1) A₀^N`.
* `TauCeti.Huber.pow_dvd_sub_of_weightedEval_eq_zero`: the error bound `u ≡ t mod ϖ^(e - k)`.

## References

* [R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*], proof of
  Proposition 1.7.1, point (1).
* [O. Gabber and L. Ramero, *Almost ring theory*], Lemma 5.4.8.
-/

public section

open Matrix Pointwise

namespace TauCeti.Huber

variable {C : Type*} [CommRing C]

variable [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [CompleteSpace C]
  (P : PairOfDefinition C) {N : ℕ}

/-- **A restricted series with integral coefficients takes integral values** at integral points:
if the coefficients of `F` lie in the ring of definition `A₀`, then so does `F(x)` for every
`x ∈ A₀^N`. -/
theorem weightedEval_mem_ringOfDefinition {F : MvPowerSeries (Fin N) C}
    (hF : IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) F)
    (hF₀ : ∀ ν, MvPowerSeries.coeff ν F ∈ P.ringOfDefinition) (x : Fin N → P.ringOfDefinition) :
    weightedEval (RingHom.id C) (fun i ↦ (x i : C)) F ∈ P.ringOfDefinition := by
  have := P.toNonarchimedeanRing
  simpa using P.mem_smul_of_hasSum isUnit_one
    (hasSum_weightedEval_of_forall_isPowerBounded continuous_id.continuousAt
      (fun i ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (x i).2) hF)
    fun ν ↦ by
      simpa using mul_mem (hF₀ ν) (prod_mem fun i _ ↦ pow_mem (x i).2 (ν i))

/-- **Taylor's estimate for restricted series with integral coefficients.** Let `ϖ ∈ A₀` be a
unit of `C`. If `x ≡ t mod ϖᵃ` and `x' ≡ x mod ϖᵇ` in `A₀^N` with `a ≤ b`, then the gradient of
`F` at `t` linearises `F` from `x` to `x'` up to an error in `ϖ^(a + b) A₀`. -/
theorem weightedEval_sub_weightedEval_sub_sum_mem_pow_smul {ϖ : P.ringOfDefinition}
    (hϖ : IsUnit (ϖ : C)) {F : MvPowerSeries (Fin N) C}
    (hF : IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) F)
    (hF₀ : ∀ ν, MvPowerSeries.coeff ν F ∈ P.ringOfDefinition)
    {t x x' : Fin N → P.ringOfDefinition} {a b : ℕ} (hab : a ≤ b)
    (hx : ∀ i, ϖ ^ a ∣ x i - t i) (hxx' : ∀ i, ϖ ^ b ∣ x' i - x i) :
    weightedEval (RingHom.id C) (fun i ↦ (x' i : C)) F -
        weightedEval (RingHom.id C) (fun i ↦ (x i : C)) F -
        ∑ j, weightedEval (RingHom.id C) (fun i ↦ (t i : C)) (MvPowerSeries.pderiv j F) *
          ((x' j : C) - x j) ∈
      (ϖ : C) ^ (a + b) • (P.ringOfDefinition : Set C) := by
  classical
  have := P.toNonarchimedeanRing
  have hsum (y : Fin N → P.ringOfDefinition) {G : MvPowerSeries (Fin N) C}
      (hG : IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) G) :=
    hasSum_weightedEval_of_forall_isPowerBounded (φ := RingHom.id C) continuous_id.continuousAt
      (fun i ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (y i).2) hG
  -- Reindex the evaluation of `∂ⱼF` at `t` by the monomials of `F`: the `(ν + eⱼ)`-th
  -- coefficient of `F` times the value at `t` of `∂ⱼ` of the monomial `X^(ν + eⱼ)`. The
  -- monomials with exponent `0` at `j` contribute zero.
  have hgrad (j : Fin N) : HasSum (fun μ ↦ MvPowerSeries.coeff μ F *
      ((MvPolynomial.eval t (MvPolynomial.pderiv j
        (MvPolynomial.monomial μ (1 : P.ringOfDefinition))) : P.ringOfDefinition) : C))
      (weightedEval (RingHom.id C) (fun i ↦ (t i : C)) (MvPowerSeries.pderiv j F)) := by
    refine ((add_left_injective (Finsupp.single j 1)).hasSum_iff fun μ hμ ↦ ?_).mp ?_
    · have hμj : μ j = 0 := by
        by_contra h
        exact hμ ⟨μ - Finsupp.single j 1, tsub_add_cancel_of_le
          (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))⟩
      simp [hμj]
    · convert hsum t (hF.pderiv_one_weight j) using 1
      funext ν
      simp [MvPolynomial.eval_monomial, Finsupp.prod_pow, MvPowerSeries.coeff_pderiv]
      ring
  have hD := ((hsum x' hF).sub (hsum x hF)).sub
    (hasSum_sum (s := Finset.univ) fun j _ ↦ (hgrad j).mul_right ((x' j : C) - x j))
  refine P.mem_smul_of_hasSum (hϖ.pow _) hD fun μ ↦ ?_
  -- Each term is the `μ`-th coefficient of `F` times Taylor's error for the monomial `Xᵘ`.
  obtain ⟨q, hq⟩ := MvPolynomial.mul_dvd_eval_sub_eval_sub_sum_pderiv
    (MvPolynomial.monomial μ (1 : P.ringOfDefinition)) hx (pow_dvd_pow ϖ hab) hxx'
  refine ⟨MvPowerSeries.coeff μ F * q, mul_mem (hF₀ μ) q.2, ?_⟩
  have hq' := congrArg ((↑) : P.ringOfDefinition → C) hq
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, one_mul] at hq'
  push_cast at hq'
  simp only [weightedEvalTerm_def, RingHom.id_apply, smul_eq_mul]
  rw [pow_add, mul_left_comm, ← hq', mul_sub, mul_sub, Finset.mul_sum]
  simp only [mul_assoc]

section Newton

variable {ϖ : P.ringOfDefinition} {F : Fin N → MvPowerSeries (Fin N) C}

/-- The evaluation of `F` on `A₀^N`, as a map `A₀^N → A₀^N`. -/
private noncomputable def evalOD
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (x : Fin N → P.ringOfDefinition) (i : Fin N) : P.ringOfDefinition :=
  ⟨weightedEval (RingHom.id C) (fun l ↦ (x l : C)) (F i),
    weightedEval_mem_ringOfDefinition P (hF i) (hF₀ i) x⟩

/-- The Jacobian matrix of `F` at `t`, as a matrix over `A₀`. -/
private noncomputable def jacobianOD
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) : Matrix (Fin N) (Fin N) P.ringOfDefinition :=
  Matrix.of fun i j ↦ ⟨weightedEval (RingHom.id C) (fun l ↦ (t l : C))
    (MvPowerSeries.pderiv j (F i)),
    weightedEval_mem_ringOfDefinition P ((hF i).pderiv_one_weight j)
      (MvPowerSeries.coeff_pderiv_mem (hF₀ i) j) t⟩

/-- Taylor's estimate on `A₀^N`, in the form of the linearisation hypothesis of the quantitative
Newton method. -/
private theorem pow_dvd_evalOD_sub
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (hϖ : IsUnit (ϖ : C)) {t : Fin N → P.ringOfDefinition} {k : ℕ}
    (x x' : Fin N → P.ringOfDefinition) (hx : ∀ i, ϖ ^ (k + 1) ∣ x i - t i) (n : ℕ)
    (hn : k + 1 ≤ n) (hxx' : ∀ i, ϖ ^ n ∣ x' i - x i) (i : Fin N) :
    ϖ ^ (n + k + 1) ∣ evalOD P hF hF₀ x' i - evalOD P hF hF₀ x i -
      (jacobianOD P hF hF₀ t *ᵥ (x' - x)) i := by
  refine P.coe_mem_smul_iff_dvd.mp ?_
  rw [show n + k + 1 = k + 1 + n by omega]
  convert weightedEval_sub_weightedEval_sub_sum_mem_pow_smul P hϖ (hF i) (hF₀ i) hn hx hxx'
    using 1
  simp [evalOD, jacobianOD, Matrix.mulVec, dotProduct]

/-- The scaled inverse of the Jacobian matrix over `C` is one over `A₀`. -/
private theorem mul_jacobianOD_eq
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    {t : Fin N → P.ringOfDefinition} {k : ℕ} {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hM : M.map ((↑) : P.ringOfDefinition → C) * Matrix.of (fun i j ↦
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (MvPowerSeries.pderiv j (F i))) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C)) :
    M * jacobianOD P hF hF₀ t = ϖ ^ k • (1 : Matrix (Fin N) (Fin N) P.ringOfDefinition) := by
  ext i j
  have h := congrFun (congrFun hM i) j
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at h
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  push_cast
  convert h using 2
  · simp [jacobianOD]
  · split_ifs <;> simp

/-- **Error bound in Newton's method for restricted series.** Let `ϖ ∈ A₀` be a unit of `C`, and
let `M` be an integral matrix with `M J(t) = ϖᵏ`, where `J(t) = (∂ⱼFᵢ(t))` is the Jacobian matrix
of `F` at `t ∈ A₀^N`. If `F(t) ∈ ϖᵉ A₀^N`, then every zero `u ∈ A₀^N` of `F` with
`u ≡ t mod ϖ^(k + 1)` satisfies `u ≡ t mod ϖ^(e - k)`. -/
theorem pow_dvd_sub_of_weightedEval_eq_zero (hϖ : IsUnit (ϖ : C))
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    {t : Fin N → P.ringOfDefinition} {k : ℕ} {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hM : M.map ((↑) : P.ringOfDefinition → C) * Matrix.of (fun i j ↦
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (MvPowerSeries.pderiv j (F i))) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    {e : ℕ} (ht : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (F i) ∈
      (ϖ : C) ^ e • (P.ringOfDefinition : Set C))
    {u : Fin N → P.ringOfDefinition} (hu : ∀ i, ϖ ^ (k + 1) ∣ u i - t i)
    (hFu : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C)) (F i) = 0) (i : Fin N) :
    ϖ ^ (e - k) ∣ u i - t i :=
  pow_dvd_sub_of_eq_zero_of_mul_eq_pow_smul
    (fun _ _ h ↦ Subtype.ext (hϖ.mul_left_cancel (congrArg Subtype.val h)))
    (evalOD P hF hF₀) (mul_jacobianOD_eq P hF hF₀ hM) t
    (fun x x' hx _ n hn hxx' ↦ pow_dvd_evalOD_sub P hF hF₀ hϖ x x' hx n hn hxx')
    (fun i ↦ P.coe_mem_smul_iff_dvd.mp (ht i)) hu (funext fun i ↦ Subtype.ext (hFu i : _)) i

/-- **Newton's method for restricted series with integral coefficients.** Let `C` be Hausdorff,
let `ϖ ∈ A₀` be a pseudouniformiser, and let `M` be an integral matrix with `M J(t) = ϖᵏ`, where
`J(t) = (∂ⱼFᵢ(t))` is the Jacobian matrix of `F` at `t ∈ A₀^N`. If `F(t) ∈ ϖ^(2k + 1) A₀^N`, then
`F` has exactly one zero `u ∈ A₀^N` with `u ≡ t mod ϖ^(k + 1)`. -/
theorem existsUnique_weightedEval_eq_zero [T0Space C] (hϖ : IsPseudoUniformizer (ϖ : C))
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) {k : ℕ} {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hM : M.map ((↑) : P.ringOfDefinition → C) * Matrix.of (fun i j ↦
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (MvPowerSeries.pderiv j (F i))) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    (ht : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (F i) ∈
      (ϖ : C) ^ (2 * k + 1) • (P.ringOfDefinition : Set C)) :
    ∃! u : Fin N → P.ringOfDefinition, (∀ i, ϖ ^ (k + 1) ∣ u i - t i) ∧
      ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C)) (F i) = 0 := by
  have := P.isAdicComplete_span_singleton ϖ hϖ
  have hzero (u : Fin N → P.ringOfDefinition) : evalOD P hF hF₀ u = 0 ↔
      ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C)) (F i) = 0 := by
    simp [funext_iff, evalOD, Subtype.ext_iff]
  simpa only [hzero] using IsAdicComplete.existsUnique_eq_zero_of_mul_eq_pow_smul
    (fun _ _ h ↦ Subtype.ext (hϖ.isUnit.mul_left_cancel (congrArg Subtype.val h)))
    (evalOD P hF hF₀) (mul_jacobianOD_eq P hF hF₀ hM) t
    (fun i ↦ P.coe_mem_smul_iff_dvd.mp (ht i))
    fun x x' hx _ n hn hxx' ↦ pow_dvd_evalOD_sub P hF hF₀ hϖ.isUnit x x' hx n hn hxx'

end Newton

end TauCeti.Huber
