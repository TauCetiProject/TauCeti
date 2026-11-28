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
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.RingTheory.Subsemiring.SpanSingleton

/-!
# Newton's method for restricted power series with integral coefficients

Let `C` be a complete topological ring with a pair of definition whose ring of definition `A₀`
contains an element `ϖ` that is a unit of `C`, such as a pseudouniformiser. Let `F` be a
restricted power series in `N` variables with coefficients in `A₀`, evaluated at points of `A₀^N`
by `TauCeti.Huber.weightedEval`. This file proves the multivariable Newton–Hensel lemma for such
series, with a Jacobian matrix that is only invertible up to a power of `ϖ`.

The values of `F` at points of `A₀^N` lie in `A₀`
(`TauCeti.Huber.weightedEval_mem`). More precisely, Taylor's estimate holds
termwise: if
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

* `TauCeti.Huber.weightedEval_sub_weightedEval_sub_sum_mem_pow_smul`: Taylor's estimate
  `F(x') - F(x) - ∑ⱼ ∂ⱼF(t) (x'ⱼ - xⱼ) ∈ ϖ^(a + b) A₀`.
* `TauCeti.Huber.weightedEval_sub_mem_pow_smul`: first-order congruence
  `g(u) - g(t) ∈ ϖ^m A₀` for `u ≡ t mod ϖ^m`.
* `TauCeti.Huber.weightedEval_mem_pow_smul_of_coeff`: `g(t) ∈ ϖ^m A₀` when all coefficients of `g`
  lie in `ϖ^m A₀`.
* `TauCeti.Huber.existsUnique_weightedEval_eq_zero`: Newton's method, the existence and
  uniqueness of a zero in `t + ϖ^(k + 1) A₀^N`.
* `TauCeti.Huber.pow_dvd_sub_of_weightedEval_eq_zero`: the error bound `u ≡ t mod ϖ^(e - k)`.
* `TauCeti.Huber.exists_mul_jacobianMatrix_eq_pow_smul_one_of_dvd` and
  `TauCeti.Huber.exists_mul_jacobianMatrix_eq_pow_smul_one_of_coeff_mem`: stability of a
  `ϖᵏ`-scaled Jacobian inverse under `ϖ^(k + 1)`-perturbations of the point or coefficients.
* `TauCeti.Huber.eq_of_weightedEval_eq_zero`: local uniqueness of zeros in `t + ϖ^(k + 1) A₀^N`
  without a residual hypothesis on `F(t)`.

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
      (fun i ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (y i).property) hG
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
  refine ⟨MvPowerSeries.coeff μ F * q, mul_mem (hF₀ μ) q.property, ?_⟩
  have hq' := congrArg ((↑) : P.ringOfDefinition → C) hq
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow, one_mul] at hq'
  push_cast at hq'
  simp only [weightedEvalTerm_def, RingHom.id_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  linear_combination -(MvPowerSeries.coeff μ F * hq')

/-- **First-order congruence for restricted power series with integral coefficients:** if `g` is
unit-weight restricted with coefficients in `A₀` and `u ≡ t mod ϖ ^ m` coordinatewise in `A₀`,
then `g(u) - g(t) ∈ ϖ ^ m • A₀`. -/
theorem weightedEval_sub_mem_pow_smul {ϖ : P.ringOfDefinition} (hϖ : IsUnit (ϖ : C))
    {g : MvPowerSeries (Fin N) C}
    (hg : IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) g)
    (hg₀ : ∀ ν, MvPowerSeries.coeff ν g ∈ P.ringOfDefinition)
    {t u : Fin N → P.ringOfDefinition} {m : ℕ} (hu : ∀ l, ϖ ^ m ∣ u l - t l) :
    weightedEval (RingHom.id C) (fun l ↦ (u l : C)) g -
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) g ∈
        (ϖ : C) ^ m • (P.ringOfDefinition : Set C) := by
  have htaylor := weightedEval_sub_weightedEval_sub_sum_mem_pow_smul P hϖ hg hg₀
    (t := t) (x := t) (x' := u) (a := 0) (b := m) (Nat.zero_le _) (fun _ ↦ by simp) hu
  rw [zero_add] at htaylor
  let gu : P.ringOfDefinition :=
    ⟨_, weightedEval_mem P.isClosed_ringOfDefinition (φ := RingHom.id C) hg₀ fun i ↦ (u i).property⟩
  let gt : P.ringOfDefinition :=
    ⟨_, weightedEval_mem P.isClosed_ringOfDefinition (φ := RingHom.id C) hg₀ fun i ↦ (t i).property⟩
  let lin : P.ringOfDefinition := ∑ l, ⟨_, weightedEval_mem P.isClosed_ringOfDefinition
    (φ := RingHom.id C) (MvPowerSeries.coeff_pderiv_mem hg₀ l) fun i ↦ (t i).property⟩ * (u l - t l)
  have hcoe : ((gu - gt - lin : P.ringOfDefinition) : C) =
      weightedEval (RingHom.id C) (fun l ↦ (u l : C)) g -
        weightedEval (RingHom.id C) (fun l ↦ (t l : C)) g -
        ∑ l, weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (MvPowerSeries.pderiv l g) *
          ((u l : C) - t l) := by
    simp only [gu, gt, lin]
    push_cast
    simp
  have hrem : ϖ ^ m ∣ (gu - gt) - lin :=
    (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp (hcoe ▸ htaylor)
  have hlin : ϖ ^ m ∣ lin := Finset.dvd_sum fun l _ ↦ dvd_mul_of_dvd_right (hu l) _
  exact (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mpr
    (sub_add_cancel (gu - gt) lin ▸ dvd_add hrem hlin)

/-- **Coefficientwise divisibility passes to evaluation:** if `g` is unit-weight restricted and
every coefficient of `g` lies in `ϖ ^ m • A₀`, then `g(t) ∈ ϖ ^ m • A₀` for every
`t : Fin N → A₀`. -/
theorem weightedEval_mem_pow_smul_of_coeff {ϖ : P.ringOfDefinition} (hϖ : IsUnit (ϖ : C))
    {g : MvPowerSeries (Fin N) C}
    (hg : IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) g)
    {m : ℕ} (hg₀ : ∀ ν, MvPowerSeries.coeff ν g ∈ (ϖ : C) ^ m • (P.ringOfDefinition : Set C))
    (t : Fin N → P.ringOfDefinition) :
    weightedEval (RingHom.id C) (fun l ↦ (t l : C)) g ∈
      (ϖ : C) ^ m • (P.ringOfDefinition : Set C) := by
  have := P.toNonarchimedeanRing
  have hsum := hasSum_weightedEval_of_forall_isPowerBounded (φ := RingHom.id C)
    continuous_id.continuousAt
    (fun i ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (t i).property) hg
  refine P.mem_smul_of_hasSum (hϖ.pow m) hsum fun ν ↦ ?_
  obtain ⟨r, hr, hcoeff⟩ := Set.mem_smul_set.mp (hg₀ ν)
  refine ⟨r * ∏ i, (t i : C) ^ ν i,
    mul_mem hr (prod_mem fun i _ ↦ pow_mem (t i).property _), ?_⟩
  dsimp only at hcoeff ⊢
  rw [weightedEvalTerm_def, RingHom.id_apply, ← hcoeff, smul_eq_mul, smul_eq_mul, mul_assoc]

section Newton

variable {ϖ : P.ringOfDefinition} {F : Fin N → MvPowerSeries (Fin N) C}

/-- The evaluation of `F` on `A₀^N`, as a map `A₀^N → A₀^N`. -/
private noncomputable def evalOD
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (x : Fin N → P.ringOfDefinition) (i : Fin N) : P.ringOfDefinition :=
  ⟨weightedEval (RingHom.id C) (fun l ↦ (x l : C)) (F i),
    weightedEval_mem P.isClosed_ringOfDefinition (hF₀ i) fun l ↦ (x l).property⟩

omit [IsUniformAddGroup C] [CompleteSpace C] in
/-- `F` vanishes at `u ∈ A₀^N` exactly when its evaluation on `A₀^N` does. -/
private theorem evalOD_eq_zero_iff
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (u : Fin N → P.ringOfDefinition) : evalOD P hF₀ u = 0 ↔
      ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C)) (F i) = 0 := by
  simp [funext_iff, evalOD, Subtype.ext_iff]

/-- The Jacobian matrix of `F` at `t`, as a matrix over `A₀`. -/
private noncomputable def jacobianOD
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) : Matrix (Fin N) (Fin N) P.ringOfDefinition :=
  Matrix.of fun i j ↦ ⟨weightedEval (RingHom.id C) (fun l ↦ (t l : C))
    (MvPowerSeries.pderiv j (F i)),
    weightedEval_mem P.isClosed_ringOfDefinition (MvPowerSeries.coeff_pderiv_mem (hF₀ i) j)
      fun l ↦ (t l).property⟩

omit [IsUniformAddGroup C] [CompleteSpace C] in
/-- Each entry of `jacobianOD` coerces to the evaluated partial derivative `∂ⱼFᵢ(t)` in `C`. -/
@[simp]
private theorem jacobianOD_apply
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) (i j : Fin N) :
    (jacobianOD P hF₀ t i j : C) =
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (MvPowerSeries.pderiv j (F i)) :=
  (rfl)

/-- Taylor's estimate on `A₀^N`, in the form of the linearisation hypothesis of the quantitative
Newton method. -/
private theorem pow_dvd_evalOD_sub
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    (hϖ : IsUnit (ϖ : C)) {t : Fin N → P.ringOfDefinition} {k : ℕ}
    (x x' : Fin N → P.ringOfDefinition) (hx : ∀ i, ϖ ^ (k + 1) ∣ x i - t i) (n : ℕ)
    (hn : k + 1 ≤ n) (hxx' : ∀ i, ϖ ^ n ∣ x' i - x i) (i : Fin N) :
    ϖ ^ (n + k + 1) ∣ evalOD P hF₀ x' i - evalOD P hF₀ x i -
      (jacobianOD P hF₀ t *ᵥ (x' - x)) i := by
  refine (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp ?_
  convert weightedEval_sub_weightedEval_sub_sum_mem_pow_smul P hϖ (hF i) (hF₀ i) hn hx hxx'
    using 1
  · congr 1
    push_cast
    ring
  · simp [evalOD, jacobianOD, Matrix.mulVec, dotProduct]

omit [IsUniformAddGroup C] [CompleteSpace C] in
/-- The scaled inverse of the Jacobian matrix over `C` is one over `A₀`. -/
private theorem mul_jacobianOD_eq
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    {t : Fin N → P.ringOfDefinition} {k : ℕ} {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hM : M.map ((↑) : P.ringOfDefinition → C) * Matrix.of (fun i j ↦
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (MvPowerSeries.pderiv j (F i))) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C)) :
    M * jacobianOD P hF₀ t = ϖ ^ k • (1 : Matrix (Fin N) (Fin N) P.ringOfDefinition) := by
  apply Matrix.map_injective Subtype.coe_injective
  have h : P.ringOfDefinition.subtype.mapMatrix (M * jacobianOD P hF₀ t) =
      P.ringOfDefinition.subtype.mapMatrix (ϖ ^ k • 1) := by
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow,
      Subring.coe_subtype]
    exact hM
  simpa only [RingHom.mapMatrix_apply, Subring.coe_subtype] using h

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
    (evalOD P hF₀) (mul_jacobianOD_eq P hF₀ hM) t
    (fun x x' hx _ n hn hxx' ↦ pow_dvd_evalOD_sub P hF hF₀ hϖ x x' hx n hn hxx')
    (fun i ↦ (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp (ht i)) hu
    ((evalOD_eq_zero_iff P hF₀ u).mpr hFu) i

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
  simpa only [evalOD_eq_zero_iff] using IsAdicComplete.existsUnique_eq_zero_of_mul_eq_pow_smul
    (fun _ _ h ↦ Subtype.ext (hϖ.isUnit.mul_left_cancel (congrArg Subtype.val h)))
    (evalOD P hF₀) (mul_jacobianOD_eq P hF₀ hM) t
    (fun i ↦ (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp (ht i))
    fun x x' hx _ n hn hxx' ↦ pow_dvd_evalOD_sub P hF hF₀ hϖ.isUnit x x' hx n hn hxx'

/-- **Matrix perturbation for `ϖ ^ k`-scaled inverses over `A₀`:** if `M * J₁ = ϖ ^ k • 1`
and `J₂ ≡ J₁ mod ϖ ^ (k + 1)` entrywise over `A₀`, then there is `M' ≡ M mod ϖ` satisfying
`M' * J₂ = ϖ ^ k • 1` and `J₂ * M' = ϖ ^ k • 1` over `C`. -/
private theorem exists_mul_eq_pow_smul_one_of_matrix_dvd [T0Space C]
    (hϖ : IsPseudoUniformizer (ϖ : C)) {k : ℕ}
    {M J₁ J₂ : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hJ₁ : M * J₁ = ϖ ^ k • 1)
    (hJdiff : ∀ i j, ϖ ^ (k + 1) ∣ J₂ i j - J₁ i j) :
    ∃ M' : Matrix (Fin N) (Fin N) P.ringOfDefinition,
      (∀ i j, ϖ ∣ M' i j - M i j) ∧
      M'.map ((↑) : P.ringOfDefinition → C) * J₂.map ((↑) : P.ringOfDefinition → C) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) ∧
      J₂.map ((↑) : P.ringOfDefinition → C) * M'.map ((↑) : P.ringOfDefinition → C) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) := by
  have := P.isAdicComplete_span_singleton ϖ hϖ
  -- Stage 1: Perturbation `J₂ = J₁ + ϖ ^ (k + 1) • Δ`, so `M * J₂ = ϖ ^ k • U`.
  choose Δ hΔ using hJdiff
  have hJ₂_eq : J₂ = J₁ + ϖ ^ (k + 1) • Matrix.of Δ := by
    apply Matrix.ext; intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination hΔ i j
  let U : Matrix (Fin N) (Fin N) P.ringOfDefinition := 1 + ϖ • (M * Matrix.of Δ)
  have hMJ₂ : M * J₂ = ϖ ^ k • U := by
    dsimp only [U]
    rw [hJ₂_eq, Matrix.mul_add, hJ₁, Matrix.mul_smul, pow_succ, mul_comm (ϖ ^ k) ϖ,
      ← smul_smul, smul_add]; simp [smul_smul, mul_comm]
  -- Stage 2: Invertibility of `U` over the `ϖ`-adically complete ring `A₀`.
  have hUdet : IsUnit U.det :=
    Matrix.isUnit_det_one_add_smul
      (IsAdicComplete.le_jacobson (Ideal.span ({ϖ} : Set P.ringOfDefinition))
        (Ideal.mem_span_singleton_self ϖ)) _
  -- Stage 3: Corrected left inverse `M' := U⁻¹ * M` and congruence `M' ≡ M mod ϖ`.
  let M' : Matrix (Fin N) (Fin N) P.ringOfDefinition := U⁻¹ * M
  have hUM' : U * M' = M := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUdet, Matrix.one_mul]
  have hM'mod (i j) : ϖ ∣ M' i j - M i j := ⟨-((M * Matrix.of Δ * M') i j), by
    have hij := congrFun (congrFun hUM' i) j
    simp only [U, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hij
    linear_combination hij⟩
  have hM'J₂ : M' * J₂ = ϖ ^ k • (1 : Matrix (Fin N) (Fin N) P.ringOfDefinition) := by
    rw [Matrix.mul_assoc, hMJ₂, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hUdet]
  have hleft : M'.map ((↑) : P.ringOfDefinition → C) * J₂.map ((↑) : P.ringOfDefinition → C) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) := by
    have h := congrArg P.ringOfDefinition.subtype.mapMatrix hM'J₂
    rw [map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow,
      Subring.coe_subtype] at h
    exact h
  -- Stage 4: Two-sidedness of the `ϖ ^ k`-scaled inverse.
  exact ⟨M', hM'mod, hleft,
    (Matrix.mul_eq_smul_one_comm
      (isRegular_iff_mem_nonZeroDivisors.mp (hϖ.isUnit.pow k).isRegular)).mp hleft⟩

/-- **Stability of the `ϖ ^ k`-scaled Jacobian inverse under `ϖ ^ (k + 1)`-perturbations:** if
`M * J(t) = ϖ ^ k • 1` and `u ≡ t mod ϖ ^ (k + 1)` in `A₀^N`, then there is an integral matrix
`M' ≡ M mod ϖ` satisfying both `M' * J(u) = ϖ ^ k • 1` and `J(u) * M' = ϖ ^ k • 1`. -/
theorem exists_mul_jacobianMatrix_eq_pow_smul_one_of_dvd [T0Space C]
    (hϖ : IsPseudoUniformizer (ϖ : C))
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    {t u : Fin N → P.ringOfDefinition} {k : ℕ}
    {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hJ : M.map ((↑) : P.ringOfDefinition → C) *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    (hu : ∀ l, ϖ ^ (k + 1) ∣ u l - t l) :
    ∃ M' : Matrix (Fin N) (Fin N) P.ringOfDefinition,
      (∀ i j, ϖ ∣ M' i j - M i j) ∧
      M'.map ((↑) : P.ringOfDefinition → C) *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (u l : C))
          (MvPowerSeries.pderiv j (F i))) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) ∧
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (u l : C))
          (MvPowerSeries.pderiv j (F i))) *
        M'.map ((↑) : P.ringOfDefinition → C) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) :=
  exists_mul_eq_pow_smul_one_of_matrix_dvd P hϖ (J₂ := jacobianOD P hF₀ u)
    (mul_jacobianOD_eq P hF₀ hJ) fun i j ↦
      (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp <| by
        simpa only [AddSubgroupClass.coe_sub, jacobianOD_apply, Subring.coe_pow] using
          weightedEval_sub_mem_pow_smul P hϖ.isUnit ((hF i).pderiv_one_weight j)
            (MvPowerSeries.coeff_pderiv_mem (hF₀ i) j) hu

/-- **Stability of the `ϖ ^ k`-scaled Jacobian inverse under `ϖ ^ (k + 1)`-perturbations of the
defining series:** if `M * J_F(t) = ϖ ^ k • 1` and `Gᵢ - Fᵢ` has all coefficients in
`ϖ ^ (k + 1) • A₀`, then there is an integral matrix `M' ≡ M mod ϖ` satisfying both
`M' * J_G(t) = ϖ ^ k • 1` and `J_G(t) * M' = ϖ ^ k • 1`. -/
theorem exists_mul_jacobianMatrix_eq_pow_smul_one_of_coeff_mem [T0Space C]
    (hϖ : IsPseudoUniformizer (ϖ : C))
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    {G : Fin N → MvPowerSeries (Fin N) C}
    (hG : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (G i))
    (hG₀ : ∀ i ν, MvPowerSeries.coeff ν (G i) ∈ P.ringOfDefinition)
    {k : ℕ} (hFG : ∀ i ν, MvPowerSeries.coeff ν (G i - F i) ∈
      (ϖ : C) ^ (k + 1) • (P.ringOfDefinition : Set C))
    {t : Fin N → P.ringOfDefinition}
    {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hJ : M.map ((↑) : P.ringOfDefinition → C) *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C)) :
    ∃ M' : Matrix (Fin N) (Fin N) P.ringOfDefinition,
      (∀ i j, ϖ ∣ M' i j - M i j) ∧
      M'.map ((↑) : P.ringOfDefinition → C) *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (G i))) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) ∧
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (G i))) *
        M'.map ((↑) : P.ringOfDefinition → C) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) := by
  have := P.toNonarchimedeanRing
  have hid : ContinuousAt (RingHom.id C) 0 := continuous_id.continuousAt
  have ht_bd := (isWeightBounded_one_weight_iff_forall_isPowerBounded (RingHom.id C)
    (fun l ↦ (t l : C))).mpr fun l ↦
      P.isBounded_ringOfDefinition.isPowerBounded_of_mem (t l).property
  refine exists_mul_eq_pow_smul_one_of_matrix_dvd P hϖ (J₂ := jacobianOD P hG₀ t)
    (mul_jacobianOD_eq P hF₀ hJ) fun i j ↦
      (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp ?_
  have hGF_res : IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (G i - F i) := by
    rw [sub_eq_add_neg]; exact (hG i).add (hF i).neg
  have hadd := weightedEval_add hid ht_bd (hGF_res.pderiv_one_weight j)
    ((hF i).pderiv_one_weight j)
  rw [← map_add (MvPowerSeries.pderiv j), sub_add_cancel] at hadd
  rw [AddSubgroupClass.coe_sub, jacobianOD_apply, jacobianOD_apply, Subring.coe_pow,
    hadd, add_sub_cancel_right]
  refine weightedEval_mem_pow_smul_of_coeff P hϖ.isUnit (hGF_res.pderiv_one_weight j)
    (fun ν ↦ ?_) t
  obtain ⟨r, hr, hcoeff⟩ := Set.mem_smul_set.mp (hFG i (ν + Finsupp.single j 1))
  refine ⟨((ν j + 1 : ℕ) : C) * r, mul_mem (natCast_mem P.ringOfDefinition _) hr, ?_⟩
  dsimp only at hcoeff ⊢
  rw [MvPowerSeries.coeff_pderiv, ← hcoeff, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- **Uniqueness of zeros in `t + ϖ ^ (k + 1) A₀^N`:** any two zeros `u, u' ∈ A₀^N` of `F`
congruent to `t` modulo `ϖ ^ (k + 1)` are equal, provided the Jacobian of `F` at `t` has an
integral `ϖ ^ k`-scaled left inverse `M` (with no residual hypothesis on `F(t)`). -/
theorem eq_of_weightedEval_eq_zero [T0Space C]
    (hϖ : IsPseudoUniformizer (ϖ : C))
    (hF : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C)) (F i))
    (hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i) ∈ P.ringOfDefinition)
    {t : Fin N → P.ringOfDefinition} {k : ℕ}
    {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hJ : M.map ((↑) : P.ringOfDefinition → C) *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    {u u' : Fin N → P.ringOfDefinition}
    (hu : ∀ i, ϖ ^ (k + 1) ∣ u i - t i)
    (hFu : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C)) (F i) = 0)
    (hu' : ∀ i, ϖ ^ (k + 1) ∣ u' i - t i)
    (hFu' : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u' l : C)) (F i) = 0) :
    u = u' := by
  obtain ⟨Mu, -, hMu, -⟩ := exists_mul_jacobianMatrix_eq_pow_smul_one_of_dvd P hϖ hF hF₀ hJ hu
  exact (existsUnique_weightedEval_eq_zero P hϖ hF hF₀ u hMu
    (fun i ↦ by rw [hFu i]; exact ⟨0, P.ringOfDefinition.zero_mem, by simp⟩)).unique
    ⟨fun _ ↦ by simp, hFu⟩
    ⟨fun i ↦ by simpa only [sub_sub_sub_cancel_right] using dvd_sub (hu' i) (hu i), hFu'⟩

end Newton

end TauCeti.Huber

