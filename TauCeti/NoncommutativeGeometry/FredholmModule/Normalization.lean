/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining
public import TauCeti.Analysis.InnerProductSpace.HermitianDilation.Continuous
public import TauCeti.NoncommutativeGeometry.FredholmModule.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Normalization, doubling, and forced unitization of Fredholm modules

A Fredholm module `(H, π, F)` is *normalized* (or *involutive*) when `F² = 1`, and *degenerate*
when `[F, π(a)] = 0` and `(F² - 1) π(a) = 0` for every `a`. Following Connes (*Noncommutative
Geometry*, Chapter IV, §1, Proposition 2 and Appendix A) and Higson–Roe (*Analytic K-Homology*,
Chapter 8), every Fredholm module can be replaced, up to direct sum with a degenerate module and
operator homotopy through relatively compact perturbations, by a normalized Fredholm module:

1. **Spectral contraction (`sinContraction`).** Applying the odd analytic function
   `x ↦ sin(π x / 2)` via the real continuous functional calculus replaces `F` by a self-adjoint
   contraction `S` (`‖S‖ ≤ 1`, `0 ≤ 1 - S²`). Because `sin(π x / 2) - x` vanishes at `±1`,
   iterated divided differences (`dslope`) factor `sin(π x / 2) - x = (x² - 1) g(x)` for a
   continuous function `g : ℝ → ℝ`, so `(S - F) π(a) = g(F) ((F² - 1) π(a))` is compact and the
   linear path `t ↦ F + t (S - F)` (`sinContractionHomotopy`) is a norm-continuous path of Fredholm
   modules.
2. **Contraction doubling (`double`).** Whenever `0 ≤ 1 - F²`, setting `D = √(1 - F²)` gives
   `(D π(a))* (D π(a)) = -π(a*) ((F² - 1) π(a))`, so `D π(a)` is compact. Perturbing the orthogonal
   sum `(H ⊕ H, π ⊕ 0, F ⊕ -F)` by the Hermitian dilation `[[0, D], [D, 0]]` produces an exact
   involution (`F_dbl² = 1`), connected to `(π ⊕ 0, F ⊕ -F)` by `t ↦ (F ⊕ -F) + t [[0, D], [D, 0]]`
   (`doubleHomotopy`). On any finite-dimensional Hilbert space, `F_dbl` anticommutes with
   `(x, y) ↦ (-y, x)` and therefore has trace zero.
3. **Full normalization (`normalize`).** Composing `sinContraction` with `double` normalizes an
   arbitrary Fredholm module in either parity.
4. **Forced unitization (`unitize`).** Once `F² = 1`, the defect `F² - 1` vanishes identically on
   `H`, so `Unitization.starLift` extends `π` to a unital `*`-algebra homomorphism on
   `Unitization ℂ A` without assuming `A` is unital.

## Main definitions

* `TauCeti.FredholmModule.IsNormalized`, `TauCeti.FredholmModule.IsDegenerate`: involutive and
  degenerate predicates on Fredholm modules.
* `TauCeti.FredholmModule.zeroRep`, `TauCeti.FredholmModule.prod`: zero-representation modules and
  orthogonal direct sums on `WithLp 2 (H₁ × H₂)` (with `EvenFredholmModule` counterparts).
* `TauCeti.FredholmModule.sinContraction`, `TauCeti.FredholmModule.sinContractionHomotopy`:
  functional-calculus contraction `sin(π F / 2)` and its linear homotopy from `F`.
* `TauCeti.FredholmModule.double`, `TauCeti.FredholmModule.doubleHomotopy`,
  `TauCeti.FredholmModule.normalize`: operator doubling of a contraction and two-step normalization
  of an arbitrary Fredholm module (odd and even).
* `TauCeti.FredholmModule.unitize`, `TauCeti.EvenFredholmModule.unitize`: extension of a normalized
  Fredholm module over a non-unital `*`-algebra `A` to `Unitization ℂ A`.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1, Proposition 2 and
  Appendix A.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.3.
-/

public section

noncomputable section

open scoped ComplexStarModule ENNReal InnerProduct NNReal

namespace TauCeti

/-! ### Divided-difference factorization of `sin(π x / 2) - x` -/

/-- Auxiliary continuous quotient `g(x)` satisfying `(x ^ 2 - 1) * g x = sin(π x / 2) - x` for all
`x : ℝ`, constructed by two applications of `dslope` at `1` and `-1`. -/
def sinSubIdQuotient : ℝ → ℝ :=
  dslope (dslope (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x) - x) 1) (-1)

theorem continuous_sinSubIdQuotient : Continuous sinSubIdQuotient := by
  let h₀ : ℝ → ℝ := fun x ↦ Real.sin (Real.pi / 2 * x) - x
  have hh₀ : Differentiable ℝ h₀ := by fun_prop
  have hh₁_cont : Continuous (dslope h₀ 1) :=
    continuous_iff_continuousAt.mpr fun x ↦ by
      rcases eq_or_ne x 1 with rfl | hx
      · exact continuousAt_dslope_same.mpr hh₀.differentiableAt
      · exact (continuousAt_dslope_of_ne hx).mpr hh₀.continuous.continuousAt
  have hh₁_diff : DifferentiableAt ℝ (dslope h₀ 1) (-1) :=
    (differentiableAt_dslope_of_ne (by norm_num)).mpr hh₀.differentiableAt
  exact continuous_iff_continuousAt.mpr fun x ↦ by
    rcases eq_or_ne x (-1) with rfl | hx
    · exact continuousAt_dslope_same.mpr hh₁_diff
    · exact (continuousAt_dslope_of_ne hx).mpr hh₁_cont.continuousAt

theorem sq_sub_one_mul_sinSubIdQuotient (x : ℝ) :
    (x ^ 2 - 1) * sinSubIdQuotient x = Real.sin (Real.pi / 2 * x) - x := by
  let h₀ : ℝ → ℝ := fun x ↦ Real.sin (Real.pi / 2 * x) - x
  have hh₀_one : h₀ 1 = 0 := by simp [h₀]
  have hh₀_neg_one : h₀ (-1) = 0 := by simp [h₀]
  have hh₁_eq (y : ℝ) : (y - 1) * dslope h₀ 1 y = h₀ y :=
    sub_smul_dslope_of_zero hh₀_one y
  have hh₁_neg_one : dslope h₀ 1 (-1) = 0 := by
    have h := hh₁_eq (-1)
    rw [hh₀_neg_one] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have hh₂_eq : (x - -1) * sinSubIdQuotient x = dslope h₀ 1 x :=
    sub_smul_dslope_of_zero hh₁_neg_one x
  calc
    (x ^ 2 - 1) * sinSubIdQuotient x
      = (x - 1) * ((x - -1) * sinSubIdQuotient x) := by ring
    _ = (x - 1) * dslope h₀ 1 x := by rw [hh₂_eq]
    _ = Real.sin (Real.pi / 2 * x) - x := hh₁_eq x

theorem odd_sin_pi_div_two_mul : Function.Odd (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x)) := fun x ↦ by
  dsimp
  rw [mul_neg, Real.sin_neg]

private theorem isSelfAdjoint_ofReal_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {K : H →L[ℂ] H} (hK : IsSelfAdjoint K) (t : ℝ) :
    IsSelfAdjoint ((t : ℂ) • K) := by
  rw [IsSelfAdjoint, star_smul, hK.star_eq, Complex.star_def, Complex.conj_ofReal]

/-! ### Predicates, zero modules, and orthogonal direct sums -/

section BasicConstructions

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable {H H₁ H₂ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

namespace FredholmModule

/-- A Fredholm module is **normalized** (or involutive) when `F² = 1`. -/
def IsNormalized (M : FredholmModule A H) : Prop :=
  M.operator * M.operator = 1

/-- A Fredholm module is **degenerate** when `[F, π(a)] = 0` and `(F² - 1) π(a) = 0` for every
`a : A`. -/
structure IsDegenerate (M : FredholmModule A H) : Prop where
  commutator_eq_zero (a : A) : M.operator * M.rep a - M.rep a * M.operator = 0
  mul_self_sub_one_mul_eq_zero (a : A) : (M.operator * M.operator - 1) * M.rep a = 0

theorem IsDegenerate.commute_operator_rep {M : FredholmModule A H} (hM : M.IsDegenerate) (a : A) :
    Commute M.operator (M.rep a) :=
  sub_eq_zero.mp (hM.commutator_eq_zero a)

theorem IsDegenerate.rep_mul_mul_self_sub_one_eq_zero {M : FredholmModule A H}
    (hM : M.IsDegenerate) (a : A) :
    M.rep a * (M.operator * M.operator - 1) = 0 := by
  have h := congrArg star (hM.mul_self_sub_one_mul_eq_zero (star a))
  rwa [star_mul, map_star, star_star, star_sub, star_mul, star_one, M.star_operator,
    star_zero] at h

@[simp]
theorem IsNormalized.operator_mul_operator {M : FredholmModule A H} (hM : M.IsNormalized) :
    M.operator * M.operator = 1 :=
  hM

theorem IsNormalized.conj {M : FredholmModule A H} (hM : M.IsNormalized) (U : H ≃ₗᵢ[ℂ] H₁) :
    (M.conj U).IsNormalized := by
  rw [IsNormalized, conj_operator, ← map_mul, hM.operator_mul_operator, map_one]

theorem IsDegenerate.conj {M : FredholmModule A H} (hM : M.IsDegenerate) (U : H ≃ₗᵢ[ℂ] H₁) :
    (M.conj U).IsDegenerate where
  commutator_eq_zero a := by
    rw [conj_operator, conj_rep_apply, ← map_mul, ← map_mul, ← map_sub,
      hM.commutator_eq_zero a, map_zero]
  mul_self_sub_one_mul_eq_zero a := by
    rw [conj_operator, conj_rep_apply, ← map_mul, ← map_one U.conjStarAlgEquiv, ← map_sub,
      ← map_mul, hM.mul_self_sub_one_mul_eq_zero a, map_zero]

variable (A H) in
/-- The identically zero `⋆`-representation `A →⋆ₙₐ[ℂ] H →L[ℂ] H`. -/
def zeroStarRep : A →⋆ₙₐ[ℂ] H →L[ℂ] H where
  toFun _ := 0
  map_smul' _ _ := by simp
  map_zero' := rfl
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  map_star' _ := by simp

@[simp]
theorem zeroStarRep_apply (a : A) : zeroStarRep A H a = 0 :=
  (rfl)

variable (A) in
/-- The degenerate Fredholm module with zero representation `π = 0` and a given self-adjoint
operator `F`. -/
def zeroRep (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) : FredholmModule A H where
  rep := zeroStarRep A H
  operator := F
  isSelfAdjoint_operator := hF
  isCompactOperator_commutator _ := by simp [isCompactOperator_zero]
  isCompactOperator_mul_self_sub_one_mul _ := by simp [isCompactOperator_zero]

@[simp]
theorem zeroRep_rep (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) :
    (zeroRep A F hF).rep = zeroStarRep A H :=
  (rfl)

theorem zeroRep_rep_apply (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) (a : A) :
    (zeroRep A F hF).rep a = 0 :=
  (rfl)

@[simp]
theorem zeroRep_operator (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) : (zeroRep A F hF).operator = F :=
  (rfl)

theorem isDegenerate_zeroRep (F : H →L[ℂ] H) (hF : IsSelfAdjoint F) :
    (zeroRep A F hF).IsDegenerate where
  commutator_eq_zero _ := by simp
  mul_self_sub_one_mul_eq_zero _ := by simp

/-- The orthogonal direct sum of two `⋆`-representations on `WithLp 2 (H₁ × H₂)`. -/
def prodStarRep (π₁ : A →⋆ₙₐ[ℂ] H₁ →L[ℂ] H₁) (π₂ : A →⋆ₙₐ[ℂ] H₂ →L[ℂ] H₂) :
    A →⋆ₙₐ[ℂ] WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) where
  toFun a := (π₁ a).withLpProdMap 2 (π₂ a)
  map_smul' c a := by simp [ContinuousLinearMap.withLpProdMap_smul]
  map_zero' := by simp
  map_add' a b := by simp [ContinuousLinearMap.withLpProdMap_add]
  map_mul' a b := by simp [ContinuousLinearMap.withLpProdMap_mul]
  map_star' a := by simp [map_star]

@[simp]
theorem prodStarRep_apply (π₁ : A →⋆ₙₐ[ℂ] H₁ →L[ℂ] H₁) (π₂ : A →⋆ₙₐ[ℂ] H₂ →L[ℂ] H₂) (a : A) :
    prodStarRep π₁ π₂ a = (π₁ a).withLpProdMap 2 (π₂ a) :=
  (rfl)

/-- **Orthogonal direct sum** of two odd Fredholm modules on `WithLp 2 (H₁ × H₂)`. -/
def prod (M₁ : FredholmModule A H₁) (M₂ : FredholmModule A H₂) :
    FredholmModule A (WithLp 2 (H₁ × H₂)) where
  rep := prodStarRep M₁.rep M₂.rep
  operator := M₁.operator.withLpProdMap 2 M₂.operator
  isSelfAdjoint_operator :=
    ContinuousLinearMap.isSelfAdjoint_withLpProdMap_iff.mpr
      ⟨M₁.isSelfAdjoint_operator, M₂.isSelfAdjoint_operator⟩
  isCompactOperator_commutator a := by
    rw [prodStarRep_apply, ContinuousLinearMap.withLpProdMap_mul,
      ContinuousLinearMap.withLpProdMap_mul, ← ContinuousLinearMap.withLpProdMap_sub,
      ContinuousLinearMap.isCompactOperator_withLpProdMap_iff]
    exact ⟨M₁.isCompactOperator_commutator a, M₂.isCompactOperator_commutator a⟩
  isCompactOperator_mul_self_sub_one_mul a := by
    rw [prodStarRep_apply, ContinuousLinearMap.withLpProdMap_mul,
      ← ContinuousLinearMap.withLpProdMap_one, ← ContinuousLinearMap.withLpProdMap_sub,
      ContinuousLinearMap.withLpProdMap_mul,
      ContinuousLinearMap.isCompactOperator_withLpProdMap_iff]
    exact ⟨M₁.isCompactOperator_mul_self_sub_one_mul a,
      M₂.isCompactOperator_mul_self_sub_one_mul a⟩

@[simp]
theorem prod_rep_apply (M₁ : FredholmModule A H₁) (M₂ : FredholmModule A H₂) (a : A) :
    (M₁.prod M₂).rep a = (M₁.rep a).withLpProdMap 2 (M₂.rep a) :=
  (rfl)

@[simp]
theorem prod_operator (M₁ : FredholmModule A H₁) (M₂ : FredholmModule A H₂) :
    (M₁.prod M₂).operator = M₁.operator.withLpProdMap 2 M₂.operator :=
  (rfl)

theorem IsNormalized.prod {M₁ : FredholmModule A H₁} {M₂ : FredholmModule A H₂}
    (h₁ : M₁.IsNormalized) (h₂ : M₂.IsNormalized) : (M₁.prod M₂).IsNormalized := by
  rw [IsNormalized, prod_operator, ContinuousLinearMap.withLpProdMap_mul,
    h₁.operator_mul_operator, h₂.operator_mul_operator, ContinuousLinearMap.withLpProdMap_one]

theorem IsDegenerate.prod {M₁ : FredholmModule A H₁} {M₂ : FredholmModule A H₂}
    (h₁ : M₁.IsDegenerate) (h₂ : M₂.IsDegenerate) : (M₁.prod M₂).IsDegenerate where
  commutator_eq_zero a := by
    rw [prod_operator, prod_rep_apply, ContinuousLinearMap.withLpProdMap_mul,
      ContinuousLinearMap.withLpProdMap_mul, ← ContinuousLinearMap.withLpProdMap_sub,
      h₁.commutator_eq_zero a, h₂.commutator_eq_zero a, ContinuousLinearMap.withLpProdMap_zero]
  mul_self_sub_one_mul_eq_zero a := by
    rw [prod_operator, prod_rep_apply, ContinuousLinearMap.withLpProdMap_mul,
      ← ContinuousLinearMap.withLpProdMap_one, ← ContinuousLinearMap.withLpProdMap_sub,
      ContinuousLinearMap.withLpProdMap_mul, h₁.mul_self_sub_one_mul_eq_zero a,
      h₂.mul_self_sub_one_mul_eq_zero a, ContinuousLinearMap.withLpProdMap_zero]

/-! ### Spectral contraction `sin(π F / 2)` -/

section SinContraction

variable (M : FredholmModule A H)

/-- The self-adjoint perturbation `sin(π F / 2) - F` taking `M.operator` to `sin(π F / 2)`. -/
def sinPerturbation : H →L[ℂ] H :=
  cfc (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x)) M.operator - M.operator

theorem isSelfAdjoint_sinPerturbation : IsSelfAdjoint M.sinPerturbation :=
  (cfc_predicate (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x)) M.operator).sub M.isSelfAdjoint_operator

theorem sinPerturbation_eq_cfc_mul :
    M.sinPerturbation =
      cfc sinSubIdQuotient M.operator * (M.operator * M.operator - 1) := by
  have hF_sa : IsSelfAdjoint M.operator := M.isSelfAdjoint_operator
  have hcont : ContinuousOn sinSubIdQuotient (spectrum ℝ M.operator) :=
    continuous_sinSubIdQuotient.continuousOn
  have hsub :
      M.sinPerturbation = cfc (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x) - x) M.operator := by
    rw [sinPerturbation,
      cfc_sub (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x)) (fun x : ℝ ↦ x) M.operator
        (by fun_prop) continuousOn_id,
      cfc_id' ℝ M.operator hF_sa]
  have hsq :
      cfc (fun x : ℝ ↦ x * x - 1) M.operator = M.operator * M.operator - 1 := by
    rw [cfc_sub (fun x : ℝ ↦ x * x) (fun _ : ℝ ↦ (1 : ℝ)) M.operator (by fun_prop)
        continuousOn_const,
      cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x) M.operator continuousOn_id continuousOn_id,
      cfc_id' ℝ M.operator hF_sa, cfc_const 1 M.operator hF_sa,
      Algebra.algebraMap_eq_smul_one, one_smul]
  calc
    M.sinPerturbation
      = cfc (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x) - x) M.operator := hsub
    _ = cfc (fun x : ℝ ↦ sinSubIdQuotient x * (x * x - 1)) M.operator := by
        refine cfc_congr fun x _ ↦ ?_
        have hq := sq_sub_one_mul_sinSubIdQuotient x
        linarith [sq x]
    _ = cfc sinSubIdQuotient M.operator * cfc (fun x : ℝ ↦ x * x - 1) M.operator :=
        cfc_mul sinSubIdQuotient (fun x : ℝ ↦ x * x - 1) M.operator hcont (by fun_prop)
    _ = cfc sinSubIdQuotient M.operator * (M.operator * M.operator - 1) := by rw [hsq]

theorem isCompactOperator_sinPerturbation_mul_rep (a : A) :
    IsCompactOperator ⇑(M.sinPerturbation * M.rep a) := by
  rw [M.sinPerturbation_eq_cfc_mul, mul_assoc]
  exact (M.isCompactOperator_mul_self_sub_one_mul a).clm_comp (cfc sinSubIdQuotient M.operator)

/-- **Linear operator homotopy** `t ↦ F + t (sin(π F / 2) - F)` connecting `M` at `t = 0` to
`M.sinContraction` at `t = 1` through relatively compact self-adjoint perturbations. -/
def sinContractionHomotopy (t : ℝ) : FredholmModule A H :=
  M.perturb ((t : ℂ) • M.sinPerturbation)
    (isSelfAdjoint_ofReal_smul M.isSelfAdjoint_sinPerturbation t)
    fun a ↦ by
      rw [smul_mul_assoc, FunLike.coe_smul]
      exact (M.isCompactOperator_sinPerturbation_mul_rep a).smul (t : ℂ)

/-- **Spectral contraction** of a Fredholm module: replaces `F` by `sin(π F / 2)`, producing a
self-adjoint contraction (`‖S‖ ≤ 1`, `0 ≤ 1 - S²`) that differs from `F` by a perturbation
compact relative to `π`. -/
def sinContraction : FredholmModule A H :=
  M.perturb M.sinPerturbation M.isSelfAdjoint_sinPerturbation
    M.isCompactOperator_sinPerturbation_mul_rep

@[simp]
theorem sinContraction_rep : M.sinContraction.rep = M.rep := by
  simp [sinContraction]

@[simp]
theorem sinContraction_operator :
    M.sinContraction.operator = cfc (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x)) M.operator := by
  simp [sinContraction, sinPerturbation]

@[simp]
theorem sinContractionHomotopy_rep (t : ℝ) : (M.sinContractionHomotopy t).rep = M.rep := by
  simp [sinContractionHomotopy]

@[simp]
theorem sinContractionHomotopy_operator (t : ℝ) :
    (M.sinContractionHomotopy t).operator = M.operator + (t : ℂ) • M.sinPerturbation := by
  simp [sinContractionHomotopy]

@[simp]
theorem sinContractionHomotopy_zero : M.sinContractionHomotopy 0 = M := by
  ext1 <;> simp

@[simp]
theorem sinContractionHomotopy_one : M.sinContractionHomotopy 1 = M.sinContraction := by
  ext1 <;> simp [sinPerturbation]

theorem continuous_sinContractionHomotopy_operator :
    Continuous fun t : ℝ ↦ (M.sinContractionHomotopy t).operator := by
  simp only [sinContractionHomotopy_operator]
  fun_prop

theorem norm_sinContraction_operator_le_one : ‖M.sinContraction.operator‖ ≤ 1 := by
  rw [sinContraction_operator]
  exact norm_cfc_le zero_le_one fun x _ ↦ by simpa using Real.abs_sin_le_one (Real.pi / 2 * x)

theorem sub_sinContraction_operator_mul_self_nonneg :
    0 ≤ 1 - M.sinContraction.operator * M.sinContraction.operator := by
  have hF_sa : IsSelfAdjoint M.operator := M.isSelfAdjoint_operator
  let s : ℝ → ℝ := fun x ↦ Real.sin (Real.pi / 2 * x)
  have hs : ContinuousOn s (spectrum ℝ M.operator) := by fun_prop
  have h1 :
      1 - M.sinContraction.operator * M.sinContraction.operator =
        cfc (fun x : ℝ ↦ 1 - s x * s x) M.operator := by
    rw [sinContraction_operator,
      cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) (fun x : ℝ ↦ s x * s x) M.operator
        continuousOn_const (hs.mul hs),
      cfc_const 1 M.operator hF_sa, Algebra.algebraMap_eq_smul_one, one_smul,
      cfc_mul s s M.operator hs hs]
  rw [h1]
  exact cfc_nonneg fun x _ ↦ sub_nonneg.mpr (by simpa [sq] using Real.sin_sq_le_one _)

theorem sinContraction_eq_self_of_isNormalized (hM : M.IsNormalized) :
    M.sinContraction = M := by
  have hK : M.sinPerturbation = 0 := by
    rw [M.sinPerturbation_eq_cfc_mul, hM.operator_mul_operator, sub_self, mul_zero]
  ext1
  · simp
  · simp [sinContraction, hK]

end SinContraction

/-! ### Contraction doubling and two-step normalization -/

section Double

variable (M : FredholmModule A H)

/-- Given `0 ≤ 1 - F²`, the operator `√(1 - F²) * π(a)` is compact for every `a : A`. -/
theorem isCompactOperator_sqrt_one_sub_mul_rep
    (hF : 0 ≤ 1 - M.operator * M.operator) (a : A) :
    IsCompactOperator ⇑(CFC.sqrt (1 - M.operator * M.operator) * M.rep a) := by
  let D : H →L[ℂ] H := CFC.sqrt (1 - M.operator * M.operator)
  have hD_sa : IsSelfAdjoint D := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hD_sq : D * D = 1 - M.operator * M.operator := CFC.sqrt_mul_sqrt_self _ hF
  rw [← ContinuousLinearMap.isCompactOperator_star_mul_self_iff]
  have hid :
      star (D * M.rep a) * (D * M.rep a) =
        -(M.rep (star a) * ((M.operator * M.operator - 1) * M.rep a)) := by
    calc
      star (D * M.rep a) * (D * M.rep a)
        = M.rep (star a) * ((D * D) * M.rep a) := by
            simp [star_mul, map_star, hD_sa.star_eq, mul_assoc]
      _ = M.rep (star a) * ((1 - M.operator * M.operator) * M.rep a) := by rw [hD_sq]
      _ = -(M.rep (star a) * ((M.operator * M.operator - 1) * M.rep a)) := by
            rw [← neg_sub (M.operator * M.operator) 1, neg_mul, mul_neg]
  rw [hid]
  exact ((M.isCompactOperator_mul_self_sub_one_mul a).clm_comp (M.rep (star a))).neg

/-- Mirror image of `isCompactOperator_sqrt_one_sub_mul_rep`: `π(a) * √(1 - F²)` is compact. -/
theorem isCompactOperator_rep_mul_sqrt_one_sub
    (hF : 0 ≤ 1 - M.operator * M.operator) (a : A) :
    IsCompactOperator ⇑(M.rep a * CFC.sqrt (1 - M.operator * M.operator)) := by
  have hsa : IsSelfAdjoint (CFC.sqrt (1 - M.operator * M.operator)) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint
  simpa only [star_mul, map_star, star_star, hsa.star_eq] using
    (M.isCompactOperator_sqrt_one_sub_mul_rep hF (star a)).star

/-- **Linear operator homotopy** `t ↦ (F ⊕ -F) + t [[0, √(1 - F²)], [√(1 - F²), 0]]` connecting
`M.prod (zeroRep A (-F) _)` at `t = 0` to `M.double hF` at `t = 1`. -/
def doubleHomotopy (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) :
    FredholmModule A (WithLp 2 (H × H)) :=
  (M.prod (zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg)).perturb
    ((t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation)
    (isSelfAdjoint_ofReal_smul
      (CFC.sqrt (1 - M.operator * M.operator)).isSelfAdjoint_hermitianDilation t)
    fun a ↦ by
      rw [prod_rep_apply, zeroRep_rep_apply, smul_mul_assoc, FunLike.coe_smul]
      exact ((ContinuousLinearMap.isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right
        _ _).mpr (M.isCompactOperator_sqrt_one_sub_mul_rep hF a)).smul (t : ℂ)

/-- **Contraction doubling** of a Fredholm module satisfying `0 ≤ 1 - F²`: on `WithLp 2 (H × H)`,
with representation `π ⊕ 0` and operator `(F ⊕ -F) + [[0, √(1 - F²)], [√(1 - F²), 0]]`. -/
def double (hF : 0 ≤ 1 - M.operator * M.operator) :
    FredholmModule A (WithLp 2 (H × H)) :=
  (M.prod (zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg)).perturb
    (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation
    (CFC.sqrt (1 - M.operator * M.operator)).isSelfAdjoint_hermitianDilation
    fun a ↦ by
      rw [prod_rep_apply, zeroRep_rep_apply]
      exact (ContinuousLinearMap.isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right
        _ _).mpr (M.isCompactOperator_sqrt_one_sub_mul_rep hF a)

@[simp]
theorem double_rep_apply (hF : 0 ≤ 1 - M.operator * M.operator) (a : A) :
    (M.double hF).rep a = (M.rep a).withLpProdMap 2 0 := by
  simp [double]

@[simp]
theorem double_operator (hF : 0 ≤ 1 - M.operator * M.operator) :
    (M.double hF).operator =
      M.operator.withLpProdMap 2 (-M.operator) +
        (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation := by
  simp [double]

@[simp]
theorem doubleHomotopy_rep_apply (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) (a : A) :
    (M.doubleHomotopy hF t).rep a = (M.rep a).withLpProdMap 2 0 := by
  simp [doubleHomotopy]

@[simp]
theorem doubleHomotopy_operator (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) :
    (M.doubleHomotopy hF t).operator =
      M.operator.withLpProdMap 2 (-M.operator) +
        (t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation := by
  simp [doubleHomotopy]

@[simp]
theorem doubleHomotopy_zero (hF : 0 ≤ 1 - M.operator * M.operator) :
    M.doubleHomotopy hF 0 = M.prod (zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg) := by
  ext1
  · ext1 a
    simp
  · simp

@[simp]
theorem doubleHomotopy_one (hF : 0 ≤ 1 - M.operator * M.operator) :
    M.doubleHomotopy hF 1 = M.double hF := by
  ext1
  · ext1 a
    simp
  · simp

theorem continuous_doubleHomotopy_operator (hF : 0 ≤ 1 - M.operator * M.operator) :
    Continuous fun t : ℝ ↦ (M.doubleHomotopy hF t).operator := by
  simp only [doubleHomotopy_operator]
  fun_prop

/-- **Doubling produces an exact involution.** `(M.double hF).operator ^ 2 = 1`. -/
theorem isNormalized_double (hF : 0 ≤ 1 - M.operator * M.operator) :
    (M.double hF).IsNormalized := by
  rw [IsNormalized, double_operator]
  let D : H →L[ℂ] H := CFC.sqrt (1 - M.operator * M.operator)
  have hD_sa : IsSelfAdjoint D := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hD_adj : D† = D := ContinuousLinearMap.star_eq_adjoint D ▸ hD_sa.star_eq
  have hD_sq : D * D = 1 - M.operator * M.operator := CFC.sqrt_mul_sqrt_self _ hF
  have hcomm_sub : Commute (1 - M.operator * M.operator) M.operator :=
    (Commute.one_left M.operator).sub_left ((Commute.refl M.operator).mul_left (.refl _))
  have hFD : Commute M.operator D :=
    (hcomm_sub.cfcₙ_nnreal NNReal.sqrt).symm
  have hanti :
      M.operator.withLpProdMap 2 (-M.operator) * D.hermitianDilation +
        D.hermitianDilation * M.operator.withLpProdMap 2 (-M.operator) = 0 :=
    ContinuousLinearMap.withLpProdMap_neg_mul_hermitianDilation_add hD_sa hFD
  calc
    (M.operator.withLpProdMap 2 (-M.operator) + D.hermitianDilation) *
        (M.operator.withLpProdMap 2 (-M.operator) + D.hermitianDilation)
      = M.operator.withLpProdMap 2 (-M.operator) * M.operator.withLpProdMap 2 (-M.operator) +
          (M.operator.withLpProdMap 2 (-M.operator) * D.hermitianDilation +
            D.hermitianDilation * M.operator.withLpProdMap 2 (-M.operator)) +
          D.hermitianDilation * D.hermitianDilation := by noncomm_ring
    _ = (M.operator * M.operator).withLpProdMap 2 (M.operator * M.operator) +
          (1 - M.operator * M.operator).withLpProdMap 2 (1 - M.operator * M.operator) := by
        rw [hanti, add_zero, ContinuousLinearMap.withLpProdMap_mul, neg_mul_neg,
          D.hermitianDilation_mul_self, hD_adj, ← ContinuousLinearMap.mul_def, hD_sq]
    _ = 1 := by
        rw [← ContinuousLinearMap.withLpProdMap_add, add_sub_cancel,
          ContinuousLinearMap.withLpProdMap_one]

/-- The doubled operator on `WithLp 2 (H × H)` has trace zero because it anticommutes with the
symplectic rotation `(x, y) ↦ (-y, x)`. -/
theorem trace_double_operator_eq_zero (hF : 0 ≤ 1 - M.operator * M.operator) :
    LinearMap.trace ℂ (WithLp 2 (H × H)) (M.double hF).operator.toLinearMap = 0 := by
  let J : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap ∘L
      ((-ContinuousLinearMap.snd ℂ H H).prod (ContinuousLinearMap.fst ℂ H H)) ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap
  have hJ_apply (x : WithLp 2 (H × H)) : J x = WithLp.toLp 2 (-x.snd, x.fst) := (rfl)
  let D : H →L[ℂ] H := CFC.sqrt (1 - M.operator * M.operator)
  have hD_adj : D† = D :=
    ContinuousLinearMap.star_eq_adjoint D ▸ (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  let T : WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) := (M.double hF).operator
  have hJJ : J.toLinearMap * J.toLinearMap = -1 := by
    ext ⟨x, y⟩
    simp [hJ_apply, ← WithLp.toLp_neg]
  have hJT : J.toLinearMap * T.toLinearMap = -(T.toLinearMap * J.toLinearMap) := by
    ext ⟨x, y⟩
    simp [T, double_operator, D, hJ_apply, hD_adj, ← WithLp.toLp_add, ← WithLp.toLp_neg, add_comm]
  have hneg :
      LinearMap.trace ℂ (WithLp 2 (H × H)) T.toLinearMap =
        -LinearMap.trace ℂ (WithLp 2 (H × H)) T.toLinearMap := by
    have h1 : (-J.toLinearMap * J.toLinearMap) * T.toLinearMap = T.toLinearMap := by
      rw [neg_mul, hJJ, neg_neg, one_mul]
    calc
      LinearMap.trace ℂ (WithLp 2 (H × H)) T.toLinearMap
        = LinearMap.trace ℂ (WithLp 2 (H × H))
            ((-J.toLinearMap) * (J.toLinearMap * T.toLinearMap)) := by
            rw [← mul_assoc, h1]
      _ = LinearMap.trace ℂ (WithLp 2 (H × H))
            (J.toLinearMap * (T.toLinearMap * J.toLinearMap)) := by
            rw [hJT, neg_mul_neg]
      _ = LinearMap.trace ℂ (WithLp 2 (H × H))
            ((T.toLinearMap * J.toLinearMap) * J.toLinearMap) :=
            LinearMap.trace_mul_comm ℂ J.toLinearMap (T.toLinearMap * J.toLinearMap)
      _ = LinearMap.trace ℂ (WithLp 2 (H × H)) (-T.toLinearMap) := by
            rw [mul_assoc, hJJ, mul_neg, mul_one]
      _ = -LinearMap.trace ℂ (WithLp 2 (H × H)) T.toLinearMap := map_neg _ _
  exact CharZero.eq_neg_self_iff.mp hneg

/-- **Two-step normalization** of an arbitrary odd Fredholm module: first contract `F` to
`sin(π F / 2)` and then double onto `WithLp 2 (H × H)`. -/
def normalize : FredholmModule A (WithLp 2 (H × H)) :=
  M.sinContraction.double M.sub_sinContraction_operator_mul_self_nonneg

theorem normalize_def :
    M.normalize = M.sinContraction.double M.sub_sinContraction_operator_mul_self_nonneg :=
  (rfl)

@[simp]
theorem normalize_rep_apply (a : A) :
    M.normalize.rep a = (M.rep a).withLpProdMap 2 0 := by
  simp [normalize]

theorem isNormalized_normalize : M.normalize.IsNormalized :=
  M.sinContraction.isNormalized_double M.sub_sinContraction_operator_mul_self_nonneg

end Double

/-! ### Explicit scalar check `F = (1 / 2) • 1` -/

section ScalarHalfCheck

/-- The constant scalar contraction `(2⁻¹ : ℂ) • 1` on `H` is self-adjoint. -/
theorem isSelfAdjoint_half_smul_one : IsSelfAdjoint ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)) := by
  simpa using isSelfAdjoint_ofReal_smul (IsSelfAdjoint.one (R := H →L[ℂ] H)) (2⁻¹ : ℝ)

/-- For `F = (2⁻¹ : ℂ) • 1` on `H`, `0 ≤ 1 - F * F` with square root `((√3 / 2 : ℝ) : ℂ) • 1`. -/
theorem one_sub_half_smul_one_mul_self_nonneg :
    0 ≤ (1 : H →L[ℂ] H) - ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)) * ((2⁻¹ : ℂ) • 1) := by
  let S : H →L[ℂ] H := ((Real.sqrt 3 / 2 : ℝ) : ℂ) • 1
  have hS_sa : IsSelfAdjoint S :=
    isSelfAdjoint_ofReal_smul (IsSelfAdjoint.one (R := H →L[ℂ] H)) (Real.sqrt 3 / 2)
  have hreal : (1 : ℝ) - 2⁻¹ * 2⁻¹ = Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
    linarith
  have hnum : (1 : ℂ) - 2⁻¹ * 2⁻¹ = ((Real.sqrt 3 / 2 : ℝ) : ℂ) * ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
    simpa using congrArg Complex.ofReal hreal
  have hsq :
      (1 : H →L[ℂ] H) - ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)) * ((2⁻¹ : ℂ) • 1) = star S * S := by
    rw [hS_sa.star_eq]
    ext x
    simp only [S, sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      smul_apply, one_apply_eq_self, smul_smul]
    conv_lhs =>
      enter [1]
      rw [← one_smul ℂ x]
    rw [← sub_smul, hnum]
  rw [hsq]
  exact star_mul_self_nonneg S

theorem sqrt_one_sub_half_smul_one_mul_self :
    CFC.sqrt ((1 : H →L[ℂ] H) - ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)) * ((2⁻¹ : ℂ) • 1)) =
      ((Real.sqrt 3 / 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H) := by
  let S : H →L[ℂ] H := ((Real.sqrt 3 / 2 : ℝ) : ℂ) • 1
  have hS_nonneg : 0 ≤ S := by
    let T : H →L[ℂ] H := ((Real.sqrt (Real.sqrt 3 / 2) : ℝ) : ℂ) • 1
    have hT_sa : IsSelfAdjoint T :=
      isSelfAdjoint_ofReal_smul (IsSelfAdjoint.one (R := H →L[ℂ] H))
        (Real.sqrt (Real.sqrt 3 / 2))
    have hpos : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
    have hT_num :
        ((Real.sqrt (Real.sqrt 3 / 2) : ℝ) : ℂ) * ((Real.sqrt (Real.sqrt 3 / 2) : ℝ) : ℂ) =
          ((Real.sqrt 3 / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]
    have hTT : star T * T = S := by
      rw [hT_sa.star_eq]
      ext x
      simp only [T, S, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        smul_apply, one_apply_eq_self, smul_smul, hT_num]
    exact hTT ▸ star_mul_self_nonneg T
  have hreal : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = (1 : ℝ) - 2⁻¹ * 2⁻¹ := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by positivity)
    linarith
  have hnum : ((Real.sqrt 3 / 2 : ℝ) : ℂ) * ((Real.sqrt 3 / 2 : ℝ) : ℂ) = (1 : ℂ) - 2⁻¹ * 2⁻¹ := by
    simpa using congrArg Complex.ofReal hreal
  refine CFC.sqrt_unique ?_ hS_nonneg
  ext x
  simp only [sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    smul_apply, one_apply_eq_self, smul_smul]
  conv_rhs =>
    enter [1]
    rw [← one_smul ℂ x]
  rw [← sub_smul, hnum]

variable (A H) in
/-- Degenerate Fredholm module on `H` with zero representation and constant scalar contraction
`F = (2⁻¹ : ℂ) • 1`. -/
def halfSmulZeroRep : FredholmModule A H :=
  zeroRep A ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)) isSelfAdjoint_half_smul_one

theorem sub_halfSmulZeroRep_operator_mul_self_nonneg :
    0 ≤ 1 - (halfSmulZeroRep A H).operator * (halfSmulZeroRep A H).operator :=
  one_sub_half_smul_one_mul_self_nonneg

variable (A) in
/-- Concrete check on the constant scalar contraction `F = (2⁻¹ : ℂ) • 1` on any Hilbert space `H`
(in particular `H = ℂ`): doubling produces an involutive operator (`F_dbl² = 1`) on
`WithLp 2 (H × H)` with off-diagonal entry `(√3 / 2) • 1` and trace zero. -/
theorem double_halfSmulZeroRep_check :
    ((halfSmulZeroRep A H).double sub_halfSmulZeroRep_operator_mul_self_nonneg).IsNormalized ∧
      ((halfSmulZeroRep A H).double sub_halfSmulZeroRep_operator_mul_self_nonneg).operator =
        ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)).withLpProdMap 2 (-((2⁻¹ : ℂ) • 1)) +
          (((Real.sqrt 3 / 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H)).hermitianDilation ∧
      LinearMap.trace ℂ (WithLp 2 (H × H))
        ((halfSmulZeroRep A H).double
          sub_halfSmulZeroRep_operator_mul_self_nonneg).operator.toLinearMap = 0 := by
  refine ⟨(halfSmulZeroRep A H).isNormalized_double sub_halfSmulZeroRep_operator_mul_self_nonneg,
    ?_, (halfSmulZeroRep A H).trace_double_operator_eq_zero
      sub_halfSmulZeroRep_operator_mul_self_nonneg⟩
  rw [double_operator]
  change ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)).withLpProdMap 2 (-((2⁻¹ : ℂ) • 1)) +
      (CFC.sqrt (1 - ((2⁻¹ : ℂ) • (1 : H →L[ℂ] H)) * ((2⁻¹ : ℂ) • 1))).hermitianDilation = _
  rw [sqrt_one_sub_half_smul_one_mul_self]

end ScalarHalfCheck

end FredholmModule

/-! ### Even counterparts: direct sums, contraction, doubling, and normalization -/

namespace EvenFredholmModule

/-- An even Fredholm module is **normalized** when its underlying operator satisfies `F² = 1`. -/
abbrev IsNormalized (M : EvenFredholmModule A H) : Prop :=
  M.toFredholmModule.IsNormalized

/-- An even Fredholm module is **degenerate** when `[F, π(a)] = 0` and `(F² - 1) π(a) = 0` for
every `a : A`. -/
abbrev IsDegenerate (M : EvenFredholmModule A H) : Prop :=
  M.toFredholmModule.IsDegenerate

variable (A) in
/-- The degenerate even Fredholm module with zero representation `π = 0`, operator `F`, and
grading `γ` anticommuting with `F`. -/
def zeroRep (F γ : H →L[ℂ] H) (hF : IsSelfAdjoint F) (hγ : IsSelfAdjoint γ) (hγγ : γ * γ = 1)
    (hγF : γ * F = -(F * γ)) : EvenFredholmModule A H where
  toFredholmModule := FredholmModule.zeroRep A F hF
  grading := γ
  isSelfAdjoint_grading := hγ
  grading_mul_grading := hγγ
  commute_grading_rep _ := Commute.zero_right γ
  grading_mul_operator := hγF

@[simp]
theorem zeroRep_toFredholmModule (F γ : H →L[ℂ] H) (hF hγ hγγ hγF) :
    (zeroRep A F γ hF hγ hγγ hγF).toFredholmModule = FredholmModule.zeroRep A F hF :=
  (rfl)

@[simp]
theorem zeroRep_grading (F γ : H →L[ℂ] H) (hF hγ hγγ hγF) :
    (zeroRep A F γ hF hγ hγγ hγF).grading = γ :=
  (rfl)

theorem isDegenerate_zeroRep (F γ : H →L[ℂ] H) (hF hγ hγγ hγF) :
    (zeroRep A F γ hF hγ hγγ hγF).IsDegenerate :=
  FredholmModule.isDegenerate_zeroRep F hF

/-- **Orthogonal direct sum** of two even Fredholm modules on `WithLp 2 (H₁ × H₂)`. -/
def prod (M₁ : EvenFredholmModule A H₁) (M₂ : EvenFredholmModule A H₂) :
    EvenFredholmModule A (WithLp 2 (H₁ × H₂)) where
  toFredholmModule := M₁.toFredholmModule.prod M₂.toFredholmModule
  grading := M₁.grading.withLpProdMap 2 M₂.grading
  isSelfAdjoint_grading :=
    ContinuousLinearMap.isSelfAdjoint_withLpProdMap_iff.mpr
      ⟨M₁.isSelfAdjoint_grading, M₂.isSelfAdjoint_grading⟩
  grading_mul_grading := by
    rw [ContinuousLinearMap.withLpProdMap_mul, M₁.grading_mul_grading, M₂.grading_mul_grading,
      ContinuousLinearMap.withLpProdMap_one]
  commute_grading_rep a := by
    rw [Commute, SemiconjBy, FredholmModule.prod_rep_apply, ContinuousLinearMap.withLpProdMap_mul,
      ContinuousLinearMap.withLpProdMap_mul, (M₁.commute_grading_rep a).eq,
      (M₂.commute_grading_rep a).eq]
  grading_mul_operator := by
    rw [FredholmModule.prod_operator, ContinuousLinearMap.withLpProdMap_mul,
      ContinuousLinearMap.withLpProdMap_mul, M₁.grading_mul_operator, M₂.grading_mul_operator,
      ContinuousLinearMap.withLpProdMap_neg]

@[simp]
theorem prod_toFredholmModule (M₁ : EvenFredholmModule A H₁) (M₂ : EvenFredholmModule A H₂) :
    (M₁.prod M₂).toFredholmModule = M₁.toFredholmModule.prod M₂.toFredholmModule :=
  (rfl)

@[simp]
theorem prod_grading (M₁ : EvenFredholmModule A H₁) (M₂ : EvenFredholmModule A H₂) :
    (M₁.prod M₂).grading = M₁.grading.withLpProdMap 2 M₂.grading :=
  (rfl)

section ParityOps

variable (M : EvenFredholmModule A H)

/-- Reversing the sign of the grading `γ ↦ -γ` reverses the orientation of an even Fredholm
module. -/
def flipGrading : EvenFredholmModule A H where
  toFredholmModule := M.toFredholmModule
  grading := -M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading.neg
  grading_mul_grading := by rw [neg_mul_neg, M.grading_mul_grading]
  commute_grading_rep a := (M.commute_grading_rep a).neg_left
  grading_mul_operator := by rw [neg_mul, mul_neg, M.grading_mul_operator]

@[simp]
theorem flipGrading_toFredholmModule : M.flipGrading.toFredholmModule = M.toFredholmModule :=
  (rfl)

@[simp]
theorem flipGrading_grading : M.flipGrading.grading = -M.grading :=
  (rfl)

@[simp]
theorem flipGrading_flipGrading : M.flipGrading.flipGrading = M := by
  ext1 <;> simp

theorem grading_mul_sinPerturbation :
    M.grading * M.toFredholmModule.sinPerturbation =
      -(M.toFredholmModule.sinPerturbation * M.grading) := by
  have hcfc :
      M.grading * cfc (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x)) M.operator =
        -(cfc (fun x : ℝ ↦ Real.sin (Real.pi / 2 * x)) M.operator * M.grading) :=
    mul_cfc_eq_neg_cfc_mul_of_odd M.grading_mul_operator odd_sin_pi_div_two_mul
  rw [FredholmModule.sinPerturbation, mul_sub, sub_mul, hcfc, M.grading_mul_operator,
    neg_sub_neg, neg_sub]

/-- **Linear operator homotopy** of even Fredholm modules from `M` at `t = 0` to
`M.sinContraction` at `t = 1`. -/
def sinContractionHomotopy (t : ℝ) : EvenFredholmModule A H :=
  M.perturb ((t : ℂ) • M.toFredholmModule.sinPerturbation)
    (isSelfAdjoint_ofReal_smul M.toFredholmModule.isSelfAdjoint_sinPerturbation t)
    (fun a ↦ by
      rw [smul_mul_assoc, FunLike.coe_smul]
      exact (M.toFredholmModule.isCompactOperator_sinPerturbation_mul_rep a).smul (t : ℂ))
    (by rw [mul_smul_comm, smul_mul_assoc, M.grading_mul_sinPerturbation, smul_neg])

/-- **Spectral contraction**, even version: `sin(π F / 2)` is odd, so it anticommutes with `γ`. -/
def sinContraction : EvenFredholmModule A H :=
  M.perturb M.toFredholmModule.sinPerturbation M.toFredholmModule.isSelfAdjoint_sinPerturbation
    M.toFredholmModule.isCompactOperator_sinPerturbation_mul_rep M.grading_mul_sinPerturbation

@[simp]
theorem sinContraction_toFredholmModule :
    M.sinContraction.toFredholmModule = M.toFredholmModule.sinContraction := by
  simp [sinContraction, FredholmModule.sinContraction]

@[simp]
theorem sinContraction_grading : M.sinContraction.grading = M.grading := by
  simp [sinContraction]

@[simp]
theorem sinContractionHomotopy_toFredholmModule (t : ℝ) :
    (M.sinContractionHomotopy t).toFredholmModule =
      M.toFredholmModule.sinContractionHomotopy t := by
  simp [sinContractionHomotopy, FredholmModule.sinContractionHomotopy]

@[simp]
theorem sinContractionHomotopy_grading (t : ℝ) :
    (M.sinContractionHomotopy t).grading = M.grading := by
  simp [sinContractionHomotopy]

@[simp]
theorem sinContractionHomotopy_zero : M.sinContractionHomotopy 0 = M := by
  ext1 <;> simp

@[simp]
theorem sinContractionHomotopy_one : M.sinContractionHomotopy 1 = M.sinContraction := by
  ext1 <;> simp

theorem commute_grading_sqrt_one_sub :
    Commute M.grading (CFC.sqrt (1 - M.operator * M.operator)) := by
  have hsq : Commute (1 - M.operator * M.operator) M.grading := by
    refine (Commute.one_left M.grading).sub_left ?_
    rw [Commute, SemiconjBy]
    calc
      M.operator * M.operator * M.grading
        = M.operator * (M.operator * M.grading) := mul_assoc _ _ _
      _ = -(M.operator * (M.grading * M.operator)) := by
            rw [← neg_eq_iff_eq_neg.mpr M.grading_mul_operator, mul_neg]
      _ = -((M.operator * M.grading) * M.operator) := by rw [mul_assoc]
      _ = M.grading * (M.operator * M.operator) := by
            rw [← neg_eq_iff_eq_neg.mpr M.grading_mul_operator, neg_mul, neg_neg, mul_assoc]
  exact (hsq.cfcₙ_nnreal NNReal.sqrt).symm

/-- **Linear operator homotopy** of even Fredholm modules connecting
`M.prod (zeroRep A (-F) (-γ) ...)` at `t = 0` to `M.double hF` at `t = 1`. -/
def doubleHomotopy (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) :
    EvenFredholmModule A (WithLp 2 (H × H)) :=
  (M.prod (zeroRep A (-M.operator) (-M.grading) M.isSelfAdjoint_operator.neg
    M.isSelfAdjoint_grading.neg (by rw [neg_mul_neg, M.grading_mul_grading])
    (by rw [neg_mul_neg, mul_neg, neg_mul, neg_neg, M.grading_mul_operator]))).perturb
    ((t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation)
    (isSelfAdjoint_ofReal_smul
      (CFC.sqrt (1 - M.operator * M.operator)).isSelfAdjoint_hermitianDilation t)
    (fun a ↦ by
      rw [prod_toFredholmModule, FredholmModule.prod_rep_apply, zeroRep_toFredholmModule,
        FredholmModule.zeroRep_rep_apply, smul_mul_assoc, FunLike.coe_smul]
      exact ((ContinuousLinearMap.isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right
        _ _).mpr (M.toFredholmModule.isCompactOperator_sqrt_one_sub_mul_rep hF a)).smul (t : ℂ))
    (by
      rw [prod_grading, zeroRep_grading, mul_smul_comm, smul_mul_assoc,
        ContinuousLinearMap.withLpProdMap_neg_mul_hermitianDilation_eq_neg
          (CFC.sqrt_nonneg _).isSelfAdjoint M.commute_grading_sqrt_one_sub,
        smul_neg])

/-- **Contraction doubling**, even version: equips `M.toFredholmModule.double hF` with the grading
`γ ⊕ (-γ)`, which commutes with `π ⊕ 0` and anticommutes with `[[0, √(1 - F²)], [√(1 - F²), 0]]`. -/
def double (hF : 0 ≤ 1 - M.operator * M.operator) :
    EvenFredholmModule A (WithLp 2 (H × H)) :=
  (M.prod (zeroRep A (-M.operator) (-M.grading) M.isSelfAdjoint_operator.neg
    M.isSelfAdjoint_grading.neg (by rw [neg_mul_neg, M.grading_mul_grading])
    (by rw [neg_mul_neg, mul_neg, neg_mul, neg_neg, M.grading_mul_operator]))).perturb
    (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation
    (CFC.sqrt (1 - M.operator * M.operator)).isSelfAdjoint_hermitianDilation
    (fun a ↦ by
      rw [prod_toFredholmModule, FredholmModule.prod_rep_apply, zeroRep_toFredholmModule,
        FredholmModule.zeroRep_rep_apply]
      exact (ContinuousLinearMap.isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right
        _ _).mpr (M.toFredholmModule.isCompactOperator_sqrt_one_sub_mul_rep hF a))
    (by
      rw [prod_grading, zeroRep_grading]
      exact ContinuousLinearMap.withLpProdMap_neg_mul_hermitianDilation_eq_neg
        (CFC.sqrt_nonneg _).isSelfAdjoint M.commute_grading_sqrt_one_sub)

@[simp]
theorem double_toFredholmModule (hF : 0 ≤ 1 - M.operator * M.operator) :
    (M.double hF).toFredholmModule = M.toFredholmModule.double hF := by
  simp [double, FredholmModule.double]

@[simp]
theorem double_grading (hF : 0 ≤ 1 - M.operator * M.operator) :
    (M.double hF).grading = M.grading.withLpProdMap 2 (-M.grading) := by
  simp [double]

@[simp]
theorem doubleHomotopy_toFredholmModule (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) :
    (M.doubleHomotopy hF t).toFredholmModule = M.toFredholmModule.doubleHomotopy hF t := by
  simp [doubleHomotopy, FredholmModule.doubleHomotopy]

@[simp]
theorem doubleHomotopy_grading (hF : 0 ≤ 1 - M.operator * M.operator) (t : ℝ) :
    (M.doubleHomotopy hF t).grading = M.grading.withLpProdMap 2 (-M.grading) := by
  simp [doubleHomotopy]

@[simp]
theorem doubleHomotopy_zero (hF : 0 ≤ 1 - M.operator * M.operator) :
    M.doubleHomotopy hF 0 =
      M.prod (zeroRep A (-M.operator) (-M.grading) M.isSelfAdjoint_operator.neg
        M.isSelfAdjoint_grading.neg (by rw [neg_mul_neg, M.grading_mul_grading])
        (by rw [neg_mul_neg, mul_neg, neg_mul, neg_neg, M.grading_mul_operator])) := by
  ext1 <;> simp

@[simp]
theorem doubleHomotopy_one (hF : 0 ≤ 1 - M.operator * M.operator) :
    M.doubleHomotopy hF 1 = M.double hF := by
  ext1 <;> simp

theorem isNormalized_double (hF : 0 ≤ 1 - M.operator * M.operator) :
    (M.double hF).IsNormalized := by
  rw [IsNormalized, double_toFredholmModule]
  exact M.toFredholmModule.isNormalized_double hF

/-- **Two-step normalization** of an arbitrary even Fredholm module. -/
def normalize : EvenFredholmModule A (WithLp 2 (H × H)) :=
  M.sinContraction.double
    (by simpa using M.toFredholmModule.sub_sinContraction_operator_mul_self_nonneg)

theorem normalize_def :
    M.normalize =
      M.sinContraction.double
        (by simpa using M.toFredholmModule.sub_sinContraction_operator_mul_self_nonneg) :=
  (rfl)

@[simp]
theorem normalize_toFredholmModule :
    M.normalize.toFredholmModule = M.toFredholmModule.normalize := by
  simp [normalize, FredholmModule.normalize]

@[simp]
theorem normalize_grading :
    M.normalize.grading = M.grading.withLpProdMap 2 (-M.grading) := by
  simp [normalize]

theorem isNormalized_normalize : M.normalize.IsNormalized := by
  rw [IsNormalized, normalize_toFredholmModule]
  exact M.toFredholmModule.isNormalized_normalize

end ParityOps

end EvenFredholmModule

end BasicConstructions

/-! ### Forced unitization of normalized Fredholm modules -/

section Unitization

variable {A : Type*} [NonUnitalSemiring A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem starLift_rep_inl_add_inr (π : A →⋆ₙₐ[ℂ] H →L[ℂ] H) (c : ℂ) (a : A) :
    Unitization.starLift π (Unitization.inl c + Unitization.inr a) = c • 1 + π a := by
  have hinr : Unitization.starLift π (Unitization.inr a) = π a :=
    DFunLike.congr_fun (Unitization.starLift.symm_apply_apply π) a
  have hinl : Unitization.starLift π (Unitization.inl c) = c • 1 := by
    rw [← Unitization.algebraMap_eq_inl, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]
  rw [map_add, hinl, hinr]

namespace FredholmModule

/-- **Forced unitization.** A normalized (`F² = 1`) Fredholm module over a non-unital `*`-algebra
`A` extends canonically to a unital Fredholm module over `Unitization ℂ A` via
`Unitization.starLift M.rep`, sending `(c, a) ↦ c • 1 + π(a)`. -/
def unitize (M : FredholmModule A H) (hM : M.IsNormalized) :
    FredholmModule (Unitization ℂ A) H where
  rep := (Unitization.starLift M.rep).toNonUnitalStarAlgHom
  operator := M.operator
  isSelfAdjoint_operator := M.isSelfAdjoint_operator
  isCompactOperator_commutator x := by
    change IsCompactOperator
      ⇑(M.operator * Unitization.starLift M.rep x - Unitization.starLift M.rep x * M.operator)
    induction x with
    | inl_add_inr c a =>
      have hcomm :
          M.operator * Unitization.starLift M.rep (Unitization.inl c + Unitization.inr a) -
            Unitization.starLift M.rep (Unitization.inl c + Unitization.inr a) * M.operator =
            M.operator * M.rep a - M.rep a * M.operator := by
        rw [starLift_rep_inl_add_inr, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
          one_mul, add_sub_add_left_eq_sub]
      rw [hcomm]
      exact M.isCompactOperator_commutator a
  isCompactOperator_mul_self_sub_one_mul _ := by
    rw [hM.operator_mul_operator, sub_self, zero_mul]
    exact isCompactOperator_zero

@[simp]
theorem unitize_operator (M : FredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM).operator = M.operator :=
  (rfl)

@[simp]
theorem unitize_rep_one (M : FredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM).rep 1 = 1 :=
  (Unitization.starLift M.rep).map_one

@[simp]
theorem unitize_rep_inr (M : FredholmModule A H) (hM : M.IsNormalized) (a : A) :
    (M.unitize hM).rep (Unitization.inr a) = M.rep a :=
  DFunLike.congr_fun (Unitization.starLift.symm_apply_apply M.rep) a

@[simp]
theorem unitize_rep_algebraMap (M : FredholmModule A H) (hM : M.IsNormalized) (c : ℂ) :
    (M.unitize hM).rep (algebraMap ℂ (Unitization ℂ A) c) = c • 1 := by
  change Unitization.starLift M.rep (algebraMap ℂ (Unitization ℂ A) c) = c • 1
  rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one]

theorem isNormalized_unitize (M : FredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM).IsNormalized :=
  hM

end FredholmModule

namespace EvenFredholmModule

/-- **Forced unitization**, even version: extends a normalized even Fredholm module over `A` to
`Unitization ℂ A`, preserving `F` and `γ`. -/
def unitize (M : EvenFredholmModule A H) (hM : M.IsNormalized) :
    EvenFredholmModule (Unitization ℂ A) H where
  toFredholmModule := M.toFredholmModule.unitize hM
  grading := M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading
  grading_mul_grading := M.grading_mul_grading
  commute_grading_rep x := by
    change Commute M.grading (Unitization.starLift M.rep x)
    induction x with
    | inl_add_inr c a =>
      rw [starLift_rep_inl_add_inr]
      exact ((Commute.one_right M.grading).smul_right c).add_right (M.commute_grading_rep a)
  grading_mul_operator := M.grading_mul_operator

@[simp]
theorem unitize_toFredholmModule (M : EvenFredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM).toFredholmModule = M.toFredholmModule.unitize hM :=
  (rfl)

@[simp]
theorem unitize_grading (M : EvenFredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM).grading = M.grading :=
  (rfl)

theorem isNormalized_unitize (M : EvenFredholmModule A H) (hM : M.IsNormalized) :
    (M.unitize hM).IsNormalized :=
  hM

end EvenFredholmModule

end Unitization

end TauCeti
