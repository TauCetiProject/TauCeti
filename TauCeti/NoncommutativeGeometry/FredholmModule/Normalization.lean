/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.InnerProductSpace.Contraction.Dilation
public import TauCeti.Analysis.Normed.Operator.Compact.EssentialCommutant
public import TauCeti.NoncommutativeGeometry.FredholmModule.DirectSum
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Algebra.Ring.Commute
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Intertwining
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Normalization of Fredholm modules and its operator homotopies

In a general Fredholm module `(H, π, F)` the operator `F` need only be a symmetry modulo compact
operators: `[F, π(a)]` and `(F² - 1) π(a)` are compact, rather than `F² - 1` itself, which need only
become compact after multiplication by `π(a)`. The odd index pairing, through the projection
`(1 + F) / 2`, and the Chern character are built from normalized modules (`F² = 1`), and every
Fredholm module can be brought to that form in two steps, each realized up to degenerate direct
summands by a norm-continuous linear operator homotopy:

1. **The sine replacement (`sineReplacement`, `sineReplacementHomotopy`).** For a self-adjoint `F`
   the operator `S = sin (π F / 2)`, defined by the continuous functional calculus, is a
   self-adjoint contraction. It still has compact commutators with `π(A)` because the essential
   commutant of `π(A)` is closed under the functional calculus. Moreover `sin (π x / 2) - x`
   vanishes at `x = ±1`, so iterated divided differences (`dslope`) factor
   `sin (π x / 2) - x = (x² - 1) g(x)` for a continuous `g : ℝ → ℝ`; hence `(S - F) π(a)` is
   compact, `sineReplacement` fixes already-normalized modules, and `t ↦ F + t (S - F)` is a
   norm-continuous path of Fredholm modules from `M` to `M.sineReplacement`.
2. **The doubling (`double`, `doubleHomotopy`).** For `S = √(1 - F²)`, the block operator
   `F' = [[F, S], [S, -F]]` (`ContinuousLinearMap.doublingOperator F`) on `H ⊕ H` is a self-adjoint
   involution when `‖F‖ ≤ 1`, and has trace zero in finite dimensions. Because `S π(a)` is compact,
   the linear path `t ↦ (F ⊕ -F) + t [[0, S], [S, 0]]` (`doubleHomotopy`) connects the orthogonal
   sum `M ⊕ (H, 0, -F)` at `t = 0` to `M.double` at `t = 1`. In the even case the grading is
   `γ ⊕ -γ`.

Composing the two gives `FredholmModule.normalize` and `EvenFredholmModule.normalize`, normalized
Fredholm modules (`IsNormalized`) over the same algebra on `H ⊕ H`.

## Main definitions

* `TauCeti.FredholmModule.sineReplacement`, `TauCeti.FredholmModule.sinePerturbation`,
  `TauCeti.FredholmModule.sineReplacementHomotopy`: the module with operator `sin (π F / 2)` and its
  linear operator homotopy from `M`.
* `TauCeti.FredholmModule.doubleRep`: the representation `π ⊕ 0` on `H ⊕ H`.
* `TauCeti.FredholmModule.double`, `TauCeti.FredholmModule.doubleHomotopy`: the doubled module on
  `H ⊕ H` and its linear operator homotopy from `M ⊕ (H, 0, -F)`.
* `TauCeti.FredholmModule.normalize`: the doubled sine replacement, satisfying `IsNormalized`.
* `TauCeti.EvenFredholmModule.sineReplacement`,
  `TauCeti.EvenFredholmModule.sineReplacementHomotopy`, `TauCeti.EvenFredholmModule.double`,
  `TauCeti.EvenFredholmModule.doubleHomotopy`, `TauCeti.EvenFredholmModule.normalize`: the even
  versions, with grading `γ ⊕ -γ` on `H ⊕ H`.

## Main results

* `TauCeti.FredholmModule.isCompactOperator_cfc_commutator`: `[f(F), π(a)]` is compact for every
  real function `f`.
* `TauCeti.FredholmModule.isCompactOperator_sinePerturbation_mul_rep`: `(sin (π F / 2) - F) π(a)` is
  compact.
* `TauCeti.FredholmModule.isCompactOperator_sqrt_mul_rep`: `√(1 - F²) π(a)` is compact.
* `TauCeti.FredholmModule.isNormalized_double`, `TauCeti.FredholmModule.isNormalized_normalize`,
  `TauCeti.FredholmModule.normalize_operator_mul_self`: the doubled and normalized modules have
  `F² = 1`.
* `TauCeti.FredholmModule.trace_double_operator_eq_zero`,
  `TauCeti.FredholmModule.trace_normalize_operator_eq_zero`: the doubled and normalized operators
  have trace zero.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press (1994), Chapter IV, §1, Proposition 2 and
  Appendix A.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.3
  (Lemma 8.3.8 for the doubling).
-/

public section

noncomputable section

open ContinuousLinearMap Real

namespace TauCeti

/-! ### Private divided-difference factorization of `sin (π x / 2) - x` -/

/-- Auxiliary continuous quotient `g(x)` satisfying `(x ^ 2 - 1) * g x = sin (π * x / 2) - x`,
constructed by two applications of `dslope` at `1` and `-1`. -/
private def sinSubIdQuotient : ℝ → ℝ :=
  dslope (dslope (fun x : ℝ ↦ sin (π * x / 2) - x) 1) (-1)

private theorem continuous_sinSubIdQuotient : Continuous sinSubIdQuotient := by
  let h₀ : ℝ → ℝ := fun x ↦ sin (π * x / 2) - x
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

private theorem sq_sub_one_mul_sinSubIdQuotient (x : ℝ) :
    (x ^ 2 - 1) * sinSubIdQuotient x = sin (π * x / 2) - x := by
  let h₀ : ℝ → ℝ := fun x ↦ sin (π * x / 2) - x
  have hh₀_one : h₀ 1 = 0 := by simp [h₀]
  have hh₀_neg_one : h₀ (-1) = 0 := by simp [h₀, neg_div]
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
    _ = sin (π * x / 2) - x := hh₁_eq x

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module ℂ A] [Star A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Odd Fredholm modules -/

namespace FredholmModule

variable (M : FredholmModule A H)

/-- The operator of a Fredholm module lies in the essential commutant of its representation. -/
theorem operator_mem_essentialCommutant :
    M.operator ∈ essentialCommutant (Set.range M.rep) :=
  mem_essentialCommutant.2 <| by
    rintro _ ⟨a, rfl⟩
    exact M.isCompactOperator_commutator a

/-- **Functions of `F` have compact commutators.** For every real function `f`, the commutator
`[f(F), π(a)]` of the continuous functional calculus of `F` with the representation is
compact. -/
theorem isCompactOperator_cfc_commutator (f : ℝ → ℝ) (a : A) :
    IsCompactOperator ⇑(cfc f M.operator * M.rep a - M.rep a * cfc f M.operator) :=
  mem_essentialCommutant.1 (cfc_mem_essentialCommutant
    (by rintro _ ⟨b, rfl⟩; exact ⟨star b, map_star M.rep b⟩) f M.operator_mem_essentialCommutant)
    _ ⟨a, rfl⟩

/-- The defect of the sine replacement: `sin (π F / 2)² - 1 = g(F) (F² - 1)` for a continuous
function `g`. -/
private theorem cfc_sin_mul_cfc_sin_sub_one :
    ∃ G : H →L[ℂ] H, cfc (fun x : ℝ => sin (π * x / 2)) M.operator *
      cfc (fun x : ℝ => sin (π * x / 2)) M.operator - 1 = G * (M.operator * M.operator - 1) := by
  have hF := M.isSelfAdjoint_operator
  set g : ℝ → ℝ := fun x => (π / 2) ^ 2 * sinc (π * (1 - x) / 2) * sinc (π * (1 + x) / 2)
  have hg : Continuous g := by
    have := continuous_sinc
    fun_prop
  have hs : Continuous fun x : ℝ => sin (π * x / 2) := by fun_prop
  refine ⟨cfc g M.operator, ?_⟩
  have e₁ : cfc (fun x : ℝ => sin (π * x / 2) * sin (π * x / 2) - 1) M.operator =
      cfc (fun x : ℝ => sin (π * x / 2)) M.operator *
        cfc (fun x : ℝ => sin (π * x / 2)) M.operator - 1 := by
    rw [cfc_sub (fun x : ℝ => sin (π * x / 2) * sin (π * x / 2)) (fun _ => 1) M.operator,
      cfc_mul _ _ M.operator hs.continuousOn hs.continuousOn, cfc_const_one ℝ M.operator]
  have e₂ : cfc (fun x => g x * (x * x - 1)) M.operator = cfc g M.operator *
      (M.operator * M.operator - 1) := by
    rw [cfc_mul g (fun x : ℝ => x * x - 1) M.operator hg.continuousOn,
      cfc_sub (fun x : ℝ => x * x) (fun _ => 1) M.operator,
      cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) M.operator, cfc_id' ℝ M.operator,
      cfc_const_one ℝ M.operator]
  rw [← e₁, ← e₂]
  exact cfc_congr fun x _ => mul_self_sin_pi_mul_div_two_sub_one x

/-- **The sine replacement** of a Fredholm module: the operator `F` is replaced by the
self-adjoint contraction `sin (π F / 2)` (`norm_sineReplacement_operator_le_one`), with the same
representation. -/
def sineReplacement : FredholmModule A H where
  rep := M.rep
  operator := cfc (fun x : ℝ => sin (π * x / 2)) M.operator
  isSelfAdjoint_operator := cfc_predicate _ _
  isCompactOperator_commutator := M.isCompactOperator_cfc_commutator _
  isCompactOperator_mul_self_sub_one_mul a := by
    obtain ⟨G, hG⟩ := M.cfc_sin_mul_cfc_sin_sub_one
    rw [hG, mul_assoc]
    exact (M.isCompactOperator_mul_self_sub_one_mul a).mul_left G

@[simp]
theorem sineReplacement_rep : M.sineReplacement.rep = M.rep :=
  (rfl)

@[simp]
theorem sineReplacement_operator :
    M.sineReplacement.operator = cfc (fun x : ℝ => sin (π * x / 2)) M.operator :=
  (rfl)

/-- The operator of the sine replacement is a contraction. -/
theorem norm_sineReplacement_operator_le_one : ‖M.sineReplacement.operator‖ ≤ 1 :=
  norm_cfc_le zero_le_one fun x _ => by simpa using abs_sin_le_one (π * x / 2)

/-- The self-adjoint perturbation `sin (π F / 2) - F` taking `M.operator` to
`M.sineReplacement.operator`. -/
def sinePerturbation : H →L[ℂ] H :=
  M.sineReplacement.operator - M.operator

theorem sinePerturbation_def : M.sinePerturbation = M.sineReplacement.operator - M.operator :=
  (rfl)

theorem isSelfAdjoint_sinePerturbation : IsSelfAdjoint M.sinePerturbation :=
  M.sineReplacement.isSelfAdjoint_operator.sub M.isSelfAdjoint_operator

/-- Divided-difference operator factorization `sin (π F / 2) - F = G * (F² - 1)`. -/
theorem exists_mul_mul_self_sub_one_eq_sinePerturbation :
    ∃ G : H →L[ℂ] H, M.sinePerturbation = G * (M.operator * M.operator - 1) := by
  have hF_sa : IsSelfAdjoint M.operator := M.isSelfAdjoint_operator
  have hcont : ContinuousOn sinSubIdQuotient (spectrum ℝ M.operator) :=
    continuous_sinSubIdQuotient.continuousOn
  refine ⟨cfc sinSubIdQuotient M.operator, ?_⟩
  have hsub : M.sinePerturbation = cfc (fun x : ℝ ↦ sin (π * x / 2) - x) M.operator := by
    rw [sinePerturbation_def, sineReplacement_operator,
      cfc_sub (fun x : ℝ ↦ sin (π * x / 2)) (fun x : ℝ ↦ x) M.operator (by fun_prop)
        continuousOn_id,
      cfc_id' ℝ M.operator hF_sa]
  have hsq : cfc (fun x : ℝ ↦ x * x - 1) M.operator = M.operator * M.operator - 1 := by
    rw [cfc_sub (fun x : ℝ ↦ x * x) (fun _ : ℝ ↦ (1 : ℝ)) M.operator (by fun_prop)
        continuousOn_const,
      cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x) M.operator continuousOn_id continuousOn_id,
      cfc_id' ℝ M.operator hF_sa, cfc_const_one ℝ M.operator]
  rw [hsub, ← hsq,
    ← cfc_mul sinSubIdQuotient (fun x : ℝ ↦ x * x - 1) M.operator hcont (by fun_prop)]
  refine cfc_congr fun x _ ↦ ?_
  have hq := sq_sub_one_mul_sinSubIdQuotient x
  linarith [sq x]

/-- **The sine replacement differs from `F` by a relatively compact perturbation.** -/
theorem isCompactOperator_sinePerturbation_mul_rep (a : A) :
    IsCompactOperator ⇑(M.sinePerturbation * M.rep a) := by
  obtain ⟨G, hG⟩ := M.exists_mul_mul_self_sub_one_eq_sinePerturbation
  rw [hG, mul_assoc]
  exact (M.isCompactOperator_mul_self_sub_one_mul a).mul_left G

private theorem isCompactOperator_smul_sinePerturbation_mul_rep (t : ℝ) (a : A) :
    IsCompactOperator ⇑(((t : ℂ) • M.sinePerturbation) * M.rep a) := by
  rw [smul_mul_assoc, FunLike.coe_smul]
  exact (M.isCompactOperator_sinePerturbation_mul_rep a).smul (t : ℂ)

/-- **Linear operator homotopy** `t ↦ F + t (sin (π F / 2) - F)` connecting `M` at `t = 0` to
`M.sineReplacement` at `t = 1` through relatively compact self-adjoint perturbations. -/
def sineReplacementHomotopy (t : ℝ) : FredholmModule A H :=
  M.perturb ((t : ℂ) • M.sinePerturbation)
    (IsSelfAdjoint.smul (Complex.conj_ofReal t) M.isSelfAdjoint_sinePerturbation)
    (M.isCompactOperator_smul_sinePerturbation_mul_rep t)

@[simp]
theorem sineReplacementHomotopy_rep (t : ℝ) : (M.sineReplacementHomotopy t).rep = M.rep := by
  simp [sineReplacementHomotopy]

@[simp]
theorem sineReplacementHomotopy_operator (t : ℝ) :
    (M.sineReplacementHomotopy t).operator = M.operator + (t : ℂ) • M.sinePerturbation := by
  simp [sineReplacementHomotopy]

@[simp]
theorem sineReplacementHomotopy_zero : M.sineReplacementHomotopy 0 = M := by
  ext1 <;> simp

@[simp]
theorem sineReplacementHomotopy_one : M.sineReplacementHomotopy 1 = M.sineReplacement := by
  ext1 <;> simp [sinePerturbation_def]

/-- The linear operator homotopy `t ↦ (M.sineReplacementHomotopy t).operator` is norm-continuous. -/
theorem continuous_sineReplacementHomotopy_operator :
    Continuous fun t : ℝ ↦ (M.sineReplacementHomotopy t).operator := by
  simp only [sineReplacementHomotopy_operator]
  fun_prop

variable {M} in
/-- Sine replacement fixes every already-normalized Fredholm module. -/
theorem sineReplacement_eq_self_of_isNormalized (hM : M.IsNormalized) :
    M.sineReplacement = M := by
  obtain ⟨G, hG⟩ := M.exists_mul_mul_self_sub_one_eq_sinePerturbation
  have h0 : M.sinePerturbation = 0 := by
    rw [hG, hM.operator_mul_operator, sub_self, mul_zero]
  ext1
  · rfl
  · exact sub_eq_zero.mp h0

/-- **The off-diagonal blocks of the doubling are compact after multiplication by `π(a)`.**
`√(1 - F²) π(a)` is compact (with `CFC.sqrt` returning `0` when `1 - F²` is not positive). -/
theorem isCompactOperator_sqrt_mul_rep (a : A) :
    IsCompactOperator ⇑(CFC.sqrt (1 - M.operator * M.operator) * M.rep a) := by
  by_cases hnn : 0 ≤ 1 - M.operator * M.operator
  swap
  · rw [CFC.sqrt_of_not_nonneg hnn, zero_mul]
    exact isCompactOperator_zero
  set S := CFC.sqrt (1 - M.operator * M.operator)
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hSS : S * S = 1 - M.operator * M.operator := CFC.sqrt_mul_sqrt_self _ hnn
  refine isCompactOperator_star_mul_self_iff.mp ?_
  have h : star (S * M.rep a) * (S * M.rep a) =
      -(M.rep (star a) * ((M.operator * M.operator - 1) * M.rep a)) := by
    rw [star_mul, hS.star_eq, ← map_star, ← sub_sub_cancel 1 (M.operator * M.operator), ← hSS]
    noncomm_ring
  rw [h, FunLike.coe_neg]
  exact ((M.isCompactOperator_mul_self_sub_one_mul a).mul_left _).neg

/-- Mirror image of `isCompactOperator_sqrt_mul_rep`: `π(a) √(1 - F²)` is compact. -/
theorem isCompactOperator_rep_mul_sqrt (a : A) :
    IsCompactOperator ⇑(M.rep a * CFC.sqrt (1 - M.operator * M.operator)) := by
  have hS : IsSelfAdjoint (CFC.sqrt (1 - M.operator * M.operator)) :=
    (CFC.sqrt_nonneg _).isSelfAdjoint
  simpa only [star_mul, hS.star_eq, map_star, star_star] using
    (M.isCompactOperator_sqrt_mul_rep (star a)).star

/-- Multiplying `(√(1 - F²)).hermitianDilation` against `(π ⊕ 0)(a)` gives a compact operator,
hence any real multiple is compact relative to `M.prod (zeroRep A (-F) _)`. -/
theorem isCompactOperator_hermitianDilation_sqrt_mul_prod_zeroRep_rep (t : ℝ) (a : A) :
    IsCompactOperator ⇑(((t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation) *
      (M.prod (zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg)).rep a) := by
  rw [prod_rep_apply, zeroRep_rep_apply, smul_mul_assoc, FunLike.coe_smul]
  exact ((isCompactOperator_hermitianDilation_comp_withLpProdMap_zero_right _ _).mpr
    (M.isCompactOperator_sqrt_mul_rep a)).smul (t : ℂ)

/-- The commutator of the doubling operator with `π(a) ⊕ 0` is compact: it is the block operator
`[[[F, π(a)], -π(a) S], [S π(a), 0]]` with `S = √(1 - F²)`. -/
private theorem isCompactOperator_doublingOperator_commutator (a : A) :
    IsCompactOperator ⇑(doublingOperator M.operator * (M.rep a).withLpProdMap 2 (0 : H →L[ℂ] H) -
      (M.rep a).withLpProdMap 2 (0 : H →L[ℂ] H) * doublingOperator M.operator) := by
  have h : doublingOperator M.operator * (M.rep a).withLpProdMap 2 0 -
      (M.rep a).withLpProdMap 2 0 * doublingOperator M.operator =
        WithLp.blockL2 (M.operator * M.rep a - M.rep a * M.operator)
          (-(M.rep a * CFC.sqrt (1 - M.operator * M.operator)))
          (CFC.sqrt (1 - M.operator * M.operator) * M.rep a) 0 := by
    rw [doublingOperator_def, ← WithLp.blockL2_zero_zero, WithLp.blockL2_mul_blockL2,
      WithLp.blockL2_mul_blockL2, WithLp.blockL2_sub_blockL2]
    simp [← mul_def]
  rw [h]
  exact WithLp.isCompactOperator_blockL2 (M.isCompactOperator_commutator a)
    (M.isCompactOperator_rep_mul_sqrt a).neg (M.isCompactOperator_sqrt_mul_rep a)
    isCompactOperator_zero

/-- The representation `π ⊕ 0` of `A` on `H ⊕ H`, the representation of the doubled module
`FredholmModule.double`. -/
def doubleRep : A →⋆ₙₐ[ℂ] WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H) :=
  (withLpProdMapStarAlgHom.toNonUnitalStarAlgHom.comp
    ((NonUnitalStarAlgHom.id ℂ (H →L[ℂ] H)).prod 0)).comp M.rep

@[simp]
theorem doubleRep_apply (a : A) : M.doubleRep a = (M.rep a).withLpProdMap 2 0 := by
  simp [doubleRep]

/-- **Linear operator homotopy** `t ↦ (F ⊕ -F) + t [[0, √(1 - F²)], [√(1 - F²), 0]]` connecting
`M.prod (zeroRep A (-F) _)` at `t = 0` to `M.double hF₁` at `t = 1`. -/
def doubleHomotopy (t : ℝ) : FredholmModule A (WithLp 2 (H × H)) :=
  (M.prod (zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg)).perturb
    ((t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation)
    (IsSelfAdjoint.smul (Complex.conj_ofReal t)
      (CFC.sqrt (1 - M.operator * M.operator)).isSelfAdjoint_hermitianDilation)
    (M.isCompactOperator_hermitianDilation_sqrt_mul_prod_zeroRep_rep t)

@[simp]
theorem doubleHomotopy_rep_apply (t : ℝ) (a : A) :
    (M.doubleHomotopy t).rep a = (M.rep a).withLpProdMap 2 0 := by
  simp [doubleHomotopy]

@[simp]
theorem doubleHomotopy_operator (t : ℝ) :
    (M.doubleHomotopy t).operator =
      M.operator.withLpProdMap 2 (-M.operator) +
        (t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation := by
  simp [doubleHomotopy]

@[simp]
theorem doubleHomotopy_zero :
    M.doubleHomotopy 0 = M.prod (zeroRep A (-M.operator) M.isSelfAdjoint_operator.neg) := by
  ext1
  · ext1 a
    simp
  · simp

/-- The doubling operator homotopy `t ↦ (M.doubleHomotopy t).operator` is norm-continuous. -/
theorem continuous_doubleHomotopy_operator :
    Continuous fun t : ℝ ↦ (M.doubleHomotopy t).operator := by
  simp only [doubleHomotopy_operator]
  fun_prop

section Double

variable {M}

/-- **The doubling** of a Fredholm module whose operator `F` is a contraction: the Fredholm module
on `H ⊕ H` with representation `π ⊕ 0` and operator
`[[F, √(1 - F²)], [√(1 - F²), -F]]`, which squares to `1`
(`ContinuousLinearMap.doublingOperator_mul_self`). -/
def double (M : FredholmModule A H) (hF₁ : ‖M.operator‖ ≤ 1) :
    FredholmModule A (WithLp 2 (H × H)) where
  rep := M.doubleRep
  operator := doublingOperator M.operator
  isSelfAdjoint_operator := isSelfAdjoint_doublingOperator M.isSelfAdjoint_operator
  isCompactOperator_commutator a := by
    rw [doubleRep_apply]
    exact M.isCompactOperator_doublingOperator_commutator a
  isCompactOperator_mul_self_sub_one_mul a := by
    rw [doublingOperator_mul_self M.isSelfAdjoint_operator hF₁, sub_self, zero_mul]
    exact isCompactOperator_zero

@[simp]
theorem double_rep_apply (hF₁ : ‖M.operator‖ ≤ 1) (a : A) :
    (M.double hF₁).rep a = (M.rep a).withLpProdMap 2 0 :=
  M.doubleRep_apply a

@[simp]
theorem double_operator (hF₁ : ‖M.operator‖ ≤ 1) :
    (M.double hF₁).operator = doublingOperator M.operator :=
  (rfl)

@[simp]
theorem doubleHomotopy_one (hF₁ : ‖M.operator‖ ≤ 1) : M.doubleHomotopy 1 = M.double hF₁ := by
  ext1
  · ext1 a
    simp
  · simp [doublingOperator_eq_withLpProdMap_add_hermitianDilation]

/-- Doubling a contraction Fredholm module produces a normalized (`F² = 1`) module. -/
theorem isNormalized_double (hF₁ : ‖M.operator‖ ≤ 1) : (M.double hF₁).IsNormalized :=
  isNormalized_iff.mpr (doublingOperator_mul_self M.isSelfAdjoint_operator hF₁)

/-- The doubled operator on `WithLp 2 (H × H)` has `LinearMap.trace` equal to zero. -/
theorem trace_double_operator_eq_zero (hF₁ : ‖M.operator‖ ≤ 1) :
    LinearMap.trace ℂ (WithLp 2 (H × H)) (M.double hF₁).operator.toLinearMap = 0 :=
  trace_doublingOperator_eq_zero M.operator

end Double

/-- **The normalization** of a Fredholm module: the doubling of its sine replacement, a Fredholm
module on `H ⊕ H` with representation `π ⊕ 0` whose operator squares to `1`
(`normalize_operator_mul_self`). -/
def normalize : FredholmModule A (WithLp 2 (H × H)) :=
  M.sineReplacement.double M.norm_sineReplacement_operator_le_one

theorem normalize_def :
    M.normalize = M.sineReplacement.double M.norm_sineReplacement_operator_le_one :=
  (rfl)

@[simp]
theorem normalize_rep_apply (a : A) : M.normalize.rep a = (M.rep a).withLpProdMap 2 0 :=
  M.sineReplacement.double_rep_apply _ a

@[simp]
theorem normalize_operator :
    M.normalize.operator = doublingOperator (cfc (fun x : ℝ => sin (π * x / 2)) M.operator) :=
  (rfl)

/-- The operator of the normalized module is an involution: `F² = 1`. -/
theorem normalize_operator_mul_self : M.normalize.operator * M.normalize.operator = 1 :=
  doublingOperator_mul_self M.sineReplacement.isSelfAdjoint_operator
    M.norm_sineReplacement_operator_le_one

/-- Two-step normalization produces a normalized (`F² = 1`) odd Fredholm module. -/
theorem isNormalized_normalize : M.normalize.IsNormalized :=
  isNormalized_iff.mpr M.normalize_operator_mul_self

/-- The normalized operator on `WithLp 2 (H × H)` has `LinearMap.trace` equal to zero. -/
theorem trace_normalize_operator_eq_zero :
    LinearMap.trace ℂ (WithLp 2 (H × H)) M.normalize.operator.toLinearMap = 0 :=
  trace_doublingOperator_eq_zero _

end FredholmModule

/-! ### Even Fredholm modules -/

namespace EvenFredholmModule

variable (M : EvenFredholmModule A H)

/-- **The sine replacement**, even version: the grading anticommutes with `sin (π F / 2)`, since
the sine is odd. -/
def sineReplacement : EvenFredholmModule A H where
  toFredholmModule := M.toFredholmModule.sineReplacement
  grading := M.grading
  isSelfAdjoint_grading := M.isSelfAdjoint_grading
  grading_mul_grading := M.grading_mul_grading
  commute_grading_rep := M.commute_grading_rep
  grading_mul_operator := mul_cfc_eq_neg_cfc_mul_of_odd M.grading_mul_operator fun x ↦ by
    rw [mul_neg, neg_div, sin_neg]

@[simp]
theorem sineReplacement_toFredholmModule :
    M.sineReplacement.toFredholmModule = M.toFredholmModule.sineReplacement :=
  (rfl)

@[simp]
theorem sineReplacement_grading : M.sineReplacement.grading = M.grading :=
  (rfl)

theorem grading_mul_sinePerturbation :
    M.grading * M.toFredholmModule.sinePerturbation =
      -(M.toFredholmModule.sinePerturbation * M.grading) := by
  have hsin : M.grading * M.toFredholmModule.sineReplacement.operator =
      -(M.toFredholmModule.sineReplacement.operator * M.grading) :=
    M.sineReplacement.grading_mul_operator
  rw [FredholmModule.sinePerturbation_def, mul_sub, sub_mul, hsin, M.grading_mul_operator,
    neg_sub_neg, neg_sub]

/-- **Linear operator homotopy** of even Fredholm modules from `M` at `t = 0` to
`M.sineReplacement` at `t = 1`. -/
def sineReplacementHomotopy (t : ℝ) : EvenFredholmModule A H :=
  M.perturb ((t : ℂ) • M.toFredholmModule.sinePerturbation)
    (IsSelfAdjoint.smul (Complex.conj_ofReal t) M.toFredholmModule.isSelfAdjoint_sinePerturbation)
    (M.toFredholmModule.isCompactOperator_smul_sinePerturbation_mul_rep t)
    (by rw [mul_smul_comm, smul_mul_assoc, M.grading_mul_sinePerturbation, smul_neg])

@[simp]
theorem sineReplacementHomotopy_toFredholmModule (t : ℝ) :
    (M.sineReplacementHomotopy t).toFredholmModule =
      M.toFredholmModule.sineReplacementHomotopy t := by
  simp [sineReplacementHomotopy, FredholmModule.sineReplacementHomotopy]

@[simp]
theorem sineReplacementHomotopy_grading (t : ℝ) :
    (M.sineReplacementHomotopy t).grading = M.grading := by
  simp [sineReplacementHomotopy]

@[simp]
theorem sineReplacementHomotopy_zero : M.sineReplacementHomotopy 0 = M := by
  ext1 <;> simp

@[simp]
theorem sineReplacementHomotopy_one : M.sineReplacementHomotopy 1 = M.sineReplacement := by
  ext1 <;> simp

variable {M} in
/-- Sine replacement fixes every already-normalized even Fredholm module. -/
theorem sineReplacement_eq_self_of_isNormalized (hM : M.IsNormalized) :
    M.sineReplacement = M := by
  ext1
  · exact congrArg FredholmModule.rep (FredholmModule.sineReplacement_eq_self_of_isNormalized hM)
  · exact congrArg FredholmModule.operator
      (FredholmModule.sineReplacement_eq_self_of_isNormalized hM)
  · rfl

/-- Because `γ` anticommutes with `F`, it commutes with `F²` and hence with `√(1 - F²)`. -/
theorem commute_grading_sqrt_one_sub :
    Commute M.grading (CFC.sqrt (1 - M.operator * M.operator)) :=
  ((Commute.mul_self_of_mul_eq_neg_mul M.grading_mul_operator).symm.cfcSqrt_one_sub).symm

/-- **Linear operator homotopy** of even Fredholm modules connecting `M.prod M.negZeroRep` at
`t = 0` to `M.double hF₁` at `t = 1`. -/
def doubleHomotopy (t : ℝ) : EvenFredholmModule A (WithLp 2 (H × H)) :=
  (M.prod M.negZeroRep).perturb
    ((t : ℂ) • (CFC.sqrt (1 - M.operator * M.operator)).hermitianDilation)
    (IsSelfAdjoint.smul (Complex.conj_ofReal t)
      (CFC.sqrt (1 - M.operator * M.operator)).isSelfAdjoint_hermitianDilation)
    (by
      rw [prod_toFredholmModule, negZeroRep_toFredholmModule]
      exact M.toFredholmModule.isCompactOperator_hermitianDilation_sqrt_mul_prod_zeroRep_rep t)
    (by
      rw [prod_grading, negZeroRep_grading, mul_smul_comm, smul_mul_assoc,
        withLpProdMap_neg_mul_hermitianDilation_eq_neg
          (CFC.sqrt_nonneg _).isSelfAdjoint M.commute_grading_sqrt_one_sub,
        smul_neg])

@[simp]
theorem doubleHomotopy_toFredholmModule (t : ℝ) :
    (M.doubleHomotopy t).toFredholmModule = M.toFredholmModule.doubleHomotopy t := by
  simp [doubleHomotopy, FredholmModule.doubleHomotopy]

@[simp]
theorem doubleHomotopy_grading (t : ℝ) :
    (M.doubleHomotopy t).grading = M.grading.withLpProdMap 2 (-M.grading) := by
  simp [doubleHomotopy]

@[simp]
theorem doubleHomotopy_zero : M.doubleHomotopy 0 = M.prod M.negZeroRep := by
  ext1 <;> simp

/-- **The doubling**, even version: the grading of the doubled module is `γ ⊕ -γ`, which
anticommutes with `[[F, √(1 - F²)], [√(1 - F²), -F]]` because `γ` anticommutes with `F` and
commutes with `√(1 - F²)`. -/
def double (hF₁ : ‖M.operator‖ ≤ 1) : EvenFredholmModule A (WithLp 2 (H × H)) where
  toFredholmModule := M.toFredholmModule.double hF₁
  grading := M.grading.withLpProdMap 2 (-M.grading)
  isSelfAdjoint_grading := (isSelfAdjoint_withLpProdMap_iff _ _).2
    ⟨M.isSelfAdjoint_grading, M.isSelfAdjoint_grading.neg⟩
  grading_mul_grading := by
    rw [← withLpProdMap_mul, neg_mul_neg, M.grading_mul_grading, withLpProdMap_one]
  commute_grading_rep a := by
    rw [Commute, SemiconjBy, FredholmModule.double_rep_apply, ← withLpProdMap_mul,
      ← withLpProdMap_mul, (M.commute_grading_rep a).eq, mul_zero, zero_mul]
  grading_mul_operator := by
    rw [FredholmModule.double_operator, doublingOperator_def, ← WithLp.blockL2_zero_zero,
      WithLp.blockL2_mul_blockL2, WithLp.blockL2_mul_blockL2, WithLp.neg_blockL2]
    simp [← mul_def, M.grading_mul_operator, M.commute_grading_sqrt_one_sub.eq]

@[simp]
theorem double_toFredholmModule (hF₁ : ‖M.operator‖ ≤ 1) :
    (M.double hF₁).toFredholmModule = M.toFredholmModule.double hF₁ :=
  (rfl)

@[simp]
theorem double_grading (hF₁ : ‖M.operator‖ ≤ 1) :
    (M.double hF₁).grading = M.grading.withLpProdMap 2 (-M.grading) :=
  (rfl)

variable {M} in
@[simp]
theorem doubleHomotopy_one (hF₁ : ‖M.operator‖ ≤ 1) :
    M.doubleHomotopy 1 = M.double hF₁ := by
  ext1
  · ext1 a
    simp
  · simp [doublingOperator_eq_withLpProdMap_add_hermitianDilation]
  · simp

variable {M} in
/-- Doubling a contraction even Fredholm module produces a normalized (`F² = 1`) even module. -/
theorem isNormalized_double (hF₁ : ‖M.operator‖ ≤ 1) :
    (M.double hF₁).IsNormalized :=
  M.toFredholmModule.isNormalized_double hF₁

/-- **The normalization**, even version: the doubling of the sine replacement, with grading
`γ ⊕ -γ` and an operator that squares to `1`. -/
def normalize : EvenFredholmModule A (WithLp 2 (H × H)) :=
  M.sineReplacement.double M.toFredholmModule.norm_sineReplacement_operator_le_one

@[simp]
theorem normalize_toFredholmModule :
    M.normalize.toFredholmModule = M.toFredholmModule.normalize :=
  (rfl)

@[simp]
theorem normalize_grading :
    M.normalize.grading = M.grading.withLpProdMap 2 (-M.grading) :=
  (rfl)

/-- Two-step normalization produces a normalized (`F² = 1`) even Fredholm module. -/
theorem isNormalized_normalize : M.normalize.IsNormalized :=
  M.toFredholmModule.isNormalized_normalize

end EvenFredholmModule

end TauCeti
