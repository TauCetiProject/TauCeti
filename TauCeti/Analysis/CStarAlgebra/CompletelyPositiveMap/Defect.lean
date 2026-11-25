/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Stinespring.Basic
public import TauCeti.Analysis.CStarAlgebra.Matrix.EuclideanCLM
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
import TauCeti.Analysis.CStarAlgebra.Matrix.HilbertSchmidt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Multiplicativity defects of completely positive contractions into matrices

For a completely positive contraction (c.p.c.) `φ : A → M_k` from a possibly nonunital
C⋆-algebra, the *2-norm defect* and the *norm defect* at `a` are
`d₂(φ, a) = Re tr_k(φ(a⋆a) - φ(a)⋆φ(a))` (`CompletelyPositiveMap.twoNormDefect`) and
`d_∞(φ, a) = ‖φ(a⋆a) - φ(a)⋆φ(a)‖` (`CompletelyPositiveMap.normDefect`). The matrix
`φ(a⋆a) - φ(a)⋆φ(a)` is positive by the Kadison–Schwarz inequality for c.p.c. maps,
`CompletelyPositiveMap.star_map_mul_map_le_of_norm_map_le` (from the operator version
`CompletelyPositiveMap.star_map_mul_map_le_of_opNorm_le_one`), so both defects are nonnegative and
`d₂ ≤ d_∞`.

The estimates come from a Stinespring dilation. Identify `M_k` with the operators on
`ℂᵏ = EuclideanSpace ℂ n` through `CStarMatrix.toEuclideanCLM`, and dilate `φ = V⋆π(·)V` with
`‖V‖ ≤ 1`. With `S = (1 - VV⋆)^{1/2}`, the *defect operator* `T(a) = Sπ(a)V` satisfies
`φ(a⋆b) - φ(a)⋆φ(b) = T(a)⋆T(b)`, so `d_∞(φ, a) = ‖T(a)‖²` and `d₂(φ, a)` is the squared
normalized Hilbert–Schmidt norm `k⁻¹ ‖T(a)‖²_HS` of `T(a)`
(`ContinuousLinearMap.hilbertSchmidtNorm`). Since `T` is linear, `‖T(a)‖ ≤ ‖a‖`, and
`T(ab) = T(a)φ(b) + Sπ(a)S T(b)`, this gives:

* the product estimates `‖φ(ab) - φ(a)φ(b)‖ ≤ ‖a‖ d_∞(φ, b)^{1/2}` and
  `‖φ(ab) - φ(a)φ(b)‖ ≤ d_∞(φ, a⋆)^{1/2} ‖b‖` (`CompletelyPositiveMap.norm_map_mul_sub_le` and
  its `'` version), and `‖φ(ab) - φ(a)φ(b)‖₂ ≤ ‖a‖ d₂(φ, b)^{1/2}` and
  `‖φ(ab) - φ(a)φ(b)‖₂ ≤ d₂(φ, a⋆)^{1/2} ‖b‖`
  (`CompletelyPositiveMap.normalizedTwoNorm_map_mul_sub_le` and its `'` version);
* for `d = d₂` and for `d = d_∞`, subadditivity
  `d(φ, a + b)^{1/2} ≤ d(φ, a)^{1/2} + d(φ, b)^{1/2}`, the product rule
  `d(φ, ab)^{1/2} ≤ ‖b‖ d(φ, a)^{1/2} + ‖a‖ d(φ, b)^{1/2}` and the Lipschitz bound
  `|d(φ, a)^{1/2} - d(φ, b)^{1/2}| ≤ ‖a - b‖`.

Finally `d₂(φ, a) ≤ ‖φ(a⋆a) - φ(a⋆)φ(a)‖₂`, star homomorphisms have zero defects, and both
defects are homogeneous of degree two, `d(φ, c • a) = |c|² d(φ, a)`
(`CompletelyPositiveMap.normDefect_smul`, `CompletelyPositiveMap.twoNormDefect_smul`).

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), Lemma 3.1.5 and the proof of Theorem 3.1.6.
-/

public section

noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace CompletelyPositiveMap

open CStarMatrix
open ContinuousLinearMap (hilbertSchmidtNorm_add_le_of_finiteDimensional
  hilbertSchmidtNorm_comp_le_left_of_finiteDimensional
  hilbertSchmidtNorm_comp_le_right_of_finiteDimensional)

variable {n : Type*} [Fintype n]

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **norm defect** `d_∞(φ, a) = ‖φ(a⋆a) - φ(a)⋆φ(a)‖` of a completely positive map into
matrices. -/
def normDefect (φ : A →CP CStarMatrix n n ℂ) (a : A) : ℝ :=
  ‖φ (star a * a) - star (φ a) * φ a‖

/-- Unfolding lemma for `normDefect`. -/
theorem normDefect_def (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.normDefect a = ‖φ (star a * a) - star (φ a) * φ a‖ :=
  (rfl)

/-- The **2-norm defect** `d₂(φ, a) = Re tr_k(φ(a⋆a) - φ(a)⋆φ(a))` of a completely positive map
into matrices. -/
def twoNormDefect (φ : A →CP CStarMatrix n n ℂ) (a : A) : ℝ :=
  (normalizedTrace (φ (star a * a) - star (φ a) * φ a)).re

/-- Unfolding lemma for `twoNormDefect`. -/
theorem twoNormDefect_def (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.twoNormDefect a = (normalizedTrace (φ (star a * a) - star (φ a) * φ a)).re :=
  (rfl)

/-- The norm defect is nonnegative. -/
theorem normDefect_nonneg (φ : A →CP CStarMatrix n n ℂ) (a : A) : 0 ≤ φ.normDefect a :=
  norm_nonneg _

/-- `d₂(φ, a) ≤ d_∞(φ, a)`, as `|tr_k(x)| ≤ ‖x‖`. -/
theorem twoNormDefect_le_normDefect (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.twoNormDefect a ≤ φ.normDefect a :=
  (Complex.re_le_norm _).trans (norm_normalizedTrace_le_norm _)

/-- `d_∞(φ, a) = ‖φ(a⋆a) - φ(a⋆)φ(a)‖`, as `φ` preserves the star. -/
theorem normDefect_eq_norm_map_star (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.normDefect a = ‖φ (star a * a) - φ (star a) * φ a‖ := by
  rw [normDefect_def, φ.map_star]

/-- `d₂(φ, a) ≤ ‖φ(a⋆a) - φ(a⋆)φ(a)‖₂`, as `|tr_k(x)| ≤ ‖x‖₂`. -/
theorem twoNormDefect_le_normalizedTwoNorm (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.twoNormDefect a ≤ normalizedTwoNorm (φ (star a * a) - φ (star a) * φ a) := by
  rw [φ.map_star]
  exact (Complex.re_le_norm _).trans (norm_normalizedTrace_le_normalizedTwoNorm _)

/-- Star homomorphisms have zero norm defect. -/
@[simp]
theorem normDefect_toCompletelyPositiveLinearMap (ρ : A →⋆ₙₐ[ℂ] CStarMatrix n n ℂ) (a : A) :
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ρ).normDefect a = 0 := by
  simp [normDefect_def, map_star ρ]

/-- Star homomorphisms have zero 2-norm defect. -/
@[simp]
theorem twoNormDefect_toCompletelyPositiveLinearMap (ρ : A →⋆ₙₐ[ℂ] CStarMatrix n n ℂ) (a : A) :
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ρ).twoNormDefect a = 0 := by
  simp [twoNormDefect_def, map_star ρ]

section Homogeneity

variable (φ : A →CP CStarMatrix n n ℂ)

private theorem map_star_smul_mul_smul_sub (c : ℂ) (a : A) :
    φ (star (c • a) * (c • a)) - star (φ (c • a)) * φ (c • a) =
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (φ (star a * a) - star (φ a) * φ a) := by
  simp [smul_mul_smul_comm, smul_sub, Complex.conj_mul']

/-- The norm defect is homogeneous of degree two: `d_∞(φ, c • a) = |c|² d_∞(φ, a)`. -/
theorem normDefect_smul (c : ℂ) (a : A) : φ.normDefect (c • a) = ‖c‖ ^ 2 * φ.normDefect a := by
  rw [normDefect_def, map_star_smul_mul_smul_sub, norm_smul]
  simp [normDefect_def]

/-- The 2-norm defect is homogeneous of degree two: `d₂(φ, c • a) = |c|² d₂(φ, a)`. -/
theorem twoNormDefect_smul (c : ℂ) (a : A) :
    φ.twoNormDefect (c • a) = ‖c‖ ^ 2 * φ.twoNormDefect a := by
  rw [twoNormDefect_def, map_star_smul_mul_smul_sub, normalizedTrace_smul, Complex.re_ofReal_mul,
    twoNormDefect_def]

end Homogeneity

section Dilation

variable [DecidableEq n] (φ : A →CP CStarMatrix n n ℂ)

/-- `φ` as a completely positive map into the operators on `ℂᵏ`. -/
private def toOp : A →CP (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (toEuclideanCLM (n := n))).comp φ

private theorem toOp_apply (a : A) : toOp φ a = toEuclideanCLM (φ a) := by
  simp [toOp]

/-- The operator `1 - VV⋆` on the Stinespring space. -/
private def defectProj : (toOp φ).Stinespring →L[ℂ] (toOp φ).Stinespring :=
  1 - (toOp φ).stinespringOp ∘L (toOp φ).stinespringOp.adjoint

/-- The operator `S = (1 - VV⋆)^{1/2}` on the Stinespring space. -/
private def defectSqrt : (toOp φ).Stinespring →L[ℂ] (toOp φ).Stinespring :=
  CFC.sqrt (defectProj φ)

/-- The defect operator `T(a) = Sπ(a)V`. -/
private def defectOp : A →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] (toOp φ).Stinespring) where
  toFun a := defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L (toOp φ).stinespringOp
  map_add' a b := by simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c a := by simp [ContinuousLinearMap.smul_comp]

private theorem defectOp_apply (a : A) :
    defectOp φ a = defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L (toOp φ).stinespringOp :=
  (rfl)

private theorem adjoint_defectSqrt : (defectSqrt φ).adjoint = defectSqrt φ := by
  rw [defectSqrt]
  exact (CFC.sqrt_nonneg (defectProj φ)).isSelfAdjoint.adjoint_eq

private theorem stinespring_eq' (c : A) :
    toEuclideanCLM (φ c) =
      (toOp φ).stinespringOp.adjoint ∘L (toOp φ).stinespringHom c ∘L (toOp φ).stinespringOp := by
  rw [← toOp_apply]
  exact ((toOp φ).stinespring_eq c).symm

variable {φ} (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
include hφ

private theorem norm_toContinuousLinearMap_toOp_le : ‖(toOp φ).toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [one_mul, toContinuousLinearMap_apply, toOp_apply, norm_toEuclideanCLM]
    exact hφ a

private theorem norm_stinespringOp_toOp_le : ‖(toOp φ).stinespringOp‖ ≤ 1 := by
  have h1 := norm_toContinuousLinearMap_toOp_le hφ
  have h2 := (toOp φ).norm_stinespringOp_sq
  nlinarith [norm_nonneg (toOp φ).stinespringOp]

private theorem defectProj_nonneg : 0 ≤ defectProj φ := by
  set V := (toOp φ).stinespringOp
  have hpos : 0 ≤ V ∘L V.adjoint :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr V.isPositive_self_comp_adjoint
  have hnorm : ‖V ∘L V.adjoint‖ ≤ 1 := by
    have h := ContinuousLinearMap.norm_adjoint_comp_self V.adjoint
    rw [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint.norm_map] at h
    rw [h]
    have := norm_stinespringOp_toOp_le hφ
    nlinarith [norm_nonneg V]
  rw [defectProj, sub_nonneg]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hnorm

/-- `SS = 1 - VV⋆`. -/
private theorem defectSqrt_comp_self : defectSqrt φ ∘L defectSqrt φ = defectProj φ := by
  rw [← ContinuousLinearMap.mul_def, defectSqrt]
  exact CFC.sqrt_mul_sqrt_self _ (defectProj_nonneg hφ)

/-- `S⋆S = 1 - VV⋆`. -/
private theorem adjoint_defectSqrt_comp_self :
    (defectSqrt φ).adjoint ∘L defectSqrt φ = defectProj φ := by
  rw [adjoint_defectSqrt, defectSqrt_comp_self hφ]

/-- `‖S‖ ≤ 1`. -/
private theorem norm_defectSqrt_le : ‖defectSqrt φ‖ ≤ 1 := by
  have hP : ‖defectProj φ‖ ≤ 1 := by
    rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ (defectProj_nonneg hφ), defectProj,
      sub_le_self_iff, ContinuousLinearMap.nonneg_iff_isPositive]
    exact (toOp φ).stinespringOp.isPositive_self_comp_adjoint
  have h := ContinuousLinearMap.norm_adjoint_comp_self (defectSqrt φ)
  rw [adjoint_defectSqrt_comp_self hφ] at h
  nlinarith [norm_nonneg (defectSqrt φ)]

omit hφ in
/-- `‖Sπ(a)X‖ ≤ ‖a‖` for operators `S` and `X` of norm at most `1`. -/
private theorem norm_comp_stinespringHom_comp_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {S : (toOp φ).Stinespring →L[ℂ] (toOp φ).Stinespring}
    {X : E →L[ℂ] (toOp φ).Stinespring} (hS : ‖S‖ ≤ 1) (hX : ‖X‖ ≤ 1) (a : A) :
    ‖S ∘L (toOp φ).stinespringHom a ∘L X‖ ≤ ‖a‖ := by
  calc _ ≤ ‖S‖ * (‖(toOp φ).stinespringHom a‖ * ‖X‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖a‖ * 1) := by
        gcongr
        exact NonUnitalStarAlgHom.norm_apply_le _ a
    _ = ‖a‖ := by ring

private theorem norm_defectSqrt_comp_le (a : A) :
    ‖defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L defectSqrt φ‖ ≤ ‖a‖ :=
  norm_comp_stinespringHom_comp_le (norm_defectSqrt_le hφ) (norm_defectSqrt_le hφ) a

private theorem norm_defectOp_le (a : A) : ‖defectOp φ a‖ ≤ ‖a‖ :=
  norm_comp_stinespringHom_comp_le (norm_defectSqrt_le hφ) (norm_stinespringOp_toOp_le hφ) a

/-- The defect identity `φ(a⋆b) - φ(a)⋆φ(b) = T(a)⋆T(b)`. -/
private theorem toEuclideanCLM_map_star_mul_sub (a b : A) :
    toEuclideanCLM (φ (star a * b) - star (φ a) * φ b) =
      (defectOp φ a).adjoint ∘L defectOp φ b := by
  -- The rewrites below produce the unabbreviated `(toOp φ).stinespringOp` and
  -- `(toOp φ).stinespringHom`; `hV` and `hπ` unfold `V` and `π` to match them.
  set V := (toOp φ).stinespringOp with hV
  set π := (toOp φ).stinespringHom with hπ
  calc toEuclideanCLM (φ (star a * b) - star (φ a) * φ b)
      = V.adjoint ∘L π (star a) ∘L π b ∘L V -
          (V.adjoint ∘L π (star a) ∘L V) ∘L (V.adjoint ∘L π b ∘L V) := by
        rw [← φ.map_star, map_sub, map_mul toEuclideanCLM, stinespring_eq', stinespring_eq',
          stinespring_eq', map_mul π, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
        simp only [ContinuousLinearMap.comp_assoc]
        simp only [hV, hπ]
    _ = V.adjoint ∘L (π a).adjoint ∘L ((defectSqrt φ).adjoint ∘L defectSqrt φ) ∘L π b ∘L V := by
        rw [adjoint_defectSqrt_comp_self hφ, defectProj, map_star,
          ContinuousLinearMap.star_eq_adjoint]
        simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc]
        simp only [hV, hπ]
    _ = (defectOp φ a).adjoint ∘L defectOp φ b := by
        simp only [defectOp_apply, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
        simp only [hV, hπ]

private theorem map_star_mul_sub_eq (a b : A) :
    φ (star a * b) - star (φ a) * φ b =
      toEuclideanCLM.symm ((defectOp φ a).adjoint ∘L defectOp φ b) := by
  rw [← toEuclideanCLM_map_star_mul_sub hφ, StarAlgEquiv.symm_apply_apply]

/-- The product rule for the defect operator: `T(ab) = T(a)φ(b) + Sπ(a)S T(b)`. -/
private theorem defectOp_mul (a b : A) :
    defectOp φ (a * b) = defectOp φ a ∘L toEuclideanCLM (φ b) +
      (defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L defectSqrt φ) ∘L defectOp φ b := by
  rw [stinespring_eq']
  simp only [defectOp_apply, map_mul (toOp φ).stinespringHom, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (defectSqrt φ) (defectSqrt φ), defectSqrt_comp_self hφ,
    defectProj]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc]
  abel

private theorem sqrt_normDefect_eq (a : A) : √(φ.normDefect a) = ‖defectOp φ a‖ := by
  rw [normDefect_def, ← norm_toEuclideanCLM, toEuclideanCLM_map_star_mul_sub hφ,
    ContinuousLinearMap.norm_adjoint_comp_self, Real.sqrt_mul_self (norm_nonneg _)]

private theorem twoNormDefect_eq (a : A) :
    φ.twoNormDefect a = (Fintype.card n : ℝ)⁻¹ * (defectOp φ a).hilbertSchmidtNorm ^ 2 := by
  rw [twoNormDefect_def, map_star_mul_sub_eq hφ,
    normalizedTrace_toEuclideanCLM_symm_adjoint_comp_self, Complex.ofReal_re]

private theorem sqrt_twoNormDefect_eq (a : A) :
    √(φ.twoNormDefect a) = √(Fintype.card n : ℝ)⁻¹ * (defectOp φ a).hilbertSchmidtNorm := by
  rw [twoNormDefect_eq hφ, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (defectOp φ a).hilbertSchmidtNorm_nonneg]

/-- `φ(ab) - φ(a)φ(b) = T(a⋆)⋆T(b)`. -/
private theorem map_mul_sub_eq (a b : A) :
    φ (a * b) - φ a * φ b =
      toEuclideanCLM.symm ((defectOp φ (star a)).adjoint ∘L defectOp φ b) := by
  have h := map_star_mul_sub_eq hφ (star a) b
  rwa [star_star, ← φ.map_star, star_star] at h

end Dilation

variable {φ : A →CP CStarMatrix n n ℂ} (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
include hφ

/-- **Kadison–Schwarz inequality** for a completely positive contraction into matrices:
`φ(a)⋆φ(a) ≤ φ(a⋆a)`. -/
theorem star_map_mul_map_le_of_norm_map_le (a : A) : star (φ a) * φ a ≤ φ (star a * a) := by
  classical
  rw [← toEuclideanCLM_le_toEuclideanCLM_iff, map_mul, map_star, ← toOp_apply, ← toOp_apply]
  exact (toOp φ).star_map_mul_map_le_of_opNorm_le_one (norm_toContinuousLinearMap_toOp_le hφ) a

/-- The 2-norm defect is nonnegative. -/
theorem twoNormDefect_nonneg (a : A) : 0 ≤ φ.twoNormDefect a := by
  classical
  rw [twoNormDefect_eq hφ]
  positivity

/-- The norm product estimate `‖φ(ab) - φ(a)φ(b)‖ ≤ ‖a‖ d_∞(φ, b)^{1/2}`. -/
theorem norm_map_mul_sub_le (a b : A) :
    ‖φ (a * b) - φ a * φ b‖ ≤ ‖a‖ * √(φ.normDefect b) := by
  classical
  rw [map_mul_sub_eq hφ, ← norm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply,
    sqrt_normDefect_eq hφ]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_defectOp_le hφ (star a)) (norm_nonneg _)

/-- The norm product estimate `‖φ(ab) - φ(a)φ(b)‖ ≤ d_∞(φ, a⋆)^{1/2} ‖b‖`. -/
theorem norm_map_mul_sub_le' (a b : A) :
    ‖φ (a * b) - φ a * φ b‖ ≤ √(φ.normDefect (star a)) * ‖b‖ := by
  classical
  rw [map_mul_sub_eq hφ, ← norm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply,
    sqrt_normDefect_eq hφ]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_left (norm_defectOp_le hφ b) (norm_nonneg _)

/-- The 2-norm product estimate `‖φ(ab) - φ(a)φ(b)‖₂ ≤ ‖a‖ d₂(φ, b)^{1/2}`. -/
theorem normalizedTwoNorm_map_mul_sub_le (a b : A) :
    normalizedTwoNorm (φ (a * b) - φ a * φ b) ≤ ‖a‖ * √(φ.twoNormDefect b) := by
  classical
  rw [map_mul_sub_eq hφ, normalizedTwoNorm_toEuclideanCLM_symm, sqrt_twoNormDefect_eq hφ,
    mul_left_comm]
  gcongr
  refine (hilbertSchmidtNorm_comp_le_left_of_finiteDimensional _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_defectOp_le hφ (star a))
    (ContinuousLinearMap.hilbertSchmidtNorm_nonneg _)

/-- The 2-norm product estimate `‖φ(ab) - φ(a)φ(b)‖₂ ≤ d₂(φ, a⋆)^{1/2} ‖b‖`. -/
theorem normalizedTwoNorm_map_mul_sub_le' (a b : A) :
    normalizedTwoNorm (φ (a * b) - φ a * φ b) ≤ √(φ.twoNormDefect (star a)) * ‖b‖ := by
  classical
  have h : star (φ (a * b) - φ a * φ b) = φ (star b * star a) - star (φ b) * φ (star a) := by
    rw [← star_mul, φ.map_star, φ.map_star, star_sub, star_mul]
  rw [← normalizedTwoNorm_star, h, map_star_mul_sub_eq hφ, normalizedTwoNorm_toEuclideanCLM_symm,
    sqrt_twoNormDefect_eq hφ, mul_assoc, mul_comm (ContinuousLinearMap.hilbertSchmidtNorm _)]
  gcongr
  refine (hilbertSchmidtNorm_comp_le_left_of_finiteDimensional _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right (norm_defectOp_le hφ b)
    (ContinuousLinearMap.hilbertSchmidtNorm_nonneg _)

/-- Subadditivity of `d_∞(φ, ·)^{1/2}`. -/
theorem sqrt_normDefect_add_le (a b : A) :
    √(φ.normDefect (a + b)) ≤ √(φ.normDefect a) + √(φ.normDefect b) := by
  classical
  simp only [sqrt_normDefect_eq hφ, map_add]
  exact norm_add_le (E := EuclideanSpace ℂ n →L[ℂ] (toOp φ).Stinespring) _ _

/-- Subadditivity of `d₂(φ, ·)^{1/2}`. -/
theorem sqrt_twoNormDefect_add_le (a b : A) :
    √(φ.twoNormDefect (a + b)) ≤ √(φ.twoNormDefect a) + √(φ.twoNormDefect b) := by
  classical
  simp only [sqrt_twoNormDefect_eq hφ, map_add, ← mul_add]
  gcongr
  exact hilbertSchmidtNorm_add_le_of_finiteDimensional _ _

/-- The product rule `d_∞(φ, ab)^{1/2} ≤ ‖b‖ d_∞(φ, a)^{1/2} + ‖a‖ d_∞(φ, b)^{1/2}`. -/
theorem sqrt_normDefect_mul_le (a b : A) :
    √(φ.normDefect (a * b)) ≤ ‖b‖ * √(φ.normDefect a) + ‖a‖ * √(φ.normDefect b) := by
  classical
  simp only [sqrt_normDefect_eq hφ]
  rw [defectOp_mul hφ]
  refine (norm_add_le (E := EuclideanSpace ℂ n →L[ℂ] (toOp φ).Stinespring) _ _).trans
    (add_le_add ?_ ?_)
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_toEuclideanCLM, mul_comm ‖b‖]
    exact mul_le_mul_of_nonneg_left (hφ b) (norm_nonneg _)
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (norm_defectSqrt_comp_le hφ a) (norm_nonneg _)

/-- The product rule `d₂(φ, ab)^{1/2} ≤ ‖b‖ d₂(φ, a)^{1/2} + ‖a‖ d₂(φ, b)^{1/2}`. -/
theorem sqrt_twoNormDefect_mul_le (a b : A) :
    √(φ.twoNormDefect (a * b)) ≤ ‖b‖ * √(φ.twoNormDefect a) + ‖a‖ * √(φ.twoNormDefect b) := by
  classical
  simp only [sqrt_twoNormDefect_eq hφ, mul_left_comm _ √_, ← mul_add]
  rw [defectOp_mul hφ]
  gcongr
  refine (hilbertSchmidtNorm_add_le_of_finiteDimensional _ _).trans (add_le_add ?_ ?_)
  · refine (hilbertSchmidtNorm_comp_le_right_of_finiteDimensional _ _).trans ?_
    rw [norm_toEuclideanCLM, mul_comm ‖b‖]
    exact mul_le_mul_of_nonneg_left (hφ b) (ContinuousLinearMap.hilbertSchmidtNorm_nonneg _)
  · refine (hilbertSchmidtNorm_comp_le_left_of_finiteDimensional _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (norm_defectSqrt_comp_le hφ a)
      (ContinuousLinearMap.hilbertSchmidtNorm_nonneg _)

/-- `d_∞(φ, a)^{1/2} ≤ ‖a‖`. -/
theorem sqrt_normDefect_le (a : A) : √(φ.normDefect a) ≤ ‖a‖ := by
  classical
  rw [sqrt_normDefect_eq hφ]
  exact norm_defectOp_le hφ a

/-- `d₂(φ, a)^{1/2} ≤ ‖a‖`. -/
theorem sqrt_twoNormDefect_le (a : A) : √(φ.twoNormDefect a) ≤ ‖a‖ :=
  (Real.sqrt_le_sqrt (φ.twoNormDefect_le_normDefect a)).trans (sqrt_normDefect_le hφ a)

/-- The Lipschitz bound `|d_∞(φ, a)^{1/2} - d_∞(φ, b)^{1/2}| ≤ ‖a - b‖`. -/
theorem abs_sqrt_normDefect_sub_le (a b : A) :
    |√(φ.normDefect a) - √(φ.normDefect b)| ≤ ‖a - b‖ := by
  classical
  simp only [sqrt_normDefect_eq hφ]
  refine (abs_norm_sub_norm_le (defectOp φ a) (defectOp φ b)).trans ?_
  rw [← map_sub]
  exact norm_defectOp_le hφ _

/-- The Lipschitz bound `|d₂(φ, a)^{1/2} - d₂(φ, b)^{1/2}| ≤ ‖a - b‖`. -/
theorem abs_sqrt_twoNormDefect_sub_le (a b : A) :
    |√(φ.twoNormDefect a) - √(φ.twoNormDefect b)| ≤ ‖a - b‖ := by
  have hab := sqrt_twoNormDefect_add_le hφ (a - b) b
  have hba := sqrt_twoNormDefect_add_le hφ (b - a) a
  rw [sub_add_cancel] at hab hba
  rw [abs_sub_le_iff]
  constructor <;> linarith [sqrt_twoNormDefect_le hφ (a - b), sqrt_twoNormDefect_le hφ (b - a),
    norm_sub_rev a b]

end CompletelyPositiveMap
