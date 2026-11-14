/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# `n`-positive maps and the Kadison–Schwarz inequality

A complex-linear map `φ : A → B` between C⋆-algebras is `n`-positive when its entrywise
amplification `M_n(A) → M_n(B)` is positive, with `M_n(A) = CStarMatrix (Fin n) (Fin n) A`
ordered as a C⋆-algebra. Mathlib's completely positive maps `A →CP B` are exactly the maps that
are `n`-positive for every `n`.

For a `2`-positive map with unital domain, positivity of the image of the matrix
`[[a⋆a, a⋆], [a, 1]] = [[a, 1], [0, 0]]⋆ [[a, 1], [0, 0]]` gives the **Kadison–Schwarz
inequality**

`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)`,

and `φ(a)⋆ φ(a) ≤ φ(a⋆a)` when the codomain is unital and `φ 1 = 1`. A non-unital codomain `B`
is handled through its unitization `B⁺¹`. Together with the bound `‖φ p‖ ≤ ‖φ 1‖ ‖p‖` for
positive `p`, this gives `‖φ a‖ ≤ ‖φ 1‖ ‖a‖`, so the operator norm of a continuous `2`-positive map
with unital domain is `‖φ 1‖`.

## Main declarations

* `TauCeti.IsNPositive`: `n`-positivity of a complex-linear map, with
  `CompletelyPositiveMap.isNPositive` and `CompletelyPositiveMap.ofIsNPositive`: a linear map is
  completely positive exactly when it is `n`-positive for every `n`.
* `TauCeti.IsNPositive.mono`: an `n`-positive map is `m`-positive for `m ≤ n`, and
  `TauCeti.isNPositive_one_iff`: `1`-positivity is positivity.
* `TauCeti.IsNPositive.toPositiveLinearMap`: an `n`-positive map with `0 < n` is positive.
* `PositiveLinearMap.eq_zero_of_map_one_eq_zero`: a positive map on a unital C⋆-algebra that
  vanishes at `1` is zero.
* `TauCeti.IsNPositive.star_map_mul_map_le`: the Kadison–Schwarz inequality
  `φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)` for `2`-positive maps, and
  `TauCeti.IsNPositive.star_map_mul_map_le_of_map_one` for unital ones.
* `TauCeti.IsNPositive.norm_apply_le`: `‖φ a‖ ≤ ‖φ 1‖ * ‖a‖` for `2`-positive maps, and
  `TauCeti.IsNPositive.opNorm_eq_norm_map_one`: `‖ψ‖ = ‖ψ 1‖` for continuous ones.
* `CompletelyPositiveMapClass.star_map_mul_map_le`,
  `CompletelyPositiveMapClass.star_map_mul_map_le_of_map_one` and
  `CompletelyPositiveMapClass.opNorm_ofClass_eq_norm_map_one`: the Schwarz inequality for
  completely positive maps, and `‖φ‖ = ‖φ 1‖`.

## References

* B. Blackadar, *Operator Algebras*, II.6.9.4 and II.6.9.14.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Proposition 3.3 and
  Exercise 3.4.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

variable {A B C : Type*}

section NonUnital

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A complex-linear map `φ : A → B` between C⋆-algebras is **`n`-positive** when its entrywise
amplification to `n × n` matrices, ordered as the C⋆-algebras `CStarMatrix (Fin n) (Fin n) _`,
sends positive matrices to positive matrices. -/
def IsNPositive (n : ℕ) (φ : A →ₗ[ℂ] B) : Prop :=
  ∀ M : CStarMatrix (Fin n) (Fin n) A, 0 ≤ M → 0 ≤ M.map φ

theorem isNPositive_iff {n : ℕ} {φ : A →ₗ[ℂ] B} :
    IsNPositive n φ ↔ ∀ M : CStarMatrix (Fin n) (Fin n) A, 0 ≤ M → 0 ≤ M.map φ :=
  Iff.rfl

/-- An `n`-positive map sends positive `n × n` matrices to positive matrices. -/
theorem IsNPositive.map_cstarMatrix_nonneg {n : ℕ} {φ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ)
    {M : CStarMatrix (Fin n) (Fin n) A} (hM : 0 ≤ M) : 0 ≤ M.map φ :=
  hφ M hM

/-- A completely positive map is `n`-positive for every `n`. -/
@[simp]
theorem _root_.CompletelyPositiveMap.isNPositive (φ : A →CP B) (n : ℕ) :
    IsNPositive n φ.toLinearMap :=
  φ.map_cstarMatrix_nonneg' n

/-- A map in a class of completely positive maps is `n`-positive for every `n`. -/
@[simp]
theorem _root_.CompletelyPositiveMapClass.isNPositive {F : Type*} [FunLike F A B]
    [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B] (φ : F) (n : ℕ) :
    IsNPositive n (φ : A →ₗ[ℂ] B) :=
  CompletelyPositiveMapClass.map_cstarMatrix_nonneg' φ n

@[simp]
theorem _root_.CompletelyPositiveMap.coe_toLinearMap (φ : A →CP B) : ⇑φ.toLinearMap = φ :=
  (rfl)

/-- A linear map that is `n`-positive for every `n`, as a completely positive map. -/
def _root_.CompletelyPositiveMap.ofIsNPositive (φ : A →ₗ[ℂ] B) (hφ : ∀ n, IsNPositive n φ) :
    A →CP B where
  toLinearMap := φ
  map_cstarMatrix_nonneg' := hφ

@[simp]
theorem _root_.CompletelyPositiveMap.coe_ofIsNPositive (φ : A →ₗ[ℂ] B)
    (hφ : ∀ n, IsNPositive n φ) : ⇑(CompletelyPositiveMap.ofIsNPositive φ hφ) = φ :=
  (rfl)

@[simp]
theorem _root_.CompletelyPositiveMap.toLinearMap_ofIsNPositive (φ : A →ₗ[ℂ] B)
    (hφ : ∀ n, IsNPositive n φ) : (CompletelyPositiveMap.ofIsNPositive φ hφ).toLinearMap = φ :=
  (rfl)

@[simp]
theorem _root_.CompletelyPositiveMap.ofIsNPositive_toLinearMap (φ : A →CP B)
    (hφ : ∀ n, IsNPositive n φ.toLinearMap) :
    CompletelyPositiveMap.ofIsNPositive φ.toLinearMap hφ = φ :=
  (rfl)

/-- Every linear map is `0`-positive. -/
@[simp]
theorem isNPositive_zero (φ : A →ₗ[ℂ] B) : IsNPositive 0 φ :=
  fun _ _ => (CStarMatrix.ext fun i _ => i.elim0).ge

/-- The identity is `n`-positive. -/
@[simp]
theorem IsNPositive.id (n : ℕ) : IsNPositive n (LinearMap.id : A →ₗ[ℂ] A) :=
  fun M hM => by simpa using hM

/-- The zero map is `n`-positive. -/
@[simp]
theorem IsNPositive.zero (n : ℕ) : IsNPositive n (0 : A →ₗ[ℂ] B) :=
  fun _ _ => (CStarMatrix.ext fun _ _ => by simp [CStarMatrix.zero_apply]).ge

/-- The sum of `n`-positive maps is `n`-positive. -/
theorem IsNPositive.add {n : ℕ} {φ ψ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ) (hψ : IsNPositive n ψ) :
    IsNPositive n (φ + ψ) := fun M hM => by
  have h : M.map ⇑(φ + ψ) = M.map φ + M.map ψ :=
    CStarMatrix.ext fun _ _ => by simp [CStarMatrix.add_apply]
  rw [h]
  exact add_nonneg (hφ M hM) (hψ M hM)

/-- The composition of `n`-positive maps is `n`-positive. -/
theorem IsNPositive.comp [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C] {n : ℕ}
    {ψ : B →ₗ[ℂ] C} {φ : A →ₗ[ℂ] B} (hψ : IsNPositive n ψ) (hφ : IsNPositive n φ) :
    IsNPositive n (ψ ∘ₗ φ) := fun M hM => by
  simpa only [LinearMap.coe_comp, CStarMatrix.map_comp] using hψ _ (hφ M hM)

/-- An `n`-positive map is `m`-positive for every `m ≤ n`. -/
theorem IsNPositive.mono {m n : ℕ} {φ : A →ₗ[ℂ] B} (hmn : m ≤ n) (hφ : IsNPositive n φ) :
    IsNPositive m φ := fun M hM => by
  -- Pad `M` with zeros to an `n × n` matrix, apply `φ`, and restrict back.
  have hf := Fin.castLE_injective hmn
  convert CStarMatrix.submatrix_nonneg hf (hφ _ (CStarMatrix.extend_nonneg hf hM)) using 1
  ext i j
  simp [hf.extend_apply]

/-- An `n`-positive map with `0 < n` sends positive elements to positive elements. -/
theorem IsNPositive.map_nonneg {n : ℕ} {φ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ) (hn : 0 < n)
    {a : A} (ha : 0 ≤ a) : 0 ≤ φ a := by
  -- `a` sits in a corner of the positive diagonal matrix `diag(a, 0, …, 0)`.
  let i₀ : Fin n := ⟨0, hn⟩
  let M : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrix (Matrix.diagonal (Pi.single i₀ a))
  have hM : 0 ≤ M := CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun x => by
    simpa [M, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply, Pi.single_apply]
      using star_left_conjugate_nonneg ha (x i₀)
  simpa [M, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply] using
    CStarMatrix.diag_nonneg_of_nonneg (hφ M hM) i₀

/-- An `n`-positive map with `0 < n`, as a positive linear map. -/
def IsNPositive.toPositiveLinearMap {n : ℕ} {φ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ)
    (hn : 0 < n) : A →ₚ[ℂ] B :=
  .mk₀ φ fun _ ha => hφ.map_nonneg hn ha

@[simp]
theorem IsNPositive.toPositiveLinearMap_apply {n : ℕ} {φ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ)
    (hn : 0 < n) (a : A) : hφ.toPositiveLinearMap hn a = φ a :=
  (rfl)

@[simp]
theorem IsNPositive.toLinearMap_toPositiveLinearMap {n : ℕ} {φ : A →ₗ[ℂ] B}
    (hφ : IsNPositive n φ) (hn : 0 < n) : (hφ.toPositiveLinearMap hn).toLinearMap = φ :=
  (rfl)

/-- An `n`-positive map with `0 < n` preserves `star`. -/
theorem IsNPositive.map_star {n : ℕ} {φ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ) (hn : 0 < n)
    (a : A) : φ (star a) = star (φ a) :=
  StarHomClass.map_star (hφ.toPositiveLinearMap hn) a

/-- A linear map is `1`-positive exactly when it is positive. -/
theorem isNPositive_one_iff {φ : A →ₗ[ℂ] B} : IsNPositive 1 φ ↔ ∀ a, 0 ≤ a → 0 ≤ φ a := by
  refine ⟨fun hφ _ ha => hφ.map_nonneg one_pos ha, fun h M hM => ?_⟩
  refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun x => ?_
  simpa using star_left_conjugate_nonneg (h _ (CStarMatrix.diag_nonneg_of_nonneg hM 0)) (x 0)

/-- A positive linear map is `1`-positive. -/
@[simp]
theorem _root_.OrderHomClass.isNPositive_one {F : Type*} [FunLike F A B] [LinearMapClass F ℂ A B]
    [OrderHomClass F A B] (φ : F) : IsNPositive 1 (φ : A →ₗ[ℂ] B) :=
  isNPositive_one_iff.mpr fun _ ha => map_nonneg φ ha

/-- A positive linear map is `1`-positive. -/
@[simp]
theorem _root_.PositiveLinearMap.isNPositive_one (φ : A →ₚ[ℂ] B) :
    IsNPositive 1 φ.toLinearMap :=
  isNPositive_one_iff.mpr fun _ ha => φ.map_nonneg ha

end NonUnital

end TauCeti

/-- A positive map on a unital C⋆-algebra that vanishes at `1` is zero. -/
theorem PositiveLinearMap.eq_zero_of_map_one_eq_zero {A B : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [AddCommMonoid B] [PartialOrder B] [Module ℂ B]
    (ψ : A →ₚ[ℂ] B) (h1 : ψ 1 = 0) : ψ = 0 := by
  refine PositiveLinearMap.toLinearMap_injective <|
    LinearMap.ext_on (CStarAlgebra.span_nonneg (A := A)) fun a (ha : 0 ≤ a) => ?_
  refine le_antisymm ?_ (ψ.map_nonneg ha)
  calc ψ a ≤ ψ (algebraMap ℝ A ‖a‖) := ψ.monotone (ha.isSelfAdjoint.le_algebraMap_norm_self)
    _ = 0 := by
      rw [IsScalarTower.algebraMap_apply ℝ ℂ A, Algebra.algebraMap_eq_smul_one, map_smul, h1,
        smul_zero]

namespace TauCeti

section UnitalDomain

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →ₗ[ℂ] B}

/-- An `n`-positive map with `0 < n` whose value at `1` vanishes is zero. -/
theorem IsNPositive.eq_zero_of_map_one_eq_zero {n : ℕ} (hφ : IsNPositive n φ) (hn : 0 < n)
    (h1 : φ 1 = 0) : φ = 0 := by
  rw [← hφ.toLinearMap_toPositiveLinearMap hn,
    (hφ.toPositiveLinearMap hn).eq_zero_of_map_one_eq_zero (by simpa using h1),
    PositiveLinearMap.toLinearMap_zero]

end UnitalDomain

section Unital

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →ₗ[ℂ] B}

/-- For a `2`-positive map `φ`, the quadratic form at `(x, y)` of the image
`[[φ(a⋆a), φ(a)⋆], [φ(a), φ 1]]` of the positive matrix `[[a⋆a, a⋆], [a, 1]]` is positive. -/
private theorem IsNPositive.quadratic_nonneg (hφ : IsNPositive 2 φ) (a : A) (x y : B) :
    0 ≤ star x * φ (star a * a) * x + star x * star (φ a) * y + star y * φ a * x +
      star y * φ 1 * y := by
  let M : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![star a * a, star a; a, 1]
  have hM : 0 ≤ M := CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun z => by
    have h : ∑ i, ∑ j, star (z i) * M i j * z j = star (a * z 0 + z 1) * (a * z 0 + z 1) := by
      simp only [M, Fin.sum_univ_two, CStarMatrix.ofMatrix_apply, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, star_add, star_mul, mul_add, add_mul, one_mul, mul_assoc]
      abel
    rw [h]
    exact star_mul_self_nonneg _
  have hN := hφ M hM
  have := CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hN ![x, y]
  simpa [M, Fin.sum_univ_two, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply,
    hφ.map_star two_pos a,
    add_assoc] using this

/-- **Kadison–Schwarz inequality** for a unital `2`-positive map: `φ(a)⋆ φ(a) ≤ φ(a⋆a)`. -/
theorem IsNPositive.star_map_mul_map_le_of_map_one (hφ : IsNPositive 2 φ) (h1 : φ 1 = 1)
    (a : A) : star (φ a) * φ a ≤ φ (star a * a) := by
  have := hφ.quadratic_nonneg a 1 (-φ a)
  rw [← sub_nonneg]
  convert this using 1
  simp only [star_one, one_mul, mul_one, mul_neg, star_neg, neg_mul, h1, neg_neg,
    neg_add_cancel_right]
  abel

/-- The Kadison–Schwarz inequality `φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)` for a `2`-positive map with
unital domain and codomain. -/
private theorem IsNPositive.star_map_mul_map_le_of_unital (hφ : IsNPositive 2 φ) (a : A) :
    star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a) := by
  set c := ‖φ 1‖
  rcases (norm_nonneg (φ 1)).eq_or_lt with h0 | hpos
  · simp [hφ.eq_zero_of_map_one_eq_zero two_pos (norm_eq_zero.mp h0.symm)]
  set b := φ a
  have hq := hφ.quadratic_nonneg a (c • 1) (-b)
  have hconj : star b * φ 1 * b ≤ c • (star b * b) :=
    CStarAlgebra.star_left_conjugate_le_norm_smul b (φ 1)
      (hφ.map_nonneg two_pos zero_le_one).isSelfAdjoint
  have key : 0 ≤ c • (c • φ (star a * a) - star b * b) :=
    calc 0 ≤ _ := hq
      _ = c • c • φ (star a * a) - c • (star b * b) - c • (star b * b) + star b * φ 1 * b := by
        simp only [star_smul, star_trivial, star_one, Algebra.smul_mul_assoc, one_mul,
          Algebra.mul_smul_comm, mul_one, mul_neg, star_neg, neg_mul, smul_neg, neg_neg, b]
        abel
      _ ≤ c • c • φ (star a * a) - c • (star b * b) - c • (star b * b) + c • (star b * b) :=
        add_le_add_right hconj _
      _ = c • (c • φ (star a * a) - star b * b) := by
        rw [smul_sub]
        abel
  have := smul_nonneg (inv_nonneg.mpr hpos.le) key
  rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul, sub_nonneg] at this
  exact this

end Unital

section UnitalDomain

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {φ : A →ₗ[ℂ] B}

/-- Composing with the inclusion `B → B⁺¹` into the unitization preserves `n`-positivity. -/
private theorem IsNPositive.inr {n : ℕ} (hφ : IsNPositive n φ) :
    IsNPositive n ((Unitization.inrNonUnitalStarAlgHom ℂ B : B →ₗ[ℂ] B⁺¹) ∘ₗ φ) :=
  (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (Unitization.inrNonUnitalStarAlgHom ℂ B) |>.isNPositive n).comp hφ

/-- **Kadison–Schwarz inequality** for a `2`-positive map with unital domain:
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)`. -/
theorem IsNPositive.star_map_mul_map_le (hφ : IsNPositive 2 φ) (a : A) :
    star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a) := by
  have := hφ.inr.star_map_mul_map_le_of_unital a
  rw [← Unitization.inr_le_inr_iff]
  simpa [Unitization.norm_inr, Unitization.inr_smul] using this

/-- A `2`-positive map with unital domain is bounded by `‖φ 1‖`. -/
theorem IsNPositive.norm_apply_le (hφ : IsNPositive 2 φ) (a : A) : ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ := by
  have h : ‖φ a‖ * ‖φ a‖ ≤ (‖φ 1‖ * ‖a‖) * (‖φ 1‖ * ‖a‖) := by
    rw [← CStarRing.norm_star_mul_self]
    calc ‖star (φ a) * φ a‖ ≤ ‖‖φ 1‖ • φ (star a * a)‖ :=
          CStarAlgebra.norm_le_norm_of_le_of_nonneg (hφ.star_map_mul_map_le a)
            (star_mul_self_nonneg _)
      _ = ‖φ 1‖ * ‖φ (star a * a)‖ := by rw [norm_smul, norm_norm]
      _ ≤ ‖φ 1‖ * (‖φ 1‖ * ‖star a * a‖) := by
          gcongr
          simpa [Unitization.norm_inr] using
            (hφ.inr.toPositiveLinearMap two_pos).norm_apply_le_of_nonneg _
              (star_mul_self_nonneg a)
      _ = (‖φ 1‖ * ‖a‖) * (‖φ 1‖ * ‖a‖) := by rw [CStarRing.norm_star_mul_self]; ring
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (by positivity)).mpr h

/-- The operator norm of a continuous `2`-positive map with unital domain is `‖ψ 1‖`. -/
theorem IsNPositive.opNorm_eq_norm_map_one {ψ : A →L[ℂ] B} (hψ : IsNPositive 2 (ψ : A →ₗ[ℂ] B)) :
    ‖ψ‖ = ‖ψ 1‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) hψ.norm_apply_le) ?_
  rcases subsingleton_or_nontrivial A with hA | hA
  · simp [Subsingleton.elim (1 : A) 0]
  simpa using ψ.le_opNorm 1

end UnitalDomain

end TauCeti

namespace CompletelyPositiveMapClass

open TauCeti

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

section NonUnital

variable [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [FunLike F A B]
  [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B]

/-- **Kadison–Schwarz inequality** for a completely positive map with unital domain:
`φ(a)⋆ φ(a) ≤ ‖φ 1‖ • φ(a⋆a)`. -/
theorem star_map_mul_map_le (φ : F) (a : A) :
    star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a) :=
  (isNPositive φ 2).star_map_mul_map_le a

/-- A completely positive map with unital domain is bounded by `‖φ 1‖`. -/
theorem norm_apply_le (φ : F) (a : A) : ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ :=
  (isNPositive φ 2).norm_apply_le a

/-- The operator norm of a completely positive map with unital domain, made continuous by
`PositiveContinuousLinearMap.ofClass`, is `‖φ 1‖`. -/
theorem opNorm_ofClass_eq_norm_map_one (φ : F) :
    ‖((PositiveContinuousLinearMap.ofClass φ : A →P[ℂ] B) : A →L[ℂ] B)‖ = ‖φ 1‖ :=
  (isNPositive φ 2).opNorm_eq_norm_map_one

end NonUnital

/-- **Kadison–Schwarz inequality** for a unital completely positive map:
`φ(a)⋆ φ(a) ≤ φ(a⋆a)`. -/
theorem star_map_mul_map_le_of_map_one [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B] (φ : F)
    (hφ : φ 1 = 1) (a : A) : star (φ a) * φ a ≤ φ (star a * a) :=
  (isNPositive φ 2).star_map_mul_map_le_of_map_one hφ a

end CompletelyPositiveMapClass
