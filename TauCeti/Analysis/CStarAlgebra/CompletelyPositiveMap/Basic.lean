/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Module.Gram
public import TauCeti.Analysis.CStarAlgebra.Module.Self

/-!
# Basic API and the Kadison–Schwarz inequality for completely positive maps

Mathlib defines `CompletelyPositiveMap A B` (with notation `A →CP B` in scope `CStarAlgebra`) for
linear maps between C⋆-algebras whose entrywise action on `CStarMatrix (Fin k) (Fin k) A` preserves
positivity for every `k`. Every completely positive map is positive (`OrderHomClass`), hence
star-preserving and automatically continuous (`ContinuousLinearMapClass`).

This file equips `A →CP B` with its convex cone structure, composition, the completely positive
partial order (`ψ ≤ φ` when `φ - ψ` is completely positive), the canonical compression examples
`a ↦ star b * a * b` and `S ↦ V† ∘L S ∘L V`, and the Kadison–Schwarz inequality for maps on a
unital C⋆-algebra `D`:

* `star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a)` for any codomain C⋆-algebra `B` (unital or not);
* `star (φ a) * φ a ≤ φ (star a * a)` when the codomain is unital and `φ 1 ≤ 1` (in particular
  when `φ 1 = 1`);
* `‖φ a‖ ≤ ‖φ 1‖ * ‖a‖` and `‖φ.toContinuousLinearMap‖ = ‖φ 1‖`.

## Main declarations

* `CompletelyPositiveMap.toPositiveLinearMap`, `CompletelyPositiveMap.toContinuousLinearMap`:
  reinterpretations as positive and continuous linear maps.
* `CompletelyPositiveMap.id`, `CompletelyPositiveMap.comp`: identity and composition of completely
  positive maps.
* `AddCommMonoid (A →CP B)`, `Module ℝ≥0 (A →CP B)`, `PartialOrder (A →CP B)`,
  `OrderBot (A →CP B)`: the convex cone and completely positive partial order, characterized by
  `CompletelyPositiveMap.le_iff_exists_add`.
* `CompletelyPositiveMap.conj`, `CompletelyPositiveMap.conjCLM`: compression `a ↦ star b * a * b`
  on a C⋆-algebra and `S ↦ V† ∘L S ∘L V` between Hilbert-space operator algebras.
* `CompletelyPositiveMap.star_map_mul_map_le_of_map_one_le`,
  `CompletelyPositiveMap.star_map_mul_map_le`,
  `CompletelyPositiveMap.star_map_mul_map_le_norm_map_one_smul`: the Kadison–Schwarz inequality in
  subunital, unital, and general form.
* `CompletelyPositiveMap.norm_apply_le_norm_map_one_mul`,
  `CompletelyPositiveMap.norm_toContinuousLinearMap`: sharp norm bound and operator norm formula
  `‖φ.toContinuousLinearMap‖ = ‖φ 1‖`.

## References

* W. F. Stinespring, *Positive functions on C*-algebras*, Proc. Amer. Math. Soc. 6 (1955), 211–216.
* M.-D. Choi, *A Schwarz inequality for positive linear maps on C*-algebras*, Illinois J. Math. 18
  (1974), 565–574.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Proposition 3.3 and Corollary 3.2.
-/

public section

noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace NNReal

namespace CompletelyPositiveMapClass

variable {F A B : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B]

@[simp] theorem coe_toCompletelyPositiveLinearMap (f : F) :
    ⇑(toCompletelyPositiveLinearMap f : A →CP B) = f := (rfl)

@[simp] theorem toCompletelyPositiveLinearMap_apply (f : F) (a : A) :
    (toCompletelyPositiveLinearMap f : A →CP B) a = f a := (rfl)

end CompletelyPositiveMapClass

namespace CompletelyPositiveMap

section Basic

variable {A B C : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

@[ext] theorem ext {φ ψ : A →CP B} (h : ∀ a, φ a = ψ a) : φ = ψ := DFunLike.ext φ ψ h

@[simp] theorem coe_mk (f : A →ₗ[ℂ] B) (hf) : ⇑(⟨f, hf⟩ : A →CP B) = f := (rfl)

@[simp] theorem mk_apply (f : A →ₗ[ℂ] B) (hf) (a : A) : (⟨f, hf⟩ : A →CP B) a = f a := (rfl)

/-- The underlying `ℂ`-linear map of `φ` agrees with its `LinearMapClass` coercion. -/
theorem toLinearMap_eq_coe (φ : A →CP B) : φ.toLinearMap = (φ : A →ₗ[ℂ] B) := (rfl)

@[simp] theorem coe_toLinearMap (φ : A →CP B) : ⇑φ.toLinearMap = φ := (rfl)

/-- Reinterpret a completely positive map as a positive linear map. -/
def toPositiveLinearMap (φ : A →CP B) : A →ₚ[ℂ] B := .ofClass φ

@[simp] theorem coe_toPositiveLinearMap (φ : A →CP B) : ⇑φ.toPositiveLinearMap = φ := (rfl)

@[simp] theorem toPositiveLinearMap_apply (φ : A →CP B) (a : A) :
    φ.toPositiveLinearMap a = φ a := (rfl)

/-- Reinterpret a completely positive map as a continuous linear map. Continuity is automatic
because every completely positive map is positive (`PositiveLinearMap.exists_norm_apply_le`). -/
noncomputable def toContinuousLinearMap (φ : A →CP B) : A →L[ℂ] B :=
  { φ.toLinearMap with cont := map_continuous φ }

@[simp] theorem coe_toContinuousLinearMap (φ : A →CP B) : ⇑φ.toContinuousLinearMap = φ := (rfl)

@[simp] theorem toContinuousLinearMap_apply (φ : A →CP B) (a : A) :
    φ.toContinuousLinearMap a = φ a := (rfl)

@[fun_prop] protected theorem continuous (φ : A →CP B) : Continuous φ := map_continuous φ

/-- The identity completely positive map on a C⋆-algebra. -/
protected def id (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :
    A →CP A where
  toLinearMap := LinearMap.id
  map_cstarMatrix_nonneg' _ M hM := by simpa using hM

@[simp] theorem coe_id : ⇑(CompletelyPositiveMap.id A) = id := (rfl)

@[simp] theorem id_apply (a : A) : CompletelyPositiveMap.id A a = a := (rfl)

/-- Composition of completely positive maps is completely positive. -/
def comp (ψ : B →CP C) (φ : A →CP B) : A →CP C where
  toLinearMap := ψ.toLinearMap.comp φ.toLinearMap
  map_cstarMatrix_nonneg' _ M hM := by
    have h : M.map (ψ.toLinearMap.comp φ.toLinearMap) = (M.map φ).map ψ := by ext; rfl
    exact h ▸ ψ.map_cstarMatrix_nonneg _ (φ.map_cstarMatrix_nonneg M hM)

@[simp] theorem coe_comp (ψ : B →CP C) (φ : A →CP B) : ⇑(ψ.comp φ) = ψ ∘ φ := (rfl)

@[simp] theorem comp_apply (ψ : B →CP C) (φ : A →CP B) (a : A) : ψ.comp φ a = ψ (φ a) := (rfl)

/-- Composition of completely positive maps is associative. -/
theorem comp_assoc {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (χ : C →CP D) (ψ : B →CP C) (φ : A →CP B) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := by ext; rfl

@[simp] theorem id_comp (φ : A →CP B) : (CompletelyPositiveMap.id B).comp φ = φ := by ext; rfl

@[simp] theorem comp_id (φ : A →CP B) : φ.comp (CompletelyPositiveMap.id A) = φ := by ext; rfl

instance instZero : Zero (A →CP B) where
  zero :=
    { toLinearMap := 0
      map_cstarMatrix_nonneg' _ M _ := by
        have h : M.map (0 : A →ₗ[ℂ] B) = 0 := by ext; rfl
        rw [h] }

instance : IsZeroApply (A →CP B) where

@[simp] theorem toLinearMap_zero : (0 : A →CP B).toLinearMap = 0 := (rfl)

instance instAdd : Add (A →CP B) where
  add φ ψ :=
    { toLinearMap := φ.toLinearMap + ψ.toLinearMap
      map_cstarMatrix_nonneg' _ M hM := by
        have h : M.map (φ.toLinearMap + ψ.toLinearMap) = M.map φ + M.map ψ := by ext; rfl
        exact h ▸ add_nonneg (φ.map_cstarMatrix_nonneg M hM) (ψ.map_cstarMatrix_nonneg M hM) }

instance : IsAddApply (A →CP B) where

@[simp] theorem toLinearMap_add (φ ψ : A →CP B) :
    (φ + ψ).toLinearMap = φ.toLinearMap + ψ.toLinearMap := (rfl)

instance instSMulNNReal : SMul ℝ≥0 (A →CP B) where
  smul c φ :=
    { toLinearMap := c • φ.toLinearMap
      map_cstarMatrix_nonneg' _ M hM := by
        rw [CStarMatrix.nonneg_iff_forall_sum_nonneg]
        intro x
        have hsum :
            ∑ i, ∑ j, star (x i) * M.map (c • φ.toLinearMap) i j * x j =
              (c : ℝ) • ∑ i, ∑ j, star (x i) * (M.map φ) i j * x j := by
          simp only [CStarMatrix.map_apply, LinearMap.smul_apply, NNReal.smul_def,
            ← Complex.coe_smul, mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum,
            coe_toLinearMap]
        exact hsum ▸ smul_nonneg c.coe_nonneg
          (CStarMatrix.nonneg_iff_forall_sum_nonneg.mp (φ.map_cstarMatrix_nonneg M hM) x) }

instance : IsSMulApply ℝ≥0 (A →CP B) where

@[simp] theorem toLinearMap_smul (c : ℝ≥0) (φ : A →CP B) :
    (c • φ).toLinearMap = c • φ.toLinearMap := (rfl)

instance instSMulNat : SMul ℕ (A →CP B) where
  smul n φ :=
    { toLinearMap := n • φ.toLinearMap
      map_cstarMatrix_nonneg' k M hM := by
        have h : M.map (n • φ.toLinearMap) = M.map (((n : ℝ≥0) • φ).toLinearMap) := by
          ext; simp [Nat.cast_smul_eq_nsmul]
        exact h ▸ ((n : ℝ≥0) • φ).map_cstarMatrix_nonneg' k M hM }

instance : IsSMulApply ℕ (A →CP B) where

instance instAddCommMonoid : AddCommMonoid (A →CP B) := fast_instance% FunLike.addCommMonoid

instance instModuleNNReal : Module ℝ≥0 (A →CP B) where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp
  add_smul _ _ _ := by ext; simp [add_smul]
  zero_smul _ := by ext; simp

private def subOfMatrixLe {ψ φ : A →CP B}
    (h : ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A), 0 ≤ M → M.map ψ ≤ M.map φ) : A →CP B where
  toLinearMap := φ.toLinearMap - ψ.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    have hsub : M.map (φ.toLinearMap - ψ.toLinearMap) = M.map φ - M.map ψ := by ext; rfl
    exact hsub ▸ sub_nonneg.mpr (h k M hM)

/-- The completely positive partial order on `A →CP B`: `ψ ≤ φ` means that `φ - ψ` is completely
positive, equivalently `M.map ψ ≤ M.map φ` for every positive matrix `M` over `A`. -/
instance instPartialOrder : PartialOrder (A →CP B) where
  le ψ φ := ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A), 0 ≤ M → M.map ψ ≤ M.map φ
  le_refl _ _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ k M hM := (h₁ k M hM).trans (h₂ k M hM)
  le_antisymm ψ φ h₁ h₂ := by
    have hnonneg {a : A} (ha : 0 ≤ a) : ψ a = φ a :=
      le_antisymm (sub_nonneg.mp (_root_.map_nonneg (subOfMatrixLe h₁) ha))
        (sub_nonneg.mp (_root_.map_nonneg (subOfMatrixLe h₂) ha))
    ext a
    obtain ⟨y, hy, -, rfl⟩ := CStarAlgebra.exists_sum_four_nonneg a
    simp [map_sum, map_smul, fun i => hnonneg (hy i)]

/-- Unfolding lemma for the completely positive order on `A →CP B`. -/
theorem le_def {ψ φ : A →CP B} :
    ψ ≤ φ ↔ ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A), 0 ≤ M → M.map ψ ≤ M.map φ :=
  Iff.rfl

instance instOrderBot : OrderBot (A →CP B) where
  bot := 0
  bot_le φ _ M hM := by
    have h0 : M.map (0 : A →CP B) = 0 := by ext; rfl
    exact h0 ▸ φ.map_cstarMatrix_nonneg M hM

@[simp] theorem bot_eq_zero : (⊥ : A →CP B) = 0 := (rfl)

/-- Every completely positive map dominates `0` in the completely positive order. -/
theorem zero_le (φ : A →CP B) : 0 ≤ φ := bot_le

instance : IsOrderedAddMonoid (A →CP B) where
  add_le_add_left ψ φ h χ k M hM := by
    have hadd (θ : A →CP B) : M.map (θ + χ) = M.map θ + M.map χ := by ext; rfl
    rw [hadd, hadd]
    exact add_le_add_left (h k M hM) (M.map χ)

/-- In the completely positive order, `ψ ≤ φ` if and only if `φ = ψ + θ` for some completely
positive map `θ` (namely `φ - ψ` as a linear map). -/
theorem le_iff_exists_add {ψ φ : A →CP B} :
    ψ ≤ φ ↔ ∃ θ : A →CP B, φ = ψ + θ := by
  refine ⟨fun h => ⟨subOfMatrixLe h, by ext a; simp [subOfMatrixLe]⟩, ?_⟩
  rintro ⟨θ, rfl⟩ k M hM
  have hadd : M.map (ψ + θ) = M.map ψ + M.map θ := by ext; rfl
  exact hadd ▸ le_add_of_nonneg_right (θ.map_cstarMatrix_nonneg M hM)

/-- If `ψ ≤ φ` in the completely positive order, then `ψ` is dominated entrywise by `φ` on positive
matrices indexed by any finite type. -/
theorem map_cstarMatrix_le_of_le {n : Type*} [Fintype n] {ψ φ : A →CP B} (h : ψ ≤ φ)
    {M : CStarMatrix n n A} (hM : 0 ≤ M) : M.map ψ ≤ M.map φ := by
  obtain ⟨θ, rfl⟩ := le_iff_exists_add.mp h
  have hadd : M.map (ψ + θ) = M.map ψ + M.map θ := by ext; rfl
  exact hadd ▸ le_add_of_nonneg_right (θ.map_cstarMatrix_nonneg M hM)

/-- If `ψ ≤ φ` in the completely positive order, then `ψ a ≤ φ a` for every positive `a`. -/
theorem apply_le_of_le {ψ φ : A →CP B} (h : ψ ≤ φ) {a : A} (ha : 0 ≤ a) : ψ a ≤ φ a := by
  obtain ⟨θ, rfl⟩ := le_iff_exists_add.mp h
  simpa using le_add_of_nonneg_right (a := ψ a) (_root_.map_nonneg θ ha)

/-- Conjugation `a ↦ star b * a * b` on a C⋆-algebra as a completely positive map. -/
def conj (b : A) : A →CP A where
  toLinearMap :=
    { toFun a := star b * a * b
      map_add' _ _ := by simp [mul_add, add_mul]
      map_smul' _ _ := by simp [mul_smul_comm, smul_mul_assoc] }
  map_cstarMatrix_nonneg' _ M hM := by
    rw [CStarMatrix.nonneg_iff_forall_sum_nonneg]
    intro x
    simpa [CStarMatrix.map_apply, mul_assoc] using
      CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hM fun i => b * x i

@[simp] theorem conj_apply (b a : A) : conj b a = star b * a * b := (rfl)

end Basic

section HilbertSpace

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Operator compression `S ↦ V† ∘L S ∘L V` between Hilbert-space operator algebras is completely
positive. Every Stinespring dilation `(K, π, V)` factors its completely positive map as
`(conjCLM V).comp π`. -/
def conjCLM (V : H →L[ℂ] K) : (K →L[ℂ] K) →CP (H →L[ℂ] H) where
  toLinearMap :=
    { toFun S := V.adjoint ∘L S ∘L V
      map_add' _ _ := by simp [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
      map_smul' _ _ := by simp [ContinuousLinearMap.smul_comp] }
  map_cstarMatrix_nonneg' _ M hM := by
    rw [CStarMatrix.nonneg_iff_forall_sum_inner_nonneg]
    intro ξ
    simpa [CStarMatrix.map_apply, ContinuousLinearMap.adjoint_inner_right] using
      CStarMatrix.sum_inner_nonneg hM fun i => V (ξ i)

@[simp] theorem conjCLM_apply (V : H →L[ℂ] K) (S : K →L[ℂ] K) :
    conjCLM V S = V.adjoint ∘L S ∘L V := (rfl)

end HilbertSpace

section KadisonSchwarz

variable {D E B : Type*}
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Kadison–Schwarz inequality** (subunital form): if `φ : D →CP E` satisfies `φ 1 ≤ 1`, then
`star (φ a) * φ a ≤ φ (star a * a)` for every `a : D`. -/
theorem star_map_mul_map_le_of_map_one_le (φ : D →CP E) (hφ : φ 1 ≤ 1) (a : D) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  have hquad := CStarMatrix.nonneg_iff_forall_sum_nonneg.mp
    (φ.map_cstarMatrix_nonneg _ (CStarMatrix.gram_nonneg ![1, a])) ![-φ a, 1]
  have hstar1 : star (φ 1) = φ 1 :=
    (IsSelfAdjoint.of_nonneg (_root_.map_nonneg φ zero_le_one)).star_eq
  simp only [Fin.sum_univ_two, CStarMatrix.map_apply, CStarMatrix.gram_apply,
    CStarModule.unop_inner_mulOpposite, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, star_neg, star_one, mul_one, one_mul, mul_neg, neg_mul, neg_neg,
    map_star, hstar1] at hquad
  have hconj : star (φ a) * φ 1 * φ a ≤ star (φ a) * φ a := by
    simpa using star_left_conjugate_le_conjugate hφ (φ a)
  have hsub :
      (star (φ a) * φ 1 * φ a + -(star (φ a) * φ a)) + (-(star (φ a) * φ a) + φ (star a * a)) ≤
        φ (star a * a) - star (φ a) * φ a := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_right hconj (-(star (φ a) * φ a) + (-(star (φ a) * φ a) + φ (star a * a)))
  exact sub_nonneg.mp (hquad.trans hsub)

/-- **Kadison–Schwarz inequality** (unital form): if `φ : D →CP E` is unital (`φ 1 = 1`), then
`star (φ a) * φ a ≤ φ (star a * a)` for every `a : D`. -/
theorem star_map_mul_map_le (φ : D →CP E) (hφ : φ 1 = 1) (a : D) :
    star (φ a) * φ a ≤ φ (star a * a) :=
  φ.star_map_mul_map_le_of_map_one_le hφ.le a

/-- **Kadison–Schwarz inequality** (general form): for any completely positive map `φ : D →CP B`
from a unital C⋆-algebra `D` into a (possibly nonunital) C⋆-algebra `B`,
`star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a)` for every `a : D`. -/
theorem star_map_mul_map_le_norm_map_one_smul (φ : D →CP B) (a : D) :
    star (φ a) * φ a ≤ ‖φ 1‖ • φ (star a * a) := by
  let ι : B →CP B⁺¹ := (Unitization.inrNonUnitalStarAlgHom ℂ B : B →CP B⁺¹)
  by_cases h0 : φ 1 = 0
  · have hzero : φ (star a * a) = 0 := by
      have hle : star a * a ≤ (‖star a * a‖ : ℝ) • (1 : D) := by
        rw [← Algebra.algebraMap_eq_smul_one]
        exact (IsSelfAdjoint.star_mul_self a).le_algebraMap_norm_self
      exact le_antisymm
        ((OrderHomClass.mono φ hle).trans_eq (by simp [← Complex.coe_smul, h0]))
        (_root_.map_nonneg φ (star_mul_self_nonneg a))
    have hks := (ι.comp φ).star_map_mul_map_le_of_map_one_le (by simp [ι, h0]) a
    have hks' : ((star (φ a) * φ a : B) : B⁺¹) ≤ ((0 : B) : B⁺¹) := by
      simpa [ι, Unitization.inrNonUnitalStarAlgHom_apply, hzero] using hks
    simpa [h0, hzero] using Unitization.inr_le_inr_iff.mp hks'
  · have hnorm : (0 : ℝ≥0) < ‖φ 1‖₊ := nnNorm_pos.mpr h0
    let c : ℝ≥0 := ‖φ 1‖₊⁻¹
    let ψ : D →CP B⁺¹ := c • (ι.comp φ)
    have hψ1 : ψ 1 ≤ 1 := by
      have hcφ1 : ((c • φ 1 : B) : B⁺¹) ∈ Set.Icc (0 : B⁺¹) 1 := by
        rw [CStarAlgebra.inr_mem_Icc_iff_norm_le]
        exact ⟨smul_nonneg c.coe_nonneg (_root_.map_nonneg φ zero_le_one), by
          simp [c, NNReal.smul_def, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]⟩
      simpa [ψ, ι, Unitization.inrNonUnitalStarAlgHom_apply, Unitization.inr_smul,
        NNReal.smul_def] using hcφ1.2
    have hksB : (c * c) • (star (φ a) * φ a) ≤ c • φ (star a * a) := by
      rw [← Unitization.inr_le_inr_iff]
      simpa [ψ, ι, Unitization.inrNonUnitalStarAlgHom_apply, NNReal.smul_def, ← Complex.coe_smul,
        Unitization.inr_smul, smul_mul_assoc, mul_smul_comm, smul_smul] using
        ψ.star_map_mul_map_le_of_map_one_le hψ1 a
    have hmul := smul_le_smul_of_nonneg_left hksB (‖φ 1‖₊ * ‖φ 1‖₊).coe_nonneg
    rw [← NNReal.smul_def, ← NNReal.smul_def, smul_smul, smul_smul] at hmul
    have hcc : (‖φ 1‖₊ * ‖φ 1‖₊) * (c * c) = 1 := by
      rw [mul_mul_mul_comm, mul_inv_cancel₀ hnorm.ne', mul_one]
    have hc1 : (‖φ 1‖₊ * ‖φ 1‖₊) * c = ‖φ 1‖₊ := by
      rw [mul_assoc, mul_inv_cancel₀ hnorm.ne', mul_one]
    simpa [hcc, hc1, NNReal.smul_def] using hmul

/-- For a completely positive map `φ : D →CP B` on a unital C⋆-algebra `D`,
`‖φ a‖ ≤ ‖φ 1‖ * ‖a‖` for every `a : D`. -/
theorem norm_apply_le_norm_map_one_mul (φ : D →CP B) (a : D) :
    ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ := by
  have hle_aa : star a * a ≤ (‖a‖ ^ 2 : ℝ) • (1 : D) := by
    rw [sq, ← CStarRing.norm_star_mul_self, ← Algebra.algebraMap_eq_smul_one]
    exact (IsSelfAdjoint.star_mul_self a).le_algebraMap_norm_self
  have hnorm_aa : ‖φ (star a * a)‖ ≤ ‖a‖ ^ 2 * ‖φ 1‖ :=
    (CStarAlgebra.norm_le_norm_of_le_of_nonneg (OrderHomClass.mono φ hle_aa)
      (_root_.map_nonneg φ (star_mul_self_nonneg a))).trans_eq
      (by simp [← Complex.coe_smul, norm_smul])
  have hsq : ‖φ a‖ ^ 2 ≤ (‖φ 1‖ * ‖a‖) ^ 2 := by
    calc ‖φ a‖ ^ 2 = ‖star (φ a) * φ a‖ := by rw [CStarRing.norm_star_mul_self, sq]
      _ ≤ ‖‖φ 1‖ • φ (star a * a)‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
          (φ.star_map_mul_map_le_norm_map_one_smul a) (star_mul_self_nonneg (φ a))
      _ = ‖φ 1‖ * ‖φ (star a * a)‖ := by simp [norm_smul]
      _ ≤ ‖φ 1‖ * (‖a‖ ^ 2 * ‖φ 1‖) := by gcongr
      _ = (‖φ 1‖ * ‖a‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- A completely positive map `φ : D →CP B` on a unital C⋆-algebra attains its operator norm at the
unit: `‖φ.toContinuousLinearMap‖ = ‖φ 1‖`. -/
@[simp] theorem norm_toContinuousLinearMap (φ : D →CP B) :
    ‖φ.toContinuousLinearMap‖ = ‖φ 1‖ := by
  refine le_antisymm
    (φ.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun a =>
      by simpa using φ.norm_apply_le_norm_map_one_mul a) ?_
  rcases subsingleton_or_nontrivial D with hD | hD
  · simp [Subsingleton.elim (1 : D) 0]
  · simpa using φ.toContinuousLinearMap.le_opNorm 1

/-- A subunital completely positive map (`φ 1 ≤ 1`) between unital C⋆-algebras is contractive. -/
theorem norm_toContinuousLinearMap_le_one_of_map_one_le (φ : D →CP E) (hφ : φ 1 ≤ 1) :
    ‖φ.toContinuousLinearMap‖ ≤ 1 := by
  rw [φ.norm_toContinuousLinearMap]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (φ 1) (_root_.map_nonneg φ zero_le_one)).mpr hφ

end KadisonSchwarz

end CompletelyPositiveMap
