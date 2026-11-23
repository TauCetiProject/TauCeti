/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Analysis.CStarAlgebra.Exponential
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import TauCeti.Algebra.Star.Projection.Idempotent
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Unitization
import TauCeti.Analysis.CStarAlgebra.Projection.Nearby

/-!
# Rectangular Murray–von Neumann equivalence

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular matrix. The index types may differ, so this relation identifies
a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, compatibility with block sums,
orthogonal sums, unitization unitary conjugacy, and preservation by nonunital star homomorphisms,
bridge the relation to `Matrix.IsMurrayVonNeumannEquivalent`, and establish the analytic C⋆-algebra
criteria: Blackadar's algebraic equivalence theorem (`of_mul_eq`), paths (`of_path`), nearby
projections (`of_norm_sub_lt_one`), explicit stabilized unitary conjugacy (`stabilizedUnitary`,
`stabilizedUnitaryPath`, `exists_stabilized_unitary_conj`, `exists_stabilized_unitary_conj_same`),
and stabilized homotopy of equivalent projections (`exists_projection_path_to_opposite_corner`,
`exists_projection_path_to_same_corner`).

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998, §4.6
  and §5.1.
-/

public section

open scoped CStarAlgebra ComplexOrder Matrix NNReal Real unitInterval Ring

namespace CStarMatrix

variable {A B m n k l : Type*} [Fintype m] [Fintype n] [Fintype k] [Fintype l]

section Algebraic

variable [NonUnitalSemiring A] [StarRing A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A} {r : CStarMatrix k k A}

/-- Two matrix projections are Murray–von Neumann equivalent when a rectangular matrix has
them as its initial and final projections. The projection conditions are part of the relation. -/
def MurrayVonNeumannEquiv (p : CStarMatrix m m A) (q : CStarMatrix n n A) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q

/-- `CStarMatrix.MurrayVonNeumannEquiv` agrees with `Matrix.IsMurrayVonNeumannEquivalent` on the
underlying matrices. -/
theorem murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent :
    MurrayVonNeumannEquiv p q ↔
      Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  refine ⟨fun ⟨hp, hq, v, hv, hv'⟩ => ?_, fun ⟨hp, hq, v, hv, hv'⟩ => ?_⟩
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ofMatrix.symm v, ?_, ?_⟩
    · simpa only [IsIdempotentElem, ofMatrix_symm_mul] using
        congrArg ofMatrix.symm hp.isIdempotentElem.eq
    · simpa only [IsSelfAdjoint, ofMatrix_symm_star, ← Matrix.star_eq_conjTranspose] using
        congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq
    · simpa only [IsIdempotentElem, ofMatrix_symm_mul] using
        congrArg ofMatrix.symm hq.isIdempotentElem.eq
    · simpa only [IsSelfAdjoint, ofMatrix_symm_star, ← Matrix.star_eq_conjTranspose] using
        congrArg ofMatrix.symm hq.isSelfAdjoint.star_eq
    · simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hv
    · simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hv'
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ofMatrix v, ?_, ?_⟩
    · simpa only [IsIdempotentElem, ofMatrix_mul, Equiv.apply_symm_apply] using
        congrArg ofMatrix hp.isIdempotentElem.eq
    · simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ofMatrix_conjTranspose,
        ← star_eq_conjTranspose, Equiv.apply_symm_apply] using
        congrArg ofMatrix hp.isSelfAdjoint.star_eq
    · simpa only [IsIdempotentElem, ofMatrix_mul, Equiv.apply_symm_apply] using
        congrArg ofMatrix hq.isIdempotentElem.eq
    · simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose, ofMatrix_conjTranspose,
        ← star_eq_conjTranspose, Equiv.apply_symm_apply] using
        congrArg ofMatrix hq.isSelfAdjoint.star_eq
    · simpa only [← ofMatrix_conjTranspose, ← ofMatrix_mul, Equiv.apply_symm_apply] using
        congrArg ofMatrix hv
    · simpa only [← ofMatrix_conjTranspose, ← ofMatrix_mul, Equiv.apply_symm_apply] using
        congrArg ofMatrix hv'

namespace MurrayVonNeumannEquiv

/-- The initial matrix of a Murray–von Neumann equivalence is a projection. -/
theorem isStarProjection_left (h : MurrayVonNeumannEquiv p q) : IsStarProjection p :=
  h.1

/-- The final matrix of a Murray–von Neumann equivalence is a projection. -/
theorem isStarProjection_right (h : MurrayVonNeumannEquiv p q) : IsStarProjection q :=
  h.2.1

/-- Extract a rectangular implementing matrix. -/
theorem exists_matrix (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  h.2.2

/-- Every matrix projection is Murray–von Neumann equivalent to itself. -/
protected theorem refl (hp : IsStarProjection p) : MurrayVonNeumannEquiv p p :=
  ⟨hp, hp, p, by simpa only [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] using
    hp.isIdempotentElem.eq, by simpa only [← star_eq_conjTranspose,
      hp.isSelfAdjoint.star_eq] using hp.isIdempotentElem.eq⟩

/-- Rectangular Murray–von Neumann equivalence is symmetric. -/
protected theorem symm (h : MurrayVonNeumannEquiv p q) : MurrayVonNeumannEquiv q p := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  exact ⟨hq, hp, v.conjTranspose, by simpa using hv', by simpa using hv⟩

/-- Zero projections of any two finite sizes are equivalent. -/
protected theorem zero : MurrayVonNeumannEquiv (0 : CStarMatrix m m A)
    (0 : CStarMatrix n n A) :=
  ⟨.zero _, .zero _, 0, by simp, by simp⟩

/-- Block-diagonal sums of equivalent projections are equivalent. -/
theorem fromBlocks {p' : CStarMatrix k k A} {q' : CStarMatrix l l A}
    (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv p' q') :
    MurrayVonNeumannEquiv (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (ofMatrix.symm p')))
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm q) 0 0 (ofMatrix.symm q'))) := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  obtain ⟨hp', hq', w, hw, hw'⟩ := h'
  refine ⟨⟨hp.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ hp'.isIdempotentElem,
    hp.isSelfAdjoint.isHermitian.fromBlocks (by simp) hp'.isSelfAdjoint.isHermitian⟩,
    ⟨hq.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ hq'.isIdempotentElem,
      hq.isSelfAdjoint.isHermitian.fromBlocks (by simp) hq'.isSelfAdjoint.isHermitian⟩,
    ofMatrix (Matrix.fromBlocks (ofMatrix.symm v) 0 0 (ofMatrix.symm w)), ?_, ?_⟩
  · apply ofMatrix.symm.injective
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      using congrArg₂ (fun x y => Matrix.fromBlocks x 0 0 y)
        (congrArg ofMatrix.symm hv) (congrArg ofMatrix.symm hw)
  · apply ofMatrix.symm.injective
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      using congrArg₂ (fun x y => Matrix.fromBlocks x 0 0 y)
        (congrArg ofMatrix.symm hv') (congrArg ofMatrix.symm hw')

/-- A nonunital star ring homomorphism preserves rectangular equivalence entrywise. -/
theorem map [NonUnitalSemiring B] [StarRing B] {F : Type*} [FunLike F A B]
    [NonUnitalRingHomClass F A B] [StarHomClass F A B]
    (h : MurrayVonNeumannEquiv p q) (f : F) :
    MurrayVonNeumannEquiv (p.map f) (q.map f) := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  have hpf : ofMatrix.symm (p.map f) = (ofMatrix.symm p).map f := rfl
  have hqf : ofMatrix.symm (q.map f) = (ofMatrix.symm q).map f := rfl
  have hvf : ofMatrix.symm (v.map f) = (ofMatrix.symm v).map f := rfl
  have hf : Function.Semiconj f star star := map_star f
  refine ⟨isStarProjection_iff'.mpr ⟨?_, ?_⟩, isStarProjection_iff'.mpr ⟨?_, ?_⟩, v.map f, ?_,
    ?_⟩ <;> apply ofMatrix.symm.injective
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hp.isIdempotentElem.eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hq.isIdempotentElem.eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hq.isSelfAdjoint.star_eq)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hv)
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_conjTranspose, hpf, hqf, hvf,
      Matrix.map_mul, Matrix.conjTranspose_map f hf] using
      congrArg (Matrix.map · f) (congrArg ofMatrix.symm hv')

/-- Padding a projection by a zero block does not change its rectangular equivalence class. -/
theorem pad_zero (hp : IsStarProjection p) :
    MurrayVonNeumannEquiv p
      (ofMatrix (Matrix.fromBlocks (ofMatrix.symm p) 0 0 (0 : Matrix k k A))) := by
  have hsa : (ofMatrix.symm p)ᴴ = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_star] using congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq
  have hid : ofMatrix.symm p * ofMatrix.symm p = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_mul] using congrArg ofMatrix.symm hp.isIdempotentElem.eq
  refine ⟨hp, ⟨hp.isIdempotentElem.fromBlocks_zero₁₂_zero₂₁ .zero,
    hp.isSelfAdjoint.isHermitian.fromBlocks (by simp) Matrix.isHermitian_zero⟩,
    ofMatrix (Matrix.fromRows (ofMatrix.symm p) (0 : Matrix k m A)), ?_, ?_⟩ <;>
    apply ofMatrix.symm.injective
  · simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_zero, hsa]
    ext i j
    simpa [Matrix.mul_apply] using congrFun (congrFun hid i) j
  · simp only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.conjTranspose_zero, hsa]
    ext (i | i) (j | j)
    · simpa [Matrix.mul_apply] using congrFun (congrFun hid i) j
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]
    · simp [Matrix.mul_apply]

/-- A Murray–von Neumann equivalence is implemented by a matrix supported on its initial
projection. -/
theorem exists_matrix_mul_eq_self (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A,
      v.conjTranspose * v = p ∧ v * v.conjTranspose = q ∧ v * p = v := by
  obtain ⟨hp, hq, v, hv, hv'⟩ := h
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hpc : p.conjTranspose = p := by rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  refine ⟨v * p, ?_, ?_, by rw [mul_assoc_rectangular, hpp]⟩
  · calc
      _ = p * (v.conjTranspose * v) * p := by
        simp only [conjTranspose_mul, hpc, mul_assoc_rectangular]
      _ = p := by rw [hv, hpp, hpp]
  · calc
      _ = v * (p * p) * v.conjTranspose := by
        simp only [conjTranspose_mul, hpc, mul_assoc_rectangular]
      _ = (v * v.conjTranspose) * (v * v.conjTranspose) := by
        rw [hpp, ← hv]
        simp only [mul_assoc_rectangular]
      _ = q := by rw [hv', hq.isIdempotentElem.eq]

/-- Rectangular Murray–von Neumann equivalence is transitive. -/
protected theorem trans (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv q r) :
    MurrayVonNeumannEquiv p r := by
  obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
  obtain ⟨w, hw, hw', hwq⟩ := h'.exists_matrix_mul_eq_self
  have hqv : q * v = v := by
    rw [← hv', mul_assoc_rectangular, hv, hvp]
  refine ⟨h.isStarProjection_left, h'.isStarProjection_right, w * v, ?_, ?_⟩
  · calc
      _ = v.conjTranspose * (w.conjTranspose * w) * v := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = v.conjTranspose * v := by rw [hw, mul_assoc_rectangular, hqv]
      _ = p := hv
  · calc
      _ = w * (v * v.conjTranspose) * w.conjTranspose := by
        simp only [conjTranspose_mul, mul_assoc_rectangular]
      _ = w * w.conjTranspose := by rw [hv', hwq]
      _ = r := hw'

end MurrayVonNeumannEquiv

/-- The witness criterion for Murray–von Neumann equivalence of given projections. -/
theorem murrayVonNeumannEquiv_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_matrix, fun h => ⟨hp, hq, h⟩⟩

/-- Reflexivity characterizes the matrices on which the relation is defined. -/
@[simp]
theorem murrayVonNeumannEquiv_self_iff : MurrayVonNeumannEquiv p p ↔ IsStarProjection p :=
  ⟨MurrayVonNeumannEquiv.isStarProjection_left, MurrayVonNeumannEquiv.refl⟩

/-- For equal matrix sizes, two matrices are Murray–von Neumann equivalent if and only if they
are the initial and final projections of some partial isometry. -/
theorem murrayVonNeumannEquiv_iff_exists_partialIsometry {q : CStarMatrix m m A} :
    MurrayVonNeumannEquiv p q ↔
      ∃ v : CStarMatrix m m A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧
        v * star v = q := by
  constructor
  · intro h
    obtain ⟨v, hv, hv', hvp⟩ := h.exists_matrix_mul_eq_self
    simp only [← star_eq_conjTranspose] at hv hv'
    refine ⟨v, ?_, hv, hv'⟩
    rw [TauCeti.isPartialIsometry_iff, mul_assoc, hv]
    exact hvp
  · rintro ⟨v, hv, rfl, rfl⟩
    exact ⟨hv.isStarProjection_star_mul_self, hv.isStarProjection_mul_star_self, v,
      by rw [star_eq_conjTranspose], by rw [star_eq_conjTranspose]⟩

/-- Only the zero projection is equivalent to a zero projection, in any matrix size. -/
@[simp]
theorem murrayVonNeumannEquiv_zero_iff :
    MurrayVonNeumannEquiv p (0 : CStarMatrix n n A) ↔ p = 0 := by
  refine ⟨?_, fun h => h ▸ .zero⟩
  rintro ⟨hp, _, v, hv, hv'⟩
  calc
    p = p * p := hp.isIdempotentElem.eq.symm
    _ = v.conjTranspose * (v * v.conjTranspose) * v := by
      rw [← hv]
      simp only [mul_assoc_rectangular]
    _ = 0 := by rw [hv', CStarMatrix.mul_zero, CStarMatrix.zero_mul]

/-- Only zero is equivalent to the zero projection on the initial side. -/
@[simp]
theorem zero_murrayVonNeumannEquiv_iff :
    MurrayVonNeumannEquiv (0 : CStarMatrix n n A) p ↔ p = 0 :=
  ⟨fun h => murrayVonNeumannEquiv_zero_iff.mp h.symm,
    fun h => h ▸ MurrayVonNeumannEquiv.zero⟩

end Algebraic

private theorem unitary_mul_proj_witness [Semiring B] [StarRing B] [DecidableEq n]
    {p : CStarMatrix n n B} (hp : IsStarProjection p) (u : unitary (CStarMatrix n n B)) :
    ((u : CStarMatrix n n B) * p).conjTranspose * ((u : CStarMatrix n n B) * p) = p ∧
      ((u : CStarMatrix n n B) * p) * ((u : CStarMatrix n n B) * p).conjTranspose =
        (u : CStarMatrix n n B) * p * star (u : CStarMatrix n n B) := by
  rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq]
  refine ⟨?_, ?_⟩
  · simp only [mul_assoc, ← mul_assoc (star (u : CStarMatrix n n B)), Unitary.coe_star_mul_self,
      one_mul, hp.isIdempotentElem.eq]
  · simp only [mul_assoc, ← mul_assoc p, hp.isIdempotentElem.eq]

/-- Unitary conjugacy implies Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_unitary_conj [Semiring B] [StarRing B] [DecidableEq m]
    {p : CStarMatrix m m B} (hp : IsStarProjection p) (u : unitary (CStarMatrix m m B)) :
    MurrayVonNeumannEquiv p ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) := by
  have hq : IsStarProjection ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) :=
    ⟨by simp only [IsIdempotentElem, mul_assoc,
        ← mul_assoc (star (u : CStarMatrix m m B)), Unitary.coe_star_mul_self,
        one_mul, ← mul_assoc p, hp.isIdempotentElem.eq], hp.isSelfAdjoint.conjugate u⟩
  obtain ⟨hv1, hv2⟩ := unitary_mul_proj_witness hp u
  exact ⟨hp, hq, (u : CStarMatrix m m B) * p, hv1, hv2⟩

/-! ### Orthogonal sums and unitization conjugacy -/

section OrthogonalSum

/-- Murray–von Neumann equivalence is compatible with sums of orthogonal star projections. -/
theorem MurrayVonNeumannEquiv.add [NonUnitalSemiring A] [StarRing A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : MurrayVonNeumannEquiv p₁ q₁) (h₂ : MurrayVonNeumannEquiv p₂ q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    MurrayVonNeumannEquiv (p₁ + p₂) (q₁ + q₂) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent] at h₁ h₂ ⊢
  simp only [ofMatrix_symm_add]
  refine h₁.add h₂ ?_ ?_
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_zero] using congrArg ofMatrix.symm hp
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_zero] using congrArg ofMatrix.symm hq

end OrthogonalSum

section UnitizationConjugacy

/-- Unitary conjugacy in `CStarMatrix n n A⁺¹` implies Murray–von Neumann equivalence in
`CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_matrix_unitization_unitary_conj [DecidableEq n]
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A] {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A⁺¹))
    (h : (u : CStarMatrix n n A⁺¹) * p.map (Unitization.inr : A → A⁺¹) *
      star (u : CStarMatrix n n A⁺¹) = q.map (Unitization.inr : A → A⁺¹)) :
    MurrayVonNeumannEquiv p q := by
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  let mapι := CStarMatrix.mapₙₐ (n := n) ι
  have hmap_inr (M : CStarMatrix n n A) : mapι M = M.map (Unitization.inr : A → A⁺¹) := rfl
  have hmap_ι (M : CStarMatrix n n A) : mapι M = M.map ι := rfl
  let p' : CStarMatrix n n A⁺¹ := mapι p
  let q' : CStarMatrix n n A⁺¹ := mapι q
  let v' : CStarMatrix n n A⁺¹ := (u : CStarMatrix n n A⁺¹) * p'
  have hp' : IsStarProjection p' := hp.map mapι
  have hconj : (u : CStarMatrix n n A⁺¹) * p' * star (u : CStarMatrix n n A⁺¹) = q' := by
    rw [show p' = p.map Unitization.inr from hmap_inr p,
      show q' = q.map Unitization.inr from hmap_inr q]
    exact h
  have hq' : IsStarProjection q' := by
    rw [← hconj]
    simpa only [Unitary.conjStarAlgAut_apply] using
      hp'.map (Unitary.conjStarAlgAut ℂ (CStarMatrix n n A⁺¹) u)
  have hinj : Function.Injective mapι :=
    CStarMatrix.map_injective (Unitization.inr_injective (R := ℂ) (A := A))
  have hq : IsStarProjection q := hq'.of_map_injective hinj
  have hv'_fst : v'.map (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), show p' = p.map ι from hmap_ι p,
      map_fstHom_map_inr p, mul_zero]
  let v : CStarMatrix n n A := v'.map fun x : A⁺¹ => x.snd
  have hv_inr : mapι v = v' := map_inr_map_snd_of_map_fstHom_eq_zero hv'_fst
  obtain ⟨hv1, hv2⟩ := unitary_mul_proj_witness hp' u
  refine ⟨hp, hq, v, hinj ?_, hinj ?_⟩
  · rw [hmap_ι, CStarMatrix.map_mul ι, map_conjTranspose ι, ← hmap_ι, hv_inr]
    exact hv1
  · rw [hmap_ι, CStarMatrix.map_mul ι, map_conjTranspose ι, ← hmap_ι, hv_inr]
    exact hv2.trans hconj

/-- Unitary conjugacy in the unitization `(CStarMatrix n n A)⁺¹` implies Murray–von Neumann
equivalence in `CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_unitization_unitary_conj
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A] {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)⁺¹)
    (h : (u : (CStarMatrix n n A)⁺¹) * (p : (CStarMatrix n n A)⁺¹) *
      star (u : (CStarMatrix n n A)⁺¹) = (q : (CStarMatrix n n A)⁺¹)) :
    MurrayVonNeumannEquiv p q := by
  classical
  let φ : (CStarMatrix n n A)⁺¹ →⋆ₐ[ℂ] CStarMatrix n n A⁺¹ :=
    Unitization.starLift (CStarMatrix.mapₙₐ (n := n) (Unitization.inrNonUnitalStarAlgHom ℂ A))
  let φₘ : (CStarMatrix n n A)⁺¹ →⋆* CStarMatrix n n A⁺¹ :=
    { toFun := φ, map_one' := map_one φ, map_mul' := map_mul φ, map_star' := map_star φ }
  refine MurrayVonNeumannEquiv.of_matrix_unitization_unitary_conj hp (Unitary.map φₘ u) ?_
  have hφ (M : CStarMatrix n n A) : φ (M : (CStarMatrix n n A)⁺¹) = M.map Unitization.inr := by
    simp [φ, Unitization.starLift_apply_apply]
    rfl
  rw [Unitary.coe_map]
  change φ ↑u * p.map Unitization.inr * star (φ ↑u) = q.map Unitization.inr
  simpa only [map_mul, map_star, hφ] using congrArg φ h

end UnitizationConjugacy

/-! ### Algebraic equivalence implies Murray–von Neumann equivalence -/

section AlgebraicEquiv

private theorem normalize_mul_eq {B m n : Type*} [Fintype m] [Fintype n] [NonUnitalSemiring B]
    [StarRing B] {p : CStarMatrix m m B} {q : CStarMatrix n n B}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x₀ : CStarMatrix m n B} {y₀ : CStarMatrix n m B}
    (hxy : x₀ * y₀ = p) (hyx : y₀ * x₀ = q) :
    ∃ (x : CStarMatrix m n B) (y : CStarMatrix n m B),
      x * y = p ∧ y * x = q ∧ p * x = x ∧ x * q = x ∧ q * y = y ∧ y * p = y := by
  refine ⟨p * x₀ * q, q * y₀ * p, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc (p * x₀ * q) * (q * y₀ * p) = p * x₀ * (q * q) * y₀ * p := by
          simp only [CStarMatrix.mul_assoc_rectangular]
      _ = p * (x₀ * y₀) * (x₀ * y₀) * p := by
          rw [hq.isIdempotentElem.eq, ← hyx]; simp only [CStarMatrix.mul_assoc_rectangular]
      _ = p := by
          rw [hxy, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq, hp.isIdempotentElem.eq]
  · calc (q * y₀ * p) * (p * x₀ * q) = q * y₀ * (p * p) * x₀ * q := by
          simp only [CStarMatrix.mul_assoc_rectangular]
      _ = q * (y₀ * x₀) * (y₀ * x₀) * q := by
          rw [hp.isIdempotentElem.eq, ← hxy]; simp only [CStarMatrix.mul_assoc_rectangular]
      _ = q := by
          rw [hyx, hq.isIdempotentElem.eq, hq.isIdempotentElem.eq, hq.isIdempotentElem.eq]
  · simp only [← CStarMatrix.mul_assoc_rectangular, hp.isIdempotentElem.eq]
  · simp only [CStarMatrix.mul_assoc_rectangular, hq.isIdempotentElem.eq]
  · simp only [← CStarMatrix.mul_assoc_rectangular, hq.isIdempotentElem.eq]
  · simp only [CStarMatrix.mul_assoc_rectangular, hp.isIdempotentElem.eq]

private theorem normalized_mul_eq_witness {B m n : Type*} [Fintype m] [Fintype n]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {p : CStarMatrix m m B} {q : CStarMatrix n n B}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x : CStarMatrix m n B} {y : CStarMatrix n m B}
    (hxy : x * y = p) (hyx : y * x = q)
    (hpx : p * x = x) (hxq : x * q = x) (hqy : q * y = y) :
    ∃ w : CStarMatrix n m B, w.conjTranspose * w = p ∧ w * w.conjTranspose = q ∧ w * p = w := by
  classical
  have hqs : q.conjTranspose = q := by
    simpa only [← star_eq_conjTranspose] using hq.isSelfAdjoint.star_eq
  have hps : p.conjTranspose = p := by
    simpa only [← star_eq_conjTranspose] using hp.isSelfAdjoint.star_eq
  have hxsp : x.conjTranspose * p = x.conjTranspose := by
    simpa only [conjTranspose_mul, hps] using congrArg conjTranspose hpx
  have hqxs : q * x.conjTranspose = x.conjTranspose := by
    simpa only [conjTranspose_mul, hqs] using congrArg conjTranspose hxq
  let c : CStarMatrix n n B := (1 - q) + x.conjTranspose * x
  let b : CStarMatrix n n B := (1 - q) + y * y.conjTranspose
  have hx_1q : x * (1 - q) = 0 := by
    simp only [CStarMatrix.mul_sub, CStarMatrix.mul_one, hxq, sub_self]
  have h1q_y : (1 - q) * y = 0 := by
    simp only [CStarMatrix.sub_mul, CStarMatrix.one_mul, hqy, sub_self]
  have hdiag : (x.conjTranspose * x) * (y * y.conjTranspose) = q := by
    calc (x.conjTranspose * x) * (y * y.conjTranspose)
        = x.conjTranspose * (x * y) * y.conjTranspose := by
          simp only [CStarMatrix.mul_assoc_rectangular]
      _ = (y * x).conjTranspose := by rw [hxy, hxsp, ← conjTranspose_mul]
      _ = q := by rw [hyx, hqs]
  have hcb : c * b = 1 := by
    have h1 : x.conjTranspose * x * (1 - q) = 0 := by
      rw [CStarMatrix.mul_assoc_rectangular, hx_1q, CStarMatrix.mul_zero]
    have h2 : (1 - q) * (y * y.conjTranspose) = 0 := by
      rw [← CStarMatrix.mul_assoc_rectangular, h1q_y, CStarMatrix.zero_mul]
    simp [c, b, add_mul, mul_add, hq.one_sub.isIdempotentElem.eq, h1, h2, hdiag]
  have hc_sa : IsSelfAdjoint c :=
    hq.one_sub.isSelfAdjoint.add (by simp [isSelfAdjoint_iff, star_eq_conjTranspose])
  have hb_sa : IsSelfAdjoint b :=
    hq.one_sub.isSelfAdjoint.add (by simp [isSelfAdjoint_iff, star_eq_conjTranspose])
  have hbc : b * c = 1 := by
    simpa only [star_mul, hc_sa.star_eq, hb_sa.star_eq, star_one] using congrArg star hcb
  have hc_nonneg : 0 ≤ c :=
    add_nonneg hq.one_sub.nonneg (CStarMatrix.conjTranspose_mul_self_nonneg x)
  let s : CStarMatrix n n B := CFC.sqrt c
  have hs_pos : IsStrictlyPositive s :=
    (IsUnit.isStrictlyPositive ⟨⟨c, b, hcb, hbc⟩, rfl⟩ hc_nonneg).sqrt
  have hss : s * s = c := CFC.sqrt_mul_sqrt_self c hc_nonneg
  have hcq : c * q = x.conjTranspose * x := by
    simp only [c, add_mul, sub_mul, one_mul, hq.isIdempotentElem.eq, sub_self, zero_add,
      CStarMatrix.mul_assoc_rectangular, hxq]
  have hcomm_cq : Commute c q := hcq.trans (by
    simp only [c, mul_add, mul_sub, mul_one, hq.isIdempotentElem.eq, sub_self, zero_add,
      ← CStarMatrix.mul_assoc_rectangular, hqxs])
  have hsinv_sa : s⁻¹ʳ.conjTranspose = s⁻¹ʳ := by
    rw [← star_eq_conjTranspose, ← Ring.inverse_star, hs_pos.isSelfAdjoint.star_eq]
  let w : CStarMatrix n m B := s⁻¹ʳ * x.conjTranspose
  have hw₁ : w.conjTranspose * w = p := by
    have hsinv_sq : s⁻¹ʳ * s⁻¹ʳ = b := by
      rw [← Ring.mul_inverse_rev' (Commute.refl s), hss, Ring.inverse_unit ⟨c, b, hcb, hbc⟩]; rfl
    calc w.conjTranspose * w
        = x * (s⁻¹ʳ * s⁻¹ʳ) * x.conjTranspose := by
          simp only [w, conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa,
            CStarMatrix.mul_assoc_rectangular]
      _ = x * (1 - q) * x.conjTranspose + (x * y) * (y.conjTranspose * x.conjTranspose) := by
          rw [hsinv_sq, CStarMatrix.mul_add, CStarMatrix.add_mul]
          simp only [CStarMatrix.mul_assoc_rectangular]
      _ = p := by
          rw [hx_1q, CStarMatrix.zero_mul, zero_add, ← conjTranspose_mul, hxy, hps,
            hp.isIdempotentElem.eq]
  have hw₂ : w * w.conjTranspose = q := by
    have hcomm_sq : Commute s q := hcomm_cq.cfcₙ_nnreal NNReal.sqrt
    have hxx : x.conjTranspose * x = s * q * s := by
      conv_lhs => rw [← hcq, ← hss, mul_assoc, hcomm_sq.eq, ← mul_assoc]
    calc w * w.conjTranspose
        = s⁻¹ʳ * (x.conjTranspose * x) * s⁻¹ʳ := by
          simp only [w, conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa,
            CStarMatrix.mul_assoc_rectangular]
      _ = (s⁻¹ʳ * s) * q * (s * s⁻¹ʳ) := by
          rw [hxx]; simp only [CStarMatrix.mul_assoc_rectangular]
      _ = q := by
          rw [Ring.inverse_mul_cancel _ hs_pos.isUnit, Ring.mul_inverse_cancel _ hs_pos.isUnit,
            one_mul, mul_one]
  exact ⟨w, hw₁, hw₂, by rw [CStarMatrix.mul_assoc_rectangular, hxsp]⟩

/-- **Rectangular algebraic equivalence of matrix projections implies Murray–von Neumann
equivalence** (Blackadar, Proposition 4.6.4). If `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` are star projections in a (possibly non-unital) C⋆-algebra `A` with
rectangular `x`, `y` satisfying `x * y = p` and `y * x = q`, then `p` and `q` are Murray–von
Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_mul_eq [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x : CStarMatrix m n A} {y : CStarMatrix n m A}
    (hxy : x * y = p) (hyx : y * x = q) : MurrayVonNeumannEquiv p q := by
  classical
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  let p' : CStarMatrix m m A⁺¹ := p.map ι
  let q' : CStarMatrix n n A⁺¹ := q.map ι
  have hp' : IsStarProjection p' := hp.map (CStarMatrix.mapₙₐ ι)
  have hq' : IsStarProjection q' := hq.map (CStarMatrix.mapₙₐ ι)
  obtain ⟨x', y', hx'y', hy'x', hpx', hx'q, hqy', -⟩ := normalize_mul_eq hp' hq'
    (by rw [← CStarMatrix.map_mul ι, hxy]) (by rw [← CStarMatrix.map_mul ι, hyx])
  obtain ⟨w', hw'₁, hw'₂, hw'p⟩ :=
    normalized_mul_eq_witness hp' hq' hx'y' hy'x' hpx' hx'q hqy'
  let w : CStarMatrix n m A := w'.map fun z : A⁺¹ => z.snd
  have hw_inr : w.map ι = w' := map_inr_map_snd_of_map_fstHom_eq_zero (by
    rw [← hw'p, CStarMatrix.map_mul (Unitization.fstHom ℂ A), map_fstHom_map_inr p,
      CStarMatrix.mul_zero])
  refine ⟨hp, hq, w, CStarMatrix.ext fun i j => Unitization.inr_injective (R := ℂ) ?_,
    CStarMatrix.ext fun i j => Unitization.inr_injective (R := ℂ) ?_⟩
  · simpa only [← hw_inr, ← map_conjTranspose ι, ← CStarMatrix.map_mul ι, p',
      CStarMatrix.map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply] using
      congrArg (fun M : CStarMatrix m m A⁺¹ => M i j) hw'₁
  · simpa only [← hw_inr, ← map_conjTranspose ι, ← CStarMatrix.map_mul ι, q',
      CStarMatrix.map_apply, ι, Unitization.inrNonUnitalStarAlgHom_apply] using
      congrArg (fun M : CStarMatrix n n A⁺¹ => M i j) hw'₂

end AlgebraicEquiv

/-! ### Paths of projections and stabilized unitary conjugacy -/

section PathsAndStabilization

/-- Endpoints of a norm-continuous path of matrix projections are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_path [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    MurrayVonNeumannEquiv p q := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨u, hconj, -⟩ := γ.exists_unitization_unitary_conj_of_isStarProjection hγ
  exact MurrayVonNeumannEquiv.of_unitization_unitary_conj (by simpa only [γ.source] using hγ 0)
    u hconj

/-- Nearby matrix projections (`‖p - q‖ < 1`) are Murray–von Neumann equivalent. -/
theorem MurrayVonNeumannEquiv.of_norm_sub_lt_one [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p q : CStarMatrix n n A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    MurrayVonNeumannEquiv p q := by
  obtain ⟨u, hconj, -, -⟩ :=
    IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one hp hq hpq
  exact MurrayVonNeumannEquiv.of_unitization_unitary_conj hp u hconj

/-- The stabilized self-adjoint unitary `!![1 - p, vᴴ; v, 1 - q]` built from an implementer `v`
of `p ∼ q` satisfying `v * p = v`, reusing `Matrix.fromBlocks_one_sub_mul_self_of_mul_eq`. -/
def stabilizedUnitary [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    have hpH : (ofMatrix.symm p)ᴴ = ofMatrix.symm p := by
      simpa only [ofMatrix_symm_star, ← Matrix.star_eq_conjTranspose] using
        congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq
    have hbeM : ofMatrix.symm v * ofMatrix.symm p = ofMatrix.symm v := by
      simpa only [ofMatrix_symm_mul] using congrArg ofMatrix.symm hbe
    have heaM : ofMatrix.symm p * (ofMatrix.symm v)ᴴ = (ofMatrix.symm v)ᴴ := by
      simpa only [Matrix.conjTranspose_mul, hpH] using congrArg Matrix.conjTranspose hbeM
    have hvpM : (ofMatrix.symm v)ᴴ * ofMatrix.symm v = ofMatrix.symm p := by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hvp
    have hvqM : ofMatrix.symm v * (ofMatrix.symm v)ᴴ = ofMatrix.symm q := by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hvq
    have hsa : IsSelfAdjoint (fromBlocks (1 - p) v.conjTranspose v (1 - q)) := by
      simp only [isSelfAdjoint_iff, fromBlocks_star, star_sub, star_one,
        hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, conjTranspose_conjTranspose]
    have hsq : fromBlocks (1 - p) v.conjTranspose v (1 - q) *
        fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := by
      apply ofMatrix.symm.injective
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub,
        ofMatrix_symm_one, ofMatrix_symm_conjTranspose] using
        Matrix.fromBlocks_one_sub_mul_self_of_mul_eq hvpM hvqM heaM hbeM
    exact ⟨by simpa only [hsa.star_eq] using hsq, by simpa only [hsa.star_eq] using hsq⟩⟩

/-- Underlying matrix of `CStarMatrix.stabilizedUnitary`. -/
@[simp]
theorem coe_stabilizedUnitary [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    (stabilizedUnitary hp hq hvp hvq hbe : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks (1 - p) v.conjTranspose v (1 - q) :=
  (rfl)

/-- `CStarMatrix.stabilizedUnitary` is self-adjoint. -/
theorem isSelfAdjoint_stabilizedUnitary [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    IsSelfAdjoint (stabilizedUnitary hp hq hvp hvq hbe : CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
  simp only [coe_stabilizedUnitary, isSelfAdjoint_iff, fromBlocks_star, star_sub, star_one,
    hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, conjTranspose_conjTranspose]

/-- Conjugating `p ⊕ 0` by `CStarMatrix.stabilizedUnitary` gives `0 ⊕ q`, reusing
`Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq`. -/
theorem stabilizedUnitary_conj [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    (stabilizedUnitary hp hq hvp hvq hbe : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedUnitary hp hq hvp hvq hbe : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  rw [(isSelfAdjoint_stabilizedUnitary hp hq hvp hvq hbe).star_eq, coe_stabilizedUnitary]
  apply ofMatrix.symm.injective
  have hvpM : (ofMatrix.symm v)ᴴ * ofMatrix.symm v = ofMatrix.symm p := by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hvp
  have hvqM : ofMatrix.symm v * (ofMatrix.symm v)ᴴ = ofMatrix.symm q := by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using congrArg ofMatrix.symm hvq
  have hbeM : ofMatrix.symm v * ofMatrix.symm p = ofMatrix.symm v := by
    simpa only [ofMatrix_symm_mul] using congrArg ofMatrix.symm hbe
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_one,
    ofMatrix_symm_conjTranspose, ofMatrix_symm_zero] using
    Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq hvpM hvqM hbeM

/-- Explicit continuous path in `unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)` from `1` to
`CStarMatrix.stabilizedUnitary`, constructed with `selfAdjoint.expUnitaryPathToOne` and
`Unitary.expUnitary_pi_half_one_sub`. -/
noncomputable def stabilizedUnitaryPath [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A))
      (stabilizedUnitary hp hq hvp hvq hbe) :=
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let w := stabilizedUnitary hp hq hvp hvq hbe
  let hw := isSelfAdjoint_stabilizedUnitary hp hq hvp hvq hbe
  let x : selfAdjoint (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
    ⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))),
      IsSelfAdjoint.smul (Complex.conj_ofReal π)
        (IsSelfAdjoint.smul (by simp : IsSelfAdjoint ((2 : ℂ)⁻¹)) ((IsSelfAdjoint.one _).sub hw))⟩
  (selfAdjoint.expUnitaryPathToOne x).cast rfl (Unitary.expUnitary_pi_half_one_sub w hw).symm

/-- Pointwise exponential formula for `CStarMatrix.stabilizedUnitaryPath`. -/
@[simp]
theorem stabilizedUnitaryPath_apply [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    {v : CStarMatrix n m A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) (t : I) :
    stabilizedUnitaryPath hp hq hvp hvq hbe t =
      selfAdjoint.expUnitary ((t : ℝ) •
        ⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (stabilizedUnitary hp hq hvp hvq hbe :
            CStarMatrix (m ⊕ n) (m ⊕ n) A))),
          IsSelfAdjoint.smul (Complex.conj_ofReal π)
            (IsSelfAdjoint.smul (by simp : IsSelfAdjoint ((2 : ℂ)⁻¹))
              ((IsSelfAdjoint.one _).sub (isSelfAdjoint_stabilizedUnitary hp hq hvp hvq hbe)))⟩) :=
  (rfl)

/-- Closed-form matrix formula for `CStarMatrix.stabilizedUnitaryPath` at parameter `t : I`. -/
theorem coe_stabilizedUnitaryPath_apply [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) (t : I) :
    ((stabilizedUnitaryPath hp hq hvp hvq hbe t : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :
        CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      1 + (Complex.exp (Complex.I * (((t : ℝ) * π : ℝ) : ℂ)) - 1) •
        ((2 : ℂ)⁻¹ • (1 - fromBlocks (1 - p) v.conjTranspose v (1 - q))) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let w := stabilizedUnitary hp hq hvp hvq hbe
  have hw := isSelfAdjoint_stabilizedUnitary hp hq hvp hvq hbe
  have hw_sq : (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
      (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = 1 := by
    simpa only [w, hw.star_eq] using Unitary.coe_star_mul_self w
  have hr : IsStarProjection ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))) :=
    IsStarProjection.half_one_sub_of_mul_self_eq_one hw_sq hw
  rw [stabilizedUnitaryPath_apply]
  have hsmul : ((t : ℝ) •
      (⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))),
        IsSelfAdjoint.smul (Complex.conj_ofReal π) hr.isSelfAdjoint⟩ :
        selfAdjoint (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      (((t : ℝ) * π : ℝ) : ℂ) •
        ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))) := by
    change (t : ℝ) • ((π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A)))) = _
    rw [← smul_assoc, Complex.real_smul, ← Complex.ofReal_mul]
  have hsub : ((t : ℝ) •
      (⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))),
        IsSelfAdjoint.smul (Complex.conj_ofReal π) hr.isSelfAdjoint⟩ :
        selfAdjoint (CStarMatrix (m ⊕ n) (m ⊕ n) A))) =
      ⟨(((t : ℝ) * π : ℝ) : ℂ) • ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))),
        IsSelfAdjoint.smul (Complex.conj_ofReal ((t : ℝ) * π)) hr.isSelfAdjoint⟩ :=
    Subtype.ext hsmul
  have hexp := congrArg (fun a : selfAdjoint (CStarMatrix (m ⊕ n) (m ⊕ n) A) =>
    ((selfAdjoint.expUnitary a : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) :
      CStarMatrix (m ⊕ n) (m ⊕ n) A)) hsub
  rw [hr.coe_expUnitary_smul ((t : ℝ) * π)] at hexp
  simpa only [w, coe_stabilizedUnitary] using hexp

/-- **Stabilized unitary conjugacy (unequal sizes, unital case).** Uses the self-adjoint
algebraic conjugator from
`Matrix.IsMurrayVonNeumannEquivalent.exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star`
(packaged as `CStarMatrix.stabilizedUnitary`) and connects it to `1` via
`CStarMatrix.stabilizedUnitaryPath`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitary_conj [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * CStarMatrix.fromBlocks p 0 0 0 *
        star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = CStarMatrix.fromBlocks 0 0 0 q ∧
      Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) u := by
  obtain ⟨v, hvp, hvq, hbe⟩ := h.exists_matrix_mul_eq_self
  exact ⟨stabilizedUnitary h.isStarProjection_left h.isStarProjection_right hvp hvq hbe,
    stabilizedUnitary_conj h.isStarProjection_left h.isStarProjection_right hvp hvq hbe,
    ⟨stabilizedUnitaryPath h.isStarProjection_left h.isStarProjection_right hvp hvq hbe⟩⟩

/-- **Stabilized unitary conjugacy (equal sizes, unital case).** Murray–von Neumann equivalent
projections `p q : CStarMatrix n n A` satisfy `u * (p ⊕ 0) * u⋆ = q ⊕ 0` for a unitary `u` in the
identity path component of `unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitary_conj_same [DecidableEq n] [CStarAlgebra A]
    {p q : CStarMatrix n n A} (h : MurrayVonNeumannEquiv p q) :
    ∃ u : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A),
      (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) * CStarMatrix.fromBlocks p 0 0 0 *
        star (u : CStarMatrix (n ⊕ n) (n ⊕ n) A) = CStarMatrix.fromBlocks q 0 0 0 ∧
      Joined (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) u := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨w, hw_conj, hw_join⟩ := h.exists_stabilized_unitary_conj
  let rot := blockRotation (n := n) (A := A) (π / 2)
  refine ⟨rot * w, ?_,
    by simpa only [one_mul] using (joined_one_blockRotation (n := n) (A := A) (π / 2)).mul hw_join⟩
  calc ((rot * w : unitary _) : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
          CStarMatrix.fromBlocks p 0 0 0 *
          star ((rot * w : unitary _) : CStarMatrix (n ⊕ n) (n ⊕ n) A)
      = (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) * ((w : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
          CStarMatrix.fromBlocks p 0 0 0 * star (w : CStarMatrix (n ⊕ n) (n ⊕ n) A)) *
          star (rot : CStarMatrix (n ⊕ n) (n ⊕ n) A) := by
        simp only [Submonoid.coe_mul, star_mul]; noncomm_ring
    _ = CStarMatrix.fromBlocks q 0 0 0 := by
        rw [hw_conj]; exact blockRotation_pi_div_two_conj 0 q

/-- **Stabilized homotopy of equivalent projections (unequal sizes, non-unital case).**
If `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann equivalent star
projections in a (possibly non-unital) C⋆-algebra `A`, then `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are joined by a norm-continuous path of star projections in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_projection_path_to_opposite_corner [NonUnitalCStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : MurrayVonNeumannEquiv p q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  classical
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  obtain ⟨u, hconj, hjoin⟩ := (h.map ι).exists_stabilized_unitary_conj
  refine path_of_unitization_unitary_path
    (by simpa only [CStarMatrix.inlCornerHom_apply] using
      h.isStarProjection_left.map (CStarMatrix.inlCornerHom ℂ m n A)) ?_ hjoin
  simpa only [← hι, fromBlocks_map, CStarMatrix.map_zero (_root_.map_zero ι)] using hconj

/-- **Stabilized homotopy of equivalent projections (equal sizes, non-unital case).**
If `p q : CStarMatrix n n A` are Murray–von Neumann equivalent star projections in a (possibly
non-unital) C⋆-algebra `A`, then `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` are joined by a
norm-continuous path of star projections in `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_projection_path_to_same_corner [NonUnitalCStarAlgebra A]
    {p q : CStarMatrix n n A} (h : MurrayVonNeumannEquiv p q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (CStarMatrix.fromBlocks q 0 0 (0 : CStarMatrix n n A)),
      ∀ t : I, IsStarProjection (γ t) := by
  classical
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  obtain ⟨u, hconj, hjoin⟩ := (h.map ι).exists_stabilized_unitary_conj_same
  refine path_of_unitization_unitary_path
    (by simpa only [CStarMatrix.inlCornerHom_apply] using
      h.isStarProjection_left.map (CStarMatrix.inlCornerHom ℂ n n A)) ?_ hjoin
  simpa only [← hι, fromBlocks_map, CStarMatrix.map_zero (_root_.map_zero ι)] using hconj

end PathsAndStabilization

end CStarMatrix
