/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Block
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Hermitian
import TauCeti.Analysis.CStarAlgebra.Projection.Nearby
import TauCeti.Data.Matrix.Block

/-!
# Rectangular Murray–von Neumann equivalence

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular matrix. The index types may differ, so this relation identifies
a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, compatibility with block sums,
orthogonal sums, unitization unitary conjugacy, and preservation by nonunital star homomorphisms,
bridge the relation to `Matrix.IsMurrayVonNeumannEquivalent`, and establish the analytic C⋆-algebra
criteria: Blackadar's algebraic equivalence theorem (`of_mul_eq`), paths (`of_path`), nearby
projections (`of_norm_sub_lt_one`), stabilized unitary conjugacy in the identity path component
(`exists_stabilized_unitary_conj`, `exists_stabilized_unitary_conj_same`), and stabilized homotopy
of equivalent projections (`exists_path_fromBlocks_zero_left`, `exists_path_fromBlocks_zero_right`).

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
      Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) :=
  ⟨fun ⟨hp, hq, v, hv, hv'⟩ =>
    ⟨⟨congrArg ofMatrix.symm hp.isIdempotentElem.eq,
      congrArg ofMatrix.symm hp.isSelfAdjoint.star_eq⟩,
     ⟨congrArg ofMatrix.symm hq.isIdempotentElem.eq,
      congrArg ofMatrix.symm hq.isSelfAdjoint.star_eq⟩,
     ofMatrix.symm v, hv, hv'⟩,
   fun ⟨hp, hq, v, hv, hv'⟩ =>
    ⟨⟨ofMatrix.symm.injective hp.isIdempotentElem.eq,
      ofMatrix.symm.injective hp.isSelfAdjoint.star_eq⟩,
     ⟨ofMatrix.symm.injective hq.isIdempotentElem.eq,
      ofMatrix.symm.injective hq.isSelfAdjoint.star_eq⟩,
     ofMatrix v, hv, hv'⟩⟩

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

/-- Unitary conjugacy implies Murray–von Neumann equivalence. -/
theorem murrayVonNeumannEquiv_unitary_conj [Semiring B] [StarRing B] [DecidableEq m]
    {p : CStarMatrix m m B} (hp : IsStarProjection p) (u : unitary (CStarMatrix m m B)) :
    MurrayVonNeumannEquiv p ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) := by
  have hq : IsStarProjection ((u : CStarMatrix m m B) * p * star (u : CStarMatrix m m B)) :=
    ⟨by simp only [IsIdempotentElem, mul_assoc,
        ← mul_assoc (star (u : CStarMatrix m m B)), Unitary.coe_star_mul_self,
        one_mul, ← mul_assoc p, hp.isIdempotentElem.eq], hp.isSelfAdjoint.conjugate u⟩
  refine ⟨hp, hq, (u : CStarMatrix m m B) * p, ?_, ?_⟩
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq]
    simp only [mul_assoc, ← mul_assoc (star (u : CStarMatrix m m B)),
      Unitary.coe_star_mul_self, one_mul, hp.isIdempotentElem.eq]
  · rw [← star_eq_conjTranspose, star_mul, hp.isSelfAdjoint.star_eq]
    simp only [mul_assoc, ← mul_assoc p, hp.isIdempotentElem.eq]

/-! ### Orthogonal sums and unitization conjugacy -/

private theorem map_inr_map_snd_of_map_fstHom_eq_zero {m n A : Type*}
    [NonUnitalSemiring A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    {M : CStarMatrix m n A⁺¹} (hM : M.map (Unitization.fstHom ℂ A) = 0) :
    (M.map (fun x : A⁺¹ => x.snd)).map (Unitization.inr : A → A⁺¹) = M := by
  refine CStarMatrix.ext fun i j => Unitization.ext ?_ rfl
  simpa using (congrArg (fun X : CStarMatrix m n ℂ => X i j) hM).symm

private theorem map_fstHom_map_inr {m n A : Type*} [NonUnitalSemiring A] [Star A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (M : CStarMatrix m n A) :
    (M.map (Unitization.inrNonUnitalStarAlgHom ℂ A)).map (Unitization.fstHom ℂ A) = 0 :=
  CStarMatrix.ext fun _ _ => by simp

section OrthogonalSum

/-- Murray–von Neumann equivalence is compatible with sums of orthogonal star projections. -/
theorem MurrayVonNeumannEquiv.add [NonUnitalRing A] [StarRing A]
    {p₁ p₂ : CStarMatrix m m A} {q₁ q₂ : CStarMatrix n n A}
    (h₁ : MurrayVonNeumannEquiv p₁ q₁) (h₂ : MurrayVonNeumannEquiv p₂ q₂)
    (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    MurrayVonNeumannEquiv (p₁ + p₂) (q₁ + q₂) := by
  have hp₁ := h₁.isStarProjection_left; have hq₁ := h₁.isStarProjection_right
  have hp₂ := h₂.isStarProjection_left; have hq₂ := h₂.isStarProjection_right
  obtain ⟨v₁, hv₁, hw₁, hv₁p⟩ := h₁.exists_matrix_mul_eq_self
  obtain ⟨v₂, hv₂, hw₂, hv₂p⟩ := h₂.exists_matrix_mul_eq_self
  have hq₁v₁ : q₁ * v₁ = v₁ := by rw [← hw₁, mul_assoc_rectangular, hv₁, hv₁p]
  have hq₂v₂ : q₂ * v₂ = v₂ := by rw [← hw₂, mul_assoc_rectangular, hv₂, hv₂p]
  have hv₁q₁ : v₁.conjTranspose * q₁ = v₁.conjTranspose := by
    simpa only [conjTranspose_mul, ← star_eq_conjTranspose, hq₁.isSelfAdjoint.star_eq] using
      congrArg conjTranspose hq₁v₁
  have hp₂v₂ : p₂ * v₂.conjTranspose = v₂.conjTranspose := by
    simpa only [conjTranspose_mul, ← star_eq_conjTranspose, hp₂.isSelfAdjoint.star_eq] using
      congrArg conjTranspose hv₂p
  have h12 : v₁.conjTranspose * v₂ = 0 := by
    rw [← hv₁q₁, ← hq₂v₂, mul_assoc_rectangular, ← mul_assoc_rectangular q₁ q₂, hq,
      CStarMatrix.zero_mul, CStarMatrix.mul_zero]
  have h21 : v₂.conjTranspose * v₁ = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose h12
  have h12' : v₁ * v₂.conjTranspose = 0 := by
    rw [← hv₁p, ← hp₂v₂, mul_assoc_rectangular, ← mul_assoc_rectangular p₁ p₂, hp,
      CStarMatrix.zero_mul, CStarMatrix.mul_zero]
  have h21' : v₂ * v₁.conjTranspose = 0 := by
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] using
      congrArg conjTranspose h12'
  refine ⟨hp₁.add hp₂ hp, hq₁.add hq₂ hq, v₁ + v₂, ?_, ?_⟩
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hv₁, hv₂, h12, h21, add_zero, zero_add]
  · rw [conjTranspose_add, CStarMatrix.add_mul, CStarMatrix.mul_add, CStarMatrix.mul_add,
      hw₁, hw₂, h12', h21', add_zero, zero_add]

end OrthogonalSum

section UnitizationConjugacy

/-- Unitary conjugacy in the unitization `(CStarMatrix n n A)⁺¹` implies Murray–von Neumann
equivalence in `CStarMatrix n n A`. -/
theorem MurrayVonNeumannEquiv.of_unitization_unitary_conj
    [NonUnitalSemiring A] [StarRing A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    [StarModule ℂ A] {p q : CStarMatrix n n A} (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)⁺¹)
    (h : (u : (CStarMatrix n n A)⁺¹) * (p : (CStarMatrix n n A)⁺¹) *
      star (u : (CStarMatrix n n A)⁺¹) = (q : (CStarMatrix n n A)⁺¹)) :
    MurrayVonNeumannEquiv p q := by
  have hq : IsStarProjection q := by
    have hq' : IsStarProjection (q : (CStarMatrix n n A)⁺¹) := by
      rw [← h]
      simpa only [Unitary.conjStarAlgAut_apply] using
        hp.inr.map (Unitary.conjStarAlgAut ℂ (CStarMatrix n n A)⁺¹ u)
    exact IsStarProjection.of_inr (R := ℂ) hq'
  let v' : (CStarMatrix n n A)⁺¹ := (u : (CStarMatrix n n A)⁺¹) * (p : (CStarMatrix n n A)⁺¹)
  have hinr : (v'.snd : (CStarMatrix n n A)⁺¹) = v' :=
    Unitization.ext (by simp [v', Unitization.fst_mul, Unitization.fst_inr]) rfl
  refine ⟨hp, hq, v'.snd, ?_, ?_⟩ <;>
  · apply Unitization.inr_injective (R := ℂ)
    rw [← star_eq_conjTranspose, Unitization.inr_mul, Unitization.inr_star, hinr]
    simp only [v', star_mul, hp.inr.isSelfAdjoint.star_eq, mul_assoc]
    first
    | rw [← mul_assoc (star (u : (CStarMatrix n n A)⁺¹)), Unitary.star_mul_self_of_mem u.property,
        one_mul, hp.inr.isIdempotentElem.eq]
    | rw [← mul_assoc (p : (CStarMatrix n n A)⁺¹) (p : (CStarMatrix n n A)⁺¹),
        hp.inr.isIdempotentElem.eq, ← mul_assoc, h]

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
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  let p' : CStarMatrix n n A⁺¹ := p.map ι
  let v' : CStarMatrix n n A⁺¹ := (u : CStarMatrix n n A⁺¹) * p'
  have hv'_fst : v'.map (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), map_fstHom_map_inr p, mul_zero]
  let v : CStarMatrix n n A := v'.map fun x : A⁺¹ => x.snd
  have hv_inr : v.map ι = v' := map_inr_map_snd_of_map_fstHom_eq_zero hv'_fst
  have hp' : IsStarProjection p' := hp.map (CStarMatrix.mapₙₐ ι)
  have hq' : IsStarProjection (q.map ι) := by
    have hconj : (u : CStarMatrix n n A⁺¹) * p' * star (u : CStarMatrix n n A⁺¹) = q.map ι := by
      simpa only [p', hι] using h
    rw [← hconj]
    simpa only [Unitary.conjStarAlgAut_apply] using
      hp'.map (Unitary.conjStarAlgAut ℂ (CStarMatrix n n A⁺¹) u)
  have hinj : Function.Injective (fun M : CStarMatrix n n A => M.map (ι : A → A⁺¹)) := by
    simpa only [hι] using CStarMatrix.map_injective (m := n) (n := n)
      (Unitization.inr_injective (R := ℂ) (A := A))
  have hq : IsStarProjection q :=
    ⟨hinj (by dsimp only; rw [CStarMatrix.map_mul ι]; exact hq'.isIdempotentElem.eq),
      hinj (by
        dsimp only; rw [star_eq_conjTranspose, map_conjTranspose ι, ← star_eq_conjTranspose]
        exact hq'.isSelfAdjoint.star_eq)⟩
  refine ⟨hp, hq, v, ?_, ?_⟩ <;>
  · apply hinj; dsimp only
    rw [CStarMatrix.map_mul ι, map_conjTranspose ι, hv_inr, ← star_eq_conjTranspose]
    simp only [v', star_mul, hp'.isSelfAdjoint.star_eq, mul_assoc]
    first
    | rw [← mul_assoc (star (u : CStarMatrix n n A⁺¹)),
        Unitary.star_mul_self_of_mem u.property, one_mul, hp'.isIdempotentElem.eq]
    | rw [← mul_assoc p' p', hp'.isIdempotentElem.eq, ← mul_assoc, hι]; exact h

end UnitizationConjugacy

/-! ### Algebraic equivalence implies Murray–von Neumann equivalence -/

section AlgebraicEquiv

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
  let x₀ : CStarMatrix m n A⁺¹ := x.map ι
  let y₀ : CStarMatrix n m A⁺¹ := y.map ι
  have hp' : IsStarProjection p' := hp.map (CStarMatrix.mapₙₐ ι)
  have hq' : IsStarProjection q' := hq.map (CStarMatrix.mapₙₐ ι)
  have hx₀y₀ : x₀ * y₀ = p' := by rw [← CStarMatrix.map_mul ι, hxy]
  have hy₀x₀ : y₀ * x₀ = q' := by rw [← CStarMatrix.map_mul ι, hyx]
  let x' : CStarMatrix m n A⁺¹ := p' * x₀ * q'
  let y' : CStarMatrix n m A⁺¹ := q' * y₀ * p'
  have hx'y' : x' * y' = p' := by
    calc (p' * x₀ * q') * (q' * y₀ * p') = p' * x₀ * (q' * q') * y₀ * p' := by
          simp only [CStarMatrix.mul_assoc_rectangular]
      _ = p' * (x₀ * y₀) * (x₀ * y₀) * p' := by
          rw [hq'.isIdempotentElem.eq, ← hy₀x₀]; simp only [CStarMatrix.mul_assoc_rectangular]
      _ = p' := by
          rw [hx₀y₀, hp'.isIdempotentElem.eq, hp'.isIdempotentElem.eq, hp'.isIdempotentElem.eq]
  have hy'x' : y' * x' = q' := by
    calc (q' * y₀ * p') * (p' * x₀ * q') = q' * y₀ * (p' * p') * x₀ * q' := by
          simp only [CStarMatrix.mul_assoc_rectangular]
      _ = q' * (y₀ * x₀) * (y₀ * x₀) * q' := by
          rw [hp'.isIdempotentElem.eq, ← hx₀y₀]; simp only [CStarMatrix.mul_assoc_rectangular]
      _ = q' := by
          rw [hy₀x₀, hq'.isIdempotentElem.eq, hq'.isIdempotentElem.eq, hq'.isIdempotentElem.eq]
  have hpx' : p' * x' = x' := by
    simp only [x', ← CStarMatrix.mul_assoc_rectangular, hp'.isIdempotentElem.eq]
  have hx'q : x' * q' = x' := by
    simp only [x', CStarMatrix.mul_assoc_rectangular, hq'.isIdempotentElem.eq]
  have hqy' : q' * y' = y' := by
    simp only [y', ← CStarMatrix.mul_assoc_rectangular, hq'.isIdempotentElem.eq]
  have hq's : q'.conjTranspose = q' := by
    simpa only [← star_eq_conjTranspose] using hq'.isSelfAdjoint.star_eq
  have hp's : p'.conjTranspose = p' := by
    simpa only [← star_eq_conjTranspose] using hp'.isSelfAdjoint.star_eq
  have hx's_p : x'.conjTranspose * p' = x'.conjTranspose := by
    simpa only [conjTranspose_mul, hp's] using congrArg conjTranspose hpx'
  have hq_x's : q' * x'.conjTranspose = x'.conjTranspose := by
    simpa only [conjTranspose_mul, hq's] using congrArg conjTranspose hx'q
  let c : CStarMatrix n n A⁺¹ := (1 - q') + x'.conjTranspose * x'
  let b : CStarMatrix n n A⁺¹ := (1 - q') + y' * y'.conjTranspose
  have hx'_1q : x' * (1 - q') = 0 := by
    rw [CStarMatrix.mul_sub, CStarMatrix.mul_one, hx'q, sub_self]
  have hcb : c * b = 1 := by
    have hdiag : (x'.conjTranspose * x') * (y' * y'.conjTranspose) = q' := by
      calc (x'.conjTranspose * x') * (y' * y'.conjTranspose)
          = x'.conjTranspose * (x' * y') * y'.conjTranspose := by
            simp only [CStarMatrix.mul_assoc_rectangular]
        _ = (y' * x').conjTranspose := by rw [hx'y', hx's_p, ← conjTranspose_mul]
        _ = q' := by rw [hy'x', hq's]
    have h1q_y' : (1 - q') * y' = 0 := by
      rw [CStarMatrix.sub_mul, CStarMatrix.one_mul, hqy', sub_self]
    dsimp only [c, b]
    rw [add_mul, mul_add, mul_add, hq'.one_sub.isIdempotentElem.eq,
      ← CStarMatrix.mul_assoc_rectangular, h1q_y', CStarMatrix.zero_mul,
      CStarMatrix.mul_assoc_rectangular, hx'_1q, CStarMatrix.mul_zero, hdiag,
      add_zero, zero_add, sub_add_cancel]
  have hc_sa : IsSelfAdjoint c :=
    hq'.one_sub.isSelfAdjoint.add (by simp [isSelfAdjoint_iff, star_eq_conjTranspose])
  have hb_sa : IsSelfAdjoint b :=
    hq'.one_sub.isSelfAdjoint.add (by simp [isSelfAdjoint_iff, star_eq_conjTranspose])
  have hbc : b * c = 1 := by
    simpa only [star_mul, hc_sa.star_eq, hb_sa.star_eq, star_one] using congrArg star hcb
  have hc_nonneg : 0 ≤ c :=
    add_nonneg hq'.one_sub.nonneg (CStarMatrix.conjTranspose_mul_self_nonneg x')
  let s : CStarMatrix n n A⁺¹ := CFC.sqrt c
  have hs_pos : IsStrictlyPositive s :=
    (IsUnit.isStrictlyPositive ⟨⟨c, b, hcb, hbc⟩, rfl⟩ hc_nonneg).sqrt
  have hss : s * s = c := CFC.sqrt_mul_sqrt_self c hc_nonneg
  have hcq : c * q' = x'.conjTranspose * x' := by
    simp only [c, add_mul, sub_mul, one_mul, hq'.isIdempotentElem.eq, sub_self, zero_add,
      CStarMatrix.mul_assoc_rectangular, hx'q]
  have hcomm_cq : Commute c q' := hcq.trans (by
    simp only [c, mul_add, mul_sub, mul_one, hq'.isIdempotentElem.eq, sub_self, zero_add,
      ← CStarMatrix.mul_assoc_rectangular, hq_x's])
  have hsinv_sa : s⁻¹ʳ.conjTranspose = s⁻¹ʳ := by
    rw [← star_eq_conjTranspose, ← Ring.inverse_star, hs_pos.isSelfAdjoint.star_eq]
  let w' : CStarMatrix n m A⁺¹ := s⁻¹ʳ * x'.conjTranspose
  have hw'₁ : w'.conjTranspose * w' = p' := by
    have hsinv_sq : s⁻¹ʳ * s⁻¹ʳ = b := by
      rw [← Ring.mul_inverse_rev' (Commute.refl s), hss, Ring.inverse_unit ⟨c, b, hcb, hbc⟩]; rfl
    calc w'.conjTranspose * w'
        = x' * (s⁻¹ʳ * s⁻¹ʳ) * x'.conjTranspose := by
          simp only [w', conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa,
            CStarMatrix.mul_assoc_rectangular]
      _ = x' * (1 - q') * x'.conjTranspose + (x' * y') * (y'.conjTranspose * x'.conjTranspose) := by
          rw [hsinv_sq, CStarMatrix.mul_add, CStarMatrix.add_mul]
          simp only [CStarMatrix.mul_assoc_rectangular]
      _ = p' := by
          rw [hx'_1q, CStarMatrix.zero_mul, zero_add, ← conjTranspose_mul, hx'y', hp's,
            hp'.isIdempotentElem.eq]
  have hw'₂ : w' * w'.conjTranspose = q' := by
    have hcomm_sq : Commute s q' := hcomm_cq.cfcₙ_nnreal NNReal.sqrt
    have hxx : x'.conjTranspose * x' = s * q' * s := by
      conv_lhs => rw [← hcq, ← hss, mul_assoc, hcomm_sq.eq, ← mul_assoc]
    calc w' * w'.conjTranspose
        = s⁻¹ʳ * (x'.conjTranspose * x') * s⁻¹ʳ := by
          simp only [w', conjTranspose_mul, conjTranspose_conjTranspose, hsinv_sa,
            CStarMatrix.mul_assoc_rectangular]
      _ = (s⁻¹ʳ * s) * q' * (s * s⁻¹ʳ) := by
          rw [hxx]; simp only [CStarMatrix.mul_assoc_rectangular]
      _ = q' := by
          rw [Ring.inverse_mul_cancel _ hs_pos.isUnit, Ring.mul_inverse_cancel _ hs_pos.isUnit,
            one_mul, mul_one]
  let w : CStarMatrix n m A := w'.map fun z : A⁺¹ => z.snd
  have hw_inr : w.map ι = w' := map_inr_map_snd_of_map_fstHom_eq_zero (by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), map_conjTranspose (Unitization.fstHom ℂ A),
      CStarMatrix.map_mul (Unitization.fstHom ℂ A), CStarMatrix.map_mul (Unitization.fstHom ℂ A),
      map_fstHom_map_inr p, CStarMatrix.zero_mul, CStarMatrix.zero_mul, conjTranspose_zero,
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
  obtain ⟨u, hconj, -⟩ := IsStarProjection.exists_unitization_unitary_conj_of_path γ hγ
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

/-- **Stabilized unitary conjugacy (unequal sizes, unital case).** Murray–von Neumann equivalent
projections `p : CStarMatrix m m A` and `q : CStarMatrix n n A` satisfy
`u * (p ⊕ 0) * u⋆ = 0 ⊕ q` for a unitary `u` in the identity path component. -/
theorem MurrayVonNeumannEquiv.exists_stabilized_unitary_conj [DecidableEq m] [DecidableEq n]
    [CStarAlgebra A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    ∃ u : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A),
      (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) * CStarMatrix.fromBlocks p 0 0 0 *
        star (u : CStarMatrix (m ⊕ n) (m ⊕ n) A) = CStarMatrix.fromBlocks 0 0 0 q ∧
      Joined (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)) u := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  obtain ⟨wM, hwM_sa, hwM_mem, hwM_conj⟩ :=
    (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp
      h).exists_isSelfAdjoint_mem_unitary_mul_fromBlocks_mul_star
  let w : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) := ⟨ofMatrix wM, hwM_mem⟩
  have hw_sa : IsSelfAdjoint (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) := hwM_sa
  have hmem : (π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (w : CStarMatrix (m ⊕ n) (m ⊕ n) A))) ∈
      selfAdjoint (CStarMatrix (m ⊕ n) (m ⊕ n) A) := by
    rw [selfAdjoint.mem_iff, star_smul, star_smul, star_sub, star_one, hw_sa.star_eq,
      RCLike.star_def, Complex.conj_ofReal, map_inv₀, map_ofNat]
  have hconj : (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) * CStarMatrix.fromBlocks p 0 0 0 *
      star (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = CStarMatrix.fromBlocks 0 0 0 q := by
    apply ofMatrix.symm.injective
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_star, ofMatrix_symm_fromBlocks,
      ← Matrix.star_eq_conjTranspose,
      show ofMatrix.symm (w : CStarMatrix (m ⊕ n) (m ⊕ n) A) = wM from rfl,
      show ofMatrix.symm (0 : CStarMatrix m n A) = 0 from rfl,
      show ofMatrix.symm (0 : CStarMatrix n m A) = 0 from rfl,
      show ofMatrix.symm (0 : CStarMatrix m m A) = 0 from rfl,
      show ofMatrix.symm (0 : CStarMatrix n n A) = 0 from rfl] using hwM_conj
  refine ⟨w, hconj, ?_⟩
  rw [← Unitary.expUnitary_pi_half_one_sub w hw_sa hmem]
  exact selfAdjoint.joined_one_expUnitary ⟨_, hmem⟩

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

private theorem path_of_unitization_unitary_path {k A : Type*} [Fintype k] [DecidableEq k]
    [NonUnitalCStarAlgebra A] {P Q : CStarMatrix k k A} (hP : IsStarProjection P)
    {u : unitary (CStarMatrix k k A⁺¹)}
    (hconj : (u : CStarMatrix k k A⁺¹) * P.map (Unitization.inr : A → A⁺¹) *
      star (u : CStarMatrix k k A⁺¹) = Q.map (Unitization.inr : A → A⁺¹))
    (hjoin : Joined (1 : unitary (CStarMatrix k k A⁺¹)) u) :
    ∃ γ : Path P Q, ∀ t : I, IsStarProjection (γ t) := by
  let : PartialOrder A⁺¹ := CStarAlgebra.spectralOrder A⁺¹
  let : StarOrderedRing A⁺¹ := CStarAlgebra.spectralOrderedRing A⁺¹
  let ι : A →⋆ₙₐ[ℂ] A⁺¹ := Unitization.inrNonUnitalStarAlgHom ℂ A
  have hι : (ι : A → A⁺¹) = Unitization.inr := funext fun _ => rfl
  obtain ⟨δ⟩ := hjoin
  have hfst (t : I) :
      ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
        (Unitization.fstHom ℂ A) = 0 := by
    rw [CStarMatrix.map_mul (Unitization.fstHom ℂ A), CStarMatrix.map_mul (Unitization.fstHom ℂ A),
      map_fstHom_map_inr P, mul_zero, zero_mul]
  let f : I → CStarMatrix k k A := fun t =>
    ((δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹)).map
      (fun x : A⁺¹ => x.snd)
  have hf_inr (t : I) : (f t).map ι =
      (δ t : CStarMatrix k k A⁺¹) * P.map ι * star (δ t : CStarMatrix k k A⁺¹) :=
    map_inr_map_snd_of_map_fstHom_eq_zero (hfst t)
  have hf_cont : Continuous f := by
    have hδ : Continuous (fun t : I => ((δ t : unitary (CStarMatrix k k A⁺¹)) :
        CStarMatrix k k A⁺¹)) := continuous_subtypeVal.comp δ.continuous
    have hmap : Continuous (fun M : CStarMatrix k k A⁺¹ => M.map (fun x : A⁺¹ => x.snd)) :=
      continuous_id.matrix_map (Unitization.continuous_snd (𝕜 := ℂ) (A := A))
    exact hmap.comp ((hδ.mul continuous_const).mul hδ.star)
  have hinj : Function.Injective (fun M : CStarMatrix k k A => M.map (ι : A → A⁺¹)) := by
    simpa only [hι] using CStarMatrix.map_injective (m := k) (n := k)
      (Unitization.inr_injective (R := ℂ) (A := A))
  have hP' : IsStarProjection (P.map ι) := hP.map (CStarMatrix.mapₙₐ ι)
  refine ⟨⟨⟨f, hf_cont⟩, hinj (by simp [hf_inr 0, δ.source]),
    hinj (by dsimp only; rw [hf_inr 1, δ.target, hι]; exact hconj)⟩, fun t => ?_⟩
  have hproj' : IsStarProjection ((f t).map ι) := by
    rw [hf_inr t]
    simpa only [Unitary.conjStarAlgAut_apply] using
      hP'.map (Unitary.conjStarAlgAut ℂ (CStarMatrix k k A⁺¹) (δ t))
  exact ⟨hinj (by dsimp only; rw [CStarMatrix.map_mul ι]; exact hproj'.isIdempotentElem.eq),
    hinj (by
      dsimp only; rw [star_eq_conjTranspose, map_conjTranspose ι, ← star_eq_conjTranspose]
      exact hproj'.isSelfAdjoint.star_eq)⟩

/-- **Stabilized homotopy of equivalent projections (unequal sizes, non-unital case).**
If `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann equivalent star
projections in a (possibly non-unital) C⋆-algebra `A`, then `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are joined by a norm-continuous path of star projections in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_path_fromBlocks_zero_left [NonUnitalCStarAlgebra A]
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
theorem MurrayVonNeumannEquiv.exists_path_fromBlocks_zero_right [NonUnitalCStarAlgebra A]
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

/-! ### Concrete checks -/

section Checks

/-- Unequal-size Murray–von Neumann equivalence: `diag(1, 0) : M₂(ℂ)` is equivalent to
`1 : M₁(ℂ)`. -/
example :
    MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) 0 0
        (0 : CStarMatrix (Fin 1) (Fin 1) ℂ))
      (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) :=
  (MurrayVonNeumannEquiv.pad_zero
    (IsStarProjection.one (R := CStarMatrix (Fin 1) (Fin 1) ℂ))).symm

/-- Midpoint of the stabilized exponential path for `p = q = 1` in `M₁(ℂ)` and `v = 1`:
`exp(i π r / 2) * diag(1, 0) * exp(-i π r / 2) = [[1 / 2, i / 2], [-i / 2, 1 / 2]]`. -/
example :
    let p : CStarMatrix (Fin 1) (Fin 1) ℂ := 1
    let w : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fromBlocks 0 1 1 0
    let r : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := (2 : ℂ)⁻¹ • (1 - w)
    have hr : IsStarProjection r :=
      IsStarProjection.half_one_sub_of_mul_self_eq_one
        (by simp [w]) (by simp [w, isSelfAdjoint_iff])
    have hmem : ((π / 2 : ℝ) : ℂ) • r ∈
        selfAdjoint (CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, RCLike.star_def, Complex.conj_ofReal,
        hr.isSelfAdjoint.star_eq]
    let u : unitary (CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) :=
      selfAdjoint.expUnitary ⟨((π / 2 : ℝ) : ℂ) • r, hmem⟩
    (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) * fromBlocks p 0 0 0 *
        star (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks ((1 / 2 : ℂ) • 1) ((Complex.I / 2 : ℂ) • 1)
        ((-(Complex.I / 2) : ℂ) • 1) ((1 / 2 : ℂ) • 1) := by
  intro p w r hr hmem u
  have hexp : Complex.exp (Complex.I * ((π / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  have hu : (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks (((1 + Complex.I) / 2 : ℂ) • 1) (((1 - Complex.I) / 2 : ℂ) • 1)
        (((1 - Complex.I) / 2 : ℂ) • 1) (((1 + Complex.I) / 2 : ℂ) • 1) := by
    dsimp only [u]; rw [hr.coe_expUnitary_smul (π / 2) hmem, hexp]
    ext (i | i) (j | j) <;> simp [r, w, ← fromBlocks_one] <;> ring
  have hsu : star (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks (((1 - Complex.I) / 2 : ℂ) • 1) (((1 + Complex.I) / 2 : ℂ) • 1)
        (((1 + Complex.I) / 2 : ℂ) • 1) (((1 - Complex.I) / 2 : ℂ) • 1) := by
    rw [hu, fromBlocks_star]; ext (i | i) (j | j) <;> simp [Complex.conj_I, sub_eq_add_neg]
  rw [hsu, hu]
  ext (i | i) (j | j) <;> simp [p, fromBlocks_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end Checks

end CStarMatrix
