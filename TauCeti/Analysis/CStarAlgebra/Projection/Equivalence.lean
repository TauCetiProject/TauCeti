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
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Star.Projection.Basic
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Unitization
import TauCeti.Analysis.CStarAlgebra.Projection.Nearby

/-!
# Rectangular Murray–von Neumann equivalence

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular matrix. The index types may differ, so this relation identifies
a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, compatibility with reindexing
(`MurrayVonNeumannEquiv.reindex`), block sums (`fromBlocks`, `fromBlocks_comm`, `fromBlocks_assoc`,
`pad_zero`), orthogonal sums, unitization unitary conjugacy, and preservation by nonunital star
homomorphisms, bridge the relation to `Matrix.IsMurrayVonNeumannEquivalent`, and establish the
analytic C⋆-algebra criteria: Blackadar's algebraic equivalence theorem (`of_mul_eq`), paths
(`of_path`), nearby projections (`of_norm_sub_lt_one`), explicit stabilized unitary conjugacy
(`stabilizedUnitary`, `stabilizedUnitaryPath`, `exists_stabilized_unitary_conj`,
`exists_stabilized_unitary_conj_same`), and stabilized homotopy of equivalent projections
(`exists_path_isStarProjection_fromBlocks_zero₂₂_fromBlocks_zero₁₁`,
`exists_path_isStarProjection_fromBlocks_zero₂₂`).

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
  simp only [MurrayVonNeumannEquiv, Matrix.isMurrayVonNeumannEquivalent_iff,
    isStarProjection_ofMatrix_symm_iff, and_congr_right_iff]
  intro _ _
  refine Equiv.exists_congr ofMatrix.symm fun v => ?_
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_mul, ofMatrix_symm_conjTranspose]

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

/-- Murray–von Neumann equivalence is preserved by reindexing both matrices. -/
theorem reindex {m' n' R : Type*} [Fintype m'] [Fintype n'] [Semiring R] [Module R A]
    (h : MurrayVonNeumannEquiv p q) (eₘ : m ≃ m') (eₙ : n ≃ n') :
    MurrayVonNeumannEquiv (reindexₐ R A eₘ p) (reindexₐ R A eₙ q) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent] at h ⊢
  simpa only [ofMatrix_symm_reindexₐ] using h.reindex eₘ eₙ

/-- A matrix projection is equivalent to each of its reindexings. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindex {m' R : Type*} [Fintype m']
    [Semiring R] [Module R A] (hp : IsStarProjection p) (e : m ≃ m') :
    MurrayVonNeumannEquiv p (reindexₐ R A e p) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_reindexₐ] using
    (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_reindex e

/-- Block-diagonal sums of equivalent projections are equivalent. -/
theorem fromBlocks {p' : CStarMatrix k k A} {q' : CStarMatrix l l A}
    (h : MurrayVonNeumannEquiv p q) (h' : MurrayVonNeumannEquiv p' q') :
    MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 p')
      (CStarMatrix.fromBlocks q 0 0 q') := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent] at h h' ⊢
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using h.fromBlocks h'

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
    MurrayVonNeumannEquiv p (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix k k A)) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using
    (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_fromBlocks_zero

/-- Commutativity of block sums up to Murray–von Neumann equivalence. -/
theorem fromBlocks_comm (hp : IsStarProjection p) (hq : IsStarProjection q) :
    MurrayVonNeumannEquiv (CStarMatrix.fromBlocks p 0 0 q) (CStarMatrix.fromBlocks q 0 0 p) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using
    Matrix.isMurrayVonNeumannEquivalent_fromBlocks_comm
      (isStarProjection_ofMatrix_symm_iff.mpr hp)
      (isStarProjection_ofMatrix_symm_iff.mpr hq)

/-- Associativity of block sums up to Murray–von Neumann equivalence. -/
theorem fromBlocks_assoc (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) :
    MurrayVonNeumannEquiv (CStarMatrix.fromBlocks (CStarMatrix.fromBlocks p 0 0 q) 0 0 r)
      (CStarMatrix.fromBlocks p 0 0 (CStarMatrix.fromBlocks q 0 0 r)) := by
  rw [murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent]
  simpa only [ofMatrix_symm_fromBlocks, ofMatrix_symm_zero] using
    Matrix.isMurrayVonNeumannEquivalent_fromBlocks_assoc
      (isStarProjection_ofMatrix_symm_iff.mpr hp)
      (isStarProjection_ofMatrix_symm_iff.mpr hq)
      (isStarProjection_ofMatrix_symm_iff.mpr hr)

/-- A Murray–von Neumann equivalence is implemented by a matrix supported on its initial
projection. -/
theorem exists_matrix_mul_eq_self (h : MurrayVonNeumannEquiv p q) :
    ∃ v : CStarMatrix n m A,
      v.conjTranspose * v = p ∧ v * v.conjTranspose = q ∧ v * p = v := by
  obtain ⟨v, hvp, hvq, hvp_eq, -⟩ :=
    (murrayVonNeumannEquiv_iff_isMurrayVonNeumannEquivalent.mp
      h).exists_mul_conjTranspose_mul_self_eq_support
  refine ⟨ofMatrix v, ?_, ?_, ?_⟩ <;> apply ofMatrix.symm.injective
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply] using hvp
  · simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose, Equiv.symm_apply_apply] using hvq
  · simpa only [ofMatrix_symm_mul, Equiv.symm_apply_apply] using hvp_eq

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
  let p' : CStarMatrix n n A⁺¹ := mapι p
  let q' : CStarMatrix n n A⁺¹ := mapι q
  let v' : CStarMatrix n n A⁺¹ := (u : CStarMatrix n n A⁺¹) * p'
  have hp' : IsStarProjection p' := hp.map mapι
  have hconj : (u : CStarMatrix n n A⁺¹) * p' * star (u : CStarMatrix n n A⁺¹) = q' := by
    simpa only [p', q', mapι, CStarMatrix.mapₙₐ_apply, CStarMatrix.mapₗ_apply, ι,
      LinearMap.coe_ofClass, CStarMatrix.map_inrNonUnitalStarAlgHom] using h
  have hq' : IsStarProjection q' := by
    rw [← hconj]
    simpa only [Unitary.conjStarAlgAut_apply] using
      hp'.map (Unitary.conjStarAlgAut ℂ (CStarMatrix n n A⁺¹) u)
  have hinj : Function.Injective mapι :=
    CStarMatrix.map_injective (Unitization.inr_injective (R := ℂ) (A := A))
  have hq : IsStarProjection q := hq'.of_map_injective hinj
  let v : CStarMatrix n n A := v'.map fun x : A⁺¹ => x.snd
  have hv_inr : mapι v = v' := by
    dsimp only [mapι, ι]
    rw [CStarMatrix.mapₙₐ_apply, CStarMatrix.mapₗ_apply, LinearMap.coe_ofClass,
      CStarMatrix.map_inrNonUnitalStarAlgHom]
    exact map_inr_map_snd_of_mul_map_inr_eq (by
      simpa only [v', p', mapι, CStarMatrix.mapₙₐ_apply, CStarMatrix.mapₗ_apply, ι,
        LinearMap.coe_ofClass, CStarMatrix.map_inrNonUnitalStarAlgHom, mul_assoc] using
        congrArg (fun M => (u : CStarMatrix n n A⁺¹) * M) hp'.isIdempotentElem.eq)
  obtain ⟨hv1, hv2⟩ := unitary_mul_proj_witness hp' u
  refine ⟨hp, hq, v, hinj ?_, hinj ?_⟩
  · rw [map_mul, ← star_eq_conjTranspose, map_star, star_eq_conjTranspose, hv_inr]
    exact hv1
  · rw [map_mul, ← star_eq_conjTranspose, map_star, star_eq_conjTranspose, hv_inr]
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
  obtain ⟨v, hv₁, hv₂⟩ := hp.exists_star_mul_self_eq_of_mem_unitary_unitization u.property h
  have hq : IsStarProjection q := IsStarProjection.of_inr (R := ℂ) (by
    rw [← h]
    simpa only [Unitary.conjStarAlgAut_apply] using
      hp.inr.map (Unitary.conjStarAlgAut ℂ (CStarMatrix n n A)⁺¹ u))
  exact ⟨hp, hq, v, by rwa [← star_eq_conjTranspose], by rwa [← star_eq_conjTranspose]⟩

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

private theorem normalized_mul_eq_inv {B m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Ring B] [StarRing B] {p : CStarMatrix m m B} {q : CStarMatrix n n B}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x : CStarMatrix m n B} {y : CStarMatrix n m B}
    (hxy : x * y = p) (hyx : y * x = q) (hpx : p * x = x) (hxq : x * q = x) (hqy : q * y = y) :
    ((1 - q) + x.conjTranspose * x) * ((1 - q) + y * y.conjTranspose) = 1 ∧
      ((1 - q) + y * y.conjTranspose) * ((1 - q) + x.conjTranspose * x) = 1 := by
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
      _ = (y * x).conjTranspose := by
          rw [hxy, hp.isSelfAdjoint.conjTranspose_mul_of_mul_eq hpx, ← conjTranspose_mul]
      _ = q := by rw [hyx, ← star_eq_conjTranspose, hq.isSelfAdjoint.star_eq]
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
  exact ⟨hcb, hbc⟩

private theorem normalized_mul_eq_witness {B m n : Type*} [Fintype m] [Fintype n]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {p : CStarMatrix m m B} {q : CStarMatrix n n B}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    {x : CStarMatrix m n B} {y : CStarMatrix n m B}
    (hxy : x * y = p) (hyx : y * x = q)
    (hpx : p * x = x) (hxq : x * q = x) (hqy : q * y = y) :
    ∃ w : CStarMatrix n m B, w.conjTranspose * w = p ∧ w * w.conjTranspose = q ∧ w * p = w := by
  classical
  have hx_1q : x * (1 - q) = 0 := by
    simp only [CStarMatrix.mul_sub, CStarMatrix.mul_one, hxq, sub_self]
  -- Step 1: `c = (1 - q) + xᴴ * x` is positive and invertible with inverse `b = (1 - q) + y * yᴴ`.
  let c : CStarMatrix n n B := (1 - q) + x.conjTranspose * x
  let b : CStarMatrix n n B := (1 - q) + y * y.conjTranspose
  obtain ⟨hcb, hbc⟩ := normalized_mul_eq_inv hp hq hxy hyx hpx hxq hqy
  have hc_nonneg : 0 ≤ c :=
    add_nonneg hq.one_sub.nonneg (CStarMatrix.conjTranspose_mul_self_nonneg x)
  -- Step 2: Take the positive square root `s = c^(1/2)` and polar factor `w = s⁻¹ * xᴴ`.
  let s : CStarMatrix n n B := CFC.sqrt c
  have hs_pos : IsStrictlyPositive s :=
    (IsUnit.isStrictlyPositive ⟨⟨c, b, hcb, hbc⟩, rfl⟩ hc_nonneg).sqrt
  have hss : s * s = c := CFC.sqrt_mul_sqrt_self c hc_nonneg
  have hcq : c * q = x.conjTranspose * x := by
    simp only [c, add_mul, sub_mul, one_mul, hq.isIdempotentElem.eq, sub_self, zero_add,
      CStarMatrix.mul_assoc_rectangular, hxq]
  have hcomm_cq : Commute c q := hcq.trans (by
    simp only [c, mul_add, mul_sub, mul_one, hq.isIdempotentElem.eq, sub_self, zero_add,
      ← CStarMatrix.mul_assoc_rectangular, hq.isSelfAdjoint.mul_conjTranspose_of_mul_eq hxq])
  have hsinv_sa : s⁻¹ʳ.conjTranspose = s⁻¹ʳ := by
    rw [← star_eq_conjTranspose, ← Ring.inverse_star, hs_pos.isSelfAdjoint.star_eq]
  let w : CStarMatrix n m B := s⁻¹ʳ * x.conjTranspose
  -- Step 3: Verify `wᴴ * w = p` (via `s⁻¹ * s⁻¹ = b`) and `w * wᴴ = q`
  -- (since `s` commutes with `q`).
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
          rw [hx_1q, CStarMatrix.zero_mul, zero_add, ← conjTranspose_mul, hxy,
            ← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
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
  exact ⟨w, hw₁, hw₂,
    by rw [CStarMatrix.mul_assoc_rectangular, hp.isSelfAdjoint.conjTranspose_mul_of_mul_eq hpx]⟩

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
  have hw_inr : w.map ι = w' := by
    rw [CStarMatrix.map_inrNonUnitalStarAlgHom]
    exact map_inr_map_snd_of_mul_map_inr_eq (by
      simpa only [p', ι, CStarMatrix.map_inrNonUnitalStarAlgHom] using hw'p)
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
of `p ∼ q` satisfying `v * p = v`. -/
def stabilizedUnitary [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  ⟨fromBlocks (1 - p) v.conjTranspose v (1 - q), by
    have hbeM : ofMatrix.symm v * ofMatrix.symm p = ofMatrix.symm v := by
      simpa only [ofMatrix_symm_mul] using congrArg ofMatrix.symm hbe
    have heaM : ofMatrix.symm p * (ofMatrix.symm v)ᴴ = (ofMatrix.symm v)ᴴ := by
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm (hp.isSelfAdjoint.mul_conjTranspose_of_mul_eq hbe)
    have hsa : IsSelfAdjoint (fromBlocks (1 - p) v.conjTranspose v (1 - q)) := by
      simp only [isSelfAdjoint_iff, fromBlocks_star, star_sub, star_one,
        hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, conjTranspose_conjTranspose]
    -- Verify `w * w = 1` via `Matrix.fromBlocks_one_sub_mul_self_of_mul_eq`.
    have hsq : fromBlocks (1 - p) v.conjTranspose v (1 - q) *
        fromBlocks (1 - p) v.conjTranspose v (1 - q) = 1 := by
      apply ofMatrix.symm.injective
      simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub,
        ofMatrix_symm_one, ofMatrix_symm_conjTranspose] using
        Matrix.fromBlocks_one_sub_mul_self_of_mul_eq
          (by simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
            congrArg ofMatrix.symm hvp)
          (by simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
            congrArg ofMatrix.symm hvq)
          heaM hbeM
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

/-- Conjugating `p ⊕ 0` by `CStarMatrix.stabilizedUnitary` gives `0 ⊕ q`. -/
theorem stabilizedUnitary_conj [DecidableEq m] [DecidableEq n] [Ring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    (stabilizedUnitary hp hq hvp hvq hbe : CStarMatrix (m ⊕ n) (m ⊕ n) A) *
        fromBlocks p 0 0 0 *
        star (stabilizedUnitary hp hq hvp hvq hbe : CStarMatrix (m ⊕ n) (m ⊕ n) A) =
      fromBlocks 0 0 0 q := by
  -- Follows from `Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq`.
  rw [(isSelfAdjoint_stabilizedUnitary hp hq hvp hvq hbe).star_eq, coe_stabilizedUnitary]
  apply ofMatrix.symm.injective
  simpa only [ofMatrix_symm_mul, ofMatrix_symm_fromBlocks, ofMatrix_symm_sub, ofMatrix_symm_one,
    ofMatrix_symm_conjTranspose, ofMatrix_symm_zero] using
    Matrix.fromBlocks_one_sub_mul_fromBlocks_mul_fromBlocks_one_sub_of_mul_eq
      (by simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm hvp)
      (by simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
        congrArg ofMatrix.symm hvq)
      (by simpa only [ofMatrix_symm_mul] using congrArg ofMatrix.symm hbe)

/-- Explicit continuous path in `unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)` from `1` to
`CStarMatrix.stabilizedUnitary`. -/
noncomputable def stabilizedUnitaryPath [DecidableEq m] [DecidableEq n] [CStarAlgebra A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} {v : CStarMatrix n m A}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hvp : v.conjTranspose * v = p) (hvq : v * v.conjTranspose = q) (hbe : v * p = v) :
    Path (1 : unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A))
      (stabilizedUnitary hp hq hvp hvq hbe) :=
  -- Specializes `Unitary.expUnitaryPathOfIsSelfAdjoint` to `stabilizedUnitary`.
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  Unitary.expUnitaryPathOfIsSelfAdjoint (stabilizedUnitary hp hq hvp hvq hbe)
    (isSelfAdjoint_stabilizedUnitary hp hq hvp hvq hbe)

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
              ((IsSelfAdjoint.one _).sub
                (isSelfAdjoint_stabilizedUnitary hp hq hvp hvq hbe)))⟩) := by
  dsimp only [stabilizedUnitaryPath]
  exact Unitary.expUnitaryPathOfIsSelfAdjoint_apply _ _ t

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
  dsimp only [stabilizedUnitaryPath]
  rw [Unitary.coe_expUnitaryPathOfIsSelfAdjoint_apply, coe_stabilizedUnitary]

/-- **Stabilized unitary conjugacy (unital case).** If `p : CStarMatrix m m A` and
`q : CStarMatrix n n A` are Murray–von Neumann equivalent projections over a unital C⋆-algebra `A`,
then some unitary in the identity path component of `unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A)`
conjugates `fromBlocks p 0 0 0` to `fromBlocks 0 0 0 q`. -/
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

/-- **Stabilized homotopy of equivalent projections (non-unital case).**
If `p : CStarMatrix m m A` and `q : CStarMatrix n n A` are Murray–von Neumann equivalent star
projections in a (possibly non-unital) C⋆-algebra `A`, then `fromBlocks p 0 0 0` and
`fromBlocks 0 0 0 q` are joined by a norm-continuous path of star projections in
`CStarMatrix (m ⊕ n) (m ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_path_isStarProjection_fromBlocks_zero₂₂_fromBlocks_zero₁₁
    [NonUnitalCStarAlgebra A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}
    (h : MurrayVonNeumannEquiv p q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (CStarMatrix.fromBlocks (0 : CStarMatrix m m A) 0 0 q),
      ∀ t : I, IsStarProjection (γ t) := by
  classical
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  obtain ⟨u, hconj, hjoin⟩ := (h.map ι).exists_stabilized_unitary_conj
  refine exists_path_isStarProjection_of_unitization_unitary_conj
    (by simpa only [CStarMatrix.inlCornerHom_apply] using
      h.isStarProjection_left.map (CStarMatrix.inlCornerHom ℂ m n A)) ?_ hjoin
  simpa only [fromBlocks_map, ι, CStarMatrix.map_inrNonUnitalStarAlgHom,
    CStarMatrix.map_zero (Unitization.inr_zero (R := ℂ) (A := A))] using hconj

/-- **Stabilized homotopy of equivalent projections (equal sizes, non-unital case).**
If `p q : CStarMatrix n n A` are Murray–von Neumann equivalent star projections in a (possibly
non-unital) C⋆-algebra `A`, then `fromBlocks p 0 0 0` and `fromBlocks q 0 0 0` are joined by a
norm-continuous path of star projections in `CStarMatrix (n ⊕ n) (n ⊕ n) A`. -/
theorem MurrayVonNeumannEquiv.exists_path_isStarProjection_fromBlocks_zero₂₂
    [NonUnitalCStarAlgebra A] {p q : CStarMatrix n n A} (h : MurrayVonNeumannEquiv p q) :
    ∃ γ : Path (CStarMatrix.fromBlocks p 0 0 (0 : CStarMatrix n n A))
        (CStarMatrix.fromBlocks q 0 0 (0 : CStarMatrix n n A)),
      ∀ t : I, IsStarProjection (γ t) := by
  classical
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ A
  obtain ⟨u, hconj, hjoin⟩ := (h.map ι).exists_stabilized_unitary_conj_same
  refine exists_path_isStarProjection_of_unitization_unitary_conj
    (by simpa only [CStarMatrix.inlCornerHom_apply] using
      h.isStarProjection_left.map (CStarMatrix.inlCornerHom ℂ n n A)) ?_ hjoin
  simpa only [fromBlocks_map, ι, CStarMatrix.map_inrNonUnitalStarAlgHom,
    CStarMatrix.map_zero (Unitization.inr_zero (R := ℂ) (A := A))] using hconj

end PathsAndStabilization

end CStarMatrix
