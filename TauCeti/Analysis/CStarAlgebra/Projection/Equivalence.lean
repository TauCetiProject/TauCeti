/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import TauCeti.Algebra.Star.PartialIsometry
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Connected.PathConnected

/-!
# Projection equivalences: unitary, homotopy, and rectangular Murray–von Neumann

This file defines projection unitary equivalence (`TauCeti.UnitaryEquiv`) on any star monoid,
projection homotopy equivalence (`TauCeti.HomotopyEquiv`) on any topological star magma (together
with conjugacy by a unitary in the identity component), and rectangular Murray–von Neumann
equivalence (`CStarMatrix.MurrayVonNeumannEquiv`) across rectangular matrices.

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular matrix. The index types may differ, so this relation identifies
a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, and preservation by nonunital star
homomorphisms. These are the relations needed to form the projection monoid (compatibility with
block sums is in `TauCeti.Analysis.CStarAlgebra.Projection.Stabilization`). No unit,
separability, or cancellation is assumed.

The algebraic matrix calculations use Mathlib's underlying `Matrix` operations, which are the
operations used to define `CStarMatrix` multiplication and conjugate transpose.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, §4.6 (Definition 4.6.1) and §5.1.
-/

public section

open scoped Matrix

namespace TauCeti

section UnitaryEquiv

variable {S : Type*} [Monoid S] [StarMul S] {p q r : S}

/-- Two elements are unitarily equivalent projections when both are star projections and some
unitary `u : unitary S` satisfies `(u : S) * p * star (u : S) = q`. -/
def UnitaryEquiv (p q : S) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧ ∃ u : unitary S, (u : S) * p * star (u : S) = q

namespace UnitaryEquiv

/-- The left element of a unitary equivalence is a star projection. -/
theorem isStarProjection_left (h : UnitaryEquiv p q) : IsStarProjection p := h.1

/-- The right element of a unitary equivalence is a star projection. -/
theorem isStarProjection_right (h : UnitaryEquiv p q) : IsStarProjection q := h.2.1

/-- Extract a unitary conjugating `p` to `q`. -/
theorem exists_unitary (h : UnitaryEquiv p q) :
    ∃ u : unitary S, (u : S) * p * star (u : S) = q := h.2.2

/-- Every star projection is unitarily equivalent to itself. -/
protected theorem refl (hp : IsStarProjection p) : UnitaryEquiv p p := ⟨hp, hp, 1, by simp⟩

/-- Unitary equivalence of star projections is symmetric. -/
protected theorem symm (h : UnitaryEquiv p q) : UnitaryEquiv q p := by
  obtain ⟨hp, hq, u, hu⟩ := h
  refine ⟨hq, hp, star u, ?_⟩
  have hU : star (u : S) * (u : S) = 1 := Unitary.coe_star_mul_self u
  calc
    ((star u : unitary S) : S) * q * star ((star u : unitary S) : S)
        = (star (u : S) * (u : S)) * p * (star (u : S) * (u : S)) := by
          simp only [← hu, Unitary.coe_star, star_star, mul_assoc]
    _ = p := by rw [hU, one_mul, mul_one]

/-- Unitary equivalence of star projections is transitive. -/
protected theorem trans (h₁ : UnitaryEquiv p q) (h₂ : UnitaryEquiv q r) : UnitaryEquiv p r := by
  obtain ⟨hp, _, u, hu⟩ := h₁
  obtain ⟨_, hr, v, hv⟩ := h₂
  refine ⟨hp, hr, v * u, ?_⟩
  calc
    ((v * u : unitary S) : S) * p * star ((v * u : unitary S) : S)
        = (v : S) * ((u : S) * p * star (u : S)) * star (v : S) := by
          simp only [Submonoid.coe_mul, star_mul, mul_assoc]
    _ = r := by rw [hu, hv]

end UnitaryEquiv

/-- The witness criterion for unitary equivalence of given star projections. -/
theorem unitaryEquiv_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    UnitaryEquiv p q ↔ ∃ u : unitary S, (u : S) * p * star (u : S) = q :=
  ⟨UnitaryEquiv.exists_unitary, fun h => ⟨hp, hq, h⟩⟩

@[simp]
theorem unitaryEquiv_self_iff : UnitaryEquiv p p ↔ IsStarProjection p :=
  ⟨UnitaryEquiv.isStarProjection_left, UnitaryEquiv.refl⟩

theorem unitaryEquiv_comm : UnitaryEquiv p q ↔ UnitaryEquiv q p :=
  ⟨UnitaryEquiv.symm, UnitaryEquiv.symm⟩

/-- A star projection `p` is unitarily equivalent to `(u : S) * p * star (u : S)` for any unitary
`u`. -/
theorem _root_.IsStarProjection.unitaryEquiv_conj (hp : IsStarProjection p) (u : unitary S) :
    UnitaryEquiv p ((u : S) * p * star (u : S)) :=
  ⟨hp, hp.conj_unitary u, u, rfl⟩

end UnitaryEquiv

section HomotopyEquiv

section

variable {S : Type*} [Mul S] [Star S] [TopologicalSpace S] {p q r : S}

/-- Two elements are homotopy equivalent projections when both are star projections and they are
`Joined` in the subtype `{P : S // IsStarProjection P}`. -/
def HomotopyEquiv (p q : S) : Prop :=
  ∃ (hp : IsStarProjection p) (hq : IsStarProjection q),
    Joined (⟨p, hp⟩ : {P : S // IsStarProjection P}) ⟨q, hq⟩

namespace HomotopyEquiv

/-- The left element of a homotopy equivalence is a star projection. -/
theorem isStarProjection_left (h : HomotopyEquiv p q) : IsStarProjection p := h.1

/-- The right element of a homotopy equivalence is a star projection. -/
theorem isStarProjection_right (h : HomotopyEquiv p q) : IsStarProjection q := h.2.1

/-- The projections `p` and `q` are `Joined` in the projection subtype
`{P : S // IsStarProjection P}` (use `Joined.somePath` if an explicit path value is needed). -/
theorem joined (h : HomotopyEquiv p q) :
    Joined (⟨p, h.isStarProjection_left⟩ : {P : S // IsStarProjection P})
      ⟨q, h.isStarProjection_right⟩ := h.2.2

/-- Every star projection is homotopy equivalent to itself. -/
protected theorem refl (hp : IsStarProjection p) : HomotopyEquiv p p := ⟨hp, hp, .refl _⟩

/-- Homotopy equivalence of star projections is symmetric. -/
protected theorem symm (h : HomotopyEquiv p q) : HomotopyEquiv q p := ⟨h.2.1, h.1, h.2.2.symm⟩

/-- Homotopy equivalence of star projections is transitive. -/
protected theorem trans (h₁ : HomotopyEquiv p q) (h₂ : HomotopyEquiv q r) :
    HomotopyEquiv p r := ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩

end HomotopyEquiv

/-- The witness criterion for homotopy equivalence of given star projections. -/
theorem homotopyEquiv_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    HomotopyEquiv p q ↔ Joined (⟨p, hp⟩ : {P : S // IsStarProjection P}) ⟨q, hq⟩ :=
  ⟨HomotopyEquiv.joined, fun h => ⟨hp, hq, h⟩⟩

@[simp]
theorem homotopyEquiv_self_iff : HomotopyEquiv p p ↔ IsStarProjection p :=
  ⟨HomotopyEquiv.isStarProjection_left, HomotopyEquiv.refl⟩

theorem homotopyEquiv_comm : HomotopyEquiv p q ↔ HomotopyEquiv q p :=
  ⟨HomotopyEquiv.symm, HomotopyEquiv.symm⟩

end

section

variable {S : Type*} [Monoid S] [StarMul S] [TopologicalSpace S] [ContinuousMul S]
  [ContinuousStar S] {p q : S}

/-- Conjugating a star projection `p` by a unitary in the identity component yields a homotopy
equivalent projection. -/
theorem _root_.IsStarProjection.homotopyEquiv_conj_of_joined_one (hp : IsStarProjection p)
    {u : unitary S} (hu : Joined (1 : unitary S) u) :
    HomotopyEquiv p ((u : S) * p * star (u : S)) := by
  refine ⟨hp, hp.conj_unitary u, ?_⟩
  let φ : unitary S → {P : S // IsStarProjection P} :=
    fun v => ⟨(v : S) * p * star (v : S), hp.conj_unitary v⟩
  have hφ : Continuous φ :=
    ((continuous_subtypeVal.mul continuous_const).mul continuous_subtypeVal.star).subtype_mk _
  simpa [φ] using hu.map hφ

/-- Projections conjugated by a unitary joined to `1` are homotopy equivalent. -/
theorem _root_.IsStarProjection.homotopyEquiv_of_joined_one_unitary_conj (hp : IsStarProjection p)
    {u : unitary S} (hu : Joined (1 : unitary S) u)
    (hu_conj : (u : S) * p * star (u : S) = q) : HomotopyEquiv p q :=
  hu_conj ▸ hp.homotopyEquiv_conj_of_joined_one hu

end

end HomotopyEquiv

end TauCeti

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

end CStarMatrix
