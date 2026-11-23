/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.PartialIsometry
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Connected.PathConnected

/-!
# Projection equivalences: unitary, homotopy, and rectangular Murray–von Neumann

This file defines projection unitary equivalence (`TauCeti.IsUnitarilyEquivalent`) on any star
monoid, projection homotopy (`TauCeti.IsHomotopicProjection`) on any topological star magma
(together with conjugacy by a unitary in the identity component), and rectangular Murray–von Neumann
equivalence (`CStarMatrix.MurrayVonNeumannEquiv`) across rectangular matrices.

Matrix projections are Murray–von Neumann equivalent when they are the initial and final
projections of a rectangular partial isometry. The index types may differ, so this relation
identifies a projection with its zero padding, without identifying different matrix sizes by casts.

We prove reflexivity on projections, symmetry, transitivity, partial-isometry and proper-star
characterizations, compatibility with block sums, amplification, reindexing, orthogonal sums, and
unitary conjugacy, and preservation by nonunital star homomorphisms. These are the relations needed
to form the projection monoid (unitization descent, stabilized unitary conjugacy, and stabilized
projection paths are in `TauCeti.Analysis.CStarAlgebra.Projection.Stabilization`). No unit,
separability, or cancellation is assumed.

The algebraic matrix calculations use Mathlib's underlying `Matrix` operations, which are the
operations used to define `CStarMatrix` multiplication and conjugate transpose.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, §4.6 (Definition 4.6.1) and §5.1.
-/

public section

open scoped Matrix

namespace TauCeti

section IsUnitarilyEquivalent

variable {S : Type*} [Monoid S] [StarMul S] {p q r : S}

/-- Two elements are unitarily equivalent projections when both are star projections and some
unitary `u : unitary S` satisfies `(u : S) * p * star (u : S) = q`. -/
def IsUnitarilyEquivalent (p q : S) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧ ∃ u : unitary S, (u : S) * p * star (u : S) = q

namespace IsUnitarilyEquivalent

/-- The left element of a unitary equivalence is a star projection. -/
theorem isStarProjection_left (h : IsUnitarilyEquivalent p q) : IsStarProjection p := h.1

/-- The right element of a unitary equivalence is a star projection. -/
theorem isStarProjection_right (h : IsUnitarilyEquivalent p q) : IsStarProjection q := h.2.1

/-- Extract a unitary conjugating `p` to `q`. -/
theorem exists_unitary (h : IsUnitarilyEquivalent p q) :
    ∃ u : unitary S, (u : S) * p * star (u : S) = q := h.2.2

/-- Every star projection is unitarily equivalent to itself. -/
protected theorem refl (hp : IsStarProjection p) : IsUnitarilyEquivalent p p := ⟨hp, hp, 1, by simp⟩

/-- Unitary equivalence of star projections is symmetric. -/
protected theorem symm (h : IsUnitarilyEquivalent p q) : IsUnitarilyEquivalent q p := by
  obtain ⟨hp, hq, u, hu⟩ := h
  refine ⟨hq, hp, star u, ?_⟩
  have hU : star (u : S) * (u : S) = 1 := Unitary.coe_star_mul_self u
  calc
    ((star u : unitary S) : S) * q * star ((star u : unitary S) : S)
        = (star (u : S) * (u : S)) * p * (star (u : S) * (u : S)) := by
          simp only [← hu, Unitary.coe_star, star_star, mul_assoc]
    _ = p := by rw [hU, one_mul, mul_one]

/-- Unitary equivalence of star projections is transitive. -/
protected theorem trans (h₁ : IsUnitarilyEquivalent p q) (h₂ : IsUnitarilyEquivalent q r) :
    IsUnitarilyEquivalent p r := by
  obtain ⟨hp, _, u, hu⟩ := h₁
  obtain ⟨_, hr, v, hv⟩ := h₂
  refine ⟨hp, hr, v * u, ?_⟩
  calc
    ((v * u : unitary S) : S) * p * star ((v * u : unitary S) : S)
        = (v : S) * ((u : S) * p * star (u : S)) * star (v : S) := by
          simp only [Submonoid.coe_mul, star_mul, mul_assoc]
    _ = r := by rw [hu, hv]

end IsUnitarilyEquivalent

/-- The witness criterion for unitary equivalence of given star projections. -/
theorem isUnitarilyEquivalent_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsUnitarilyEquivalent p q ↔ ∃ u : unitary S, (u : S) * p * star (u : S) = q :=
  ⟨IsUnitarilyEquivalent.exists_unitary, fun h => ⟨hp, hq, h⟩⟩

@[simp]
theorem isUnitarilyEquivalent_self_iff : IsUnitarilyEquivalent p p ↔ IsStarProjection p :=
  ⟨IsUnitarilyEquivalent.isStarProjection_left, IsUnitarilyEquivalent.refl⟩

theorem isUnitarilyEquivalent_comm : IsUnitarilyEquivalent p q ↔ IsUnitarilyEquivalent q p :=
  ⟨IsUnitarilyEquivalent.symm, IsUnitarilyEquivalent.symm⟩

/-- A star projection `p` is unitarily equivalent to `(u : S) * p * star (u : S)` for any unitary
`u`. -/
theorem _root_.IsStarProjection.isUnitarilyEquivalent_conj (hp : IsStarProjection p)
    (u : unitary S) :
    IsUnitarilyEquivalent p ((u : S) * p * star (u : S)) :=
  ⟨hp, hp.conj_unitary u, u, rfl⟩

end IsUnitarilyEquivalent

section IsHomotopicProjection

section

variable {S : Type*} [Mul S] [Star S] [TopologicalSpace S] {p q r : S}

/-- Two elements are homotopic star projections when both are star projections and they are
`Joined` in the subtype `{P : S // IsStarProjection P}`. -/
def IsHomotopicProjection (p q : S) : Prop :=
  ∃ (hp : IsStarProjection p) (hq : IsStarProjection q),
    Joined (⟨p, hp⟩ : {P : S // IsStarProjection P}) ⟨q, hq⟩

namespace IsHomotopicProjection

/-- The left element of a projection homotopy is a star projection. -/
theorem isStarProjection_left (h : IsHomotopicProjection p q) : IsStarProjection p := h.1

/-- The right element of a projection homotopy is a star projection. -/
theorem isStarProjection_right (h : IsHomotopicProjection p q) : IsStarProjection q := h.2.1

/-- The projections `p` and `q` are `Joined` in the projection subtype
`{P : S // IsStarProjection P}` (use `Joined.somePath` if an explicit path value is needed). -/
theorem joined (h : IsHomotopicProjection p q) :
    Joined (⟨p, h.isStarProjection_left⟩ : {P : S // IsStarProjection P})
      ⟨q, h.isStarProjection_right⟩ := h.2.2

/-- Every star projection is homotopic to itself. -/
protected theorem refl (hp : IsStarProjection p) : IsHomotopicProjection p p := ⟨hp, hp, .refl _⟩

/-- Projection homotopy is symmetric. -/
protected theorem symm (h : IsHomotopicProjection p q) : IsHomotopicProjection q p :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- Projection homotopy is transitive. -/
protected theorem trans (h₁ : IsHomotopicProjection p q) (h₂ : IsHomotopicProjection q r) :
    IsHomotopicProjection p r := ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩

end IsHomotopicProjection

/-- The witness criterion for projection homotopy of given star projections. -/
theorem isHomotopicProjection_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsHomotopicProjection p q ↔ Joined (⟨p, hp⟩ : {P : S // IsStarProjection P}) ⟨q, hq⟩ :=
  ⟨IsHomotopicProjection.joined, fun h => ⟨hp, hq, h⟩⟩

@[simp]
theorem isHomotopicProjection_self_iff : IsHomotopicProjection p p ↔ IsStarProjection p :=
  ⟨IsHomotopicProjection.isStarProjection_left, IsHomotopicProjection.refl⟩

theorem isHomotopicProjection_comm :
    IsHomotopicProjection p q ↔ IsHomotopicProjection q p :=
  ⟨IsHomotopicProjection.symm, IsHomotopicProjection.symm⟩

end

section

variable {S : Type*} [Monoid S] [StarMul S] [TopologicalSpace S] [ContinuousMul S]
  [ContinuousStar S] {p q : S}

/-- Conjugating a star projection `p` by a unitary in the identity component yields a homotopic
projection. -/
theorem _root_.IsStarProjection.isHomotopicProjection_conj_of_joined_one (hp : IsStarProjection p)
    {u : unitary S} (hu : Joined (1 : unitary S) u) :
    IsHomotopicProjection p ((u : S) * p * star (u : S)) := by
  refine ⟨hp, hp.conj_unitary u, ?_⟩
  let φ : unitary S → {P : S // IsStarProjection P} :=
    fun v => ⟨(v : S) * p * star (v : S), hp.conj_unitary v⟩
  have hφ : Continuous φ :=
    ((continuous_subtypeVal.mul continuous_const).mul continuous_subtypeVal.star).subtype_mk _
  simpa [φ] using hu.map hφ

/-- Projections conjugated by a unitary joined to `1` are homotopic. -/
theorem _root_.IsStarProjection.isHomotopicProjection_of_joined_one_unitary_conj
    (hp : IsStarProjection p) {u : unitary S} (hu : Joined (1 : unitary S) u)
    (hu_conj : (u : S) * p * star (u : S) = q) : IsHomotopicProjection p q :=
  hu_conj ▸ hp.isHomotopicProjection_conj_of_joined_one hu

end

end IsHomotopicProjection

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

section
variable {o R : Type*} [Fintype o]

/-- `CStarMatrix.MurrayVonNeumannEquiv` coincides with `Matrix.IsMurrayVonNeumannEquivalent` on
underlying matrices via `ofMatrix.symm`. -/
theorem murrayVonNeumannEquiv_iff_matrix [NonUnitalSemiring A] [StarRing A]
    {p : CStarMatrix m m A} {q : CStarMatrix n n A} :
    p.MurrayVonNeumannEquiv q ↔
      Matrix.IsMurrayVonNeumannEquivalent (ofMatrix.symm p) (ofMatrix.symm q) := by
  rw [Matrix.isMurrayVonNeumannEquivalent_iff]
  refine ⟨fun h => let ⟨v, hvp, hvq⟩ := h.exists_matrix
    ⟨isStarProjection_ofMatrix_symm_iff.mpr h.isStarProjection_left,
     isStarProjection_ofMatrix_symm_iff.mpr h.isStarProjection_right, ofMatrix.symm v,
     by rw [← ofMatrix_symm_conjTranspose, ← ofMatrix_symm_mul, hvp],
     by rw [← ofMatrix_symm_conjTranspose, ← ofMatrix_symm_mul, hvq]⟩,
    fun ⟨hp, hq, v, hvp, hvq⟩ => (murrayVonNeumannEquiv_iff
      (isStarProjection_ofMatrix_symm_iff.mp hp) (isStarProjection_ofMatrix_symm_iff.mp hq)).mpr
        ⟨ofMatrix v, ofMatrix.symm.injective (by simp [hvp]),
          ofMatrix.symm.injective (by simp [hvq])⟩⟩

theorem murrayVonNeumannEquiv_comm [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} : p.MurrayVonNeumannEquiv q ↔ q.MurrayVonNeumannEquiv p :=
  ⟨MurrayVonNeumannEquiv.symm, MurrayVonNeumannEquiv.symm⟩

section
variable [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A}

/-- A rectangular partial isometry implements Murray–von Neumann equivalence between its initial
and final projections. -/
theorem IsPartialIsometry.murrayVonNeumannEquiv {v : CStarMatrix n m A} (hv : v.IsPartialIsometry) :
    (v.conjTranspose * v).MurrayVonNeumannEquiv (v * v.conjTranspose) :=
  (murrayVonNeumannEquiv_iff hv.isStarProjection_conjTranspose_mul_self
    hv.isStarProjection_mul_conjTranspose_self).mpr ⟨v, rfl, rfl⟩

/-- Extract a rectangular partial-isometry witness from a Murray–von Neumann equivalence. -/
theorem MurrayVonNeumannEquiv.exists_isPartialIsometry (h : p.MurrayVonNeumannEquiv q) :
    ∃ v : CStarMatrix n m A, v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧
      v * v.conjTranspose = q :=
  let ⟨v, hvp, hvq, hvp_eq⟩ := h.exists_matrix_mul_eq_self
  ⟨v, isPartialIsometry_iff.mpr <| by rw [mul_assoc_rectangular, hvp, hvp_eq], hvp, hvq⟩

/-- Rectangular `MurrayVonNeumannEquiv` holds iff witnessed by a rectangular partial isometry. -/
theorem murrayVonNeumannEquiv_iff_exists_isPartialIsometry :
    p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.IsPartialIsometry ∧ v.conjTranspose * v = p ∧
        v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_isPartialIsometry,
    fun ⟨_, hv, hvp, hvq⟩ => hvp ▸ hvq ▸ hv.murrayVonNeumannEquiv⟩

end

section
variable [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
  {p : CStarMatrix m m A} {q : CStarMatrix n n A}

/-- Over a proper-star ordered ring, idempotent `p ∼ q` iff `∃ v, vᴴ * v = p ∧ v * vᴴ = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_left (hp : IsIdempotentElem p) :
    p.MurrayVonNeumannEquiv q ↔ ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧
      v * v.conjTranspose = q :=
  ⟨MurrayVonNeumannEquiv.exists_matrix, fun ⟨v, hvp, hvq⟩ =>
    murrayVonNeumannEquiv_iff_exists_isPartialIsometry.mpr
      ⟨v, .of_isIdempotentElem_conjTranspose_mul_self (by rwa [hvp]), hvp, hvq⟩⟩

/-- Over a proper-star ordered ring, `p ∼ q` (idempotent `q`) iff `∃ v, vᴴ * v = p ∧ v * vᴴ = q`. -/
theorem murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_right
    (hq : IsIdempotentElem q) : p.MurrayVonNeumannEquiv q ↔
      ∃ v : CStarMatrix n m A, v.conjTranspose * v = p ∧ v * v.conjTranspose = q := by
  rw [murrayVonNeumannEquiv_comm,
    murrayVonNeumannEquiv_iff_exists_mul_eq_of_isIdempotentElem_left hq]
  exact ⟨fun ⟨v, hvq, hvp⟩ => ⟨v.conjTranspose, by simpa using hvp, by simpa using hvq⟩,
    fun ⟨v, hvp, hvq⟩ => ⟨v.conjTranspose, by simpa using hvq, by simpa using hvp⟩⟩

end

namespace MurrayVonNeumannEquiv

/-- `MurrayVonNeumannEquiv` is compatible with `blockSum`. -/
protected theorem blockSum [NonUnitalSemiring A] [StarRing A] {p₁ : CStarMatrix l l A}
    {q₁ : CStarMatrix m m A} {p₂ : CStarMatrix n n A} {q₂ : CStarMatrix o o A}
    (h₁ : p₁.MurrayVonNeumannEquiv q₁) (h₂ : p₂.MurrayVonNeumannEquiv q₂) :
    (CStarMatrix.blockSum p₁ p₂).MurrayVonNeumannEquiv (CStarMatrix.blockSum q₁ q₂) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      (murrayVonNeumannEquiv_iff_matrix.mp h₁).fromBlocks (murrayVonNeumannEquiv_iff_matrix.mp h₂)

/-- Finite block-diagonal amplification preserves rectangular `MurrayVonNeumannEquiv`. -/
protected theorem amplify (k : Type*) [Fintype k] [DecidableEq k] [NonUnitalSemiring A]
    [StarRing A] {p : CStarMatrix m m A} {q : CStarMatrix n n A} (h : p.MurrayVonNeumannEquiv q) :
    (CStarMatrix.amplify k p).MurrayVonNeumannEquiv (CStarMatrix.amplify k q) := by
  rcases h.exists_isPartialIsometry with ⟨v, hv, rfl, rfl⟩
  simpa [amplify_conjTranspose, amplify_mul] using (hv.amplify k).murrayVonNeumannEquiv

end MurrayVonNeumannEquiv

section
variable [NonUnitalSemiring A] [StarRing A]

private theorem mvn_reindexₐ_congr (R) [Semiring R] [Module R A] (e₁ : k ≃ l) (e₂ : m ≃ n)
    {p : CStarMatrix k k A} {q : CStarMatrix m m A} (h : p.MurrayVonNeumannEquiv q) :
    (reindexₐ R A e₁ p).MurrayVonNeumannEquiv (reindexₐ R A e₂ q) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_reindexₐ] using (murrayVonNeumannEquiv_iff_matrix.mp h).reindex e₁ e₂

/-- Reindexing a star projection along a bijection `e : m ≃ n` yields an equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_reindexₐ {p : CStarMatrix m m A}
    (hp : IsStarProjection p) (R : Type*) [Semiring R] [Module R A] (e : m ≃ n) :
    p.MurrayVonNeumannEquiv (reindexₐ R A e p) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_reindexₐ] using
      (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_reindex e

@[simp] theorem murrayVonNeumannEquiv_reindexₐ_right_iff [Semiring R] [Module R A] (e : m ≃ n)
    {p : CStarMatrix l l A} {q : CStarMatrix m m A} :
    p.MurrayVonNeumannEquiv (reindexₐ R A e q) ↔ p.MurrayVonNeumannEquiv q :=
  ⟨fun h => by simpa [reindexₐ_symm] using mvn_reindexₐ_congr R (.refl l) e.symm h,
   fun h => by simpa using mvn_reindexₐ_congr R (.refl l) e h⟩

@[simp] theorem murrayVonNeumannEquiv_reindexₐ_left_iff [Semiring R] [Module R A] (e : l ≃ m)
    {p : CStarMatrix l l A} {q : CStarMatrix n n A} :
    (reindexₐ R A e p).MurrayVonNeumannEquiv q ↔ p.MurrayVonNeumannEquiv q :=
  ⟨fun h => by simpa [reindexₐ_symm] using mvn_reindexₐ_congr R e.symm (.refl n) h,
   fun h => by simpa using mvn_reindexₐ_congr R e (.refl n) h⟩

/-- Padding a star projection by a lower-right zero block yields an equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_blockSum_zero {p : CStarMatrix m m A}
    (hp : IsStarProjection p) (n : Type*) [Fintype n] :
    p.MurrayVonNeumannEquiv (blockSum p (0 : CStarMatrix n n A)) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_fromBlocks_zero

/-- Swapping the two diagonal blocks of `blockSum p q` preserves Murray–von Neumann equivalence. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_blockSum_comm {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    (blockSum p q).MurrayVonNeumannEquiv (blockSum q p) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      Matrix.isMurrayVonNeumannEquivalent_fromBlocks_comm
        (isStarProjection_ofMatrix_symm_iff.mpr hp) (isStarProjection_ofMatrix_symm_iff.mpr hq)

/-- `blockSum` of star projections is associative up to Murray–von Neumann equivalence. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_blockSum_assoc {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} {r : CStarMatrix n n A} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hr : IsStarProjection r) :
    (blockSum (blockSum p q) r).MurrayVonNeumannEquiv (blockSum p (blockSum q r)) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      Matrix.isMurrayVonNeumannEquivalent_fromBlocks_assoc
        (isStarProjection_ofMatrix_symm_iff.mpr hp) (isStarProjection_ofMatrix_symm_iff.mpr hq)
        (isStarProjection_ofMatrix_symm_iff.mpr hr)

/-- Padding a star projection by an upper-left zero block yields an equivalent projection. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_zero_blockSum {q : CStarMatrix n n A}
    (hq : IsStarProjection q) (m : Type*) [Fintype m] :
    q.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix m m A) q) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_blockSum, ofMatrix_symm_zero] using
      (isStarProjection_ofMatrix_symm_iff.mpr hq).isMurrayVonNeumannEquivalent_zero_fromBlocks

@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_right_iff {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} : p.MurrayVonNeumannEquiv (blockSum q (0 : CStarMatrix n n A)) ↔
      p.MurrayVonNeumannEquiv q :=
  ⟨fun h => h.trans ((isStarProjection_blockSum_iff.mp
    h.isStarProjection_right).1.murrayVonNeumannEquiv_blockSum_zero n).symm,
   fun h => h.trans (h.isStarProjection_right.murrayVonNeumannEquiv_blockSum_zero n)⟩

@[simp] theorem murrayVonNeumannEquiv_blockSum_zero_left_iff {p : CStarMatrix l l A}
    {q : CStarMatrix n n A} : (blockSum p (0 : CStarMatrix m m A)).MurrayVonNeumannEquiv q ↔
      p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_blockSum_zero_right_iff,
    murrayVonNeumannEquiv_comm]

@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_right_iff {p : CStarMatrix l l A}
    {q : CStarMatrix m m A} : p.MurrayVonNeumannEquiv (blockSum (0 : CStarMatrix n n A) q) ↔
      p.MurrayVonNeumannEquiv q :=
  ⟨fun h => h.trans ((isStarProjection_blockSum_iff.mp
    h.isStarProjection_right).2.murrayVonNeumannEquiv_zero_blockSum n).symm,
   fun h => h.trans (h.isStarProjection_right.murrayVonNeumannEquiv_zero_blockSum n)⟩

@[simp] theorem murrayVonNeumannEquiv_zero_blockSum_left_iff {p : CStarMatrix m m A}
    {q : CStarMatrix n n A} : (blockSum (0 : CStarMatrix l l A) p).MurrayVonNeumannEquiv q ↔
      p.MurrayVonNeumannEquiv q := by
  rw [murrayVonNeumannEquiv_comm, murrayVonNeumannEquiv_zero_blockSum_right_iff,
    murrayVonNeumannEquiv_comm]

/-- For orthogonal star projections `p₁, p₂`, `p₁ + p₂` is equivalent to `blockSum p₁ p₂`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero
    {p₁ p₂ : CStarMatrix n n A} (hp₁ : IsStarProjection p₁) (hp₂ : IsStarProjection p₂)
    (h₁₂ : p₁ * p₂ = 0) : (p₁ + p₂).MurrayVonNeumannEquiv (blockSum p₁ p₂) := by
  have h1 : (fromRows p₁ p₂).conjTranspose * fromRows p₁ p₂ = p₁ + p₂ := by
    rw [conjTranspose_fromRows_mul_fromRows, hp₁.isSelfAdjoint.conjTranspose_eq,
      hp₂.isSelfAdjoint.conjTranspose_eq, hp₁.isIdempotentElem.eq, hp₂.isIdempotentElem.eq]
  rw [← h1, ← hp₁.fromRows_mul_conjTranspose_fromRows_eq_blockSum hp₂ h₁₂]
  exact (hp₁.isPartialIsometry_fromRows_of_mul_eq_zero hp₂ h₁₂).murrayVonNeumannEquiv

/-- Orthogonal sums of pairwise Murray–von Neumann equivalent projections are equivalent. -/
theorem MurrayVonNeumannEquiv.add_of_mul_eq_zero {p₁ p₂ : CStarMatrix m m A}
    {q₁ q₂ : CStarMatrix n n A} (h₁ : p₁.MurrayVonNeumannEquiv q₁)
    (h₂ : p₂.MurrayVonNeumannEquiv q₂) (hp : p₁ * p₂ = 0) (hq : q₁ * q₂ = 0) :
    (p₁ + p₂).MurrayVonNeumannEquiv (q₁ + q₂) :=
  (h₁.isStarProjection_left.murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero
    h₂.isStarProjection_left hp).trans <| (h₁.blockSum h₂).trans
      (h₁.isStarProjection_right.murrayVonNeumannEquiv_add_blockSum_of_mul_eq_zero
        h₂.isStarProjection_right hq).symm

/-- If `uᴴ * u` acts as the identity on the range of a star projection `p`, then
`p ∼ u * p * uᴴ`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_mul_eq
    {p : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u * p = p) :
    p.MurrayVonNeumannEquiv (u * p * u.conjTranspose) :=
  murrayVonNeumannEquiv_iff_matrix.mpr <| by
    simpa only [ofMatrix_symm_mul, ofMatrix_symm_conjTranspose] using
      (isStarProjection_ofMatrix_symm_iff.mpr hp).isMurrayVonNeumannEquivalent_mul_mul_conjTranspose
        (w := ofMatrix.symm u) (by
          simpa only [← ofMatrix_symm_mul, ← ofMatrix_symm_conjTranspose] using
            congrArg ofMatrix.symm hu)

end

/-- Conjugating a star projection `p` by an isometry `u` (`uᴴ * u = 1`) gives `p ∼ u * p * uᴴ`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_eq_one
    [DecidableEq n] [Semiring A] [StarRing A] {p : CStarMatrix n n A} (hp : IsStarProjection p)
    {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) :
    p.MurrayVonNeumannEquiv (u * p * u.conjTranspose) :=
  hp.murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_mul_eq (by rw [hu, CStarMatrix.one_mul])

section
variable [DecidableEq n] [Semiring A] [StarRing A] {p q : CStarMatrix n n A}

/-- Unitarily equivalent square matrix projections are Murray–von Neumann equivalent. -/
theorem _root_.TauCeti.IsUnitarilyEquivalent.murrayVonNeumannEquiv
    (h : TauCeti.IsUnitarilyEquivalent p q) : p.MurrayVonNeumannEquiv q := by
  obtain ⟨u, hu⟩ := h.exists_unitary
  rw [← hu, star_eq_conjTranspose]
  exact h.isStarProjection_left.murrayVonNeumannEquiv_conj_of_conjTranspose_mul_self_eq_one
    (by rw [← star_eq_conjTranspose, Unitary.coe_star_mul_self u])

/-- A square matrix projection `p` is Murray–von Neumann equivalent to `u * p * star u` for any
unitary `u`. -/
theorem _root_.IsStarProjection.murrayVonNeumannEquiv_conj_unitary (hp : IsStarProjection p)
    (u : unitary (CStarMatrix n n A)) :
    p.MurrayVonNeumannEquiv ((u : CStarMatrix n n A) * p * star (u : CStarMatrix n n A)) :=
  (hp.isUnitarilyEquivalent_conj u).murrayVonNeumannEquiv

end

end

end CStarMatrix
