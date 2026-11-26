/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.PosSemidef
import TauCeti.LinearAlgebra.QuadraticForm.Even

/-!
# Positive definite quadratic maps

Multiplication by a positive scalar preserves and reflects positive-definiteness when the scalar
action preserves and reflects strict inequalities on values. In particular, symmetrizing a
bilinear form preserves positive-definiteness of its quadratic map, since the diagonal values
are doubled. A diagonal form is positive definite exactly when its weights are positive, and a
form is positive definite on the line spanned by any vector of positive value. The quadratic form
of a symmetric bilinear form is positive definite exactly when the bilinear form is positive
semidefinite and nondegenerate.

A positive definite quadratic form on a finitely generated `ℤ`-module takes each of its values
only finitely often: the sets `{x | q x ≤ n}` and `{x | q x = n}` are finite. This is the
finiteness that makes "the vectors of norm `n`" of a positive definite lattice a finite list, and
the one that turns an orbit lying in a level set into a periodic orbit.

## Main results

* `QuadraticMap.PosDef.comp`: injective pullback preserves positive definiteness.
* `LinearMap.BilinForm.posDef_toQuadraticMap_iff`: positive definiteness is positivity
  of the diagonal at nonzero vectors.
* `LinearMap.BilinForm.posDef_toQuadraticMap_compl₁₂`: an injective pullback preserves
  positive definiteness of a bilinear form's quadratic map.
* `QuadraticMap.posDef_smul_iff_of_pos`: a quadratic map is positive definite if and only if
  its multiple by a positive scalar is positive definite.
* `LinearMap.BilinForm.posDef_toQuadraticMap_add_flip_iff`: symmetrizing a bilinear form
  preserves and reflects positive-definiteness of its quadratic map.
* `LinearMap.BilinForm.posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate`: over a linearly
  ordered ring, the quadratic form of a symmetric bilinear form is positive definite exactly when
  the form is positive semidefinite and nondegenerate.
* `QuadraticMap.posDef_weightedSumSquares_iff`: a diagonal form over a linearly ordered ring is
  positive definite exactly when all of its weights are positive.
* `QuadraticMap.posDef_restrict_span_singleton`: a quadratic form is positive definite on the
  line spanned by a vector of positive value.
* `TauCeti.exists_posDef_quadraticForm`: every finitely generated free module over a strictly
  linearly ordered commutative ring admits a positive-definite quadratic form.
* `QuadraticMap.PosDef.finite_setOf_apply_le`: a positive definite quadratic form on a
  finitely generated `ℤ`-module has only finitely many vectors of value at most `n`.
* `QuadraticMap.PosDef.finite_setOf_apply_eq`: consequently only finitely many vectors of
  value exactly `n`.

The finiteness results live in the root `QuadraticMap.PosDef` namespace so that they are
available by dot notation on a `QuadraticForm.PosDef` hypothesis.

## Implementation notes

A positive definite form makes the module torsion free, hence free; let `b` be a basis. The Gram
matrix of the polar form in `b` is a positive definite integer matrix, since the polar form is
symmetric with diagonal `2 • q`, and its sublevel sets are finite by Mathlib's
`Matrix.PosDef.finite_setOfPred_dotProduct_mulVec_le`. The set in question is the preimage of one
of them under the injective coordinate map `b.equivFun`.
-/

public section

/-- An injective pullback of a positive-definite quadratic map is positive definite. -/
theorem QuadraticMap.PosDef.comp {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [PartialOrder N]
    [AddCommMonoid P] [Module R P] {Q : QuadraticMap R M N} (hQ : Q.PosDef)
    (f : P →ₗ[R] M) (hf : Function.Injective f) : (Q.comp f).PosDef := by
  intro x hx
  exact hQ (f x) (fun h ↦ hx (hf (h.trans (map_zero f).symm)))

namespace QuadraticMap

variable {R M N : Type*} [CommSemiring R] [Preorder R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [PartialOrder N] [Module R N]
  [PosSMulStrictMono R N] [PosSMulReflectLT R N]

/-- Multiplication by a positive scalar preserves and reflects positive-definiteness when the
scalar action preserves and reflects strict inequalities on values. -/
@[simp]
theorem posDef_smul_iff_of_pos (Q : QuadraticMap R M N) {a : R} (ha : 0 < a) :
    (a • Q).PosDef ↔ Q.PosDef :=
  forall₂_congr fun _ _ ↦ smul_pos_iff_of_pos_left ha

end QuadraticMap

namespace QuadraticMap

variable {ι : Type*} [Fintype ι]

/-- A diagonal form `⟨w₁, …, wₙ⟩` over a linearly ordered ring is positive definite exactly when
all of its weights are positive. -/
theorem posDef_weightedSumSquares_iff {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (w : ι → R) :
    (weightedSumSquares R w).PosDef ↔ ∀ i, 0 < w i := by
  classical
  refine ⟨fun h i ↦ by simpa [Pi.single_apply] using h (Pi.single i 1) (by simp),
    fun h x hx ↦ ?_⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  rw [weightedSumSquares_apply]
  exact Finset.sum_pos' (fun j _ ↦ mul_nonneg (h j).le (mul_self_nonneg _))
    ⟨i, Finset.mem_univ i, mul_pos (h i) (mul_self_pos.mpr hi)⟩

/-- A quadratic form over a linearly ordered ring is positive definite on the line spanned by a
vector of positive value. -/
theorem posDef_restrict_span_singleton {R M : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [AddCommGroup M] [Module R M] {Q : QuadraticForm R M} {y : M}
    (hy : 0 < Q y) : (Q.restrict (R ∙ y)).PosDef := by
  rintro ⟨w, hw⟩ hw0
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw0 (by simp)
  rw [restrict_apply, QuadraticMap.map_smul, smul_eq_mul]
  exact mul_pos (mul_self_pos.mpr hc) hy

end QuadraticMap

namespace LinearMap.BilinForm

/-- Positive definiteness of a bilinear form's quadratic map is positivity on nonzero vectors. -/
theorem posDef_toQuadraticMap_iff {R M : Type*} [CommSemiring R] [PartialOrder R]
    [AddCommMonoid M] [Module R M] (B : LinearMap.BilinForm R M) :
    B.toQuadraticMap.PosDef ↔ ∀ x ≠ 0, 0 < B x x := by
  simp only [QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply]

/-- An injective pullback preserves positive definiteness of the diagonal of a bilinear form. -/
theorem posDef_toQuadraticMap_compl₁₂ {R M N : Type*} [CommSemiring R] [PartialOrder R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (B : LinearMap.BilinForm R M) (hB : B.toQuadraticMap.PosDef)
    (f : N →ₗ[R] M) (hf : Function.Injective f) :
    (LinearMap.BilinMap.toQuadraticMap (B.compl₁₂ f f)).PosDef := by
  rw [LinearMap.BilinMap.toQuadraticMap_comp_same]
  exact hB.comp f hf

/-- Symmetrization preserves and reflects positive-definiteness of a bilinear form's quadratic
map. -/
theorem posDef_toQuadraticMap_add_flip_iff {R M : Type*} [CommSemiring R] [LinearOrder R]
    [IsStrictOrderedRing R] [AddCommMonoid M] [Module R M] (B : LinearMap.BilinForm R M) :
    (B + B.flip).toQuadraticMap.PosDef ↔ B.toQuadraticMap.PosDef := by
  have hflip : B.flip.toQuadraticMap = B.toQuadraticMap := by
    ext x
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.BilinForm.flip_apply]
  rw [LinearMap.BilinMap.toQuadraticMap_add, hflip, ← two_smul R B.toQuadraticMap]
  exact QuadraticMap.posDef_smul_iff_of_pos _ (a := (2 : R)) zero_lt_two

/-- The quadratic form of a symmetric bilinear form is positive-definite if and only if the
bilinear form is positive-semidefinite and nondegenerate. -/
@[grind =]
theorem posDef_toQuadraticMap_iff_isPosSemidef_and_nondegenerate {R M : Type*} [CommRing R]
    [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (hB : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ B.IsPosSemidef ∧ B.Nondegenerate := by
  have hB' : LinearMap.IsSymm B := LinearMap.BilinForm.isSymm_iff.mp hB
  rw [isPosSemidef_iff_forall_nonneg B hB]
  refine ⟨fun h ↦ ?_, fun ⟨hnn, hnd⟩ ↦ ?_⟩
  · have hnn : ∀ x, 0 ≤ B x x := fun x ↦ by simpa using h.nonneg x
    refine ⟨hnn, (LinearMap.BilinForm.nondegenerate_iff' B hnn hB').mpr ?_⟩
    simpa only [QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply] using h
  · simpa only [QuadraticMap.PosDef, LinearMap.BilinMap.toQuadraticMap_apply] using
      (LinearMap.BilinForm.nondegenerate_iff' B hnn hB').mp hnd

end LinearMap.BilinForm

namespace TauCeti

/-- Every finitely generated free module over a strictly linearly ordered commutative ring admits a
positive-definite quadratic form. -/
theorem exists_posDef_quadraticForm (R W : Type*) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W] :
    ∃ Q₀ : QuadraticForm R W, Q₀.PosDef := by
  classical
  let b := Module.Free.chooseBasis R W
  exact ⟨_, ((QuadraticMap.posDef_weightedSumSquares_iff
    (fun _ : Module.Free.ChooseBasisIndex R W ↦ (1 : R))).mpr fun _ ↦ zero_lt_one).comp
    b.equivFun.toLinearMap b.equivFun.injective⟩

end TauCeti

namespace QuadraticMap.PosDef

variable {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]

/-- **A positive definite integral quadratic form has finitely many vectors of bounded value.**
For a positive definite quadratic form `q` on a finitely generated `ℤ`-module (which is then free,
being torsion free) and any integer `n`, only finitely many vectors satisfy `q x ≤ n`. -/
theorem finite_setOf_apply_le {q : QuadraticForm ℤ M} (hq : q.PosDef) (n : ℤ) :
    {x : M | q x ≤ n}.Finite := by
  classical
  -- A positive definite form makes `M` torsion free, hence free over the PID `ℤ`.
  have : Module.IsTorsionFree ℤ M := ⟨fun r hr x y (hxy : r • x = r • y) ↦ by
    by_contra hne
    have hz := hq (x - y) (sub_ne_zero.mpr hne)
    have h := q.map_smul r (x - y)
    rw [smul_sub, hxy, sub_self, QuadraticMap.map_zero, smul_eq_mul] at h
    exact (mul_pos (mul_self_pos.mpr hr.ne_zero) hz).ne h⟩
  let b := Module.Free.chooseBasis ℤ M
  -- The Gram matrix of the polar form in `b` is a positive definite integer matrix, because the
  -- diagonal of the polar form is `2 • q`.
  have hA : (LinearMap.BilinForm.toMatrix b q.polarBilin).PosDef := by
    refine (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b _ q.isSymm_polarBilin).mp ?_
    rw [QuadraticMap.toQuadraticMap_polarBilin]
    exact hq.smul zero_lt_two
  -- In the coordinates `b.repr x`, the bound `q x ≤ n` reads `B x x ≤ 2 * n` for the Gram
  -- matrix of the polar form `B`, whose sublevel sets are finite.
  refine ((hA.finite_setOfPred_dotProduct_mulVec_le (2 * n)).preimage
    b.equivFun.injective.injOn).subset fun x (hx : q x ≤ n) ↦ ?_
  rw [Set.mem_preimage, Set.mem_ofPred_eq, b.equivFun_apply,
    ← LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec, q.polarBilin_self x]
  omega

/-- **A positive definite integral quadratic form takes each value finitely often.** For a
positive definite quadratic form `q` on a finitely generated `ℤ`-module, only finitely many
vectors satisfy `q x = n`; for a positive definite lattice this is the finiteness of the set of
vectors of a given norm. -/
theorem finite_setOf_apply_eq {q : QuadraticForm ℤ M} (hq : q.PosDef) (n : ℤ) :
    {x : M | q x = n}.Finite :=
  (finite_setOf_apply_le hq n).subset fun _ hx ↦ le_of_eq hx

end QuadraticMap.PosDef
