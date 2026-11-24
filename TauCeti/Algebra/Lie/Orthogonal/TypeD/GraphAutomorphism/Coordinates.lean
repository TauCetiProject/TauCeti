/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.Folding.Eigenspaces
import TauCeti.Algebra.Lie.Orthogonal.Basic

/-!
# Coordinates for the type-D graph involution

The two equal coordinates in the chosen hyperbolic pair give the norm-two line
of the native odd orthogonal form. The remaining pairs retain their coordinates.
Inclusion and averaging projection split this space from the anti-invariant line.
These rectangular matrices supply the coordinate maps for restriction and extension
of fixed orthogonal operators.

The linear equivalence `typeDGraphSplitAt` is the eigenspace decomposition `typeDGraphSplit`
with its distinguished index moved from `none` to an arbitrary index `c`, along
`Equiv.optionSubtypeNe c`. The four coordinate matrices are the matrices of the blocks of this
equivalence and of its inverse. Their identities are therefore its inverse laws, its swap
action and its Gram decomposition, each inherited from `typeDGraphSplit`.
-/

public section

open Matrix LieAlgebra.Orthogonal

namespace TauCeti

variable {I : Type*} [DecidableEq I] (c : I) (A : Type*) [CommRing A]

/-- Moving the distinguished index from `none` to `c` commutes with the hyperbolic-pair swap. -/
private theorem sumMap_optionSubtypeNe_symm_typeDGraphIndex (s : I ⊕ I) :
    Sum.map (Equiv.optionSubtypeNe c).symm (Equiv.optionSubtypeNe c).symm (typeDGraphIndex c s) =
      typeDGraphIndex (none : Option {i : I // i ≠ c})
        (Sum.map (Equiv.optionSubtypeNe c).symm (Equiv.optionSubtypeNe c).symm s) := by
  rcases s with i | i <;> obtain rfl | hi := eq_or_ne i c <;> simp [*]

variable [Invertible (2 : A)]

/-- The eigenspace coordinates `typeDGraphSplit` of the hyperbolic-pair swap, with the
distinguished pair at an arbitrary index `c` and the remaining pairs indexed by the other
indices. The first summand is the fixed space and the second is the anti-fixed line. -/
def typeDGraphSplitAt :
    (((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A) ≃ₗ[A] ((I ⊕ I) → A) :=
  typeDGraphSplit {i : I // i ≠ c} A ≪≫ₗ
    LinearEquiv.funCongrLeft A A
      ((Equiv.optionSubtypeNe c).sumCongr (Equiv.optionSubtypeNe c)).symm

/-- The coordinates at `c` are those of `typeDGraphSplit` after renaming `c` to `none`. -/
theorem typeDGraphSplitAt_apply (p : ((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A)
    (s : I ⊕ I) :
    typeDGraphSplitAt c A p s = typeDGraphSplit {i : I // i ≠ c} A p
      (Sum.map (Equiv.optionSubtypeNe c).symm (Equiv.optionSubtypeNe c).symm s) :=
  (rfl)

/-- The inverse coordinates at `c` are those of `typeDGraphSplit` after renaming `none`
to `c`. -/
theorem typeDGraphSplitAt_symm_apply (v : I ⊕ I → A) :
    (typeDGraphSplitAt c A).symm v = (typeDGraphSplit {i : I // i ≠ c} A).symm
      fun s => v (Sum.map (Equiv.optionSubtypeNe c) (Equiv.optionSubtypeNe c) s) :=
  (rfl)

/-- The chosen positive coordinate is the sum of the norm-two and anti-fixed coordinates. -/
@[simp]
theorem typeDGraphSplitAt_inl_self
    (p : ((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A) :
    typeDGraphSplitAt c A p (.inl c) = p.1 (.inl ()) + p.2 := by
  simp [typeDGraphSplitAt_apply]

/-- The chosen negative coordinate is the difference of the norm-two and anti-fixed
coordinates. -/
@[simp]
theorem typeDGraphSplitAt_inr_self
    (p : ((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A) :
    typeDGraphSplitAt c A p (.inr c) = p.1 (.inl ()) - p.2 := by
  simp [typeDGraphSplitAt_apply]

/-- Outside the chosen pair, a positive coordinate is the corresponding fixed coordinate. -/
@[simp]
theorem typeDGraphSplitAt_inl_of_ne
    (p : ((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A) {i : I} (hi : i ≠ c) :
    typeDGraphSplitAt c A p (.inl i) = p.1 (.inr (.inl ⟨i, hi⟩)) := by
  simp [typeDGraphSplitAt_apply, hi]

/-- Outside the chosen pair, a negative coordinate is the corresponding fixed coordinate. -/
@[simp]
theorem typeDGraphSplitAt_inr_of_ne
    (p : ((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A) {i : I} (hi : i ≠ c) :
    typeDGraphSplitAt c A p (.inr i) = p.1 (.inr (.inr ⟨i, hi⟩)) := by
  simp [typeDGraphSplitAt_apply, hi]

/-- The norm-two coordinate is the average of the chosen pair. -/
@[simp]
theorem typeDGraphSplitAt_symm_fst_inl (v : I ⊕ I → A) (u : Unit) :
    ((typeDGraphSplitAt c A).symm v).1 (.inl u) = ⅟(2 : A) * (v (.inl c) + v (.inr c)) := by
  simp [typeDGraphSplitAt_symm_apply]

/-- The fixed coordinates retain the positive coordinates outside the chosen pair. -/
@[simp]
theorem typeDGraphSplitAt_symm_fst_inr_inl (v : I ⊕ I → A) (i : {i : I // i ≠ c}) :
    ((typeDGraphSplitAt c A).symm v).1 (.inr (.inl i)) = v (.inl i.val) := by
  simp [typeDGraphSplitAt_symm_apply]

/-- The fixed coordinates retain the negative coordinates outside the chosen pair. -/
@[simp]
theorem typeDGraphSplitAt_symm_fst_inr_inr (v : I ⊕ I → A) (i : {i : I // i ≠ c}) :
    ((typeDGraphSplitAt c A).symm v).1 (.inr (.inr i)) = v (.inr i.val) := by
  simp [typeDGraphSplitAt_symm_apply]

/-- The anti-fixed coordinate is half the difference of the chosen pair. -/
@[simp]
theorem typeDGraphSplitAt_symm_snd (v : I ⊕ I → A) :
    ((typeDGraphSplitAt c A).symm v).2 = ⅟(2 : A) * (v (.inl c) - v (.inr c)) := by
  simp [typeDGraphSplitAt_symm_apply]

/-- In the coordinates at `c`, the hyperbolic-pair swap acts by `(x, t) ↦ (x, -t)`. -/
theorem typeDGraphSplitAt_graphIndex
    (p : ((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A) :
    (fun s => typeDGraphSplitAt c A p (typeDGraphIndex c s)) =
      typeDGraphSplitAt c A (p.1, -p.2) := by
  ext s
  rw [typeDGraphSplitAt_apply, typeDGraphSplitAt_apply,
    sumMap_optionSubtypeNe_symm_typeDGraphIndex]
  exact congrFun (typeDGraphSplit_graphIndex {i : I // i ≠ c} A p) _

variable [Fintype I]

/-- The coordinates at `c` split the even orthogonal form into the native odd orthogonal
form and a line of norm `-2`. -/
@[simp]
theorem typeDGraphSplitAt_bilin
    (p q : ((Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) → A) × A) :
    (JD I A).toBilin' (typeDGraphSplitAt c A p) (typeDGraphSplitAt c A q) =
      (JB {i : I // i ≠ c} A).toBilin' p.1 q.1 - 2 * p.2 * q.2 := by
  rw [← typeDGraphSplit_bilin]
  exact toBilin'_JD_comp_sumMap (Equiv.optionSubtypeNe c).symm _ _

/-- Include the native odd coordinates by repeating the distinguished coordinate: the matrix
of the fixed-space summand of `typeDGraphSplitAt`. -/
def typeDGraphInclusion : Matrix (I ⊕ I) (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) A :=
  LinearMap.toMatrix' ((typeDGraphSplitAt c A).toLinearMap ∘ₗ LinearMap.inl A _ A)

/-- The anti-invariant line is generated by the difference of the chosen coordinates: the
matrix of the anti-fixed summand of `typeDGraphSplitAt`. -/
def typeDGraphAntiInclusion : Matrix (I ⊕ I) Unit A :=
  LinearMap.toMatrix' ((typeDGraphSplitAt c A).toLinearMap ∘ₗ LinearMap.inr A _ A ∘ₗ
    LinearMap.proj ())

/-- Average the chosen coordinates and retain every remaining hyperbolic pair: the matrix of
the fixed-space component of the inverse of `typeDGraphSplitAt`. -/
def typeDGraphProjection : Matrix (Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c}) (I ⊕ I) A :=
  LinearMap.toMatrix' (LinearMap.fst A _ A ∘ₗ (typeDGraphSplitAt c A).symm.toLinearMap)

/-- Read half the difference of the two chosen coordinates: the matrix of the anti-fixed
component of the inverse of `typeDGraphSplitAt`. -/
def typeDGraphAntiProjection : Matrix Unit (I ⊕ I) A :=
  LinearMap.toMatrix' (LinearMap.pi fun _ : Unit =>
    LinearMap.snd A _ A ∘ₗ (typeDGraphSplitAt c A).symm.toLinearMap)

/-- Inclusion sends native odd coordinates to the fixed vector with those coordinates. -/
@[simp]
theorem typeDGraphInclusion_mulVec (x : Unit ⊕ {i : I // i ≠ c} ⊕ {i : I // i ≠ c} → A) :
    typeDGraphInclusion c A *ᵥ x = typeDGraphSplitAt c A (x, 0) := by
  simp [typeDGraphInclusion]

omit [Fintype I] in
/-- Anti-inclusion sends a scalar to the anti-fixed vector with that coordinate. -/
@[simp]
theorem typeDGraphAntiInclusion_mulVec (x : Unit → A) :
    typeDGraphAntiInclusion c A *ᵥ x = typeDGraphSplitAt c A (0, x ()) := by
  simp [typeDGraphAntiInclusion]

/-- Projection reads the fixed coordinates of a vector. -/
@[simp]
theorem typeDGraphProjection_mulVec (v : I ⊕ I → A) :
    typeDGraphProjection c A *ᵥ v = ((typeDGraphSplitAt c A).symm v).1 := by
  simp [typeDGraphProjection]

/-- Anti-projection reads the anti-fixed coordinate of a vector. -/
@[simp]
theorem typeDGraphAntiProjection_mulVec (v : I ⊕ I → A) :
    typeDGraphAntiProjection c A *ᵥ v = fun _ => ((typeDGraphSplitAt c A).symm v).2 := by
  ext u
  simp [typeDGraphAntiProjection]

/-- The included odd coordinates are fixed by the graph permutation. -/
@[simp]
theorem typeDGraphMatrix_mul_inclusion :
    typeDGraphMatrix c A * typeDGraphInclusion c A = typeDGraphInclusion c A := by
  refine Matrix.ext_iff_mulVec.mpr fun x => funext fun s => ?_
  rw [← Matrix.mulVec_mulVec, typeDGraphMatrix_mulVec, typeDGraphInclusion_mulVec]
  simpa using congrFun (typeDGraphSplitAt_graphIndex c A (x, 0)) s

/-- The graph permutation negates the distinguished difference line. -/
@[simp]
theorem typeDGraphMatrix_mul_antiInclusion :
    typeDGraphMatrix c A * typeDGraphAntiInclusion c A = -typeDGraphAntiInclusion c A := by
  refine Matrix.ext_iff_mulVec.mpr fun x => funext fun s => ?_
  rw [← Matrix.mulVec_mulVec, typeDGraphMatrix_mulVec, Matrix.neg_mulVec,
    typeDGraphAntiInclusion_mulVec, ← map_neg]
  simpa using congrFun (typeDGraphSplitAt_graphIndex c A (0, x ())) s

/-- Projection is a left inverse to inclusion. -/
@[simp]
theorem typeDGraphProjection_mul_inclusion :
    typeDGraphProjection c A * typeDGraphInclusion c A = 1 := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← Matrix.mulVec_mulVec, typeDGraphInclusion_mulVec, typeDGraphProjection_mulVec,
    LinearEquiv.symm_apply_apply, Matrix.one_mulVec]

/-- Projection kills the anti-invariant line. -/
@[simp]
theorem typeDGraphProjection_mul_antiInclusion :
    typeDGraphProjection c A * typeDGraphAntiInclusion c A = 0 := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← Matrix.mulVec_mulVec, typeDGraphAntiInclusion_mulVec, typeDGraphProjection_mulVec,
    LinearEquiv.symm_apply_apply, Matrix.zero_mulVec]

/-- The anti-invariant projection kills the included odd coordinates. -/
@[simp]
theorem typeDGraphAntiProjection_mul_inclusion :
    typeDGraphAntiProjection c A * typeDGraphInclusion c A = 0 := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← Matrix.mulVec_mulVec, typeDGraphInclusion_mulVec, typeDGraphAntiProjection_mulVec,
    LinearEquiv.symm_apply_apply, Matrix.zero_mulVec]
  rfl

/-- The anti-invariant coefficient recovers its original scalar. -/
@[simp]
theorem typeDGraphAntiProjection_mul_antiInclusion :
    typeDGraphAntiProjection c A * typeDGraphAntiInclusion c A = 1 := by
  refine Matrix.ext_iff_mulVec.mpr fun x => ?_
  rw [← Matrix.mulVec_mulVec, typeDGraphAntiInclusion_mulVec, typeDGraphAntiProjection_mulVec,
    LinearEquiv.symm_apply_apply, Matrix.one_mulVec]

/-- The invariant coordinates and anti-invariant line reconstruct every vector. -/
theorem typeDGraphInclusion_mul_projection_add :
    typeDGraphInclusion c A * typeDGraphProjection c A +
      typeDGraphAntiInclusion c A * typeDGraphAntiProjection c A = 1 := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    typeDGraphProjection_mulVec, typeDGraphInclusion_mulVec, typeDGraphAntiProjection_mulVec,
    typeDGraphAntiInclusion_mulVec, ← map_add, Prod.mk_add_mk, add_zero, zero_add,
    Prod.mk.eta, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]

/-- A matrix with rows indexed by `I ⊕ I` is the sum of its parts through the invariant
coordinates and through the anti-invariant line. -/
theorem typeDGraphInclusion_mul_projection_mul_add {n : Type*} (M : Matrix (I ⊕ I) n A) :
    typeDGraphInclusion c A * (typeDGraphProjection c A * M) +
      typeDGraphAntiInclusion c A * (typeDGraphAntiProjection c A * M) = M := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul,
    typeDGraphInclusion_mul_projection_add, Matrix.one_mul]

private theorem typeDGraphMatrix_eq_inclusion_mul_projection_sub :
    typeDGraphMatrix c A = typeDGraphInclusion c A * typeDGraphProjection c A -
      typeDGraphAntiInclusion c A * typeDGraphAntiProjection c A := by
  calc
    _ = typeDGraphMatrix c A * (typeDGraphInclusion c A * typeDGraphProjection c A +
        typeDGraphAntiInclusion c A * typeDGraphAntiProjection c A) := by
      rw [typeDGraphInclusion_mul_projection_add, Matrix.mul_one]
    _ = _ := by
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, typeDGraphMatrix_mul_inclusion,
        typeDGraphMatrix_mul_antiInclusion, Matrix.neg_mul, sub_eq_add_neg]

/-- Averaging projection is unchanged by the graph permutation. -/
@[simp]
theorem typeDGraphProjection_mul_graphMatrix :
    typeDGraphProjection c A * typeDGraphMatrix c A = typeDGraphProjection c A := by
  rw [typeDGraphMatrix_eq_inclusion_mul_projection_sub]
  simp [Matrix.mul_sub, ← Matrix.mul_assoc]

/-- The difference projection changes sign under the graph permutation. -/
@[simp]
theorem typeDGraphAntiProjection_mul_graphMatrix :
    typeDGraphAntiProjection c A * typeDGraphMatrix c A = -typeDGraphAntiProjection c A := by
  rw [typeDGraphMatrix_eq_inclusion_mul_projection_sub]
  simp [Matrix.mul_sub, ← Matrix.mul_assoc]

/-- Inclusion after projection is the averaging projector of the graph involution. -/
theorem typeDGraphInclusion_mul_projection :
    typeDGraphInclusion c A * typeDGraphProjection c A =
      ⅟(2 : A) • (1 + typeDGraphMatrix c A) := by
  have hsum : 1 + typeDGraphMatrix c A =
      (2 : A) • (typeDGraphInclusion c A * typeDGraphProjection c A) := by
    rw [← typeDGraphInclusion_mul_projection_add c A,
      typeDGraphMatrix_eq_inclusion_mul_projection_sub, two_smul A]
    abel
  rw [hsum, smul_smul, invOf_mul_self, one_smul]

/-- The complementary projector extracts the anti-invariant line. -/
theorem typeDGraphAntiInclusion_mul_antiProjection :
    typeDGraphAntiInclusion c A * typeDGraphAntiProjection c A =
      ⅟(2 : A) • (1 - typeDGraphMatrix c A) := by
  have hdiff : 1 - typeDGraphMatrix c A =
      (2 : A) • (typeDGraphAntiInclusion c A * typeDGraphAntiProjection c A) := by
    rw [← typeDGraphInclusion_mul_projection_add c A,
      typeDGraphMatrix_eq_inclusion_mul_projection_sub, two_smul A]
    abel
  rw [hdiff, smul_smul, invOf_mul_self, one_smul]

/-- The even orthogonal form is the orthogonal sum of the odd orthogonal form on the invariant
coordinates and the form of norm `-2` on the anti-invariant line. -/
theorem typeDGraphProjection_gram_add_antiProjection_gram :
    (typeDGraphProjection c A)ᵀ * JB {i : I // i ≠ c} A * typeDGraphProjection c A +
      (typeDGraphAntiProjection c A)ᵀ * ((-2 : A) • (1 : Matrix Unit Unit A)) *
        typeDGraphAntiProjection c A = JD I A := by
  apply Matrix.toBilin'.injective
  rw [map_add, ← Matrix.toBilin'_comp, ← Matrix.toBilin'_comp]
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨p, rfl⟩ := (typeDGraphSplitAt c A).surjective v
  obtain ⟨q, rfl⟩ := (typeDGraphSplitAt c A).surjective w
  simp [Matrix.toBilin'_apply' (1 : Matrix Unit Unit A), dotProduct, sub_eq_add_neg, mul_assoc,
    mul_left_comm]

/-- Inclusion and projection intertwine the native even and odd orthogonal forms. -/
theorem typeDGraphInclusion_form_transport :
    JD I A * typeDGraphInclusion c A =
      (typeDGraphProjection c A)ᵀ * JB {i : I // i ≠ c} A := by
  rw [← typeDGraphProjection_gram_add_antiProjection_gram c A]
  simp only [Matrix.add_mul, Matrix.mul_assoc, typeDGraphProjection_mul_inclusion,
    typeDGraphAntiProjection_mul_inclusion, Matrix.mul_one, Matrix.mul_zero, add_zero]

/-- Anti-inclusion and anti-projection intertwine the native even orthogonal form and the form
of norm `-2` on the anti-invariant line. -/
theorem typeDGraphAntiInclusion_form_transport :
    JD I A * typeDGraphAntiInclusion c A =
      (typeDGraphAntiProjection c A)ᵀ * ((-2 : A) • (1 : Matrix Unit Unit A)) := by
  rw [← typeDGraphProjection_gram_add_antiProjection_gram c A]
  simp only [Matrix.add_mul, Matrix.mul_assoc, typeDGraphProjection_mul_antiInclusion,
    typeDGraphAntiProjection_mul_antiInclusion, Matrix.mul_one, Matrix.mul_zero, zero_add]

/-- Inclusion pulls the native even orthogonal form back to the native odd form. -/
@[simp]
theorem typeDGraphInclusion_gram :
    (typeDGraphInclusion c A)ᵀ * JD I A * typeDGraphInclusion c A =
      JB {i : I // i ≠ c} A := by
  rw [Matrix.mul_assoc, typeDGraphInclusion_form_transport, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, typeDGraphProjection_mul_inclusion, Matrix.transpose_one,
    Matrix.one_mul]

/-- The invariant coordinates and the anti-invariant line are orthogonal. -/
@[simp]
theorem typeDGraphInclusion_gram_antiInclusion :
    (typeDGraphInclusion c A)ᵀ * JD I A * typeDGraphAntiInclusion c A = 0 := by
  rw [Matrix.mul_assoc, typeDGraphAntiInclusion_form_transport, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, typeDGraphAntiProjection_mul_inclusion, Matrix.transpose_zero,
    Matrix.zero_mul]

/-- The distinguished difference line has coefficient minus two. -/
@[simp]
theorem typeDGraphAntiInclusion_gram :
    (typeDGraphAntiInclusion c A)ᵀ * JD I A * typeDGraphAntiInclusion c A =
      (-2 : A) • (1 : Matrix Unit Unit A) := by
  rw [Matrix.mul_assoc, typeDGraphAntiInclusion_form_transport, ← Matrix.mul_assoc,
    ← Matrix.transpose_mul, typeDGraphAntiProjection_mul_antiInclusion, Matrix.transpose_one,
    Matrix.one_mul]

end TauCeti
