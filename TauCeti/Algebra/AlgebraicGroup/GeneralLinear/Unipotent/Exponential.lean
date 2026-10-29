/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Unipotent.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.OneParameter
import TauCeti.Algebra.AlgebraicGroup.Tangent.Antipode
import TauCeti.Algebra.AlgebraicGroup.Tangent.GroupLike
import TauCeti.RingTheory.Derivation.LocallyNilpotent

/-!
# Invariant-vector-field exponentials on `GLₙ` are matrix exponentials

A tangent vector `d` to `GLₙ` at the identity has a matrix `X`, its values on the generic entries.
Its left-invariant vector field `D` acts on the generic matrix `x` by right multiplication,
`D x = x X`, so `Dᵐ x = x Xᵐ`, and on the determinant by `D det = tr(X) det`. When `X` is
nilpotent, so is `tr X`, and since the generic entries and the inverse determinant generate the
coordinate algebra, `D` is locally nilpotent. Over a rational base its Taylor exponential then
defines the abstract polynomial one-parameter subgroup `t ↦ exp(t d)` of
`TauCeti.Bialgebra.expPointPolynomial`, and this file identifies it with the matrix curve
`t ↦ exp(tX)` of `TauCeti.GeneralLinear.nilpotentOneParameterCoordinateMap`.

The abstract curve lies in every closed subgroup whose Lie algebra contains `d`, because `D`
preserves the defining Hopf ideal. So for a closed subgroup `H ⊆ GLₙ` over a rational ring and a
nilpotent matrix `X ∈ Lie H`, the matrices `exp(tX)` are points of `H` over every commutative
value algebra, with no smoothness, connectedness or reducedness assumption on `H`. Over a rational
domain this is the converse of
`TauCeti.GeneralLinear.mem_map_lieSubalgebra_of_nilpotentExpUnit_mem`, and together with
`TauCeti.GeneralLinear.log_mem_map_lieSubalgebra` it shows that the finite exponential and
logarithm are inverse bijections between the nilpotent elements of `Lie H` and the
unipotent points of `H`.

## Main declarations

* `TauCeti.GeneralLinear.iterate_leftInvariantDerivation_genericMatrix`: `Dᵐ x = x Xᵐ` on the
  generic entries.
* `TauCeti.GeneralLinear.exists_iterate_leftInvariantDerivation_eq_zero`: the invariant vector
  field of a nilpotent tangent matrix is locally nilpotent.
* `TauCeti.GeneralLinear.expPointPolynomial_eq_nilpotentOneParameterCoordinateMap`: the abstract
  exponential curve is the matrix curve `t ↦ exp(tX)`.
* `TauCeti.GeneralLinear.pointsMulEquiv_expPointAt`: its value at `t` has matrix `exp(tX)`.
* `TauCeti.GeneralLinear.expSMulHom_mem_hopfIdealPointsSubgroup`: for nilpotent `X ∈ Lie H`, the
  curve `exp(tX)` lies in `H` over every rational value algebra.
* `TauCeti.GeneralLinear.nilpotentExpUnit_mem_hopfIdealPointsSubgroup_iff`: over a rational
  domain, `exp X ∈ H` exactly when `X ∈ Lie H`, for nilpotent `X`.
* `TauCeti.GeneralLinear.expEquivHopfIdealPoints`: over a rational domain, exponential and
  logarithm identify the nilpotent elements of `Lie H` with the unipotent points of `H`.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §15.3.
* J. S. Milne, *Algebraic Groups* (2017), §14.c.
* G. Freudenburg, *Algebraic Theory of Locally Nilpotent Derivations*, Encyclopaedia of
  Mathematical Sciences 136, Springer (2006), Chapter 1.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R] (n : ℕ)

section InvariantDerivation

variable (d : Derivation R (coordinateHopfAlgebra R n)
  (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R n) R))

/-- **The invariant vector field of a tangent vector to `GLₙ` is right multiplication by its
matrix** on the generic matrix: `D x_ij = ∑ₖ x_ik X_kj`. -/
theorem leftInvariantDerivation_genericMatrix (i j : Fin n) :
    Bialgebra.leftInvariantDerivation d (genericMatrix R n i j) =
      ∑ k, tangentMatrix n d k j • genericMatrix R n i k := by
  simp only [genericMatrix_apply, Bialgebra.leftInvariantDerivation_apply,
    coordinateHopfAlgebra_comul_X, map_sum, LinearMap.tensorComponent_tmul, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe, tangentMatrix_apply]

/-- Iterating the invariant vector field of a tangent vector to `GLₙ` multiplies the generic
matrix on the right by the powers of its matrix: `Dᵐ x_ij = ∑ₖ x_ik (Xᵐ)_kj`. -/
theorem iterate_leftInvariantDerivation_genericMatrix (m : ℕ) (i j : Fin n) :
    (Bialgebra.leftInvariantDerivation d)^[m] (genericMatrix R n i j) =
      ∑ k, (tangentMatrix n d ^ m) k j • genericMatrix R n i k := by
  induction m generalizing j with
  | zero => simp [Matrix.one_apply]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    simp only [Derivation.map_smul, leftInvariantDerivation_genericMatrix, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, pow_succ', Matrix.mul_apply]
    simp only [mul_comm]

/-- The counit of the iterated invariant vector field on a generic entry is the corresponding
entry of the power of the tangent matrix. -/
theorem counit_iterate_leftInvariantDerivation_genericMatrix (m : ℕ) (i j : Fin n) :
    Coalgebra.counit (R := R)
        ((Bialgebra.leftInvariantDerivation d)^[m] (genericMatrix R n i j)) =
      (tangentMatrix n d ^ m) i j := by
  rw [iterate_leftInvariantDerivation_genericMatrix, map_sum]
  simp [coordinateHopfAlgebra_counit_X]

/-- The antipode of a generic entry of `GLₙ`, an entry of the inverse generic matrix, is the
inverse determinant `S(det)` times the corresponding entry of the adjugate. -/
private theorem antipode_genericMatrix (i j : Fin n) :
    HopfAlgebra.antipode R (genericMatrix R n i j) =
      HopfAlgebra.antipode R (determinantGroupLike R n : coordinateHopfAlgebra R n) *
        (genericMatrix R n).adjugate i j := by
  have hdet : (genericMatrix R n).det = (determinantGroupLike R n : coordinateHopfAlgebra R n) := by
    have hmap : genericMatrix R n =
        (coordinateHopfAlgebraAlgEquiv R n).mapMatrix (localizedGenericMatrix R n) := by
      ext i j
      simp [localizedGenericMatrix_apply]
    rw [hmap, ← AlgEquiv.map_det, determinantGroupLike_val]
  have hinv : Ring.inverse (genericMatrix R n).det =
      HopfAlgebra.antipode R (determinantGroupLike R n : coordinateHopfAlgebra R n) := by
    rw [hdet]
    exact Ring.inverse_unit (GroupLike.toUnits R (determinantGroupLike R n))
  rw [genericMatrix_apply, coordinateHopfAlgebra_antipode_X, ← genericMatrix_inv_apply,
    Matrix.inv_def, hinv, Matrix.smul_apply, smul_eq_mul]

/-- The generic entries and the inverse determinant generate the coordinate algebra of `GLₙ`. -/
private theorem adjoin_genericMatrix_union_antipode_determinant :
    Algebra.adjoin R (Set.range (fun ij : Fin n × Fin n => genericMatrix R n ij.1 ij.2) ∪
        {HopfAlgebra.antipode R (determinantGroupLike R n : coordinateHopfAlgebra R n)}) = ⊤ := by
  set S := Algebra.adjoin R (Set.range (fun ij : Fin n × Fin n => genericMatrix R n ij.1 ij.2) ∪
    {HopfAlgebra.antipode R (determinantGroupLike R n : coordinateHopfAlgebra R n)})
  have hentry (i j : Fin n) : genericMatrix R n i j ∈ S :=
    Algebra.subset_adjoin (Or.inl ⟨(i, j), rfl⟩)
  -- The adjugate is a polynomial in the entries, so its entries lie in `S`.
  have hadj (i j : Fin n) : (genericMatrix R n).adjugate i j ∈ S := by
    let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨genericMatrix R n i j, hentry i j⟩
    have hM : (S.val : S →+* coordinateHopfAlgebra R n).mapMatrix M = genericMatrix R n := rfl
    rw [← hM, ← RingHom.map_adjugate]
    exact ((M.adjugate) i j).property
  rw [eq_top_iff, ← adjoin_coordinateHopfAlgebra_X_union_antipode_X R n, Algebra.adjoin_le_iff]
  rintro _ (⟨⟨i, j⟩, rfl⟩ | ⟨⟨i, j⟩, rfl⟩) <;> beta_reduce <;>
    rw [SetLike.mem_coe, ← genericMatrix_apply]
  · exact hentry i j
  · rw [antipode_genericMatrix]
    exact mul_mem (Algebra.subset_adjoin (Or.inr rfl)) (hadj i j)

/-- **The invariant vector field of a nilpotent tangent matrix is locally nilpotent.** It kills
the generic entries since `Dᵐ x = x Xᵐ`, and the inverse determinant since that is group-like with
nilpotent differential `-tr X`. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero (hX : IsNilpotent (tangentMatrix n d))
    (h : coordinateHopfAlgebra R n) :
    ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0 := by
  refine (Bialgebra.leftInvariantDerivation d).exists_iterate_eq_zero_of_adjoin_eq_top
    (adjoin_genericMatrix_union_antipode_determinant n) ?_ h
  rintro _ (⟨⟨i, j⟩, rfl⟩ | rfl)
  · obtain ⟨m, hm⟩ := hX
    refine ⟨m, ?_⟩
    rw [iterate_leftInvariantDerivation_genericMatrix, hm]
    simp
  · refine Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_isGroupLikeElem d
      (determinantGroupLike R n).isGroupLikeElem_val.antipode ?_
    rw [Derivation.apply_antipode, map_neg]
    refine IsNilpotent.neg ?_
    simpa only [trace_tangentMatrix, Bialgebra.CounitAlgebra.algEquivSelf_apply] using
      Matrix.isNilpotent_trace_of_isNilpotent hX

variable [Algebra ℚ R] [Algebra ℚ (coordinateHopfAlgebra R n)]

/-- **The exponential curve of a nilpotent tangent vector to `GLₙ` is the matrix curve
`t ↦ exp(tX)`.** The coefficients of the abstract curve are `ε(Dᵐ x) / m! = Xᵐ / m!`. -/
theorem expPointPolynomial_eq_nilpotentOneParameterCoordinateMap
    (hd : ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0)
    (hX : IsNilpotent (tangentMatrix n d)) :
    Bialgebra.expPointPolynomial d hd = nilpotentOneParameterCoordinateMap n hX := by
  apply coordinateHopfAlgebra_algHom_ext
  intro i j
  ext m
  rw [Bialgebra.coeff_expPointPolynomial, nilpotentOneParameterCoordinateMap_apply_X,
    Matrix.coeff_exp_X_smul_C_mapMatrix hX, ← genericMatrix_apply, map_rat_smul,
    counit_iterate_leftInvariantDerivation_genericMatrix, Matrix.smul_apply]

/-- The value at `t` of the exponential curve of a nilpotent tangent vector to `GLₙ` is the
matrix exponential `exp(tX)`, over every rational value algebra. -/
theorem pointsMulEquiv_expPointAt
    (hd : ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0)
    (hX : IsNilpotent (tangentMatrix n d))
    {A : Type v} [CommRing A] [Algebra R A] [Algebra ℚ A] (t : A) :
    pointsMulEquiv n (Bialgebra.expPointAt d hd t) =
      expSMulHom A (hX.map (algebraMap R A).mapMatrix) (Multiplicative.ofAdd t) := by
  rw [← Matrix.GeneralLinearGroup.map_aeval_expSMulHom hX t]
  ext i j
  rw [pointsMulEquiv_apply, pointToGeneralLinear_apply, Bialgebra.expPointAt_apply,
    expPointPolynomial_eq_nilpotentOneParameterCoordinateMap n d hd hX,
    nilpotentOneParameterCoordinateMap_apply_X]
  simp

/-- The exponential of a nilpotent tangent vector to `GLₙ` is the matrix exponential of its
tangent matrix. -/
theorem pointsMulEquiv_expPoint
    (hd : ∀ h, ∃ m, (Bialgebra.leftInvariantDerivation d)^[m] h = 0)
    (hX : IsNilpotent (tangentMatrix n d)) :
    pointsMulEquiv n (toConv (Bialgebra.expPoint d hd)) = nilpotentExpUnit hX := by
  rw [← Bialgebra.expPointAt_one, pointsMulEquiv_expPointAt n d hd hX]
  ext i j
  simp

end InvariantDerivation

section ClosedSubgroup

variable [Algebra ℚ R] {X : Matrix (Fin n) (Fin n) R}

/-- **For a nilpotent matrix `X` in the Lie algebra of a closed subgroup `H` of `GLₙ`, the whole
curve `t ↦ exp(tX)` lies in `H`**, over every rational value algebra, including nonreduced ones.
The subgroup is cut out by the Hopf ideal `I`, and its Lie algebra is read inside the matrix Lie
algebra through `tangentLieEquivMatrix`. No smoothness, connectedness or reducedness assumption
is needed. -/
theorem expSMulHom_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (hX : IsNilpotent X)
    (hXI : X ∈ (I.lieSubalgebra (B := R)).map (tangentLieEquivMatrix (R := R) (B := R) n).toLieHom)
    {A : Type v} [CommRing A] [Algebra R A] [Algebra ℚ A] (t : A) :
    expSMulHom A (hX.map (algebraMap R A).mapMatrix) (Multiplicative.ofAdd t) ∈
      hopfIdealPointsSubgroup n I A := by
  -- The rational structure of the base induces one on the coordinate algebra.
  let : Algebra ℚ (coordinateHopfAlgebra R n) :=
    ((algebraMap R (coordinateHopfAlgebra R n)).comp (algebraMap ℚ R)).toAlgebra
  obtain ⟨d, hdI, hdX⟩ := (LieSubalgebra.mem_map _ _ _).mp hXI
  rw [LieEquiv.coe_toLieHom, tangentLieEquivMatrix_apply] at hdX
  subst hdX
  have hd := exists_iterate_leftInvariantDerivation_eq_zero n d hX
  rw [← pointsMulEquiv_expPointAt n d hd hX t]
  exact pointsMulEquiv_mem_hopfIdealPointsSubgroup n I A _
    (I.expPointAt_mem_quotientPointsSubgroup hdI hd t)

/-- The exponential of a nilpotent matrix in the Lie algebra of a closed subgroup of `GLₙ` is a
point of that subgroup. -/
theorem nilpotentExpUnit_mem_hopfIdealPointsSubgroup
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (hX : IsNilpotent X)
    (hXI : X ∈ (I.lieSubalgebra (B := R)).map
      (tangentLieEquivMatrix (R := R) (B := R) n).toLieHom) :
    nilpotentExpUnit hX ∈ hopfIdealPointsSubgroup n I R := by
  convert expSMulHom_mem_hopfIdealPointsSubgroup n I hX hXI (1 : R) using 1
  ext i j
  simp

/-- **Over a rational domain, a nilpotent matrix lies in the Lie algebra of a closed subgroup of
`GLₙ` exactly when its exponential is a point of the subgroup.** -/
theorem nilpotentExpUnit_mem_hopfIdealPointsSubgroup_iff [IsDomain R]
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) (hX : IsNilpotent X) :
    nilpotentExpUnit hX ∈ hopfIdealPointsSubgroup n I R ↔
      X ∈ (I.lieSubalgebra (B := R)).map (tangentLieEquivMatrix (R := R) (B := R) n).toLieHom :=
  ⟨mem_map_lieSubalgebra_of_nilpotentExpUnit_mem n I hX,
    nilpotentExpUnit_mem_hopfIdealPointsSubgroup n I hX⟩

/-- **Over a rational domain, the finite exponential and logarithm identify the nilpotent
elements of the Lie algebra of a closed subgroup of `GLₙ` with its unipotent points.** This is an
equivalence of sets, not of groups. -/
noncomputable def expEquivHopfIdealPoints [IsDomain R]
    (I : HopfIdeal R (coordinateHopfAlgebra R n)) :
    {X : Matrix (Fin n) (Fin n) R // X ∈ (I.lieSubalgebra (B := R)).map
        (tangentLieEquivMatrix (R := R) (B := R) n).toLieHom ∧ IsNilpotent X} ≃
      {g : Matrix.GeneralLinearGroup (Fin n) R //
        g ∈ hopfIdealPointsSubgroup n I R ∧ IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1)} where
  toFun X := ⟨nilpotentExpUnit X.2.2,
    nilpotentExpUnit_mem_hopfIdealPointsSubgroup n I X.2.2 X.2.1,
    by simpa using IsNilpotent.isNilpotent_exp_sub_one X.2.2⟩
  invFun g := ⟨IsNilpotent.log ((g.1 : Matrix.GeneralLinearGroup (Fin n) R) :
      Matrix (Fin n) (Fin n) R),
    log_mem_map_lieSubalgebra n I g.1 g.2.2 g.2.1, IsNilpotent.isNilpotent_log g.2.2⟩
  left_inv X := Subtype.ext (by simpa using IsNilpotent.log_exp X.2.2)
  right_inv g := Subtype.ext (Units.nilpotentExpUnit_log g.1 g.2.2)

/-- The forward map of `expEquivHopfIdealPoints` is the finite exponential. -/
@[simp]
theorem coe_expEquivHopfIdealPoints_apply [IsDomain R]
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (X : {X : Matrix (Fin n) (Fin n) R // X ∈ (I.lieSubalgebra (B := R)).map
        (tangentLieEquivMatrix (R := R) (B := R) n).toLieHom ∧ IsNilpotent X}) :
    ((expEquivHopfIdealPoints n I X : Matrix.GeneralLinearGroup (Fin n) R) :
        Matrix (Fin n) (Fin n) R) = IsNilpotent.exp (X : Matrix (Fin n) (Fin n) R) := by
  simp only [expEquivHopfIdealPoints, Equiv.coe_fn_mk, coe_nilpotentExpUnit]

/-- The inverse map of `expEquivHopfIdealPoints` is the finite logarithm. -/
@[simp]
theorem coe_expEquivHopfIdealPoints_symm_apply [IsDomain R]
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (g : {g : Matrix.GeneralLinearGroup (Fin n) R //
        g ∈ hopfIdealPointsSubgroup n I R ∧ IsNilpotent ((g : Matrix (Fin n) (Fin n) R) - 1)}) :
    ((expEquivHopfIdealPoints n I).symm g : Matrix (Fin n) (Fin n) R) =
      IsNilpotent.log ((g : Matrix.GeneralLinearGroup (Fin n) R) : Matrix (Fin n) (Fin n) R) :=
  (rfl)

end ClosedSubgroup

end TauCeti.GeneralLinear
