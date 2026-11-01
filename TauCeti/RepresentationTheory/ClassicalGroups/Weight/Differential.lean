/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.HighestWeight
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.RepresentationTheory.ClassicalGroups.Differential
public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Root.Differential
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
import TauCeti.RingTheory.FiniteType.PointSeparation

/-!
# Differentiating weight vectors of a rational representation of `GL n`

A rational representation `ρ` of `GL n ℂ` differentiates to a representation
`dρ = TauCeti.IsRationalRep.differential` of the matrix Lie algebra `𝔤𝔩ₙ(ℂ)`. This file computes
`dρ` on the two kinds of vectors the group-level highest-weight theory produces, so that a highest
weight vector of `ρ` (`TauCeti.IsRationalRep.exists_highestWeightVector`) is one of `dρ` as well:

* a **weight vector** `w` of weight `l : Fin n → ℤ`, on which every diagonal matrix `diag(t)` acts
  by `∏ᵢ tᵢ ^ lᵢ`, is an eigenvector of every diagonal matrix `diag(a)` in `𝔤𝔩ₙ`, with eigenvalue
  `∑ᵢ aᵢ lᵢ`: the group character `t ↦ ∏ᵢ tᵢ ^ lᵢ` differentiates to the linear functional
  `diag(a) ↦ ∑ᵢ lᵢ aᵢ` on the diagonal Cartan subalgebra;
* a vector fixed by the root subgroup `c ↦ xᵢⱼ(c) = 1 + c Eᵢⱼ` is killed by the root vector
  `Eᵢⱼ`.

## The argument

Both statements restrict the comodule of `ρ` along a one-parameter subgroup of `GLₙ` and
differentiate there, using that the differential commutes with restriction
(`TauCeti.Comodule.differential_corestrict`).

For the root vector the subgroup is the root subgroup `xᵢⱼ : 𝔾ₐ → GLₙ`, whose differential is
`Eᵢⱼ` (`TauCeti.GeneralLinear.tangentMatrix_derivationComp_rootSubgroup`). A vector fixed by
every complex point of `𝔾ₐ` is fixed by its coaction, the coordinate ring of `𝔾ₐ` being reduced
and of finite type over the algebraically closed field `ℂ`
(`TauCeti.Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq`), and a fixed vector
of a comodule is killed by every tangent vector.

For the diagonal the subgroup is the cocharacter `𝔾ₘ → GLₙ`, `t ↦ diag(1, …, t, …, 1)` with `t` in
place `i`, whose differential is `Eᵢᵢ`
(`TauCeti.GeneralLinear.tangentMatrix_derivationComp_weightCocharacter`). Pairing with a linear
functional `φ`, the matrix coefficient of `w` along it is a Laurent polynomial which agrees with
`φ(w) Tˡⁱ` at every complex point, hence equals it, and the tangent vector `d/dT` at `T = 1` takes
it to `lᵢ φ(w)`.

## Main results

* `TauCeti.IsRationalRep.differential_single_self_apply_of_mem_weightSpace`: on a vector of weight
  `l`, the matrix unit `Eᵢᵢ` acts by the scalar `lᵢ`.
* `TauCeti.IsRationalRep.differential_diagonal_apply_of_mem_weightSpace`: on a vector of weight
  `l`, the diagonal matrix `diag(a)` acts by the scalar `∑ᵢ aᵢ lᵢ`.
* `TauCeti.IsRationalRep.differential_single_apply_eq_zero`: a vector fixed by the root subgroup
  `xᵢⱼ` is killed by `Eᵢⱼ`.
* `TauCeti.IsRationalRep.isGlHighestWeightVector_differential`: a highest weight vector for the
  transvections is a highest weight vector for `𝔤𝔩ₙ` through the differential.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, Chapter 7.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open WithConv LaurentPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace IsRationalRep

open GeneralLinear

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

/-- **A vector fixed by a root subgroup is killed by its root vector**: if every transvection
`xᵢⱼ(c) = 1 + c Eᵢⱼ` fixes `w`, then the differential of `ρ` sends `w` to zero along `Eᵢⱼ`. -/
theorem differential_single_apply_eq_zero (hρ : IsRationalRep ρ) {i j : Fin n} (hij : i ≠ j)
    {w : W} (hw : ∀ c : ℂ, ρ (transvectionUnit hij c) w = w) :
    hρ.differential (Matrix.single i j 1) w = 0 := by
  let φ := (rootSubgroupCoordinateMap (R := ℂ) (N := n) hij).hom
  let d := (AdditiveGroup.gaTangentLinearEquiv (R := ℂ) (B := ℂ)).symm 1
  have hX : (tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm (Matrix.single i j 1) =
      derivationComp φ d := by
    rw [LieEquiv.symm_apply_eq, tangentLieEquivMatrix_apply,
      tangentMatrix_derivationComp_rootSubgroup, LinearEquiv.apply_symm_apply]
  let _ := hρ.comodule
  rw [differential_apply, hX, ← Comodule.differential_corestrict]
  let _ : Comodule ℂ (AdditiveGroup.coordinateHopfAlgebra ℂ) W :=
    Comodule.Corestrict φ.toCoalgHom
  refine Comodule.differential_eq_zero_of_coact_eq_tmul_one
    ((Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq w).mpr fun g ↦ ?_) d
  rw [Comodule.basePointsRepresentation_corestrict, mapDomain_rootSubgroupCoordinateMap,
    hρ.basePointsRepresentation_comodule_eq_pointsMulEquiv, pointsMulEquiv_rootSubgroupPoints]
  exact hw _

/-- **A weight vector is an eigenvector of each diagonal matrix unit**: if every diagonal matrix
`diag(t)` acts on `w` by `∏ₖ tₖ ^ lₖ`, then `Eᵢᵢ` acts on `w` through the differential of `ρ` by
the scalar `lᵢ`. -/
theorem differential_single_self_apply_of_mem_weightSpace (hρ : IsRationalRep ρ)
    {l : Fin n → ℤ} {w : W} (hw : w ∈ weightSpace ρ l) (i : Fin n) :
    hρ.differential (Matrix.single i i 1) w = (l i : ℂ) • w := by
  classical
  let c := weightCocharacter (R := ℂ) (N := n) (Pi.single i 1)
  let d := (MultiplicativeGroup.tangentLinearEquiv (R := ℂ) (B := ℂ)).symm 1
  have hd (m : ℤ) :
      Bialgebra.CounitAlgebra.algEquivSelf ℂ (LaurentPolynomial ℂ) ℂ (d (T m)) = m := by
    rw [MultiplicativeGroup.derivation_T_zsmul, map_zsmul,
      ← MultiplicativeGroup.tangentLinearEquiv_apply, LinearEquiv.apply_symm_apply, zsmul_one]
  have hX : (tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm (Matrix.single i i 1) =
      derivationComp c d := by
    rw [LieEquiv.symm_apply_eq, tangentLieEquivMatrix_apply,
      tangentMatrix_derivationComp_weightCocharacter, LinearEquiv.apply_symm_apply,
      ← Matrix.diagonal_single]
    congr 1
    funext a
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  have := hρ.finite
  let _ := hρ.comodule
  rw [differential_apply, hX, ← Comodule.differential_corestrict]
  let _ : Comodule ℂ (LaurentPolynomial ℂ) W := Comodule.Corestrict c.toCoalgHom
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, sub_eq_zero, ← Derivation.apply_matrixCoefficient]
  -- The matrix coefficient of `w` along the cocharacter is the Laurent monomial `φ(w) Tˡⁱ`.
  have hcoeff : Comodule.matrixCoefficient (R := ℂ) (C := LaurentPolynomial ℂ) φ w =
      φ w • T (l i) := by
    refine eq_of_forall_algHom_apply_eq (k := ℂ) (K := ℂ) fun p ↦ ?_
    have hp := Comodule.apply_matrixCoefficient (H := LaurentPolynomial ℂ) (toConv p) φ w
    rw [ofConv_toConv] at hp
    rw [hp, Comodule.basePointsRepresentation_corestrict, mapDomain_weightCocharacter,
      hρ.basePointsRepresentation_comodule_eq_pointsMulEquiv,
      pointsMulEquiv_weightCocharacterPoints, (mem_weightSpace_iff ρ l w).mp hw]
    have hu :
        p = laurentEval (MultiplicativeGroup.pointsMulEquiv (R := ℂ) (A := ℂ) (toConv p)) := by
      simp [laurentEval_laurentEvalEquiv_symm]
    set u := MultiplicativeGroup.pointsMulEquiv (R := ℂ) (A := ℂ) (toConv p)
    have hchar : weightChar ℂ l (weightDiagonalUnits (Pi.single i 1) u) = u ^ l i := by
      rw [weightChar_apply, torusCharacter_def, Finset.prod_eq_single i (fun b _ hb ↦ by simp [hb])
        (by simp)]
      simp
    rw [hchar, map_smul, map_smul, hu, laurentEval_T, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [hcoeff, Derivation.map_smul, map_smul, hd, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- **A weight differentiates to a linear functional on the diagonal Cartan subalgebra**: if
every diagonal matrix `diag(t)` acts on `w` by `∏ₖ tₖ ^ lₖ`, then `diag(a)` acts on `w` through the
differential of `ρ` by the scalar `∑ₖ aₖ lₖ`. -/
theorem differential_diagonal_apply_of_mem_weightSpace (hρ : IsRationalRep ρ)
    {l : Fin n → ℤ} {w : W} (hw : w ∈ weightSpace ρ l) (a : Fin n → ℂ) :
    hρ.differential (Matrix.diagonal a) w = (∑ k, a k * l k) • w := by
  have ha : Matrix.diagonal a = ∑ k, a k • Matrix.single k k (1 : ℂ) := by
    rw [← Matrix.sum_single_eq_diagonal]
    simp [Matrix.smul_single]
  simp only [ha, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    hρ.differential_single_self_apply_of_mem_weightSpace hw, smul_smul, Finset.sum_smul]

/-- **A highest weight vector differentiates to a highest weight vector**: a nonzero vector of
weight `l` fixed by every transvection `xᵢⱼ(c)` with `i < j` is a highest weight vector of weight
`l` for `𝔤𝔩ₙ(ℂ)` through the differential of `ρ`. -/
theorem isGlHighestWeightVector_differential (hρ : IsRationalRep ρ) {l : Fin n → ℤ}
    {w : W} (hw0 : w ≠ 0) (hwl : w ∈ weightSpace ρ l)
    (hw : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), ρ (transvectionUnit hij.ne c) w = w) :
    letI := LieRingModule.compLieHom W hρ.differential
    IsGlHighestWeightVector (fun k ↦ (l k : ℂ)) w := by
  let _ := LieRingModule.compLieHom W hρ.differential
  refine isGlHighestWeightVector_iff.mpr ⟨hw0, fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · rw [LieRingModule.compLieHom_apply, Module.End.lie_apply,
      hρ.differential_single_self_apply_of_mem_weightSpace hwl]
  · rw [LieRingModule.compLieHom_apply, Module.End.lie_apply,
      hρ.differential_single_apply_eq_zero hij.ne (hw i j hij)]

end IsRationalRep

end TauCeti
