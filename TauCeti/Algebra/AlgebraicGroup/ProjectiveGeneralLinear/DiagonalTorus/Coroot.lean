/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.RootSubgroup.Torus
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.RootDatum.Basic

/-!
# Coroot morphisms of the projective general linear group

The coroot for the elementary root indexed by `(i,j)` is conjugation by the
matrix with diagonal entries `u` at `i`, `u⁻¹` at `j`, and one elsewhere.
In the normalized projective torus its exponents are obtained by subtracting
the last diagonal exponent. In particular the coroot of `PGL₂` is the square
map into its diagonal torus, as required for the adjoint root datum.

We construct these cocharacters as group-scheme morphisms and as natural maps
on convolution points. The point formula computes their conjugation action on
every elementary root subgroup, with the integral type-A Cartan exponent.
The chosen root is rescaled by `u²`. These formulas provide the coroot maps
and their root normalization equations for pinnings over arbitrary base rings.

The construction uses `SplitTorus.coordinateCoroot`, `SplitTorus.cocharEquiv`,
`SplitTorus.cocharacterGroupSchemeMap`, and the projective diagonal-torus and
root-subgroup maps. The coordinate convention is the one used by
`GeneralLinear.diagonalCorootCocharacter`, followed by normalization of the last entry.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u v

noncomputable section

variable {r : ℕ}

/-- The cocharacter of the normalized projective diagonal torus associated to
`(i,j)`. Its coordinate exponents are `δₖᵢ - δₖⱼ - δᵣᵢ + δᵣⱼ`. -/
def diagonalCorootCocharacter (i j : Fin (r + 1)) :
    Multiplicative (ULift.{u} (Fin r) →₀ ℤ) →* Multiplicative ℤ :=
  SplitTorus.cocharEquiv.symm fun k ↦
    SplitTorus.coordinateCoroot i j k.down.castSucc - SplitTorus.coordinateCoroot i j (Fin.last r)

/-- A coroot coordinate is the difference between its diagonal exponent and
its last diagonal exponent; this normalization removes scalar matrices. -/
@[simp high]
theorem cocharEquiv_diagonalCorootCocharacter (i j : Fin (r + 1))
    (k : ULift.{u} (Fin r)) :
    SplitTorus.cocharEquiv (diagonalCorootCocharacter.{u} i j) k =
      ((if k.down.castSucc = i then (1 : ℤ) else 0) -
        (if k.down.castSucc = j then (1 : ℤ) else 0)) -
      ((if Fin.last r = i then (1 : ℤ) else 0) - (if Fin.last r = j then (1 : ℤ) else 0)) := by
  rw [diagonalCorootCocharacter, Equiv.apply_symm_apply]
  -- The coordinate model uses classical equality; split to align the presentations.
  simp only [SplitTorus.coordinateCoroot_apply]
  split_ifs <;> rfl

variable (R : Type u) [CommRing R]

/-- The coroot `𝔾ₘ → PGL_{r+1}`, factoring through the normalized diagonal torus. -/
def coroot (i j : Fin (r + 1)) :
    DiagonalizableGroup.multiplicativeGroupScheme R ⟶ groupScheme (r + 1) R :=
  SplitTorus.cocharacterGroupSchemeMap (R := R) (diagonalCorootCocharacter.{u} i j) ≫
    diagonalTorus r R

/-- The coroot factors through the split diagonal torus by its normalized
integral cocharacter. -/
theorem coroot_def (i j : Fin (r + 1)) :
    coroot R i j =
      SplitTorus.cocharacterGroupSchemeMap (R := R) (diagonalCorootCocharacter.{u} i j) ≫
        diagonalTorus r R := (rfl)

variable {R}

/-- On convolution points, the coroot is the diagonal-torus map applied to
the corresponding multiplicative-group cocharacter. -/
def corootPoints (A : CommAlgCat.{v} R) (i j : Fin (r + 1)) :
    WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra (r + 1) R →ₐ[R] A) :=
  (BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom).comp
    (DiagonalizableGroup.cocharPoints (diagonalCorootCocharacter.{u} i j))

/-- The point map of a coroot factors through the point map of the diagonal torus. -/
theorem corootPoints_def (A : CommAlgCat.{v} R) (i j : Fin (r + 1))
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    corootPoints A i j p =
      BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom
        (DiagonalizableGroup.cocharPoints (diagonalCorootCocharacter.{u} i j) p) := (rfl)

private theorem coroot_torus_coordinate (A : CommAlgCat.{v} R) (i j : Fin (r + 1))
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A))
    (k : ULift.{u} (Fin r)) :
    SplitTorus.pointsMulEquiv
        (DiagonalizableGroup.cocharPoints (diagonalCorootCocharacter.{u} i j) p) k =
      DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^
        (SplitTorus.coordinateCoroot i j k.down.castSucc -
          SplitTorus.coordinateCoroot i j (Fin.last r)) := by
  rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv, freeAbelianCharEquiv_apply,
    DiagonalizableGroup.pointsMulEquiv_cocharPoints, ← SplitTorus.cocharEquiv_apply,
    cocharEquiv_diagonalCorootCocharacter]
  simp only [SplitTorus.coordinateCoroot_apply]
  split_ifs <;> rfl

private theorem normalized_coroot_diagonal (A : CommAlgCat.{v} R) (i j k : Fin (r + 1))
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    Fin.lastCases 1 (fun a ↦ SplitTorus.pointsMulEquiv
        (DiagonalizableGroup.cocharPoints (diagonalCorootCocharacter.{u} i j) p) (ULift.up a)) k =
      DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^
        (SplitTorus.coordinateCoroot i j k - SplitTorus.coordinateCoroot i j (Fin.last r)) := by
  refine Fin.lastCases ?_ (fun a ↦ ?_) k
  · simp
  · simp only [Fin.lastCases_castSucc]
    exact coroot_torus_coordinate A i j p (ULift.up a)

/-- The projective coroot is conjugation by the normalized diagonal matrix
whose entries are `u^(δₖᵢ - δₖⱼ - δᵣᵢ + δᵣⱼ)`. -/
theorem pointsMulEquiv_corootPoints (A : CommAlgCat.{v} R) (i j : Fin (r + 1))
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    pointsMulEquiv (r + 1) R A (corootPoints A i j p) =
      Matrix.GeneralLinearGroup.innerAut (diagGL fun k ↦
        DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^
          (((if k = i then (1 : ℤ) else 0) -
              (if k = j then (1 : ℤ) else 0)) -
            ((if Fin.last r = i then (1 : ℤ) else 0) -
              (if Fin.last r = j then (1 : ℤ) else 0)))) := by
  rw [corootPoints_def]
  have h := pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap r R A
    (DiagonalizableGroup.cocharPoints (diagonalCorootCocharacter.{u} i j) p)
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply] at h
  rw [h]
  congr 2
  funext k
  have hk := normalized_coroot_diagonal A i j k p
  simp only [SplitTorus.coordinateCoroot_apply] at hk
  split_ifs at hk ⊢ <;> exact hk

/-- Evaluating an elementary root character on a coroot gives the unit raised
to the type-A Cartan integer `δₖᵢ - δₖⱼ - δₗᵢ + δₗⱼ`. -/
theorem torusCharacter_diagonalCorootCocharacter (A : CommAlgCat.{v} R)
    (i j k l : Fin (r + 1))
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    torusCharacter (SplitTorus.pointsMulEquiv
        (DiagonalizableGroup.cocharPoints (diagonalCorootCocharacter.{u} i j) p))
        (diagonalTorusWeight r (finProdFinEquiv (k, l))) =
      DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^
        (((if k = i then (1 : ℤ) else 0) - (if k = j then (1 : ℤ) else 0)) -
          ((if l = i then (1 : ℤ) else 0) - (if l = j then (1 : ℤ) else 0))) := by
  rw [torusCharacter_diagonalTorusWeight]
  simp only [Equiv.symm_apply_apply, normalized_coroot_diagonal]
  rw [div_eq_mul_inv, ← zpow_sub]
  congr 1
  simp only [SplitTorus.coordinateCoroot_apply]
  omega

/-- Conjugation by a coroot rescales every elementary root subgroup by its
integral Cartan exponent, over arbitrary commutative value algebras. -/
theorem corootPoints_mul_rootSubgroupPoints_mul_inv (A : CommAlgCat.{v} R)
    (i j : Fin (r + 1)) {k l : Fin (r + 1)} (hkl : k ≠ l)
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    corootPoints A i j p * rootSubgroupPoints A hkl c * (corootPoints A i j p)⁻¹ =
      rootSubgroupPoints A hkl
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm
          (Multiplicative.ofAdd
            ((DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^
                (((if k = i then (1 : ℤ) else 0) -
                    (if k = j then (1 : ℤ) else 0)) -
                  ((if l = i then (1 : ℤ) else 0) - (if l = j then (1 : ℤ) else 0))) : Aˣ) •
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c)))) := by
  rw [corootPoints_def A i j p]
  rw [diagonalTorus_mul_rootSubgroupPoints_mul_inv,
    torusCharacter_diagonalCorootCocharacter]

/-- A root evaluated on its own coroot has Cartan exponent two. This remains
valid for the adjoint rank-one group and in characteristic two. -/
@[simp high]
theorem torusCharacter_diagonalCorootCocharacter_self (A : CommAlgCat.{v} R)
    {i j : Fin (r + 1)} (hij : i ≠ j)
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A)) :
    torusCharacter (SplitTorus.pointsMulEquiv
        (DiagonalizableGroup.cocharPoints (diagonalCorootCocharacter.{u} i j) p))
        (diagonalTorusWeight r (finProdFinEquiv (i, j))) =
      DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^ (2 : ℤ) := by
  rw [torusCharacter_diagonalCorootCocharacter A i j i j p]
  simp [hij, hij.symm]

/-- Conjugation by the coroot of a root rescales that root's additive
parameter by the square of the input unit. -/
theorem corootPoints_mul_rootSubgroupPoints_mul_inv_self (A : CommAlgCat.{v} R)
    {i j : Fin (r + 1)} (hij : i ≠ j)
    (p : WithConv (MonoidAlgebra R (Multiplicative ℤ) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    corootPoints A i j p * rootSubgroupPoints A hij c * (corootPoints A i j p)⁻¹ =
      rootSubgroupPoints A hij
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm
          (Multiplicative.ofAdd
            ((DiagonalizableGroup.pointsMulEquiv p (Multiplicative.ofAdd 1) ^ (2 : ℤ) : Aˣ) •
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c)))) := by
  simpa only [hij, hij.symm, ↓reduceIte, sub_zero, zero_sub, sub_neg_eq_add,
    Int.reduceAdd] using corootPoints_mul_rootSubgroupPoints_mul_inv A i j hij p c

end

end TauCeti.ProjectiveGeneralLinear
