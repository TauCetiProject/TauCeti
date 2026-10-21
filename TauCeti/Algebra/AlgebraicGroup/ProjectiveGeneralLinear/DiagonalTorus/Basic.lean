/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus

/-!
# The diagonal split torus of the projective general linear group

The rank-`r` split torus embeds in `PGL_{r+1}` by conjugation with
`diag(s₀, …, s_{r-1}, 1)`. Fixing the last diagonal entry removes the scalar kernel
of the diagonal torus of `GL_{r+1}`. This construction works over every commutative
base ring, and its coordinate morphism is surjective.

In the matrix-unit representation of `PGL`, the torus is diagonal: the weight at
`Eᵢⱼ` is `εᵢ - εⱼ`, with `εᵣ = 0`. These weights span the full character lattice,
since the weights at `Eᵢᵣ` are the coordinate basis. This supplies the torus and
its explicit characters for the root datum of the projective general linear group.
Maximality and the identification of its adjoint roots are separate assertions.

The construction reuses `ProjectiveGeneralLinear.conjugationMap` and
`GeneralLinear.weightTorusCoordinateMap`. Its organization follows the
special-linear diagonal torus in `SpecialLinear.DiagonalTorus.Basic`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§16.1 and 26.3.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ProjectiveGeneralLinear

universe u v

noncomputable section

private def diagonalLiftWeight (r : ℕ) (k : Fin (r + 1)) : ULift.{u} (Fin r) → ℤ :=
  fun i ↦ if k = i.down.castSucc then 1 else 0

/-- The weights of the diagonal projective torus on the matrix units, with the
last diagonal coordinate normalized to one. -/
def diagonalTorusWeight (r : ℕ) (a : Fin ((r + 1) * (r + 1))) :
    ULift.{u} (Fin r) → ℤ :=
  diagonalLiftWeight r (finProdFinEquiv.symm a).1 -
    diagonalLiftWeight r (finProdFinEquiv.symm a).2

/-- The weight at `Eᵢⱼ` is the difference of the two coordinate characters;
the last coordinate character is zero. -/
@[simp]
theorem diagonalTorusWeight_apply (r : ℕ) (a : Fin ((r + 1) * (r + 1)))
    (i : ULift.{u} (Fin r)) :
    diagonalTorusWeight r a i =
      (if (finProdFinEquiv.symm a).1 = i.down.castSucc then 1 else 0) -
        (if (finProdFinEquiv.symm a).2 = i.down.castSucc then 1 else 0) :=
  (rfl)

/-- The matrix-unit weights generate the character lattice of the projective torus. -/
theorem span_range_diagonalTorusWeight_eq_top (r : ℕ) :
    Submodule.span ℤ (Set.range (diagonalTorusWeight.{u} r)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℤ (ULift.{u} (Fin r))).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  refine ⟨finProdFinEquiv (i.down.castSucc, Fin.last r), ?_⟩
  ext j
  simp [diagonalTorusWeight_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]

variable (r : ℕ) (R : Type u) [CommRing R]

/-- The coordinate morphism of the rank-`r` diagonal torus in `PGL_{r+1}`:
conjugation by `diag(s₀, …, s_{r-1}, 1)`. -/
def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra (r + 1) R ⟶
      (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj :=
  conjugationMap (r + 1) R ≫
    GeneralLinear.weightTorusCoordinateMap (diagonalLiftWeight r)

private theorem map_genericMatrix_diagonalLift :
    (GeneralLinear.genericMatrix R (r + 1)).map
        (GeneralLinear.weightTorusCoordinateMap (R := R) (diagonalLiftWeight r)).hom =
      Matrix.diagonal (fun i ↦ MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (diagonalLiftWeight r i))) 1) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply, GeneralLinear.genericMatrix_apply,
    GeneralLinear.weightTorusCoordinateMap_X, Matrix.diagonal_apply]

private theorem map_inv_genericMatrix_diagonalLift :
    ((GeneralLinear.genericMatrix R (r + 1))⁻¹).map
        (GeneralLinear.weightTorusCoordinateMap (R := R) (diagonalLiftWeight r)).hom =
      Matrix.diagonal (fun i ↦ MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (diagonalLiftWeight r i)))⁻¹ 1) := by
  have h := GeneralLinear.map_inv_genericMatrix R (r + 1)
    (GeneralLinear.weightTorusCoordinateMap (R := R) (diagonalLiftWeight r)).hom.toAlgHom
  simp only [BialgHom.coe_toAlgHom] at h
  rw [h, map_genericMatrix_diagonalLift]
  apply Matrix.inv_eq_left_inv
  simp [Matrix.diagonal_mul_diagonal, ← MonoidAlgebra.one_def]

/-- In its matrix-unit representation, the projective diagonal torus is the
weight torus of the coordinate differences. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_diagonalTorusCoordinateMap :
    CommHopfAlgCat.mkQuotient _ (definingHopfIdeal (r + 1) R) ≫
        diagonalTorusCoordinateMap r R =
      GeneralLinear.weightTorusCoordinateMap (diagonalTorusWeight r) := by
  apply _root_.CommHopfAlgCat.hom_ext
  apply GeneralLinear.coordinateHopfAlgebra_bialgHom_ext
  intro a b
  have hmatrix :
      (GeneralLinear.genericMatrix R ((r + 1) * (r + 1))).map
          (CommHopfAlgCat.mkQuotient _ (definingHopfIdeal (r + 1) R) ≫
            diagonalTorusCoordinateMap r R).hom =
        conjugationMatrix
          ((GeneralLinear.genericMatrix R (r + 1)).map
            (GeneralLinear.weightTorusCoordinateMap (R := R) (diagonalLiftWeight r)).hom)
          (((GeneralLinear.genericMatrix R (r + 1))⁻¹).map
            (GeneralLinear.weightTorusCoordinateMap (R := R) (diagonalLiftWeight r)).hom) := by
    rw [diagonalTorusCoordinateMap, ← Category.assoc, CommHopfAlgCat.hom_comp,
      BialgHom.coe_comp, ← Matrix.map_map, map_genericMatrix_conjugationMap,
      conjugationMatrix_map]
  rw [map_genericMatrix_diagonalLift, map_inv_genericMatrix_diagonalLift] at hmatrix
  have hentry := congrArg (fun M ↦ M a b) hmatrix
  simp only [Matrix.map_apply, GeneralLinear.genericMatrix_apply] at hentry
  rw [hentry, GeneralLinear.weightTorusCoordinateMap_X, conjugationMatrix_apply]
  classical
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, ↓reduceIte,
      MonoidAlgebra.single_mul_single, mul_one]
    congr 1
    apply Multiplicative.toAdd.injective
    ext i
    simp [diagonalTorusWeight, sub_eq_add_neg]
  · by_cases hfirst : (finProdFinEquiv.symm a).1 = (finProdFinEquiv.symm b).1
    · have hsecond : (finProdFinEquiv.symm b).2 ≠ (finProdFinEquiv.symm a).2 := by
        intro h
        exact hab (finProdFinEquiv.symm.injective (Prod.ext hfirst h.symm))
      simp only [finProdFinEquiv_symm_apply] at hsecond
      simp [Matrix.diagonal_apply, hsecond, hab]
    · simp only [finProdFinEquiv_symm_apply] at hfirst
      simp [Matrix.diagonal_apply, hfirst, hab]

/-- The projective diagonal-torus coordinate morphism is surjective over every
commutative ring. Thus it defines a closed immersion of the split torus. -/
theorem diagonalTorusCoordinateMap_surjective :
    Function.Surjective (diagonalTorusCoordinateMap r R).hom := by
  have h := GeneralLinear.weightTorusCoordinateMap_surjective (R := R)
    (diagonalTorusWeight r) (span_range_diagonalTorusWeight_eq_top r)
  rw [← mkQuotient_comp_diagonalTorusCoordinateMap, CommHopfAlgCat.hom_comp] at h
  exact Function.Surjective.of_comp h

private theorem torusCharacter_diagonalLiftWeight {A : Type v} [CommRing A]
    (s : ULift.{u} (Fin r) → Aˣ) (k : Fin (r + 1)) :
    torusCharacter s (diagonalLiftWeight r k) =
      Fin.lastCases 1 (fun i ↦ s (ULift.up i)) k := by
  classical
  refine Fin.lastCases ?_ (fun j ↦ ?_) k
  · have hzero : diagonalLiftWeight.{u} r (Fin.last r) = 0 := by
      ext i
      simp [diagonalLiftWeight, (Fin.castSucc_lt_last i.down).ne']
    simp [hzero]
  · have hweight : diagonalLiftWeight r j.castSucc =
        Pi.single (ULift.up j : ULift.{u} (Fin r)) (1 : ℤ) := by
      ext i
      simp [diagonalLiftWeight, Pi.single_apply, ← ULift.down_inj, eq_comm]
    simp [hweight]

/-- The character at `Eᵢⱼ` evaluates to the ratio of the normalized diagonal
coordinates. The last coordinate is one, so this includes roots involving it. -/
@[simp]
theorem torusCharacter_diagonalTorusWeight {A : Type v} [CommRing A]
    (s : ULift.{u} (Fin r) → Aˣ) (a : Fin ((r + 1) * (r + 1))) :
    torusCharacter s (diagonalTorusWeight r a) =
      Fin.lastCases 1 (fun k ↦ s (ULift.up k)) (finProdFinEquiv.symm a).1 /
        Fin.lastCases 1 (fun k ↦ s (ULift.up k)) (finProdFinEquiv.symm a).2 := by
  -- Unfold only the difference of lift weights, then use their evaluation formula.
  simp only [diagonalTorusWeight, torusCharacter_sub,
    torusCharacter_diagonalLiftWeight]

/-- On algebra-valued points, the projective diagonal torus acts on the matrix
algebra by conjugation with `diag(s₀, …, s_{r-1}, 1)`. -/
@[simp]
theorem pointsMulEquiv_mapPointsFunctor_diagonalTorusCoordinateMap
    (A : CommAlgCat.{v} R)
    (p : HopfAlgebra.points (R := R)
      (H := MonoidAlgebra R (SplitTorus.characterGroup (ULift.{u} (Fin r)))) A) :
    pointsMulEquiv (r + 1) R A
        ((CommHopfAlgCat.Hom.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app A p) =
      Matrix.GeneralLinearGroup.innerAut
        (diagGL (Fin.lastCases 1 (fun i ↦ SplitTorus.pointsMulEquiv p (ULift.up i)))) := by
  rw [diagonalTorusCoordinateMap, CommHopfAlgCat.Hom.mapPointsFunctor_comp_app_apply]
  -- The point functor stores its coordinate algebra implicitly; `erw` resolves
  -- that presentation when the outer point map is exposed.
  erw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  erw [pointsMulEquiv_conjugationMap,
    GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap]
  congr 2
  funext k
  exact torusCharacter_diagonalLiftWeight r _ k

/-- The rank-`r` diagonal split torus as a morphism into `PGL_{r+1}`. -/
def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin r)) ⟶ groupScheme (r + 1) R :=
  eqToHom (DiagonalizableGroup.groupScheme_def R
      (SplitTorus.characterGroup (ULift.{u} (Fin r)))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (diagonalTorusCoordinateMap r R).op

/-- The diagonal-torus morphism is spectrum applied to coordinate restriction,
using the named split-torus presentation. -/
theorem diagonalTorus_def :
    diagonalTorus r R =
      eqToHom (DiagonalizableGroup.groupScheme_def R
          (SplitTorus.characterGroup (ULift.{u} (Fin r)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap r R).op :=
  (rfl)

/-- The diagonal split torus embeds as a closed subgroup of `PGL_{r+1}` over
every commutative base ring. -/
instance isClosedImmersion_diagonalTorus :
    AlgebraicGeometry.IsClosedImmersion (diagonalTorus r R).hom.hom.left := by
  rw [diagonalTorus_def]
  simpa only [eqToHom_refl, Category.comp_id] using
    (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin r)))) rfl
      (diagonalTorusCoordinateMap r R)).mpr (diagonalTorusCoordinateMap_surjective r R)

/-- The diagonal split torus, bundled as a closed subgroup scheme of `PGL_{r+1}`. -/
def diagonalTorusClosedSubgroup :
    ClosedSubgroupScheme (groupScheme (r + 1) R) :=
  ClosedSubgroupScheme.mk (diagonalTorus r R)

/-- The bundled diagonal torus has the subobject represented by its inclusion. -/
@[simp]
theorem coe_diagonalTorusClosedSubgroup :
    (diagonalTorusClosedSubgroup r R).1 = Subobject.mk (diagonalTorus r R) :=
  ClosedSubgroupScheme.coe_mk _

end

end TauCeti.ProjectiveGeneralLinear
