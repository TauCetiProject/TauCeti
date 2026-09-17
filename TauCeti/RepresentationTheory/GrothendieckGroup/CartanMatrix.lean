/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.ProjectiveBasis
public import TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis

/-!
# Projective-simple coordinates and the Cartan matrix

Let `R` be an Artinian ring, and choose exhaustive families `(P i)` and `(S i)` of pairwise
nonisomorphic indecomposable projective and simple modules, indexed so that `P i` is a projective
cover of `S i`. The corresponding bases of `K₀(proj R)` and `G₀(mod R)` are in perfect integral
pairing: pairing `[P i]` with `[M]` reads the Jordan--Hölder multiplicity `[M : S i]`.

The matrix of the Cartan map in these bases therefore has entry

`C i j = [P j : S i]`.

Thus columns record projectives in the simple basis. This convention is important for left
modules: the row index is the simple module and the column index is the projective module.

## Main definitions

* `TauCeti.projectiveSimplePairing`: the integral multiplicity pairing between the projective and
  simple Grothendieck groups.
* `TauCeti.cartanMatrix`: the matrix of `TauCeti.cartanMap` in the indecomposable-projective and
  simple-class bases.

## Main results

* `TauCeti.projectiveSimplePairing_of_left`: pairing with `[P i]` is the `S i` Jordan--Hölder
  coordinate.
* `TauCeti.projectiveSimplePairing_isPerfPair`: for a finite indexing set, the multiplicity
  pairing is perfect.
* `TauCeti.cartanMatrix_apply`: the `(i,j)` entry is `[P j : S i]`.
* `TauCeti.cartanMap_of_eq_sum`: the `j`th Cartan-map column is the composition-factor vector of
  `P j`.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.ObjectProperty

universe u v

variable {R : Type u} [Ring R] [IsArtinianRing R]
variable {I : Type v}
variable (P : I → (finiteProjectiveModules R).FullSubcategory)
variable (S : I → FGModuleCat.{u} R) [hS : ∀ i, IsSimpleModule R (S i)]
variable (hind : ∀ i, IsIndecomposableModule R (P i).obj)
variable (hPnoniso : Pairwise fun i j ↦ IsEmpty (↥(P i).obj ≃ₗ[R] ↥(P j).obj))
variable (hPexhaustive : IsExhaustiveIndecomposableProjectiveFamily P)
variable (hSnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[R] S j))
variable (hSexhaustive : IsExhaustiveSimpleFamily S)

/-! ### The projective-simple multiplicity pairing -/

/-- **The projective-simple multiplicity pairing.** This is the coordinate-dual pairing between the
chosen projective and simple bases, indexed by the common type `I`, so pairing `[P i]` with a
module class reads its `S i` Jordan--Hölder coordinate.

It has its representation-theoretic meaning when `P i` is a projective cover of `S i`; the
construction itself only uses the common indexing, so no cover maps are required. -/
noncomputable def projectiveSimplePairing :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) →ₗ[ℤ]
      ExactK0.{u} (finiteModulesExactStructure R) →ₗ[ℤ] ℤ := by
  classical
  let bP := indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive
  let bS := simpleClassBasis S hSnoniso hSexhaustive
  exact bS.toDual.comp (bP.equiv bS (Equiv.refl I)).toLinearMap

/-- Pairing with the class of `P i` is the Jordan--Hölder coordinate attached to `S i`. -/
@[simp]
theorem projectiveSimplePairing_of_left (i : I)
    (x : ExactK0.{u} (finiteModulesExactStructure R)) :
    projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
        (ExactK0.of (P i)) x =
      jordanHolderCoordinate R (S i) x := by
  classical
  rw [← indecomposableProjectiveClassBasis_apply P hind hPnoniso hPexhaustive i,
    projectiveSimplePairing, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
    Equiv.refl_apply, Module.Basis.toDual_apply_right, simpleClassBasis_repr_apply]

/-- On object classes, the projective-simple pairing is Jordan--Hölder multiplicity. -/
theorem projectiveSimplePairing_of_of (i : I) (M : FGModuleCat.{u} R) :
    projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
        (ExactK0.of (P i)) (ExactK0.of M) =
      jordanHolderMultiplicity R M (S i) := by
  rw [projectiveSimplePairing_of_left, jordanHolderCoordinate_of]

/-- The selected projective and simple basis classes pair as a Kronecker delta. -/
theorem projectiveSimplePairing_basis [DecidableEq I] (i j : I) :
    projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
        (ExactK0.of (P i)) (ExactK0.of (S j)) =
      if i = j then 1 else 0 := by
  rw [projectiveSimplePairing_of_left]
  simpa only [exactK0OfFamily_apply, eq_comm] using
    jordanHolderCoordinate_exactK0OfFamily S hSnoniso i j

/-- For a finite indexing type, the integral projective-simple multiplicity pairing
is perfect: it identifies either Grothendieck group with the integral dual of the other. -/
theorem projectiveSimplePairing_isPerfPair [Finite I] :
    (projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive).IsPerfPair := by
  classical
  let bP := indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive
  let bS := simpleClassBasis S hSnoniso hSexhaustive
  have := Module.Finite.of_basis bS
  have := Module.Free.of_basis bS
  -- The pairing is the composite of the basis-matching equivalence with `bS.toDualEquiv`.
  have hbij : Function.Bijective
      (projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive) := by
    convert ((bP.equiv bS (Equiv.refl I)).trans bS.toDualEquiv).bijective using 1
    ext x
    rw [projectiveSimplePairing, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, Module.Basis.toDualEquiv_apply]
  exact .of_bijective _ hbij

/-! ### The Cartan matrix -/

variable [Fintype I]

/-- **The Cartan matrix** of the selected projective and simple families: the matrix of the Cartan
map `K₀(proj R) → G₀(mod R)` in the indecomposable-projective basis on the source and the
simple-class basis on the target. Rows are indexed by simples and columns by projectives. -/
noncomputable def cartanMatrix : Matrix I I ℤ := by
  classical
  exact LinearMap.toMatrix
    (indecomposableProjectiveClassBasis P hind hPnoniso hPexhaustive)
    (simpleClassBasis S hSnoniso hSexhaustive)
    (cartanMap R).toIntLinearMap

/-- **Cartan-matrix entries are composition multiplicities**: the `(i,j)` entry is the
Jordan--Hölder multiplicity `[P j : S i]`. -/
@[simp]
theorem cartanMatrix_apply (i j : I) :
    cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive i j =
      (jordanHolderMultiplicity R
        (⟨(P j).obj, (ModuleCat.isFG_iff (P j).obj).mpr
          (finiteProjectiveModules_iff.mp (P j).property).1⟩ : FGModuleCat.{u} R)
        (S i) : ℤ) := by
  classical
  rw [cartanMatrix, LinearMap.toMatrix_apply,
    indecomposableProjectiveClassBasis_apply, AddMonoidHom.coe_toIntLinearMap, cartanMap_of,
    simpleClassBasis_repr_apply, jordanHolderCoordinate_of]

/-- A Cartan-matrix entry is obtained by pairing the corresponding projective basis vector with
the image under the Cartan map of the column projective. -/
theorem cartanMatrix_apply_eq_projectiveSimplePairing (i j : I) :
    cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive i j =
      projectiveSimplePairing P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive
        (ExactK0.of (P i)) (cartanMap R (ExactK0.of (P j))) := by
  classical
  rw [cartanMatrix_apply, projectiveSimplePairing_of_left, cartanMap_of,
    jordanHolderCoordinate_of]

include hSnoniso hSexhaustive in
/-- **Columns of the Cartan matrix are projective composition-factor vectors.** The image of
`[P j]` under the Cartan map is the sum of the simple basis vectors with coefficients
`[P j : S i]`. -/
theorem cartanMap_of_eq_sum (j : I) :
    cartanMap R (ExactK0.of (P j)) =
      ∑ i, (jordanHolderMultiplicity R
        (⟨(P j).obj, (ModuleCat.isFG_iff (P j).obj).mpr
          (finiteProjectiveModules_iff.mp (P j).property).1⟩ : FGModuleCat.{u} R)
        (S i) : ℤ) • ExactK0.of (S i) := by
  classical
  let bS := simpleClassBasis S hSnoniso hSexhaustive
  have h := bS.sum_repr (cartanMap R (ExactK0.of (P j)))
  have hcoeff (i : I) :
      bS.repr (cartanMap R (ExactK0.of (P j))) i =
        (jordanHolderMultiplicity R
          (⟨(P j).obj, (ModuleCat.isFG_iff (P j).obj).mpr
            (finiteProjectiveModules_iff.mp (P j).property).1⟩ : FGModuleCat.{u} R)
          (S i) : ℤ) := by
    dsimp only [bS]
    rw [simpleClassBasis_repr_apply, cartanMap_of, jordanHolderCoordinate_of]
  calc
    cartanMap R (ExactK0.of (P j)) = ∑ i, bS.repr
        (cartanMap R (ExactK0.of (P j))) i • bS i := h.symm
    _ = ∑ i, (jordanHolderMultiplicity R
          (⟨(P j).obj, (ModuleCat.isFG_iff (P j).obj).mpr
            (finiteProjectiveModules_iff.mp (P j).property).1⟩ : FGModuleCat.{u} R)
          (S i) : ℤ) • ExactK0.of (S i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoeff i]
      congr 1
      exact simpleClassBasis_apply S hSnoniso hSexhaustive i

end TauCeti
