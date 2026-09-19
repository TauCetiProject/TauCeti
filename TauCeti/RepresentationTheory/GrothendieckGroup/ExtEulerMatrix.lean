/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Matrix
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.ModuleResolution
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.ProjectiveCover
public import TauCeti.RepresentationTheory.GrothendieckGroup.UnimodularCartanMatrix

/-!
# The Ext-Euler matrix of a finite-dimensional algebra

Let `A` be an algebra over a field `k`, with finite exhaustive families of pairwise nonisomorphic
simple modules `S i` and indecomposable projectives `P i`, where `P i ⟶ S i` is a projective
cover. This file computes the Ext-Euler characteristic

`χ(M, N) = ∑ n, (-1)ⁿ dim_k Extⁿ_A(M, N)`

of `TauCeti.extEuler` on these two families.

Against simples, the projective covers are dual to the simples up to the division algebras
`D i = End_A(S i)`: `χ(P i, S j) = dim_k Hom_A(P i, S j)` is `dim_k D i` when `i = j` and `0`
otherwise. Over a general field the diagonal entry is `dim_k D i`; it is `1` when `S i` is
absolutely simple, that is, when `D i` is one-dimensional.

If every pair of finitely generated modules is Euler-admissible, the matrix `E i j = χ(S i, S j)`
is therefore constrained by the Cartan matrix `C i j = [P j : S i]`: column `i` of `C` expresses
`[P i]` in the simple basis of `G₀(mod A)`. Over a general field this gives
`Cᵀ * E = diagonal (fun i ↦ dim_k D i)`; when every simple is absolutely simple it gives
`Cᵀ * E = 1`. If `A` is finite-dimensional and every finitely generated module has a finite
resolution by finitely generated projectives, all these pairs are Euler-admissible and `C` is
invertible, so `E = (C⁻¹)ᵀ * diagonal (fun i ↦ dim_k D i)`: the entry `E i j` is the `(j, i)`
entry of `C⁻¹` times `dim_k D j`. If moreover every simple is absolutely simple, then
`E = (C⁻¹)ᵀ`. Rows of `E` are indexed by the first argument of the Euler form,
which is not symmetric in general, so the transpose is part of the statement.

## Main results

* `TauCeti.transpose_cartanMatrix_mul_extEulerMatrix_eq_diagonal`:
  `Cᵀ * E = diagonal (fun i ↦ dim_k End_A(S i))` over a general field.
* `TauCeti.transpose_cartanMatrix_mul_extEuler`: `Cᵀ * E = 1` for absolutely simple simples.
* `TauCeti.extEulerMatrix_eq_transpose_inverseCartanMatrix_mul_diagonal` and
  `TauCeti.extEuler_eq_inverseCartanMatrix_mul_finrank`: under finite projective resolutions,
  `E = (C⁻¹)ᵀ * diagonal (fun i ↦ dim_k End_A(S i))` over a general field.
* `TauCeti.extEulerMatrix_eq_transpose_inverseCartanMatrix` and
  `TauCeti.extEuler_eq_inverseCartanMatrix`: for absolutely simple simples under finite projective
  resolutions, `E = (C⁻¹)ᵀ`, so `χ(S i, S j)` is the `(j, i)` entry of the inverse Cartan matrix.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, Definition 3.11 and Proposition 3.13.
* Peter Webb, *A Course in Finite Group Representation Theory*, Chapter 7, Section 7.4, for the
  division-algebra correction over a general field.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat Matrix

universe u v

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]

/-! ### The Ext-Euler matrix of the simple modules -/

variable [IsArtinianRing A] {I : Type v} [Fintype I] [DecidableEq I]
variable (P : I → (finiteProjectiveModules A).FullSubcategory)
variable (S : I → FGModuleCat.{u} A) [hS : ∀ i, IsSimpleModule A (S i)]
variable (hind : ∀ i, IsIndecomposableModule A (P i).obj)
variable (hPnoniso : Pairwise fun i j ↦ IsEmpty (↑(P i).obj ≃ₗ[A] ↑(P j).obj))
variable (hPexhaustive : IsExhaustiveIndecomposableProjectiveFamily P)
variable (hSnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[A] S j))
variable (hSexhaustive : IsExhaustiveSimpleFamily S)

include hSnoniso hSexhaustive in
/-- **The general-field Cartan/Ext-Euler identity.** Let `P i ⟶ S i` be projective covers of
simple modules. If every pair of finitely generated modules is Euler-admissible, then
`Cᵀ * E = diagonal (fun i ↦ dim_k End_A(S i))`, where `C i j = [P j : S i]` is the Cartan
matrix and `E` is the Ext-Euler matrix in the simple-class basis. -/
theorem transpose_cartanMatrix_mul_extEulerMatrix_eq_diagonal
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (hadm : IsEulerAdmissibleOn.{u} k (ModuleCat.isFG A) (ModuleCat.isFG A)) :
    (cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive)ᵀ *
      extEulerMatrix (ModuleCat.isFG A) (ModuleCat.isFG A)
        (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A) hadm
        (simpleClassBasis S hSnoniso hSexhaustive)
        (simpleClassBasis S hSnoniso hSexhaustive) =
      Matrix.diagonal fun i ↦ (Module.finrank k (Module.End A (S i).obj) : ℤ) := by
  -- `Φ` is the Ext-Euler pairing, typed on the Grothendieck group of `cartanMap` and
  -- `simpleClassBasis`; this is definitionally the domain of `extEulerMatrix`.
  let Φ : ExactK0 (finiteModulesExactStructure A) →+ ExactK0 (finiteModulesExactStructure A) →+ ℤ :=
    extEulerPairing (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A) hadm
  have hΦ (X Y : FGModuleCat.{u} A) :
      Φ (ExactK0.of X) (ExactK0.of Y) = extEuler.{u} k (hadm.isEulerAdmissible X.2 Y.2) :=
    extEulerPairing_of_of _ _ hadm X Y
  ext i j
  -- The `(i, j)` entry is `χ` of the Cartan image of `[P i]` against `[S j]`.
  have hentry : ((cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive)ᵀ *
      extEulerMatrix (ModuleCat.isFG A) (ModuleCat.isFG A)
        (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A) hadm
        (simpleClassBasis S hSnoniso hSexhaustive)
        (simpleClassBasis S hSnoniso hSexhaustive)) i j =
      Φ (cartanMap A (ExactK0.of (P i))) (ExactK0.of (S j)) := by
    rw [cartanMap_of_eq_sum P S hSnoniso hSexhaustive i]
    simp only [map_sum, AddMonoidHom.finsetSum_apply, Matrix.mul_apply,
      Matrix.transpose_apply, cartanMatrix_apply, map_zsmul, AddMonoidHom.zsmul_apply,
      smul_eq_mul, hΦ]
    refine Finset.sum_congr rfl fun x _ ↦ congrArg _ ?_
    exact extEulerMatrix_of_of (h := hadm) (X := S x) (Y := S j)
      (hi := simpleClassBasis_apply S hSnoniso hSexhaustive x)
      (hj := simpleClassBasis_apply S hSnoniso hSexhaustive j)
  rw [hentry, cartanMap_of A (P i).property, Matrix.diagonal_apply, hΦ]
  have : IsSimpleModule A (S j).obj := hS j
  have : IsSimpleModule A (S i).obj := hS i
  split_ifs with hij
  · subst hij
    rw [(hf i).extEuler_eq_finrank_end (LinearEquiv.refl A _)]
  · exact (hf i).extEuler_eq_zero (hSnoniso (Ne.symm hij)) _

include hSnoniso hSexhaustive in
/-- **The Ext-Euler matrix is a right inverse of the transposed Cartan matrix.** Let `P i ⟶ S i`
be projective covers of absolutely simple modules. If every pair of finitely generated modules is
Euler-admissible, then `Cᵀ * E = 1`, where `C i j = [P j : S i]` is the Cartan matrix and `E` is
the Ext-Euler matrix in the simple-class basis. -/
theorem transpose_cartanMatrix_mul_extEuler
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (hend : ∀ i, Module.finrank k (Module.End A (S i).obj) = 1)
    (hadm : IsEulerAdmissibleOn.{u} k (ModuleCat.isFG A) (ModuleCat.isFG A)) :
    (cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive)ᵀ *
      extEulerMatrix (ModuleCat.isFG A) (ModuleCat.isFG A)
        (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A) hadm
        (simpleClassBasis S hSnoniso hSexhaustive)
        (simpleClassBasis S hSnoniso hSexhaustive) = 1 := by
  rw [transpose_cartanMatrix_mul_extEulerMatrix_eq_diagonal P S hind hPnoniso hPexhaustive
    hSnoniso hSexhaustive hf]
  ext i j
  simp [hend]

include hSnoniso hSexhaustive in
/-- **The Ext-Euler matrix via the inverse Cartan matrix over a general field.** Let `P i ⟶ S i`
be projective covers of simple modules over a finite-dimensional algebra. If every finitely
generated module has a finite resolution by finitely generated projectives, then
`E = (C⁻¹)ᵀ * diagonal (fun i ↦ dim_k End_A(S i))`, where `C i j = [P j : S i]` is the Cartan
matrix and `E` is the Ext-Euler matrix in the simple-class basis. -/
theorem extEulerMatrix_eq_transpose_inverseCartanMatrix_mul_diagonal [FiniteDimensional k A]
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A)) :
    extEulerMatrix (ModuleCat.isFG A) (ModuleCat.isFG A)
        (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A)
        (isEulerAdmissibleOn_isFG k h)
        (simpleClassBasis S hSnoniso hSexhaustive)
        (simpleClassBasis S hSnoniso hSexhaustive) =
      (inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)ᵀ *
        Matrix.diagonal fun i ↦ (Module.finrank k (Module.End A (S i).obj) : ℤ) := by
  have hC := congrArg Matrix.transpose
    (cartanMatrix_mul_inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)
  rw [Matrix.transpose_mul, Matrix.transpose_one] at hC
  -- Multiply `Cᵀ * E = diagonal d` on the left by the left inverse `(C⁻¹)ᵀ` of `Cᵀ`.
  rw [← transpose_cartanMatrix_mul_extEulerMatrix_eq_diagonal P S hind hPnoniso hPexhaustive
    hSnoniso hSexhaustive hf, ← Matrix.mul_assoc, hC, Matrix.one_mul]

include hSnoniso hSexhaustive in
/-- **The Ext-Euler matrix is the transposed inverse Cartan matrix.** Let `P i ⟶ S i` be
projective covers of absolutely simple modules over a finite-dimensional algebra. If every finitely
generated module has a finite resolution by finitely generated projectives, then `E = (C⁻¹)ᵀ`,
where `C i j = [P j : S i]` is the Cartan matrix and `E` is the Ext-Euler matrix in the
simple-class basis. -/
theorem extEulerMatrix_eq_transpose_inverseCartanMatrix [FiniteDimensional k A]
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (hend : ∀ i, Module.finrank k (Module.End A (S i).obj) = 1)
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A)) :
    extEulerMatrix (ModuleCat.isFG A) (ModuleCat.isFG A)
        (isExtensionClosed_finiteModules A) (isExtensionClosed_finiteModules A)
        (isEulerAdmissibleOn_isFG k h)
        (simpleClassBasis S hSnoniso hSexhaustive)
        (simpleClassBasis S hSnoniso hSexhaustive) =
      (inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)ᵀ := by
  rw [extEulerMatrix_eq_transpose_inverseCartanMatrix_mul_diagonal P S hind hPnoniso
    hPexhaustive hSnoniso hSexhaustive hf h]
  simp [hend]

include hSnoniso hSexhaustive in
/-- **The Ext-Euler characteristic of simples via the inverse Cartan matrix over a general
field.** Let `P i ⟶ S i` be projective covers of simple modules over a finite-dimensional
algebra. If every finitely generated module has a finite resolution by finitely generated
projectives, then `χ(S i, S j)` is the `(j, i)` entry of the inverse of the Cartan matrix
`C i j = [P j : S i]` times `dim_k End_A(S j)`. -/
theorem extEuler_eq_inverseCartanMatrix_mul_finrank [FiniteDimensional k A]
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A))
    (i j : I) (hadm : IsEulerAdmissible.{u} k (S i).obj (S j).obj) :
    extEuler.{u} k hadm =
      inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h j i *
        Module.finrank k (Module.End A (S j).obj) := by
  have hij := congrFun₂ (extEulerMatrix_eq_transpose_inverseCartanMatrix_mul_diagonal (k := k) P S
    hind hPnoniso hPexhaustive hSnoniso hSexhaustive hf h) i j
  rw [extEulerMatrix_of_of (X := S i) (Y := S j)
      (hi := simpleClassBasis_apply S hSnoniso hSexhaustive i)
      (hj := simpleClassBasis_apply S hSnoniso hSexhaustive j),
    Matrix.mul_diagonal, Matrix.transpose_apply] at hij
  exact hij

include hSnoniso hSexhaustive in
/-- **The Ext-Euler characteristic of simples is the transposed inverse Cartan matrix.** Let
`P i ⟶ S i` be projective covers of absolutely simple modules over a finite-dimensional algebra.
If every finitely generated module has a finite resolution by finitely generated projectives, then
`χ(S i, S j)` is the `(j, i)` entry of the inverse of the Cartan matrix `C i j = [P j : S i]`. -/
theorem extEuler_eq_inverseCartanMatrix [FiniteDimensional k A]
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (hend : ∀ i, Module.finrank k (Module.End A (S i).obj) = 1)
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A))
    (i j : I) (hadm : IsEulerAdmissible.{u} k (S i).obj (S j).obj) :
    extEuler.{u} k hadm =
      inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h j i := by
  simp [extEuler_eq_inverseCartanMatrix_mul_finrank P S hind hPnoniso hPexhaustive hSnoniso
    hSexhaustive hf h i j hadm, hend]

end TauCeti
