/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Descent
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Resolution
public import TauCeti.Algebra.Module.ProjectiveCover.Multiplicity
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
`[P i]` in the simple basis of `G₀(mod A)`, and when every simple is absolutely simple this gives
`Cᵀ * E = 1`. If `A` is finite-dimensional and every finitely generated module has a finite
resolution by finitely generated projectives, all these pairs are Euler-admissible and
`E i j` is the `(j, i)` entry of `C⁻¹`. Rows of `E` are indexed by the first argument of the
Euler form, which is not symmetric in general, so the transpose is part of the statement.

## Main results

* `TauCeti.IsProjectiveCover.extEuler_eq_finrank_end` and
  `TauCeti.IsProjectiveCover.extEuler_eq_zero`: `χ(P, T)` for a projective cover `P ⟶ S` and a
  simple module `T` is `dim_k End_A(S)` if `T ≅ S` and `0` otherwise.
* `TauCeti.isEulerAdmissibleOn_isFG`: over a finite-dimensional algebra, if every finitely
  generated module has a finite resolution by finitely generated projectives, every pair of
  finitely generated modules is Euler-admissible.
* `TauCeti.transpose_cartanMatrix_mul_extEuler`: `Cᵀ * E = 1` for absolutely simple simples.
* `TauCeti.extEuler_eq_inverseCartanMatrix`: under finite projective resolutions,
  `χ(S i, S j)` is the `(j, i)` entry of the inverse Cartan matrix.

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

/-! ### Projective covers against simple modules -/

section ProjectiveCover

variable {P T : ModuleCat.{u} A} {S : Type*} [AddCommGroup S] [Module A S] {f : P →ₗ[A] S}

/-- **The diagonal Ext-Euler value.** For a projective cover `P ⟶ S` of a simple module and a
simple module `T ≅ S`, `χ(P, T)` is the dimension of the division algebra `End_A(S)`. -/
theorem IsProjectiveCover.extEuler_eq_finrank_end [Module k S] [IsScalarTower k A S]
    (hf : IsProjectiveCover f) [IsSimpleModule A T] (e : T ≃ₗ[A] S)
    (h : IsEulerAdmissible.{u} k P T) :
    extEuler.{u} k h = Module.finrank k (Module.End A S) := by
  have : Module.Projective A P := hf.projective
  rw [extEuler_projective k h, (ModuleCat.homLinearEquiv (S := k)).finrank_eq,
    hf.finrank_linearMap_eq_finrank_end e]

/-- **The off-diagonal Ext-Euler value.** For a projective cover `P ⟶ S` of a simple module and a
simple module `T` not isomorphic to `S`, `χ(P, T) = 0`. -/
theorem IsProjectiveCover.extEuler_eq_zero [IsSimpleModule A S] (hf : IsProjectiveCover f)
    [IsSimpleModule A T] (he : IsEmpty (T ≃ₗ[A] S)) (h : IsEulerAdmissible.{u} k P T) :
    extEuler.{u} k h = 0 := by
  have : Module.Projective A P := hf.projective
  rw [extEuler_projective k h, (ModuleCat.homLinearEquiv (S := k)).finrank_eq,
    hf.finrank_linearMap_eq_zero he, Nat.cast_zero]

end ProjectiveCover

/-! ### Euler-admissibility of finitely generated modules -/

variable (k) in
/-- If every finitely generated module over a finite-dimensional algebra has a finite resolution by
finitely generated projectives, then every pair of finitely generated modules is
Euler-admissible: the resolution bounds the `Ext` groups, and the Hom spaces from its terms are
finite-dimensional. -/
theorem isEulerAdmissibleOn_isFG [FiniteDimensional k A]
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A)) :
    IsEulerAdmissibleOn.{u} k (ModuleCat.isFG A) (ModuleCat.isFG A) where
  isEulerAdmissible X Y hX hY := by
    obtain ⟨r⟩ := (ExactStructure.admitsFiniteResolution_iff _ _).mp (h X hX)
    refine r.isEulerAdmissible (finiteProjectiveModules_le_isProjective A) fun Z hZ => ?_
    have : Module.Finite A Z := (finiteProjectiveModules_iff.mp hZ).1
    have : Module.Finite A Y := (ModuleCat.isFG_iff Y).mp hY
    have : FiniteDimensional k Z := Module.Finite.trans A Z
    have : FiniteDimensional k Y := Module.Finite.trans A Y
    exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := k)).symm

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
/-- **The Ext-Euler matrix is a left inverse of the transposed Cartan matrix.** Let `P i ⟶ S i`
be projective covers of absolutely simple modules. If every pair of finitely generated modules is
Euler-admissible, then `Cᵀ * E = 1`, where `C i j = [P j : S i]` is the Cartan matrix and
`E i j = χ(S i, S j)` is the Ext-Euler matrix of the simples. -/
theorem transpose_cartanMatrix_mul_extEuler
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (hend : ∀ i, Module.finrank k (Module.End A (S i).obj) = 1)
    (hadm : IsEulerAdmissibleOn.{u} k (ModuleCat.isFG A) (ModuleCat.isFG A)) :
    (cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive)ᵀ *
      Matrix.of (fun i j ↦
        extEuler.{u} k (hadm.isEulerAdmissible (S i).property (S j).property)) = 1 := by
  -- `G₀(mod A)` is the exact `K₀` of the structure induced on the finitely generated modules, so
  -- the Ext-Euler pairing of `TauCeti.extEulerPairing` transports to it.
  have hG : finiteModulesExactStructure A =
      (ExactStructure.abelian (ModuleCat.{u} A)).fullSubcategory (ModuleCat.isFG A)
        (isExtensionClosed_finiteModules A) :=
    ExactStructure.ext _ _ fun T => by
      rw [finiteModulesExactStructure_conflation_iff, ExactStructure.fullSubcategory_conflation_iff,
        ExactStructure.abelian_conflation]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ExactK0.{u} (finiteModulesExactStructure A) →+
      ExactK0.{u} (finiteModulesExactStructure A) →+ ℤ, ∀ X Y : FGModuleCat.{u} A,
        Φ (ExactK0.of X) (ExactK0.of Y) =
          extEuler.{u} k (hadm.isEulerAdmissible X.property Y.property) := by
    rw [hG]
    exact ⟨extEulerPairing _ _ hadm, extEulerPairing_of_of _ _ hadm⟩
  ext i j
  have hPi : ModuleCat.isFG A (P i).obj :=
    finiteProjectiveModules_le_finiteModules A _ (P i).property
  -- The `(i, j)` entry is `χ` of the Cartan image of `[P i]` against `[S j]`.
  have hentry : ((cartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive)ᵀ *
      Matrix.of (fun i j ↦
        extEuler.{u} k (hadm.isEulerAdmissible (S i).property (S j).property))) i j =
      Φ (cartanMap A (ExactK0.of (P i))) (ExactK0.of (S j)) := by
    rw [cartanMap_of_eq_sum P S hSnoniso hSexhaustive i, map_sum, AddMonoidHom.finsetSum_apply,
      Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.transpose_apply, cartanMatrix_apply, map_zsmul, AddMonoidHom.zsmul_apply,
      Matrix.of_apply, smul_eq_mul, hΦ]
  rw [hentry, cartanMap_of A (P i).property, hΦ, Matrix.one_apply]
  have : IsSimpleModule A (S j).obj := hS j
  have : IsSimpleModule A (S i).obj := hS i
  split_ifs with hij
  · subst hij
    rw [(hf i).extEuler_eq_finrank_end (LinearEquiv.refl A _), hend i, Nat.cast_one]
  · exact (hf i).extEuler_eq_zero (hSnoniso (Ne.symm hij)) _

include hSnoniso hSexhaustive in
/-- **The Ext-Euler matrix is the transposed inverse Cartan matrix.** Let `P i ⟶ S i` be
projective covers of absolutely simple modules over a finite-dimensional algebra. If every finitely
generated module has a finite resolution by finitely generated projectives, then `χ(S i, S j)` is
the `(j, i)` entry of the inverse of the Cartan matrix `C i j = [P j : S i]`. -/
theorem extEuler_eq_inverseCartanMatrix [FiniteDimensional k A]
    {f : ∀ i, (P i).obj →ₗ[A] (S i).obj} (hf : ∀ i, IsProjectiveCover (f i))
    (hend : ∀ i, Module.finrank k (Module.End A (S i).obj) = 1)
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A))
    (i j : I) (hadm : IsEulerAdmissible.{u} k (S i).obj (S j).obj) :
    extEuler.{u} k hadm =
      inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h j i := by
  have hE := transpose_cartanMatrix_mul_extEuler P S hind hPnoniso hPexhaustive hSnoniso
    hSexhaustive hf hend (isEulerAdmissibleOn_isFG k h)
  have hC := congrArg Matrix.transpose
    (cartanMatrix_mul_inverseCartanMatrix P S hind hPnoniso hPexhaustive hSnoniso hSexhaustive h)
  rw [Matrix.transpose_mul, Matrix.transpose_one] at hC
  -- `(C⁻¹)ᵀ` is a left inverse and `E` a right inverse of `Cᵀ`, so they agree.
  have hinv := left_inv_eq_right_inv hC hE
  have hij' := congrFun₂ hinv i j
  rw [Matrix.transpose_apply, Matrix.of_apply] at hij'
  exact hij'.symm

end TauCeti
