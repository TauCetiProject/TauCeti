/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic
public import TauCeti.CategoryTheory.Semisimple.Finrank

/-!
# The Grothendieck ring of a finite semisimple category

In a finite semisimple abelian category every object is a finite biproduct of simple objects, with
multiplicities that do not depend on the decomposition (`TauCeti.simpleMultiplicities`). This file
reads that fact in the split Grothendieck group `TauCeti.SplitK0 C`: the classes of the chosen
simple representatives form a `ℤ`-basis, `TauCeti.SplitK0.simpleBasis`, and the coordinates of the
class of an object in that basis are its simple multiplicities. In particular two objects have the
same class exactly when they are isomorphic, and split `K₀` is a free abelian group of rank the
number of simple classes.

When the category is moreover monoidal with additive tensor product, `TauCeti.SplitK0 C` is a ring
(`TauCeti/CategoryTheory/GrothendieckGroup/Monoidal/Basic.lean`), and the basis turns it into a
ring with a distinguished basis whose structure constants are the multiplicities of the simple
objects in tensor products of simple objects. Over an algebraically closed field `k`, with
finite-dimensional morphism spaces, these are the **fusion coefficients**
`N_{ST}^U = finrank k (S ⊗ T ⟶ U)` (`TauCeti.fusionCoeff`), which can equally be computed from
`U ⟶ S ⊗ T`. If the tensor unit is simple, the unit of the ring is a basis element. This is the
based ring of a fusion category in the sense of Etingof–Gelaki–Nikshych–Ostrik; its duality
involution is in `TauCeti/CategoryTheory/Semisimple/Rigid.lean`.

⚠ The fusion coefficients are computed by a `k`-dimension, so their identification with
multiplicities needs the endomorphisms of each simple object to be `k`. Over a field that is not
algebraically closed this fails: for the real representations of a cyclic group of order three, the
two-dimensional rotation representation `V` has `End V ≅ ℂ`, so `finrank ℝ (𝟙 ⊗ V ⟶ V) = 2` while
`V` occurs once in `𝟙 ⊗ V`. The multiplicity form of the structure constants
(`TauCeti.SplitK0.simpleBasis_mul_simpleBasis`) needs no field at all.

## Main definitions

* `TauCeti.SplitK0.simpleBasis C`: the `ℤ`-basis of split `K₀` given by the classes of the simple
  representatives.
* `TauCeti.fusionCoeff k S T U`: the fusion coefficient `finrank k (S ⊗ T ⟶ U)` of three simple
  classes.
* `TauCeti.fusionMatrix k S`: the fusion matrix of `S`, with entry `N_{ST}^U` in row `T` and
  column `U`.

## Main results

* `TauCeti.SplitK0.simpleBasis_repr_of`: the coordinates of the class of an object are its simple
  multiplicities.
* `TauCeti.SplitK0.of_eq_of_iff_nonempty_iso`: objects with equal classes are isomorphic.
* `TauCeti.SplitK0.finrank_eq_card`: the rank of split `K₀` is the number of simple classes.
* `TauCeti.SplitK0.one_eq_simpleBasis`: the unit is the basis element of the tensor unit, when the
  tensor unit is simple.
* `TauCeti.fusionCoeff_eq_simpleMultiplicities` and `TauCeti.fusionCoeff_eq_finrank_hom`: the
  fusion coefficient is the multiplicity of `U` in `S ⊗ T`, and the dimension of `U ⟶ S ⊗ T`.
* `TauCeti.SplitK0.simpleBasis_mul_simpleBasis`: the product of two basis elements is the sum of
  the basis elements weighted by the multiplicities of the simple objects in their tensor product.
* `TauCeti.SplitK0.simpleBasis_mul_simpleBasis_eq_sum_fusionCoeff`: the same expansion, weighted
  by the fusion coefficients.
* `TauCeti.SplitK0.simpleBasis_repr_simpleBasis_mul_simpleBasis_nonneg`: the structure constants
  are nonnegative, so the Grothendieck ring is a ℤ₊-ring.
* `TauCeti.fusionMatrix_classOf_unit`: the fusion matrix of a simple tensor unit is the identity.
* `TauCeti.SplitK0.fusionMatrix_map_mulVec_ringHom`: the values of a ring homomorphism on the
  simple classes form a common eigenvector of the fusion matrices.
* `TauCeti.SplitK0.fusionMatrix_eq_transpose_leftMulMatrix`: the fusion matrix of `S` is the
  transpose of the matrix of left multiplication by `[S]`.
* `TauCeti.SplitK0.isIntegral_ringHom_apply`: the values of a ring homomorphism out of the
  Grothendieck ring are algebraic integers.

## References

* Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych, Victor Ostrik, *Tensor Categories*, Mathematical
  Surveys and Monographs **205**, AMS (2015), Sections 3.1 (based rings), 4.5 (the Grothendieck
  ring of a fusion category) and 4.16 (the split hypothesis over a general field).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w w' v u

namespace SplitK0

section Basis

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]
  [EssentiallySmall.{w} C]

variable (C) in
/-- The simple multiplicities, read in `ℤ`, as a biproduct-additive invariant. -/
private def simpleMultiplicitiesInvariant : AdditiveInvariant C (SimpleClasses C →₀ ℤ) where
  obj X := Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ) (simpleMultiplicities X)
  map_iso _ _ e := by rw [simpleMultiplicities_eq_of_iso e]
  map_biprod X Y := by rw [simpleMultiplicities_biprod, map_add]

/-- The class of an object is the sum of the classes of the simple representatives, each counted
with its multiplicity in the object. -/
theorem of_eq_sum (X : C) :
    (of X : SplitK0 C) = (simpleMultiplicities X).sum fun S n ↦ n • of S.repr := by
  obtain ⟨ι, hι, f, hf, hbf, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  let := hι
  let := hf
  let := hbf
  rw [simpleMultiplicities_eq_of_iso_biproduct f e, of_congr e, of_biproduct,
    ← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finsupp.sum_single_index (by simp), one_smul,
    of_congr (SimpleClasses.classOfReprIso (f i))]

variable (C) in
/-- The classes of the simple representatives form a `ℤ`-basis of split `K₀`. -/
def simpleBasis : Module.Basis (SimpleClasses C) ℤ (SplitK0 C) :=
  .ofRepr <| AddEquiv.toIntLinearEquiv <|
    AddMonoidHom.toAddEquiv (lift (simpleMultiplicitiesInvariant C))
      (Finsupp.linearCombination ℤ fun S ↦ (of S.repr : SplitK0 C)).toAddMonoidHom
      (hom_ext fun X ↦ by
        rw [AddMonoidHom.comp_apply, lift_of, AddMonoidHom.id_apply, of_eq_sum X]
        simp [simpleMultiplicitiesInvariant, Finsupp.linearCombination_apply,
          Finsupp.sum_mapRange_index])
      (Finsupp.addHom_ext fun S n ↦ by
        simp [simpleMultiplicitiesInvariant, Finsupp.smul_single])

/-- The basis element of a simple class is the class of its representative. -/
@[simp]
theorem simpleBasis_apply (S : SimpleClasses C) : simpleBasis C S = of S.repr := by
  simp [simpleBasis]

/-- The coordinates of the class of an object in `TauCeti.SplitK0.simpleBasis` are its simple
multiplicities. -/
@[simp]
theorem simpleBasis_repr_of (X : C) :
    (simpleBasis C).repr (of X) = (simpleMultiplicities X).mapRange (↑) Nat.cast_zero :=
  lift_of (simpleMultiplicitiesInvariant C) X

/-- The class of a simple object is the basis element of its simple class. -/
theorem of_eq_simpleBasis (X : C) [Simple X] :
    (of X : SplitK0 C) = simpleBasis C (SimpleClasses.classOf X) := by
  rw [simpleBasis_apply, of_congr (SimpleClasses.classOfReprIso X)]

/-- Two objects of a finite semisimple category have the same class in split `K₀` exactly when
they are isomorphic. -/
theorem of_eq_of_iff_nonempty_iso (X Y : C) :
    (of X : SplitK0 C) = of Y ↔ Nonempty (X ≅ Y) := by
  rw [nonempty_iso_iff_simpleMultiplicities_eq, ← (simpleBasis C).repr.injective.eq_iff,
    simpleBasis_repr_of, simpleBasis_repr_of]
  exact (Finsupp.mapRange_injective _ _ Nat.cast_injective).eq_iff

/-- The class of an object of a finite semisimple category vanishes exactly when the object is
zero. -/
@[simp]
theorem of_eq_zero_iff (X : C) : (of X : SplitK0 C) = 0 ↔ IsZero X := by
  rw [← of_zero, of_eq_of_iff_nonempty_iso]
  exact ⟨fun ⟨e⟩ ↦ (isZero_zero C).of_iso e, fun h ↦ ⟨h.isoZero⟩⟩

/-- Split `K₀` of a finite semisimple category is a free abelian group. -/
instance : Module.Free ℤ (SplitK0 C) :=
  .of_basis (simpleBasis C)

/-- Split `K₀` of a finite semisimple category with finitely many simple classes is finitely
generated. -/
instance [Finite (SimpleClasses C)] : Module.Finite ℤ (SplitK0 C) :=
  .of_basis (simpleBasis C)

/-- Split `K₀` of a finite semisimple category has rank the number of simple classes. -/
theorem finrank_eq_card : Module.finrank ℤ (SplitK0 C) = Nat.card (SimpleClasses C) :=
  Module.finrank_eq_nat_card_basis (simpleBasis C)

end Basis

section Unit

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]
  [EssentiallySmall.{w} C] [MonoidalCategory C]

/-- When the tensor unit is simple, the unit of the Grothendieck ring is the basis element of the
tensor unit. -/
theorem one_eq_simpleBasis [Simple (𝟙_ C)] :
    (1 : SplitK0 C) = simpleBasis C (SimpleClasses.classOf (𝟙_ C)) := by
  rw [one_def, of_eq_simpleBasis]

end Unit

section Mul

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]
  [EssentiallySmall.{w} C] [MonoidalCategory C] [MonoidalPreadditive C]

/-- The coordinates of the product of two basis elements of the Grothendieck ring are the
multiplicities of the simple objects in the tensor product of the representatives. -/
theorem simpleBasis_repr_simpleBasis_mul_simpleBasis (S T U : SimpleClasses C) :
    (simpleBasis C).repr (simpleBasis C S * simpleBasis C T) U =
      simpleMultiplicities (S.repr ⊗ T.repr) U := by
  simp

/-- The structure constants of the Grothendieck ring in the basis of simple classes are
nonnegative: it is a ℤ₊-ring. -/
theorem simpleBasis_repr_simpleBasis_mul_simpleBasis_nonneg (S T U : SimpleClasses C) :
    0 ≤ (simpleBasis C).repr (simpleBasis C S * simpleBasis C T) U := by
  rw [simpleBasis_repr_simpleBasis_mul_simpleBasis]
  positivity

/-- The product of two basis elements of the Grothendieck ring of a finite semisimple category
with finitely many simple classes is the sum of the basis elements weighted by the multiplicities
of the simple objects in the tensor product of the representatives. -/
theorem simpleBasis_mul_simpleBasis [Fintype (SimpleClasses C)] (S T : SimpleClasses C) :
    simpleBasis C S * simpleBasis C T =
      ∑ U, (simpleMultiplicities (S.repr ⊗ T.repr) U : ℤ) • simpleBasis C U := by
  conv_lhs => rw [← (simpleBasis C).sum_repr (simpleBasis C S * simpleBasis C T)]
  simp_rw [simpleBasis_repr_simpleBasis_mul_simpleBasis]

/-- The values of a ring homomorphism out of the Grothendieck ring of a finite semisimple
category with finitely many simple classes are algebraic integers, since the Grothendieck ring is
then a finitely generated abelian group. -/
theorem isIntegral_ringHom_apply [Finite (SimpleClasses C)] {R : Type*} [Ring R]
    (ψ : SplitK0 C →+* R) (x : SplitK0 C) : IsIntegral ℤ (ψ x) :=
  (IsIntegral.of_finite ℤ x).map ψ.toIntAlgHom

end Mul

end SplitK0

section Fusion

variable (k : Type w') [Field k]

/-- The **fusion coefficient** `N_{ST}^U` of three simple classes: the dimension over `k` of the
morphisms from the tensor product of the representatives of `S` and `T` to the representative of
`U`. Over an algebraically closed field, with finite-dimensional morphism spaces, it is the
multiplicity of `U` in `S ⊗ T` (`TauCeti.fusionCoeff_eq_simpleMultiplicities`). -/
def fusionCoeff {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
    (S T U : SimpleClasses C) : ℕ :=
  Module.finrank k (S.repr ⊗ T.repr ⟶ U.repr)

/-- The defining formula of `TauCeti.fusionCoeff`. -/
theorem fusionCoeff_def {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] (S T U : SimpleClasses C) :
    fusionCoeff k S T U = Module.finrank k (S.repr ⊗ T.repr ⟶ U.repr) :=
  (rfl)

/-- The **fusion matrix** of a simple class `S`: the matrix of fusion coefficients `N_{ST}^U`,
indexed by `T` (row) and `U` (column). Over an algebraically closed field, with
finite-dimensional morphism spaces, its row `T` lists the coordinates of `[S] * [T]` in the basis
of simple classes (`TauCeti.SplitK0.simpleBasis_mul_simpleBasis_eq_sum_fusionCoeff`). -/
def fusionMatrix {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [MonoidalCategory C]
    (S : SimpleClasses C) : Matrix (SimpleClasses C) (SimpleClasses C) ℕ :=
  Matrix.of fun T U ↦ fusionCoeff k S T U

/-- The entry `(T, U)` of the fusion matrix of `S` is the fusion coefficient `N_{ST}^U`. -/
@[simp]
theorem fusionMatrix_apply {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
    [MonoidalCategory C] (S T U : SimpleClasses C) : fusionMatrix k S T U = fusionCoeff k S T U :=
  (rfl)

variable [IsAlgClosed k] {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] [MonoidalCategory C]

/-- The fusion coefficient `N_{ST}^U` is the multiplicity of `U` in `S ⊗ T`. -/
theorem fusionCoeff_eq_simpleMultiplicities (S T U : SimpleClasses C) :
    fusionCoeff k S T U = simpleMultiplicities (S.repr ⊗ T.repr) U := by
  rw [fusionCoeff_def, finrank_homTo_simple_eq_simpleMultiplicities, SimpleClasses.classOf_repr]

/-- The fusion coefficient `N_{ST}^U` is also the dimension of the morphisms from `U` to
`S ⊗ T`. -/
theorem fusionCoeff_eq_finrank_hom (S T U : SimpleClasses C) :
    fusionCoeff k S T U = Module.finrank k (U.repr ⟶ S.repr ⊗ T.repr) := by
  rw [fusionCoeff_eq_simpleMultiplicities, finrank_hom_simple_eq_simpleMultiplicities,
    SimpleClasses.classOf_repr]

omit [IsFiniteSemisimpleCategory C] in
/-- When the tensor unit is simple, its fusion matrix is the identity matrix:
`N_{𝟙 T}^U = 1` if `T = U` and `0` otherwise. -/
@[simp]
theorem fusionMatrix_classOf_unit [Simple (𝟙_ C)] [DecidableEq (SimpleClasses C)] :
    fusionMatrix k (SimpleClasses.classOf (𝟙_ C)) = 1 := by
  ext T U
  rw [fusionMatrix_apply, fusionCoeff_def,
    (Linear.homCongr k (whiskerRightIso (SimpleClasses.classOfReprIso (𝟙_ C)) T.repr ≪≫ λ_ T.repr)
      (Iso.refl U.repr)).finrank_eq, finrank_hom_simple_simple, Matrix.one_apply]
  by_cases h : T = U
  · subst h
    rw [ite_eq_left ⟨Iso.refl _⟩, ite_eq_left rfl]
  · rw [ite_eq_right (mt (SimpleClasses.eq_iff_nonempty_iso T U).2 h), ite_eq_right h]

namespace SplitK0

variable [EssentiallySmall.{w} C] [MonoidalPreadditive C]

/-- The coordinates of the product of two basis elements of the Grothendieck ring are the fusion
coefficients. -/
theorem simpleBasis_repr_simpleBasis_mul_simpleBasis_eq_fusionCoeff (S T U : SimpleClasses C) :
    (simpleBasis C).repr (simpleBasis C S * simpleBasis C T) U = fusionCoeff k S T U := by
  rw [simpleBasis_repr_simpleBasis_mul_simpleBasis, fusionCoeff_eq_simpleMultiplicities]

/-- The fusion matrix of `S` is the transpose of the matrix of left multiplication by `[S]` in the
basis of simple classes. -/
theorem fusionMatrix_eq_transpose_leftMulMatrix [Fintype (SimpleClasses C)]
    [DecidableEq (SimpleClasses C)] (S : SimpleClasses C) :
    (fusionMatrix k S).map (Nat.cast : ℕ → ℤ) =
      (Algebra.leftMulMatrix (simpleBasis C) (simpleBasis C S)).transpose := by
  ext T U
  simp [Algebra.leftMulMatrix_eq_repr_mul, fusionCoeff_eq_simpleMultiplicities]

/-- The product of two basis elements of the Grothendieck ring of a finite semisimple category
with finitely many simple classes is the sum of the basis elements weighted by the fusion
coefficients: `[S] * [T] = ∑ U, N_{ST}^U [U]`. -/
theorem simpleBasis_mul_simpleBasis_eq_sum_fusionCoeff [Fintype (SimpleClasses C)]
    (S T : SimpleClasses C) :
    simpleBasis C S * simpleBasis C T = ∑ U, (fusionCoeff k S T U : ℤ) • simpleBasis C U := by
  simp_rw [simpleBasis_mul_simpleBasis, fusionCoeff_eq_simpleMultiplicities]

open Matrix in
/-- The values of a ring homomorphism `ψ` on the basis of simple classes form an eigenvector of
each fusion matrix, with eigenvalue the value of `ψ` on that class:
`∑ U, N_{ST}^U ψ [U] = ψ [S] ψ [T]` for all simple classes `S` and `T`. -/
theorem fusionMatrix_map_mulVec_ringHom [Fintype (SimpleClasses C)] {R : Type*} [Ring R]
    (ψ : SplitK0 C →+* R) (S : SimpleClasses C) :
    (fusionMatrix k S).map (Nat.cast : ℕ → R) *ᵥ (fun T ↦ ψ (simpleBasis C T)) =
      ψ (simpleBasis C S) • fun T ↦ ψ (simpleBasis C T) := by
  ext T
  rw [Pi.smul_apply, smul_eq_mul, ← map_mul, simpleBasis_mul_simpleBasis_eq_sum_fusionCoeff k,
    map_sum]
  simp [Matrix.mulVec, dotProduct]

end SplitK0

end Fusion

end TauCeti
