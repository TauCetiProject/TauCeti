/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Homology.Cube.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.Finite

/-!
# The Euler characteristic of a cube of modules

The signed totalization of a finite commutative cube in any preadditive category with finite
biproducts is strictly supported in the degrees `0, …, #ι`; this file records that support as
instances of `CochainComplex.IsStrictlyGE` and `CochainComplex.IsStrictlyLE`, which is how the
Euler-characteristic API bounds its sums.

Let `F : Finset ι ⥤ ModuleCat R` be a finite commutative cube of modules. The term of degree `r`
of its signed totalization `F.cubeComplex` is the product of the vertices `F(S)` of height
`#S = r` (`CategoryTheory.Functor.cubeComplexXLinearEquiv`). When the vertices are finite free,
so are the terms, and the Euler characteristic of the cube complex is the signed sum of the ranks
of the vertices, each vertex `F(S)` counted with the sign `(-1) ^ #S`. Over a Noetherian ring with
the rank-nullity property, such as `ℤ` or a field, Euler–Poincaré identifies this signed sum with
the Euler characteristic of the cohomology of the cube complex.

This computes the quantum components of the graded Euler characteristic of Khovanov homology from
the cube of resolutions: there the vertices are the homogeneous pieces of the circle tensors,
which are finite free.

## Main definitions

* `CategoryTheory.Functor.cubeComplexXLinearEquiv`: the term of degree `r` of the cube complex is
  the product of the vertices of height `r`.

## Main results

* `CategoryTheory.Functor.finrank_cubeComplex_X`: for finite free vertices, the rank of the term of
  degree `r` is the sum of the ranks of the vertices of height `r`.
* `CategoryTheory.Functor.eulerChar_cubeComplex`: the Euler characteristic of the cube complex is
  `∑ S, (-1) ^ #S rank F(S)`.
* `CategoryTheory.Functor.homologyEulerChar_cubeComplex`: **Euler–Poincaré for cubes**, the
  Euler characteristic of the cohomology of the cube complex is `∑ S, (-1) ^ #S rank F(S)`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*, Algebr. Geom. Topol. 2
  (2002), §2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset Module

universe w v u

namespace CategoryTheory.Functor

section Bounds

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {ι : Type w} [Fintype ι] [LinearOrder ι] (F : Finset ι ⥤ C)

/-- The cube complex is strictly supported in nonnegative degrees. -/
instance : F.cubeComplex.IsStrictlyGE 0 :=
  (F.cubeComplex.isStrictlyGE_iff 0).2 fun _ hr ↦ F.isZero_cubeComplex_X_of_neg hr

/-- The cube complex is strictly supported in the degrees at most the cardinality of the index
type. -/
instance : F.cubeComplex.IsStrictlyLE (Fintype.card ι) :=
  (F.cubeComplex.isStrictlyLE_iff _).2 fun _ hr ↦ F.isZero_cubeComplex_X_of_card_lt hr

end Bounds

variable {ι : Type w} [Fintype ι] [LinearOrder ι] {R : Type u} [Ring R]
  (F : Finset ι ⥤ ModuleCat.{v} R)

/-- The term of degree `r` of the cube complex of a cube of modules is the product of the vertices
of height `r`: an element is determined by its projections to these vertices, and a family of
elements of the vertices is the sum of their inclusions. -/
def cubeComplexXLinearEquiv (r : ℤ) :
    F.cubeComplex.X r ≃ₗ[R] ∀ S : {S : Finset ι // (#S : ℤ) = r}, F.obj S.1 where
  toFun x S := (F.cubeComplexπ S).hom x
  map_add' x y := by
    ext S
    simp
  map_smul' c x := by
    ext S
    simp
  invFun f := ∑ S, (F.cubeComplexι S).hom (f S)
  left_inv x := by
    simpa [-cubeComplex_total] using congr($(F.cubeComplex_total r).hom x)
  right_inv f := by
    ext T
    dsimp only
    rw [_root_.map_sum, Finset.sum_eq_single T]
    · exact congr($(F.cubeComplexι_π_self T).hom (f T))
    · intro S _ hS
      exact congr($(F.cubeComplexι_π_of_ne hS).hom (f S))
    · simp

/-- The coordinate of an element of a term of the cube complex at a vertex is its projection to
that vertex. -/
@[simp]
theorem cubeComplexXLinearEquiv_apply {r : ℤ} (x : F.cubeComplex.X r)
    (S : {S : Finset ι // (#S : ℤ) = r}) :
    F.cubeComplexXLinearEquiv r x S = (F.cubeComplexπ S).hom x :=
  (rfl)

/-- A family of elements of the vertices of height `r` corresponds to the sum of their inclusions
into the term of degree `r` of the cube complex. -/
@[simp]
theorem cubeComplexXLinearEquiv_symm_apply {r : ℤ}
    (f : ∀ S : {S : Finset ι // (#S : ℤ) = r}, F.obj S.1) :
    (F.cubeComplexXLinearEquiv r).symm f = ∑ S, (F.cubeComplexι S).hom (f S) :=
  (rfl)

/-- The terms of the cube complex of a cube of finitely generated modules are finitely
generated. -/
instance [∀ S, Module.Finite R (F.obj S)] (r : ℤ) : Module.Finite R (F.cubeComplex.X r) :=
  Module.Finite.equiv (F.cubeComplexXLinearEquiv r).symm

/-- The terms of the cube complex of a cube of free modules are free. -/
instance [∀ S, Module.Free R (F.obj S)] (r : ℤ) : Module.Free R (F.cubeComplex.X r) :=
  Module.Free.of_equiv (F.cubeComplexXLinearEquiv r).symm

variable [∀ S, Module.Free R (F.obj S)] [∀ S, Module.Finite R (F.obj S)]

/-- For a cube of finite free modules, the rank of the term of degree `r` of the cube complex is
the sum of the ranks of the vertices of height `r`. -/
theorem finrank_cubeComplex_X [StrongRankCondition R] (r : ℤ) :
    finrank R (F.cubeComplex.X r) = ∑ S : Finset ι with (#S : ℤ) = r, finrank R (F.obj S) := by
  rw [(F.cubeComplexXLinearEquiv r).finrank_eq, Module.finrank_pi_fintype]
  exact (Finset.sum_subtype {S : Finset ι | (#S : ℤ) = r} (fun S ↦ by simp)
    (fun S ↦ finrank R (F.obj S))).symm

/-- **The Euler characteristic of a cube complex.** For a cube of finite free modules, the Euler
characteristic of the cube complex is the sum of the ranks of the vertices `F(S)`, each with the
sign `(-1) ^ #S`. -/
theorem eulerChar_cubeComplex [StrongRankCondition R] :
    F.cubeComplex.eulerChar = ∑ S : Finset ι, ((#S : ℤ).negOnePow : ℤ) * finrank R (F.obj S) := by
  rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _
    (Finset.Icc (0 : ℤ) (Fintype.card ι)) (HomologicalComplex.finrankSupport_X_subset_Icc _ _ _)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := Finset.Icc (0 : ℤ) (Fintype.card ι))
    (g := fun S ↦ (#S : ℤ))
    (fun S _ ↦ Finset.mem_Icc.2 ⟨by positivity, by exact_mod_cast card_le_univ S⟩)]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  simp only [ComplexShape.eulerCharSignsUpInt_χ]
  rw [finrank_cubeComplex_X, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS ↦ ?_
  rw [(Finset.mem_filter.1 hS).2]

/-- **Euler–Poincaré for cubes.** Over a Noetherian ring with the rank-nullity property, such as
`ℤ` or a field, the Euler characteristic of the cohomology of the cube complex of a cube of finite
free modules is the sum of the ranks of the vertices `F(S)`, each with the sign `(-1) ^ #S`. Over
`ℤ` the rank of a cohomology group is the rank of its free part, so torsion does not
contribute. -/
theorem homologyEulerChar_cubeComplex [IsNoetherianRing R] [HasRankNullity.{v} R] :
    F.cubeComplex.homologyEulerChar =
      ∑ S : Finset ι, ((#S : ℤ).negOnePow : ℤ) * finrank R (F.obj S) := by
  rw [← F.eulerChar_cubeComplex,
    CochainComplex.eulerChar_eq_homologyEulerChar _ inferInstance 0 (Fintype.card ι)]

end CategoryTheory.Functor
