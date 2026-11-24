/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Center
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel

/-!
# The scalar subgroup of the general linear group

The scalar matrices `t ↦ t • 1` form a homomorphism `𝔾ₘ → GLₙ` of affine groups. This file
records it as a morphism of coordinate Hopf algebras `k[GLₙ] ⟶ k[T, T⁻¹]`, recovered from its
natural action on points. Its kernel cuts out the scheme-theoretic image of `𝔾ₘ`, the scalar
subgroup of `GLₙ`: a copy of `𝔾ₘ` for `0 < n`, trivial for `n = 0`.

Over a field the scalar subgroup is the center: a coordinate function lies in
`TauCeti.CommHopfAlgCat.centerDefiningIdeal` exactly when it vanishes on scalar matrices. One
inclusion is centrality of scalar points, read at the universal point of `𝔾ₘ`; the other is that
the universally central quotient point of the center is a scalar point
(`TauCeti.GeneralLinear.mem_centerPointsSubgroup_iff_exists_scalarTorusPoints`).

## Main declarations

* `TauCeti.GeneralLinear.scalarTorusCoordinateMap`: the scalar homomorphism `𝔾ₘ → GLₙ` on
  coordinate rings.
* `TauCeti.GeneralLinear.mapPointsFunctor_scalarTorusCoordinateMap_app`: on points it is
  `TauCeti.GeneralLinear.scalarTorusPoints`.
* `TauCeti.GeneralLinear.mem_centerDefiningIdeal_iff`: the center ideal of `GLₙ` is the kernel of
  the scalar homomorphism, so the center is the scalar subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 2.4 and §21.
-/
public section

open CategoryTheory WithConv
open scoped LaurentPolynomial

namespace TauCeti.GeneralLinear

universe u

variable {R : Type u} [CommRing R] (n : ℕ)

/-- The scalar-matrix map `𝔾ₘ → GLₙ` on points, as a natural transformation of group-valued
functors of points. -/
noncomputable def scalarTorusPointsMap :
    HopfAlgebra.pointsFunctor (R := R) (H := R[T;T⁻¹]) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R n) where
  app A := GrpCat.ofHom (scalarTorusPoints n (A := A))
  naturality _ _ φ := by
    ext f
    exact (mapValue_scalarTorusPoints n φ.hom f).symm

/-- The components of `scalarTorusPointsMap` are the scalar-matrix maps. -/
@[simp]
theorem scalarTorusPointsMap_app_apply (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := R[T;T⁻¹]) A) :
    (scalarTorusPointsMap n).app A f = scalarTorusPoints n f := by
  rw [scalarTorusPointsMap]
  rfl

/-- **The scalar homomorphism `𝔾ₘ → GLₙ`** on coordinate rings, `k[GLₙ] ⟶ k[T, T⁻¹]`,
recovered from its natural action on points. Its direction is opposite to that of the group
homomorphism. -/
noncomputable def scalarTorusCoordinateMap :
    coordinateHopfAlgebra R n ⟶ _root_.CommHopfAlgCat.of R R[T;T⁻¹] :=
  CommHopfAlgCat.homOfPointsMap (H := _root_.CommHopfAlgCat.of R R[T;T⁻¹])
    (K := coordinateHopfAlgebra R n) (scalarTorusPointsMap n)

/-- On points with values in a commutative `R`-algebra `A` in the universe of `R`, precomposition
with `scalarTorusCoordinateMap` is the scalar-matrix map. -/
@[simp]
theorem mapPointsFunctor_scalarTorusCoordinateMap_app (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points (R := R) (H := R[T;T⁻¹]) A) :
    (CommHopfAlgCat.Hom.mapPointsFunctor (scalarTorusCoordinateMap (R := R) n)).app A f =
      scalarTorusPoints n f := by
  rw [scalarTorusCoordinateMap, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap,
    scalarTorusPointsMap_app_apply]

/-- Precomposing a point of `𝔾ₘ` with `scalarTorusCoordinateMap` gives its scalar matrix. -/
theorem toConv_comp_scalarTorusCoordinateMap {A : Type u} [CommRing A] [Algebra R A]
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    toConv (f.ofConv.comp ((scalarTorusCoordinateMap (R := R) n).hom :
        coordinateHopfAlgebra R n →ₐ[R] R[T;T⁻¹])) =
      scalarTorusPoints n f := by
  have h := CommHopfAlgCat.Hom.mapPointsFunctor_app_apply.{u, u}
    (scalarTorusCoordinateMap (R := R) n) (CommAlgCat.of R A) f
  rw [mapPointsFunctor_scalarTorusCoordinateMap_app] at h
  exact h.symm

section Field

variable (k : Type u) [Field k]

/-- Scalar matrices are central: a coordinate function in the center ideal vanishes on scalar
matrices. -/
private theorem centerDefiningIdeal_le_ker {x : coordinateHopfAlgebra k n}
    (hx : x ∈ CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) :
    (scalarTorusCoordinateMap (R := k) n).hom x = 0 := by
  let p : WithConv (k[T;T⁻¹] →ₐ[k] k[T;T⁻¹]) := toConv (AlgHom.id k k[T;T⁻¹])
  have hp := scalarTorusPoints_mem_centerPointsSubgroup n p
  rw [← toConv_comp_scalarTorusCoordinateMap, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    at hp
  exact hp x hx

/-- The center of `GLₙ` consists of scalars: a coordinate function vanishing on scalar matrices
lies in the center ideal. -/
private theorem mem_centerDefiningIdeal_of_ker {x : coordinateHopfAlgebra k n}
    (hx : (scalarTorusCoordinateMap (R := k) n).hom x = 0) :
    x ∈ CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) := by
  let I := CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)
  let A : CommAlgCat.{u} k := CommAlgCat.of k (coordinateHopfAlgebra k n ⧸ I.toIdeal)
  let q : WithConv (coordinateHopfAlgebra k n →ₐ[k] A) :=
    toConv (Ideal.Quotient.mkₐ k I.toIdeal)
  have hq : q ∈ CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro y hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (HopfIdeal.mem_toIdeal.mpr hy)
  obtain ⟨f, hf⟩ := (mem_centerPointsSubgroup_iff_exists_scalarTorusPoints n A q).mp hq
  rw [← toConv_comp_scalarTorusCoordinateMap] at hf
  have hqx : q.ofConv x = 0 := by
    rw [← hf, ofConv_toConv, AlgHom.comp_apply]
    exact (congrArg f.ofConv hx).trans (map_zero _)
  exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hqx)

/-- **The center of `GLₙ` is its scalar subgroup**: a coordinate function lies in the center
ideal exactly when it vanishes on scalar matrices. -/
theorem mem_centerDefiningIdeal_iff {x : coordinateHopfAlgebra k n} :
    x ∈ CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) ↔
      (scalarTorusCoordinateMap (R := k) n).hom x = 0 :=
  ⟨centerDefiningIdeal_le_ker n k, mem_centerDefiningIdeal_of_ker n k⟩

end Field

end TauCeti.GeneralLinear
