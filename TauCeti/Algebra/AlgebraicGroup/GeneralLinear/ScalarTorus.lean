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
natural action on points, and its kernel as the Hopf ideal cutting out the scalar subgroup of
`GLₙ`, the scheme-theoretic image of `𝔾ₘ`. For `0 < n` this image is a copy of `𝔾ₘ`; for `n = 0`
it is trivial.

Over a field the scalar subgroup is the center: its Hopf ideal is
`TauCeti.CommHopfAlgCat.centerDefiningIdeal`. One inequality is centrality of scalar points, read
at the universal point of `𝔾ₘ`; the other is that the universally central quotient point of the
center is a scalar point
(`TauCeti.GeneralLinear.mem_centerPointsSubgroup_iff_exists_scalarTorusPoints`).

## Main declarations

* `TauCeti.GeneralLinear.scalarTorusCoordinateMap`: the scalar homomorphism `𝔾ₘ → GLₙ` on
  coordinate rings.
* `TauCeti.GeneralLinear.mapPointsFunctor_scalarTorusCoordinateMap_app`: on points it is
  `TauCeti.GeneralLinear.scalarTorusPoints`.
* `TauCeti.GeneralLinear.scalarHopfIdeal`: the Hopf ideal of the scalar subgroup of `GLₙ`, a copy
  of `𝔾ₘ` when `0 < n`.
* `TauCeti.GeneralLinear.scalarHopfIdeal_eq_centerDefiningIdeal`: the scalar subgroup is the
  center.

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
  rw [scalarTorusCoordinateMap, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap]
  rfl

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

/-- **The scalar subgroup of `GLₙ`**, as the Hopf ideal of `k[GLₙ]` cutting it out: the kernel of
the scalar homomorphism `scalarTorusCoordinateMap`, which cuts out its scheme-theoretic image. For
`0 < n` this is a copy of `𝔾ₘ`; for `n = 0` it is trivial. -/
noncomputable def scalarHopfIdeal : HopfIdeal k (coordinateHopfAlgebra k n) :=
  HopfIdeal.ker (scalarTorusCoordinateMap (R := k) n).hom

/-- A coordinate function lies in the scalar ideal exactly when it vanishes on scalar matrices. -/
@[simp]
theorem mem_scalarHopfIdeal {x : coordinateHopfAlgebra k n} :
    x ∈ scalarHopfIdeal n k ↔ (scalarTorusCoordinateMap (R := k) n).hom x = 0 :=
  HopfIdeal.mem_ker _

/-- The underlying ideal of the scalar subgroup is the kernel of the scalar homomorphism. -/
theorem scalarHopfIdeal_toIdeal :
    (scalarHopfIdeal n k).toIdeal =
      RingHom.ker (scalarTorusCoordinateMap (R := k) n).hom.toAlgHom.toRingHom :=
  HopfIdeal.ker_toIdeal _

/-- **The scalar subgroup is central**: the center ideal lies below the scalar ideal. This is
centrality of the universal scalar point, the scalar homomorphism itself. -/
theorem centerDefiningIdeal_le_scalarHopfIdeal :
    CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) ≤ scalarHopfIdeal n k := by
  intro x hx
  let p : WithConv (k[T;T⁻¹] →ₐ[k] k[T;T⁻¹]) := toConv (AlgHom.id k k[T;T⁻¹])
  have hp := scalarTorusPoints_mem_centerPointsSubgroup n p
  rw [← toConv_comp_scalarTorusCoordinateMap, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    at hp
  exact (mem_scalarHopfIdeal n k).mpr (hp x hx)

/-- **The center of `GLₙ` consists of scalars**: the scalar ideal lies below the center ideal.
The quotient point of the center is universally central, hence a scalar point, so it factors
through the scalar homomorphism and kills its kernel. -/
theorem scalarHopfIdeal_le_centerDefiningIdeal :
    scalarHopfIdeal n k ≤ CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) := by
  intro x hx
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
    exact (congrArg f.ofConv ((mem_scalarHopfIdeal n k).mp hx)).trans (map_zero _)
  exact HopfIdeal.mem_toIdeal.mp (Ideal.Quotient.eq_zero_iff_mem.mp hqx)

/-- **The scalar subgroup of `GLₙ` is its center.** -/
theorem scalarHopfIdeal_eq_centerDefiningIdeal :
    scalarHopfIdeal n k = CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n) :=
  le_antisymm (scalarHopfIdeal_le_centerDefiningIdeal n k)
    (centerDefiningIdeal_le_scalarHopfIdeal n k)

end Field

end TauCeti.GeneralLinear
