/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.FiniteEtale
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.Ideal.Quotient.Finite

/-!
# Centers under isogenies in characteristic zero

For an isogeny from a geometrically connected affine group in characteristic zero to a
group with finite center, the inverse image of the target center is the source center.
Indeed, that inverse image is a finite normal closed subgroup. Cartier's theorem makes it
geometrically reduced, and a finite geometrically reduced normal subgroup of a connected
smooth affine group is central.

Consequently, if the kernel of the isogeny is the entire source center, the target is
centerless. This applies to the represented center quotient of a semisimple group.
All centers, kernels, and inverse images here are scheme-theoretic.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 21.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] [CharZero k]
  {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k K]
  [Module.Finite k (centerCoordinateHopfAlgebra H)]

/-- In characteristic zero, an isogeny with geometrically connected source and finite
target center pulls the target center back to the full source center. The coordinate arrow
`f : H ⟶ K` represents a homomorphism from `Spec K` to `Spec H`. -/
theorem IsIsogeny.map_centerDefiningIdeal_eq {f : H ⟶ K} (hf : IsIsogeny f)
    (hK : geometricallyConnectedCommHopfAlgProperty k K) :
    (centerDefiningIdeal H).map f.hom = centerDefiningIdeal K := by
  let J := (centerDefiningIdeal H).map f.hom
  have hnormal : J.IsNormal := (isCentral_centerDefiningIdeal H).isNormal.map f.hom
  have hJ : J.toIdeal = Ideal.map (f.hom.toAlgHom : H →+* K)
      (centerDefiningIdeal H).toIdeal := HopfIdeal.map_toIdeal _ _
  let _ := f.hom.toAlgHom.toAlgebra
  let _ : IsScalarTower k H K :=
    IsScalarTower.of_algebraMap_eq' f.hom.toAlgHom.comp_algebraMap.symm
  let _ : Module.Finite H K := hf.finite
  let _ : Module.Finite k (quotient K J) :=
    finite_quotient_of_map_algebraMap_le (A := k) (R := H) (B := K)
      (I := (centerDefiningIdeal H).toIdeal) (J := J.toIdeal)
      (by rw [hJ]; exact le_rfl) inferInstance
  let _ : Algebra.Smooth k K :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k K)
  let _ : Algebra.IsGeometricallyReduced k K := isGeometricallyReduced_of_smooth k K
  let _ : Algebra.Smooth k (quotient K J) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_charZero k (quotient K J))
  let _ : Algebra.IsGeometricallyReduced k (quotient K J) :=
    isGeometricallyReduced_of_smooth k (quotient K J)
  have hcentral : J.IsCentral :=
    hnormal.isCentral_of_finite_of_isGeometricallyReduced (H := FiniteTypeCommHopfAlgCat.of k K) hK
  exact le_antisymm
    (HopfIdeal.map_le_iff.mpr fun _ hx ↦
      HopfIdeal.mem_comap.mp (centerDefiningIdeal_le_comap f hf.injective hx))
    ((centerDefiningIdeal_le_iff K J).mpr hcentral)

/-- An isogeny in characteristic zero from a geometrically connected group, with kernel its
full center and target of finite center, has centerless target. -/
theorem IsIsogeny.centerDefiningIdeal_eq_augmentation_of_kernel_eq_center
    {f : H ⟶ K} (hf : IsIsogeny f)
    (hK : geometricallyConnectedCommHopfAlgProperty k K)
    (hker : kernelHopfIdeal f = centerDefiningIdeal K) :
    centerDefiningIdeal H = HopfIdeal.augmentation k H := by
  let _ := f.hom.toAlgHom.toAlgebra
  let _ : Module.FaithfullyFlat H K := hf.faithfullyFlat
  have hmap : (centerDefiningIdeal H).map f.hom =
      (HopfIdeal.augmentation k H).map f.hom := by
    rw [hf.map_centerDefiningIdeal_eq hK, ← kernelHopfIdeal_def, hker]
  have hI : (centerDefiningIdeal H).toIdeal = (HopfIdeal.augmentation k H).toIdeal := by
    apply Ideal.map_injective_of_faithfullyFlat (B := K)
    have he := congrArg HopfIdeal.toIdeal hmap
    rw [HopfIdeal.map_toIdeal, HopfIdeal.map_toIdeal] at he
    exact he
  exact HopfIdeal.ext fun x ↦ SetLike.ext_iff.mp hI x

end TauCeti.CommHopfAlgCat
