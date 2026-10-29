/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Coordinate
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
import TauCeti.Algebra.AlgebraicGroup.Representation.FiniteOrder
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Unipotent groups in characteristic zero are connected

Over an algebraically closed field of characteristic zero, a finite-type affine group whose
rational points are all unipotent is connected. Its component group is finite and constant.
The image of each rational point in that group is both unipotent and of finite order, hence
trivial. Every component contains a rational point, so there is only one component.

It follows over any characteristic-zero field that a smooth unipotent affine group is
geometrically connected. This supplies the connectedness condition when applying the
unipotent radical's maximality to a smooth normal unipotent subgroup. No ambient connectedness
or commutativity is required. The characteristic assumption is essential: the constant group
of order `p` in characteristic `p` is unipotent and disconnected.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 14, unipotent groups in characteristic zero.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §8.
-/

public section

open WithConv

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

/-- Over an algebraically closed field of characteristic zero, a finite-type affine group
whose rational points are all unipotent is connected. Reducedness is not needed. -/
theorem connectedSpace_of_forall_isUnipotentPoint (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hH : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint g) :
    ConnectedSpace (PrimeSpectrum H) := by
  let C := ConnectedComponents (PrimeSpectrum H)
  let e := ConstantGroup.pointsMulEquiv k C
  have hcomponent (g : WithConv (H →ₐ[k] k)) : rationalComponentMap H g = 1 := by
    let f := componentCoordinateBialgHom H
    let q := BialgHom.mapDomain f g
    have hq : HopfAlgebra.IsUnipotentPoint q := (hH g).mapDomain f
    have : Finite (WithConv (ConstantGroup.coordinateRing k C →ₐ[k] k)) :=
      Finite.of_injective e.symm e.symm.injective
    have hqone : q = 1 := hq.eq_one_of_isOfFinOrder (isOfFinOrder_of_finite q)
    apply e.injective
    rw [map_one]
    calc
      e (rationalComponentMap H g) = q := by
        apply ofConv_injective
        rw [ConstantGroup.pointsMulEquiv_apply, ofConv_toConv]
        dsimp only [q]
        rw [BialgHom.mapDomain_apply, componentCoordinateBialgHom_toAlgHom]
        exact (eval_componentCoordinateMap H g).symm
      _ = 1 := hqone
  have hC (c : C) : c = 1 := by
    obtain ⟨g, rfl⟩ := rationalComponentMap_surjective H c
    exact hcomponent g
  apply connectedSpace_iff_connectedComponent.mpr
  refine ⟨Bialgebra.augmentationPoint k H, Set.eq_univ_of_forall fun x ↦ ?_⟩
  apply ConnectedComponents.coe_eq_coe'.mp
  exact (hC x).trans (rationalKernelPoint_one_component H).symm

end FiniteTypeCommHopfAlgCat

namespace smoothUnipotentCommHopfAlgProperty

variable {k : Type u} [Field k] [CharZero k]

/-- Every smooth unipotent affine group of finite type over a characteristic-zero field is
geometrically connected. -/
theorem geometricallyConnected {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    (hH : smoothUnipotentCommHopfAlgProperty k H) :
    geometricallyConnectedCommHopfAlgProperty k H.obj := by
  let K := AlgebraicClosure k
  let G := FiniteTypeCommHopfAlgCat.baseChange (K := K) H
  have hG : smoothUnipotentCommHopfAlgProperty K G := hH.baseChange H
  have hG' := (smoothUnipotentCommHopfAlgProperty_iff K G).mp hG
  let _ : Algebra.Smooth K G := hG'.1
  let _ : IsReduced G := isReduced_of_smooth K G
  have hgeom : geometricallyUnipotentPointsCommHopfAlgProperty K G.obj :=
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff K G.obj).mpr hG'.2
  have hconn : ConnectedSpace (PrimeSpectrum G) :=
    G.connectedSpace_of_forall_isUnipotentPoint fun g ↦
      geometricallyUnipotentPointsCommHopfAlgProperty.isUnipotentPoint hgeom g
  exact (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange
    k K H.obj).mpr hconn

end smoothUnipotentCommHopfAlgProperty

end

end TauCeti
