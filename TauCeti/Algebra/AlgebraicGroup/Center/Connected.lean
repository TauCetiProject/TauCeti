/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Reduced
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.RingTheory.TensorProduct.Reduced
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.RationalPoint
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The connected center of an affine group

Over an algebraically closed field `k`, the **connected center** `Z(G)°_red` of a finite-type
affine group `G` is the identity component of its reduced center. It is cut out by
`FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal`, and it is the greatest smooth connected
central closed subgroup of `G`: every central closed subgroup with reduced, geometrically
connected coordinate algebra lies in it. This universal property makes the connected center
characteristic, so it is preserved by every automorphism of `G`.

For a closed subgroup `N` of `G`, `HopfIdeal.connectedCenter` cuts out the connected center
`Z(N)°_red` of `N` as a closed subgroup of `G`. When `G` is reduced and `N` is normal in `G`, the
connected center of `N` is normal in `G` as well, since it is characteristic in `N` and normality
of a reduced closed subgroup can be tested on rational points. Applied to the unipotent radical
`R_u(G)`, which is normal by `FiniteTypeCommHopfAlgCat.isNormal_unipotentRadicalDefiningIdeal`,
this gives a smooth connected normal subgroup of `G` that is central in `R_u(G)`. The connected
center of `G` is trivial exactly when every smooth connected central closed subgroup is
trivial.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal`: the Hopf ideal cutting out
  the connected center.
* `TauCeti.FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal_le_of_isCentral`: the connected
  center contains every smooth connected central closed subgroup.
* `TauCeti.FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal_eq_augmentation_iff`: the
  connected center is trivial exactly when every such subgroup is trivial.
* `TauCeti.FiniteTypeCommHopfAlgCat.comapOfSurjective_connectedCenterDefiningIdeal`: isomorphisms
  of affine groups identify their connected centers.
* `TauCeti.HopfIdeal.connectedCenter`: the connected center of a closed subgroup, as a closed
  subgroup of the ambient group.
* `TauCeti.HopfIdeal.IsNormal.connectedCenter`: the connected center of a normal closed subgroup
  of a reduced affine group is normal.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.k (centers), Proposition 2.37 (identity
  components), and the proof of Theorem 16.33, where the center of the unipotent radical is used.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace FiniteTypeCommHopfAlgCat

variable (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- The Hopf ideal cutting out the connected center `Z(G)°_red` of a finite-type affine group
over an algebraically closed field: the identity component of the reduced center. -/
def connectedCenterDefiningIdeal : HopfIdeal k G :=
  (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj).identityComponent

/-- The connected center is the identity component of the reduced center, both viewed as closed
subgroups of `G`. -/
theorem connectedCenterDefiningIdeal_eq_identityComponent :
    connectedCenterDefiningIdeal G =
      (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj).identityComponent :=
  (rfl)

/-- The connected center is a closed subgroup of the reduced center. The inequality is reversed
on defining ideals. -/
theorem reducedCenterDefiningIdeal_le_connectedCenterDefiningIdeal :
    CommHopfAlgCat.reducedCenterDefiningIdeal G.obj ≤ connectedCenterDefiningIdeal G :=
  HopfIdeal.le_identityComponent _

/-- The connected center is a closed subgroup of the center. The inequality is reversed on
defining ideals. -/
theorem centerDefiningIdeal_le_connectedCenterDefiningIdeal :
    CommHopfAlgCat.centerDefiningIdeal G.obj ≤ connectedCenterDefiningIdeal G :=
  (CommHopfAlgCat.centerDefiningIdeal_le_reducedCenterDefiningIdeal G.obj).trans
    (reducedCenterDefiningIdeal_le_connectedCenterDefiningIdeal G)

/-- The connected center is central. -/
theorem isCentral_connectedCenterDefiningIdeal : (connectedCenterDefiningIdeal G).IsCentral :=
  (CommHopfAlgCat.isCentral_centerDefiningIdeal G.obj).mono
    (centerDefiningIdeal_le_connectedCenterDefiningIdeal G)

/-- The connected center is geometrically connected. -/
theorem geometricallyConnected_connectedCenter :
    geometricallyConnectedCommHopfAlgProperty k
      (quotient G (connectedCenterDefiningIdeal G)).obj :=
  HopfIdeal.geometricallyConnected_identityComponent _

/-- The connected center is smooth. -/
theorem smooth_connectedCenter : Algebra.Smooth k (quotient G (connectedCenterDefiningIdeal G)) :=
  let _ : IsReduced (quotient G (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj)) :=
    CommHopfAlgCat.isReduced_quotient_reducedCenterDefiningIdeal G.obj
  let _ : Algebra.Smooth k (quotient G (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj)) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)
  HopfIdeal.smooth_identityComponent _

/-- The coordinate algebra of the connected center is reduced. -/
theorem isReduced_connectedCenter : IsReduced (quotient G (connectedCenterDefiningIdeal G)) :=
  let _ := smooth_connectedCenter G
  isReduced_of_smooth k _

/-- **Maximality of the connected center.** Every central closed subgroup with reduced,
geometrically connected coordinate algebra lies in the connected center. The inequality is
reversed on defining ideals. -/
theorem connectedCenterDefiningIdeal_le_of_isCentral {J : HopfIdeal k G} (hJ : J.IsCentral)
    [IsReduced (quotient G J)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k (quotient G J).obj) :
    connectedCenterDefiningIdeal G ≤ J :=
  HopfIdeal.identityComponent_le_of_le
    (CommHopfAlgCat.reducedCenterDefiningIdeal_le_of_centerDefiningIdeal_le_of_isReduced_quotient
      G.obj J ((CommHopfAlgCat.centerDefiningIdeal_le_iff G.obj J).mpr hJ)) hconn

/-- The connected center is trivial exactly when every central closed subgroup with reduced,
geometrically connected coordinate algebra is trivial. -/
theorem connectedCenterDefiningIdeal_eq_augmentation_iff :
    connectedCenterDefiningIdeal G = HopfIdeal.augmentation k G ↔
      ∀ J : HopfIdeal k G, J.IsCentral → IsReduced (quotient G J) →
        geometricallyConnectedCommHopfAlgProperty k (quotient G J).obj →
          J = HopfIdeal.augmentation k G := by
  refine ⟨fun h J hJ _ hconn ↦ le_antisymm (HopfIdeal.le_augmentation k G J) ?_, fun h ↦ ?_⟩
  · exact h ▸ connectedCenterDefiningIdeal_le_of_isCentral G hJ hconn
  · exact h _ (isCentral_connectedCenterDefiningIdeal G) (isReduced_connectedCenter G)
      (geometricallyConnected_connectedCenter G)

/-- Pulling the connected center of the target back along an isomorphism gives a closed
subgroup containing the connected center of the source; one half of
`comapOfSurjective_connectedCenterDefiningIdeal`. -/
private theorem connectedCenterDefiningIdeal_le_comapOfSurjective
    {K : FiniteTypeCommHopfAlgCat.{u, u} k} (e : G.obj ≅ K.obj) :
    connectedCenterDefiningIdeal G ≤
      (connectedCenterDefiningIdeal K).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 := by
  have he := ConcreteCategory.bijective_of_isIso e.hom
  let i := CommHopfAlgCat.quotientIsoOfComapEq e (connectedCenterDefiningIdeal K) rfl
  let _ : IsReduced (quotient K (connectedCenterDefiningIdeal K)) := isReduced_connectedCenter K
  let _ : IsReduced (quotient G
      ((connectedCenterDefiningIdeal K).comapOfSurjective e.hom.hom he.2)) :=
    isReduced_of_injective i.hom.hom.toAlgHom.toRingHom
      (ConcreteCategory.bijective_of_isIso i.hom).1
  exact connectedCenterDefiningIdeal_le_of_isCentral G
    ((isCentral_connectedCenterDefiningIdeal K).comapOfSurjective_of_bijective _ he.1 he.2)
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso i.symm
      (geometricallyConnected_connectedCenter K))

/-- **The connected center is characteristic.** An isomorphism of affine groups carries the
connected center of the source onto the connected center of the target. -/
@[simp]
theorem comapOfSurjective_connectedCenterDefiningIdeal {K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (e : G.obj ≅ K.obj) :
    (connectedCenterDefiningIdeal K).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 = connectedCenterDefiningIdeal G := by
  refine le_antisymm (fun x hx ↦ ?_) (connectedCenterDefiningIdeal_le_comapOfSurjective G e)
  have hxK : e.hom.hom x ∈ connectedCenterDefiningIdeal K := HopfIdeal.mem_comapOfSurjective.mp hx
  have hxG : e.inv.hom (e.hom.hom x) ∈ connectedCenterDefiningIdeal G :=
    HopfIdeal.mem_comapOfSurjective.mp
      (connectedCenterDefiningIdeal_le_comapOfSurjective K e.symm hxK)
  simpa using hxG

end FiniteTypeCommHopfAlgCat

namespace HopfIdeal

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The Hopf ideal cutting out the connected center `Z(N)°_red` of the closed subgroup `N` cut
out by `I`, viewed as a closed subgroup of the ambient group. -/
def connectedCenter (I : HopfIdeal k H) : HopfIdeal k H :=
  (FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal
    (FiniteTypeCommHopfAlgCat.quotient H I)).comapOfSurjective
      (CommHopfAlgCat.mkQuotient H.obj I).hom (CommHopfAlgCat.mkQuotient_surjective _ _)

/-- A function vanishes on `Z(N)°_red` exactly when its restriction to `N` vanishes on the
connected center of `N`. -/
@[simp]
theorem mem_connectedCenter (I : HopfIdeal k H) (x : H) :
    x ∈ I.connectedCenter ↔
      (CommHopfAlgCat.mkQuotient H.obj I).hom x ∈
        FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal
          (FiniteTypeCommHopfAlgCat.quotient H I) := by
  rw [connectedCenter, mem_comapOfSurjective]

/-- The connected center of a closed subgroup is contained in that subgroup. The inequality is
reversed on defining ideals. -/
theorem le_connectedCenter (I : HopfIdeal k H) : I ≤ I.connectedCenter := by
  intro x hx
  rw [mem_connectedCenter, (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr hx]
  exact zero_mem _

/-- Computing the coordinate algebra of `Z(N)°_red` inside `G` or inside `N` gives isomorphic
commutative Hopf algebras. -/
def connectedCenterQuotientIso (I : HopfIdeal k H) :
    (FiniteTypeCommHopfAlgCat.quotient H I.connectedCenter).obj ≅
      (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.quotient H I)
        (FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal
          (FiniteTypeCommHopfAlgCat.quotient H I))).obj :=
  (CommHopfAlgCat.mkQuotient H.obj I).quotientIsoOfSurjective
    (CommHopfAlgCat.mkQuotient_surjective _ _)
    (FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal (FiniteTypeCommHopfAlgCat.quotient H I))

/-- The comparison of the two coordinate algebras of `Z(N)°_red` respects restriction of
functions from the ambient group. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_connectedCenterQuotientIso_hom (I : HopfIdeal k H) :
    CommHopfAlgCat.mkQuotient H.obj I.connectedCenter ≫ I.connectedCenterQuotientIso.hom =
      CommHopfAlgCat.mkQuotient H.obj I ≫
        CommHopfAlgCat.mkQuotient (CommHopfAlgCat.quotient H.obj I)
          (FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal
            (FiniteTypeCommHopfAlgCat.quotient H I)) :=
  (CommHopfAlgCat.mkQuotient H.obj I).mkQuotient_comp_quotientIsoOfSurjective_hom _ _

/-- The connected center of a closed subgroup is geometrically connected. -/
theorem geometricallyConnected_connectedCenter (I : HopfIdeal k H) :
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I.connectedCenter).obj :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso I.connectedCenterQuotientIso.symm
    (FiniteTypeCommHopfAlgCat.geometricallyConnected_connectedCenter _)

/-- The connected center of a closed subgroup is smooth. -/
theorem smooth_connectedCenter (I : HopfIdeal k H) :
    Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I.connectedCenter) :=
  let _ := FiniteTypeCommHopfAlgCat.smooth_connectedCenter (FiniteTypeCommHopfAlgCat.quotient H I)
  (smoothCommHopfAlgProperty_iff _).mp <|
    (smoothCommHopfAlgProperty k).prop_of_iso I.connectedCenterQuotientIso.symm
      ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)

/-- **The connected center of a normal subgroup is normal.** Over an algebraically closed field,
the connected center `Z(N)°_red` of a normal closed subgroup `N` of a reduced finite-type affine
group `G` is normal in `G`. The subgroup `N` itself need not be reduced. -/
theorem IsNormal.connectedCenter {I : HopfIdeal k H} (hI : I.IsNormal) [IsReduced H] :
    I.connectedCenter.IsNormal := by
  let _ := I.smooth_connectedCenter
  let N := FiniteTypeCommHopfAlgCat.quotient H I
  -- `comapOfSurjective_of_forall_iso` asks for reducedness of the unfolded pullback ideal.
  let _ : IsReduced (H ⧸
      ((FiniteTypeCommHopfAlgCat.connectedCenterDefiningIdeal N).comapOfSurjective
        (CommHopfAlgCat.mkQuotient H.obj I).hom
        (CommHopfAlgCat.mkQuotient_surjective _ _)).toIdeal) :=
    isReduced_of_smooth k (H ⧸ I.connectedCenter.toIdeal)
  exact hI.comapOfSurjective_of_forall_iso _
    (FiniteTypeCommHopfAlgCat.comapOfSurjective_connectedCenterDefiningIdeal N (K := N))

end HopfIdeal

end

end TauCeti
