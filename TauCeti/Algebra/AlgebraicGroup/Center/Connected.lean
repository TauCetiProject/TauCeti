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
import TauCeti.Algebra.Coalgebra.Cocommutative

/-!
# The reduced connected center of an affine group

Over an algebraically closed field `k`, the **reduced connected center** `Z(G)°_red` of a
finite-type affine group `G` is the identity component of its reduced center. It is cut out by
`FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal`, and it is the greatest smooth
connected central closed subgroup of `G`: every central closed subgroup with reduced,
geometrically connected coordinate algebra lies in it. This universal property makes the reduced
connected center characteristic, so it is preserved by every automorphism of `G`. It can differ
from the identity component of the scheme-theoretic center: in characteristic `p`, the center
`μ_p` of `SL_p` is connected, while its reduced connected center is trivial.

For a closed subgroup `N` of `G`, `HopfIdeal.reducedConnectedCenter` cuts out the reduced
connected center `Z(N)°_red` of `N` as a closed subgroup of `G`. When `G` is reduced and `N` is
normal in `G`, the reduced connected center of `N` is normal in `G` as well: it is characteristic
in `N`, it is reduced, and normality of a reduced closed subgroup of a reduced ambient group can
be tested on rational points. No reducedness of `N` itself is needed. Applied to the unipotent
radical `R_u(G)` of a reduced `G`, which is normal by
`FiniteTypeCommHopfAlgCat.isNormal_unipotentRadicalDefiningIdeal`, this gives a smooth connected
normal subgroup of `G` that is central in `R_u(G)`. The reduced connected center of `G` is
trivial exactly when every smooth connected central closed subgroup is trivial.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal`: the Hopf ideal cutting
  out the reduced connected center.
* `TauCeti.FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal_le_of_isCentral`: the
  reduced connected center contains every smooth connected central closed subgroup.
* `TauCeti.FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal_eq_augmentation_iff`: the
  reduced connected center is trivial exactly when every such subgroup is trivial.
* `TauCeti.FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal_eq_comapOfSurjective`:
  comparison with the identity component of the iterated quotient model
  `CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra` of the reduced center.
* `TauCeti.FiniteTypeCommHopfAlgCat.comapOfSurjective_reducedConnectedCenterDefiningIdeal`:
  isomorphisms of affine groups identify their reduced connected centers.
* `TauCeti.HopfIdeal.reducedConnectedCenter`: the reduced connected center of a closed subgroup,
  as a closed subgroup of the ambient group.
* `TauCeti.HopfIdeal.isCocomm_reducedConnectedCenter`: the reduced connected center of a closed
  subgroup is commutative.
* `TauCeti.HopfIdeal.IsNormal.reducedConnectedCenter`: the reduced connected center of a normal
  closed subgroup of a reduced affine group is normal.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.k (centers), Proposition 2.37 (identity
  components), and the proof of Theorem 16.33, where the center of the unipotent radical is used.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
* The ambient construction `HopfIdeal.reducedConnectedCenter` and the normality proof
  `HopfIdeal.IsNormal.reducedConnectedCenter` follow `HopfIdeal.identityComponent` and
  `HopfIdeal.IsNormal.identityComponent` in
  `TauCeti/Algebra/AlgebraicGroup/HopfIdeal/IdentityComponent.lean`; both normality proofs apply
  the shared criterion `HopfIdeal.IsNormal.comapOfSurjective_of_forall_iso`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace FiniteTypeCommHopfAlgCat

variable (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- The Hopf ideal cutting out the reduced connected center `Z(G)°_red` of a finite-type affine
group over an algebraically closed field: the identity component of the reduced center. -/
def reducedConnectedCenterDefiningIdeal : HopfIdeal k G :=
  (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj).identityComponent

/-- The reduced connected center is the identity component of the reduced center, both viewed
as closed subgroups of `G`. -/
theorem reducedConnectedCenterDefiningIdeal_eq_identityComponent :
    reducedConnectedCenterDefiningIdeal G =
      (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj).identityComponent :=
  (rfl)

/-- The reduced connected center is a closed subgroup of the reduced center. The inequality is
reversed on defining ideals. -/
theorem reducedCenterDefiningIdeal_le_reducedConnectedCenterDefiningIdeal :
    CommHopfAlgCat.reducedCenterDefiningIdeal G.obj ≤ reducedConnectedCenterDefiningIdeal G :=
  HopfIdeal.le_identityComponent _

/-- The reduced connected center is a closed subgroup of the center. The inequality is reversed
on defining ideals. -/
theorem centerDefiningIdeal_le_reducedConnectedCenterDefiningIdeal :
    CommHopfAlgCat.centerDefiningIdeal G.obj ≤ reducedConnectedCenterDefiningIdeal G :=
  (CommHopfAlgCat.centerDefiningIdeal_le_reducedCenterDefiningIdeal G.obj).trans
    (reducedCenterDefiningIdeal_le_reducedConnectedCenterDefiningIdeal G)

/-- The reduced connected center is central. -/
theorem isCentral_reducedConnectedCenterDefiningIdeal :
    (reducedConnectedCenterDefiningIdeal G).IsCentral :=
  (CommHopfAlgCat.isCentral_centerDefiningIdeal G.obj).mono
    (centerDefiningIdeal_le_reducedConnectedCenterDefiningIdeal G)

/-- The reduced connected center is geometrically connected. -/
theorem geometricallyConnected_reducedConnectedCenter :
    geometricallyConnectedCommHopfAlgProperty k
      (quotient G (reducedConnectedCenterDefiningIdeal G)).obj :=
  HopfIdeal.geometricallyConnected_identityComponent _

/-- The reduced connected center is smooth. -/
theorem smooth_reducedConnectedCenter :
    Algebra.Smooth k (quotient G (reducedConnectedCenterDefiningIdeal G)) :=
  let _ : IsReduced (quotient G (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj)) :=
    CommHopfAlgCat.isReduced_quotient_reducedCenterDefiningIdeal G.obj
  let _ : Algebra.Smooth k (quotient G (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj)) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)
  HopfIdeal.smooth_identityComponent _

/-- The coordinate algebra of the reduced connected center is reduced. -/
theorem isReduced_reducedConnectedCenter :
    IsReduced (quotient G (reducedConnectedCenterDefiningIdeal G)) :=
  let _ := smooth_reducedConnectedCenter G
  isReduced_of_smooth k _

/-- **Maximality of the reduced connected center.** Every central closed subgroup with reduced,
geometrically connected coordinate algebra lies in the reduced connected center. The inequality
is reversed on defining ideals. -/
theorem reducedConnectedCenterDefiningIdeal_le_of_isCentral {J : HopfIdeal k G}
    (hJ : J.IsCentral) [IsReduced (quotient G J)]
    (hconn : geometricallyConnectedCommHopfAlgProperty k (quotient G J).obj) :
    reducedConnectedCenterDefiningIdeal G ≤ J :=
  HopfIdeal.identityComponent_le_of_le
    (CommHopfAlgCat.reducedCenterDefiningIdeal_le_of_centerDefiningIdeal_le_of_isReduced_quotient
      G.obj J ((CommHopfAlgCat.centerDefiningIdeal_le_iff G.obj J).mpr hJ)) hconn

/-- The reduced connected center is trivial exactly when every central closed subgroup with
reduced, geometrically connected coordinate algebra is trivial. -/
theorem reducedConnectedCenterDefiningIdeal_eq_augmentation_iff :
    reducedConnectedCenterDefiningIdeal G = HopfIdeal.augmentation k G ↔
      ∀ J : HopfIdeal k G, J.IsCentral → IsReduced (quotient G J) →
        geometricallyConnectedCommHopfAlgProperty k (quotient G J).obj →
          J = HopfIdeal.augmentation k G := by
  refine ⟨fun h J hJ _ hconn ↦ le_antisymm (HopfIdeal.le_augmentation k G J) ?_, fun h ↦ ?_⟩
  · exact h ▸ reducedConnectedCenterDefiningIdeal_le_of_isCentral G hJ hconn
  · exact h _ (isCentral_reducedConnectedCenterDefiningIdeal G)
      (isReduced_reducedConnectedCenter G) (geometricallyConnected_reducedConnectedCenter G)

/-- The restriction map from `G` to the iterated quotient model
`CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra` of its reduced center is surjective. -/
theorem surjective_mkQuotient_comp_quotientReducedCenterIso_hom :
    Function.Surjective (CommHopfAlgCat.mkQuotient G.obj
      (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj) ≫
        (CommHopfAlgCat.quotientReducedCenterIso G.obj).hom).hom := by
  rw [CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).2.comp (CommHopfAlgCat.mkQuotient_surjective _ _)

/-- The reduced connected center, cut out in `G`, is the pullback of the identity component of
the iterated quotient model `CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra` of the reduced
center. -/
theorem reducedConnectedCenterDefiningIdeal_eq_comapOfSurjective :
    reducedConnectedCenterDefiningIdeal G =
      (HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra G.obj)).comapOfSurjective
          (CommHopfAlgCat.mkQuotient G.obj (CommHopfAlgCat.reducedCenterDefiningIdeal G.obj) ≫
            (CommHopfAlgCat.quotientReducedCenterIso G.obj).hom).hom
          (surjective_mkQuotient_comp_quotientReducedCenterIso_hom G) := by
  ext x
  rw [HopfIdeal.mem_comapOfSurjective, CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
    reducedConnectedCenterDefiningIdeal, HopfIdeal.mem_identityComponent]
  exact (HopfAlgebra.apply_mem_identityComponentHopfIdeal_iff
    (_root_.CommHopfAlgCat.ofIso (CommHopfAlgCat.quotientReducedCenterIso G.obj))).symm

/-- The identity component of the iterated quotient model
`CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra` of the reduced center is trivial exactly
when the reduced connected center of `G` is trivial. -/
theorem identityComponentHopfIdeal_reducedCenterCoordinateHopfAlgebra_eq_augmentation_iff :
    HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra G.obj) =
        HopfIdeal.augmentation k (CommHopfAlgCat.reducedCenterCoordinateHopfAlgebra G.obj) ↔
      reducedConnectedCenterDefiningIdeal G = HopfIdeal.augmentation k G := by
  rw [reducedConnectedCenterDefiningIdeal_eq_comapOfSurjective,
    ← HopfIdeal.comapOfSurjective_augmentation _
      (surjective_mkQuotient_comp_quotientReducedCenterIso_hom G),
    HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff]

/-- Pulling the reduced connected center of the target back along an isomorphism gives a closed
subgroup contained in the reduced connected center of the source: the inclusion of defining
ideals goes the other way. One half of
`comapOfSurjective_reducedConnectedCenterDefiningIdeal`. -/
private theorem reducedConnectedCenterDefiningIdeal_le_comapOfSurjective
    {K : FiniteTypeCommHopfAlgCat.{u, u} k} (e : G.obj ≅ K.obj) :
    reducedConnectedCenterDefiningIdeal G ≤
      (reducedConnectedCenterDefiningIdeal K).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 := by
  have he := ConcreteCategory.bijective_of_isIso e.hom
  let _ : IsReduced (quotient K (reducedConnectedCenterDefiningIdeal K)) :=
    isReduced_reducedConnectedCenter K
  let _ : IsReduced (quotient G
      ((reducedConnectedCenterDefiningIdeal K).comapOfSurjective e.hom.hom he.2)) :=
    (CommHopfAlgCat.Hom.isReduced_quotient_comapOfSurjective_iff e.hom he.2 _).mpr ‹_›
  exact reducedConnectedCenterDefiningIdeal_le_of_isCentral G
    ((isCentral_reducedConnectedCenterDefiningIdeal K).comapOfSurjective_of_bijective _ he.1 he.2)
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      (CommHopfAlgCat.quotientIsoOfIso e _).symm
      (geometricallyConnected_reducedConnectedCenter K))

/-- **The reduced connected center is characteristic.** An isomorphism of affine groups carries
the reduced connected center of the source onto the reduced connected center of the target. -/
@[simp]
theorem comapOfSurjective_reducedConnectedCenterDefiningIdeal
    {K : FiniteTypeCommHopfAlgCat.{u, u} k} (e : G.obj ≅ K.obj) :
    (reducedConnectedCenterDefiningIdeal K).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 = reducedConnectedCenterDefiningIdeal G := by
  refine le_antisymm ?_ (reducedConnectedCenterDefiningIdeal_le_comapOfSurjective G e)
  exact (HopfIdeal.comapOfSurjective_mono _ _
    (reducedConnectedCenterDefiningIdeal_le_comapOfSurjective K e.symm)).trans_eq
      ((reducedConnectedCenterDefiningIdeal G).comapOfSurjective_bialgEquiv_symm_apply
        (_root_.CommHopfAlgCat.ofIso e))

end FiniteTypeCommHopfAlgCat

namespace HopfIdeal

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The Hopf ideal cutting out the reduced connected center `Z(N)°_red` of the closed subgroup
`N` cut out by `I`, viewed as a closed subgroup of the ambient group. -/
def reducedConnectedCenter (I : HopfIdeal k H) : HopfIdeal k H :=
  (FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal
    (FiniteTypeCommHopfAlgCat.quotient H I)).comapOfSurjective
      (CommHopfAlgCat.mkQuotient H.obj I).hom (CommHopfAlgCat.mkQuotient_surjective _ _)

/-- The ambient reduced connected center of `N` is the pullback of the intrinsic one along the
restriction map to `N`. -/
theorem reducedConnectedCenter_eq_comapOfSurjective (I : HopfIdeal k H) :
    I.reducedConnectedCenter =
      (FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal
        (FiniteTypeCommHopfAlgCat.quotient H I)).comapOfSurjective
          (CommHopfAlgCat.mkQuotient H.obj I).hom (CommHopfAlgCat.mkQuotient_surjective _ _) :=
  (rfl)

/-- Restricting the ambient reduced connected center of `N` to `N` gives the intrinsic reduced
connected center of `N`. -/
@[simp]
theorem map_mkQuotient_reducedConnectedCenter (I : HopfIdeal k H) :
    I.reducedConnectedCenter.map (Bialgebra.Quotient.mkBialgHom I.toIdeal) =
      FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal
        (FiniteTypeCommHopfAlgCat.quotient H I) :=
  map_comapOfSurjective _ _ (CommHopfAlgCat.mkQuotient_surjective _ _)

/-- A function vanishes on `Z(N)°_red` exactly when its restriction to `N` vanishes on the
reduced connected center of `N`. -/
@[simp]
theorem mem_reducedConnectedCenter (I : HopfIdeal k H) (x : H) :
    x ∈ I.reducedConnectedCenter ↔
      (CommHopfAlgCat.mkQuotient H.obj I).hom x ∈
        FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal
          (FiniteTypeCommHopfAlgCat.quotient H I) := by
  rw [reducedConnectedCenter, mem_comapOfSurjective]

/-- The reduced connected center of a closed subgroup is contained in that subgroup. The
inequality is reversed on defining ideals. -/
theorem le_reducedConnectedCenter (I : HopfIdeal k H) : I ≤ I.reducedConnectedCenter := by
  rw [← toIdeal_le_toIdeal, reducedConnectedCenter, comapOfSurjective_toIdeal]
  conv_lhs => rw [← CommHopfAlgCat.mkQuotient_ker H.obj I]
  exact Ideal.ker_le_comap _

/-- The ambient reduced connected center of `N` is trivial exactly when the intrinsic reduced
connected center of `N` is trivial. -/
@[simp]
theorem reducedConnectedCenter_eq_augmentation_iff (I : HopfIdeal k H) :
    I.reducedConnectedCenter = augmentation k H ↔
      FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal
          (FiniteTypeCommHopfAlgCat.quotient H I) =
        augmentation k (FiniteTypeCommHopfAlgCat.quotient H I) := by
  rw [reducedConnectedCenter,
    ← comapOfSurjective_augmentation (CommHopfAlgCat.mkQuotient H.obj I).hom
      (CommHopfAlgCat.mkQuotient_surjective _ _),
    comapOfSurjective_eq_comapOfSurjective_iff]

/-- The reduced connected center of a closed subgroup is geometrically connected. -/
theorem geometricallyConnected_reducedConnectedCenter (I : HopfIdeal k H) :
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I.reducedConnectedCenter).obj :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    ((CommHopfAlgCat.mkQuotient H.obj I).quotientIsoOfSurjective
      (CommHopfAlgCat.mkQuotient_surjective _ _) _).symm
    (FiniteTypeCommHopfAlgCat.geometricallyConnected_reducedConnectedCenter _)

/-- The reduced connected center of a closed subgroup is smooth. -/
theorem smooth_reducedConnectedCenter (I : HopfIdeal k H) :
    Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I.reducedConnectedCenter) :=
  let _ := FiniteTypeCommHopfAlgCat.smooth_reducedConnectedCenter
    (FiniteTypeCommHopfAlgCat.quotient H I)
  (smoothCommHopfAlgProperty_iff _).mp <|
    (smoothCommHopfAlgProperty k).prop_of_iso
      ((CommHopfAlgCat.mkQuotient H.obj I).quotientIsoOfSurjective
        (CommHopfAlgCat.mkQuotient_surjective _ _) _).symm
      ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)

/-- The reduced connected center of a closed subgroup is commutative: its coordinate Hopf algebra
is cocommutative. -/
noncomputable instance isCocomm_reducedConnectedCenter (I : HopfIdeal k H) :
    Coalgebra.IsCocomm k (FiniteTypeCommHopfAlgCat.quotient H I.reducedConnectedCenter) :=
  let e := (CommHopfAlgCat.mkQuotient H.obj I).quotientIsoOfSurjective
    (CommHopfAlgCat.mkQuotient_surjective _ _)
    (FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal
      (FiniteTypeCommHopfAlgCat.quotient H I))
  let _ := (FiniteTypeCommHopfAlgCat.isCentral_reducedConnectedCenterDefiningIdeal
    (FiniteTypeCommHopfAlgCat.quotient H I)).isCocomm_quotient
  TauCeti.Coalgebra.IsCocomm.of_surjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2

/-- **The reduced connected center of a normal subgroup is normal.** Over an algebraically
closed field, the reduced connected center `Z(N)°_red` of a normal closed subgroup `N` of a
reduced finite-type affine group `G` is normal in `G`. The subgroup `N` itself need not be
reduced. -/
theorem IsNormal.reducedConnectedCenter {I : HopfIdeal k H} (hI : I.IsNormal) [IsReduced H] :
    I.reducedConnectedCenter.IsNormal := by
  let N := FiniteTypeCommHopfAlgCat.quotient H I
  let _ := FiniteTypeCommHopfAlgCat.isReduced_reducedConnectedCenter N
  let _ := (CommHopfAlgCat.Hom.isReduced_quotient_comapOfSurjective_iff
    (CommHopfAlgCat.mkQuotient H.obj I) (CommHopfAlgCat.mkQuotient_surjective _ _)
    (FiniteTypeCommHopfAlgCat.reducedConnectedCenterDefiningIdeal N)).mpr ‹_›
  exact hI.comapOfSurjective_of_forall_iso _
    (FiniteTypeCommHopfAlgCat.comapOfSurjective_reducedConnectedCenterDefiningIdeal N (K := N))

end HopfIdeal

end

end TauCeti
