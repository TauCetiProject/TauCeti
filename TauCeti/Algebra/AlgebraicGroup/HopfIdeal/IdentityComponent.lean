/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.Characteristic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.LieAlgebra
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.RationalPoint
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Identity components of closed subgroups

For a closed subgroup `N` of an affine group `G`, `HopfIdeal.identityComponent` cuts out
`N°` as a closed subgroup of `G`. Its quotient coordinate algebra is canonically isomorphic
to the coordinate algebra obtained by taking the identity component inside `N`.

The identity component has the same tangent Lie algebra as `N`. When `G` and `N` are reduced,
normality of `N` implies normality of `N°` in `G`: the identity component is characteristic
in `N`, and normality can be tested on rational points. All statements are over an
algebraically closed field; no connectedness of the ambient group is required.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Chapter 10.
* The construction uses `CommHopfAlgCat.Hom.quotientIsoOfSurjective`; normality uses
  `HopfIdeal.IsNormal.comapOfSurjective_of_forall_iso`.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The defining Hopf ideal of the identity component of a closed subgroup, viewed as a
closed subgroup of the original ambient group. -/
def identityComponent (I : HopfIdeal k H) : HopfIdeal k H :=
  (HopfAlgebra.identityComponentHopfIdeal
    (k := k) (H := FiniteTypeCommHopfAlgCat.quotient H I)).comapOfSurjective
      (CommHopfAlgCat.mkQuotient H.obj I).hom (CommHopfAlgCat.mkQuotient_surjective _ _)

/-- A function vanishes on `N°` exactly when its restriction to `N` vanishes on the identity
component of `N`. -/
@[simp]
theorem mem_identityComponent (I : HopfIdeal k H) (x : H) :
    x ∈ I.identityComponent ↔
      (CommHopfAlgCat.mkQuotient H.obj I).hom x ∈
        HopfAlgebra.identityComponentHopfIdeal
          (k := k) (H := FiniteTypeCommHopfAlgCat.quotient H I) :=
  by rw [identityComponent, mem_comapOfSurjective]

/-- The identity component of a closed subgroup is contained in that subgroup.
The inequality is reversed on defining ideals. -/
theorem le_identityComponent (I : HopfIdeal k H) : I ≤ I.identityComponent := by
  intro x hx
  rw [mem_identityComponent, (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr hx]
  exact zero_mem _

/-- A connected closed subgroup of a closed subgroup `N` is contained in the identity
component of `N`. The inequalities are reversed because they compare defining ideals. -/
theorem identityComponent_le_of_le {I J : HopfIdeal k H} (hIJ : I ≤ J)
    (hJ : geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H J).obj) :
    I.identityComponent ≤ J := by
  let f := CommHopfAlgCat.quotientMapOfLe H.obj hIJ
  let _ : ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H J)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hJ
  intro x hx
  apply (CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj J x).mp
  rw [← CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe H.obj hIJ]
  exact CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected f
    (HopfIdeal.mem_toIdeal.mpr ((mem_identityComponent I x).mp hx))

/-- Computing the coordinate algebra of `N°` inside `G` or inside `N` gives isomorphic
commutative Hopf algebras. -/
def identityComponentQuotientIso (I : HopfIdeal k H) :
    (FiniteTypeCommHopfAlgCat.quotient H I.identityComponent).obj ≅
      (FiniteTypeCommHopfAlgCat.identityComponent
        (FiniteTypeCommHopfAlgCat.quotient H I)).obj :=
  (CommHopfAlgCat.mkQuotient H.obj I).quotientIsoOfSurjective
    (CommHopfAlgCat.mkQuotient_surjective _ _)
    (HopfAlgebra.identityComponentHopfIdeal
      (k := k) (H := FiniteTypeCommHopfAlgCat.quotient H I))

/-- The comparison of the two coordinate algebras of `N°` respects restriction of functions
from the ambient group. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_identityComponentQuotientIso_hom (I : HopfIdeal k H) :
    CommHopfAlgCat.mkQuotient H.obj I.identityComponent ≫
        I.identityComponentQuotientIso.hom =
      CommHopfAlgCat.mkQuotient H.obj I ≫
        CommHopfAlgCat.mkQuotient (CommHopfAlgCat.quotient H.obj I)
          (HopfAlgebra.identityComponentHopfIdeal
            (k := k) (H := FiniteTypeCommHopfAlgCat.quotient H I)) := by
  exact (CommHopfAlgCat.mkQuotient H.obj I).mkQuotient_comp_quotientIsoOfSurjective_hom _ _

/-- The identity component of a closed subgroup is geometrically connected. -/
theorem geometricallyConnected_identityComponent (I : HopfIdeal k H) :
    geometricallyConnectedCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I.identityComponent).obj :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    I.identityComponentQuotientIso.symm
    (FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent _)

/-- The identity component of a smooth closed subgroup is smooth. -/
theorem smooth_identityComponent (I : HopfIdeal k H)
    [Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I)] :
    Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I.identityComponent) :=
  (smoothCommHopfAlgProperty_iff _).mp <|
    (smoothCommHopfAlgProperty k).prop_of_iso I.identityComponentQuotientIso.symm
      ((smoothCommHopfAlgProperty_iff _).mpr
        (FiniteTypeCommHopfAlgCat.smooth_identityComponent _))

/-- The identity component of a reduced normal closed subgroup is normal in a reduced
ambient affine group. -/
theorem IsNormal.identityComponent {I : HopfIdeal k H} (hI : I.IsNormal)
    [IsReduced H] [IsReduced (FiniteTypeCommHopfAlgCat.quotient H I)] :
    I.identityComponent.IsNormal := by
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k _)
  let _ := I.smooth_identityComponent
  let _ : IsReduced (H ⧸ I.identityComponent.toIdeal) := isReduced_of_smooth k _
  let C := HopfAlgebra.identityComponentHopfIdeal
    (k := k) (H := FiniteTypeCommHopfAlgCat.quotient H I)
  let _ : IsReduced (H ⧸ (C.comapOfSurjective
      (CommHopfAlgCat.mkQuotient H.obj I).hom
      (CommHopfAlgCat.mkQuotient_surjective _ _)).toIdeal) :=
    ‹IsReduced (H ⧸ I.identityComponent.toIdeal)›
  exact hI.comapOfSurjective_of_forall_iso C
    HopfAlgebra.comapOfSurjective_identityComponentHopfIdeal

/-- A closed subgroup and its identity component have the same tangent Lie algebra in the
ambient group. -/
@[simp]
theorem lieSubalgebra_identityComponent (I : HopfIdeal k H) :
    I.identityComponent.lieSubalgebra (B := k) = I.lieSubalgebra (B := k) := by
  apply le_antisymm
  · intro d hd
    rw [mem_lieSubalgebra_iff] at hd ⊢
    exact fun x hx ↦ hd x (I.le_identityComponent hx)
  · intro d hd
    obtain ⟨d', hd'⟩ := (I.quotientLieEquiv (B := k)).surjective ⟨d, hd⟩
    have heq : (I.quotientLieEquiv d' :
        Derivation k H (Bialgebra.CounitAlgebra k H k)) = d := congrArg Subtype.val hd'
    rw [← heq]
    rw [quotientLieEquiv_apply_coe, quotientLieHom_apply]
    rw [identityComponent]
    apply (derivationComp_mem_lieSubalgebra_comapOfSurjective_iff _ _ _ _).mpr
    rw [lieSubalgebra_identityComponentHopfIdeal_eq_top]
    exact LieSubalgebra.mem_top _

end

end TauCeti.HopfIdeal
