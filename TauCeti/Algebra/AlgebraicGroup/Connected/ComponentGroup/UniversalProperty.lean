/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Components
import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Connected
import TauCeti.Algebra.AlgebraicGroup.Tangent.Etale

/-!
# The universal property of the component group

Over an algebraically closed field, every homomorphism from a finite-type affine group to a
finite étale group factors uniquely through its component group. The group may be nonreduced.
In Hopf coordinates, composition with `componentCoordinateHom` is therefore a bijection on
morphisms from any étale finite-type coordinate Hopf algebra.

A morphism to a constant group kills the connected identity component. Its coordinate functions
thus belong to the identity-component coinvariants, which are precisely the image of the
component coordinate algebra. An étale affine group over the algebraically closed field is
constant by `Tangent.Etale` and `ComponentGroup.TrivialIdentity`. The remaining inputs are the
coinvariant description in `HopfIdeal.Coinvariants.Components` and the connected-group theorem in
`ConstantGroup.Connected`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 6.7.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

noncomputable section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- A homomorphism to a finite constant group kills the entire identity-component subgroup
scheme, including its possible infinitesimal structure. Coordinate ideals reverse containment.
-/
private theorem kernelHopfIdeal_le_identityComponentHopfIdeal_of_constant
    {G : Type u} [Group G] [Finite G]
    (f : CommHopfAlgCat.of k (ConstantGroup.coordinateRing k G) ⟶ H.obj) :
    CommHopfAlgCat.kernelHopfIdeal f ≤
      HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) := by
  let I := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)
  let q := CommHopfAlgCat.mkQuotient H.obj I
  have hconn := (geometricallyConnected_identityComponent H).connectedSpace k _
  have htriv := ConstantGroup.bialgHom_eq_unit_comp_counit_of_connected G hconn
    (q.hom.comp f.hom)
  apply HopfIdeal.toIdeal_le_toIdeal.mp
  rw [← CommHopfAlgCat.mkQuotient_ker H.obj I]
  apply (CommHopfAlgCat.kernelHopfIdeal_toIdeal_le_ker_iff f q.hom.toAlgHom).mpr
  exact congrArg BialgHom.toAlgHom htriv

/-- A homomorphism to an étale affine group kills the scheme-theoretic identity component.
No reducedness assumption on the source group is required. -/
theorem kernelHopfIdeal_le_identityComponentHopfIdeal_of_etale
    (Q : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Etale k Q] (f : Q.obj ⟶ H.obj) :
    CommHopfAlgCat.kernelHopfIdeal f ≤
      HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H) := by
  have hQ := identityComponentHopfIdeal_eq_augmentation_of_finrank_lie_eq_zero Q
    (HopfAlgebra.algebraEtale_iff_finrank_lie_eq_zero.mp inferInstance)
  let e := componentCoordinateIsoOfIdentityComponentHopfIdealEqAugmentation Q hQ
  have h := kernelHopfIdeal_le_identityComponentHopfIdeal_of_constant H (e.hom ≫ f)
  rwa [CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective e.hom
    (ConcreteCategory.bijective_of_isIso e.hom).2 f] at h

/-- **The universal property of the component group.** Every affine-group homomorphism to a
finite étale group factors uniquely through the canonical component morphism. The coordinate
arrow of the factorization runs from the étale target to the component coordinate algebra. -/
theorem existsUnique_comp_componentCoordinateHom
    (Q : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Etale k Q] (f : Q.obj ⟶ H.obj) :
    ∃! g : Q.obj ⟶
        CommHopfAlgCat.of k
          (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H))),
      g ≫ componentCoordinateHom H = f := by
  let l := CommHopfAlgCat.liftCoinvariants (isNormal_identityComponentHopfIdeal H) f
    (kernelHopfIdeal_le_identityComponentHopfIdeal_of_etale H Q f)
  have hfactor : (l ≫ (componentCoinvariantsIso H).inv) ≫ componentCoordinateHom H = f := by
    rw [Category.assoc, ← componentCoinvariantsIso_hom_comp H, Iso.inv_hom_id_assoc]
    exact CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι _ _ _
  exact ⟨l ≫ (componentCoinvariantsIso H).inv, hfactor,
    fun g hg ↦ (cancel_mono (componentCoordinateHom H)).mp (hg.trans hfactor.symm)⟩

/-- Homomorphisms from an affine group to an étale finite-type affine group are exactly
homomorphisms from its component group to that group, in coordinate Hopf algebras. -/
def componentEtaleHomEquiv (Q : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Etale k Q] :
    (Q.obj ⟶ CommHopfAlgCat.of k
      (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) ≃
    (Q.obj ⟶ H.obj) :=
  Equiv.ofBijective (fun g ↦ g ≫ componentCoordinateHom H)
    ⟨fun g h heq ↦ by
      obtain ⟨l, -, hl⟩ := existsUnique_comp_componentCoordinateHom H Q
        (g ≫ componentCoordinateHom H)
      exact (hl g rfl).trans (hl h heq.symm).symm,
      fun f ↦ (existsUnique_comp_componentCoordinateHom H Q f).exists⟩

/-- The universal-property equivalence is composition with the component coordinate morphism. -/
@[simp]
theorem componentEtaleHomEquiv_apply (Q : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Algebra.Etale k Q]
    (g : Q.obj ⟶ CommHopfAlgCat.of k
      (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) :
    componentEtaleHomEquiv H Q g = g ≫ componentCoordinateHom H :=
  (rfl)

/-- The inverse equivalence supplies the factorization of a homomorphism to an étale group. -/
@[reassoc (attr := simp)]
theorem componentEtaleHomEquiv_symm_comp (Q : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Algebra.Etale k Q] (f : Q.obj ⟶ H.obj) :
    (componentEtaleHomEquiv H Q).symm f ≫ componentCoordinateHom H = f :=
  (componentEtaleHomEquiv H Q).apply_symm_apply f

/-- Factoring a morphism already composed with the component projection recovers that morphism. -/
@[simp]
theorem componentEtaleHomEquiv_symm_apply_comp (Q : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Algebra.Etale k Q]
    (g : Q.obj ⟶ CommHopfAlgCat.of k
      (ConstantGroup.coordinateRing k (ConnectedComponents (PrimeSpectrum H)))) :
    (componentEtaleHomEquiv H Q).symm (g ≫ componentCoordinateHom H) = g := by
  rw [← componentEtaleHomEquiv_apply]
  exact (componentEtaleHomEquiv H Q).symm_apply_apply g

end

end TauCeti.FiniteTypeCommHopfAlgCat
