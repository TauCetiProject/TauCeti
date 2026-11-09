/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Coefficient naturality of group homology computed by a resolution

For any projective resolution `P` of the trivial representation, Mathlib's
`groupHomologyIso A n P` identifies group homology with the homology of `(A ⊗ P)_G`.
This identification commutes with every morphism of coefficient representations, including
nontrivial actions. Thus coefficient maps computed using a geometric resolution agree with
the maps on Mathlib's inhomogeneous group homology.

The chain-level input is coefficient naturality of `groupHomology.inhomogeneousChainsIso`.
The resulting naturality of `groupHomologyIsoTor` upgrades that comparison to an isomorphism
of functors. The final result applies to any chosen resolution, for example the singular
chains of a contractible free group space.

## References

* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Chapters I.7 and III.1.

The comparisons and inhomogeneous chain maps used here are Mathlib's constructions by
Amelia Livingston; no alternative group homology is introduced.
-/

public section

noncomputable section

open CategoryTheory Rep

universe u

namespace TauCeti.groupHomology

open _root_.groupHomology

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  {A B : Rep.{u} k G}

/-- The inhomogeneous-to-bar chain comparison commutes with coefficient morphisms. -/
@[reassoc]
theorem inhomogeneousChainsIso_hom_naturality (φ : A ⟶ B) :
    chainsMap (MonoidHom.id G) φ ≫ (inhomogeneousChainsIso B).hom =
      (inhomogeneousChainsIso A).hom ≫
        (NatTrans.mapHomologicalComplex ((coinvariantsTensor k G).map φ) _).app
          (barComplex k G) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext
    (Finsupp.lhom_ext fun x a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    chainsMap_id_f_hom_eq_mapRange, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, inhomogeneousChainsIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_hom,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
    coinvariantsTensorFreeLEquiv_symm_apply, finsuppToCoinvariantsTensorFree_single,
    NatTrans.mapHomologicalComplex_app_f]
  rfl

/-- The comparison between group homology and `Tor` is natural in the coefficients. -/
@[reassoc]
theorem groupHomologyIsoTor_hom_naturality (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id G) φ n ≫ (groupHomologyIsoTor B n).hom =
      (groupHomologyIsoTor A n).hom ≫
        ((Rep.Tor k G n).map φ).app (Rep.trivial k G k) := by
  have h := (Rep.barResolution k G).leftDerived_app_eq
    ((coinvariantsTensor k G).map φ) n
  have hc := congrArg (HomologicalComplex.homologyMap · n)
    (inhomogeneousChainsIso_hom_naturality φ)
  simp only [HomologicalComplex.homologyMap_comp] at hc
  rw [HomologicalComplex.homologyFunctor_map] at h
  -- `groupHomology` hides the homology objects at which the factors of the comparison
  -- compose. Present those factors explicitly: rewriting Iso.trans_hom inside the
  -- definition does not match these objects at reducible transparency.
  change HomologicalComplex.homologyMap (chainsMap (MonoidHom.id G) φ) n ≫
      (HomologicalComplex.homologyMap (inhomogeneousChainsIso B).hom n ≫
        (Rep.torIso B (barResolution k G) n).inv) =
    (HomologicalComplex.homologyMap (inhomogeneousChainsIso A).hom n ≫
        (Rep.torIso A (barResolution k G) n).inv) ≫
      (NatTrans.leftDerived ((coinvariantsTensor k G).map φ) n).app (Rep.trivial k G k)
  have ht : (Rep.torIso A (barResolution k G) n).inv ≫
      (NatTrans.leftDerived ((coinvariantsTensor k G).map φ) n).app (Rep.trivial k G k) =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((coinvariantsTensor k G).map φ) _).app
          (barComplex k G)) n ≫ (Rep.torIso B (barResolution k G) n).inv :=
    (Iso.inv_comp_eq _).2 h
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (Rep.torIso B (barResolution k G) n).inv) hc).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (HomologicalComplex.homologyMap (inhomogeneousChainsIso A).hom n ≫ ·)
      ht.symm).trans (Category.assoc _ _ _).symm

/-- Group homology and `Tor` of the trivial representation are naturally isomorphic
as functors of the coefficient representation. -/
def groupHomologyFunctorIsoTor (n : ℕ) :
    _root_.groupHomology.functor k G n ≅ (Rep.Tor k G n).flip.obj (Rep.trivial k G k) :=
  NatIso.ofComponents (fun A => groupHomologyIsoTor A n)
    (fun φ => groupHomologyIsoTor_hom_naturality φ n)

/-- The forward component is Mathlib's existing comparison with `Tor`. -/
@[simp]
theorem groupHomologyFunctorIsoTor_hom_app (n : ℕ) (A : Rep.{u} k G) :
    (groupHomologyFunctorIsoTor (k := k) (G := G) n).hom.app A =
      (groupHomologyIsoTor A n).hom :=
  (rfl)

/-- The inverse component is the inverse of Mathlib's comparison with `Tor`. -/
@[simp]
theorem groupHomologyFunctorIsoTor_inv_app (n : ℕ) (A : Rep.{u} k G) :
    (groupHomologyFunctorIsoTor (k := k) (G := G) n).inv.app A =
      (groupHomologyIsoTor A n).inv :=
  (rfl)

/-- Computing group homology with a chosen projective resolution commutes with
coefficient morphisms. The map on the resolution tensors `φ` with its identity. -/
@[reassoc]
theorem groupHomologyIso_hom_naturality (φ : A ⟶ B) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    map (MonoidHom.id G) φ n ≫ (groupHomologyIso B n P).hom =
      (groupHomologyIso A n P).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((coinvariantsTensor k G).map φ) _).app P.complex) n := by
  have h := P.leftDerived_app_eq ((coinvariantsTensor k G).map φ) n
  rw [HomologicalComplex.homologyFunctor_map] at h
  have ht : ((Rep.Tor k G n).map φ).app (Rep.trivial k G k) ≫
      (Rep.torIso B P n).hom = (Rep.torIso A P n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex ((coinvariantsTensor k G).map φ) _).app P.complex) n :=
    (Iso.eq_comp_inv _).1 h
  -- Unfold only the outer composite; the Tor and resolution objects then remain fixed
  -- while associativity and the two naturality squares are composed as equalities.
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (Rep.torIso B P n).hom)
      (groupHomologyIsoTor_hom_naturality φ n)).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((groupHomologyIsoTor A n).hom ≫ ·) ht).trans
      (Category.assoc _ _ _).symm

/-- The inverse resolution comparison also commutes with coefficient morphisms. -/
@[reassoc]
theorem groupHomologyIso_inv_naturality (φ : A ⟶ B) (n : ℕ)
    (P : ProjectiveResolution (Rep.trivial k G k)) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex ((coinvariantsTensor k G).map φ) _).app P.complex) n ≫
        (groupHomologyIso B n P).inv =
      (groupHomologyIso A n P).inv ≫ map (MonoidHom.id G) φ n := by
  apply (cancel_epi (groupHomologyIso A n P).hom).1
  rw [← Category.assoc, ← groupHomologyIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end TauCeti.groupHomology
