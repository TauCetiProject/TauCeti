/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Corestriction.ConnectingMap

/-!
# Coefficient naturality of Tate corestriction

Corestriction from a subgroup of a finite group is natural in the coefficient representation
in every integer degree. This allows a coefficient pairing, such as tensoring with an invariant
vector, to pass through corestriction.

In nonnegative degrees this is the naturality of the relative norm and ordinary corestriction;
in negative degrees it follows from the canonical injection into group homology.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

/-- Tate corestriction is natural in the coefficient representation, in every integer degree.
The subgroup carrier uses the canonical `Subgroup.fintypeOfFinite` instance, as in `cor`. -/
@[reassoc]
theorem cor_natural {M N : Rep k G} (f : M ⟶ N) (H : Subgroup G) (r : ℤ) :
    (tateCohomologyFunctor r).map (Rep.resMap H.subtype f) ≫ cor N H r =
      cor M H r ≫ (tateCohomologyFunctor r).map f := by
  cases r with
  | ofNat n =>
    cases n with
    | zero =>
      -- Retype only the index before rewriting the opaque corestriction definition.
      change (tateCohomologyFunctor 0).map (Rep.resMap H.subtype f) ≫ cor N H 0 =
        cor M H 0 ≫ (tateCohomologyFunctor 0).map f
      rw [cor_zero, cor_zero]
      ext x
      induction x using H0_induction_on with
      | h x =>
        rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
          H0π_comp_tateCohomologyFunctor_map_apply, H0π_comp_H0Cor_apply,
          H0π_comp_H0Cor_apply, H0π_comp_tateCohomologyFunctor_map_apply]
        congr 1
        apply Subtype.ext
        simp only [Rep.invariantsFunctor, LinearMap.codRestrict_apply, LinearMap.comp_apply,
          Submodule.subtype_apply, Rep.resMap_hom_toLinearMap,
          Representation.coe_relNormInvariants, Representation.relNorm_apply]
        erw [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
          Representation.coe_relNormInvariants, Representation.relNorm_apply, map_sum]
        exact Finset.sum_congr rfl fun q _ ↦ (Rep.hom_comm_apply f q.out x.1).symm
    | succ n =>
      -- Restate comparison naturality with the ordinary-cohomology carrier, which is a
      -- semireducible wrapper around the functor's value.
      have hG : (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map f ≫
          (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).hom.app N =
        (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).hom.app M ≫
          groupCohomology.map (MonoidHom.id G) f (n + 1) :=
        NatTrans.naturality
          (self := (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).hom) f
      have hH : (tateCohomologyFunctor ((n + 1 : ℕ) : ℤ)).map (Rep.resMap H.subtype f) ≫
          (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
            (Rep.res H.subtype N) =
        (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
            (Rep.res H.subtype M) ≫
          groupCohomology.map (MonoidHom.id H) (Rep.resMap H.subtype f) (n + 1) :=
        NatTrans.naturality
          (self := (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom)
          (Rep.resMap H.subtype f)
      -- Prove the conjugation square on named ModuleCat objects, avoiding rewrites across
      -- the semireducible ordinary-cohomology functor wrapper.
      have square {A B C D A' B' C' D' : ModuleCat k}
          (a : A ⟶ B) (b : C ⟶ D) (c : A ⟶ C) (d : B ⟶ D)
          (i : A ≅ A') (j : B ≅ B') (l : C ≅ C') (m : D ≅ D')
          (a' : A' ⟶ B') (b' : C' ⟶ D') (c' : A' ⟶ C') (d' : B' ⟶ D')
          (ha : a ≫ j.hom = i.hom ≫ a') (hb : b ≫ m.hom = l.hom ≫ b')
          (hc : c ≫ l.hom = i.hom ≫ c') (hd : d ≫ m.hom = j.hom ≫ d')
          (hs : a' ≫ d' = c' ≫ b') : a ≫ d = c ≫ b := by
        rw [← cancel_mono m.hom]
        simp only [Category.assoc, hd, hb]
        simp only [← Category.assoc, ha, hc]
        simp only [Category.assoc, hs]
      exact square _ _ _ _
        ((_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).app _)
        ((_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).app _)
        ((_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).app _)
        ((_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).app _)
        _ _ _ _ hH hG (cor_pos_comp_isoGroupCohomology_hom M H n)
        (cor_pos_comp_isoGroupCohomology_hom N H n)
        (groupCohomology.map_comp_corestriction H f (n + 1))
  | negSucc n =>
    cases n with
    | zero =>
      rw [← cancel_mono (toGroupHomology N 0), Category.assoc, cor_comp_toGroupHomology,
        tateCohomologyFunctor_map_comp_toGroupHomology_assoc, Category.assoc,
        tateCohomologyFunctor_map_comp_toGroupHomology,
        cor_comp_toGroupHomology_assoc, ← groupHomology.map_comp,
        ← groupHomology.map_comp]
      simp only [Category.id_comp]
      rfl
    | succ n =>
      simpa only [cor_negSucc_succ] using map_comp_negSuccCor H.subtype (n + 1) f

end TauCeti.TateCohomology
