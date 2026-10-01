/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Positive
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Trans
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction

/-!
# Restriction and corestriction in every Tate degree

For a subgroup `H` of a finite group `G`, the separate constructions of restriction and
corestriction in positive, zero, minus one, and lower negative degrees assemble into maps in
every integer degree. Their composite is multiplication by the index `[G : H]`. These uniform
maps are the group-change operations used in the restriction law for the Tate cup product.
In negative degrees, restriction is natural in the coefficient representation
(`res_natural_of_neg`).
Tower composition for class-field-theory layers is provided by
`ClassFieldTheory.LayerRestriction.tateRes_trans` and
`ClassFieldTheory.LayerRestriction.tateCor_trans`.

In positive degrees the maps use the canonical comparison with ordinary group cohomology; in
degrees zero and minus one they use invariants and norm kernels; below minus one they use the
comparison with group homology. The normalization follows the usual restriction-corestriction
identity (Brown, *Cohomology of Groups*, Chapter III, §9; Artin and Tate, *Class Field Theory*,
Chapter IV, §6).
-/

public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

/-- Restriction of Tate cohomology from a finite group to a subgroup, in every integer degree. -/
def res (M : Rep.{u} R G) (H : Subgroup G) :
    (r : ℤ) → tateCohomology M r ⟶ tateCohomology (Rep.res H.subtype M) r
  | .ofNat 0 => H0Res M H
  | .ofNat (n + 1) => posRes M H n
  | .negSucc 0 => HNegOneRes M H
  | .negSucc (n + 1) => negSuccRes M H (n + 1)

/-- In degree zero, uniform Tate restriction is induced by inclusion of invariants. -/
@[simp]
theorem res_zero (M : Rep.{u} R G) (H : Subgroup G) : res M H 0 = H0Res M H := by rfl

/-- In positive degrees, uniform Tate restriction is ordinary cohomological restriction. -/
@[simp]
theorem res_ofNat_succ (M : Rep.{u} R G) (H : Subgroup G) (n : ℕ) :
    res M H ((n : ℤ) + 1) = posRes M H n := by
  -- The recursor reduces at `Int.ofNat (n + 1)`; normalize the casted sum to that index first.
  simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
    (show res M H ((n + 1 : ℕ) : ℤ) = posRes M H n from rfl)

/-- In degree minus one, uniform Tate restriction uses the relative transfer on norm kernels. -/
@[simp]
theorem res_neg_one (M : Rep.{u} R G) (H : Subgroup G) :
    res M H (-1) = HNegOneRes M H := by rfl

/-- Below degree minus one, uniform Tate restriction is homological transfer. -/
@[simp]
theorem res_negSucc_succ (M : Rep.{u} R G) (H : Subgroup G) (n : ℕ) :
    res M H (Int.negSucc (n + 1)) = negSuccRes M H (n + 1) := by rfl

/-- **Tate restriction in negative degrees is natural in the coefficient representation.** -/
@[reassoc]
theorem res_natural_of_neg {M N : Rep.{u} R G} (f : M ⟶ N) (H : Subgroup G) {r : ℤ}
    (hr : r < 0) :
    (tateCohomologyFunctor r).map f ≫ res N H r =
      res M H r ≫ (tateCohomologyFunctor r).map ((Rep.resFunctor H.subtype).map f) := by
  obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hr.le
  rcases n with _ | _ | n
  · simp at hr
  · exact HNegOneRes_natural M H f
  · exact negSuccRes_natural M H f (n + 1)

/-- Corestriction of Tate cohomology from a subgroup of a finite group, in every integer
degree. -/
def cor (M : Rep.{u} R G) (H : Subgroup G) :
    (r : ℤ) → tateCohomology (Rep.res H.subtype M) r ⟶ tateCohomology M r
  | .ofNat 0 => H0Cor M H
  | .ofNat (n + 1) =>
      (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
          (Rep.res H.subtype M) ≫
        groupCohomology.corestriction H M (n + 1) ≫
          (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).inv.app M
  | .negSucc 0 => HNegOneCor M H
  | .negSucc (n + 1) => negSuccCor M H.subtype (n + 1)

/-- In degree zero, uniform Tate corestriction is the relative norm. -/
@[simp]
theorem cor_zero (M : Rep.{u} R G) (H : Subgroup G) : cor M H 0 = H0Cor M H := by rfl

/-- In positive degrees, uniform Tate corestriction is ordinary corestriction transported
through the canonical comparison isomorphisms. -/
@[simp]
theorem cor_ofNat_succ (M : Rep.{u} R G) (H : Subgroup G) (n : ℕ) :
    cor M H ((n : ℤ) + 1) =
      (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
          (Rep.res H.subtype M) ≫
        groupCohomology.corestriction H M (n + 1) ≫
          (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).inv.app M := by
  -- The recursor reduces at `Int.ofNat (n + 1)`; normalize the casted sum to that index first.
  simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
    (show cor M H ((n + 1 : ℕ) : ℤ) =
      (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
          (Rep.res H.subtype M) ≫
        groupCohomology.corestriction H M (n + 1) ≫
          (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).inv.app M from rfl)

/-- In degree minus one, uniform Tate corestriction includes the subgroup norm kernel. -/
@[simp]
theorem cor_neg_one (M : Rep.{u} R G) (H : Subgroup G) :
    cor M H (-1) = HNegOneCor M H := by rfl

/-- Below degree minus one, uniform Tate corestriction is the covariant map on homology. -/
@[simp]
theorem cor_negSucc_succ (M : Rep.{u} R G) (H : Subgroup G) (n : ℕ) :
    cor M H (Int.negSucc (n + 1)) = negSuccCor M H.subtype (n + 1) := by rfl

/-- In positive degrees, Tate corestriction agrees with ordinary cohomological corestriction
through the canonical comparison. -/
@[reassoc]
theorem cor_pos_comp_isoGroupCohomology_hom (M : Rep.{u} R G) (H : Subgroup G) (n : ℕ) :
    cor M H ((n : ℤ) + 1) ≫
        (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).hom.app M =
      (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
          (Rep.res H.subtype M) ≫ groupCohomology.corestriction H M (n + 1) := by
  -- The recursor reduces at `Int.ofNat (n + 1)`; normalize the casted sum to that index first.
  simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
    (show cor M H ((n + 1 : ℕ) : ℤ) ≫
        (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).hom.app M =
      (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
        (Rep.res H.subtype M) ≫ groupCohomology.corestriction H M (n + 1) from by
      simp only [cor]
      exact (Iso.eq_comp_inv
        ((_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).app M)).1 (by rfl))

/-- Restriction followed by corestriction multiplies every Tate class by the subgroup index,
in every integer degree. -/
@[simp, reassoc (attr := simp), elementwise (attr := simp)]
theorem res_comp_cor (M : Rep.{u} R G) (H : Subgroup G) (r : ℤ) :
    res M H r ≫ cor M H r = H.index • 𝟙 (tateCohomology M r) := by
  cases r with
  | ofNat n =>
    cases n with
    | zero => exact H0Res_comp_H0Cor M H
    | succ n =>
      let i : tateCohomology M ((n + 1 : ℕ) : ℤ) ≅ groupCohomology M (n + 1) :=
        (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).app M
      let j : tateCohomology (Rep.res H.subtype M) ((n + 1 : ℕ) : ℤ) ≅
          groupCohomology (Rep.res H.subtype M) (n + 1) :=
        (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).app _
      have key {A B C D : ModuleCat R} (f : A ⟶ B) (g : B ⟶ A)
          (i : A ≅ C) (j : B ≅ D) (r : C ⟶ D) (c : D ⟶ C) (d : ℕ)
          (hf : f ≫ j.hom = i.hom ≫ r) (hg : g ≫ i.hom = j.hom ≫ c)
          (hr : r ≫ c = d • 𝟙 C) : f ≫ g = d • 𝟙 A := by
        rw [← cancel_mono i.hom]
        rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, hr]
        simp
      exact key (posRes M H n) (cor M H ((n + 1 : ℕ) : ℤ)) i j
        (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) (n + 1))
        (groupCohomology.corestriction H M (n + 1)) H.index
        (posRes_comp_isoGroupCohomology_hom M H n)
        (cor_pos_comp_isoGroupCohomology_hom M H n)
        (groupCohomology.map_subtype_id_comp_corestriction H M (n + 1))
  | negSucc n =>
    cases n with
    | zero => exact HNegOneRes_comp_HNegOneCor M H
    | succ n => exact negSuccRes_comp_negSuccCor M H (n + 1)

end TauCeti.TateCohomology
