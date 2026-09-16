/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.FiniteIndex
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Corestriction in group cohomology

Let `S` be a subgroup of finite index in a group `G` and `A` a `G`-representation. The
**corestriction** (or transfer) is the map

`cor : Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)`

in every degree `n`, going the opposite way to restriction. It is defined through Shapiro's lemma
as the composite

`Hⁿ(S, Res_S A) ≅ Hⁿ(G, Coind_S^G Res_S A) ⟶ Hⁿ(G, A)`

of the inverse of Mathlib's Shapiro isomorphism `groupCohomology.coindIso` and the map induced by
the trace `Coind_S^G Res_S A ⟶ A`, `f ↦ ∑ g⁻¹ • f g` over representatives of the right cosets of
`S`, which is the counit of the finite-index adjunction `Rep.coindResAdjunction`. The finiteness of
the index is used only for the trace.

The two basic properties are proved here in every degree: corestriction is natural in the
coefficients, and corestriction after restriction is multiplication by the index,
`cor ∘ res = [G : S]`. The latter is obtained by identifying Shapiro's isomorphism with
restriction followed by evaluation at `1`
(`TauCeti.groupCohomology.coindIso_hom`): restriction then becomes the map induced by the unit
`A ⟶ Coind_S^G Res_S A`, and the unit followed by the trace is `[G : S]`.

Corestriction is the map along which cohomological invariants are pushed from a subgroup to the
whole group; in class field theory it is the cohomological counterpart of the norm, and the
normalization `cor ∘ res = [G : S]` is what relates the invariants of a layer to those of its
restrictions.

## Main definitions

* `TauCeti.groupCohomology.corestrictionNatTrans k S n`: corestriction, as a natural
  transformation from `A ↦ Hⁿ(S, Res_S A)` to `A ↦ Hⁿ(G, A)`.
* `TauCeti.groupCohomology.corestriction S A n`: its component at `A`.

## Main results

* `TauCeti.groupCohomology.coindIso_hom_comp_corestriction`: read through Shapiro's isomorphism,
  corestriction is the map induced by the trace.
* `TauCeti.groupCohomology.map_comp_corestriction`: corestriction is natural in the coefficients.
* `TauCeti.groupCohomology.map_subtype_id_comp_corestriction`: corestriction after restriction is
  multiplication by `[G : S]`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter III, §9.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren
  der mathematischen Wissenschaften 323, Springer (2008), Chapter I, §5.
-/

public section

open CategoryTheory Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

universe u

variable (k : Type u) {G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.FiniteIndex]

open scoped Classical in
/-- The composite of the inverse of Shapiro's isomorphism with the map induced by the trace, for a
single representation. This is the component of `corestrictionNatTrans`. -/
private noncomputable def corestrictionApp (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology (res S.subtype A) n ⟶ groupCohomology A n :=
  (coindIso (res S.subtype A) n).inv ≫
    map (MonoidHom.id G) ((coindResAdjunction.{u, u, u} k S).counit.app A) n

variable {k}

private theorem map_comp_corestrictionApp {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id S) ((resFunctor S.subtype).map φ) n ≫ corestrictionApp k S B n =
      corestrictionApp k S A n ≫ map (MonoidHom.id G) φ n := by
  classical
  have hinv : map (MonoidHom.id S) ((resFunctor S.subtype).map φ) n ≫
      (coindIso (res S.subtype B) n).inv = (coindIso (res S.subtype A) n).inv ≫
        map (MonoidHom.id G) ((coindFunctor k S.subtype).map ((resFunctor S.subtype).map φ)) n := by
    rw [Iso.comp_inv_eq, Category.assoc, coindIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [corestrictionApp, corestrictionApp, ← Category.assoc, hinv, Category.assoc, Category.assoc,
    ← map_id_comp, ← map_id_comp]
  exact congrArg _ (congrArg (map (MonoidHom.id G) · n)
    ((coindResAdjunction.{u, u, u} k S).counit.naturality φ))

variable (k)

/-- **Corestriction in group cohomology**, natural in the coefficients: for a finite-index subgroup
`S ≤ G`, the map `Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)` obtained from Shapiro's isomorphism
`Hⁿ(S, Res_S A) ≅ Hⁿ(G, Coind_S^G Res_S A)` and the trace `Coind_S^G Res_S A ⟶ A`. -/
noncomputable def corestrictionNatTrans (n : ℕ) :
    resFunctor.{u} S.subtype ⋙ functor k S n ⟶ functor k G n where
  app A := corestrictionApp k S A n
  naturality _ _ φ := map_comp_corestrictionApp S φ n

variable {k}

/-- **Corestriction** `Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)` along a finite-index subgroup `S ≤ G`. -/
noncomputable def corestriction (A : Rep.{u} k G) (n : ℕ) :
    groupCohomology (res S.subtype A) n ⟶ groupCohomology A n :=
  (corestrictionNatTrans k S n).app A

@[simp]
theorem corestrictionNatTrans_app (A : Rep.{u} k G) (n : ℕ) :
    (corestrictionNatTrans k S n).app A = corestriction S A n := (rfl)

open scoped Classical in
/-- **Corestriction through Shapiro's lemma.** Precomposed with Shapiro's isomorphism
`Hⁿ(G, Coind_S^G Res_S A) ≅ Hⁿ(S, Res_S A)`, corestriction is the map induced by the trace
`Coind_S^G Res_S A ⟶ A`, the counit of `Rep.coindResAdjunction`. -/
theorem coindIso_hom_comp_corestriction (A : Rep.{u} k G) (n : ℕ) :
    (coindIso (res S.subtype A) n).hom ≫ corestriction S A n =
      map (MonoidHom.id G) ((coindResAdjunction.{u, u, u} k S).counit.app A) n :=
  Iso.hom_inv_id_assoc _ _

/-- **Corestriction is natural in the coefficients.** -/
@[reassoc, elementwise]
theorem map_comp_corestriction {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    map (MonoidHom.id S) ((resFunctor S.subtype).map φ) n ≫ corestriction S B n =
      corestriction S A n ≫ map (MonoidHom.id G) φ n :=
  map_comp_corestrictionApp S φ n

/-- **Corestriction after restriction is multiplication by the index**: for a finite-index
subgroup `S ≤ G`, the composite `Hⁿ(G, A) ⟶ Hⁿ(S, Res_S A) ⟶ Hⁿ(G, A)` of restriction and
corestriction is `[G : S]` times the identity, in every degree `n`. -/
@[reassoc, elementwise]
theorem map_subtype_id_comp_corestriction (A : Rep.{u} k G) (n : ℕ) :
    map S.subtype (𝟙 (res S.subtype A)) n ≫ corestriction S A n = S.index • 𝟙 _ := by
  classical
  -- The functor `Hⁿ(G, -)` is the composite of two additive functors.
  have hsmul : map (MonoidHom.id G) (S.index • 𝟙 A) n =
      (HomologicalComplex.homologyFunctor _ _ n).map ((cochainsFunctor k G).map (S.index • 𝟙 A)) :=
    rfl
  rw [← map_unit_comp_coindIso_hom, Category.assoc, coindIso_hom_comp_corestriction, ← map_id_comp,
    TauCeti.Rep.resCoindAdjunction_unit_app_comp_coindResAdjunction_counit_app, hsmul,
    Functor.map_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact congrArg (S.index • ·) (CategoryTheory.Functor.map_id _ _)

end TauCeti.groupCohomology
