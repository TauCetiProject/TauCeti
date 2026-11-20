/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DegreeOne
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DegreeZero
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Injective
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Leray's acyclicity theorem for a covering of a site

Let `(C, J)` be a site with finite products and a terminal object `T`, let `U` be a family of
objects covering the terminal object (`CategoryTheory.GrothendieckTopology.CoversTop`), and let
`F` be an abelian sheaf with no cohomology in positive degrees on any finite product
`U (a 0) × ⋯ × U (a m)` of members of `U` (a *Leray covering* for `F`). Then the Čech
cohomology `Hⁿ(U, F)`, the cohomology of the Čech complex `Č(U, F)`, is isomorphic to the sheaf
cohomology `Hⁿ(F)` in every degree, naturally in `F`
(`TauCeti.CategoryTheory.homologyCechComplexIsoH`).

For a covering `{Uᵢ ⟶ V}` of an object `V` of a site with fibre products, it can be applied to
the site `C/V`, whose products are the fibre products over `V`. For an open cover of a
topological space it is `TauCeti.Topology.homologyCechComplexIsoH`, which is derived from it.

The proof is by dimension shifting. Embed `F` into an injective sheaf `I`, with cokernel `Q`.

* On every finite product `V` of members of `U`, the sequence of sections
  `0 ⟶ F(V) ⟶ I(V) ⟶ Q(V) ⟶ 0` is exact, because `H¹(V, F) = 0`; so the Čech complexes form a
  short exact sequence `0 ⟶ Č(U, F) ⟶ Č(U, I) ⟶ Č(U, Q) ⟶ 0`.
* `Č(U, I)` has no cohomology in positive degrees, as for every injective abelian sheaf
  (`TauCeti.CategoryTheory.exactAt_cechComplexFunctor_obj_obj_of_injective`). This holds on
  any site, so the argument uses it in place of the flasqueness of injective sheaves on a
  topological space. Nor has `I` sheaf cohomology in positive degrees. The two long exact
  sequences then give `Hⁿ⁺¹(U, F) ≅ Hⁿ(U, Q)` and `Hⁿ⁺¹(F) ≅ Hⁿ(Q)` for `n ≥ 1`, while in degree
  one both `H¹(U, F)` and `H¹(F)` are the cokernel of `I(T) ⟶ Q(T)`, since `H⁰(U, -)` and
  `H⁰(-)` are both global sections.
* `Q` is again acyclic on the finite products, as `Hᵏ(V, Q) ≅ Hᵏ⁺¹(V, F)` for `k ≥ 1`.

Induction on the degree, for all sheaves at once, concludes.

## Main results

* `TauCeti.CategoryTheory.cechInjectiveCokernelSequence`: the sequence of Čech complexes of the
  chosen injective cokernel sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`, with its maps
  `TauCeti.CategoryTheory.cechInjectiveCokernelSequenceMap` induced by morphisms of sheaves and
  `TauCeti.CategoryTheory.cechInjectiveCokernelSequenceRefinement` induced by refinements of
  families; it is left exact (`TauCeti.CategoryTheory.cechInjectiveCokernelSequence_exact`), and
  short exact when `F` has no first cohomology on the finite products of members of `U`
  (`TauCeti.CategoryTheory.cechInjectiveCokernelSequence_shortExact`);
* `TauCeti.CategoryTheory.homologyCechComplexIsoH`: for a Leray covering `U`, `Hⁿ(U, F) ≅ Hⁿ(F)`
  for every `n`;
* `TauCeti.CategoryTheory.homologyMap_comp_homologyCechComplexIsoH_hom`: this isomorphism is
  natural in `F`;
* `TauCeti.CategoryTheory.homologyCechComplexIsoH_zero`: in degree `0` it is the identification of
  both groups with the global sections (`TauCeti.CategoryTheory.homologyZeroCechIso`);
* `TauCeti.CategoryTheory.δ_comp_homologyCechComplexIsoH_one_hom` and
  `TauCeti.CategoryTheory.δ_comp_homologyCechComplexIsoH_succ_hom`: it intertwines the connecting
  maps of the Čech and sheaf injective cokernel sequences;
* `TauCeti.CategoryTheory.homologyMap_cechComplexMap_comp_homologyCechComplexIsoH_hom`: it is
  compatible with refinement of Leray coverings.

## References

The formalization is adapted from split 6 of the
[lookahead development](https://github.com/roed-math/TauCeti-w2-fresh/tree/lookahead/SchemeAndStackFoundations/leray-spectral-sequence),
at commit `877ee62`
(<https://github.com/roed-math/TauCeti-w2-fresh/tree/877ee6253118ae038b46aca137f48841db354fe9>).
The degree `0` part of that development is in
`TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DegreeZero`.

* [Stacks: Tag 03AV](https://stacks.math.columbia.edu/tag/03AV), Section 21.10 on Čech cohomology
  and cohomology, and [Stacks: Tag 03OW](https://stacks.math.columbia.edu/tag/03OW), for Leray's
  acyclicity theorem.
* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.11, for an open cover of a topological space.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w' v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] {ι : Type v} (U : ι → C) {T : C} (hT : IsTerminal T)
  (hU : J.CoversTop U) [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-! ### Dimension shifting -/

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- The Leray condition: `F` has no cohomology in positive degrees on the finite products
`U (a 0) × ⋯ × U (a m)` of members of the family. -/
private def IsLerayProd (F : Sheaf J AddCommGrpCat.{v}) : Prop :=
  ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ), Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j)))

variable {U}

/-- The Čech complexes of the injective cokernel sequence of a Leray sheaf form a short exact
sequence. -/
private lemma cechSeq_shortExact {F : Sheaf J AddCommGrpCat.{v}} (hF : IsLerayProd U F) :
    (cechInjectiveCokernelSequence U F).ShortExact :=
  cechInjectiveCokernelSequence_shortExact U fun m a ↦ hF m a 0

/-- The cokernel `Q` of the chosen injective embedding of a Leray sheaf is again Leray. -/
private lemma isLerayProd_cokernel {F : Sheaf J AddCommGrpCat.{v}} (hF : IsLerayProd U F) :
    IsLerayProd U (cokernel (Injective.ι F)) :=
  fun m a k ↦ _root_.CategoryTheory.Sheaf.H'.subsingleton_X₃
    (injectiveCokernelSequence_shortExact F) _ (k + 1)
    (Abelian.Ext.subsingleton_of_injective _ _ _) (hF m a (k + 1))

variable (U)

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] in
/-- The injective sheaf `Injective.under F` has no Čech cohomology in positive degrees. -/
private lemma isZero_homology_cechComplex_under (F : Sheaf J AddCommGrpCat.{v}) (k : ℕ) :
    IsZero (((cechComplexFunctor U).obj (Injective.under F).obj).homology (k + 1)) :=
  (exactAt_cechComplexFunctor_obj_obj_of_injective U (Injective.under F) k).isZero_homology

/-- The Čech connecting map `Hⁿ(U, Q) ⟶ Hⁿ⁺¹(U, F)` is onto. -/
private lemma epi_δ_cechSeq {F : Sheaf J AddCommGrpCat.{v}} (hF : IsLerayProd U F) (n : ℕ) :
    Epi ((cechSeq_shortExact hF).δ n (n + 1) rfl) :=
  (cechSeq_shortExact hF).epi_δ n (n + 1) _ (isZero_homology_cechComplex_under U F n)

omit [EnoughInjectives (Sheaf J AddCommGrpCat.{v})] in
/-- The Leray product hypothesis includes first-cohomology vanishing on each member. -/
private lemma isLerayProd_one {F : Sheaf J AddCommGrpCat.{v}} (hF : IsLerayProd U F) (i : ι) :
    Subsingleton (F.H' 1 (U i)) := by
  have := hF 0 (fun _ ↦ i) 0
  exact (((F.cohomologyPresheaf 1).mapIso
    (productUniqueIso (fun _ : Fin 1 ↦ U i)).op).addCommGroupIsoToAddEquiv).injective.subsingleton

include hU

/-- **Leray's theorem, in the form constructed by induction.** The comparison is defined by
dimension shifting along the chosen injective cokernel sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`: in degree
`0` both groups are the global sections, in degree `1` both are the cokernel of the degree `0`
map induced by `I ⟶ Q`, and in degree `n + 2` both are identified with degree `n + 1` of `Q` by
the connecting maps. -/
private def cechIsoAux :
    (n : ℕ) → (F : Sheaf J AddCommGrpCat.{v}) → IsLerayProd U F →
      (((cechComplexFunctor U).obj F.obj).homology n ≅
        AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F n))
  | 0, F, _ => homologyZeroCechIso U hT hU F
  | 1, F, hF => homologyCechComplexIsoHOne U hT hU F (isLerayProd_one U hF)
  | n + 1 + 1, F, hF =>
    ((cechSeq_shortExact hF).δIso (n + 1) (n + 1 + 1) rfl
        (isZero_homology_cechComplex_under U F n)
        (isZero_homology_cechComplex_under U F (n + 1))).symm ≪≫
      cechIsoAux (n + 1) _ (isLerayProd_cokernel hF) ≪≫
      (AddEquiv.ofBijective _ (_root_.CategoryTheory.Sheaf.H.δ_bijective
        (injectiveCokernelSequence_shortExact F) (n + 1) (n + 1 + 1) rfl
        inferInstance inferInstance)).toAddCommGrpIso

/-- In positive degrees the comparison commutes with the connecting maps of the chosen injective
cokernel sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`. -/
@[reassoc]
private lemma δ_comp_cechIsoAux_hom (n : ℕ) (F : Sheaf J AddCommGrpCat.{v})
    (hF : IsLerayProd U F) :
    (cechSeq_shortExact hF).δ n (n + 1) rfl ≫ (cechIsoAux U hT hU (n + 1) F hF).hom =
      (cechIsoAux U hT hU n _ (isLerayProd_cokernel hF)).hom ≫ AddCommGrpCat.ofHom
        (_root_.CategoryTheory.Sheaf.H.δ (injectiveCokernelSequence_shortExact F) n (n + 1)
          rfl) := by
  rcases n with _ | n
  · exact δ_comp_homologyCechComplexIsoHOne_hom U hT hU F
      (isLerayProd_one U hF) (cechSeq_shortExact hF)
  · have := (cechSeq_shortExact hF).isIso_δ (n + 1) (n + 1 + 1) rfl
      (isZero_homology_cechComplex_under U F n)
      (isZero_homology_cechComplex_under U F (n + 1))
    simp only [cechIsoAux, Iso.trans_hom, Iso.symm_hom, ShortComplex.ShortExact.δIso, asIso_inv,
      IsIso.hom_inv_id_assoc, AddEquiv.toAddCommGrpIso_hom]
    -- `AddEquiv.ofBijective δ _` has underlying homomorphism `δ` by construction; Mathlib states
    -- no lemma for its `toAddMonoidHom`
    rfl

/-- The comparison is natural in the sheaf. -/
private lemma cechIsoAux_naturality (n : ℕ) :
    ∀ {F G : Sheaf J AddCommGrpCat.{v}} (hF : IsLerayProd U F) (hG : IsLerayProd U G)
      (f : F ⟶ G),
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) n ≫
          (cechIsoAux U hT hU n G hG).hom =
        (cechIsoAux U hT hU n F hF).hom ≫
          AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f n) := by
  induction n with
  | zero =>
    intro F G _ _ f
    exact homologyMap_comp_homologyZeroCechIso_hom U hT hU f
  | succ n ih =>
    intro F G hF hG f
    have := epi_δ_cechSeq U hF n
    rw [← cancel_epi ((cechSeq_shortExact hF).δ n (n + 1) rfl)]
    -- `f` extends to a morphism of the chosen injective cokernel sequences, with last component `g`
    let g : cokernel (Injective.ι F) ⟶ cokernel (Injective.ι G) :=
      (injectiveCokernelSequenceMap f).τ₃
    have hδC : (cechSeq_shortExact hF).δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) =
          HomologicalComplex.homologyMap ((cechComplexFunctor U).map g.hom) n ≫
            (cechSeq_shortExact hG).δ n (n + 1) rfl := by
      simpa only [cechInjectiveCokernelSequenceMap_τ₁, cechInjectiveCokernelSequenceMap_τ₃] using
        HomologicalComplex.HomologySequence.δ_naturality
          (cechInjectiveCokernelSequenceMap U f) (cechSeq_shortExact hF) (cechSeq_shortExact hG)
          n (n + 1) rfl
    have hδH : AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g n) ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact G) n (n + 1) rfl) =
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) n (n + 1) rfl) ≫
          AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f (n + 1)) := by
      ext x
      simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
        Function.comp_apply]
      have h := _root_.CategoryTheory.Sheaf.H.δ_naturality n (n + 1) rfl
        (injectiveCokernelSequence_shortExact F) (injectiveCokernelSequence_shortExact G)
        (injectiveCokernelSequenceMap f) x
      rwa [injectiveCokernelSequenceMap_τ₁] at h
    rw [reassoc_of% hδC, δ_comp_cechIsoAux_hom,
      reassoc_of% (ih (isLerayProd_cokernel hF) (isLerayProd_cokernel hG) g), hδH,
      ← δ_comp_cechIsoAux_hom_assoc]

/-- The comparison is compatible with refinement of Leray families. -/
private lemma cechIsoAux_refinement {κ : Type v} (V : κ → C) (hV : J.CoversTop V) (n : ℕ) :
    ∀ {F : Sheaf J AddCommGrpCat.{v}} (hFU : IsLerayProd U F) (hFV : IsLerayProd V F)
      (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V),
      HomologicalComplex.homologyMap (cechComplexMap F.obj φ) n ≫
          (cechIsoAux U hT hU n F hFU).hom = (cechIsoAux V hT hV n F hFV).hom := by
  induction n with
  | zero =>
    intro F _ _ φ
    exact homologyMap_cechComplexMap_comp_homologyZeroCechIso_hom U hT hU V hV F φ
  | succ n ih =>
    intro F hFU hFV φ
    have := epi_δ_cechSeq V hFV n
    rw [← cancel_epi ((cechSeq_shortExact hFV).δ n (n + 1) rfl)]
    have hδ : (cechSeq_shortExact hFV).δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap (cechComplexMap F.obj φ) (n + 1) =
          HomologicalComplex.homologyMap (cechComplexMap (cokernel (Injective.ι F)).obj φ) n ≫
            (cechSeq_shortExact hFU).δ n (n + 1) rfl := by
      have h := HomologicalComplex.HomologySequence.δ_naturality
        (cechInjectiveCokernelSequenceRefinement U V F φ)
        (cechSeq_shortExact hFV) (cechSeq_shortExact hFU) n (n + 1) rfl
      simp only [cechInjectiveCokernelSequenceRefinement_τ₁,
        cechInjectiveCokernelSequenceRefinement_τ₃] at h
      exact h
    rw [reassoc_of% hδ, δ_comp_cechIsoAux_hom,
      reassoc_of% (ih (isLerayProd_cokernel hFU) (isLerayProd_cokernel hFV) φ),
      δ_comp_cechIsoAux_hom]

/-! ### Leray's theorem -/

/-- **Leray's acyclicity theorem.** Let `U` be a family of objects of a site with finite products
whose maps to the terminal object `T` generate a covering sieve, and let `F` be an abelian sheaf
with no cohomology in positive degrees on any finite product `U (a 0) × ⋯ × U (a m)` of members of
`U`. Then the Čech cohomology `Hⁿ(U, F)`, the cohomology of the Čech complex of `F` for `U`, is
isomorphic to the sheaf cohomology `Hⁿ(F)`, for every `n`, naturally in `F`
(`TauCeti.CategoryTheory.homologyMap_comp_homologyCechComplexIsoH_hom`). -/
def homologyCechComplexIsoH (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j)))) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology n ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F n) :=
  cechIsoAux U hT hU n F hF

/-- In degree `0`, the comparison of Leray's theorem is the identification of both groups with
the global sections. -/
@[simp]
lemma homologyCechComplexIsoH_zero (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j)))) :
    homologyCechComplexIsoH U hT hU F hF 0 = homologyZeroCechIso U hT hU F :=
  (rfl)

/-- The degree-one case of Leray's theorem is the comparison using only memberwise
first-cohomology vanishing; the memberwise witness can be chosen independently. -/
lemma homologyCechComplexIsoH_one (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j))))
    (hF₁ : ∀ i, Subsingleton (F.H' 1 (U i))) :
    homologyCechComplexIsoH U hT hU F hF 1 = homologyCechComplexIsoHOne U hT hU F hF₁ :=
  (rfl)

/-- In degree one, the comparison of Leray's theorem intertwines the connecting maps
`H⁰(U, Q) ⟶ H¹(U, F)` and `H⁰(Q) ⟶ H¹(F)` of the chosen injective cokernel sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0`. The short exactness witness of its Čech complexes may be any one. -/
@[reassoc]
lemma δ_comp_homologyCechComplexIsoH_one_hom (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j))))
    (hS : (cechInjectiveCokernelSequence U F).ShortExact) :
    hS.δ 0 1 rfl ≫ (homologyCechComplexIsoH U hT hU F hF 1).hom =
      (homologyZeroCechIso U hT hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) :=
  δ_comp_homologyCechComplexIsoHOne_hom U hT hU F (isLerayProd_one U hF) hS

/-- In positive degrees, the comparison of Leray's theorem intertwines the connecting maps
`Hⁿ(U, Q) ⟶ Hⁿ⁺¹(U, F)` and `Hⁿ(Q) ⟶ Hⁿ⁺¹(F)` of the chosen injective cokernel sequence
`0 ⟶ F ⟶ I ⟶ Q ⟶ 0`, where `Q` again satisfies the hypotheses of Leray's theorem. The short
exactness witness of its Čech complexes may be any one. -/
@[reassoc]
lemma δ_comp_homologyCechComplexIsoH_succ_hom (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j))))
    (hQ : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton ((cokernel (Injective.ι F)).H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j))))
    (hS : (cechInjectiveCokernelSequence U F).ShortExact) (n : ℕ) :
    hS.δ n (n + 1) rfl ≫ (homologyCechComplexIsoH U hT hU F hF (n + 1)).hom =
      (homologyCechComplexIsoH U hT hU (cokernel (Injective.ι F)) hQ n).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) n (n + 1) rfl) :=
  δ_comp_cechIsoAux_hom U hT hU n F hF

/-- **Naturality of Leray's theorem.** The comparison `Hⁿ(U, F) ≅ Hⁿ(F)` commutes with the maps
induced by a morphism `F ⟶ G` of sheaves which both satisfy the hypotheses of Leray's theorem. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoH_hom {F G : Sheaf J AddCommGrpCat.{v}}
    (hF : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j))))
    (hG : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (G.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j))))
    (f : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) n ≫
        (homologyCechComplexIsoH U hT hU G hG n).hom =
      (homologyCechComplexIsoH U hT hU F hF n).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f n) :=
  cechIsoAux_naturality U hT hU n hF hG f

/-- **Leray's theorem and refinement.** For two families `U` and `V` covering the terminal object
on which `F` satisfies the hypotheses of Leray's theorem, the map `Hⁿ(V, F) ⟶ Hⁿ(U, F)` induced by
a morphism of families `U ⟶ V` commutes with the comparisons with `Hⁿ(F)`. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_homologyCechComplexIsoH_hom {κ : Type v} (V : κ → C)
    (hV : J.CoversTop V) (F : Sheaf J AddCommGrpCat.{v})
    (hFU : ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ U (a j))))
    (hFV : ∀ (m : ℕ) (a : Fin (m + 1) → κ) (k : ℕ),
      Subsingleton (F.H'.{v} (k + 1) (∏ᶜ fun j ↦ V (a j))))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) (n : ℕ) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj φ) n ≫
        (homologyCechComplexIsoH U hT hU F hFU n).hom =
      (homologyCechComplexIsoH V hT hV F hFV n).hom :=
  cechIsoAux_refinement U hT hU V hV n hFU hFV φ

end TauCeti.CategoryTheory
