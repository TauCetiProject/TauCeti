/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.HomotopyCategory.ShortExact
public import TauCeti.Topology.Sets.Compacts
public import TauCeti.Topology.Sheaves.KSheaf.Homotopy

/-!
# Short exact sequences and mapping cones of homotopy K-sheaves

Homotopy K-sheaves (`TopCat.KPresheaf.IsHomotopyKSheaf`, Pardon, Definition A.2.5) are the
K-presheaves of cochain complexes which satisfy the K-sheaf axioms up to quasi-isomorphism. The
virtual cochain complexes of implicit atlases are built from them by cones and finite totals, so
the class has to be closed under these operations. This file proves that it is closed under
extensions, and that it contains the mapping cones of its morphisms: the case of sequences of
length two of Pardon's Lemma A.2.11.

* **Two out of three** (`CategoryTheory.ShortComplex.ShortExact.isHomotopyKSheaf_X₁`,
  `CategoryTheory.ShortComplex.ShortExact.isHomotopyKSheaf_X₂`,
  `CategoryTheory.ShortComplex.ShortExact.isHomotopyKSheaf_X₃`). In a short exact sequence
  `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of K-presheaves of cochain complexes, if two of the three terms are
  homotopy K-sheaves, so is the third. Each axiom compares the three terms through a morphism of
  short exact sequences of complexes and the long exact cohomology sequences: the three empty
  sections; the mapping cones of the Mayer–Vietoris maps of the three terms, which form a short
  exact sequence (`CochainComplex.mappingCone.shortExact_mapShortComplex`) mapping to the
  sections over the intersection by the natural map `TopCat.KPresheaf.mayerVietorisDesc`
  (`TopCat.KPresheaf.mappingConeMap_comp_mayerVietorisDesc`); and the colimits over compact
  neighbourhoods, which remain short exact because filtered colimits are exact.
* **Acyclic K-presheaves** (`TopCat.KPresheaf.isHomotopyKSheaf_of_acyclic`). A K-presheaf of
  acyclic complexes is a homotopy K-sheaf, since every map between acyclic complexes is a
  quasi-isomorphism.
* **Mapping cones** (`TopCat.KPresheaf.isHomotopyKSheaf_mappingConeFunctor`). The mapping cone
  `K ↦ cone (τ_K)` of a morphism `τ : F ⟶ G` of homotopy K-sheaves is a homotopy K-sheaf. It sits
  in the short exact sequence `G ⟶ cone τ ⟶ F⟦1⟧`, whose third term, the shift of `F`, is
  the cokernel of `F ⟶ cone (𝟙 F)` into the acyclic mapping cone of the identity
  (`CategoryTheory.NatTrans.shortExact_mappingConeInrShortComplex`).

The colimit axiom uses that filtered colimits in `C` are exact and that `X` is weakly locally
compact, as in Pardon's setting of locally compact Hausdorff spaces.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.isHomotopyKSheaf_X₂`: the middle term of a short exact
  sequence of homotopy K-sheaves is a homotopy K-sheaf, and similarly for the outer terms.
* `TopCat.KPresheaf.isHomotopyKSheaf_of_acyclic`: acyclic K-presheaves are homotopy K-sheaves.
* `TopCat.KPresheaf.isHomotopyKSheaf_mappingConeFunctor`: mapping cones of morphisms of homotopy
  K-sheaves are homotopy K-sheaves.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.2, Definition A.2.5 and
  Lemma A.2.11.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex CochainComplex

universe w v u

namespace TopCat.KPresheaf

variable {X : TopCat.{w}} [T2Space X] {C : Type u} [Category.{v} C] [Abelian C]

variable {S : ShortComplex (KPresheaf (CochainComplex C ℤ) X)}

omit [T2Space X] in
@[reassoc]
private lemma f_app_comp_g_app (S : ShortComplex (KPresheaf (CochainComplex C ℤ) X))
    (K : (Compacts X)ᵒᵖ) : S.f.app K ≫ S.g.app K = 0 := by
  rw [← NatTrans.comp_app, S.zero, NatTrans.app_zero]

/-- The short complex of sections of `S` over a compact set `K`. -/
private noncomputable abbrev sectionsShortComplex
    (S : ShortComplex (KPresheaf (CochainComplex C ℤ) X)) (K : Compacts X) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (S.f.app (op K)) (S.g.app (op K)) (f_app_comp_g_app S (op K))

/-- The morphism of short complexes of cochain complexes from the sections over `K₂ ∪ K₃` to the
sums of the sections over `K₂` and over `K₃`, given by the pairs of restrictions. -/
private noncomputable def restrictionHom (S : ShortComplex (KPresheaf (CochainComplex C ℤ) X))
    {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    sectionsShortComplex S K₄ ⟶ ShortComplex.mk
      (biprod.map (S.f.app (op K₂)) (S.f.app (op K₃)))
      (biprod.map (S.g.app (op K₂)) (S.g.app (op K₃)))
      (by apply biprod.hom_ext' <;> simp [f_app_comp_g_app_assoc]) where
  τ₁ := biprod.lift (S.X₁.map (opHomOfLE h.le₂₄)) (S.X₁.map (opHomOfLE h.le₃₄))
  τ₂ := biprod.lift (S.X₂.map (opHomOfLE h.le₂₄)) (S.X₂.map (opHomOfLE h.le₃₄))
  τ₃ := biprod.lift (S.X₃.map (opHomOfLE h.le₂₄)) (S.X₃.map (opHomOfLE h.le₃₄))
  comm₁₂ := by apply biprod.hom_ext <;> simp
  comm₂₃ := by apply biprod.hom_ext <;> simp

/-- The Mayer–Vietoris maps of the three terms of `S`, as a morphism of short complexes from the
mapping cones of the restrictions to the sections over `K₂ ∩ K₃`. -/
private noncomputable def mayerVietorisHom (S : ShortComplex (KPresheaf (CochainComplex C ℤ) X))
    {K₁ K₂ K₃ K₄ : Compacts X} (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    mappingCone.mapShortComplex (restrictionHom S h) ⟶ sectionsShortComplex S K₁ where
  τ₁ := S.X₁.mayerVietorisDesc h
  τ₂ := S.X₂.mayerVietorisDesc h
  τ₃ := S.X₃.mayerVietorisDesc h
  comm₁₂ := (mappingConeMap_comp_mayerVietorisDesc S.f h).symm
  comm₂₃ := (mappingConeMap_comp_mayerVietorisDesc S.g h).symm

omit [T2Space X] in
private lemma shortExact_sectionsShortComplex (hS : S.ShortExact) (K : Compacts X) :
    (sectionsShortComplex S K).ShortExact :=
  hS.map_of_exact ((evaluation _ _).obj (op K))

omit [T2Space X] in
private lemma shortExact_restrictionHom_target (hS : S.ShortExact) (K₂ K₃ : Compacts X) :
    (ShortComplex.mk (biprod.map (S.f.app (op K₂)) (S.f.app (op K₃)))
      (biprod.map (S.g.app (op K₂)) (S.g.app (op K₃)))
      (by apply biprod.hom_ext' <;> simp [f_app_comp_g_app_assoc])).ShortExact :=
  (shortExact_sectionsShortComplex hS K₂).biprod (shortExact_sectionsShortComplex hS K₃)

/-- The short exact sequences compared by the Mayer–Vietoris maps of the three terms of `S`. -/
private lemma shortExact_mayerVietorisHom (hS : S.ShortExact) {K₁ K₂ K₃ K₄ : Compacts X}
    (h : Lattice.BicartSq K₁ K₂ K₃ K₄) :
    (mappingCone.mapShortComplex (restrictionHom S h)).ShortExact ∧
      (sectionsShortComplex S K₁).ShortExact :=
  ⟨mappingCone.shortExact_mapShortComplex _ (shortExact_sectionsShortComplex hS K₄)
    (shortExact_restrictionHom_target hS K₂ K₃), shortExact_sectionsShortComplex hS K₁⟩

section Colimit

variable [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] [WeaklyLocallyCompactSpace X]

/-- The short complex of the colimits of the sections of `S` over the compact neighbourhoods of
`K`. -/
private noncomputable abbrev colimitShortComplex
    (S : ShortComplex (KPresheaf (CochainComplex C ℤ) X)) (K : Compacts X) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (colim.map (Functor.whiskerLeft (Set.mono_coe K.compactNhds).functor.op S.f))
    (colim.map (Functor.whiskerLeft (Set.mono_coe K.compactNhds).functor.op S.g))
    (colimit.hom_ext fun L ↦ by simp [f_app_comp_g_app_assoc])

/-- The maps from the colimits of the sections of the three terms of `S` over the compact
neighbourhoods of `K` to their sections over `K`. -/
private noncomputable def colimitHom (S : ShortComplex (KPresheaf (CochainComplex C ℤ) X))
    (K : Compacts X) : colimitShortComplex S K ⟶ sectionsShortComplex S K where
  τ₁ := colimit.desc _ (S.X₁.coconeOfCompacts K)
  τ₂ := colimit.desc _ (S.X₂.coconeOfCompacts K)
  τ₃ := colimit.desc _ (S.X₃.coconeOfCompacts K)
  comm₁₂ := colimit.hom_ext fun L ↦ by simp [coconeOfCompacts]
  comm₂₃ := colimit.hom_ext fun L ↦ by simp [coconeOfCompacts]

/-- Filtered colimits are exact, so the colimits of the sections of `S` over the compact
neighbourhoods of `K` form a short exact sequence. -/
private lemma shortExact_colimitShortComplex (hS : S.ShortExact) (K : Compacts X) :
    (colimitShortComplex S K).ShortExact := by
  let S' : ShortComplex ((K.compactNhds)ᵒᵖ ⥤ CochainComplex C ℤ) :=
    ShortComplex.mk (Functor.whiskerLeft (Set.mono_coe K.compactNhds).functor.op S.f)
      (Functor.whiskerLeft (Set.mono_coe K.compactNhds).functor.op S.g) (by
        ext L : 2
        simp [f_app_comp_g_app])
  have hS' : S'.ShortExact := ShortComplex.shortExact_of_forall_evaluation S' fun L ↦
    shortExact_sectionsShortComplex hS L.unop.val
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp)) (hS'.map_of_exact colim)

end Colimit

end TopCat.KPresheaf

/-! ### Two out of three -/

namespace CategoryTheory.ShortComplex.ShortExact

open TopCat TopCat.KPresheaf HomologySequence

variable {X : TopCat.{w}} [T2Space X] {C : Type u} [Category.{v} C] [Abelian C]
  [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] [WeaklyLocallyCompactSpace X]
  {S : ShortComplex (KPresheaf (CochainComplex C ℤ) X)} (hS : S.ShortExact)
include hS

/-- **Homotopy K-sheaves are closed under extensions.** In a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of K-presheaves of cochain complexes, if `F₁` and `F₃` are homotopy
K-sheaves, so is `F₂`. -/
theorem isHomotopyKSheaf_X₂ (h₁ : S.X₁.IsHomotopyKSheaf) (h₃ : S.X₃.IsHomotopyKSheaf) :
    S.X₂.IsHomotopyKSheaf where
  acyclic_bot := (shortExact_sectionsShortComplex hS ⊥).acyclic_X₂ h₁.acyclic_bot h₃.acyclic_bot
  quasiIso_mayerVietorisDesc h :=
    quasiIso_τ₂ (mayerVietorisHom S h) (shortExact_mayerVietorisHom hS h).1
      (shortExact_mayerVietorisHom hS h).2 (h₁.quasiIso_mayerVietorisDesc h)
      (h₃.quasiIso_mayerVietorisDesc h)
  exists_isColimit_quasiIso_desc K := by
    refine ⟨_, colimit.isColimit _, quasiIso_τ₂ (colimitHom S K)
      (shortExact_colimitShortComplex hS K) (shortExact_sectionsShortComplex hS K) ?_ ?_⟩
    · exact IsHomotopyKSheaf.quasiIso_desc _ h₁ K _
    · exact IsHomotopyKSheaf.quasiIso_desc _ h₃ K _

/-- In a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of K-presheaves of cochain complexes, if
`F₂` and `F₃` are homotopy K-sheaves, so is `F₁`. -/
theorem isHomotopyKSheaf_X₁ (h₂ : S.X₂.IsHomotopyKSheaf) (h₃ : S.X₃.IsHomotopyKSheaf) :
    S.X₁.IsHomotopyKSheaf where
  acyclic_bot := (shortExact_sectionsShortComplex hS ⊥).acyclic_X₁
    (quasiIso_of_acyclic _ h₂.acyclic_bot h₃.acyclic_bot)
  quasiIso_mayerVietorisDesc h :=
    quasiIso_τ₁ (mayerVietorisHom S h) (shortExact_mayerVietorisHom hS h).1
      (shortExact_mayerVietorisHom hS h).2 (h₂.quasiIso_mayerVietorisDesc h)
      (h₃.quasiIso_mayerVietorisDesc h)
  exists_isColimit_quasiIso_desc K := by
    refine ⟨_, colimit.isColimit _, quasiIso_τ₁ (colimitHom S K)
      (shortExact_colimitShortComplex hS K) (shortExact_sectionsShortComplex hS K) ?_ ?_⟩
    · exact IsHomotopyKSheaf.quasiIso_desc _ h₂ K _
    · exact IsHomotopyKSheaf.quasiIso_desc _ h₃ K _

/-- In a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of K-presheaves of cochain complexes, if
`F₁` and `F₂` are homotopy K-sheaves, so is `F₃`. -/
theorem isHomotopyKSheaf_X₃ (h₁ : S.X₁.IsHomotopyKSheaf) (h₂ : S.X₂.IsHomotopyKSheaf) :
    S.X₃.IsHomotopyKSheaf where
  acyclic_bot := (shortExact_sectionsShortComplex hS ⊥).acyclic_X₃
    (quasiIso_of_acyclic _ h₁.acyclic_bot h₂.acyclic_bot)
  quasiIso_mayerVietorisDesc h :=
    quasiIso_τ₃ (mayerVietorisHom S h) (shortExact_mayerVietorisHom hS h).1
      (shortExact_mayerVietorisHom hS h).2 (h₁.quasiIso_mayerVietorisDesc h)
      (h₂.quasiIso_mayerVietorisDesc h)
  exists_isColimit_quasiIso_desc K := by
    refine ⟨_, colimit.isColimit _, quasiIso_τ₃ (colimitHom S K)
      (shortExact_colimitShortComplex hS K) (shortExact_sectionsShortComplex hS K) ?_ ?_⟩
    · exact IsHomotopyKSheaf.quasiIso_desc _ h₁ K _
    · exact IsHomotopyKSheaf.quasiIso_desc _ h₂ K _

end CategoryTheory.ShortComplex.ShortExact

/-! ### Acyclic K-presheaves and mapping cones -/

namespace TopCat.KPresheaf

open ZeroObject

variable {X : TopCat.{w}} [T2Space X] {C : Type u} [Category.{v} C] [Abelian C]
  [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] [WeaklyLocallyCompactSpace X]

/-- A K-presheaf of acyclic cochain complexes is a homotopy K-sheaf: each of the axioms asks for a
map between acyclic complexes to be a quasi-isomorphism, the colimits of acyclic complexes over the
compact neighbourhoods of a compact set being acyclic because filtered colimits commute with
cohomology. -/
theorem isHomotopyKSheaf_of_acyclic {F : KPresheaf (CochainComplex C ℤ) X}
    (hF : ∀ K : Compacts X, (F.obj (op K)).Acyclic) : F.IsHomotopyKSheaf where
  acyclic_bot := hF ⊥
  quasiIso_mayerVietorisDesc h := quasiIso_of_acyclic _
    ((quasiIso_iff_acyclic_mappingCone _).1
      (quasiIso_of_acyclic _ (hF _) ((acyclic_biprod_iff _ _).2 ⟨hF _, hF _⟩))) (hF _)
  exists_isColimit_quasiIso_desc K := by
    refine ⟨_, colimit.isColimit _, quasiIso_of_acyclic _ (fun n ↦ ?_) (hF K)⟩
    rw [exactAt_iff_isZero_homology]
    exact (IsZero.iff_id_eq_zero _).2
      ((isColimitOfPreserves (homologyFunctor C (ComplexShape.up ℤ) n)
        (colimit.isColimit _)).hom_ext fun L ↦ ((hF _ n).isZero_homology).eq_of_src _ _)

variable {F G : KPresheaf (CochainComplex C ℤ) X} (τ : F ⟶ G)

/-- **Pardon, Lemma A.2.11, for mapping cones.** The mapping cone `K ↦ cone (τ_K)` of a morphism
`τ : F ⟶ G` of homotopy K-sheaves is a homotopy K-sheaf. -/
theorem isHomotopyKSheaf_mappingConeFunctor (hF : F.IsHomotopyKSheaf) (hG : G.IsHomotopyKSheaf) :
    IsHomotopyKSheaf (NatTrans.mappingConeFunctor τ) := by
  -- the shift `F⟦1⟧` of `F` is the cokernel of `F ⟶ cone (𝟙 F)`, whose middle term is acyclic
  have hcone : IsHomotopyKSheaf (NatTrans.mappingConeFunctor (𝟙 F)) :=
    isHomotopyKSheaf_of_acyclic fun K ↦
      (quasiIso_iff_acyclic_mappingCone (𝟙 (F.obj (op K)))).1 inferInstance
  exact (NatTrans.shortExact_mappingConeInrShortComplex τ).isHomotopyKSheaf_X₂ hG
    ((NatTrans.shortExact_mappingConeInrShortComplex (𝟙 F)).isHomotopyKSheaf_X₃ hF hcone)

end TopCat.KPresheaf
