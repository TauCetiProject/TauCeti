/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent of morphisms of quasi-coherent modules along fpqc coverings

This file proves that `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctor`, the pseudofunctor
`T ↦ QCoh(T)` with pullback, is a prestack for the fpqc topology: for every fpqc covering of a
scheme `S` and quasi-coherent modules `M`, `N` on `S`, a family of morphisms between the pullbacks
of `M` and `N` to the members of the covering which agree on the overlaps comes from a unique
morphism `M ⟶ N`. In terms of Mathlib's descent data, the functor from `QCoh(S)` to descent data
along any fpqc covering family is fully faithful (`Pseudofunctor.fullyFaithfulToDescentData`).
This is the descent of morphisms in fpqc descent of quasi-coherent modules; the effectivity of
descent data, which makes the pseudofunctor a stack, is not treated here.

The statement is proved for morphisms of arbitrary `𝒪_S`-modules into a quasi-coherent module
(`TauCeti.AlgebraicGeometry.Descent.existsUnique_pullback_map_eq_of_mem_fpqcTopology`). The proof
glues sections on the big site. Global sections of the pullbacks of `N` to the `S`-schemes form
an fpqc sheaf on `Over S` (`AlgebraicGeometry.Scheme.Modules.isSheaf_bigPresheaf_fpqcTopology`,
Stacks, Lemma 35.8.1). A compatible family of morphisms `m_Z : Z^* M ⟶ Z^* N`, for `Z` in a
covering sieve, therefore sends a global section of the pullback of `M` to an `S`-scheme `W` to a
global section of the pullback of `N` to `W`, glued from the sections `m_Z` of its restrictions.
Applied to the open subschemes `U` of `S`, whose global sections of the pullbacks are the sections
over `U`, this defines a morphism `M ⟶ N` whose pullbacks are the `m_Z`; uniqueness follows from
the uniqueness of the glued sections.

## Main declarations

* `TauCeti.AlgebraicGeometry.Descent.existsUnique_pullback_map_eq_of_mem_fpqcTopology`: a
  compatible family of morphisms from the pullbacks of an `𝒪_S`-module `M` to those of a
  quasi-coherent `N` over an fpqc covering sieve comes from a unique morphism `M ⟶ N`.
* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctor_isPrestack_fpqcTopology`:
  `qcohPseudofunctor` is a prestack for `Scheme.fpqcTopology`.

## References

* The Stacks Project, Proposition 35.5.2 (023T), descent of quasi-coherent modules along fpqc
  coverings, and Lemma 35.8.1 (023M), fpqc descent of sections of quasi-coherent modules.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace TauCeti.AlgebraicGeometry.Descent

open _root_.AlgebraicGeometry Scheme.Modules Pseudofunctor.LocallyDiscreteOpToCat

variable {S : Scheme.{u}} {M N : S.Modules}

namespace PresheafHomGlue

variable {R : Sieve (Over.mk (𝟙 S))}
  {m : ∀ ⦃Z : Over S⦄ (g : Z ⟶ Over.mk (𝟙 S)), R g →
    ((Scheme.Modules.pullback Z.hom).obj M ⟶ (Scheme.Modules.pullback Z.hom).obj N)}

variable (m) in
private lemma m_congr {Z : Over S} {g g' : Z ⟶ Over.mk (𝟙 S)} (hg : R g) (hg' : R g') :
    m g hg = m g' hg' := by
  obtain rfl := Over.mkIdTerminal.hom_ext g g'
  rfl

variable (hR : R ∈ (Scheme.fpqcTopology.over S) (Over.mk (𝟙 S)))

variable (hm : ∀ ⦃Z Z' : Over S⦄ (f : Z' ⟶ Z) (g : Z ⟶ Over.mk (𝟙 S)) (hg : R g),
  m (f ≫ g) (R.downward_closed hg f) = pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := N)
    (f₁ := Z.hom) (f₂ := Z.hom) (m g hg) f.left Z'.hom Z'.hom (Over.w f) (Over.w f))

variable (m) in
/-- The family of sections of `N` over the sieve pulled back to `W`, obtained by applying the
members of `m` to the restrictions of `z`. -/
private noncomputable def fam (W : Over S) (z : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤)) :
    Presieve.FamilyOfElements (N.bigPresheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (R.pullback (Over.mkIdTerminal.from W)).arrows :=
  fun _ g hg ↦ (m (g ≫ Over.mkIdTerminal.from W) hg).app ⊤ (bigSectionsRestrict M g z)

include hm in
private lemma fam_compatible (W : Over S)
    (z : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤)) : (fam m W z).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Z Z' g f hg
  have hfg : R (f ≫ g ≫ Over.mkIdTerminal.from W) := R.downward_closed hg f
  refine (congr(Hom.app $(m_congr m _ hfg) ⊤ (bigSectionsRestrict M (f ≫ g) z))).trans ?_
  refine (congr(Hom.app $(hm f _ hg) ⊤ _)).trans ?_
  rw [bigSectionsRestrict_comp]
  exact (bigSectionsRestrict_app f _ _).symm

variable [N.IsQuasicoherent]

include hR in
private lemma isSheafFor (W : Over S) :
    Presieve.IsSheafFor (N.bigPresheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (R.pullback (Over.mkIdTerminal.from W)).arrows :=
  isSheaf_bigPresheaf_comp_forget_fpqcTopology N _
    ((Scheme.fpqcTopology.over S).pullback_stable _ hR)

include hR hm in
/-- The section of `N` over `W` glued from the family `fam m W z`. -/
private noncomputable def glue (W : Over S) (z : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤)) :
    Γ((Scheme.Modules.pullback W.hom).obj N, ⊤) :=
  (isSheafFor hR W).amalgamate (fam m W z) (fam_compatible hm W z)

private lemma bigSectionsRestrict_glue (W : Over S)
    (z : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤))
    {Z : Over S} (g : Z ⟶ W) (hg : R (g ≫ Over.mkIdTerminal.from W)) :
    bigSectionsRestrict N g (glue hR hm W z) =
      (m (g ≫ Over.mkIdTerminal.from W) hg).app ⊤ (bigSectionsRestrict M g z) :=
  (isSheafFor hR W).valid_glue (fam_compatible hm W z) g hg

private lemma eq_glue (W : Over S) (z : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤))
    (t : Γ((Scheme.Modules.pullback W.hom).obj N, ⊤))
    (ht : ∀ ⦃Z : Over S⦄ (g : Z ⟶ W) (hg : R (g ≫ Over.mkIdTerminal.from W)),
      bigSectionsRestrict N g t =
        (m (g ≫ Over.mkIdTerminal.from W) hg).app ⊤ (bigSectionsRestrict M g z)) :
    t = glue hR hm W z :=
  (isSheafFor hR W).isSeparatedFor.ext fun _ g hg ↦
    (ht g hg).trans (bigSectionsRestrict_glue hR hm W z g hg).symm

private lemma glue_add (W : Over S) (z z' : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤)) :
    glue hR hm W (z + z') = glue hR hm W z + glue hR hm W z' :=
  (eq_glue hR hm W _ _ fun _ g hg ↦ by
    rw [map_add, map_add, map_add, bigSectionsRestrict_glue, bigSectionsRestrict_glue]).symm

private lemma glue_smul (W : Over S) (r : Γ(W.left, ⊤))
    (z : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤)) :
    glue hR hm W (r • z) = r • glue hR hm W z :=
  (eq_glue hR hm W _ _ fun _ g hg ↦ by
    rw [map_smulₛₗ, map_smulₛₗ, Hom.app_smul, bigSectionsRestrict_glue]).symm

private lemma bigSectionsRestrict_glue_eq_glue {W W' : Over S} (f : W' ⟶ W)
    (z : Γ((Scheme.Modules.pullback W.hom).obj M, ⊤)) :
    bigSectionsRestrict N f (glue hR hm W z) = glue hR hm W' (bigSectionsRestrict M f z) :=
  eq_glue hR hm W' _ _ fun Z g hg ↦ by
    have hgf : R ((g ≫ f) ≫ Over.mkIdTerminal.from W) := by
      rwa [Over.mkIdTerminal.hom_ext ((g ≫ f) ≫ _) (g ≫ _)]
    rw [← bigSectionsRestrict_comp, bigSectionsRestrict_glue hR hm W z (g ≫ f) hgf,
      bigSectionsRestrict_comp, m_congr m hgf hg]

/-- The `S`-scheme given by an open `U` of `S`. -/
private abbrev opensOver (U : S.Opens) : Over S := Over.mk U.ι

variable (M) in
/-- Sections of `M` over `U` as global sections of the pullback of `M` to `U`. -/
private noncomputable def sectionsEquiv (U : S.Opens) :
    Γ(M, U) ≃ Γ((Scheme.Modules.pullback U.ι).obj M, ⊤) :=
  Equiv.ofBijective _ (bijective_pullbackSectionsLE_ι M U ⊤ rfl)

private lemma sectionsEquiv_apply (U : S.Opens) (s : Γ(M, U)) :
    sectionsEquiv M U s = U.ι.pullbackSectionsLE M U ⊤ (by simp) s :=
  rfl

private lemma sectionsEquiv_add (F : S.Modules) (U : S.Opens) (s s' : Γ(F, U)) :
    sectionsEquiv F U (s + s') = sectionsEquiv F U s + sectionsEquiv F U s' :=
  map_add (U.ι.pullbackSectionsLE F U ⊤ (by simp)) s s'

private lemma sectionsEquiv_smul (F : S.Modules) (U : S.Opens) (r : Γ(S, U)) (s : Γ(F, U)) :
    sectionsEquiv F U (r • s) = (U.ι.appLE U ⊤ (by simp)).hom r • sectionsEquiv F U s :=
  map_smulₛₗ (U.ι.pullbackSectionsLE F U ⊤ (by simp)) r s

/-- The map on sections over `U` of the glued morphism. -/
private noncomputable def sectionsMap (U : S.Opens) (s : Γ(M, U)) : Γ(N, U) :=
  (sectionsEquiv N U).symm (glue hR hm (opensOver U) (sectionsEquiv M U s))

private lemma sectionsEquiv_sectionsMap (U : S.Opens) (s : Γ(M, U)) :
    sectionsEquiv N U (sectionsMap hR hm U s) = glue hR hm (opensOver U) (sectionsEquiv M U s) :=
  Equiv.apply_symm_apply _ _

/-- Restriction from `U` to `U' ≤ U` on the big site, read through `sectionsEquiv`. -/
private lemma bigSectionsRestrict_sectionsEquiv (F : S.Modules) {U U' : S.Opens} (i : U' ⟶ U)
    (s : Γ(F, U)) :
    bigSectionsRestrict F (Over.homMk (S.homOfLE i.le) (by simp) : opensOver U' ⟶ opensOver U)
      (sectionsEquiv F U s) = sectionsEquiv F U' (F.presheaf.map i.op s) := by
  rw [sectionsEquiv_apply, sectionsEquiv_apply, Scheme.Hom.pullbackSectionsLE_map]
  · exact bigSectionsRestrict_pullbackSectionsLE F _ U _ _ s
  · exact fun x _ ↦ i.le x.2

private lemma sectionsMap_add (U : S.Opens) (s s' : Γ(M, U)) :
    sectionsMap hR hm U (s + s') = sectionsMap hR hm U s + sectionsMap hR hm U s' :=
  (sectionsEquiv N U).injective (by
    rw [sectionsEquiv_add, sectionsEquiv_sectionsMap, sectionsEquiv_sectionsMap,
      sectionsEquiv_sectionsMap, sectionsEquiv_add, glue_add])

private lemma sectionsMap_smul (U : S.Opens) (r : Γ(S, U)) (s : Γ(M, U)) :
    sectionsMap hR hm U (r • s) = r • sectionsMap hR hm U s :=
  (sectionsEquiv N U).injective (by
    rw [sectionsEquiv_smul, sectionsEquiv_sectionsMap, sectionsEquiv_sectionsMap,
      sectionsEquiv_smul, glue_smul])

private lemma sectionsMap_map {U U' : S.Opens} (i : U' ⟶ U) (s : Γ(M, U)) :
    sectionsMap hR hm U' (M.presheaf.map i.op s) = N.presheaf.map i.op (sectionsMap hR hm U s) :=
  (sectionsEquiv N U').injective (by
    rw [sectionsEquiv_sectionsMap, ← bigSectionsRestrict_sectionsEquiv,
      ← bigSectionsRestrict_sectionsEquiv, sectionsEquiv_sectionsMap,
      bigSectionsRestrict_glue_eq_glue])

/-- The glued morphism of the underlying abelian presheaves. -/
private noncomputable def presheafMap : M.presheaf ⟶ N.presheaf where
  app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (sectionsMap hR hm U.unop)
    (sectionsMap_add hR hm U.unop))
  naturality _ _ i := by
    ext s
    exact sectionsMap_map hR hm i.unop s

/-- The glued morphism of modules. -/
private noncomputable def glued : M ⟶ N :=
  ⟨PresheafOfModules.homMk (presheafMap hR hm) fun U r s ↦ sectionsMap_smul hR hm U.unop r s⟩

private lemma glued_app (U : S.Opens) (s : Γ(M, U)) :
    (glued hR hm).app U s = sectionsMap hR hm U s :=
  rfl

private lemma pullback_map_glued {Y : Over S} (g : Y ⟶ Over.mk (𝟙 S)) (hg : R g) :
    (Scheme.Modules.pullback Y.hom).map (glued hR hm) = m g hg := by
  refine pullback_hom_ext fun U s ↦ ?_
  let V : Y.left.Opens := Y.hom ⁻¹ᵁ U
  let ιV : Over.mk (V.ι ≫ Y.hom) ⟶ Y := Over.homMk V.ι
  let c : Over.mk (V.ι ≫ Y.hom) ⟶ opensOver U :=
    Over.homMk (Y.hom.resLE U V le_rfl) (Scheme.Hom.resLE_comp_ι _ _)
  have hc : R (c ≫ Over.mkIdTerminal.from (opensOver U)) := by
    rw [Over.mkIdTerminal.hom_ext (c ≫ _) (ιV ≫ g)]
    exact R.downward_closed hg ιV
  have hV : ⊤ ≤ (V.ι ≫ Y.hom) ⁻¹ᵁ U := by simp [V]
  apply (bijective_bigSectionsRestrictLE_ι N Y.hom V).injective
  -- Both sides, read as global sections over the open subscheme `V = Y⁻¹ U`, are the value of
  -- the member of `m` over `V` on the pullback of `s`: for the glued morphism by construction of
  -- its sections over `U`, for `m g hg` by compatibility of `m` with restriction to `V`.
  have h₁ : bigSectionsRestrictLE N V.ι rfl V ⊤ (by simp)
      (((Scheme.Modules.pullback Y.hom).map (glued hR hm)).app V (Y.hom.pullbackSections M U s)) =
      (m _ hc).app ⊤ ((V.ι ≫ Y.hom).pullbackSectionsLE M U ⊤ hV s) := by
    rw [Scheme.Hom.pullbackSections_naturality, ← Scheme.Hom.pullbackSectionsLE_self,
      bigSectionsRestrictLE_pullbackSectionsLE N V.ι rfl U V ⊤ le_rfl _ hV]
    refine (bigSectionsRestrict_pullbackSectionsLE N c U (by simp) hV _).symm.trans ?_
    refine (congrArg (bigSectionsRestrict N c) (sectionsEquiv_sectionsMap hR hm U s)).trans ?_
    refine (bigSectionsRestrict_glue hR hm _ _ c hc).trans ?_
    exact congrArg _ (bigSectionsRestrict_pullbackSectionsLE M c U _ hV s)
  have h₂ : bigSectionsRestrictLE N V.ι rfl V ⊤ (by simp)
      ((m g hg).app V (Y.hom.pullbackSections M U s)) =
      (m _ hc).app ⊤ ((V.ι ≫ Y.hom).pullbackSectionsLE M U ⊤ hV s) := by
    rw [bigSectionsRestrictLE_app, ← Scheme.Hom.pullbackSectionsLE_self,
      bigSectionsRestrictLE_pullbackSectionsLE M V.ι rfl U V ⊤ le_rfl _ hV]
    have := hm ιV g hg
    exact congr(Hom.app $((this.symm.trans (m_congr m _ hc))) ⊤ _)
  exact h₁.trans h₂.symm

private lemma sectionsEquiv_app_eq_glue (φ : M ⟶ N)
    (hφ : ∀ ⦃Z : Over S⦄ (g : Z ⟶ Over.mk (𝟙 S)) (hg : R g),
      (Scheme.Modules.pullback Z.hom).map φ = m g hg)
    (U : S.Opens) (s : Γ(M, U)) :
    sectionsEquiv N U (φ.app U s) = glue hR hm (opensOver U) (sectionsEquiv M U s) :=
  eq_glue hR hm (opensOver U) (sectionsEquiv M U s) (sectionsEquiv N U (φ.app U s))
    fun Z g hg ↦ by
    have hU : ⊤ ≤ U.ι ⁻¹ᵁ U := (Scheme.Opens.ι_preimage_self U).ge
    have hZ : ⊤ ≤ Z.hom ⁻¹ᵁ U := by
      rw [← Over.w g]
      exact fun z _ ↦ (g.left z).2
    have h₁ := bigSectionsRestrict_pullbackSectionsLE N g U hU hZ (φ.app U s)
    have h₂ := bigSectionsRestrict_pullbackSectionsLE M g U hU hZ s
    have h₃ := Scheme.Hom.pullbackSectionsLE_naturality Z.hom M U ⊤ hZ φ s
    rw [hφ _ hg] at h₃
    exact h₁.trans (h₃.symm.trans (congrArg _ h₂.symm))

include hR hm in
private lemma existsUnique_pullback_map_eq :
    ∃! φ : M ⟶ N, ∀ ⦃Z : Over S⦄ (g : Z ⟶ Over.mk (𝟙 S)) (hg : R g),
      (Scheme.Modules.pullback Z.hom).map φ = m g hg := by
  refine ⟨glued hR hm, fun _ g hg ↦ pullback_map_glued hR hm g hg, fun φ hφ ↦ ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext s
  apply (sectionsEquiv N U).injective
  rw [sectionsEquiv_app_eq_glue hR hm φ hφ, glued_app, sectionsEquiv_sectionsMap]

end PresheafHomGlue

open PresheafHomGlue in
/-- **Morphisms into a quasi-coherent module glue along fpqc coverings.** Let `R` be an fpqc
covering sieve of `S`, viewed as a sieve on the terminal object of `Over S`, `M` an `𝒪_S`-module
and `N` a quasi-coherent `𝒪_S`-module. A family of morphisms `m_Z : Z^* M ⟶ Z^* N`, for the
`S`-schemes `Z` in `R`, compatible with pullback along morphisms of `S`-schemes, comes from a
unique morphism `φ : M ⟶ N`: `Z^* φ = m_Z` for every `Z` in `R`. -/
theorem existsUnique_pullback_map_eq_of_mem_fpqcTopology [N.IsQuasicoherent]
    {R : Sieve (Over.mk (𝟙 S))} (hR : R ∈ (Scheme.fpqcTopology.over S) (Over.mk (𝟙 S)))
    (m : ∀ ⦃Z : Over S⦄ (g : Z ⟶ Over.mk (𝟙 S)), R g →
      ((Scheme.Modules.pullback Z.hom).obj M ⟶ (Scheme.Modules.pullback Z.hom).obj N))
    (hm : ∀ ⦃Z Z' : Over S⦄ (f : Z' ⟶ Z) (g : Z ⟶ Over.mk (𝟙 S)) (hg : R g),
      m (f ≫ g) (R.downward_closed hg f) = pullHom (F := modulesPseudofunctor) (M₁ := M)
        (M₂ := N) (f₁ := Z.hom) (f₂ := Z.hom) (m g hg) f.left Z'.hom Z'.hom (Over.w f) (Over.w f)) :
    ∃! φ : M ⟶ N, ∀ ⦃Z : Over S⦄ (g : Z ⟶ Over.mk (𝟙 S)) (hg : R g),
      (Scheme.Modules.pullback Z.hom).map φ = m g hg :=
  existsUnique_pullback_map_eq hR hm

/-- **Descent of morphisms of quasi-coherent modules along fpqc coverings.** The pseudofunctor
`T ↦ QCoh(T)` is a prestack for the fpqc topology: for an fpqc covering of `S`, morphisms of
quasi-coherent modules on `S` are the families of morphisms between their pullbacks to the members
of the covering which agree on the overlaps. -/
instance qcohPseudofunctor_isPrestack_fpqcTopology :
    qcohPseudofunctor.{u}.IsPrestack Scheme.fpqcTopology :=
  Pseudofunctor.IsPrestack.of_isPrestackFor fun S R hR ↦ by
    rw [Pseudofunctor.isPrestackFor_iff_isSheafFor]
    intro M N x hx
    have : ((isQuasicoherent.prop ⟨op S⟩).ι.obj N).IsQuasicoherent := N.property
    have hR' : (Sieve.overEquiv _).symm R ∈ (Scheme.fpqcTopology.over S) (Over.mk (𝟙 S)) := by
      rwa [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
    let e := qcohPseudofunctor.presheafHomObjHomEquiv (M := M) (N := N)
    -- An element of the presheaf of morphisms over the terminal object is an amalgamation of `x`
    -- when the pullbacks of the corresponding morphism `M ⟶ N` are the members of `x`.
    have key (ψ : M ⟶ N) : x.IsAmalgamation (e ψ) ↔
        ∀ ⦃Z : Over S⦄ (g : Z ⟶ Over.mk (𝟙 S)) (hg : _),
          (Scheme.Modules.pullback Z.hom).map ψ.hom = (x g hg).hom :=
      forall_congr' fun _ ↦ forall_congr' fun g ↦ forall_congr' fun _ ↦ by
        rw [Pseudofunctor.presheafHom_map_presheafHomObjHomEquiv]
        exact ⟨fun h ↦ congrArg (·.hom) h, fun h ↦ ObjectProperty.hom_ext _ h⟩
    obtain ⟨φ, hφ, huniq⟩ := existsUnique_pullback_map_eq_of_mem_fpqcTopology hR'
      (fun _ g hg ↦ (x g hg).hom) fun _ _ f g hg ↦
        (congrArg (·.hom) (hx.to_sieveCompatible g f hg)).trans
          (qcohPseudofunctor_pullHom_hom (M₁ := M) (M₂ := N) _ _ _ _ _ _)
    refine ⟨e (ObjectProperty.homMk φ), (key _).2 hφ, fun y hy ↦ ?_⟩
    obtain ⟨ψ, rfl⟩ := e.surjective y
    exact congrArg e (ObjectProperty.hom_ext _ (huniq ψ.hom ((key ψ).1 hy)))

end TauCeti.AlgebraicGeometry.Descent
