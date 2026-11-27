/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.FullyFaithful
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
These glued sections form a morphism `M^a ⟶ N^a` of big-site presheaves of modules. Read off on
the open subschemes `U` of `S`, whose global sections of the pullbacks are the sections over `U`,
it defines a morphism `M ⟶ N` (`AlgebraicGeometry.Scheme.Modules.bigOfHom`) whose pullbacks are
the `m_Z`; uniqueness follows from the uniqueness of the glued sections.

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

/-- The glued sections as a morphism `M^a ⟶ N^a` of presheaves of modules on the big site. -/
private noncomputable def glueHom : M.bigPresheaf ⟶ N.bigPresheaf :=
  PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (AddMonoidHom.mk' (glue hR hm W.unop) (glue_add hR hm W.unop))
      naturality _ _ f := by
        ext z
        exact (bigSectionsRestrict_glue_eq_glue hR hm f.unop z).symm }
    fun W r z ↦ glue_smul hR hm W.unop r z

/-- The glued morphism of modules, read off from `glueHom` on the open subschemes of `S`. -/
private noncomputable def glued : M ⟶ N :=
  bigOfHom (glueHom hR hm)

private lemma bigPresheafOpensAddEquiv_glued_app (U : S.Opens) (s : Γ(M, U)) :
    bigPresheafOpensAddEquiv N U ((glued hR hm).app U s) =
      glue hR hm (opensOver U) (bigPresheafOpensAddEquiv M U s) :=
  -- `glued` is `bigOfHom (glueHom hR hm)`, and `glueHom` acts by `glue` by its definition.
  bigPresheafOpensAddEquiv_bigOfHom_app (glueHom hR hm) U s

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
  apply (bijective_bigSectionsRestrictLE_ι N Y.hom V rfl).injective
  -- Both sides, read as global sections over the open subscheme `V = Y⁻¹ U`, are the value of
  -- the member of `m` over `V` on the pullback of `s`: for the glued morphism by construction of
  -- its sections over `U`, for `m g hg` by compatibility of `m` with restriction to `V`.
  have h₁ : bigSectionsRestrictLE N V.ι rfl V ⊤ (by simp)
      (((Scheme.Modules.pullback Y.hom).map (glued hR hm)).app V (Y.hom.pullbackSections M U s)) =
      (m _ hc).app ⊤ ((V.ι ≫ Y.hom).pullbackSectionsLE M U ⊤ hV s) := by
    rw [Scheme.Hom.pullbackSections_naturality, ← Scheme.Hom.pullbackSectionsLE_self,
      bigSectionsRestrictLE_pullbackSectionsLE N V.ι rfl U V ⊤ le_rfl _ hV]
    refine (bigSectionsRestrict_pullbackSectionsLE N c U (by simp) hV _).symm.trans ?_
    refine (congrArg (bigSectionsRestrict N c) ((bigPresheafOpensAddEquiv_apply N U _).symm.trans
      (bigPresheafOpensAddEquiv_glued_app hR hm U s))).trans ?_
    rw [bigSectionsRestrict_glue hR hm _ _ c hc, bigPresheafOpensAddEquiv_apply]
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
    bigPresheafOpensAddEquiv N U (φ.app U s) =
      glue hR hm (opensOver U) (bigPresheafOpensAddEquiv M U s) :=
  eq_glue hR hm (opensOver U) _ _ fun Z g hg ↦ by
    rw [bigPresheafOpensAddEquiv_apply, bigPresheafOpensAddEquiv_apply]
    have hU : ⊤ ≤ U.ι ⁻¹ᵁ U := (Scheme.Opens.ι_preimage_self U).ge
    have hZ : ⊤ ≤ Z.hom ⁻¹ᵁ U := by
      rw [← Over.w g]
      exact fun z _ ↦ (g.left z).property
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
  apply (bigPresheafOpensAddEquiv N U).injective
  rw [sectionsEquiv_app_eq_glue hR hm φ hφ, bigPresheafOpensAddEquiv_glued_app]

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
