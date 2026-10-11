/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.StructurePresheaf
public import TauCeti.Topology.Category.TopCommRingCat.Sheaf

import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sections of `𝒪_𝒳` over the image of a wandering open

Let `q : 𝒴 → 𝒳 = 𝒴 / φ^ℤ` be the projection onto the Frobenius orbit space, and let `𝒪_𝒳` be its
structure presheaf, whose sections over `U ⊆ 𝒳` are the Frobenius-invariant sections of `𝒪_𝒴`
over `q⁻¹U` (`TauCeti.FarguesFontaine.spaXPresheaf`). An open `V ⊆ 𝒴` *wanders* when it meets none
of its nontrivial integer Frobenius translates `φ⁻ᵏ V`; the Frobenius windows `U_n` and `V_n`, and
hence all their open subsets, wander. This file shows that over the image of a wandering open,
`𝒪_𝒳` is computed by `𝒪_𝒴`:

```text
𝒪_𝒳(q V) ≅ 𝒪_𝒴(V),
```

as complete separated topological rings, by restriction, provided `𝒪_𝒴` is a sheaf. The preimage
`q⁻¹(q V)` is the disjoint union of the translates `φ⁻ᵏ V`
(`TauCeti.FarguesFontaine.quotientMap_preimage_image` and
`TauCeti.FarguesFontaine.pairwise_disjoint_preimage_zpow`), and Frobenius carries the sections over
one translate isomorphically onto those over the next. So a Frobenius-invariant section over
`q⁻¹(q V)` is determined by its restriction to `V`, and every section over `V` is such a
restriction, glued from its Frobenius transports to the translates. The topologies agree because
the topology of a sheaf of topological rings is induced from the product over a cover
(`TauCeti.TopCommRingCat.isInducing_restrictionMap_of_isSheafFor`).

Together with the open embeddings of the windows into `𝒳`, this identifies the restriction of
`𝒪_𝒳` to the image of a window with the restriction of `𝒪_𝒴` to the window, on sections.

## Main definitions

* `TauCeti.FarguesFontaine.spaXPresheafRestrict` : the restriction `𝒪_𝒳(q V) → 𝒪_𝒴(V)`.

## Main results

* `TauCeti.FarguesFontaine.isIso_spaXPresheafRestrict` : for a wandering open `V`, restriction
  `𝒪_𝒳(q V) → 𝒪_𝒴(V)` is an isomorphism of complete separated topological rings when `𝒪_𝒴` is a
  sheaf.
* `TauCeti.FarguesFontaine.isIso_spaXPresheafRestrict_of_subset_windowU` and its `V` analogue :
  the same for every open subset of a Frobenius window.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017 notes, §3.1.
* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
-/

public section

noncomputable section

universe v

namespace TauCeti.FarguesFontaine

open CategoryTheory CategoryTheory.Limits Opposite _root_.TopologicalSpace Topology
open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type v} [CommRing R] [TopologicalSpace (WittVector p R)]
  [CharP R p] [PerfectRing R p] {ϖ : R}

/-! ### Frobenius translates -/

section Translate

variable (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-- The integer Frobenius translate `φ⁻ᵏ V = {v | φᵏ v ∈ V}` of an open `V ⊆ 𝒴`. -/
private def translate (V : Opens (spaY p ϖ)) (k : ℤ) : Opens (spaY p ϖ) :=
  ⟨⇑(frobeniusHomeomorph hI ^ k) ⁻¹' V, (frobeniusHomeomorph hI ^ k).continuous.isOpen_preimage _
    V.isOpen⟩

private theorem translate_zero (V : Opens (spaY p ϖ)) : translate hI V 0 = V :=
  Opens.ext <| Set.ext fun v ↦ by simp [translate, Homeomorph.one_apply]

private theorem translate_add_one (V : Opens (spaY p ϖ)) (k : ℤ) :
    translate hI V (k + 1) = (Opens.map (frobeniusTopHom hI)).obj (translate hI V k) :=
  Opens.ext <| by
    rw [Opens.map_coe]
    ext v
    simp [translate, zpow_add_one, Homeomorph.mul_apply]

/-- The image `q V` of an open `V ⊆ 𝒴` in `𝒳`, an open since `q` is an open map. -/
private abbrev quotientImage (V : Opens (spaY p ϖ)) : Opens (spaX hI) :=
  (IsOpenMap.functor (f := quotientTopHom hI) (isOpenQuotientMap_quotientMap hI).isOpenMap).obj V

/-- The open subset `q⁻¹(q V)` of `𝒴`, over which the sections of `𝒪_𝒳` on `q V` live. -/
private abbrev saturation (V : Opens (spaY p ϖ)) : Opens (spaY p ϖ) :=
  (Opens.map (quotientTopHom hI)).obj (quotientImage hI V)

private theorem translate_le_saturation (V : Opens (spaY p ϖ)) (k : ℤ) :
    translate hI V k ≤ saturation hI V := fun v hv ↦ ⟨_, hv, quotientMap_zpow hI k v⟩

private theorem saturation_le_iSup_translate (V : Opens (spaY p ϖ)) :
    saturation hI V ≤ ⨆ k, translate hI V k := fun v hv ↦ by
  have : v ∈ quotientMap hI ⁻¹' (quotientMap hI '' V) := hv
  rw [quotientMap_preimage_image] at this
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp this
  exact Opens.mem_iSup.mpr ⟨k, hk⟩

private theorem le_saturation (V : Opens (spaY p ϖ)) : V ≤ saturation hI V :=
  fun v hv ↦ ⟨v, hv, rfl⟩

end Translate

/-! ### Sections over a wandering open -/

section Wandering

variable [IsTopologicalRing (WittVector p R)] (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-- Restriction from `q⁻¹(q V)` to a Frobenius translate of `V`. -/
private abbrev restrictTranslate (V : Opens (spaY p ϖ)) (k : ℤ) :
    (spaYPresheaf P ϖ).obj (op (saturation hI V)) ⟶
      (spaYPresheaf P ϖ).obj (op (translate hI V k)) :=
  (spaYPresheaf P ϖ).map (homOfLE (translate_le_saturation hI V k)).op

/-- Frobenius identifies the sections over consecutive translates of `V`. -/
private def stepIso (V : Opens (spaY p ϖ)) (k l : ℤ) (hkl : l = k + 1) :
    (spaYPresheaf P ϖ).obj (op (translate hI V k)) ≅
      (spaYPresheaf P ϖ).obj (op (translate hI V l)) :=
  asIso ((spaYPresheafFrobenius P hI).app (op (translate hI V k))) ≪≫
    (spaYPresheaf P ϖ).mapIso (eqToIso (congrArg op (hkl ▸ translate_add_one hI V k).symm))

/-- **Frobenius on `q⁻¹(q V)` shifts the translates of `V`**: restricting the Frobenius image of a
section to `φ⁻ˡ V` is applying Frobenius to its restriction to `φ⁻ᵏ V`, for `l = k + 1`. -/
private theorem pushforwardSpaYPresheafFrobenius_comp_restrictTranslate (V : Opens (spaY p ϖ))
    (k l : ℤ) (hkl : l = k + 1) :
    (pushforwardSpaYPresheafFrobenius P hI).app
        (op (quotientImage hI V)) ≫
        restrictTranslate P hI V l =
      restrictTranslate P hI V k ≫ (stepIso P hI V k l hkl).hom := by
  rw [pushforwardSpaYPresheafFrobenius_app, stepIso, Iso.trans_hom, asIso_hom, ← Category.assoc,
    restrictTranslate, (spaYPresheafFrobenius P hI).naturality]
  simp only [Category.assoc, TopCat.Presheaf.pushforward_obj_map, Functor.mapIso_hom,
    ← Functor.map_comp]
  congr 2

/-- The composite of the Frobenius steps, identifying the sections over `V` with those over its
`k`-th Frobenius translate. -/
private def translateIso (V : Opens (spaY p ϖ)) (k : ℤ) :
    (spaYPresheaf P ϖ).obj (op V) ≅ (spaYPresheaf P ϖ).obj (op (translate hI V k)) :=
  Int.inductionOn' (motive := fun k ↦
      (spaYPresheaf P ϖ).obj (op V) ≅ (spaYPresheaf P ϖ).obj (op (translate hI V k))) k 0
    ((spaYPresheaf P ϖ).mapIso (eqToIso (congrArg op (translate_zero hI V).symm)))
    (fun k _ e ↦ e ≪≫ stepIso P hI V k (k + 1) rfl)
    (fun k _ e ↦ e ≪≫ (stepIso P hI V (k - 1) k (by omega)).symm)

private theorem translateIso_zero (V : Opens (spaY p ϖ)) :
    translateIso P hI V 0 =
      (spaYPresheaf P ϖ).mapIso (eqToIso (congrArg op (translate_zero hI V).symm)) :=
  Int.inductionOn'_self

private theorem translateIso_add_one (V : Opens (spaY p ϖ)) (k l : ℤ) (hkl : l = k + 1) :
    translateIso P hI V l = translateIso P hI V k ≪≫ stepIso P hI V k l hkl := by
  rcases le_or_gt 0 k with hk | hk
  · subst hkl
    exact Int.inductionOn'_add_one hk
  · obtain rfl : k = l - 1 := by omega
    have h : translateIso P hI V (l - 1) =
        translateIso P hI V l ≪≫ (stepIso P hI V (l - 1) l (by omega)).symm :=
      Int.inductionOn'_sub_one (by omega)
    rw [h, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- **An invariant section is determined by its restriction to `V`**: its restriction to each
Frobenius translate of `V` is the Frobenius transport of its restriction to `V`. -/
private theorem spaXPresheafι_app_comp_restrictTranslate (V : Opens (spaY p ϖ)) (k : ℤ) :
    (spaXPresheafι P hI).app
        (op (quotientImage hI V)) ≫
        restrictTranslate P hI V k =
      (spaXPresheafι P hI).app
          (op (quotientImage hI V)) ≫
        (spaYPresheaf P ϖ).map (homOfLE (le_saturation hI V)).op ≫ (translateIso P hI V k).hom := by
  -- invariant sections are moved one translate along by Frobenius
  have hstep (k l : ℤ) (hkl : l = k + 1) : (spaXPresheafι P hI).app (op (quotientImage hI V)) ≫
      restrictTranslate P hI V l = (spaXPresheafι P hI).app (op (quotientImage hI V)) ≫
        restrictTranslate P hI V k ≫ (stepIso P hI V k l hkl).hom := by
    rw [← pushforwardSpaYPresheafFrobenius_comp_restrictTranslate, ← Category.assoc,
      ← NatTrans.comp_app, spaXPresheafι_comp_pushforwardSpaYPresheafFrobenius]
  induction k using Int.induction_on with
  | zero =>
    rw [translateIso_zero, Functor.mapIso_hom, eqToIso.hom, ← Functor.map_comp]
    congr 2
  | succ k ih =>
    rw [hstep k (k + 1) rfl, reassoc_of% ih, translateIso_add_one P hI V k (k + 1) rfl,
      Iso.trans_hom]
  | pred k ih =>
    rw [← cancel_mono (stepIso P hI V (-k - 1) (-k) (by omega)).hom, Category.assoc,
      ← hstep, ih, Category.assoc, Category.assoc, ← Iso.trans_hom,
      ← translateIso_add_one]

/-- When `𝒪_𝒴` is a sheaf, the sections over `q⁻¹(q V)` carry the topology induced by their
restrictions to the Frobenius translates of `V`, which cover `q⁻¹(q V)`. -/
private theorem isInducing_restrictTranslate (h : (spaYPresheaf P ϖ).IsSheaf)
    (V : Opens (spaY p ϖ)) :
    IsInducing fun (s : (spaYPresheaf P ϖ).obj (op (saturation hI V))) (k : ℤ) ↦
      (restrictTranslate P hI V k).hom.1 s := by
  have hO : Presheaf.IsSheaf (Opens.grothendieckTopology _)
      (spaYPresheaf P ϖ ⋙ TopCommRingCat.isCompleteSeparated.ι) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ h
  let S := Sieve.ofArrows (translate hI V) fun k ↦ homOfLE (translate_le_saturation hI V k)
  have hS : S ∈ Opens.grothendieckTopology _ (saturation hI V) := fun v hv ↦ by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (saturation_le_iSup_translate hI V hv)
    exact ⟨_, homOfLE (translate_le_saturation hI V k), Sieve.ofArrows_mk _ _ k, hk⟩
  exact (TopCommRingCat.isInducing_restrictionMap_ofArrows_iff _ _ _).mp
    (TopCommRingCat.isInducing_restrictionMap_of_isSheafFor _ S fun E ↦ hO E S hS)

/-- **Gluing the Frobenius transports.** When `𝒪_𝒴` is a sheaf and `V` wanders, every section `y`
over `V` is the restriction of a Frobenius-invariant section over `q⁻¹(q V)`: its Frobenius
transports to the translates of `V` are compatible, as the translates are disjoint, and glue to an
invariant section. -/
private theorem exists_spaXPresheafι_app_comp_eq (h : (spaYPresheaf P ϖ).IsSheaf)
    {V : Opens (spaY p ϖ)}
    (hV : ∀ k : ℤ, k ≠ 0 → Disjoint (⇑(frobeniusHomeomorph hI ^ k) ⁻¹' (V : Set (spaY p ϖ))) V)
    (y : (spaYPresheaf P ϖ).obj (op V)) :
    ∃ x, ((spaXPresheafι P hI).app (op (quotientImage hI V)) ≫
      (spaYPresheaf P ϖ).map (homOfLE (le_saturation hI V)).op).hom.1 x = y := by
  have hO : Presheaf.IsSheaf (Opens.grothendieckTopology _)
      (spaYPresheaf P ϖ ⋙ TopCommRingCat.isCompleteSeparated.ι) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ h
  let G : TopCat.Sheaf (Type v) (TopCat.of (spaY p ϖ)) :=
    ⟨_, Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _root_.TopCommRingCat) hO⟩
  -- the transports of `y` to the translates of `V`
  let sf (k : ℤ) : (spaYPresheaf P ϖ).obj (op (translate hI V k)) :=
    (translateIso P hI V k).hom.hom.1 y
  have hcompat : TopCat.Presheaf.IsCompatible G.1 (translate hI V) sf := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · congr 3
    -- distinct translates are disjoint, and a sheaf has a single section over `⊥`
    have hbot : translate hI V i ⊓ translate hI V j ≤ ⨆ e : Empty, Empty.elim e := by
      rw [iSup_of_empty, le_bot_iff]
      exact Opens.ext
        (Set.disjoint_iff_inter_eq_empty.mp (pairwise_disjoint_preimage_zpow hI hV hij))
    exact G.eq_of_locally_eq' (fun e : Empty ↦ Empty.elim e) _ (fun e ↦ e.elim) hbot _ _
      fun e ↦ e.elim
  obtain ⟨s, hs, -⟩ := G.existsUnique_gluing' (translate hI V) (saturation hI V)
    (fun k ↦ homOfLE (translate_le_saturation hI V k)) (saturation_le_iSup_translate hI V) sf
    hcompat
  -- `G` is the presheaf of sets underlying `𝒪_𝒴`, so its restriction maps are those of `𝒪_𝒴`
  have hs' (k : ℤ) : (restrictTranslate P hI V k).hom.1 s = sf k := hs k
  -- the glued section is Frobenius-invariant, as Frobenius shifts the transports
  have hinv : ((pushforwardSpaYPresheafFrobenius P hI).app (op (quotientImage hI V))).hom.1 s =
      s := by
    refine G.eq_of_locally_eq' (translate hI V) (saturation hI V)
      (fun k ↦ homOfLE (translate_le_saturation hI V k)) (saturation_le_iSup_translate hI V) _ _
      fun l ↦ ?_
    have hstep := congrArg (fun m ↦ m.hom.1 s)
      (pushforwardSpaYPresheafFrobenius_comp_restrictTranslate P hI V (l - 1) l (by omega))
    have hτ := congrArg (fun e ↦ e.hom.hom.1 y) (translateIso_add_one P hI V (l - 1) l (by omega))
    exact hstep.trans <| (congrArg (stepIso P hI V (l - 1) l (by omega)).hom.hom.1
      (hs' (l - 1))).trans <| hτ.symm.trans (hs' l).symm
  obtain ⟨x, hx⟩ : s ∈ Set.range ((spaXPresheafι P hI).app (op (quotientImage hI V))).hom.1 := by
    rw [range_spaXPresheafι_app]
    exact hinv
  refine ⟨x, ?_⟩
  -- restricting to `V = φ⁰ V` recovers `y`
  have e₀ : (spaYPresheaf P ϖ).map (homOfLE (le_saturation hI V)).op =
      restrictTranslate P hI V 0 ≫
        (spaYPresheaf P ϖ).map (eqToHom (congrArg op (translate_zero hI V))) := by
    rw [← Functor.map_comp]
    congr 2
  have e₁ : ((spaYPresheaf P ϖ).mapIso (eqToIso (congrArg op (translate_zero hI V).symm))).hom ≫
      (spaYPresheaf P ϖ).map (eqToHom (congrArg op (translate_zero hI V))) = 𝟙 _ := by
    rw [Functor.mapIso_hom, eqToIso.hom, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id]
  rw [e₀, ← Category.assoc]
  -- the composite is evaluated one map at a time
  calc ((spaYPresheaf P ϖ).map (eqToHom (congrArg op (translate_zero hI V)))).hom.1
        ((restrictTranslate P hI V 0).hom.1
          (((spaXPresheafι P hI).app (op (quotientImage hI V))).hom.1 x)) = _ :=
        by rw [hx, hs' 0]; dsimp only [sf]; rw [translateIso_zero]; rfl
    _ = y := congrArg (fun m ↦ m.hom.1 y) e₁

/-- **Restriction from `𝒪_𝒳(q V)` to `𝒪_𝒴(V)`** for an open `V ⊆ 𝒴`: a section of `𝒪_𝒳` over
the open image `q V` is a Frobenius-invariant section of `𝒪_𝒴` over `q⁻¹(q V) ⊇ V`, and this map
restricts it to `V`. -/
def spaXPresheafRestrict (V : Opens (spaY p ϖ)) :
    (spaXPresheaf P hI).obj (op ((IsOpenMap.functor (f := quotientTopHom hI)
      (isOpenQuotientMap_quotientMap hI).isOpenMap).obj V)) ⟶ (spaYPresheaf P ϖ).obj (op V) :=
  (spaXPresheafι P hI).app _ ≫
    (spaYPresheaf P ϖ).map ((IsOpenMap.adjunction (f := quotientTopHom hI)
      (isOpenQuotientMap_quotientMap hI).isOpenMap).unit.app V).op

/-- `spaXPresheafRestrict` is the inclusion `𝒪_𝒳(q V) → 𝒪_𝒴(q⁻¹(q V))` followed by restriction
to `V`. -/
theorem spaXPresheafRestrict_def (V : Opens (spaY p ϖ)) :
    spaXPresheafRestrict P hI V = (spaXPresheafι P hI).app _ ≫
      (spaYPresheaf P ϖ).map ((IsOpenMap.adjunction (f := quotientTopHom hI)
      (isOpenQuotientMap_quotientMap hI).isOpenMap).unit.app V).op := (rfl)

/-- **Sections of `𝒪_𝒳` over the image of a wandering open.** Let `V ⊆ 𝒴` be an open set meeting
none of its nontrivial integer Frobenius translates, and suppose that `𝒪_𝒴` is a sheaf. Then
restriction `𝒪_𝒳(q V) → 𝒪_𝒴(V)` is an isomorphism of complete separated topological rings.

Indeed `q⁻¹(q V)` is the disjoint union of the translates `φ⁻ᵏ V`, and a Frobenius-invariant
section over it is the same as a section over `V`, transported to each translate by Frobenius. -/
theorem isIso_spaXPresheafRestrict (h : (spaYPresheaf P ϖ).IsSheaf) {V : Opens (spaY p ϖ)}
    (hV : ∀ k : ℤ, k ≠ 0 → Disjoint (⇑(frobeniusHomeomorph hI ^ k) ⁻¹' (V : Set (spaY p ϖ))) V) :
    IsIso (spaXPresheafRestrict P hI V) := by
  have hr : spaXPresheafRestrict P hI V = (spaXPresheafι P hI).app (op (quotientImage hI V)) ≫
      (spaYPresheaf P ϖ).map (homOfLE (le_saturation hI V)).op := by
    rw [spaXPresheafRestrict_def]
    congr 3
  -- a section of `𝒪_𝒳(q V)` is determined, topologically too, by its restrictions to the
  -- translates of `V`, which are the Frobenius transports of its restriction to `V`
  have hcomp : (fun y (k : ℤ) ↦ (translateIso P hI V k).hom.hom.1 y) ∘
      (spaXPresheafRestrict P hI V).hom.1 =
      (fun s (k : ℤ) ↦ (restrictTranslate P hI V k).hom.1 s) ∘
        ((spaXPresheafι P hI).app (op (quotientImage hI V))).hom.1 := by
    funext x k
    rw [hr]
    exact congrArg (fun m ↦ m.hom.1 x) (spaXPresheafι_app_comp_restrictTranslate P hI V k).symm
  have hind : IsInducing (spaXPresheafRestrict P hI V).hom.1 :=
    .of_comp (spaXPresheafRestrict P hI V).hom.2
      (continuous_pi fun k ↦ (translateIso P hI V k).hom.hom.2) <| hcomp ▸
      (isInducing_restrictTranslate P hI h V).comp
        (isClosedEmbedding_spaXPresheafι_app P hI _).isInducing
  have := ((TopCommRingCat.isCompleteSeparated_iff _).mp
    ((spaXPresheaf P hI).obj (op (quotientImage hI V))).property).t0Space
  have hsurj : Function.Surjective (spaXPresheafRestrict P hI V).hom.1 := fun y ↦ by
    simpa only [hr] using exists_spaXPresheafι_app_comp_eq P hI h hV y
  -- a bijective inducing map is a homeomorphism, so `r` is an isomorphism of topological rings
  have hhomeo : IsHomeomorph (spaXPresheafRestrict P hI V).hom.1 :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, hind.injective⟩, hsurj⟩
  have : IsIso ((forget₂ _root_.TopCommRingCat TopCat).map (spaXPresheafRestrict P hI V).hom) :=
    (TopCat.isIso_iff_isHomeomorph _).mpr hhomeo
  have : IsIso (spaXPresheafRestrict P hI V).hom :=
    isIso_of_reflects_iso _ (forget₂ _root_.TopCommRingCat TopCat)
  have : IsIso (TopCommRingCat.isCompleteSeparated.ι.map (spaXPresheafRestrict P hI V)) := this
  exact isIso_of_fully_faithful TopCommRingCat.isCompleteSeparated.ι _

/-- **Sections of `𝒪_𝒳` over the image of an open inside a `U` window.** If `𝒪_𝒴` is a sheaf and
`V ⊆ U_n` is open, restriction `𝒪_𝒳(q V) → 𝒪_𝒴(V)` is an isomorphism of complete separated
topological rings. -/
theorem isIso_spaXPresheafRestrict_of_subset_windowU (h : (spaYPresheaf P ϖ).IsSheaf) (n : ℤ)
    {V : Opens (spaY p ϖ)} (hV : (V : Set (spaY p ϖ)) ⊆ Subtype.val ⁻¹' windowU p ϖ n) :
    IsIso (spaXPresheafRestrict P hI V) :=
  isIso_spaXPresheafRestrict P hI h fun _ hk ↦
    (disjoint_preimage_zpow_windowU hI n hk).mono (Set.preimage_mono hV) hV

/-- **Sections of `𝒪_𝒳` over the image of an open inside a `V` window.** If `𝒪_𝒴` is a sheaf and
`V ⊆ V_n` is open, restriction `𝒪_𝒳(q V) → 𝒪_𝒴(V)` is an isomorphism of complete separated
topological rings. -/
theorem isIso_spaXPresheafRestrict_of_subset_windowV (h : (spaYPresheaf P ϖ).IsSheaf) (n : ℤ)
    {V : Opens (spaY p ϖ)} (hV : (V : Set (spaY p ϖ)) ⊆ Subtype.val ⁻¹' windowV p ϖ n) :
    IsIso (spaXPresheafRestrict P hI V) :=
  isIso_spaXPresheafRestrict P hI h fun _ hk ↦
    (disjoint_preimage_zpow_windowV hI n hk).mono (Set.preimage_mono hV) hV

end Wandering

end TauCeti.FarguesFontaine
