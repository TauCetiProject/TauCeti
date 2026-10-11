/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.WindowSections
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Descent
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.OpenImmersion
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Sheaf

import TauCeti.CategoryTheory.Thin

/-!
# The Frobenius orbit space as a pre-adic space

Let `R` be a perfect ring of characteristic `p` and give the Witt vectors `𝕎 R` the `(p, [ϖ])`-adic
topology; for `R = 𝒪_F` this is `A_inf`. The adic Fargues–Fontaine curve is the orbit space
`𝒳 = 𝒴 / φ^ℤ` of the open subset `𝒴 = D(p) ∩ D([ϖ])` of `Spa(𝕎 R, 𝕎 R)` under Witt Frobenius, with
the structure presheaf `𝒪_𝒳(U) = 𝒪_𝒴(q⁻¹U)^{φ=1}` (`TauCeti.FarguesFontaine.spaXPresheaf`). This
file makes `𝒳` an object of Wedhorn's category `𝒱^pre` of pre-adic spaces and identifies its charts
on wandering opens, such as the Frobenius windows, with the corresponding pieces of `𝒴`.

* `𝒴` is the pre-adic space obtained by restricting `Spa(𝕎 R, 𝕎 R)`, and Frobenius acts on it by
  an endomorphism in `𝒱^pre`, the restriction of the automorphism of `Spa(𝕎 R, 𝕎 R)` induced by
  `φ`; on sections it is `spaYPresheafFrobenius`.
* The projection `q : 𝒴 → 𝒳`, with the inclusion of the Frobenius-invariant sections, is a
  morphism of presheafed spaces, and it is invariant under Frobenius.
* Suppose that `𝒪_𝒴` is a sheaf. On an open `V ⊆ 𝒴` meeting none of its nontrivial Frobenius
  translates, `q` is an open embedding along which `𝒪_𝒳` restricts to `𝒪_𝒴`
  (`TauCeti.FarguesFontaine.isIso_spaXPresheafRestrict`), so `V → 𝒳` is an open immersion. Every
  point of `𝒴` lies in such an open, a Frobenius window, so the stalk maps of `q` are isomorphisms:
  the stalks of `𝒪_𝒳` are local, and the stalk at `q y` receives the valuation of `𝒴` at `y`.
  Frobenius preserves these valuations, so they do not depend on the point `y` of the orbit, and
  `PreAdicSpace.descend` makes `𝒳` a pre-adic space with `q` a morphism of `𝒱^pre`.

The sheaf condition on `𝒪_𝒴` is a hypothesis throughout, as for `isSheaf_spaXPresheaf` and
`isIso_spaXPresheafRestrict`; it is not proved here.

## Main definitions

* `TauCeti.FarguesFontaine.spaYPreAdicSpace`: `𝒴` as a pre-adic space.
* `TauCeti.FarguesFontaine.spaYFrobenius`: Witt Frobenius as an endomorphism of `𝒴` in `𝒱^pre`.
* `TauCeti.FarguesFontaine.quotientPresheafedHom`: the projection `q : 𝒴 → 𝒳` of presheafed
  spaces.
* `TauCeti.FarguesFontaine.spaXPreAdicSpace`: `𝒳` as a pre-adic space, when `𝒪_𝒴` is a sheaf.
* `TauCeti.FarguesFontaine.quotientPreAdicHom`: the projection `q` as a morphism of pre-adic
  spaces.

## Main results

* `TauCeti.FarguesFontaine.spaYFrobenius_toHom_comp_quotientPresheafedHom`: `q ∘ φ = q` as
  morphisms of presheafed spaces.
* `TauCeti.FarguesFontaine.isOpenImmersion_ofRestrict_comp_quotientPresheafedHom`: `V → 𝒳` is an
  open immersion for every wandering open `V`.
* `TauCeti.FarguesFontaine.isIso_stalkMap_quotientPresheafedHom`: the stalk maps of `q` are
  isomorphisms.
* `TauCeti.FarguesFontaine.isSheafy_spaXPreAdicSpace`: the pre-adic space `𝒳` is sheafy.
* `TauCeti.FarguesFontaine.isOpenImmersion_ofRestrict_comp_quotientPreAdicHom`: the window charts
  `V → 𝒳` are open immersions of pre-adic spaces.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1, for the category `𝒱^pre`.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017 notes, §3.1.
* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018), Chapter 1.
-/

public section

noncomputable section

universe v

namespace TauCeti.FarguesFontaine

open AlgebraicGeometry _root_.CategoryTheory Opposite _root_.TopologicalSpace Topology
open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type v} [CommRing R] [TopologicalSpace (WittVector p R)]
  [IsTopologicalRing (WittVector p R)] {ϖ : R}
  (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-! ### `𝒴` as a pre-adic space -/

-- The construction is exposed, as `PreAdicSpace.restrict` is: a point of `𝒴` must be a point of
-- this pre-adic space, and its presheaf `spaYPresheaf`, for the Frobenius action and the
-- projection to `𝒳` to be morphisms out of it.
@[expose] public section SpaYDef

/-- `Spa(𝕎 R, 𝕎 R)` with its presentation-limit structure presheaf, as a pre-adic space. Every
element of the `(p, [ϖ])`-adic ring `𝕎 R` is power-bounded, so `𝕎 R` is a plus ring of itself. -/
abbrev spaPreAdicSpace : PreAdicSpace.{v} :=
  presentationLimitPreAdicSpace P (⊤ : Subring (WittVector p R))
    (fun _ _ ↦ haveI := hI.isLinearTopology
      isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) le_top

/-- **`𝒴` as a pre-adic space**: the restriction of the pre-adic space `Spa(𝕎 R, 𝕎 R)` to the open
subset `𝒴 = D(p) ∩ D([ϖ])`. Its presheaf is `𝒪_𝒴 = spaYPresheaf P ϖ`. -/
def spaYPreAdicSpace : PreAdicSpace.{v} :=
  (spaPreAdicSpace P hI).restrict (isOpenEmbedding_spaYInclusion p ϖ)

end SpaYDef

/-- The presheaf of the pre-adic space `𝒴` is `𝒪_𝒴`. -/
theorem spaYPreAdicSpace_presheaf :
    (spaYPreAdicSpace P hI).toPresheafedSpace.presheaf = spaYPresheaf P ϖ :=
  (rfl)

/-! ### Frobenius on `𝒴` -/

variable [CharP R p] [PerfectRing R p]

/-- Witt Frobenius on `𝒴` as a morphism of presheafed spaces: `v ↦ v ∘ φ` on points, and
`spaYPresheafFrobenius` on sections. It underlies the morphism of pre-adic spaces
`spaYFrobenius`. -/
@[expose]
def spaYFrobeniusHom :
    (spaYPreAdicSpace P hI).toPresheafedSpace ⟶ (spaYPreAdicSpace P hI).toPresheafedSpace where
  base := frobeniusTopHom hI
  c := spaYPresheafFrobenius P hI

/-- Frobenius on `𝒴` is compatible with Frobenius on `Spa(𝕎 R, 𝕎 R)` along the inclusion. -/
private theorem spaYFrobeniusHom_comp_ofRestrict :
    spaYFrobeniusHom P hI ≫ ((spaPreAdicSpace P hI).ofRestrict
      (isOpenEmbedding_spaYInclusion p ϖ)).toHom =
    (((spaPreAdicSpace P hI).ofRestrict
      (isOpenEmbedding_spaYInclusion p ϖ)) ≫
      (presentationLimitPreAdicSpaceFrobeniusIso P hI).hom).toHom := by
  -- on sections, Frobenius of `Spa(𝕎 R, 𝕎 R)` is the transport of the structure presheaf
  refine Eq.trans ?_
    (congrArg (fun t ↦ _ ≫ t) (presentationLimitPreAdicSpaceComapIso_hom_toHom ..)).symm
  refine PresheafedSpace.ext _ _ ?_ ?_
  · ext v
    exact Subtype.ext ((spaYInclusion_apply_val ϖ _).trans
      ((frobeniusHomeomorph_apply_val hI v).trans
        ((congrArg (comap WittVector.frobenius) (spaYInclusion_apply_val ϖ v)).symm.trans
          (spaComap_val ..).symm)))
  · refine NatTrans.ext (funext fun W ↦ ?_)
    refine Eq.trans (congrArg (fun t ↦ (_ ≫ t) ≫ _) (spaYPresheafFrobenius_app P hI _)) ?_
    -- the casts in `spaYPresheafFrobenius_app` relate objects that are only definitionally
    -- equal, so `eqToHom_refl` cannot remove them; unification absorbs them instead
    exact (presentationLimitPresheafFrobeniusIso P hI).hom.map_comp_app_comp_map_comp_map
      _ rfl _ rfl _ _

/-- **Witt Frobenius as an endomorphism of the pre-adic space `𝒴`**: on points it is `v ↦ v ∘ φ`
and on sections it is `spaYPresheafFrobenius` (`spaYFrobenius_toHom`). It is compatible with the
stalk valuations, being the restriction to `𝒴` of the automorphism of `Spa(𝕎 R, 𝕎 R)` induced by
`φ`. -/
def spaYFrobenius : spaYPreAdicSpace P hI ⟶ spaYPreAdicSpace P hI :=
  -- the inclusion of `𝒴` is typed into `Spa(𝕎 R, 𝕎 R)` rather than into the underlying space of
  -- its pre-adic space, so the open-immersion instance of the inclusion is supplied by hand
  PreAdicSpace.Hom.ofFac
    (i := (spaPreAdicSpace P hI).ofRestrict _ ≫
      (presentationLimitPreAdicSpaceFrobeniusIso P hI).hom)
    (j := (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ))
    (g := spaYFrobeniusHom P hI)
    (hj := fun _ ↦ @PreAdicSpace.IsOpenImmersion.isIso_stalkMap _ _ _
      (PreAdicSpace.IsOpenImmersion.ofRestrict _ (isOpenEmbedding_spaYInclusion p ϖ)) _)
    (spaYFrobeniusHom_comp_ofRestrict P hI)

/-- The underlying morphism of presheafed spaces of `spaYFrobenius`. -/
@[simp]
theorem spaYFrobenius_toHom : (spaYFrobenius P hI).toHom = spaYFrobeniusHom P hI := by
  -- instance search cannot find the stalk-isomorphism instance that `spaYFrobenius` supplies by
  -- hand, so `PreAdicSpace.Hom.ofFac_toHom` is applied to the unfolded definition with all of its
  -- arguments, including that instance, read off by unification
  unfold spaYFrobenius
  exact @PreAdicSpace.Hom.ofFac_toHom ..

/-! ### The projection to `𝒳` -/

-- The presheafed space and the projection are exposed: a point of `𝒳` must be a point of
-- `spaXPresheafedSpace`, and the projection must unfold to `q` and to the inclusion of the
-- Frobenius-invariant sections, for the stalk maps of the projection to typecheck.
@[expose] public section SpaXDef

/-- The Frobenius orbit space `𝒳` with its structure presheaf `𝒪_𝒳`, as a presheafed space of
complete separated topological rings. -/
def spaXPresheafedSpace : PresheafedSpace CompleteSeparatedTopCommRingCat.{v} where
  carrier := TopCat.of (spaX hI)
  presheaf := spaXPresheaf P hI

/-- **The projection `q : 𝒴 → 𝒳`** as a morphism of presheafed spaces: on sections it is the
inclusion `𝒪_𝒳(U) → 𝒪_𝒴(q⁻¹U)` of the Frobenius-invariant sections. -/
def quotientPresheafedHom :
    (spaYPreAdicSpace P hI).toPresheafedSpace ⟶ spaXPresheafedSpace P hI where
  base := quotientTopHom hI
  c := spaXPresheafι P hI

end SpaXDef

/-- **The projection to `𝒳` is Frobenius-invariant**, as a morphism of presheafed spaces: on
points because `q ∘ φ = q`, on sections because the sections of `𝒪_𝒳` are Frobenius-invariant. -/
theorem spaYFrobenius_toHom_comp_quotientPresheafedHom :
    (spaYFrobenius P hI).toHom ≫ quotientPresheafedHom P hI = quotientPresheafedHom P hI := by
  -- the invariance of the sections of `𝒪_𝒳`, on each open of `𝒳`
  have h (U : (Opens (spaX hI))ᵒᵖ) := by
    have h := congrArg (fun f ↦ NatTrans.app f U)
      (spaXPresheafι_comp_pushforwardSpaYPresheafFrobenius P hI)
    rw [NatTrans.comp_app, pushforwardSpaYPresheafFrobenius_app] at h
    exact h
  rw [spaYFrobenius_toHom]
  refine PresheafedSpace.ext _ _ (frobeniusTopHom_comp_quotientTopHom hI) ?_
  -- the two restriction maps to `q⁻¹U` agree, as the opens of `𝒴` form a thin category
  exact NatTrans.ext (funext fun U ↦ (Category.assoc _ _ _).trans
    ((congrArg (fun t ↦ _ ≫ _ ≫ (spaYPresheaf P ϖ).map t) (Subsingleton.elim _ _)).trans (h U)))

/-! ### Charts on wandering opens -/

section Wandering

variable {P hI}

/-- Over the image `q V` of a wandering open `V`, the inclusion of the Frobenius-invariant sections
followed by restriction to `V` is an isomorphism, whatever form the image and `V` are given in. -/
private theorem isIso_spaXPresheafι_app_comp_map (h : (spaYPresheaf P ϖ).IsSheaf)
    {U : Opens (spaX hI)} {V V' : Opens (spaY p ϖ)}
    (hV : ∀ k : ℤ, k ≠ 0 → Disjoint (⇑(frobeniusHomeomorph hI ^ k) ⁻¹' (V : Set (spaY p ϖ))) V)
    (hU : U = (IsOpenMap.functor (f := quotientTopHom hI)
      (isOpenQuotientMap_quotientMap hI).isOpenMap).obj V) (hV' : V' = V)
    (k : op ((Opens.map (quotientTopHom hI)).obj U) ⟶ op V') :
    IsIso ((spaXPresheafι P hI).app (op U) ≫ (spaYPresheaf P ϖ).map k) := by
  subst hU hV'
  rw [Subsingleton.elim k ((IsOpenMap.adjunction (f := quotientTopHom hI)
    (isOpenQuotientMap_quotientMap hI).isOpenMap).unit.app V').op, ← spaXPresheafRestrict_def]
  exact isIso_spaXPresheafRestrict P hI h hV

/-- **The projection is an open immersion on every wandering open.** If `𝒪_𝒴` is a sheaf and the
open `V ⊆ 𝒴` meets none of its nontrivial integer Frobenius translates, then `V → 𝒳`, the
inclusion followed by the projection, is an open immersion of presheafed spaces: it is an open
embedding, and over each open of its image it identifies the sections of `𝒪_𝒳` with those of
`𝒪_𝒴`. -/
theorem isOpenImmersion_ofRestrict_comp_quotientPresheafedHom (h : (spaYPresheaf P ϖ).IsSheaf)
    {V : Opens (spaY p ϖ)}
    (hV : ∀ k : ℤ, k ≠ 0 → Disjoint (⇑(frobeniusHomeomorph hI ^ k) ⁻¹' (V : Set (spaY p ϖ))) V) :
    PresheafedSpace.IsOpenImmersion
      ((spaYPreAdicSpace P hI).toPresheafedSpace.ofRestrict V.isOpenEmbedding ≫
        quotientPresheafedHom P hI) where
  base_open := isOpenEmbedding_quotientMap_restrict hI V V.isOpen
    (injOn_quotientMap_of_disjoint_preimage_zpow hI hV)
  c_iso W := by
    -- the image of `W` in `𝒴`
    let W' := (IsOpenMap.functor (f := Opens.inclusion' (X := TopCat.of (spaY p ϖ)) V)
      (Opens.isOpenEmbedding (X := TopCat.of (spaY p ϖ)) V).isOpenMap).obj W
    have hsub : (W' : Set (spaY p ϖ)) ⊆ V := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    refine isIso_spaXPresheafι_app_comp_map h (V := W')
      (fun k hk ↦ (hV k hk).mono (Set.preimage_mono hsub) hsub) ?_ ?_ _
    · -- the image of `W` under `V → 𝒴 → 𝒳` is the image under `q` of its image in `𝒴`
      exact Opens.ext (Set.ext fun x ↦ ⟨fun ⟨w, hw, hx⟩ ↦ ⟨_, ⟨w, hw, rfl⟩, hx⟩,
        fun ⟨_, ⟨w, hw, rfl⟩, hx⟩ ↦ ⟨w, hw, hx⟩⟩)
    · -- the projection is injective on `V`, so `W` is the preimage of its image
      have hinj : Function.Injective fun v : V ↦ quotientMap hI v.val :=
        (injOn_quotientMap_of_disjoint_preimage_zpow hI hV).injective
      exact Opens.ext (congrArg (Subtype.val '' ·) (hinj.preimage_image _))

/-- **The stalk maps of the projection are isomorphisms** when `𝒪_𝒴` is a sheaf: every point of
`𝒴` lies in a wandering window, on which the projection is an open immersion. -/
theorem isIso_stalkMap_quotientPresheafedHom (h : (spaYPresheaf P ϖ).IsSheaf) (y : spaY p ϖ) :
    IsIso ((PreAdicSpace.toRingPresheafedSpaceHom
      (X := spaYPreAdicSpace P hI) (quotientPresheafedHom P hI)).stalkMap y) := by
  obtain ⟨V, hV, hy⟩ := exists_wandering_open_mem hI y
  let o := (spaYPreAdicSpace P hI).ofRestrict V.isOpenEmbedding
  let y' : (spaYPreAdicSpace P hI).restrict V.isOpenEmbedding := ⟨y, hy⟩
  have := isOpenImmersion_ofRestrict_comp_quotientPresheafedHom h hV
  -- the open immersion `V → 𝒳` stays one after forgetting the topology on sections
  have : PresheafedSpace.IsOpenImmersion (PreAdicSpace.toRingPresheafedSpaceHom o.toHom ≫
      PreAdicSpace.toRingPresheafedSpaceHom (quotientPresheafedHom P hI)) :=
    Functor.map_comp (TopCommRingCat.isCompleteSeparated.ι ⋙
      forget₂ TopCommRingCat CommRingCat).mapPresheaf o.toHom (quotientPresheafedHom P hI) ▸
      PresheafedSpace.IsOpenImmersion.mapPresheaf_map _ (o.toHom ≫ quotientPresheafedHom P hI)
        (H := this)
  -- the stalk maps of the inclusion of `V`, an open immersion of pre-adic spaces, are invertible
  have : IsIso ((PreAdicSpace.toRingPresheafedSpaceHom o.toHom).stalkMap y') :=
    PreAdicSpace.Hom.stalkMap_def o y' ▸
      PreAdicSpace.IsOpenImmersion.isIso_stalkMap ((spaYPreAdicSpace P hI).ofRestrict _) y'
  exact PresheafedSpace.isIso_stalkMap_of_isOpenImmersion_comp
    (PreAdicSpace.toRingPresheafedSpaceHom o.toHom)
    (PreAdicSpace.toRingPresheafedSpaceHom (quotientPresheafedHom P hI)) y'

end Wandering

/-! ### The pre-adic space `𝒳` -/

section SpaX

variable {P hI}

variable (P hI) in
/-- The valuation on the stalk of `𝒳` at `q y` descended from `y`: the stalk valuation of `𝒴` at
`y`, pulled back along the stalk map of the projection. -/
private def descendedValuation (y : spaY p ϖ) :=
  ValuationSpectrum.comap
    ((PreAdicSpace.toRingPresheafedSpaceHom (quotientPresheafedHom P hI)).stalkMap y).hom
    ((spaYPreAdicSpace P hI).stalkValuation y)

/-- Frobenius does not change the descended valuation. -/
private theorem heq_descendedValuation_frobenius (y : spaY p ϖ) :
    HEq (descendedValuation P hI (frobeniusHomeomorph hI y)) (descendedValuation P hI y) := by
  have hb : (spaYFrobenius P hI).base y = frobeniusHomeomorph hI y :=
    congrArg (fun f ↦ f.base y) (spaYFrobenius_toHom P hI)
  have h₀ : (quotientPresheafedHom P hI).base y =
      (quotientPresheafedHom P hI).base ((spaYFrobenius P hI).base y) :=
    (congrArg (fun f ↦ f.base y) (spaYFrobenius_toHom_comp_quotientPresheafedHom P hI)).symm
  exact (congr_arg_heq (descendedValuation P hI) hb).symm.trans
    ((ValuationSpectrum.comap_eqToHom_eq_iff_heq _ h₀.symm _ _).mp
      (PreAdicSpace.comap_stalkMap_base_eq_of_comp_eq (spaYFrobenius P hI)
        (spaYFrobenius_toHom_comp_quotientPresheafedHom P hI) y h₀))

/-- Integer powers of Frobenius do not change the descended valuation. -/
private theorem heq_descendedValuation_zpow (n : ℤ) (y : spaY p ϖ) :
    HEq (descendedValuation P hI ((frobeniusHomeomorph hI ^ n) y)) (descendedValuation P hI y) := by
  induction n using Int.induction_on generalizing y with
  | zero => exact congr_arg_heq (descendedValuation P hI) (by simp [Homeomorph.one_apply])
  | succ n ih =>
    rw [add_comm, zpow_one_add, Homeomorph.mul_apply]
    exact (heq_descendedValuation_frobenius _).trans (ih y)
  | pred n ih =>
    have e : frobeniusHomeomorph hI ((frobeniusHomeomorph hI ^ (-(n : ℤ) - 1)) y) =
        (frobeniusHomeomorph hI ^ (-(n : ℤ))) y := by
      rw [← Homeomorph.mul_apply, ← zpow_one_add]
      congr 2
      omega
    exact (heq_descendedValuation_frobenius _).symm.trans
      ((congr_arg_heq (descendedValuation P hI) e).trans (ih y))

/-- **The descended valuations do not depend on the representative of an orbit**: the compatibility
hypothesis of `PreAdicSpace.descend` for the projection `𝒴 → 𝒳`. -/
private theorem comap_stalkMap_quotientPresheafedHom_eq (y y' : spaY p ϖ)
    (h : (quotientPresheafedHom P hI).base y = (quotientPresheafedHom P hI).base y') :
    descendedValuation P hI y' = ValuationSpectrum.comap (eqToHom (congrArg
      ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).mapPresheaf.obj
        (spaXPresheafedSpace P hI)).presheaf.stalk h.symm)).hom (descendedValuation P hI y) := by
  obtain ⟨n, rfl⟩ := (quotientMap_eq_iff hI y y').mp h
  exact (ValuationSpectrum.comap_eqToHom_eq_iff_heq _ h.symm _ _).mpr
    (heq_descendedValuation_zpow n y').symm

-- The pre-adic space is exposed, as `PreAdicSpace.descend` is: a point of `𝒳` must be a point of
-- this pre-adic space for the projection and its charts on wandering opens to be stated.
@[expose] public section SpaXPreAdicDef

variable (P hI) in
/-- **The Frobenius orbit space `𝒳 = 𝒴 / φ^ℤ` as a pre-adic space**, when `𝒪_𝒴` is a sheaf. Its
presheaf is `𝒪_𝒳`, the Frobenius-invariant sections of `𝒪_𝒴`; the stalk of `𝒪_𝒳` at `q y` is the
stalk of `𝒪_𝒴` at `y` through the projection, hence local, and carries the valuation of `𝒴` at `y`,
which does not depend on the point `y` of the orbit. -/
def spaXPreAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) : PreAdicSpace.{v} :=
  (spaYPreAdicSpace P hI).descend (quotientPresheafedHom P hI)
    (isOpenQuotientMap_quotientMap hI).surjective (isIso_stalkMap_quotientPresheafedHom h)

end SpaXPreAdicDef

variable (P hI) in
/-- **The projection `𝒴 → 𝒳` as a morphism of pre-adic spaces**, when `𝒪_𝒴` is a sheaf. -/
def quotientPreAdicHom (h : (spaYPresheaf P ϖ).IsSheaf) :
    spaYPreAdicSpace P hI ⟶ spaXPreAdicSpace P hI h :=
  PreAdicSpace.toDescend _ _ comap_stalkMap_quotientPresheafedHom_eq

/-- The presheafed space underlying the pre-adic space `𝒳` is `(𝒳, 𝒪_𝒳)`. -/
@[simp]
theorem spaXPreAdicSpace_toPresheafedSpace (h : (spaYPresheaf P ϖ).IsSheaf) :
    (spaXPreAdicSpace P hI h).toPresheafedSpace = spaXPresheafedSpace P hI :=
  (rfl)

/-- The morphism of presheafed spaces underlying the pre-adic projection is `q`. -/
@[simp]
theorem quotientPreAdicHom_toHom (h : (spaYPresheaf P ϖ).IsSheaf) :
    (quotientPreAdicHom P hI h).toHom = quotientPresheafedHom P hI :=
  PreAdicSpace.toDescend_toHom ..

/-- **The pre-adic space `𝒳` is sheafy** when `𝒪_𝒴` is a sheaf. -/
theorem isSheafy_spaXPreAdicSpace (h : (spaYPresheaf P ϖ).IsSheaf) :
    PreAdicSpace.isSheafy (spaXPreAdicSpace P hI h) :=
  isSheaf_spaXPresheaf P hI h

/-- **The projection to `𝒳` is Frobenius-invariant** as a morphism of pre-adic spaces. -/
@[reassoc (attr := simp)]
theorem spaYFrobenius_comp_quotientPreAdicHom (h : (spaYPresheaf P ϖ).IsSheaf) :
    spaYFrobenius P hI ≫ quotientPreAdicHom P hI h = quotientPreAdicHom P hI h :=
  PreAdicSpace.Hom.ext' (by
    rw [PreAdicSpace.comp_toHom, quotientPreAdicHom_toHom]
    exact spaYFrobenius_toHom_comp_quotientPresheafedHom P hI)

/-- **The window charts of `𝒳`.** If `𝒪_𝒴` is a sheaf and the open `V ⊆ 𝒴` meets none of its
nontrivial integer Frobenius translates, as every open subset of a Frobenius window does, then
`V → 𝒳`, the inclusion followed by the projection, is an open immersion of pre-adic spaces, so
that `PreAdicSpace.IsOpenImmersion.isoRestrict` identifies `𝒴` restricted to `V` with `𝒳`
restricted to the open image `q V`, as objects of `𝒱^pre`. -/
theorem isOpenImmersion_ofRestrict_comp_quotientPreAdicHom (h : (spaYPresheaf P ϖ).IsSheaf)
    {V : Opens (spaY p ϖ)}
    (hV : ∀ k : ℤ, k ≠ 0 → Disjoint (⇑(frobeniusHomeomorph hI ^ k) ⁻¹' (V : Set (spaY p ϖ))) V) :
    PreAdicSpace.IsOpenImmersion
      ((spaYPreAdicSpace P hI).ofRestrict V.isOpenEmbedding ≫ quotientPreAdicHom P hI h) := by
  rw [PreAdicSpace.IsOpenImmersion, PreAdicSpace.comp_toHom, quotientPreAdicHom_toHom]
  exact isOpenImmersion_ofRestrict_comp_quotientPresheafedHom h hV

end SpaX

end TauCeti.FarguesFontaine
