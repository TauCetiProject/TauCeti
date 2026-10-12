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
  `PreAdicSpace.descend`, applied to `q` alone, makes `𝒳` a pre-adic space with `q` a morphism
  of `𝒱^pre`.
* `𝒳` is the quotient of `𝒴` by Frobenius: a morphism out of `𝒴` with `φ ≫ g = g` factors
  uniquely through `q`, so `q` is the coequalizer of the identity and Frobenius, among presheafed
  spaces and, when `𝒪_𝒴` is a sheaf, in `𝒱^pre`. On points the factorization is the induced map of
  orbit spaces; on sections it takes values in the Frobenius-invariant sections of `𝒪_𝒴`, which are
  those of `𝒪_𝒳`.

The sheaf condition on `𝒪_𝒴` is a hypothesis for the window charts and the stalks of `𝒳`, for `𝒳`
as a pre-adic space and for the universal property in `𝒱^pre`, as for `isSheaf_spaXPresheaf` and
`isIso_spaXPresheafRestrict`; it is not proved here. Frobenius on `𝒴`, the projection `q` and its
universal property among presheafed spaces do not need it.

## Main definitions

* `TauCeti.FarguesFontaine.spaYPreAdicSpace`: `𝒴` as a pre-adic space.
* `TauCeti.FarguesFontaine.spaYFrobenius`: Witt Frobenius as an endomorphism of `𝒴` in `𝒱^pre`.
* `TauCeti.FarguesFontaine.quotientPresheafedHom`: the projection `q : 𝒴 → 𝒳` of presheafed
  spaces.
* `TauCeti.FarguesFontaine.spaXPreAdicSpace`: `𝒳` as a pre-adic space, when `𝒪_𝒴` is a sheaf.
* `TauCeti.FarguesFontaine.quotientPreAdicHom`: the projection `q` as a morphism of pre-adic
  spaces.
* `TauCeti.FarguesFontaine.quotientPresheafedDesc` and
  `TauCeti.FarguesFontaine.quotientPreAdicDesc`: the factorization through `q` of a
  Frobenius-invariant morphism out of `𝒴`.

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
* `TauCeti.FarguesFontaine.spaYFrobenius_comp_ofRestrict`: Frobenius on `𝒴` is the restriction of
  Frobenius on `Spa(𝕎 R, 𝕎 R)`.
* `TauCeti.FarguesFontaine.isColimitQuotientPresheafedCofork` and
  `TauCeti.FarguesFontaine.isColimitQuotientPreAdicCofork`: `q` is the coequalizer of the
  identity and Frobenius on `𝒴`, among presheafed spaces and in `𝒱^pre`; uniqueness is
  `quotientPresheafedHom_hom_ext` and `quotientPreAdicHom_hom_ext`.

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

/-- **Frobenius on `𝒴` is the restriction of Frobenius on `Spa(𝕎 R, 𝕎 R)`**: the inclusion of `𝒴`
intertwines `spaYFrobenius` with the automorphism of `Spa(𝕎 R, 𝕎 R)` induced by `φ`. -/
@[reassoc]
theorem spaYFrobenius_comp_ofRestrict :
    spaYFrobenius P hI ≫ (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ) =
      (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ) ≫
        (presentationLimitPreAdicSpaceFrobeniusIso P hI).hom :=
  PreAdicSpace.Hom.ext' ((congrArg (· ≫ _) (spaYFrobenius_toHom P hI)).trans
    (spaYFrobeniusHom_comp_ofRestrict P hI))

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

omit [IsTopologicalRing (WittVector p R)] in
variable {hI} in
/-- A function on `𝒴`, possibly dependent, that is invariant under Frobenius is invariant under
every integer power of Frobenius. -/
private theorem heq_zpow_apply_of_heq_frobenius {β : spaY p ϖ → Sort*} (F : ∀ y, β y)
    (hF : ∀ y, HEq (F (frobeniusHomeomorph hI y)) (F y)) (n : ℤ) (y : spaY p ϖ) :
    HEq (F ((frobeniusHomeomorph hI ^ n) y)) (F y) := by
  induction n using Int.induction_on generalizing y with
  | zero => exact congr_arg_heq F (by simp [Homeomorph.one_apply])
  | succ n ih =>
    rw [add_comm, zpow_one_add, Homeomorph.mul_apply]
    exact (hF _).trans (ih y)
  | pred n ih =>
    have e : frobeniusHomeomorph hI ((frobeniusHomeomorph hI ^ (-(n : ℤ) - 1)) y) =
        (frobeniusHomeomorph hI ^ (-(n : ℤ))) y := by
      rw [← Homeomorph.mul_apply, ← zpow_one_add]
      congr 2
      omega
    exact (hF _).symm.trans ((congr_arg_heq F e).trans (ih y))

/-! ### The universal property of the projection -/

section Desc

open CategoryTheory.Limits

variable {P hI} {W : PresheafedSpace CompleteSeparatedTopCommRingCat.{v}}
  {g : (spaYPreAdicSpace P hI).toPresheafedSpace ⟶ W}

/-- A Frobenius-invariant morphism out of `𝒴` is invariant on points under every integer power of
Frobenius. -/
private theorem base_zpow_apply_of_comp_eq (hg : (spaYFrobenius P hI).toHom ≫ g = g) (n : ℤ)
    (v : spaY p ϖ) : g.base ((frobeniusHomeomorph hI ^ n) v) = g.base v := by
  refine eq_of_heq (heq_zpow_apply_of_heq_frobenius (fun v ↦ g.base v) (fun v ↦ heq_of_eq ?_) n v)
  have := congrArg (fun f ↦ f.base v) hg
  rw [spaYFrobenius_toHom] at this
  exact this

/-- The continuous map `𝒳 → W` through which a Frobenius-invariant morphism `𝒴 → W` factors. -/
private def descBase (hg : (spaYFrobenius P hI).toHom ≫ g = g) :
    TopCat.of (spaX hI) ⟶ W.carrier :=
  TopCat.ofHom ⟨spaX.lift hI (g.base ·) (base_zpow_apply_of_comp_eq hg), by
    rw [(isOpenQuotientMap_quotientMap hI).isQuotientMap.continuous_iff]
    exact (continuous_congr fun v ↦
      (spaX.lift_quotientMap hI _ (base_zpow_apply_of_comp_eq hg) v).symm).mp
        g.base.hom.continuous⟩

private theorem base_comp_descBase (hg : (spaYFrobenius P hI).toHom ≫ g = g) :
    (quotientPresheafedHom P hI).base ≫ descBase hg = g.base := by
  ext v
  exact spaX.lift_quotientMap hI _ (base_zpow_apply_of_comp_eq hg) v

/-- The map on sections `𝒪_W → 𝒪_𝒳` through which a Frobenius-invariant morphism `𝒴 → W` factors:
the sections of `𝒪_𝒴` it produces are Frobenius-invariant, so they lie in `𝒪_𝒳`. -/
private def descC (hg : (spaYFrobenius P hI).toHom ≫ g = g) :
    W.presheaf ⟶ (TopCat.Presheaf.pushforward _ (descBase hg)).obj (spaXPresheaf P hI) :=
  -- pushforward is precomposition with the preimage functor, so it preserves equalizers
  haveI : PreservesLimitsOfShape WalkingParallelPair
      (TopCat.Presheaf.pushforward CompleteSeparatedTopCommRingCat.{v} (descBase hg)) :=
    whiskeringLeft_preservesLimitsOfShape _ _
  Fork.IsLimit.lift (isLimitMapConeForkEquiv _ _
      (isLimitOfPreserves (TopCat.Presheaf.pushforward _ (descBase hg))
        (isLimitSpaXPresheafFork P hI)))
    (g.c ≫ (TopCat.Presheaf.pushforwardEq (base_comp_descBase hg).symm _).hom ≫
      (TopCat.Presheaf.Pushforward.comp _ _ _).hom)
    (by
      -- on sections over `U`, Frobenius-invariance of `g` says that `g.c` followed by Frobenius
      -- is `g.c`, up to restrictions along equalities of opens
      have hg' : spaYFrobeniusHom P hI ≫ g = g := by rwa [spaYFrobenius_toHom] at hg
      refine NatTrans.ext (funext fun U ↦ ?_)
      have h := PresheafedSpace.congr_app hg' U
      rw [PresheafedSpace.comp_c_app] at h
      simp only [TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_map_app',
        pushforwardSpaYPresheafFrobenius_app, Category.assoc, Category.comp_id,
        CategoryTheory.Functor.map_id]
      -- the points of `𝒴` occur both as `TopCat.of (spaY p ϖ)` and as the carrier of the pre-adic
      -- space `𝒴`, which agree only after unfolding, so the remaining rewrites need `erw`
      erw [NatTrans.comp_app, TopCat.Presheaf.pushforwardEq_hom_app,
        TopCat.Presheaf.Pushforward.comp_hom_app, Category.comp_id,
        (spaYPresheafFrobenius P hI).naturality_assoc, reassoc_of% h, Category.assoc]
      refine congrArg (g.c.app U ≫ ·) ?_
      erw [eqToHom_map, eqToHom_map, eqToHom_map, eqToHom_map, eqToHom_trans, eqToHom_trans]
      rfl)

private theorem descC_comp (hg : (spaYFrobenius P hI).toHom ≫ g = g) :
    descC hg ≫ (TopCat.Presheaf.pushforward _ (descBase hg)).map (spaXPresheafι P hI) =
      g.c ≫ (TopCat.Presheaf.pushforwardEq (base_comp_descBase hg).symm _).hom ≫
        (TopCat.Presheaf.Pushforward.comp _ _ _).hom :=
  Fork.IsLimit.lift_ι' _ _ _

variable (g) in
/-- **Morphisms out of `𝒳`**: a morphism of presheafed spaces `g : 𝒴 → W` with `φ ≫ g = g`
factors through the projection `q : 𝒴 → 𝒳`
(`quotientPresheafedHom_comp_quotientPresheafedDesc`), and uniquely so
(`quotientPresheafedHom_hom_ext`). On points it is the map induced on Frobenius orbits; on
sections it lands in the Frobenius-invariant sections of `𝒪_𝒴`, which are those of `𝒪_𝒳`. -/
def quotientPresheafedDesc (hg : (spaYFrobenius P hI).toHom ≫ g = g) :
    spaXPresheafedSpace P hI ⟶ W where
  base := descBase hg
  c := descC hg

/-- The factorization of a Frobenius-invariant morphism through `q` sends the orbit of a point to
the image of that point. -/
@[simp]
theorem quotientPresheafedDesc_base_quotientMap (hg : (spaYFrobenius P hI).toHom ≫ g = g)
    (v : spaY p ϖ) : (quotientPresheafedDesc g hg).base (quotientMap hI v) = g.base v :=
  spaX.lift_quotientMap hI _ (base_zpow_apply_of_comp_eq hg) v

/-- A Frobenius-invariant morphism out of `𝒴` factors through the projection `q : 𝒴 → 𝒳`. -/
@[reassoc (attr := simp)]
theorem quotientPresheafedHom_comp_quotientPresheafedDesc
    (hg : (spaYFrobenius P hI).toHom ≫ g = g) :
    quotientPresheafedHom P hI ≫ quotientPresheafedDesc g hg = g := by
  have hc : (quotientPresheafedHom P hI ≫ quotientPresheafedDesc g hg).c =
      descC hg ≫ (TopCat.Presheaf.pushforward _ (descBase hg)).map (spaXPresheafι P hI) :=
    PresheafedSpace.comp_c _ _
  refine PresheafedSpace.ext _ _ (base_comp_descBase hg) ?_
  -- as in `descC`, the two descriptions of the points of `𝒴` force `erw`; what remains on sections
  -- over `U` is `g.c` followed by restrictions along equalities of opens
  erw [hc, descC_comp hg]
  refine NatTrans.ext (funext fun U ↦ ?_)
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    TopCat.Presheaf.pushforwardEq_hom_app, TopCat.Presheaf.Pushforward.comp_hom_app,
    Functor.whiskerRight_app, eqToHom_app, Category.comp_id, Category.assoc, ← Functor.map_comp,
    eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Morphisms out of `𝒳` are determined by their composites with `q`**: the projection is an
epimorphism of presheafed spaces. On points this is surjectivity of `q`; on sections it is
injectivity of the inclusion of the Frobenius-invariant sections. -/
theorem quotientPresheafedHom_hom_ext {m₁ m₂ : spaXPresheafedSpace P hI ⟶ W}
    (h : quotientPresheafedHom P hI ≫ m₁ = quotientPresheafedHom P hI ≫ m₂) : m₁ = m₂ := by
  have hb : m₁.base = m₂.base := by
    ext x
    induction x using spaX.inductionOn with
    | h v => exact congrArg (fun f ↦ f.base v) h
  refine PresheafedSpace.ext _ _ hb (NatTrans.ext (funext fun U ↦ ?_))
  refine (cancel_mono ((spaXPresheafι P hI).app (op ((Opens.map m₂.base).obj U.unop)))).mp ?_
  have h' := PresheafedSpace.congr_app h U
  rw [PresheafedSpace.comp_c_app, PresheafedSpace.comp_c_app] at h'
  -- after the inclusion into `𝒪_𝒴`, the sections over `U` are those given by `h'`; the presheaf of
  -- `𝒳` occurs both as `spaXPresheaf` and as that of `spaXPresheafedSpace`, hence `erw`
  erw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, Category.assoc,
    (spaXPresheafι P hI).naturality, ← Category.assoc, h', Category.assoc, Category.assoc,
    ← Functor.map_comp, eqToHom_map (Opens.map (quotientTopHom hI)).op, eqToHom_trans,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  -- the projection's map on sections is the inclusion of the Frobenius-invariant sections
  rfl

instance : Epi (quotientPresheafedHom P hI) :=
  ⟨fun _ _ h ↦ quotientPresheafedHom_hom_ext h⟩

variable (P hI) in
/-- **`𝒳` is the coequalizer of the identity and Frobenius on `𝒴`** in presheafed spaces of complete
separated topological rings, with the projection `q` as coprojection. -/
def isColimitQuotientPresheafedCofork :
    IsColimit (Cofork.ofπ (f := 𝟙 _) (g := (spaYFrobenius P hI).toHom)
      (quotientPresheafedHom P hI)
      ((Category.id_comp _).trans (spaYFrobenius_toHom_comp_quotientPresheafedHom P hI).symm)) :=
  Cofork.IsColimit.mk _
    (fun s ↦ quotientPresheafedDesc s.π (by simpa using s.condition.symm))
    (fun s ↦ quotientPresheafedHom_comp_quotientPresheafedDesc _)
    (fun s m hm ↦ quotientPresheafedHom_hom_ext
      (hm.trans (quotientPresheafedHom_comp_quotientPresheafedDesc _).symm))

end Desc

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
      (PreAdicSpace.comap_stalkMap_base_eq_of_comp_eq
        (π := fun _ : Unit ↦ quotientPresheafedHom P hI) (i := ()) (j := ()) (𝟙 _)
        (spaYFrobenius P hI) (by
          rw [PreAdicSpace.id_toHom, Category.id_comp]
          exact (spaYFrobenius_toHom_comp_quotientPresheafedHom P hI).symm) y h₀))

/-- Integer powers of Frobenius do not change the descended valuation. -/
private theorem heq_descendedValuation_zpow (n : ℤ) (y : spaY p ϖ) :
    HEq (descendedValuation P hI ((frobeniusHomeomorph hI ^ n) y)) (descendedValuation P hI y) :=
  heq_zpow_apply_of_heq_frobenius _ heq_descendedValuation_frobenius n y

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
  PreAdicSpace.descend (fun _ : Unit ↦ spaYPreAdicSpace P hI)
    (fun _ ↦ quotientPresheafedHom P hI)
    (fun y ↦ ⟨(), (isOpenQuotientMap_quotientMap hI).surjective y⟩)
    (fun _ ↦ isIso_stalkMap_quotientPresheafedHom h)

end SpaXPreAdicDef

variable (P hI) in
/-- **The projection `𝒴 → 𝒳` as a morphism of pre-adic spaces**, when `𝒪_𝒴` is a sheaf. -/
def quotientPreAdicHom (h : (spaYPresheaf P ϖ).IsSheaf) :
    spaYPreAdicSpace P hI ⟶ spaXPreAdicSpace P hI h :=
  PreAdicSpace.toDescend (X := fun _ : Unit ↦ spaYPreAdicSpace P hI)
    (π := fun _ ↦ quotientPresheafedHom P hI) _ _
    (fun _ _ ↦ comap_stalkMap_quotientPresheafedHom_eq) ()

/-- The presheafed space underlying the pre-adic space `𝒳` is `(𝒳, 𝒪_𝒳)`. -/
@[simp]
theorem spaXPreAdicSpace_toPresheafedSpace (h : (spaYPresheaf P ϖ).IsSheaf) :
    (spaXPreAdicSpace P hI h).toPresheafedSpace = spaXPresheafedSpace P hI :=
  (rfl)

/-- The morphism of presheafed spaces underlying the pre-adic projection is `q`. -/
@[simp]
theorem quotientPreAdicHom_toHom (h : (spaYPresheaf P ϖ).IsSheaf) :
    (quotientPreAdicHom P hI h).toHom = quotientPresheafedHom P hI :=
  PreAdicSpace.toDescend_toHom (X := fun _ : Unit ↦ spaYPreAdicSpace P hI)
    (π := fun _ ↦ quotientPresheafedHom P hI) ..

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

/-! ### The universal property of `𝒳` in `𝒱^pre` -/

section Desc

open CategoryTheory.Limits

variable {W : PreAdicSpace.{v}} {g : spaYPreAdicSpace P hI ⟶ W}

variable (g) in
/-- **Morphisms out of the pre-adic space `𝒳`**: when `𝒪_𝒴` is a sheaf, a morphism of pre-adic
spaces `g : 𝒴 → W` with `φ ≫ g = g` factors through the projection `q : 𝒴 → 𝒳`
(`quotientPreAdicHom_comp_quotientPreAdicDesc`), and uniquely so (`quotientPreAdicHom_hom_ext`).
Its underlying morphism of presheafed spaces is `quotientPresheafedDesc`; it is compatible with the
stalk valuations because `q` is surjective and those of `𝒳` are descended from `𝒴`. -/
def quotientPreAdicDesc (h : (spaYPresheaf P ϖ).IsSheaf) (hg : spaYFrobenius P hI ≫ g = g) :
    spaXPreAdicSpace P hI h ⟶ W :=
  PreAdicSpace.Hom.ofFacOfSurjective g (quotientPreAdicHom P hI h)
    (quotientPresheafedDesc g.toHom (congrArg PreAdicSpace.Hom.toHom hg))
    (by
      rw [congrArg PresheafedSpace.Hom.base (quotientPreAdicHom_toHom h)]
      exact (isOpenQuotientMap_quotientMap hI).surjective)
    ((congrArg (· ≫ _) (quotientPreAdicHom_toHom h)).trans
      (quotientPresheafedHom_comp_quotientPresheafedDesc _))

/-- The morphism of presheafed spaces underlying `quotientPreAdicDesc` is
`quotientPresheafedDesc`. -/
@[simp]
theorem quotientPreAdicDesc_toHom (h : (spaYPresheaf P ϖ).IsSheaf)
    (hg : spaYFrobenius P hI ≫ g = g) :
    (quotientPreAdicDesc g h hg).toHom =
      quotientPresheafedDesc g.toHom (congrArg PreAdicSpace.Hom.toHom hg) :=
  PreAdicSpace.Hom.ofFacOfSurjective_toHom ..

/-- A Frobenius-invariant morphism of pre-adic spaces out of `𝒴` factors through the projection
`q : 𝒴 → 𝒳`. -/
@[reassoc (attr := simp)]
theorem quotientPreAdicHom_comp_quotientPreAdicDesc (h : (spaYPresheaf P ϖ).IsSheaf)
    (hg : spaYFrobenius P hI ≫ g = g) :
    quotientPreAdicHom P hI h ≫ quotientPreAdicDesc g h hg = g :=
  PreAdicSpace.Hom.ext' (by
    rw [PreAdicSpace.comp_toHom, quotientPreAdicHom_toHom, quotientPreAdicDesc_toHom]
    exact quotientPresheafedHom_comp_quotientPresheafedDesc _)

/-- **Morphisms of pre-adic spaces out of `𝒳` are determined by their composites with `q`.** -/
theorem quotientPreAdicHom_hom_ext {h : (spaYPresheaf P ϖ).IsSheaf}
    {m₁ m₂ : spaXPreAdicSpace P hI h ⟶ W}
    (hm : quotientPreAdicHom P hI h ≫ m₁ = quotientPreAdicHom P hI h ≫ m₂) : m₁ = m₂ :=
  PreAdicSpace.Hom.ext' (quotientPresheafedHom_hom_ext (by
    have hm' := congrArg PreAdicSpace.Hom.toHom hm
    rw [PreAdicSpace.comp_toHom, PreAdicSpace.comp_toHom, quotientPreAdicHom_toHom] at hm'
    exact hm'))

instance (h : (spaYPresheaf P ϖ).IsSheaf) : Epi (quotientPreAdicHom P hI h) :=
  ⟨fun _ _ hm ↦ quotientPreAdicHom_hom_ext hm⟩

variable (P hI) in
/-- **`𝒳 = 𝒴 / φ^ℤ` is the quotient of `𝒴` by Frobenius in `𝒱^pre`**: when `𝒪_𝒴` is a sheaf, the
pre-adic space `𝒳` is the coequalizer of the identity and Frobenius on `𝒴`, with the projection `q`
as coprojection. -/
def isColimitQuotientPreAdicCofork (h : (spaYPresheaf P ϖ).IsSheaf) :
    IsColimit (Cofork.ofπ (f := 𝟙 _) (g := spaYFrobenius P hI) (quotientPreAdicHom P hI h)
      ((Category.id_comp _).trans (spaYFrobenius_comp_quotientPreAdicHom h).symm)) :=
  Cofork.IsColimit.mk _
    (fun s ↦ quotientPreAdicDesc s.π h (by simpa using s.condition.symm))
    (fun s ↦ quotientPreAdicHom_comp_quotientPreAdicDesc h _)
    (fun s m hm ↦ quotientPreAdicHom_hom_ext
      (hm.trans (quotientPreAdicHom_comp_quotientPreAdicDesc h _).symm))

end Desc

end SpaX

end TauCeti.FarguesFontaine
