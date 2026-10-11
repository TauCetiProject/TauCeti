/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Quotient
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Transport

import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits

/-!
# The structure presheaf of the Frobenius orbit space

Let `R` be a perfect ring of characteristic `p`, give the Witt vectors `𝕎 R` the `(p, [ϖ])`-adic
topology, and let `𝒪` be the presentation-limit structure presheaf of `Spa(𝕎 R, 𝕎 R)` for a pair
of definition `P`. For `R = 𝒪_F` this is `Spa(A_inf, A_inf)`. The adic Fargues–Fontaine curve is
the orbit space `𝒳 = 𝒴 / φ^ℤ` of the open subset `𝒴 = D(p) ∩ D([ϖ])` under Witt Frobenius, and its
structure presheaf is

```text
𝒪_𝒳(U) = 𝒪_𝒴(q⁻¹U)^{φ=1},
```

the Frobenius-invariant sections of `𝒪_𝒴` over the preimage of `U` under the projection
`q : 𝒴 → 𝒳`. This file constructs it.

* `𝒪_𝒴` is the restriction of `𝒪` to the open subset `𝒴`.
* Witt Frobenius is an automorphism of the pair `(𝕎 R, 𝕎 R)`, continuous in both directions, so
  it acts on `𝒪` (`TauCeti.ValuationSpectrum.presentationLimitPresheafIsoPushforward`). Since `𝒴`
  is Frobenius-stable this restricts to a morphism `𝒪_𝒴 → φ_* 𝒪_𝒴`, whose component on `V ⊆ 𝒴`
  is `𝒪(V) → 𝒪(φ⁻¹V)`.
* Since `q ∘ φ = q`, pushing it forward along `q` gives an endomorphism of `q_* 𝒪_𝒴`, and `𝒪_𝒳`
  is its equalizer with the identity, taken in presheaves of complete separated topological
  rings.

The sections of `𝒪_𝒳` over `U` form the closed subring of Frobenius-invariant sections of `𝒪_𝒴`
over `q⁻¹U`, with the subspace topology. Equalizers and pushforwards of sheaves are sheaves, so
`𝒪_𝒳` is a sheaf as soon as `𝒪_𝒴` is one. Sheafiness of `𝒪_𝒴` is not proved here. In
characteristic `p` with `ϖ` not a unit, `𝕎 R` is not a Tate ring, so it is not an instance of Tate
acyclicity for `Spa(𝕎 R, 𝕎 R)`; since the sheaf condition is local and the Frobenius windows are
rational subsets covering `𝒴`, it suffices to know that `𝒪` is a sheaf on each window.

## Main definitions

* `TauCeti.FarguesFontaine.spaYPresheaf` : the structure presheaf `𝒪_𝒴` of `𝒴`.
* `TauCeti.FarguesFontaine.presentationLimitPresheafFrobeniusIso` : the Frobenius action
  `𝒪 ≅ φ_* 𝒪` on the structure presheaf of `Spa(𝕎 R, 𝕎 R)`.
* `TauCeti.FarguesFontaine.presentationLimitPreAdicSpaceFrobeniusIso` : Frobenius as an
  automorphism of the pre-adic space `Spa(𝕎 R, 𝕎 R)`, compatible with the stalk valuations.
* `TauCeti.FarguesFontaine.spaYPresheafFrobenius` : its restriction `𝒪_𝒴 → φ_* 𝒪_𝒴`.
* `TauCeti.FarguesFontaine.pushforwardSpaYPresheafFrobenius` : the induced endomorphism of
  `q_* 𝒪_𝒴`.
* `TauCeti.FarguesFontaine.spaXPresheaf` : the structure presheaf `𝒪_𝒳` of the orbit space, with
  its inclusion `TauCeti.FarguesFontaine.spaXPresheafι` into `q_* 𝒪_𝒴`.

## Main results

* `TauCeti.FarguesFontaine.isIso_spaYPresheafFrobenius_app` : each component
  `𝒪_𝒴(V) → 𝒪_𝒴(φ⁻¹V)` of Frobenius is an isomorphism, since `𝒴` is stable under Frobenius in
  both directions (`TauCeti.FarguesFontaine.functor_obj_map_frobeniusTopHom`).
* `TauCeti.FarguesFontaine.isLimitSpaXPresheafFork` : `𝒪_𝒳` is the equalizer of the identity and
  Frobenius on `q_* 𝒪_𝒴`.
* `TauCeti.FarguesFontaine.isClosedEmbedding_spaXPresheafι_app` and
  `TauCeti.FarguesFontaine.range_spaXPresheafι_app` : on each open `U ⊆ 𝒳`, the inclusion
  `𝒪_𝒳(U) → 𝒪_𝒴(q⁻¹U)` is a closed embedding onto the Frobenius-invariant sections.
* `TauCeti.FarguesFontaine.isSheaf_spaXPresheaf` : `𝒪_𝒳` is a sheaf when `𝒪_𝒴` is.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017 notes, §3.1.
* P. Scholze and J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 12.
* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018).
-/

public section

noncomputable section

universe v

namespace TauCeti.FarguesFontaine

open CategoryTheory CategoryTheory.Limits Opposite _root_.TopologicalSpace Topology
open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type v} [CommRing R] [TopologicalSpace (WittVector p R)]

/-! ### The structure presheaf of `𝒴` -/

section SpaY

variable (p) in
/-- `𝒴` is contained in `Spa(𝕎 R, 𝕎 R)`. -/
theorem spaY_subset_spa (ϖ : R) : spaY p ϖ ⊆ spa (⊤ : Subring (WittVector p R)) :=
  fun v hv ↦ ((mem_spaY_iff p ϖ v).mp hv).1

variable (p) in
/-- The inclusion of `𝒴` into `Spa(𝕎 R, 𝕎 R)`, as a morphism of topological spaces. -/
def spaYInclusion (ϖ : R) :
    TopCat.of (spaY p ϖ) ⟶ TopCat.of (spa (⊤ : Subring (WittVector p R))) :=
  TopCat.ofHom ⟨Set.inclusion (spaY_subset_spa p ϖ), continuous_inclusion _⟩

/-- The inclusion of `𝒴` into `Spa(𝕎 R, 𝕎 R)` does not change the underlying valuation. -/
@[simp]
theorem spaYInclusion_apply_val (ϖ : R) (v : spaY p ϖ) : (spaYInclusion p ϖ v).val = v.val :=
  (rfl)

variable (p) in
/-- The inclusion of `𝒴` into `Spa(𝕎 R, 𝕎 R)` is an open embedding. -/
theorem isOpenEmbedding_spaYInclusion (ϖ : R) : IsOpenEmbedding (spaYInclusion p ϖ) :=
  IsOpenEmbedding.inclusion (spaY_subset_spa p ϖ) (isOpen_val_preimage_spaY p ϖ)

variable [IsTopologicalRing (WittVector p R)]

/-- **The structure presheaf `𝒪_𝒴` of `𝒴`**: the restriction to the open subset `𝒴` of the
presentation-limit structure presheaf of `Spa(𝕎 R, 𝕎 R)` for the pair of definition `P`. Its
sections over an open `V ⊆ 𝒴` are those of `Spa(𝕎 R, 𝕎 R)` over `V`. -/
def spaYPresheaf (P : PairOfDefinition (WittVector p R)) (ϖ : R) :
    (TopCat.of (spaY p ϖ)).Presheaf CompleteSeparatedTopCommRingCat.{v} :=
  (isOpenEmbedding_spaYInclusion p ϖ).functor.op ⋙
    presentationLimitPresheaf P (⊤ : Subring (WittVector p R))

/-- The sections of `𝒪_𝒴` over `V` are the sections of `Spa(𝕎 R, 𝕎 R)` over `V`. -/
theorem spaYPresheaf_obj (P : PairOfDefinition (WittVector p R)) (ϖ : R)
    (V : (Opens (spaY p ϖ))ᵒᵖ) :
    (spaYPresheaf P ϖ).obj V = (presentationLimitPresheaf P ⊤).obj
      (op ((isOpenEmbedding_spaYInclusion p ϖ).functor.obj V.unop)) :=
  (rfl)

end SpaY

/-! ### Frobenius on `𝒪_𝒴` -/

section TopHom

variable [CharP R p] [PerfectRing R p] {ϖ : R}
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-- The Frobenius homeomorphism of `𝒴`, as a morphism of topological spaces. -/
abbrev frobeniusTopHom : TopCat.of (spaY p ϖ) ⟶ TopCat.of (spaY p ϖ) :=
  TopCat.ofHom (frobeniusHomeomorph hI : C(spaY p ϖ, spaY p ϖ))

/-- The projection `q : 𝒴 → 𝒳`, as a morphism of topological spaces. -/
abbrev quotientTopHom : TopCat.of (spaY p ϖ) ⟶ TopCat.of (spaX hI) :=
  TopCat.ofHom ⟨quotientMap hI, (isOpenQuotientMap_quotientMap hI).continuous⟩

/-- Frobenius followed by the projection to `𝒳` is the projection. -/
theorem frobeniusTopHom_comp_quotientTopHom :
    frobeniusTopHom hI ≫ quotientTopHom hI = quotientTopHom hI := by
  ext v
  simpa using quotientMap_zpow hI 1 v

/-- The image in `Spa(𝕎 R, 𝕎 R)` of `φ⁻¹V` lies in the preimage under Frobenius of the image of
`V`. -/
theorem functor_obj_map_frobeniusTopHom_le (V : Opens (spaY p ϖ)) :
    (isOpenEmbedding_spaYInclusion p ϖ).functor.obj
        ((Opens.map (frobeniusTopHom hI)).obj V) ≤
      (Opens.map (spaComapTopHom frobenius (TauCeti.WittVector.continuous_frobenius hI)
        (fun _ _ ↦ Subring.mem_top _))).obj
        ((isOpenEmbedding_spaYInclusion p ϖ).functor.obj V) := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨frobeniusHomeomorph hI v, hv, Subtype.ext (by
    simp only [ConcreteCategory.hom_ofHom, ContinuousMap.coe_mk, spaComap_val]
    exact frobeniusHomeomorph_apply_val hI v)⟩

/-- The image in `Spa(𝕎 R, 𝕎 R)` of `φ⁻¹V` is the preimage under Frobenius of the image of `V`:
`𝒴` is stable under Frobenius in both directions. -/
theorem functor_obj_map_frobeniusTopHom (V : Opens (spaY p ϖ)) :
    (isOpenEmbedding_spaYInclusion p ϖ).functor.obj
        ((Opens.map (frobeniusTopHom hI)).obj V) =
      (Opens.map (spaComapTopHom frobenius (TauCeti.WittVector.continuous_frobenius hI)
        (fun _ _ ↦ Subring.mem_top _))).obj
        ((isOpenEmbedding_spaYInclusion p ϖ).functor.obj V) := by
  refine le_antisymm (functor_obj_map_frobeniusTopHom_le hI V) ?_
  rintro w ⟨v, hv, hvw⟩
  have hvw' : v.val = comap frobenius w.val := by
    simpa [spaYInclusion_apply_val ϖ v] using congrArg Subtype.val hvw
  have hw : w.val ∈ spaY p ϖ := (comap_frobenius_mem_spaY_iff hI _).mp (hvw' ▸ v.2)
  refine ⟨⟨w.val, hw⟩, ?_, Subtype.ext (spaYInclusion_apply_val ϖ _)⟩
  have : frobeniusHomeomorph hI ⟨w.val, hw⟩ = v :=
    Subtype.ext ((frobeniusHomeomorph_apply_val hI _).trans hvw'.symm)
  exact Opens.mem_map.mpr (this ▸ hv)

end TopHom

section Frobenius

variable [IsTopologicalRing (WittVector p R)] [CharP R p] [PerfectRing R p] {ϖ : R}
  (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-- **Witt Frobenius acting on the structure presheaf of `Spa(𝕎 R, 𝕎 R)`**: the isomorphism
`𝒪 ≅ φ_* 𝒪` obtained by transporting the presentation-limit presheaf along the automorphism `φ` of
the pair `(𝕎 R, 𝕎 R)`, where `φ` acts on points by `v ↦ v ∘ φ`. -/
abbrev presentationLimitPresheafFrobeniusIso :=
  presentationLimitPresheafIsoPushforward (P := P) (P' := P)
    (Aplus := (⊤ : Subring (WittVector p R))) (Bplus := ⊤) frobenius
    (TauCeti.WittVector.continuous_frobenius hI) (fun _ _ ↦ Subring.mem_top _)
    ((frobeniusEquiv p R).symm : WittVector p R →+* WittVector p R)
    (TauCeti.WittVector.continuous_frobeniusEquiv_symm hI)
    (fun a ↦ (frobeniusEquiv p R).symm_apply_apply a)
    (fun b ↦ (frobeniusEquiv p R).apply_symm_apply b) (fun _ _ ↦ Subring.mem_top _)

/-- **Witt Frobenius as an automorphism of the pre-adic space `Spa(𝕎 R, 𝕎 R)`**: the isomorphism
in `𝒱^pre` induced by the automorphism `φ` of the pair `(𝕎 R, 𝕎 R)`. On points it is
`v ↦ v ∘ φ`, on sections it is `presentationLimitPresheafFrobeniusIso`, and it matches the stalk
valuations: through the Frobenius map of stalks `𝒪_{v ∘ φ} → 𝒪_v`, the stalk valuation at `v ∘ φ`
is the pullback of the stalk valuation at `v` (`TauCeti.PreAdicSpace.Hom.stalkValuation_eq_comap`).
No sheaf condition on `Spa(𝕎 R, 𝕎 R)` is needed. -/
abbrev presentationLimitPreAdicSpaceFrobeniusIso :=
  presentationLimitPreAdicSpaceComapIso (P := P) (P' := P)
    (Aplus := (⊤ : Subring (WittVector p R))) (Bplus := ⊤) frobenius
    (TauCeti.WittVector.continuous_frobenius hI) (fun _ _ ↦ Subring.mem_top _)
    ((frobeniusEquiv p R).symm : WittVector p R →+* WittVector p R)
    (TauCeti.WittVector.continuous_frobeniusEquiv_symm hI)
    (fun a ↦ (frobeniusEquiv p R).symm_apply_apply a)
    (fun b ↦ (frobeniusEquiv p R).apply_symm_apply b) (fun _ _ ↦ Subring.mem_top _)
    -- every element of the `(p, [ϖ])`-adic ring `𝕎 R` is power-bounded
    (fun _ _ ↦ haveI := hI.isLinearTopology
      isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _))
    (fun _ _ ↦ haveI := hI.isLinearTopology
      isPowerBounded_iff.mpr (isBounded_of_isLinearTopology _)) le_top le_top

/-- **Frobenius acting on `𝒪_𝒴`**: the morphism `𝒪_𝒴 → φ_* 𝒪_𝒴` whose component on an open
`V ⊆ 𝒴` is the map `𝒪(V) → 𝒪(φ⁻¹V)` induced by the Witt-vector Frobenius `φ`, an automorphism of
the pair `(𝕎 R, 𝕎 R)`. Here `φ` acts on points by `v ↦ v ∘ φ`. -/
def spaYPresheafFrobenius :
    spaYPresheaf P ϖ ⟶ (TopCat.Presheaf.pushforward _ (frobeniusTopHom hI)).obj
      (spaYPresheaf P ϖ) where
  app V := (presentationLimitPresheafFrobeniusIso P hI).hom.app
      (op ((isOpenEmbedding_spaYInclusion p ϖ).functor.obj V.unop)) ≫
    (presentationLimitPresheaf P ⊤).map (homOfLE (functor_obj_map_frobeniusTopHom_le hI V.unop)).op
  naturality V W f := by
    have h := (presentationLimitPresheafFrobeniusIso P hI).hom.naturality
      ((isOpenEmbedding_spaYInclusion p ϖ).functor.op.map f)
    dsimp only [spaYPresheaf, Functor.comp_map, Functor.op_obj, Functor.op_map,
      TopCat.Presheaf.pushforward_obj_map] at h ⊢
    simp only [Category.assoc, reassoc_of% h, ← Functor.map_comp]
    rfl

/-- The component of `spaYPresheafFrobenius` on `V ⊆ 𝒴` is that of
`presentationLimitPresheafFrobeniusIso` on `V`, followed by restriction from `φ⁻¹V` computed in
`Spa(𝕎 R, 𝕎 R)` to `φ⁻¹V` computed in `𝒴`. -/
theorem spaYPresheafFrobenius_app (V : (Opens (spaY p ϖ))ᵒᵖ) :
    (spaYPresheafFrobenius P hI).app V =
      eqToHom (spaYPresheaf_obj P ϖ V) ≫
        (presentationLimitPresheafFrobeniusIso P hI).hom.app
          (op ((isOpenEmbedding_spaYInclusion p ϖ).functor.obj V.unop)) ≫
        (presentationLimitPresheaf P ⊤).map
          (homOfLE (functor_obj_map_frobeniusTopHom_le hI V.unop)).op ≫
        eqToHom (spaYPresheaf_obj P ϖ (op ((Opens.map (frobeniusTopHom hI)).obj V.unop))).symm :=
  (rfl)

/-- **Frobenius acts on the sections of `𝒪_𝒴` by isomorphisms**: each component `𝒪_𝒴(V) → 𝒪_𝒴(φ⁻¹V)`
of `spaYPresheafFrobenius` is an isomorphism of complete separated topological rings. -/
instance isIso_spaYPresheafFrobenius_app (V : (Opens (spaY p ϖ))ᵒᵖ) :
    IsIso ((spaYPresheafFrobenius P hI).app V) := by
  rw [spaYPresheafFrobenius_app,
    Subsingleton.elim (homOfLE (functor_obj_map_frobeniusTopHom_le hI V.unop))
      (eqToHom (functor_obj_map_frobeniusTopHom hI V.unop)), eqToHom_op, eqToHom_map]
  infer_instance

/-- **Frobenius acting on `q_* 𝒪_𝒴`**: the pushforward along `q : 𝒴 → 𝒳` of
`spaYPresheafFrobenius`, an endomorphism because `q ∘ φ = q`. Its component on an open `U ⊆ 𝒳` is
the map `𝒪_𝒴(q⁻¹U) → 𝒪_𝒴(φ⁻¹q⁻¹U) = 𝒪_𝒴(q⁻¹U)` induced by Frobenius. -/
def pushforwardSpaYPresheafFrobenius :
    (TopCat.Presheaf.pushforward _ (quotientTopHom hI)).obj (spaYPresheaf P ϖ) ⟶
      (TopCat.Presheaf.pushforward _ (quotientTopHom hI)).obj (spaYPresheaf P ϖ) :=
  (TopCat.Presheaf.pushforward _ (quotientTopHom hI)).map (spaYPresheafFrobenius P hI) ≫
    (TopCat.Presheaf.Pushforward.comp _ _ _).inv ≫
    (TopCat.Presheaf.pushforwardEq (frobeniusTopHom_comp_quotientTopHom hI) _).hom

/-- The component of `pushforwardSpaYPresheafFrobenius` on `U ⊆ 𝒳` is the component of
`spaYPresheafFrobenius` on `q⁻¹U`, followed by the identification `φ⁻¹q⁻¹U = q⁻¹U`. -/
@[simp]
theorem pushforwardSpaYPresheafFrobenius_app (U : (Opens (spaX hI))ᵒᵖ) :
    (pushforwardSpaYPresheafFrobenius P hI).app U =
      (spaYPresheafFrobenius P hI).app (op ((Opens.map (quotientTopHom hI)).obj U.unop)) ≫
        (spaYPresheaf P ϖ).map (eqToHom (congrArg op
          (by rw [← Opens.map_comp_obj, frobeniusTopHom_comp_quotientTopHom] :
            (Opens.map (frobeniusTopHom hI)).obj ((Opens.map (quotientTopHom hI)).obj U.unop) =
              (Opens.map (quotientTopHom hI)).obj U.unop))) := by
  simp [pushforwardSpaYPresheafFrobenius]

end Frobenius

/-! ### The structure presheaf of `𝒳` -/

section SpaX

variable [IsTopologicalRing (WittVector p R)] [CharP R p] [PerfectRing R p] {ϖ : R}
  (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))

/-- **The structure presheaf `𝒪_𝒳` of the Frobenius orbit space `𝒳 = 𝒴 / φ^ℤ`**, given on an
open `U ⊆ 𝒳` by the Frobenius-invariant sections `𝒪_𝒴(q⁻¹U)^{φ=1}`: the equalizer of the identity
and Frobenius on `q_* 𝒪_𝒴`, in presheaves of complete separated topological rings. The
characterizing API is `spaXPresheafι` with `isLimitSpaXPresheafFork`, and on sections
`isClosedEmbedding_spaXPresheafι_app` with `range_spaXPresheafι_app`. -/
def spaXPresheaf : (TopCat.of (spaX hI)).Presheaf CompleteSeparatedTopCommRingCat.{v} :=
  equalizer (𝟙 _) (pushforwardSpaYPresheafFrobenius P hI)

/-- The inclusion `𝒪_𝒳 → q_* 𝒪_𝒴` of the Frobenius-invariant sections. -/
def spaXPresheafι :
    spaXPresheaf P hI ⟶
      (TopCat.Presheaf.pushforward _ (quotientTopHom hI)).obj (spaYPresheaf P ϖ) :=
  equalizer.ι _ _

/-- Sections of `𝒪_𝒳` are Frobenius-invariant. -/
@[reassoc (attr := simp)]
theorem spaXPresheafι_comp_pushforwardSpaYPresheafFrobenius :
    spaXPresheafι P hI ≫ pushforwardSpaYPresheafFrobenius P hI = spaXPresheafι P hI :=
  (equalizer.condition _ _).symm.trans (Category.comp_id _)

/-- **The universal property of `𝒪_𝒳`**: with its inclusion into `q_* 𝒪_𝒴`, it is the equalizer
of the identity and Frobenius. -/
def isLimitSpaXPresheafFork :
    IsLimit (Fork.ofι (f := 𝟙 _) (g := pushforwardSpaYPresheafFrobenius P hI)
      (spaXPresheafι P hI) (by simp)) :=
  equalizerIsEqualizer _ _

/-- On the sections over `U`, the inclusion `𝒪_𝒳(U) → 𝒪_𝒴(q⁻¹U)` is a homeomorphism onto the
agreement subring of the identity and Frobenius, followed by the inclusion of that subring. -/
private theorem exists_homeomorph_eqLocus (U : (Opens (spaX hI))ᵒᵖ) :
    ∃ e : (spaXPresheaf P hI).obj U ≃ₜ RingHom.eqLocus (RingHom.id _)
        ((pushforwardSpaYPresheafFrobenius P hI).app U).hom.1,
      ⇑((spaXPresheafι P hI).app U).hom.1 = Subtype.val ∘ e := by
  -- Evaluation at `U` followed by the inclusion into `TopCommRingCat` preserves the equalizer,
  -- which in `TopCommRingCat` is the agreement subring `equalizerFork`.
  let G := (evaluation (Opens (spaX hI))ᵒᵖ CompleteSeparatedTopCommRingCat.{v}).obj U ⋙
    TopCommRingCat.isCompleteSeparated.ι
  let hl := isLimitMapConeForkEquiv G _ (isLimitOfPreserves G (isLimitSpaXPresheafFork P hI))
  let e := hl.conePointUniqueUpToIso (TopCommRingCat.equalizerForkIsLimit _ _)
  have he := hl.conePointUniqueUpToIso_hom_comp (TopCommRingCat.equalizerForkIsLimit _ _)
    WalkingParallelPair.zero
  refine ⟨TopCat.homeoOfIso ((forget₂ _root_.TopCommRingCat TopCat).mapIso e), funext fun x ↦ ?_⟩
  exact (ConcreteCategory.congr_hom he x).symm

/-- **The sections of `𝒪_𝒳` embed in those of `𝒪_𝒴`**: on each open `U ⊆ 𝒳`, the inclusion
`𝒪_𝒳(U) → 𝒪_𝒴(q⁻¹U)` is a closed embedding. -/
theorem isClosedEmbedding_spaXPresheafι_app (U : (Opens (spaX hI))ᵒᵖ) :
    IsClosedEmbedding ((spaXPresheafι P hI).app U).hom.1 := by
  obtain ⟨e, he⟩ := exists_homeomorph_eqLocus P hI U
  have hcl : IsClosed {s | s = ((pushforwardSpaYPresheafFrobenius P hI).app U).hom.1 s} :=
    isClosed_eq continuous_id ((pushforwardSpaYPresheafFrobenius P hI).app U).hom.2
  rw [he]
  -- membership in `RingHom.eqLocus f g` is `f s = g s` by definition (`RingHom.mem_eqLocus` is
  -- proved by `Iff.rfl`), so the agreement subring is the closed set `hcl` as a subtype
  exact hcl.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding

/-- **The sections of `𝒪_𝒳` are the Frobenius-invariant sections of `𝒪_𝒴`**: on each open
`U ⊆ 𝒳`, the image of `𝒪_𝒳(U)` in `𝒪_𝒴(q⁻¹U)` consists of the sections fixed by Frobenius. -/
theorem range_spaXPresheafι_app (U : (Opens (spaX hI))ᵒᵖ) :
    Set.range ((spaXPresheafι P hI).app U).hom.1 =
      {s | ((pushforwardSpaYPresheafFrobenius P hI).app U).hom.1 s = s} := by
  obtain ⟨e, he⟩ := exists_homeomorph_eqLocus P hI U
  rw [he, Set.range_comp, e.range_coe, Set.image_univ, Subtype.range_coe_subtype]
  ext s
  exact eq_comm

/-- **`𝒪_𝒳` is a sheaf when `𝒪_𝒴` is**: pushforwards and equalizers of sheaves are sheaves. -/
theorem isSheaf_spaXPresheaf (h : (spaYPresheaf P ϖ).IsSheaf) : (spaXPresheaf P hI).IsSheaf :=
  TopCat.limit_isSheaf _ fun j ↦ by
    cases j <;> exact TopCat.Sheaf.pushforward_sheaf_of_sheaf _ h

end SpaX

end TauCeti.FarguesFontaine
