/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Adic
public import TauCeti.RingTheory.WittVector.AdicTopology
public import TauCeti.Topology.Algebra.Valued.NormedValued

/-!
# Independence of the pseudouniformiser

The space `𝒴 = D(p) ∩ D([ϖ]) ⊆ Spa(𝕎 R, 𝕎 R)`, its Frobenius action and the orbit space
`𝒳 = 𝒴 / φ^ℤ` are defined in terms of a chosen element `ϖ : R`, which for `R = 𝒪_F` is a
pseudouniformiser of a complete perfect nonarchimedean field `F` of characteristic `p`. None of
these depends on that choice. Let `ϖ, ϖ' : R` generate ideals with the same radical, as any two
pseudouniformisers of `𝒪_F` do (`Valuation.Integers.radical_span_singleton_eq_of_norm_lt_one`).
Then the ideals `(p, [ϖ])` and `(p, [ϖ'])` define the same adic topology on `𝕎 R`
(`TauCeti.WittVector.isAdic_span_p_teichmuller_iff`), and this file shows the following.

* The subsets `𝒴` defined by `ϖ` and by `ϖ'` coincide, since a prime ideal contains `[ϖ]` exactly
  when it contains `[ϖ']`.
* The Frobenius actions on them agree, since both are pullback along the Witt-vector Frobenius.
* Consequently the two orbit spaces `𝒳` are homeomorphic, compatibly with the projections
  from `𝒴`.
* As pre-adic spaces, the two restrictions `𝒴` of `Spa(𝕎 R, 𝕎 R)` are isomorphic in `𝒱^pre`,
  compatibly with their Frobenius endomorphisms. When `𝒪_𝒴` is a sheaf, so that `𝒳` is a pre-adic
  space, this descends through the universal property of the quotient
  (`TauCeti.FarguesFontaine.isColimitQuotientPreAdicCofork`) to an isomorphism in `𝒱^pre` of the
  two pre-adic spaces `𝒳`, which on points is the homeomorphism of orbit spaces.
* Both isomorphisms lift to the category `(Adic)` of adic spaces, where they identify the adic
  spaces `𝒴` compatibly with Frobenius and the adic spaces `𝒳` compatibly with the projections
  `𝒴 → 𝒳`. When `R` is the ring of integers of a valuation on a field, `𝒪_𝒴` is a sheaf
  (`TauCeti.FarguesFontaine.isSheaf_spaYPresheaf`), so the adic Fargues–Fontaine curve
  `𝒳 = 𝒴 / φ^ℤ` does not depend on the pseudouniformiser.

## Main results

* `TauCeti.FarguesFontaine.spaY_eq_of_radical_eq` : `𝒴` depends only on the radical of `(ϖ)`.
* `TauCeti.FarguesFontaine.frobeniusHomeomorph_zpow_apply_val_eq` : the integer powers of
  Frobenius on `𝒴` do not depend on the element used to define `𝒴`.
* `TauCeti.FarguesFontaine.spaXCongr` : the homeomorphism between the orbit spaces defined by two
  elements with the same `𝒴`.
* `TauCeti.FarguesFontaine.spaYPreAdicSpaceCongr` and
  `TauCeti.FarguesFontaine.spaYPreAdicSpaceCongr_hom_comp_spaYFrobenius` : the isomorphism of the
  pre-adic spaces `𝒴`, which intertwines Frobenius.
* `TauCeti.FarguesFontaine.isSheaf_spaYPresheaf_of_spaY_eq` : the sheaf condition on `𝒪_𝒴` depends
  only on the subset `𝒴`.
* `TauCeti.FarguesFontaine.spaXPreAdicSpaceCongr` : the isomorphism in `𝒱^pre` of the pre-adic
  spaces `𝒳`, with `quotientPreAdicHom_comp_spaXPreAdicSpaceCongr_hom` and
  `spaXPreAdicSpaceCongr_hom_base` describing it.
* `TauCeti.FarguesFontaine.spaYAdicSpaceCongr` and
  `TauCeti.FarguesFontaine.spaYAdicSpaceCongr_hom_comp_spaYAdicFrobenius` : the isomorphism of the
  adic spaces `𝒴`, which intertwines Frobenius.
* `TauCeti.FarguesFontaine.spaXAdicSpaceCongr` : the isomorphism of the adic spaces `𝒳`, with
  `quotientAdicHom_comp_spaXAdicSpaceCongr_hom` describing it.

## References

* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018).
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017, §3.1.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1 and Definition 8.22, for the categories
  `𝒱^pre` and `(Adic)`.
-/

public section

noncomputable section

universe v

namespace TauCeti.FarguesFontaine

open TauCeti.Huber TauCeti.ValuationSpectrum _root_.WittVector

variable {p : ℕ} [Fact p.Prime] {R : Type v} [CommRing R] {ϖ ϖ' : R}

/-- If `ϖ` lies in the radical of `(ϖ')`, then every prime ideal of `𝕎 R` containing `[ϖ']`
contains `[ϖ]`. -/
private theorem teichmuller_mem_supp_of_mem_radical (h : ϖ ∈ (Ideal.span {ϖ'}).radical)
    {v : Spv (WittVector p R)} (hv : teichmuller p ϖ' ∈ v.supp) : teichmuller p ϖ ∈ v.supp :=
  (Ideal.IsPrime.radical_le_iff inferInstance).mpr ((Ideal.span_singleton_le_iff_mem _).mpr hv)
    (teichmuller_mem_radical_span_singleton h)

variable [TopologicalSpace (WittVector p R)]

/-- **`𝒴` depends only on the radical of `(ϖ)`.** If `ϖ` and `ϖ'` generate ideals with the same
radical, for instance if they are two pseudouniformisers of `𝒪_F`, then
`D(p) ∩ D([ϖ]) = D(p) ∩ D([ϖ'])` in `Spa(𝕎 R, 𝕎 R)`. -/
theorem spaY_eq_of_radical_eq (h : (Ideal.span {ϖ}).radical = (Ideal.span {ϖ'}).radical) :
    spaY p ϖ = spaY p ϖ' := by
  have hϖ : ϖ ∈ (Ideal.span {ϖ'}).radical :=
    h.le (Ideal.le_radical (Ideal.mem_span_singleton_self ϖ))
  have hϖ' : ϖ' ∈ (Ideal.span {ϖ}).radical :=
    h.ge (Ideal.le_radical (Ideal.mem_span_singleton_self ϖ'))
  ext v
  simp only [mem_spaY_iff]
  exact and_congr_right' <| and_congr_right' <|
    not_congr ⟨teichmuller_mem_supp_of_mem_radical hϖ', teichmuller_mem_supp_of_mem_radical hϖ⟩

section SpaYPreAdic

open AlgebraicGeometry _root_.CategoryTheory

/-- The range of the inclusion of `𝒴` into `Spa(𝕎 R, 𝕎 R)` consists of the points of `𝒴`. -/
private theorem range_spaYInclusion (ϖ : R) :
    Set.range (spaYInclusion p ϖ) = {w | w.val ∈ spaY p ϖ} := by
  ext w
  refine ⟨?_, fun hw ↦ ⟨⟨w.val, hw⟩, Subtype.ext (spaYInclusion_apply_val ϖ _)⟩⟩
  rintro ⟨v, rfl⟩
  rw [Set.mem_ofPred_eq, spaYInclusion_apply_val]
  exact v.property

/-- The inclusions into `Spa(𝕎 R, 𝕎 R)` of the subsets `𝒴` defined by `ϖ` and by `ϖ'` have the
same range when the two subsets agree. -/
private theorem range_spaYInclusion_eq (h : spaY p ϖ = spaY p ϖ') :
    Set.range (spaYInclusion p ϖ) = Set.range (spaYInclusion p ϖ') := by
  rw [range_spaYInclusion, range_spaYInclusion, h]

variable [IsTopologicalRing (WittVector p R)] (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
  (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))

/-- **`𝒴` as a pre-adic space depends only on the subset `𝒴`.** If `ϖ` and `ϖ'` define the same
subset `𝒴` of `Spa(𝕎 R, 𝕎 R)`, the two restrictions of the pre-adic space `Spa(𝕎 R, 𝕎 R)` to it
are isomorphic in `𝒱^pre`, compatibly with the inclusions into `Spa(𝕎 R, 𝕎 R)`
(`spaYPreAdicSpaceCongr_hom_ofRestrict`). -/
def spaYPreAdicSpaceCongr (h : spaY p ϖ = spaY p ϖ') :
    spaYPreAdicSpace P hI ≅ spaYPreAdicSpace P hI' :=
  (spaPreAdicSpace P hI).restrictIsoOfRangeEq (isOpenEmbedding_spaYInclusion p ϖ)
    (isOpenEmbedding_spaYInclusion p ϖ') (range_spaYInclusion_eq h)

/-- The isomorphism `spaYPreAdicSpaceCongr` commutes with the inclusions into
`Spa(𝕎 R, 𝕎 R)`. -/
@[simp, reassoc]
theorem spaYPreAdicSpaceCongr_hom_ofRestrict (h : spaY p ϖ = spaY p ϖ') :
    (spaYPreAdicSpaceCongr P hI hI' h).hom ≫
        (spaPreAdicSpace P hI').ofRestrict (isOpenEmbedding_spaYInclusion p ϖ') =
      (spaPreAdicSpace P hI).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ) :=
  PreAdicSpace.restrictIsoOfRangeEq_hom_ofRestrict ..

/-- On points, `spaYPreAdicSpaceCongr` does not change the underlying valuation. -/
@[simp]
theorem spaYPreAdicSpaceCongr_hom_base_val (h : spaY p ϖ = spaY p ϖ') (v : spaY p ϖ) :
    ((spaYPreAdicSpaceCongr P hI hI' h).hom.base v : spaY p ϖ').val = v.val := by
  -- both sides are the image in `Spa(𝕎 R, 𝕎 R)`, read off from the compatibility with the
  -- inclusions; the inclusion of a restriction is the given open embedding
  have hc := congrArg (fun f ↦ (f.base v).val) (spaYPreAdicSpaceCongr_hom_ofRestrict P hI hI' h)
  have hι (ϖ₀ : R) (hI₀ : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ₀}))
      (w : spaY p ϖ₀) :
      (((spaPreAdicSpace P hI₀).ofRestrict (isOpenEmbedding_spaYInclusion p ϖ₀)).base w).val =
        w.val :=
    (congrArg (fun f ↦ (ConcreteCategory.hom f w).val) (PreAdicSpace.ofRestrict_base
      (spaPreAdicSpace P hI₀) (isOpenEmbedding_spaYInclusion p ϖ₀))).trans
      (spaYInclusion_apply_val ϖ₀ w)
  exact (hι ϖ' hI' _).symm.trans (hc.trans (hι ϖ hI v))

/-- **The sheaf condition on `𝒪_𝒴` depends only on the subset `𝒴`.** Both presheaves restrict the
structure presheaf of `Spa(𝕎 R, 𝕎 R)` to the same open subset. -/
theorem isSheaf_spaYPresheaf_of_spaY_eq (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) : (spaYPresheaf P ϖ').IsSheaf :=
  -- `Spa(𝕎 R, 𝕎 R)` with its structure presheaf, as a presheafed space
  let X : PresheafedSpace CompleteSeparatedTopCommRingCat :=
    ⟨TopCat.of (spa (⊤ : Subring (WittVector p R))), presentationLimitPresheaf P ⊤⟩
  (PresheafedSpace.IsOpenImmersion.isSheaf_iff_of_range_eq
    (X.ofRestrict (isOpenEmbedding_spaYInclusion p ϖ))
    (X.ofRestrict (isOpenEmbedding_spaYInclusion p ϖ')) (range_spaYInclusion_eq h)).mp hY

end SpaYPreAdic

/-! ### The adic spaces `𝒴` -/

section SpaYAdic

open _root_.CategoryTheory

variable [IsTopologicalRing (WittVector p R)] (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
  (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))

/-- **The adic spaces `𝒴` for two pseudouniformisers are isomorphic.** If `ϖ` and `ϖ'` define the
same subset `𝒴` of `Spa(𝕎 R, 𝕎 R)` and `𝒪_𝒴` is a sheaf, the isomorphism `spaYPreAdicSpaceCongr` of
pre-adic spaces is an isomorphism in the full subcategory `(Adic)`. For perfect `R` it
intertwines Frobenius (`spaYAdicSpaceCongr_hom_comp_spaYAdicFrobenius`). -/
def spaYAdicSpaceCongr (h : spaY p ϖ = spaY p ϖ') (hY : (spaYPresheaf P ϖ).IsSheaf) :
    spaYAdicSpace P hI hY ≅
      spaYAdicSpace P hI' (isSheaf_spaYPresheaf_of_spaY_eq P h hY) :=
  ObjectProperty.isoMk _ (spaYPreAdicSpaceCongr P hI hI' h)

/-- The morphism of pre-adic spaces underlying `spaYAdicSpaceCongr` is `spaYPreAdicSpaceCongr`. -/
@[simp]
theorem spaYAdicSpaceCongr_hom_hom (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    (spaYAdicSpaceCongr P hI hI' h hY).hom.hom = (spaYPreAdicSpaceCongr P hI hI' h).hom :=
  (rfl)

/-- The morphism of pre-adic spaces underlying the inverse of `spaYAdicSpaceCongr` is the inverse
of `spaYPreAdicSpaceCongr`. -/
@[simp]
theorem spaYAdicSpaceCongr_inv_hom (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    (spaYAdicSpaceCongr P hI hI' h hY).inv.hom = (spaYPreAdicSpaceCongr P hI hI' h).inv :=
  (rfl)

end SpaYAdic

variable [CharP R p] [PerfectRing R p]

/-- **The Frobenius actions on `𝒴` do not depend on the pseudouniformiser.** For points of the
subsets `𝒴` defined by `ϖ` and by `ϖ'` with the same underlying valuation, every integer power of
Frobenius gives the same valuation: on either subset, Frobenius is pullback along the Witt-vector
Frobenius. -/
theorem frobeniusHomeomorph_zpow_apply_val_eq
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'})) (n : ℤ)
    {v : spaY p ϖ} {w : spaY p ϖ'} (h : v.val = w.val) :
    ((frobeniusHomeomorph hI ^ n) v).val = ((frobeniusHomeomorph hI' ^ n) w).val := by
  induction n using Int.induction_on generalizing v w with
  | zero => simpa using h
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, Homeomorph.mul_apply, Homeomorph.mul_apply]
    exact ih (by simp [h])
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, Homeomorph.mul_apply, Homeomorph.mul_apply]
    exact ih (by simp [h])

/-- The map of orbit spaces induced by the identity of `𝒴`, when `ϖ` and `ϖ'` define the same
subset `𝒴`. It is well defined because the two Frobenius actions agree. -/
private def spaXMap (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : spaX hI → spaX hI' :=
  spaX.lift hI (fun v ↦ quotientMap hI' ⟨v.val, h ▸ v.property⟩) fun n _ ↦
    (quotientMap_eq_iff hI' _ _).mpr
      ⟨n, Subtype.ext (frobeniusHomeomorph_zpow_apply_val_eq hI' hI n rfl)⟩

private theorem spaXMap_quotientMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') (v : spaY p ϖ) :
    spaXMap hI hI' h (quotientMap hI v) = quotientMap hI' ⟨v.val, h ▸ v.property⟩ :=
  spaX.lift_quotientMap hI _ _ v

private theorem continuous_spaXMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : Continuous (spaXMap hI hI' h) := by
  rw [(isOpenQuotientMap_quotientMap hI).isQuotientMap.continuous_iff]
  have : spaXMap hI hI' h ∘ quotientMap hI =
      fun v ↦ quotientMap hI' ⟨v.val, h ▸ v.property⟩ :=
    funext (spaXMap_quotientMap hI hI' h)
  rw [this]
  exact (isOpenQuotientMap_quotientMap hI').continuous.comp
    (continuous_subtype_val.subtype_mk _)

private theorem spaXMap_spaXMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') (x : spaX hI) :
    spaXMap hI' hI h.symm (spaXMap hI hI' h x) = x := by
  induction x using spaX.inductionOn with
  | h v => rw [spaXMap_quotientMap, spaXMap_quotientMap]

/-- **The orbit spaces `𝒴 / φ^ℤ` for two pseudouniformisers are homeomorphic.** If `ϖ` and `ϖ'`
define the same subset `𝒴` of `Spa(𝕎 R, 𝕎 R)`, as they do when they generate ideals with the same
radical (`spaY_eq_of_radical_eq`), then the identity of `𝒴` descends to a homeomorphism of the
Frobenius orbit spaces, because the two Frobenius actions agree. -/
def spaXCongr (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : spaX hI ≃ₜ spaX hI' where
  toFun := spaXMap hI hI' h
  invFun := spaXMap hI' hI h.symm
  left_inv := spaXMap_spaXMap hI hI' h
  right_inv := spaXMap_spaXMap hI' hI h.symm
  continuous_toFun := continuous_spaXMap hI hI' h
  continuous_invFun := continuous_spaXMap hI' hI h.symm

/-- The homeomorphism of orbit spaces sends the orbit of a point of `𝒴` to its orbit. -/
@[simp]
theorem spaXCongr_quotientMap
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') (v : spaY p ϖ) :
    spaXCongr hI hI' h (quotientMap hI v) = quotientMap hI' ⟨v.val, h ▸ v.property⟩ :=
  spaXMap_quotientMap hI hI' h v

/-- The inverse of the homeomorphism of orbit spaces is the homeomorphism in the other direction. -/
@[simp]
theorem spaXCongr_symm
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))
    (h : spaY p ϖ = spaY p ϖ') : (spaXCongr hI hI' h).symm = spaXCongr hI' hI h.symm := (rfl)

/-! ### The pre-adic spaces `𝒳` -/

section SpaXPreAdic

open _root_.CategoryTheory

variable [IsTopologicalRing (WittVector p R)] (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
  (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))

/-- **The identification of the two pre-adic spaces `𝒴` intertwines their Frobenius
endomorphisms**: both are restrictions of the automorphism of `Spa(𝕎 R, 𝕎 R)` induced by `φ`. -/
@[reassoc]
theorem spaYPreAdicSpaceCongr_hom_comp_spaYFrobenius (h : spaY p ϖ = spaY p ϖ') :
    (spaYPreAdicSpaceCongr P hI hI' h).hom ≫ spaYFrobenius P hI' =
      spaYFrobenius P hI ≫ (spaYPreAdicSpaceCongr P hI hI' h).hom := by
  -- the codomain of the inclusion of `𝒴` is not syntactically the space of `Spa(𝕎 R, 𝕎 R)`, so the
  -- monomorphism instance of the inclusion is supplied by hand
  have : Mono ((spaPreAdicSpace P hI').ofRestrict (isOpenEmbedding_spaYInclusion p ϖ')) :=
    @PreAdicSpace.IsOpenImmersion.mono _ _ _ (PreAdicSpace.IsOpenImmersion.ofRestrict _ _)
  -- after composing with the inclusion `ι'` of `𝒴` into `Spa(𝕎 R, 𝕎 R)`, both sides are the
  -- inclusion followed by Frobenius on `Spa(𝕎 R, 𝕎 R)`; the two Frobenius automorphisms defined
  -- from `ϖ` and from `ϖ'` differ only in proofs of continuity
  refine (cancel_mono ((spaPreAdicSpace P hI').ofRestrict (isOpenEmbedding_spaYInclusion p ϖ'))).mp
    ((Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (spaYFrobenius_comp_ofRestrict P hI')).trans <|
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ _) (spaYPreAdicSpaceCongr_hom_ofRestrict P hI hI' h)).trans <|
          (spaYFrobenius_comp_ofRestrict P hI).symm.trans <|
            (congrArg (_ ≫ ·) (spaYPreAdicSpaceCongr_hom_ofRestrict P hI hI' h).symm).trans
              (Category.assoc _ _ _).symm)

/-- The inverse of `spaYPreAdicSpaceCongr` also intertwines the Frobenius endomorphisms. -/
@[reassoc]
theorem spaYPreAdicSpaceCongr_inv_comp_spaYFrobenius (h : spaY p ϖ = spaY p ϖ') :
    (spaYPreAdicSpaceCongr P hI hI' h).inv ≫ spaYFrobenius P hI =
      spaYFrobenius P hI' ≫ (spaYPreAdicSpaceCongr P hI hI' h).inv := by
  rw [Iso.inv_comp_eq, spaYPreAdicSpaceCongr_hom_comp_spaYFrobenius_assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **The pre-adic spaces `𝒳 = 𝒴 / φ^ℤ` for two pseudouniformisers are isomorphic.** If `ϖ` and
`ϖ'` define the same subset `𝒴` of `Spa(𝕎 R, 𝕎 R)`, as they do when they generate ideals with the
same radical (`spaY_eq_of_radical_eq`), and `𝒪_𝒴` is a sheaf, then the identification
`spaYPreAdicSpaceCongr` of the two pre-adic spaces `𝒴` descends to an isomorphism in `𝒱^pre` of the
Frobenius quotients, by their universal property (`isColimitQuotientPreAdicCofork`). On points it is
the homeomorphism `spaXCongr` (`spaXPreAdicSpaceCongr_hom_base`). -/
def spaXPreAdicSpaceCongr (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    spaXPreAdicSpace P hI hY ≅
      spaXPreAdicSpace P hI' (isSheaf_spaYPresheaf_of_spaY_eq P h hY) where
  hom := quotientPreAdicDesc ((spaYPreAdicSpaceCongr P hI hI' h).hom ≫ quotientPreAdicHom P hI' _)
    hY (by rw [← spaYPreAdicSpaceCongr_hom_comp_spaYFrobenius_assoc,
      spaYFrobenius_comp_quotientPreAdicHom])
  inv := quotientPreAdicDesc ((spaYPreAdicSpaceCongr P hI hI' h).inv ≫ quotientPreAdicHom P hI hY)
    _ (by rw [← spaYPreAdicSpaceCongr_inv_comp_spaYFrobenius_assoc,
      spaYFrobenius_comp_quotientPreAdicHom])
  hom_inv_id := quotientPreAdicHom_hom_ext (by simp)
  inv_hom_id := quotientPreAdicHom_hom_ext (by simp)

/-- The isomorphism of the pre-adic spaces `𝒳` is induced by the identification of the pre-adic
spaces `𝒴`. -/
@[reassoc (attr := simp)]
theorem quotientPreAdicHom_comp_spaXPreAdicSpaceCongr_hom (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    quotientPreAdicHom P hI hY ≫ (spaXPreAdicSpaceCongr P hI hI' h hY).hom =
      (spaYPreAdicSpaceCongr P hI hI' h).hom ≫ quotientPreAdicHom P hI' _ :=
  quotientPreAdicHom_comp_quotientPreAdicDesc ..

/-- On points, the isomorphism of the pre-adic spaces `𝒳` is the homeomorphism `spaXCongr` of the
orbit spaces. -/
@[simp]
theorem spaXPreAdicSpaceCongr_hom_base (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) (x : spaX hI) :
    (spaXPreAdicSpaceCongr P hI hI' h hY).hom.base x = spaXCongr hI hI' h x := by
  induction x using spaX.inductionOn with
  | h v =>
    -- on points, both projections to the orbit spaces are `quotientMap`
    have hq (ϖ₀ : R) (hI₀ : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ₀}))
        (hY₀ : (spaYPresheaf P ϖ₀).IsSheaf) (w : spaY p ϖ₀) :
        (quotientPreAdicHom P hI₀ hY₀).base w = quotientMap hI₀ w :=
      congrArg (fun f : (spaYPreAdicSpace P hI₀).toPresheafedSpace ⟶
        (spaXPreAdicSpace P hI₀ hY₀).toPresheafedSpace ↦ f.base w) (quotientPreAdicHom_toHom hY₀)
    have hc := congrArg (fun f ↦ f.base v)
      (quotientPreAdicHom_comp_spaXPreAdicSpaceCongr_hom P hI hI' h hY)
    rw [spaXCongr_quotientMap]
    exact (congrArg _ (hq ϖ hI hY v)).symm.trans (hc.trans ((hq ϖ' hI' _ _).trans
      (congrArg (quotientMap hI') (Subtype.ext (spaYPreAdicSpaceCongr_hom_base_val P hI hI' h v)))))

end SpaXPreAdic

/-! ### Frobenius on the adic spaces `𝒴`, and the adic spaces `𝒳` -/

section Adic

open _root_.CategoryTheory

variable [IsTopologicalRing (WittVector p R)] (P : PairOfDefinition (WittVector p R))
  (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
  (hI' : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ'}))

/-- **The identification of the two adic spaces `𝒴` intertwines Frobenius.** -/
@[reassoc]
theorem spaYAdicSpaceCongr_hom_comp_spaYAdicFrobenius (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    (spaYAdicSpaceCongr P hI hI' h hY).hom ≫ spaYAdicFrobenius P hI' _ =
      spaYAdicFrobenius P hI hY ≫ (spaYAdicSpaceCongr P hI hI' h hY).hom :=
  ObjectProperty.hom_ext _ (by
    simp only [ObjectProperty.FullSubcategory.comp_hom, spaYAdicFrobenius_hom,
      spaYAdicSpaceCongr_hom_hom]
    exact spaYPreAdicSpaceCongr_hom_comp_spaYFrobenius P hI hI' h)

/-- The inverse of `spaYAdicSpaceCongr` also intertwines Frobenius. -/
@[reassoc]
theorem spaYAdicSpaceCongr_inv_comp_spaYAdicFrobenius (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    (spaYAdicSpaceCongr P hI hI' h hY).inv ≫ spaYAdicFrobenius P hI hY =
      spaYAdicFrobenius P hI' _ ≫ (spaYAdicSpaceCongr P hI hI' h hY).inv := by
  rw [Iso.inv_comp_eq, spaYAdicSpaceCongr_hom_comp_spaYAdicFrobenius_assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **The adic Fargues–Fontaine curves `𝒳 = 𝒴 / φ^ℤ` for two pseudouniformisers are isomorphic.**
If `ϖ` and `ϖ'` define the same subset `𝒴` of `Spa(𝕎 R, 𝕎 R)`, as they do when they generate ideals
with the same radical (`spaY_eq_of_radical_eq`), and `𝒪_𝒴` is a sheaf, then the isomorphism
`spaXPreAdicSpaceCongr` of pre-adic spaces is an isomorphism in the full subcategory `(Adic)`. It is
the isomorphism induced by `spaYAdicSpaceCongr` on the quotients by Frobenius
(`quotientAdicHom_comp_spaXAdicSpaceCongr_hom`), and on points it is the homeomorphism
`spaXCongr` of orbit spaces (`spaXPreAdicSpaceCongr_hom_base`). When `R` is the ring of integers of
a valuation on a field and `ϖ` is a pseudouniformiser, `𝒪_𝒴` is a sheaf by
`isSheaf_spaYPresheaf`. -/
def spaXAdicSpaceCongr (h : spaY p ϖ = spaY p ϖ') (hY : (spaYPresheaf P ϖ).IsSheaf) :
    spaXAdicSpace P hI hY ≅
      spaXAdicSpace P hI' (isSheaf_spaYPresheaf_of_spaY_eq P h hY) :=
  ObjectProperty.isoMk _ (spaXPreAdicSpaceCongr P hI hI' h hY)

/-- The morphism of pre-adic spaces underlying `spaXAdicSpaceCongr` is `spaXPreAdicSpaceCongr`. -/
@[simp]
theorem spaXAdicSpaceCongr_hom_hom (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    (spaXAdicSpaceCongr P hI hI' h hY).hom.hom = (spaXPreAdicSpaceCongr P hI hI' h hY).hom :=
  (rfl)

/-- The morphism of pre-adic spaces underlying the inverse of `spaXAdicSpaceCongr` is the inverse
of `spaXPreAdicSpaceCongr`. -/
@[simp]
theorem spaXAdicSpaceCongr_inv_hom (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    (spaXAdicSpaceCongr P hI hI' h hY).inv.hom = (spaXPreAdicSpaceCongr P hI hI' h hY).inv :=
  (rfl)

/-- **The isomorphism of the adic spaces `𝒳` is induced by the identification of the adic spaces
`𝒴`**: it commutes with the projections `𝒴 → 𝒳`. Together with the universal property of `𝒳`
(`isColimitQuotientAdicCofork`) this determines it. -/
@[reassoc (attr := simp)]
theorem quotientAdicHom_comp_spaXAdicSpaceCongr_hom (h : spaY p ϖ = spaY p ϖ')
    (hY : (spaYPresheaf P ϖ).IsSheaf) :
    quotientAdicHom P hI hY ≫ (spaXAdicSpaceCongr P hI hI' h hY).hom =
      (spaYAdicSpaceCongr P hI hI' h hY).hom ≫ quotientAdicHom P hI' _ :=
  ObjectProperty.hom_ext _ (by
    simp only [ObjectProperty.FullSubcategory.comp_hom, quotientAdicHom_hom,
      spaXAdicSpaceCongr_hom_hom, spaYAdicSpaceCongr_hom_hom]
    exact quotientPreAdicHom_comp_spaXPreAdicSpaceCongr_hom P hI hI' h hY)

/-- Over the ring of integers `𝒪_F` of a nonarchimedean normed field `F`, perfect of characteristic
`p`, any two pseudouniformisers `ϖ` and `ϖ'` give isomorphic adic spaces `𝒳`, with no sheaf
hypothesis: `𝒪_𝒴` is a sheaf by `isSheaf_spaYPresheaf`, and `ϖ` and `ϖ'` define the same `𝒴`. -/
example {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra R F]
    (hv : (NormedField.valuation (K := F)).Integers R) (hϖ₀ : ϖ ≠ 0)
    (hϖ : ‖algebraMap R F ϖ‖ < 1) (hϖ'₀ : ϖ' ≠ 0) (hϖ' : ‖algebraMap R F ϖ'‖ < 1) :
    spaXAdicSpace P hI (isSheaf_spaYPresheaf hI hv hϖ₀ (by simpa [← NNReal.coe_lt_coe] using hϖ)) ≅
      spaXAdicSpace P hI' (isSheaf_spaYPresheaf hI' hv hϖ'₀
        (by simpa [← NNReal.coe_lt_coe] using hϖ')) :=
  spaXAdicSpaceCongr P hI hI'
    (spaY_eq_of_radical_eq (hv.radical_span_singleton_eq_of_norm_lt_one hϖ₀ hϖ hϖ'₀ hϖ')) _

end Adic

end TauCeti.FarguesFontaine
