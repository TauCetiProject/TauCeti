/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Flat
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic

/-!
# Restriction maps of the structure presheaf between rational opens are flat

**Wedhorn's Proposition 8.30** for the structure presheaf: let `A` be a strongly noetherian Tate
ring and `X = Spa(A, A⁺)`. For rational subsets `V ⊆ U` of `X`, the restriction map
`𝒪_X(U) → 𝒪_X(V)` is flat.

On a rational open the presentation limit is the coordinate ring `A⟨T/s⟩`
(`TauCeti.ValuationSpectrum.presentationLimitRationalIso`), and under these identifications the
restriction map is the comparison map of Proposition 8.2(1)
(`TauCeti.ValuationSpectrum.presentationLimitRationalIso_inv_comp_map_comp_hom`). That comparison
map is flat by `TauCeti.ValuationSpectrum.flat_ringHomOfRationalSubsetSubset`, and flatness is
unchanged by composing with isomorphisms.

## Main results

* `TauCeti.ValuationSpectrum.flat_presentationLimitMap`: the restriction map of the presentation
  limit between rational opens is flat.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.30.
-/

open CategoryTheory TauCeti.Huber TauCeti.Huber.PairOfDefinition

public section

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A}

variable (Aplus : Subring A) in
/-- **Wedhorn's Proposition 8.30 for the structure presheaf.** Over a strongly noetherian Tate ring
`A`, let `p` and `q` be admissible presentations with `R(q) ⊆ R(p)` in `Spa(A, A⁺)`. Then the
restriction map `𝒪_X(R(p)) → 𝒪_X(R(q))` of the presentation limit is flat, as a homomorphism of
the underlying rings. -/
theorem flat_presentationLimitMap [IsTateRing A] [IsStronglyNoetherian A]
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (p q : Presentation P)
    (hp : IsOpen (Ideal.span (p.num : Set A) : Set A))
    (hq : IsOpen (Ideal.span (q.num : Set A) : Set A))
    (h : spaBasicOpen Aplus q.num q.den ≤ spaBasicOpen Aplus p.num p.den) :
    ((TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat).map
      (presentationLimitMap (P := P) h)).hom.Flat := by
  let _ := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  let _ := locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isUniformAddGroup_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  have _ := isTopologicalRing_locUniformSpace P q.num q.den _ q.hasDenominatorPower
  let F := TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat
  have hsub := spaBasicOpen_le_spaBasicOpen_iff.mp h
  have hspan : Ideal.span (insert p.den (p.num : Set A)) = ⊤ :=
    eq_top_mono (Ideal.span_mono (Set.subset_insert _ _))
      ((IsTateRing.isOpen_iff_eq_top _).mp hp)
  -- on rational opens the presentation limit is the coordinate ring, and there the restriction map
  -- is the comparison morphism
  have hlim : presentationLimitMap (P := P) h =
      (presentationLimitRationalIso Aplus hAplus p hp).hom ≫
        homOfRationalSubsetSubset Aplus hAplus hsub ≫
          (presentationLimitRationalIso Aplus hAplus q hq).inv := by
    rw [← presentationLimitRationalIso_inv_comp_map_comp_hom Aplus hAplus p q hp hq h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  -- on underlying rings, the comparison morphism is the comparison ring homomorphism
  have hring : F.map (homOfRationalSubsetSubset Aplus hAplus hsub) =
      p.completionLocObjCommRingCatIso.hom ≫
        CommRingCat.ofHom (ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _
          p.hasDenominatorPower q.num q.den _ q.hasDenominatorPower hsub) ≫
        q.completionLocObjCommRingCatIso.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact map_homOfRationalSubsetSubset_comp_completionLocObjCommRingCatIso_hom hAplus hsub
  -- so the restriction map is the comparison ring homomorphism between isomorphisms, which do not
  -- affect flatness
  rw [hlim, F.map_comp, F.map_comp, hring]
  simp only [Category.assoc]
  rw [CommRingCat.hom_comp, RingHom.Flat.respectsIso.cancel_left_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_left_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso]
  exact flat_ringHomOfRationalSubsetSubset P Aplus hAplus p.num p.den _ p.hasDenominatorPower q.num
    q.den _ q.hasDenominatorPower hsub hspan

end TauCeti.ValuationSpectrum
