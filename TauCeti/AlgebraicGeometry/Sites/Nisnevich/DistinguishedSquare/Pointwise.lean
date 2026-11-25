/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.UniversallyInjective
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# The pointwise criterion for elementary distinguished squares

Let `j : U ⟶ X` be an open immersion and `p : V ⟶ X` an étale morphism. The pair is an elementary
distinguished square (`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare`), that is,
the base change of `p` to the reduced closed complement `Z` of `U` is an isomorphism, if and only
if every point `x` of `X` outside `U` has exactly one preimage `v` under `p`, and `p` induces an
isomorphism of residue fields at `v`
(`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isIso_pullback_snd_iff`).

Uniqueness among all preimages is essential: `X = Spec ℝ`, `U = ∅`, `V = Spec ℝ ⊔ Spec ℂ` has
exactly one preimage with residue field `ℝ` and is not an elementary distinguished square. No
finiteness of `p⁻¹(Z) ⟶ Z` is needed: the base change is étale, injective with trivial residue
field extensions, hence universally injective
(`AlgebraicGeometry.UniversallyInjective.of_injective_of_isIso_residueFieldMap`) and so an open
immersion, and it is surjective.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.ofPointwise`: the elementary
  distinguished square of `j` and `p` under the pointwise hypotheses.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isIso_pullback_snd_iff`: the
  pointwise criterion.
* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.eq_of_p_eq`: over the complement
  of `U`, the étale morphism of an elementary distinguished square is injective.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Definition 1.3: the defining condition that the criterion here characterises.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData
  (mem_range_subschemeι_vanishingIdeal_opensRange_compl_iff)

universe u

namespace TauCeti.AlgebraicGeometry.Scheme

namespace ElementaryDistinguishedSquare

section Pointwise

variable {X U V : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) (p : V ⟶ X) [IsOpenImmersion j]
  [Etale p]

/-- **The pointwise criterion**, sufficiency direction, for the defining condition of an
elementary distinguished square (Morel–Voevodsky 1999, §3.1, Definition 1.3): for an open immersion
`j` and an étale `p`, the base change of `p` to the reduced closed complement of `U` is an
isomorphism if every point outside `U` has exactly one preimage under `p`, at which `p` induces an
isomorphism of residue fields. -/
theorem isIso_pullback_snd_of_pointwise (h : ∀ x ∉ Set.range j, ∃! v, p v = x)
    (hres : ∀ v, p v ∉ Set.range j → IsIso (p.residueFieldMap v)) :
    IsIso (pullback.snd p
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).subschemeι) := by
  set ι := (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).subschemeι
  have hι (z) : ι z ∉ Set.range j :=
    (mem_range_subschemeι_vanishingIdeal_opensRange_compl_iff _ _).1 ⟨z, rfl⟩
  have hcond (w) : p (pullback.fst p ι w) = ι (pullback.snd p ι w) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, pullback.condition,
      AlgebraicGeometry.Scheme.Hom.comp_apply]
  -- Every point of `p⁻¹(Z)` lies over a point outside `U`.
  have hw (w) : p (pullback.fst p ι w) ∉ Set.range j := hcond w ▸ hι _
  have hsurj : Surjective (pullback.snd p ι) := ⟨fun z ↦ by
    obtain ⟨v, hv, -⟩ := h (ι z) (hι z)
    obtain ⟨w, -, hw⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback v z hv
    exact ⟨w, hw⟩⟩
  have hinj : Function.Injective (pullback.snd p ι) := by
    intro w₁ w₂ hw₁₂
    have hfst : pullback.fst p ι w₁ = pullback.fst p ι w₂ := by
      refine (h _ (hw w₂)).unique ?_ rfl
      rw [hcond, hw₁₂, hcond]
    exact AlgebraicGeometry.Scheme.Pullback.eq_of_fst_eq_snd_eq_of_isIso hfst hw₁₂
  have hres' (w) : IsIso ((pullback.snd p ι).residueFieldMap w) :=
    have := hres _ (hw w)
    AlgebraicGeometry.Scheme.Pullback.isIso_residueFieldMap_snd w
  have := UniversallyInjective.of_injective_of_isIso_residueFieldMap _ hinj hres'
  exact isIso_of_etale_of_universallyInjective_of_surjective _

/-- The elementary distinguished square of an open immersion `j` and an étale `p` such that every
point outside `U` has exactly one preimage under `p`, at which `p` induces an isomorphism of
residue fields. -/
@[expose]
noncomputable def ofPointwise (h : ∀ x ∉ Set.range j, ∃! v, p v = x)
    (hres : ∀ v, p v ∉ Set.range j → IsIso (p.residueFieldMap v)) :
    ElementaryDistinguishedSquare X where
  U := U
  V := V
  j := j
  p := p
  isIso_pullback_snd := isIso_pullback_snd_of_pointwise j p h hres

@[simp]
lemma ofPointwise_j (h : ∀ x ∉ Set.range j, ∃! v, p v = x)
    (hres : ∀ v, p v ∉ Set.range j → IsIso (p.residueFieldMap v)) :
    (ofPointwise j p h hres).j = j :=
  rfl

@[simp]
lemma ofPointwise_p (h : ∀ x ∉ Set.range j, ∃! v, p v = x)
    (hres : ∀ v, p v ∉ Set.range j → IsIso (p.residueFieldMap v)) :
    (ofPointwise j p h hres).p = p :=
  rfl

end Pointwise

variable {X : AlgebraicGeometry.Scheme.{u}} (Q : ElementaryDistinguishedSquare X)

/-- Over the complement of `U`, the étale morphism of an elementary distinguished square is
injective. -/
theorem eq_of_p_eq {v₁ v₂ : Q.V} (h : Q.p v₁ = Q.p v₂) (hv : Q.p v₂ ∉ Set.range Q.j) :
    v₁ = v₂ := by
  set ι := (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Q.j.opensRange.compl).subschemeι
  obtain ⟨z, hz⟩ : Q.p v₂ ∈ Set.range ι :=
    (mem_range_subschemeι_vanishingIdeal_opensRange_compl_iff _ _).2 hv
  obtain ⟨w₁, hw₁, hw₁'⟩ :=
    AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback v₁ z (h.trans hz.symm)
  obtain ⟨w₂, hw₂, hw₂'⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback v₂ z hz.symm
  obtain rfl : w₁ = w₂ :=
    (AlgebraicGeometry.Scheme.homeoOfIso (asIso (pullback.snd Q.p ι))).injective
      (hw₁'.trans hw₂'.symm)
  exact hw₁.symm.trans hw₂

/-- Every point outside `U` has exactly one preimage under the étale morphism of an elementary
distinguished square. -/
theorem existsUnique_p_eq (x : X) (hx : x ∉ Set.range Q.j) : ∃! v, Q.p v = x := by
  obtain ⟨v, hv, -⟩ := Q.exists_isIso_residueFieldMap_p x hx
  exact ⟨v, hv, fun v' hv' ↦ Q.eq_of_p_eq (hv'.trans hv.symm) (hv ▸ hx)⟩

/-- At every point over the complement of `U`, the étale morphism of an elementary distinguished
square induces an isomorphism of residue fields. -/
theorem isIso_residueFieldMap_p (v : Q.V) (hv : Q.p v ∉ Set.range Q.j) :
    IsIso (Q.p.residueFieldMap v) := by
  obtain ⟨v', hv', hiso⟩ := Q.exists_isIso_residueFieldMap_p _ hv
  obtain rfl := Q.eq_of_p_eq hv' (hv' ▸ hv)
  exact hiso

/-- **The pointwise criterion**, characterising the defining condition of an elementary
distinguished square (Morel–Voevodsky 1999, §3.1, Definition 1.3): for an open immersion `j` and an
étale `p`, the base change of `p` to the reduced closed complement of `U` is an isomorphism if and
only if every point outside `U` has exactly one preimage under `p`, and `p`
induces an isomorphism of residue fields at it. -/
theorem isIso_pullback_snd_iff {U V : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) (p : V ⟶ X)
    [IsOpenImmersion j] [Etale p] :
    IsIso (pullback.snd p
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).subschemeι) ↔
      (∀ x ∉ Set.range j, ∃! v, p v = x) ∧
        ∀ v, p v ∉ Set.range j → IsIso (p.residueFieldMap v) := by
  refine ⟨fun h ↦ ?_, fun ⟨h, hres⟩ ↦ isIso_pullback_snd_of_pointwise j p h hres⟩
  let Q : ElementaryDistinguishedSquare X := ⟨U, V, j, p, h⟩
  exact ⟨Q.existsUnique_p_eq, Q.isIso_residueFieldMap_p⟩

end ElementaryDistinguishedSquare

end TauCeti.AlgebraicGeometry.Scheme
