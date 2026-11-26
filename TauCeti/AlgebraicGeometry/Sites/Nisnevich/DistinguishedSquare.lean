/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic
import TauCeti.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Elementary distinguished squares

An *elementary distinguished square* over a scheme `X` (Morel–Voevodsky, §3.1, Definition 1.3) is a
pair of morphisms `j : U ⟶ X` and `p : V ⟶ X` with `j` an open immersion and `p` étale, such that
`p` is an isomorphism over the closed complement of `U`: the base change of `p` to the reduced
closed subscheme `Z = (X ∖ U)_red` is an isomorphism `p⁻¹(Z) ⟶ Z`. Since `p` is étale and `Z` is
reduced, `p⁻¹(Z)` is already reduced, so this is the condition `p⁻¹(Z)_red ≅ Z_red` of
Morel–Voevodsky. The square itself is the fibre product square of `j` and `p`.

The pair `{j, p}` is a Nisnevich covering of `X`
(`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isNisnevichCovering`): points of
`U` lift along the open immersion `j`, and a point `x` of the complement lifts to the point of
`p⁻¹(Z) ≅ Z` over it, where `p` induces an isomorphism of residue fields because the composite
`p⁻¹(Z) ⟶ Z ⟶ X` does. Every open cover `X = U ∪ V` by two opens gives an elementary distinguished
square (`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.ofZariski`).

Elementary distinguished squares are stable under base change along any `g : Y ⟶ X`
(`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.pullback`): `g` maps the reduced
closed complement `Z'` of `U ×_X Y` in `Y` into the complement of `U`, so, `Z'` being reduced,
`Z' ⟶ Y ⟶ X` factors through `Z`, and the base change of `p` to `Z'` is the base change of the
isomorphism `p⁻¹(Z) ⟶ Z` along `Z' ⟶ Z`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare X`: an elementary distinguished
  square over `X`.
* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.ofZariski`: the square of an open
  cover `X = U ∪ V`, whose `p` is the open immersion of `V`.
* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.pullback`: the base change of a
  square along a morphism `Y ⟶ X`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isNisnevichCovering`: `{j, p}` is
  a Nisnevich covering.
* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.ofArrows_mem_nisnevichTopology`:
  it generates a covering sieve of the Nisnevich topology.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Definition 1.3.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry.Scheme

/-- An **elementary distinguished square** over `X` (Morel–Voevodsky, §3.1, Definition 1.3): an
open immersion `j : U ⟶ X` and an étale morphism `p : V ⟶ X` such that the base change of `p` to
the reduced closed complement `Z = (X ∖ U)_red` of `U` is an isomorphism `p⁻¹(Z) ⟶ Z`. -/
structure ElementaryDistinguishedSquare (X : AlgebraicGeometry.Scheme.{u}) where
  /-- The open subscheme. -/
  U : AlgebraicGeometry.Scheme.{u}
  /-- The étale neighbourhood of the complement. -/
  V : AlgebraicGeometry.Scheme.{u}
  /-- The open immersion `U ⟶ X`. -/
  j : U ⟶ X
  /-- The étale morphism `V ⟶ X`. -/
  p : V ⟶ X
  [isOpenImmersion_j : IsOpenImmersion j]
  [etale_p : Etale p]
  /-- `p` is an isomorphism over the reduced closed complement of `U`. -/
  isIso_pullback_snd :
    IsIso (pullback.snd p
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl).subschemeι)

namespace ElementaryDistinguishedSquare

attribute [instance] isOpenImmersion_j etale_p isIso_pullback_snd

variable {X : AlgebraicGeometry.Scheme.{u}} (Q : ElementaryDistinguishedSquare X)

/-- The two morphisms `j` and `p` of an elementary distinguished square, indexed by `Bool`
(`true ↦ j`, `false ↦ p`). -/
abbrev arrows : ∀ b : Bool, (Bool.rec Q.V Q.U b : AlgebraicGeometry.Scheme.{u}) ⟶ X :=
  Bool.rec (motive := fun b ↦ (Bool.rec Q.V Q.U b : AlgebraicGeometry.Scheme.{u}) ⟶ X) Q.p Q.j

/-- A point of `X` lies in the reduced closed complement of an open `U` if and only if it lies
outside `U`. -/
private lemma mem_range_subschemeι_vanishingIdeal_compl_iff (U : X.Opens) (x : X) :
    x ∈ Set.range
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal U.compl).subschemeι ↔ x ∉ U := by
  rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι,
    AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
  simp

/-- Every point of `X` outside the image of `j` has a preimage under `p` at which `p` induces an
isomorphism of residue fields. -/
theorem exists_isIso_residueFieldMap_p (x : X) (hx : x ∉ Set.range Q.j) :
    ∃ v : Q.V, Q.p v = x ∧ IsIso (Q.p.residueFieldMap v) := by
  set I := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Q.j.opensRange.compl
  have hxI : x ∈ Set.range I.subschemeι :=
    (mem_range_subschemeι_vanishingIdeal_compl_iff _ x).2 (by simpa using hx)
  obtain ⟨z, rfl⟩ := hxI
  obtain ⟨w, rfl⟩ : ∃ w, pullback.snd Q.p I.subschemeι w = z :=
    ⟨inv (pullback.snd Q.p I.subschemeι) z, by
      simp [← AlgebraicGeometry.Scheme.Hom.comp_apply]⟩
  refine ⟨pullback.fst Q.p I.subschemeι w, ?_, ?_⟩
  · rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, pullback.condition,
      AlgebraicGeometry.Scheme.Hom.comp_apply]
  · have : IsIso ((pullback.fst Q.p I.subschemeι ≫ Q.p).residueFieldMap w) := by
      rw [pullback.condition]
      infer_instance
    exact AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_comp _ _ w

/-- **An elementary distinguished square is a Nisnevich covering**: `{j, p}` is a Nisnevich
covering of `X`. -/
theorem isNisnevichCovering : IsNisnevichCovering Q.arrows where
  etale b := by cases b <;> dsimp <;> infer_instance
  exists_isIso x := by
    by_cases hx : x ∈ Set.range Q.j
    · obtain ⟨u, rfl⟩ := hx
      exact ⟨true, u, rfl, inferInstance⟩
    · obtain ⟨v, hv, hiso⟩ := Q.exists_isIso_residueFieldMap_p x hx
      exact ⟨false, v, hv, hiso⟩

/-- The sieve generated by `j` and `p` covers `X` in the Nisnevich topology. -/
theorem ofArrows_mem_nisnevichTopology :
    Sieve.ofArrows _ Q.arrows ∈ nisnevichTopology X :=
  Precoverage.generate_mem_toGrothendieck
    (ofArrows_mem_nisnevichPrecoverage_iff.2 Q.isNisnevichCovering)

/-- The elementary distinguished square of an open cover `X = U ∪ V` by two opens: `j` and `p` are
the open immersions of `U` and `V`. -/
@[expose]
noncomputable def ofZariski (U V : X.Opens) (h : U ⊔ V = ⊤) : ElementaryDistinguishedSquare X where
  U := U
  V := V
  j := U.ι
  p := V.ι
  isIso_pullback_snd := by
    -- Over the complement of `U`, the open immersion of `V` is surjective, so its base change
    -- there is a surjective open immersion.
    set I := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal U.ι.opensRange.compl
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, ⟨fun z ↦ ?_⟩⟩
    have hz : I.subschemeι z ∈ V := by
      have hzU : I.subschemeι z ∉ U := by
        simpa using (mem_range_subschemeι_vanishingIdeal_compl_iff _ _).1 ⟨z, rfl⟩
      have : I.subschemeι z ∈ U ⊔ V := h ▸ Opens.mem_top _
      exact (Opens.mem_sup.1 this).resolve_left hzU
    obtain ⟨v, hv⟩ : I.subschemeι z ∈ Set.range V.ι := by simpa using hz
    obtain ⟨w, -, hw⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback v z hv
    exact ⟨w, hw⟩

@[simp]
lemma ofZariski_j (U V : X.Opens) (h : U ⊔ V = ⊤) : (ofZariski U V h).j = U.ι :=
  rfl

@[simp]
lemma ofZariski_p (U V : X.Opens) (h : U ⊔ V = ⊤) : (ofZariski U V h).p = V.ι :=
  rfl

section Pullback

variable {Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)

/-- **Base change of an elementary distinguished square** along `g : Y ⟶ X`: the open immersion
`U ×_X Y ⟶ Y` and the étale morphism `V ×_X Y ⟶ Y`. -/
@[expose]
noncomputable def pullback : ElementaryDistinguishedSquare Y where
  U := Limits.pullback Q.j g
  V := Limits.pullback Q.p g
  j := Limits.pullback.snd Q.j g
  p := Limits.pullback.snd Q.p g
  isIso_pullback_snd := by
    set I := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Q.j.opensRange.compl
    set I' := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      (Limits.pullback.snd Q.j g).opensRange.compl
    have hrange : Set.range (I'.subschemeι ≫ g) ⊆ (Q.j.opensRange.compl : Set X) := by
      rintro _ ⟨z, rfl⟩
      have hz : I'.subschemeι z ∉ Set.range (Limits.pullback.snd Q.j g) := by
        simpa using (mem_range_subschemeι_vanishingIdeal_compl_iff _ _).1 ⟨z, rfl⟩
      rw [AlgebraicGeometry.Scheme.Pullback.range_snd] at hz
      simpa using hz
    have hker : I.subschemeι.ker ≤ (I'.subschemeι ≫ g).ker := by
      rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
      exact AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset _ hrange
    -- `Z' ⟶ Y ⟶ X` factors through `Z ⟶ X`.
    have hh := IsClosedImmersion.lift_fac I.subschemeι (I'.subschemeι ≫ g) hker
    -- So the base change of `p` to `Z'` is a base change of the isomorphism `p⁻¹(Z) ⟶ Z`.
    exact MorphismProperty.pullback_snd_pullback_snd (P := .isomorphisms _) Q.p g I'.subschemeι
      I.subschemeι _ hh.symm Q.isIso_pullback_snd

@[simp]
lemma pullback_j : (Q.pullback g).j = Limits.pullback.snd Q.j g :=
  rfl

@[simp]
lemma pullback_p : (Q.pullback g).p = Limits.pullback.snd Q.p g :=
  rfl

end Pullback

end ElementaryDistinguishedSquare

end TauCeti.AlgebraicGeometry.Scheme
