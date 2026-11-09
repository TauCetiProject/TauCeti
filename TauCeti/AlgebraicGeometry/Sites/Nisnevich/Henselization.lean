/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Henselization
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Henselian

/-!
# Nisnevich coverings and henselizations of local rings

A family of étale morphisms is a Nisnevich covering exactly when, for every point `x` of the
base, the morphism `Spec 𝒪ʰ_{X,x} ⟶ X` from the spectrum of the henselization of the local ring
at `x` lifts to one of its members. One direction lifts `Spec 𝒪ʰ_{X,x} ⟶ X` along an étale
morphism through a point with unchanged residue field, using that `𝒪ʰ_{X,x}` is henselian
(`AlgebraicGeometry.Scheme.Hom.exists_lift_of_isIso_residueFieldMap`). Conversely, a lift sends
the closed point to such a point, since `𝒪_{X,x} → 𝒪ʰ_{X,x}` induces an isomorphism of residue
fields (`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap_of_lift`).

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.isNisnevichCovering_iff_henselization`: a family of étale
  morphisms is a Nisnevich covering if and only if, for every point `x`, the morphism
  `Spec 𝒪ʰ_{X,x} ⟶ X` lifts to one of its members, that is, the base change of one member to
  `Spec 𝒪ʰ_{X,x}` has a section.

## Implementation notes

The criterion holds for arbitrary families over an arbitrary base: neither finiteness of the
family nor a Noetherian base is needed. A section of the base change of one member to
`Spec 𝒪ʰ_{X,x}` is recorded as the equivalent datum of a lift of `Spec 𝒪ʰ_{X,x} ⟶ X`.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Proposition 1.1.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Scheme

/-- **The henselization criterion for Nisnevich coverings.** A family of étale morphisms
`{fᵢ : Xᵢ ⟶ S}` is a Nisnevich covering if and only if, for every point `s` of `S`, the morphism
`Spec 𝒪ʰ_{S,s} ⟶ S` lifts to some `Xᵢ`; equivalently, the base change of some `fᵢ` to
`Spec 𝒪ʰ_{S,s}` has a section. Morel–Voevodsky, §3.1, Proposition 1.1. -/
theorem isNisnevichCovering_iff_henselization {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) :
    IsNisnevichCovering f ↔ (∀ i, Etale (f i)) ∧
      ∀ s : S, ∃ i, ∃ t : Spec (S.henselization s) ⟶ X i, t ≫ f i = S.fromSpecHenselization s := by
  refine ⟨fun hf ↦ ⟨hf.etale, fun s ↦ ?_⟩, fun ⟨hf, h⟩ ↦ ⟨hf, fun s ↦ ?_⟩⟩
  · obtain ⟨i, x, rfl, hx⟩ := hf.exists_isIso s
    have := hf.etale i
    obtain ⟨t, ht⟩ := (f i).exists_lift_of_isIso_residueFieldMap x
      (S.toHenselization (f i x))
    exact ⟨i, t, ht.trans (S.fromSpecHenselization_def _).symm⟩
  · obtain ⟨i, t, ht⟩ := h s
    obtain ⟨hx, hiso⟩ := (f i).isIso_residueFieldMap_of_lift
      (S.toHenselization s) (Henselization.residueField_map_bijective _) t
      (ht.trans (S.fromSpecHenselization_def s))
    exact ⟨i, _, hx, hiso⟩

end TauCeti.AlgebraicGeometry.Scheme
