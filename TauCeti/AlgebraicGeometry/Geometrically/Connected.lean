/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Connected.CardComponents
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Geometric connectedness: affine products and rational points

This file proves that the spectrum of a tensor product of commutative algebras is geometrically
connected when the spectra of both factors are geometrically connected and universally open over
the base, as they always are over a field. The tensor product spectrum is identified with the
fibre product of the two spectra over the base.

It also proves that a connected scheme `X` over a field `k` with a `k`-rational point, that is, a
section of its structure morphism, is geometrically connected. The rational point is needed: for a
separable quadratic extension `L` of `k`, the connected scheme `Spec L` becomes two points over
`L`. Smooth connected schemes with a rational point are therefore geometrically integral
(`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral_of_section`).

## Implementation notes

The proof first base changes to the algebraic closure `Ω` of `k`. The projection `X_Ω ⟶ X` is
open and, being integral, closed, and its fibre over the rational point is a single point, so
`X_Ω` has a single connected component by Mathlib's
`IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`. A field `K` over `k` embeds
together with `Ω` into a common field `M`. Since `Ω` is algebraically closed, `Spec M ⟶ Spec Ω` is
geometrically connected, so `X_M` is connected, and it surjects onto `X_K`.

## Main declarations

* `TauCeti.geometricallyConnected_respectsIso`: geometric connectedness of morphisms of schemes
  respects isomorphisms.
* `TauCeti.geometricallyConnected_tensorProduct`: the tensor product of two commutative algebras
  with geometrically connected, universally open spectra is geometrically connected.
* `TauCeti.geometricallyConnected_of_section`: a connected scheme over a field with a rational
  point is geometrically connected.

## References

* [The Stacks Project, Lemma 33.7.14 (04KV)](https://stacks.math.columbia.edu/tag/04KV), the case
  of a rational point.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

universe u

/-- Geometric connectedness of morphisms of schemes respects isomorphisms, being stable under
base change. -/
instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

section TensorProduct

variable {k : Type u} [CommRing k]

/-- The spectrum of a tensor product of commutative `k`-algebras is geometrically connected over
`k` when the spectra of both factors are geometrically connected and universally open over `k`.
Universal openness is automatic when `k` is a field. -/
theorem geometricallyConnected_tensorProduct
    (S T : Type u) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    [UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap k S)))]
    [UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap k T)))]
    (hS : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (hT : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k T)))) :
    GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k (S ⊗[k] T)))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
    (pullbackSpecIso k S T).hom, pullbackSpecIso_hom_base]
  exact .comp _ _

end TensorProduct

section RationalPoint

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [ConnectedSpace X]
  {s : Spec (.of k) ⟶ X}

/-- A connected scheme over a field `k` with a rational point stays connected after base change
to an algebraic field extension of `k`. -/
private theorem connectedSpace_pullback_of_isIntegralHom (hs : s ≫ f = 𝟙 _) {L : Type u}
    [Field L] (g : Spec (.of L) ⟶ Spec (.of k)) [IsIntegralHom g] :
    ConnectedSpace (pullback f g : Scheme.{u}) := by
  let p := pullback.fst f g
  have : Nonempty (pullback f g : Scheme.{u}) := p.surjective.nonempty
  -- The fibre of `p` over the rational point is the base change of `s`, a single point.
  have hfib : (p ⁻¹' {s default}).Subsingleton := by
    let e : pullback p s ≅ Spec (.of L) := pullbackSymmetry p s ≪≫
      pullbackRightPullbackFstIso f g s ≪≫ pullback.congrHom hs rfl ≪≫
      asIso (pullback.snd (𝟙 _) g)
    have : Subsingleton (pullback p s : Scheme.{u}) := e.hom.homeomorph.injective.subsingleton
    rw [← Set.range_unique, ← Scheme.Pullback.range_fst]
    exact Set.subsingleton_range _
  have : Subsingleton (_root_.ConnectedComponents (pullback f g : Scheme.{u})) :=
    (ENat.card_le_one_iff_subsingleton _).mp
      ((p.isOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton p.isClosedMap
        (s default)).trans (Set.encard_le_one_iff_subsingleton.mpr hfib))
  have : PreconnectedSpace (pullback f g : Scheme.{u}) :=
    preconnectedSpace_iff_connectedComponent.mpr fun x ↦ Set.eq_univ_of_forall fun y ↦
      ConnectedComponents.coe_eq_coe.mp (Subsingleton.elim
        (y : _root_.ConnectedComponents (pullback f g : Scheme.{u})) x) ▸ mem_connectedComponent
  exact ⟨inferInstance⟩

/-- **A connected scheme with a rational point is geometrically connected.** If `X` is a
connected scheme over a field `k` and the structure morphism `f : X ⟶ Spec k` has a section `s`,
then `X ×_k Spec K` is connected for every field `K` over `k`. -/
theorem geometricallyConnected_of_section (hs : s ≫ f = 𝟙 _) : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  let ι : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsIntegralHom ι :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  have := connectedSpace_pullback_of_isIntegralHom hs ι
  -- A field `M` over both `K` and the algebraic closure: a residue field of their product.
  obtain ⟨z⟩ : Nonempty (pullback x ι : Scheme.{u}) := (pullback.fst x ι).surjective.nonempty
  let M : Type u := (pullback x ι).residueField z
  let m : Spec (.of M) ⟶ pullback x ι := (pullback x ι).fromSpecResidueField z
  let a := m ≫ pullback.fst x ι
  let b := m ≫ pullback.snd x ι
  have hab : b ≫ ι = a ≫ x := by simp [a, b, pullback.condition]
  -- `Spec M ⟶ Spec Ω` is geometrically connected, so `X_M = X_Ω ×_Ω Spec M` is connected.
  have : ConnectedSpace (pullback f (a ≫ x) : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso f ι b ≪≫ pullback.congrHom rfl hab).hom.homeomorph
      |>.connectedSpace_iff.mp inferInstance
  have : ConnectedSpace (pullback (pullback.snd f x) a : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso f x a).inv.homeomorph.connectedSpace_iff.mp inferInstance
  -- `X_M ⟶ X_K` is surjective.
  exact (pullback.fst (pullback.snd f x) a).surjective.connectedSpace
    (pullback.fst (pullback.snd f x) a).continuous

end RationalPoint

end TauCeti
