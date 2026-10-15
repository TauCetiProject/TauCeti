/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ClosedImmersion.Basic

/-!
# The factorisation property of closed immersions, for affinoid sources

Let `(A, A⁺)` and `(B, B⁺)` be Huber pairs with `A` and `B` complete and Hausdorff, and `J ⊆ A` an
ideal, and suppose the structure presheaves of `Spa(B, B⁺)` and `Spa(A ⧸ J, (A ⧸ J)⁺)` are
sheaves. A morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` whose global-sections map kills `J`, and carries
open ideals to ideals generating open ideals, factors through the quotient morphism
`Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)`. This is the existence half of the factorisation property of
closed immersions, for affinoid sources: the global-sections map factors through `A ⧸ J`, and a
morphism of affinoid pre-adic spectra is determined by its global-sections map
(`TauCeti.ValuationSpectrum.presentationLimitPreAdicSpace_hom_ext`).

## Main results

* `TauCeti.ValuationSpectrum.exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq`:
  when the structure presheaves of the source and of `Spa(A ⧸ J, (A ⧸ J)⁺)` are sheaves, a
  morphism whose global-sections map kills `J` and carries open ideals to ideals generating open
  ideals factors through the quotient morphism by `J`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 7.38.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe u

variable {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [CompleteSpace A] [T0Space A] (P : PairOfDefinition A)

variable {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T0Space B] (P' : PairOfDefinition B)

variable [IsHuberRing A] [IsHuberRing B] (S : Pair A) (T : Pair B)
  (hS : P.ringOfDefinition ≤ S.plus) (hT : P'.ringOfDefinition ≤ T.plus) (J : Ideal A)

/-- **The factorisation property of the quotient morphism, for affinoid sources**: for complete
Hausdorff `A` and `B`, a morphism `f : Spa(B, B⁺) ⟶ Spa(A, A⁺)` of pre-adic spaces whose
global-sections map kills `J`, and carries open ideals to ideals generating open ideals, factors
through the quotient morphism `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)`. The structure presheaves of
`Spa(B, B⁺)` and `Spa(A ⧸ J, (A ⧸ J)⁺)` are assumed to be sheaves. -/
theorem exists_comp_presentationLimitPreAdicSpaceQuotientComap_eq
    (hsheafJ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
      (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (f : presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
        hT ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hS)
    (hf : J ≤ RingHom.ker (presentationLimitHomPairHom P P' S T hS hT f).toRingHom)
    (hopen : ∀ ⦃I : Ideal A⦄, IsOpen (I : Set A) →
      IsOpen (I.map (presentationLimitHomPairHom P P' S T hS hT f).toRingHom : Set B)) :
    ∃ g, g ≫ presentationLimitPreAdicSpaceQuotientComap S P hS J hsheafJ = f := by
  -- the factorisation is induced by the factorisation of the global-sections map through `A ⧸ J`
  let φ := presentationLimitHomPairHom P P' S T hS hT f
  refine ⟨presentationLimitPreAdicSpaceComap (φ.quotientLift J hf).toRingHom
    (φ.quotientLift J hf).continuous_toRingHom (fun _ hI ↦ φ.isOpen_map_quotientLift J hf hopen hI)
    (φ.quotientLift J hf).map_mem_plus (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem
    (P.quotient_ringOfDefinition_le_quotient_plus hS J) hT hsheafT,
    presentationLimitPreAdicSpace_hom_ext P S.plus _ hS P' T.plus _ hT hsheafT ?_⟩
  rw [presentationLimitPreAdicSpaceComap_quotientLift_comp_quotientComap S P hS J hsheafJ P' hT _
    hf hopen hsheafT, presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap,
    presentationLimitHomPairHom_toRingHom]

end TauCeti.ValuationSpectrum

end
