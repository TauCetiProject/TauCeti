/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Basic
public import TauCeti.RingTheory.Huber.Uniform

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.LaurentCover.Uniform

/-!
# The Laurent cover for the presentation-limit presheaf of a uniform Tate ring

For `f ∈ A` the rational opens `{|f| ≤ 1}` and `{|f| ≥ 1}` cover `X = Spa(A, A⁺)`. When `A` is a
complete Hausdorff uniform Tate ring and `A⁺` consists of power-bounded elements, a section of the
presentation-limit presheaf over `X` is determined by its restrictions to the two pieces, and
sections over the pieces that agree on their overlap glue. This transports Buzzard--Verberkmoes,
Corollary 4 (`isClosedEmbedding_laurentCover_of_isUniform`, `laurentCover_exact_of_isUniform`) to
`presentationLimit`.

## Main results

* `TauCeti.ValuationSpectrum.isClosedEmbedding_presentationLimitMap_laurentCoverOpen_of_isUniform` :
  restriction to the two Laurent pieces induces the topology on global sections.
* `TauCeti.ValuationSpectrum.injective_presentationLimitMap_laurentCoverOpen_of_isUniform` :
  restriction from `X` to the two pieces is injective.
* `TauCeti.ValuationSpectrum.exists_presentationLimitMap_eq_of_laurentCoverOpen_of_isUniform` :
  sections over the two pieces that agree on their overlap come from a section over `X`.

## References

* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018), 25--39, Corollary 4.
-/

public section

open CategoryTheory TopologicalSpace Topology TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [IsTateRing A] [IsUniform A]
  (P : PairOfDefinition A) {Aplus : Subring A}

/-- **Buzzard--Verberkmoes topological Laurent gluing for the presentation-limit presheaf.**
Restriction from `Spa(A, A⁺)` to the two Laurent pieces `{|f| ≤ 1}` and `{|f| ≥ 1}` is
a closed embedding on sections when `A` is a complete Hausdorff uniform Tate ring. Thus the
topology on global sections is the subspace topology inherited from the two coordinate rings. -/
theorem isClosedEmbedding_presentationLimitMap_laurentCoverOpen_of_isUniform
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A) :
    IsClosedEmbedding fun x : presentationLimit (P := P) Aplus ⊤ ↦
      ((presentationLimitMap (P := P)
          (le_top : laurentCoverOpen Aplus f true ≤ ⊤)).hom.1 x,
        (presentationLimitMap (P := P)
          (le_top : laurentCoverOpen Aplus f false ≤ ⊤)).hom.1 x) := by
  exact isClosedEmbedding_presentationLimitMap_laurentCoverOpen_of_isClosedEmbedding_toCompletionLoc
    P hAplus f fun hden₂ ↦
      isClosedEmbedding_laurentCover_of_isUniform P f (Localization.Away (1 : A))
        (Localization.Away f) hden₂

/-- **Buzzard--Verberkmoes Laurent injectivity for the presentation-limit presheaf.** A section
over `Spa(A, A⁺)` is determined by its restrictions to `{|f| ≤ 1}` and `{|f| ≥ 1}` when `A`
is a complete Hausdorff uniform Tate ring. -/
theorem injective_presentationLimitMap_laurentCoverOpen_of_isUniform
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A) :
    Function.Injective fun (x : presentationLimit (P := P) Aplus ⊤) (b : Bool) ↦
      (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f b ≤ ⊤)).hom.1 x :=
  injective_presentationLimitMap_laurentCoverOpen_of_injective_toCompletionLoc P hAplus f
    fun hden₂ ↦ (isClosedEmbedding_laurentCover_of_isUniform P f _ _ hden₂).injective

/-- **Buzzard--Verberkmoes Laurent gluing for the presentation-limit presheaf.** Compatible
sections on `{|f| ≤ 1}` and `{|f| ≥ 1}` glue to a section over `Spa(A, A⁺)` when `A` is a
complete Hausdorff uniform Tate ring. The gluing is unique by
`injective_presentationLimitMap_laurentCoverOpen_of_isUniform`. -/
theorem exists_presentationLimitMap_eq_of_laurentCoverOpen_of_isUniform
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (f : A)
    (x : ∀ b, presentationLimit (P := P) Aplus (laurentCoverOpen Aplus f b))
    (hx : (presentationLimitMap (P := P) (inf_le_left :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1 (x true) =
      (presentationLimitMap (P := P) (inf_le_right :
        laurentCoverOpen Aplus f true ⊓ laurentCoverOpen Aplus f false ≤ _)).hom.1 (x false)) :
    ∃ a : presentationLimit (P := P) Aplus ⊤, ∀ b,
      (presentationLimitMap (P := P) (le_top : laurentCoverOpen Aplus f b ≤ ⊤)).hom.1 a =
        x b :=
  exists_presentationLimitMap_eq_of_laurentCoverOpen_of_exact_toCompletionLoc P hAplus f
    (fun hden₂ ↦ laurentCover_exact_of_isUniform P f _ _ hden₂ _) x hx

end TauCeti.ValuationSpectrum

end
