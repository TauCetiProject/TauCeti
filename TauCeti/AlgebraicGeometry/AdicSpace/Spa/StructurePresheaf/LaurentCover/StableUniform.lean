/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Restrict
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.StableUniform

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.LaurentCover.Uniform

/-!
# The Laurent sheaf condition on rational subsets of a stably uniform affinoid

Let `A` be a stably uniform Tate ring and let `W = R(T/s)` be a rational subset of
`Spa(A, A⁺)`. The coordinate ring `A⟨T/s⟩` is again stably uniform, hence its separated
completion is uniform. Buzzard--Verberkmoes Laurent gluing on that coordinate ring therefore
transports along Wedhorn's rational-localization comparison to the two-piece Laurent cover

```text
W ∩ {|f| ≤ 1},  W ∩ {|f| ≥ 1}
```

of `W`. Thus sections on `W` are determined on the two pieces and compatible sections glue.
This is the local input for the induction proving that stably uniform affinoids are sheafy.

## Main results

* `injective_presentationLimitMap_inf_laurentCoverOpen_of_isStablyUniform`:
  sections on a rational subset are determined on its two Laurent pieces.
* `exists_presentationLimitMap_eq_of_inf_laurentCoverOpen_of_isStablyUniform`:
  compatible sections on the two pieces glue over the rational subset.

## References

* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018), 25--39, Theorem 7.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 8.4.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [UniformSpace A] [IsTopologicalRing A] [IsTateRing A]
  [IsStablyUniform A] (P : PairOfDefinition A) {Aplus : Subring A}

/-- **Laurent injectivity on a rational subset of a stably uniform affinoid.** A section over
`R(T/s)` is determined by its restrictions to the intersections with `{|f| ≤ 1}` and
`{|f| ≥ 1}`. -/
theorem injective_presentationLimitMap_inf_laurentCoverOpen_of_isStablyUniform
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (f : A) :
    Function.Injective fun (x : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s))
        (b : Bool) ↦
      (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)).hom.1 x := by
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isTateRing_completion_locTopology_of_isTateRing P T s _ hden
  have _ := PairOfDefinition.isStablyUniform_completion_locTopology P T s _ hden hT
  have _ := Huber.IsStablyUniform.isUniform
    (A := UniformSpace.Completion (Localization.Away s))
  exact injective_presentationLimitMap_inf_laurentCoverOpen_of_locOpensComap P Aplus T s _ hden
    hAplus hT f (injective_presentationLimitMap_laurentCoverOpen_of_isUniform _
      (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s _ hden) _)

/-- **Laurent gluing on a rational subset of a stably uniform affinoid.** Compatible sections on
`R(T/s) ∩ {|f| ≤ 1}` and `R(T/s) ∩ {|f| ≥ 1}` glue to a section on `R(T/s)`. The gluing
is unique by
`injective_presentationLimitMap_inf_laurentCoverOpen_of_isStablyUniform`. -/
theorem exists_presentationLimitMap_eq_of_inf_laurentCoverOpen_of_isStablyUniform
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {T : Finset A} {s : A}
    (hT : IsOpen (Ideal.span (T : Set A) : Set A)) (f : A)
    (x : ∀ b, presentationLimit (P := P) Aplus
      (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b))
    (hx : (presentationLimitMap (P := P) (inf_le_left :
        (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f true) ⊓
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false) ≤ _)).hom.1 (x true) =
      (presentationLimitMap (P := P) (inf_le_right :
        (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f true) ⊓
          (spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f false) ≤ _)).hom.1 (x false)) :
    ∃ a : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s), ∀ b,
      (presentationLimitMap (P := P)
        (inf_le_left : spaBasicOpen Aplus T s ⊓ laurentCoverOpen Aplus f b ≤ _)).hom.1 a =
          x b := by
  have hden := hasDenominatorPower_of_isOpen_span P T s (Localization.Away s) hT
  let _ := locUniformSpace P T s _ hden
  have _ := isUniformAddGroup_locUniformSpace P T s _ hden
  have _ := isTopologicalRing_locUniformSpace P T s _ hden
  have _ := isTateRing_completion_locTopology_of_isTateRing P T s _ hden
  have _ := PairOfDefinition.isStablyUniform_completion_locTopology P T s _ hden hT
  have _ := Huber.IsStablyUniform.isUniform
    (A := UniformSpace.Completion (Localization.Away s))
  exact exists_presentationLimitMap_eq_of_inf_laurentCoverOpen_of_locOpensComap P Aplus T s _ hden
    hAplus hT f (exists_presentationLimitMap_eq_of_laurentCoverOpen_of_isUniform _
      (isPowerBounded_of_mem_completedPlusSubring P Aplus hAplus T s _ hden) _) x hx

end TauCeti.ValuationSpectrum

end
