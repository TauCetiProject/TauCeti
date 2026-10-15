/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic

/-!
# Sections on the empty open of an adic spectrum

The presentation-limit presheaf has exactly one section on the empty open when the plus subring
consists of power-bounded elements. The rational presentation `R({1}/0)` identifies this value
with the completion of the zero ring. This supplies the empty-cover case of the sheaf condition,
without completeness, Tate, or noetherian hypotheses on the original ring.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

public section

open CategoryTheory TopologicalSpace TauCeti.Huber TauCeti.Huber.PairOfDefinition

universe v

namespace TauCeti.ValuationSpectrum

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- There is exactly one presentation-limit section on the empty open if `A⁺` consists of
power-bounded elements. -/
theorem subsingleton_presentationLimit_bot (P : PairOfDefinition A) {Aplus : Subring A}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) :
    Subsingleton (presentationLimit (P := P) Aplus ⊥) := by
  classical
  have hT : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A) := by
    simp
  let p : Presentation P :=
    ⟨{1}, 0, hasDenominatorPower_of_isOpen_span P {1} 0 _ hT⟩
  have hp : spaBasicOpen Aplus p.num p.den = ⊥ := by
    apply Opens.ext
    ext x
    simp [p, mem_spaBasicOpen, mem_rationalSubset_iff]
  let := locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have := isUniformAddGroup_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have := isTopologicalRing_locUniformSpace P p.num p.den _ p.hasDenominatorPower
  have : Subsingleton (Localization.Away p.den) :=
    IsLocalization.subsingleton (M := Submonoid.powers p.den) (by
      exact ⟨1, by simp [p]⟩)
  have : Subsingleton (UniformSpace.Completion (Localization.Away p.den)) :=
    subsingleton_of_zero_eq_one (by
      simpa only [UniformSpace.Completion.coe_zero, UniformSpace.Completion.coe_one] using
        congrArg (fun x : Localization.Away p.den ↦
        (x : UniformSpace.Completion (Localization.Away p.den)))
        (Subsingleton.elim (0 : Localization.Away p.den) 1))
  let e := (forget₂ TopCommRingCat CommRingCat).mapIso
    (TopCommRingCat.isCompleteSeparated.ι.mapIso
      (presentationLimitRationalIso Aplus hAplus p hT)) ≪≫
    p.completionLocObjCommRingCatIso
  rw [← hp]
  exact ⟨fun x y ↦ e.commRingCatIsoToRingEquiv.injective (Subsingleton.elim _ _)⟩

end TauCeti.ValuationSpectrum
