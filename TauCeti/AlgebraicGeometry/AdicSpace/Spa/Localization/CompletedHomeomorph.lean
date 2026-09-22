/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Homeomorph
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Homeomorph
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# The adic spectrum of `A⟨T/s⟩` is the rational subset

For a rational subset `R(T/s)` of `Spa (A, A⁺)`, pullback along the structure map
`ρ : A → A⟨T/s⟩` is a homeomorphism

```text
Spa (A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s).
```

Here `A_U⁺` is the plus ring `completedPlusSubring` puts on `A⟨T/s⟩`: the closure of the image of
`C`, the integral closure of `A⁺[T/s]` in `A(T/s)`. It agrees with the plus ring Proposition 7.48
puts on a completion, which is what `completedPlusSubring_eq_completionPlus` records.

`Spa.Localization.Homeomorph` treats the *uncompleted* topological localization `A(T/s)`; this
file supplies the completed coordinate ring, and with it the first assertion of Proposition
8.2 (2).

No completeness, Tate or Noetherian hypothesis is needed, and `A⁺` is an arbitrary subring
subject only to the hypothesis `A₀ ≤ A⁺` that `spaLocalizationHomeomorph` already carries.

## Main definitions

* `TauCeti.ValuationSpectrum.spaCompletedLocalizationHomeomorph`: the homeomorphism
  `Spa (A⟨T/s⟩, A_U⁺) ≃ₜ R(T/s)`.

## Main results

* `TauCeti.ValuationSpectrum.completedPlusSubring_eq_completionPlus`: `A_U⁺` is the completion
  plus ring of `C`.
* `TauCeti.ValuationSpectrum.spaCompletedLocalizationHomeomorph_apply` and
  `TauCeti.ValuationSpectrum.coe_spaCompletedLocalizationHomeomorph`: the homeomorphism is the
  canonical map `spaLocToRationalSubset`, so it is that map which is a homeomorphism.
* `TauCeti.ValuationSpectrum.val_comp_spaCompletedLocalizationHomeomorph`: composing the
  homeomorphism with the inclusion of `R(T/s)` into `Spa (A, A⁺)` is `spaComapLoc`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 8.2 (2), first
  assertion, and Proposition 7.48.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **`A_U⁺` is the completion plus ring of `C`.** Both are the closure, in `A⟨T/s⟩`, of the image
of the integral closure `C` of `A⁺[T/s]` in `A(T/s)`, so the plus ring that `completedPlusSubring`
puts on the completed localization is the one `completionPlus` builds from `C` — the plus ring of
Wedhorn's Proposition 7.48. -/
theorem completedPlusSubring_eq_completionPlus (P : PairOfDefinition A) (Aplus : Subring A)
    (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    completedPlusSubring P Aplus T s S hden = completionPlus (integralClosure ↥(Algebra.adjoin Aplus
      (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  -- neither `completedPlusSubring` nor `completionPlus` is exposed outside the module that
  -- introduces it, so neither side unfolds here and the two are compared on their carriers
  exact SetLike.coe_injective <| by
    rw [coe_completedPlusSubring, completionPlus_def,
      Completion.coe_topologicalClosure_map_coeRingHom, Subalgebra.coe_toSubring]

/-- **The adic spectrum of `A⟨T/s⟩` is the rational subset `R(T/s)`** — Wedhorn Proposition
8.2 (2), first assertion. Pullback along the structure map `A → A⟨T/s⟩` is a homeomorphism onto
`R(T/s)`. -/
noncomputable def spaCompletedLocalizationHomeomorph (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    spa (completedPlusSubring P Aplus T s S hden) ≃ₜ
      (Subtype.val ⁻¹' rationalSubset Aplus T s : Set (spa Aplus)) :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  -- `ρ` factors as `A → A(T/s) → A⟨T/s⟩`: the second map is a homeomorphism on adic spectra by
  -- Proposition 7.48, the first is `spaLocalizationHomeomorph`. The two `setCongr` steps only
  -- rename the plus ring and move the middle adic spectrum between the topology
  -- `locUniformSpace` induces and `locTopology`. Both are equations of subsets of the valuation
  -- spectrum, which the ring structure alone topologizes, so neither moves a point.
  (Homeomorph.setCongr (by rw [completedPlusSubring_eq_completionPlus])).trans <|
    (spaCompletionHomeomorph (integralClosure ↥(Algebra.adjoin Aplus
        (Set.range fun t : T ↦ (divBy (t : A) s : S))) S).toSubring).trans <|
      (Homeomorph.setCongr (by rw [locUniformSpace_toTopologicalSpace])).trans
        (spaLocalizationHomeomorph P Aplus hP T s S hden)

/-- The homeomorphism is the canonical map `spaLocToRationalSubset`: pullback along the structure
map `ρ : A → A⟨T/s⟩`. This is what makes `spaCompletedLocalizationHomeomorph` a statement about
`A⟨T/s⟩` itself rather than about some homeomorphic replacement of it. -/
@[simp]
theorem spaCompletedLocalizationHomeomorph_apply (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ∀ v : spa (completedPlusSubring P Aplus T s S hden),
      spaCompletedLocalizationHomeomorph P Aplus hP T s S hden v =
        spaLocToRationalSubset P Aplus T s S hden v := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  have _ := isHuberRing_locUniformSpace P T s S hden
  -- the structure map is the localisation map followed by the completion map, so pulling back
  -- along it is pulling back along the two in turn
  have hrho : toCompletionLoc P T s S hden = Completion.coeRingHom.comp (algebraMap A S) :=
    RingHom.ext (toCompletionLoc_apply P T s S hden)
  refine fun v ↦ Subtype.ext <| Subtype.ext ?_
  simp [spaCompletedLocalizationHomeomorph, hrho]

/-- The homeomorphism, as a function, is pullback along the structure map `ρ : A → A⟨T/s⟩`. This is
the functional companion of the pointwise `spaCompletedLocalizationHomeomorph_apply`, in the form
that rewrites under `Set.preimage` and `Set.image`. -/
@[simp]
theorem coe_spaCompletedLocalizationHomeomorph (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    ⇑(spaCompletedLocalizationHomeomorph P Aplus hP T s S hden) =
      spaLocToRationalSubset P Aplus T s S hden :=
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  funext (spaCompletedLocalizationHomeomorph_apply P Aplus hP T s S hden)

/-- The homeomorphism, followed by the inclusion of `R(T/s)` into `Spa (A, A⁺)`, is pullback
along the structure map `ρ : A → A⟨T/s⟩`. This is the form that turns a statement about the
homeomorphism into one about `spaComapLoc`, where the plus ring is visible and the map factors
through the uncompleted localization. -/
theorem val_comp_spaCompletedLocalizationHomeomorph (P : PairOfDefinition A) (Aplus : Subring A)
    (hP : P.ringOfDefinition ≤ Aplus) (T : Finset A) (s : A) (S : Type*) [CommRing S] [Algebra A S]
    [IsLocalization.Away s S] (hden : HasDenominatorPower P T s S) :
    letI := locUniformSpace P T s S hden
    letI := isUniformAddGroup_locUniformSpace P T s S hden
    letI := isTopologicalRing_locUniformSpace P T s S hden
    Subtype.val ∘ ⇑(spaCompletedLocalizationHomeomorph P Aplus hP T s S hden) =
      spaComapLoc P Aplus T s S hden := by
  let _ := locUniformSpace P T s S hden
  have _ := isUniformAddGroup_locUniformSpace P T s S hden
  have _ := isTopologicalRing_locUniformSpace P T s S hden
  funext v
  rw [Function.comp_apply, coe_spaCompletedLocalizationHomeomorph, spaLocToRationalSubset_val]

end TauCeti.ValuationSpectrum

end
