/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import TauCeti.RingTheory.Localization.Module

/-!
# Spreading out surjections from Kähler differentials at a prime

Let `A` be a finitely presented `k`-algebra and `p` a prime of `A`. A surjection of
`A_p`-modules `Ω[A_p⁄k] → A_p^d` spreads out to a basic open neighbourhood of `p`: there is
`s ∉ p` such that for every localization `A_s` of `A` at `s` there is a surjection of
`A_s`-modules `Ω[A_s⁄k] → A_s^d`. This is the local step of the backward direction of the stalk
criterion for locally free quotients of the differentials.

The module-theoretic step is `Module.FinitePresentation.exists_notMem_localizedMap_away_surjective`,
applied to `M = Ω[A⁄k]`, finitely presented because `A` is, whose localizations are the
differentials of the localized algebras (`KaehlerDifferential.isLocalizedModule_map`). Localizing
the differentials and extending scalars to the localized ring follows the spreading-out step in
the proof of Mathlib's `Algebra.IsSmoothAt.exists_notMem_isStandardSmooth`
(Mathlib/RingTheory/Smooth/StandardSmoothOfFree.lean).

## Main results

* `KaehlerDifferential.exists_notMem_away_surjective`: a surjection `Ω[A_p⁄k] → A_p^d` spreads
  out to a surjection `Ω[A_s⁄k] → A_s^d` for some `s ∉ p`.

## References

* The Stacks Project, *Commutative Algebra*, Lemma 10.10.2 (Tag 0583) and Lemma 10.40.5
  (Tag 00L2).
-/

public section

namespace KaehlerDifferential

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A]

/-- **Spreading out a free quotient of the differentials.** Let `A` be a finitely presented
`k`-algebra, `p` a prime of `A` and `Aₚ` a localization of `A` at `p`. A surjection of
`Aₚ`-modules `Ω[Aₚ⁄k] → Aₚ^d` spreads out: there is `s ∉ p` such that for every localization
`Aₛ` of `A` at `s` there is a surjection of `Aₛ`-modules `Ω[Aₛ⁄k] → Aₛ^d`. -/
theorem exists_notMem_away_surjective (p : Ideal A) [p.IsPrime] (Aₚ : Type*) [CommRing Aₚ]
    [Algebra A Aₚ] [IsLocalization.AtPrime Aₚ p] [Algebra k Aₚ] [IsScalarTower k A Aₚ] {d : ℕ}
    (g : Ω[Aₚ⁄k] →ₗ[Aₚ] (Fin d → Aₚ)) (hg : Function.Surjective g) :
    ∃ s ∉ p, ∀ (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization.Away s Aₛ]
      [Algebra k Aₛ] [IsScalarTower k A Aₛ],
      ∃ g' : Ω[Aₛ⁄k] →ₗ[Aₛ] (Fin d → Aₛ), Function.Surjective g' := by
  let fN : (Fin d → A) →ₗ[A] (Fin d → Aₚ) :=
    .pi fun i ↦ Algebra.linearMap A Aₚ ∘ₗ .proj i
  obtain ⟨φ, s, hs, hφ⟩ := Module.FinitePresentation.exists_notMem_localizedMap_away_surjective p
    (map k k A Aₚ) fN (g.restrictScalars A) hg
  refine ⟨s, hs, fun Aₛ _ _ _ _ _ ↦ ?_⟩
  let fN' : (Fin d → A) →ₗ[A] (Fin d → Aₛ) :=
    .pi fun i ↦ Algebra.linearMap A Aₛ ∘ₗ .proj i
  rw [← IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
    (map k k A Aₛ) fN'] at hφ
  exact ⟨(IsLocalizedModule.map (.powers s) (map k k A Aₛ) fN' φ).extendScalarsOfIsLocalization
    (.powers s) Aₛ, hφ⟩

end KaehlerDifferential
