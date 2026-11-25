/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Spreading out surjections from Kähler differentials at a prime

Let `A` be a finitely presented `k`-algebra and `p` a prime of `A`. A surjection of
`A_p`-modules `Ω[A_p⁄k] → A_p^d` spreads out to a basic open neighbourhood of `p`: there is
`s ∉ p` and a surjection of `A_s`-modules `Ω[A_s⁄k] → A_s^d`. This is the local step of the
backward direction of the stalk criterion for locally free quotients of the differentials.

The module-theoretic statement is `Module.FinitePresentation.exists_notMem_surjective_map_powers`:
for a finitely presented `M` and a finite `N`, an `R`-linear surjection between their
localizations at `p` lifts, up to a unit, to a map `φ : M → N`
(`Module.FinitePresentation.exists_lift_of_isLocalizedModule`), whose cokernel is a finite module
vanishing at `p`, hence vanishing away from some `s ∉ p`
(`Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective`). It applies to
`M = Ω[A⁄k]`, finitely presented because `A` is, whose localizations are the differentials of
the localized algebras (`KaehlerDifferential.isLocalizedModule_map`).

## Main results

* `Module.FinitePresentation.exists_notMem_surjective_map_powers`: a surjection between the
  localizations at `p` of a finitely presented and a finite module comes from a map that is
  surjective away from some `s ∉ p`.
* `KaehlerDifferential.exists_notMem_surjective_away`: a surjection `Ω[A_p⁄k] → A_p^d` spreads
  out to a surjection `Ω[A_s⁄k] → A_s^d` for some `s ∉ p`.

## References

* The Stacks Project, *Commutative Algebra*, Lemma 10.10.2 (Tag 0583) and Lemma 10.40.5
  (Tag 00L2).
-/

public section

namespace Module.FinitePresentation

variable {R M N Mₚ Nₚ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup Mₚ] [Module R Mₚ] [AddCommGroup Nₚ] [Module R Nₚ]

/-- **Spreading out a surjection.** Let `M` be finitely presented and `N` finite over `R`, and let
`fM : M → Mₚ`, `fN : N → Nₚ` be localizations at a prime `p`. If there is a surjective
`R`-linear map `Mₚ → Nₚ`, then there are an `R`-linear map `φ : M → N` and `s ∉ p` such that
`φ` becomes surjective after inverting `s`. -/
theorem exists_notMem_surjective_map_powers [Module.FinitePresentation R M] [Module.Finite R N]
    (p : Ideal R) [p.IsPrime] (fM : M →ₗ[R] Mₚ) (fN : N →ₗ[R] Nₚ)
    [IsLocalizedModule p.primeCompl fM] [IsLocalizedModule p.primeCompl fN] (g : Mₚ →ₗ[R] Nₚ)
    (hg : Function.Surjective g) :
    ∃ φ : M →ₗ[R] N, ∃ s ∉ p, Function.Surjective (LocalizedModule.map (.powers s) φ) := by
  obtain ⟨φ, s, hφ⟩ := exists_lift_of_isLocalizedModule p.primeCompl fN (g ∘ₗ fM)
  -- The localization of `φ` at `p` is `s • g`, which is surjective because `s` acts invertibly.
  have hmap : IsLocalizedModule.map p.primeCompl fM fN φ = s • g := by
    refine IsLocalizedModule.ext p.primeCompl fM (IsLocalizedModule.map_units fN) ?_
    rw [IsLocalizedModule.map_comp, hφ, LinearMap.smul_comp]
  have hsurj : Function.Surjective (IsLocalizedModule.map p.primeCompl fM fN φ) := by
    rw [hmap]
    exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units fN s)).2.comp hg
  rw [IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective fM fN] at hsurj
  obtain ⟨t, ht, h⟩ := Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective
    p φ hsurj
  exact ⟨φ, t, ht, h⟩

end Module.FinitePresentation

namespace KaehlerDifferential

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A]

/-- **Spreading out a free quotient of the differentials.** Let `A` be a finitely presented
`k`-algebra, `p` a prime of `A` and `Aₚ` its localization at `p`. A surjection of `Aₚ`-modules
`Ω[Aₚ⁄k] → Aₚ^d` spreads out: there are `s ∉ p` and a surjection of `A_s`-modules
`Ω[A_s⁄k] → A_s^d`. -/
theorem exists_notMem_surjective_away (p : Ideal A) [p.IsPrime] (Aₚ : Type*) [CommRing Aₚ]
    [Algebra A Aₚ] [IsLocalization.AtPrime Aₚ p] [Algebra k Aₚ] [IsScalarTower k A Aₚ] {d : ℕ}
    (g : Ω[Aₚ⁄k] →ₗ[Aₚ] (Fin d → Aₚ)) (hg : Function.Surjective g) :
    ∃ s ∉ p, ∃ g' : Ω[Localization.Away s⁄k] →ₗ[Localization.Away s]
      (Fin d → Localization.Away s), Function.Surjective g' := by
  let fN : (Fin d → A) →ₗ[A] (Fin d → Aₚ) :=
    .pi fun i ↦ Algebra.linearMap A Aₚ ∘ₗ .proj i
  obtain ⟨φ, s, hs, hφ⟩ := Module.FinitePresentation.exists_notMem_surjective_map_powers p
    (map k k A Aₚ) fN (g.restrictScalars A) hg
  let fN' : (Fin d → A) →ₗ[A] (Fin d → Localization.Away s) :=
    .pi fun i ↦ Algebra.linearMap A (Localization.Away s) ∘ₗ .proj i
  rw [← IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
    (map k k A (Localization.Away s)) fN'] at hφ
  exact ⟨s, hs, (IsLocalizedModule.map (.powers s) (map k k A (Localization.Away s)) fN'
    φ).extendScalarsOfIsLocalization (.powers s) (Localization.Away s), hφ⟩

end KaehlerDifferential
