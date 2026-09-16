/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-!
# Global and semi-global minimal Weierstrass equations over a Dedekind domain

Mathlib's `WeierstrassCurve.IsMinimal R W` minimises a Weierstrass equation over one discrete
valuation ring `R` at a time. Over the fraction field `K` of a Dedekind domain `O` — a number field
and its ring of integers being the case that matters — the local rings are the localisations
`Oᵥ := Localization.AtPrime v.asIdeal` at the height-one primes `v` of `O`, and a **globally
minimal** equation is one that is minimal at every `v` simultaneously (Silverman, *The Arithmetic
of Elliptic Curves*, VIII.8). This file defines that predicate and its semi-global relaxation, and
proves the one theorem the definitions need at once: a globally minimal equation has coefficients
in `O`.

## Main definitions

* `WeierstrassCurve.IsGlobalMinimal O W`: `W` is minimal over `Oᵥ` for every height-one prime `v`
  of `O`.
* `WeierstrassCurve.IsSemiGlobalMinimal O W`: `W` is globally minimal, or there is one height-one
  prime `v₀` at which `W` is merely integral while it is minimal at every other height-one prime.

## Main results

* `WeierstrassCurve.isIntegral_of_forall_isIntegral_localizationAtPrime`: an equation integral
  over every `Oᵥ` is integral over `O`. This is the descent `O = ⋂ᵥ Oᵥ`, coefficient by
  coefficient: each coefficient has `v`-adic valuation at most one at every `v`
  (`IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_le_one_of_isLocalization_atPrime`),
  hence lies in `O` (`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`).
* `WeierstrassCurve.IsGlobalMinimal.isIntegral` and
  `WeierstrassCurve.IsSemiGlobalMinimal.isIntegral`: both predicates imply integrality over `O`,
  through Mathlib's `[IsMinimal R W] : IsIntegral R W` at each prime and the descent.

## Design

* **Integrality over `O` is a theorem, not a conjunct.** Mathlib's instance gives integrality over
  each `Oᵥ` only, so `inferInstance` does not reach `IsIntegral O W`, and adding it as a hypothesis
  to the definition would hide the descent.
* **The semi-global predicate is a disjunction.** A field is a Dedekind domain whose height-one
  spectrum is empty; there `IsGlobalMinimal` is vacuously true while the bare existential
  `∃ v₀, …` is false. The disjunct is what makes `IsGlobalMinimal.isSemiGlobalMinimal` hold at
  that degenerate base. The integrality clause at `v₀` cannot be dropped either: minimality away
  from `v₀` says nothing about the denominators at `v₀`.
* **Both predicates carry `[W.IsElliptic]`.** Minimal models are a notion for elliptic curves: the
  invariants built on these predicates — the minimal discriminant ideal, the obstruction exponents,
  semistability — need `Δ ≠ 0`, and for a singular cubic the products defining them lose their
  finite support. `IsGlobalMinimal` does not itself consume the instance, which its binder name
  records.
* **The definitions are not exposed.** `isGlobalMinimal_iff` and `isSemiGlobalMinimal_iff` are the
  interface outside this module.

The localisation instances that make `IsMinimal Oᵥ W` and `IsIntegral Oᵥ W` typecheck for an
abstract fraction field `K` are in `TauCeti/RingTheory/Localization/AtPrime.lean` and
`TauCeti/RingTheory/DedekindDomain/LocalizationAtPrime.lean`.

## Provenance

The two definitions are adapted from LeanBridge (`github.com/CBirkbeck/LeanBridge`, Apache-2.0),
file `LeanBridge/ForMathlib/4-EC.lean` at `JaneShi99/LeanBridge@d84dd305` (branch
`formalize/ec-defs`), by Jane Shi, where they formalise the LMFDB knowls `ec.global_minimal_model`
and `ec.semi_global_minimal_model`. Two departures: the semi-global predicate acquires the
`IsGlobalMinimal` disjunct, and both predicates carry `[W.IsElliptic]`. The descent theorem is
proved afresh here; LeanBridge records only that it had been proved and then removed.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
variable {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- **A globally minimal Weierstrass equation** (LMFDB `ec.global_minimal_model`): `W` is minimal
over the discrete valuation ring `Localization.AtPrime v.asIdeal` at every height-one prime `v` of
`O`. Integrality over `O` is not assumed; it is the theorem `IsGlobalMinimal.isIntegral`. The
ellipticity instance keeps the predicate to elliptic curves, the setting in which the invariants
derived from it make sense; the definition itself does not consume it, which its binder name
records. -/
def IsGlobalMinimal (W : WeierstrassCurve K) [_hE : W.IsElliptic] : Prop :=
  ∀ v : HeightOneSpectrum O, IsMinimal (Localization.AtPrime v.asIdeal) W

variable {O} in
/-- Global minimality is minimality at every height-one prime. This is the interface to
`WeierstrassCurve.IsGlobalMinimal` outside its defining module. -/
theorem isGlobalMinimal_iff {W : WeierstrassCurve K} [W.IsElliptic] :
    IsGlobalMinimal O W ↔
      ∀ v : HeightOneSpectrum O, IsMinimal (Localization.AtPrime v.asIdeal) W :=
  Iff.rfl

/-- **A semi-globally minimal Weierstrass equation** (LMFDB `ec.semi_global_minimal_model`): either
`W` is globally minimal, or there is a height-one prime `v₀` of `O` at which `W` is integral and
away from which it is minimal. Over a number field of class number greater than one a curve need
not admit a globally minimal equation, but it always admits a semi-globally minimal one; that
existence theorem is not proved here. The disjunct is load-bearing: over a field, whose
height-one spectrum is empty, the existential alone is false while global minimality holds. -/
def IsSemiGlobalMinimal (W : WeierstrassCurve K) [W.IsElliptic] : Prop :=
  IsGlobalMinimal O W ∨
    ∃ v₀ : HeightOneSpectrum O, IsIntegral (Localization.AtPrime v₀.asIdeal) W ∧
      ∀ v : HeightOneSpectrum O, v ≠ v₀ → IsMinimal (Localization.AtPrime v.asIdeal) W

variable {O}

/-- Semi-global minimality, unfolded. This is the interface to
`WeierstrassCurve.IsSemiGlobalMinimal` outside its defining module. -/
theorem isSemiGlobalMinimal_iff {W : WeierstrassCurve K} [W.IsElliptic] :
    IsSemiGlobalMinimal O W ↔ IsGlobalMinimal O W ∨
      ∃ v₀ : HeightOneSpectrum O, IsIntegral (Localization.AtPrime v₀.asIdeal) W ∧
        ∀ v : HeightOneSpectrum O, v ≠ v₀ → IsMinimal (Localization.AtPrime v.asIdeal) W :=
  Iff.rfl

/-- A globally minimal equation is semi-globally minimal, at every base including a field. -/
theorem IsGlobalMinimal.isSemiGlobalMinimal {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) : IsSemiGlobalMinimal O W :=
  Or.inl h

/-! ### Descent of integrality from the localisations to `O` -/

/-- **A Weierstrass equation integral over every localisation of `O` at a height-one prime is
integral over `O`.** Each coefficient is the image of an element of `Localization.AtPrime v.asIdeal`
for every `v`, so has `v`-adic valuation at most one at every `v`, and
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` puts it in `O`. -/
theorem isIntegral_of_forall_isIntegral_localizationAtPrime {W : WeierstrassCurve K}
    (h : ∀ v : HeightOneSpectrum O, IsIntegral (Localization.AtPrime v.asIdeal) W) :
    IsIntegral O W := by
  -- `O = ⋂ᵥ Oᵥ`, one element of `K` at a time.
  have key : ∀ a : K, (∀ v : HeightOneSpectrum O, ∃ r : Localization.AtPrime v.asIdeal,
      algebraMap (Localization.AtPrime v.asIdeal) K r = a) → ∃ r : O, algebraMap O K r = a :=
    fun a ha => HeightOneSpectrum.mem_integers_of_valuation_le_one K a fun v => by
      obtain ⟨r, rfl⟩ := ha v
      exact v.valuation_algebraMap_le_one_of_isLocalization_atPrime r
  exact isIntegral_of_exists_lift O
    (key _ fun v => have := h v; ⟨_, integralModel_a₁_eq _ W⟩)
    (key _ fun v => have := h v; ⟨_, integralModel_a₂_eq _ W⟩)
    (key _ fun v => have := h v; ⟨_, integralModel_a₃_eq _ W⟩)
    (key _ fun v => have := h v; ⟨_, integralModel_a₄_eq _ W⟩)
    (key _ fun v => have := h v; ⟨_, integralModel_a₆_eq _ W⟩)

/-- **A globally minimal equation is integral over `O`.** Mathlib's `IsMinimal → IsIntegral`
instance gives integrality over each localisation; the descent does the rest. -/
theorem IsGlobalMinimal.isIntegral {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) : IsIntegral O W :=
  isIntegral_of_forall_isIntegral_localizationAtPrime fun v => have := h v; inferInstance

/-- **A semi-globally minimal equation is integral over `O`.** At the exceptional prime the
definition supplies integrality directly; everywhere else it comes from minimality. -/
theorem IsSemiGlobalMinimal.isIntegral {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsSemiGlobalMinimal O W) : IsIntegral O W := by
  rcases h with hg | ⟨v₀, h₀, hmin⟩
  · exact hg.isIntegral
  · refine isIntegral_of_forall_isIntegral_localizationAtPrime fun v => ?_
    by_cases hv : v = v₀
    · exact hv ▸ h₀
    · have := hmin v hv
      infer_instance

end WeierstrassCurve

end
