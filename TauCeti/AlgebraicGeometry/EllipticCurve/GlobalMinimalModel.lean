/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime
-- Proof-only: descent of a change of variables between integral models to `O`.
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
-- Proof-only: the comparison of two minimal models at one prime.
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic

/-!
# Global and semi-global minimal Weierstrass equations over a Dedekind domain

Mathlib's `WeierstrassCurve.IsMinimal R W` minimises a Weierstrass equation over one discrete
valuation ring `R` at a time. Over the fraction field `K` of a Dedekind domain `O` — a number field
and its ring of integers being the case that matters — the local rings are the localisations
`Oᵥ := Localization.AtPrime v.asIdeal` at the height-one primes `v` of `O`, and a **globally
minimal** equation is one that is minimal at every `v` simultaneously (Silverman, *The Arithmetic
of Elliptic Curves*, VIII.8). This file defines that predicate and its semi-global relaxation,
proves that a globally minimal equation has coefficients in `O`, and describes the changes of
variables between globally minimal equations: they are exactly those defined over `O`.

## Main definitions

* `WeierstrassCurve.IsGlobalMinimal O W`: `W` is minimal over `Oᵥ` for every height-one prime `v`
  of `O`.
* `WeierstrassCurve.IsSemiGlobalMinimal O W`: `W` is globally minimal, or there is one height-one
  prime `v₀` at which `W` is merely integral while it is minimal at every other height-one prime.

## Main results

* `WeierstrassCurve.isIntegral_of_forall_isIntegral_localizationAtPrime`: an equation integral
  over every `Oᵥ` is integral over `O`. This is `O = ⋂ᵥ Oᵥ`
  (`IsDedekindDomain.HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime`)
  applied to each coefficient.
* `WeierstrassCurve.IsGlobalMinimal.isIntegral` and
  `WeierstrassCurve.IsSemiGlobalMinimal.isIntegral`: both predicates imply integrality over `O`,
  through Mathlib's `[IsMinimal R W] : IsIntegral R W` at each prime and the descent.
* `WeierstrassCurve.IsGlobalMinimal.baseChange_smul`: a change of variables defined over `O`
  carries a globally minimal equation to a globally minimal equation.
* `WeierstrassCurve.IsGlobalMinimal.exists_baseChange_eq_of_smul_eq`: conversely, a change of
  variables between two globally minimal equations of an elliptic curve is defined over `O`, its
  scaling factor being a unit of `O` (Silverman, *AEC*, VIII.8).

The predicates are unexposed. Their interface is the `simp` lemmas `isGlobalMinimal_iff` and
`isSemiGlobalMinimal_iff` together with the introduction and elimination lemmas
`IsGlobalMinimal.isMinimal`, `IsGlobalMinimal.of_forall_isMinimal`,
`IsGlobalMinimal.isSemiGlobalMinimal` and `IsSemiGlobalMinimal.of_isIntegral_of_isMinimal`.

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
@[simp]
theorem isGlobalMinimal_iff {W : WeierstrassCurve K} [W.IsElliptic] :
    IsGlobalMinimal O W ↔
      ∀ v : HeightOneSpectrum O, IsMinimal (Localization.AtPrime v.asIdeal) W :=
  Iff.rfl

variable {O} in
/-- A globally minimal equation is minimal at each height-one prime. -/
theorem IsGlobalMinimal.isMinimal {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) (v : HeightOneSpectrum O) :
    IsMinimal (Localization.AtPrime v.asIdeal) W :=
  h v

variable {O} in
/-- An equation minimal at every height-one prime is globally minimal. -/
theorem IsGlobalMinimal.of_forall_isMinimal {W : WeierstrassCurve K} [W.IsElliptic]
    (h : ∀ v : HeightOneSpectrum O, IsMinimal (Localization.AtPrime v.asIdeal) W) :
    IsGlobalMinimal O W :=
  h

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
@[simp]
theorem isSemiGlobalMinimal_iff {W : WeierstrassCurve K} [W.IsElliptic] :
    IsSemiGlobalMinimal O W ↔ IsGlobalMinimal O W ∨
      ∃ v₀ : HeightOneSpectrum O, IsIntegral (Localization.AtPrime v₀.asIdeal) W ∧
        ∀ v : HeightOneSpectrum O, v ≠ v₀ → IsMinimal (Localization.AtPrime v.asIdeal) W :=
  Iff.rfl

/-- A globally minimal equation is semi-globally minimal, at every base including a field. -/
theorem IsGlobalMinimal.isSemiGlobalMinimal {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) : IsSemiGlobalMinimal O W :=
  Or.inl h

/-- An equation integral at a height-one prime `v₀` and minimal at every other height-one prime is
semi-globally minimal. -/
theorem IsSemiGlobalMinimal.of_isIntegral_of_isMinimal {W : WeierstrassCurve K} [W.IsElliptic]
    {v₀ : HeightOneSpectrum O} (h₀ : IsIntegral (Localization.AtPrime v₀.asIdeal) W)
    (h : ∀ v : HeightOneSpectrum O, v ≠ v₀ → IsMinimal (Localization.AtPrime v.asIdeal) W) :
    IsSemiGlobalMinimal O W :=
  Or.inr ⟨v₀, h₀, h⟩

/-! ### Descent of integrality from the localisations to `O` -/

/-- **A Weierstrass equation integral over every localisation of `O` at a height-one prime is
integral over `O`**: `O = ⋂ᵥ Oᵥ`, applied to the coefficients. This is how integrality over `O` is
obtained from local data, as in `IsGlobalMinimal.isIntegral`. -/
theorem isIntegral_of_forall_isIntegral_localizationAtPrime {W : WeierstrassCurve K}
    (h : ∀ v : HeightOneSpectrum O, IsIntegral (Localization.AtPrime v.asIdeal) W) :
    IsIntegral O W :=
  -- `O = ⋂ᵥ Oᵥ`, applied to each coefficient: the coefficient's lift to the integral model over
  -- `Localization.AtPrime v.asIdeal` witnesses that it comes from that localisation.
  isIntegral_of_exists_lift O
    (HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime W.a₁ fun v =>
      have := h v; ⟨_, integralModel_a₁_eq _ W⟩)
    (HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime W.a₂ fun v =>
      have := h v; ⟨_, integralModel_a₂_eq _ W⟩)
    (HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime W.a₃ fun v =>
      have := h v; ⟨_, integralModel_a₃_eq _ W⟩)
    (HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime W.a₄ fun v =>
      have := h v; ⟨_, integralModel_a₄_eq _ W⟩)
    (HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime W.a₆ fun v =>
      have := h v; ⟨_, integralModel_a₆_eq _ W⟩)

/-- **A globally minimal equation is integral over `O`.** Integrality is thus a consequence of
`IsGlobalMinimal`, not a hypothesis of it, and `integralModel O W` is available for such `W`. -/
theorem IsGlobalMinimal.isIntegral {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) : IsIntegral O W :=
  isIntegral_of_forall_isIntegral_localizationAtPrime fun v =>
    have := h.isMinimal v; inferInstance

/-- **A semi-globally minimal equation is integral over `O`**, so `integralModel O W` is available
for such `W` just as for a globally minimal one. -/
theorem IsSemiGlobalMinimal.isIntegral {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsSemiGlobalMinimal O W) : IsIntegral O W := by
  rcases h with hg | ⟨v₀, h₀, hmin⟩
  · exact hg.isIntegral
  · -- Integral at `v₀` by the definition's integrality clause, and at every other prime by
    -- minimality.
    refine isIntegral_of_forall_isIntegral_localizationAtPrime fun v => ?_
    by_cases hv : v = v₀
    · exact hv ▸ h₀
    · have := hmin v hv
      infer_instance

/-! ### Changes of variables between globally minimal equations -/

/-- **A change of variables defined over `O` preserves global minimality.** -/
theorem IsGlobalMinimal.baseChange_smul {W : WeierstrassCurve K} [W.IsElliptic]
    (h : IsGlobalMinimal O W) (C : VariableChange O) :
    IsGlobalMinimal O (C.baseChange K • W) := by
  refine IsGlobalMinimal.of_forall_isMinimal fun v => ?_
  have := h.isMinimal v
  have hC := isMinimal_baseChange_smul (Localization.AtPrime v.asIdeal) W
    (C.baseChange (Localization.AtPrime v.asIdeal))
  have hmap : (C.baseChange (Localization.AtPrime v.asIdeal)).baseChange K =
      C.baseChange K :=
    VariableChange.map_baseChange C
      (IsScalarTower.toAlgHom O (Localization.AtPrime v.asIdeal) K)
  rw [hmap] at hC
  exact hC

/-- **A change of variables between two globally minimal equations of an elliptic curve is defined
over `O`** (Silverman, *AEC*, VIII.8). Together with `IsGlobalMinimal.baseChange_smul`, this
characterises the changes of variables between globally minimal equations. -/
theorem IsGlobalMinimal.exists_baseChange_eq_of_smul_eq {W₁ W₂ : WeierstrassCurve K}
    [W₁.IsElliptic] [W₂.IsElliptic] (h₁ : IsGlobalMinimal O W₁) (h₂ : IsGlobalMinimal O W₂)
    (D : VariableChange K) (hD : D • W₁ = W₂) :
    ∃ C₀ : VariableChange O, C₀.baseChange K = D := by
  -- Local minimality makes the scaling factor a unit at every height-one prime. Descend that
  -- unit to `O`, then descend the remaining parameters using the integral models.
  have := h₁.isIntegral
  have := h₂.isIntegral
  have hloc : ∀ v : HeightOneSpectrum O, ∃ u₀ : (Localization.AtPrime v.asIdeal)ˣ,
      algebraMap (Localization.AtPrime v.asIdeal) K u₀ = D.u := fun v => by
    have := h₁.isMinimal v
    have := h₂.isMinimal v
    exact VariableChange.exists_unit_algebraMap_eq_u_of_isMinimal_smul _ D hD
  obtain ⟨u₀, hu₀⟩ := HeightOneSpectrum.isUnit_of_forall_isUnit_localizationAtPrime
    (D.u : K) (Units.ne_zero _) hloc
  have := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp (inferInstance : IsIntegrallyClosed O)
  exact VariableChange.exists_baseChange_eq_of_smul_eq O D hD u₀ hu₀

end WeierstrassCurve

end
