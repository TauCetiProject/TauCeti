/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Projection
public import TauCeti.MeasureTheory.OptimalTransport.Entropic.SchroedingerSystem

/-!
# The dynamic Schrödinger problem

Let `R` be a finite reference measure on a measurable space `Ω` and let `e : Ω → X × Y` be a
measurable map. The *dynamic Schrödinger problem* minimises the relative entropy `klDiv P R` over
the measures `P` on `Ω` under which `e` has a law coupling two prescribed measures `μ` and `ν`.
Its value is `TauCeti.dynamicSchroedingerValue R e μ ν`.

The motivating instance is path space: `Ω = C(I, X)`, `R` the law of a reference process, such as
Brownian motion, and `e γ = (γ 0, γ 1)` the pair of endpoints, so that `P.map e` is
`MeasureTheory.Measure.endpointLaw P`. The problem then asks for the law of a process with
prescribed initial and final laws that is closest to the reference process in relative entropy.
Nothing here uses this structure of `Ω`: only the endpoint map enters.

The dynamic problem reduces to the static Schrödinger problem `TauCeti.schroedingerValue` for the
endpoint law `R.map e` of the reference measure. For every `P`, the data processing inequality
gives `klDiv (P.map e) (R.map e) ≤ klDiv P R`. Conversely, for every coupling `π` with
`π ≪ R.map e`, reweighting `R` along `e` by the density `dπ/d(e₊R)` gives the measure
`R.fitLaw e π`, which has endpoint law `π` and relative entropy `klDiv π (R.map e)`; a coupling
that is not absolutely continuous with respect to `R.map e` has infinite relative entropy and so
only contributes the trivial bound `∞`. So the two values agree, and the dynamic minimiser is the
reweighting of `R` by the static minimiser `π`: its density against `R` is `dπ/d(e₊R) (e ω)`, a
function of the endpoints alone. Informally, on a path space where the reference process admits
regular conditional laws given its endpoints, this says that the optimal process is the mixture,
under the optimal endpoint coupling, of the bridges of the reference process; no such
disintegration is formalised here. When `π` has the product density `exp (φ(x) + ψ(y))` against
`R.map e`, the dynamic minimiser factorises as `exp (φ(X₀)) exp (ψ(X₁)) R`, a product of functions
of the initial and of the final point.

## Main definitions

* `TauCeti.dynamicSchroedingerValue R e μ ν`: the infimum of `klDiv P R` over the measures `P` on
  `Ω` such that `P.map e` couples `μ` and `ν`.

## Main statements

* `TauCeti.dynamicSchroedingerValue_eq_schroedingerValue`: the dynamic value equals the static
  value of the endpoint law `R.map e`.
* `TauCeti.IsCoupling.klDiv_fitLaw_eq_dynamicSchroedingerValue`: reweighting `R` by a static
  minimiser attains the dynamic value.
* `TauCeti.klDiv_eq_dynamicSchroedingerValue_iff`: a feasible `P` is a dynamic minimiser exactly
  when its endpoint law is a static minimiser and `P` is the reweighting of `R` by that law.
* `TauCeti.existsUnique_isCoupling_map_klDiv_eq_dynamicSchroedingerValue`: a finite dynamic value
  is attained by exactly one measure.
* `TauCeti.rnDeriv_ae_eq_rnDeriv_map_comp_of_klDiv_eq_dynamicSchroedingerValue`: the density of the
  dynamic minimiser `P` against `R` is `d(e₊P)/d(e₊R) ∘ e`.
* `TauCeti.klDiv_withDensity_exp_add_comp_eq_dynamicSchroedingerValue`: if the static problem has
  a solution with density `exp (φ(x) + ψ(y))`, for integrable potentials, then the measure with
  density `exp (φ (e ω).1 + ψ (e ω).2)` against `R` is the dynamic minimiser.
* `TauCeti.exists_klDiv_withDensity_exp_add_comp_eq_dynamicSchroedingerValue`: when the endpoint
  law of `R` has a bounded log-density against `μ.prod ν`, such bounded potentials exist.

## References

* C. Léonard, *A survey of the Schrödinger problem and some of its connections with optimal
  transport*, Discrete Contin. Dyn. Syst. 34 (2014), 1533–1574, Section 2, for the
  reduction of the dynamic problem to the static one and the form of the dynamic minimiser.
* H. Föllmer, *Random fields and diffusion processes*, École d'Été de Probabilités de Saint-Flour
  XV–XVII, Lecture Notes in Math. 1362, Springer, 1988, for the dynamic problem on path space.
-/

public section

noncomputable section

open MeasureTheory InformationTheory Set
open scoped ENNReal

namespace TauCeti

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {R P : Measure Ω} {e : Ω → X × Y} {π : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {a : ℝ≥0∞}

/-- The value of the dynamic Schrödinger problem with reference measure `R` on `Ω` and endpoint map
`e : Ω → X × Y`: the infimum of the relative entropy `klDiv P R` over the measures `P` on `Ω` such
that the law `P.map e` of `e` couples `μ` and `ν`. It is `∞` when no such `P` has finite relative
entropy. -/
def dynamicSchroedingerValue (R : Measure Ω) (e : Ω → X × Y) (μ : Measure X) (ν : Measure Y) :
    ℝ≥0∞ :=
  ⨅ (P : Measure Ω) (_ : IsCoupling (P.map e) μ ν), klDiv P R

/-- The dynamic Schrödinger value as the infimum of the relative entropies of all feasible
measures. -/
theorem dynamicSchroedingerValue_def :
    dynamicSchroedingerValue R e μ ν =
      ⨅ (P : Measure Ω) (_ : IsCoupling (P.map e) μ ν), klDiv P R :=
  (rfl)

/-- Every feasible measure bounds the dynamic Schrödinger value from above. -/
theorem dynamicSchroedingerValue_le_klDiv (hP : IsCoupling (P.map e) μ ν) (R : Measure Ω) :
    dynamicSchroedingerValue R e μ ν ≤ klDiv P R :=
  iInf₂_le P hP

/-- A bound valid on every feasible measure bounds the dynamic Schrödinger value from below. -/
theorem le_dynamicSchroedingerValue
    (h : ∀ P : Measure Ω, IsCoupling (P.map e) μ ν → a ≤ klDiv P R) :
    a ≤ dynamicSchroedingerValue R e μ ν :=
  le_iInf₂ h

/-- The dynamic Schrödinger value is below a threshold exactly when some feasible measure is. -/
theorem dynamicSchroedingerValue_lt_iff :
    dynamicSchroedingerValue R e μ ν < a ↔ ∃ P, IsCoupling (P.map e) μ ν ∧ klDiv P R < a := by
  simp only [dynamicSchroedingerValue, iInf_lt_iff, exists_prop]

/-- A measure whose endpoint law couples a finite measure is finite. -/
private theorem isFiniteMeasure_of_isCoupling_map [IsFiniteMeasure μ] (he : Measurable e)
    (hP : IsCoupling (P.map e) μ ν) : IsFiniteMeasure P :=
  have := hP.isFiniteMeasure
  Measure.isFiniteMeasure_of_map he.aemeasurable

/-- **Data processing bound.** The static Schrödinger value of the endpoint law of `R` is at most
the dynamic value: the endpoint law of a feasible measure is a coupling, and its relative entropy
is at most that of the measure. -/
theorem schroedingerValue_map_le_dynamicSchroedingerValue [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (he : Measurable e) : schroedingerValue (R.map e) μ ν ≤ dynamicSchroedingerValue R e μ ν :=
  le_dynamicSchroedingerValue fun P hP ↦
    have := isFiniteMeasure_of_isCoupling_map he hP
    (schroedingerValue_le_klDiv hP _).trans (klDiv_map_le P R he)

/-- Every coupling `π` bounds the dynamic Schrödinger value by `klDiv π (R.map e)`: when this is
finite, `π` is the endpoint law of the reweighted measure `R.fitLaw e π`, which lies at exactly
this relative entropy from `R`. -/
theorem IsCoupling.dynamicSchroedingerValue_le_klDiv_map [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (hπ : IsCoupling π μ ν) (he : Measurable e) :
    dynamicSchroedingerValue R e μ ν ≤ klDiv π (R.map e) := by
  have := hπ.isFiniteMeasure
  by_cases hac : π ≪ R.map e
  · rw [← klDiv_fitLaw he hac]
    refine dynamicSchroedingerValue_le_klDiv ?_ R
    rwa [Measure.map_fitLaw_of_absolutelyContinuous he hac]
  · rw [klDiv_of_not_ac hac]
    exact le_top

/-- **The dynamic Schrödinger problem reduces to the static one.** For a finite source measure and
a finite reference measure, the dynamic value equals the static Schrödinger value of the endpoint
law `R.map e`. -/
theorem dynamicSchroedingerValue_eq_schroedingerValue [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (he : Measurable e) :
    dynamicSchroedingerValue R e μ ν = schroedingerValue (R.map e) μ ν :=
  le_antisymm (le_schroedingerValue fun _ hπ ↦ hπ.dynamicSchroedingerValue_le_klDiv_map he)
    (schroedingerValue_map_le_dynamicSchroedingerValue he)

/-- **The reweighted reference measure is a dynamic minimiser.** If a coupling `π` attains a finite
static Schrödinger value for the endpoint law of `R`, then `R.fitLaw e π`, the measure `R`
reweighted by `dπ/d(e₊R) ∘ e`, attains the dynamic value. It is feasible, since its endpoint law is
`π` by `MeasureTheory.Measure.map_fitLaw_of_absolutelyContinuous`. -/
theorem IsCoupling.klDiv_fitLaw_eq_dynamicSchroedingerValue [IsFiniteMeasure μ]
    [IsFiniteMeasure R] (hπ : IsCoupling π μ ν) (he : Measurable e)
    (hπval : klDiv π (R.map e) = schroedingerValue (R.map e) μ ν)
    (h : schroedingerValue (R.map e) μ ν ≠ ∞) :
    klDiv (R.fitLaw e π) R = dynamicSchroedingerValue R e μ ν := by
  have := hπ.isFiniteMeasure
  rw [klDiv_fitLaw he (klDiv_ne_top_iff.1 (hπval ▸ h)).1, hπval,
    dynamicSchroedingerValue_eq_schroedingerValue he]

/-- **Characterisation of the dynamic minimiser.** Let the dynamic value be finite. A measure `P`
whose endpoint law couples `μ` and `ν` attains it exactly when its endpoint law attains the static
Schrödinger value of `R.map e` and `P` is the reweighting `R.fitLaw e (P.map e)` of `R` by
`d(e₊P)/d(e₊R) ∘ e`, so that the density of `P` against `R` depends only on the endpoints. -/
theorem klDiv_eq_dynamicSchroedingerValue_iff [IsFiniteMeasure μ] [IsFiniteMeasure R]
    (he : Measurable e) (hP : IsCoupling (P.map e) μ ν) (h : dynamicSchroedingerValue R e μ ν ≠ ∞) :
    klDiv P R = dynamicSchroedingerValue R e μ ν ↔
      klDiv (P.map e) (R.map e) = schroedingerValue (R.map e) μ ν ∧ P = R.fitLaw e (P.map e) := by
  have := isFiniteMeasure_of_isCoupling_map he hP
  have hS := dynamicSchroedingerValue_eq_schroedingerValue (R := R) (μ := μ) (ν := ν) he
  constructor
  · intro hPval
    -- By data processing the endpoint law is a static minimiser, and so its reweighting of `R`
    -- has the same relative entropy as `P`; uniqueness of the projection identifies them.
    have hstatic : klDiv (P.map e) (R.map e) = schroedingerValue (R.map e) μ ν :=
      le_antisymm ((klDiv_map_le P R he).trans (hPval.trans hS).le)
        (schroedingerValue_le_klDiv hP _)
    have hac : P.map e ≪ R.map e := (klDiv_ne_top_iff.1 (hstatic ▸ hS ▸ h)).1
    refine ⟨hstatic, eq_fitLaw_of_klDiv_le he rfl ?_ (hPval ▸ h)⟩
    rw [klDiv_fitLaw he hac, hstatic, hPval, hS]
  · rintro ⟨hstatic, hfit⟩
    have hac : P.map e ≪ R.map e := (klDiv_ne_top_iff.1 (hstatic ▸ hS ▸ h)).1
    calc klDiv P R = klDiv (R.fitLaw e (P.map e)) R := congrArg (klDiv · R) hfit
      _ = dynamicSchroedingerValue R e μ ν := by rw [klDiv_fitLaw he hac, hstatic, hS]

/-- **Existence and uniqueness of the dynamic Schrödinger minimiser.** For a finite source measure
and a finite reference measure, a finite dynamic value is attained by exactly one measure. It is
the reweighting of `R` by the static Schrödinger minimiser
(`TauCeti.IsCoupling.klDiv_fitLaw_eq_dynamicSchroedingerValue`). -/
theorem existsUnique_isCoupling_map_klDiv_eq_dynamicSchroedingerValue [IsFiniteMeasure μ]
    [IsFiniteMeasure R] (he : Measurable e) (h : dynamicSchroedingerValue R e μ ν ≠ ∞) :
    ∃! P, IsCoupling (P.map e) μ ν ∧ klDiv P R = dynamicSchroedingerValue R e μ ν := by
  have hS := dynamicSchroedingerValue_eq_schroedingerValue (R := R) (μ := μ) (ν := ν) he
  obtain ⟨π, hπ, hπval⟩ := exists_isCoupling_klDiv_eq_schroedingerValue (hS ▸ h)
  have := hπ.isFiniteMeasure
  have hmap : (R.fitLaw e π).map e = π :=
    Measure.map_fitLaw_of_absolutelyContinuous he (klDiv_ne_top_iff.1 (hπval ▸ hS ▸ h)).1
  refine ⟨R.fitLaw e π, ⟨by rwa [hmap], hπ.klDiv_fitLaw_eq_dynamicSchroedingerValue he hπval
    (hS ▸ h)⟩, fun P ⟨hP, hPval⟩ ↦ ?_⟩
  obtain ⟨hstatic, hfit⟩ := (klDiv_eq_dynamicSchroedingerValue_iff he hP h).1 hPval
  rwa [hP.eq_of_klDiv_eq_schroedingerValue hπ hstatic hπval (hS ▸ h)] at hfit

/-- **The density of the dynamic minimiser.** If `P` attains a finite dynamic value, its density
against `R` is the density of its endpoint law against that of `R`, evaluated at the endpoints:
`dP/dR = d(e₊P)/d(e₊R) ∘ e`, `R`-almost everywhere. -/
theorem rnDeriv_ae_eq_rnDeriv_map_comp_of_klDiv_eq_dynamicSchroedingerValue [IsFiniteMeasure μ]
    [IsFiniteMeasure R] (he : Measurable e) (hP : IsCoupling (P.map e) μ ν)
    (hPval : klDiv P R = dynamicSchroedingerValue R e μ ν)
    (h : dynamicSchroedingerValue R e μ ν ≠ ∞) :
    P.rnDeriv R =ᵐ[R] fun ω ↦ (P.map e).rnDeriv (R.map e) (e ω) := by
  have hfit := ((klDiv_eq_dynamicSchroedingerValue_iff he hP h).1 hPval).2
  have hdens := Measure.rnDeriv_fitLaw (π := R) (μ := P.map e) he
  rwa [← hfit] at hdens

/-! ### Factorisation through Schrödinger potentials -/

section Potentials

variable {φ : X → ℝ} {ψ : Y → ℝ}

/-- **Factorisation of the dynamic minimiser.** If the coupling of `μ` and `ν` with density
`exp (φ(x) + ψ(y))` against the endpoint law of `R` exists, for measurable potentials `φ ∈ L¹(μ)`
and `ψ ∈ L¹(ν)`, then the measure with density `exp (φ (e ω).1 + ψ (e ω).2)` against `R`, whose
endpoint law is this coupling, attains the dynamic value. On path space its density is the
product `exp (φ (γ 0)) * exp (ψ (γ 1))` of a function of the initial point and a function of the
final point. -/
theorem klDiv_withDensity_exp_add_comp_eq_dynamicSchroedingerValue [IsFiniteMeasure μ]
    [IsFiniteMeasure R] (he : Measurable e)
    (hπ : IsCoupling ((R.map e).withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)))
      μ ν)
    (hφ : Measurable φ) (hψ : Measurable ψ) (hφi : Integrable φ μ) (hψi : Integrable ψ ν) :
    klDiv (R.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (φ (e ω).1 + ψ (e ω).2))) R =
      dynamicSchroedingerValue R e μ ν := by
  have hfit : R.fitLaw e ((R.map e).withDensity fun z ↦
      ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2))) =
      R.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (φ (e ω).1 + ψ (e ω).2)) :=
    Measure.fitLaw_withDensity he (by fun_prop)
  have hval := hπ.klDiv_eq_schroedingerValue_of_eq_withDensity rfl hφ hψ hφi hψi
  have hfin : schroedingerValue (R.map e) μ ν ≠ ∞ := by
    rw [schroedingerValue_eq_ofReal_of_eq_withDensity hπ rfl hφ hψ hφi hψi]
    exact ENNReal.ofReal_ne_top
  rw [← hfit, hπ.klDiv_fitLaw_eq_dynamicSchroedingerValue he hval hfin]

/-- **The dynamic minimiser for a bounded endpoint kernel.** Let `μ` and `ν` be finite measures of
equal mass, and let the endpoint law of the reference measure `R` have density `exp g`
against `μ.prod ν`, for a bounded measurable `g`. Then there are bounded measurable potentials
`φ` and `ψ` such that the measure with density `exp (φ (e ω).1 + ψ (e ω).2)` against `R` is
feasible for the dynamic problem and attains its value, so that it is the dynamic minimiser. -/
theorem exists_klDiv_withDensity_exp_add_comp_eq_dynamicSchroedingerValue [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) (he : Measurable e)
    {g : X × Y → ℝ} {M : ℝ} (hg : Measurable g) (hgM : ∀ z, |g z| ≤ M)
    (hR : R.map e = (μ.prod ν).withDensity fun z ↦ ENNReal.ofReal (Real.exp (g z))) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (C : ℝ), Measurable φ ∧ Measurable ψ ∧ (∀ x, |φ x| ≤ C) ∧
      (∀ y, |ψ y| ≤ C) ∧
      IsCoupling ((R.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (φ (e ω).1 + ψ (e ω).2))).map e)
        μ ν ∧
      klDiv (R.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (φ (e ω).1 + ψ (e ω).2))) R =
        dynamicSchroedingerValue R e μ ν := by
  obtain ⟨φ, ψ, C, hφ, hψ, hφC, hψC, hσ⟩ :=
    exists_isCoupling_withDensity_exp_add_of_eq_withDensity hμν hg hgM hR
  -- The reference measure is finite, since its endpoint law has a bounded density.
  have : IsFiniteMeasure (R.map e) := hR ▸ isFiniteMeasure_withDensity_ofReal_exp hg.aemeasurable
    (ae_of_all _ fun z ↦ (abs_le.1 (hgM z)).2)
  have : IsFiniteMeasure R := Measure.isFiniteMeasure_of_map he.aemeasurable
  have hφi : Integrable φ μ :=
    Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun x ↦ hφC x)
  have hψi : Integrable ψ ν :=
    Integrable.of_bound hψ.aestronglyMeasurable C (ae_of_all _ fun y ↦ hψC y)
  have hmap : (R.withDensity fun ω ↦ ENNReal.ofReal (Real.exp (φ (e ω).1 + ψ (e ω).2))).map e =
      (R.map e).withDensity fun z ↦ ENNReal.ofReal (Real.exp (φ z.1 + ψ z.2)) :=
    Measure.map_withDensity_eq_withDensity (jac := 1) he measurable_const (by fun_prop) (by simp)
      (by simp)
  exact ⟨φ, ψ, C, hφ, hψ, hφC, hψC, by rwa [hmap],
    klDiv_withDensity_exp_add_comp_eq_dynamicSchroedingerValue he hσ hφ hψ hφi hψi⟩

end Potentials

end TauCeti
