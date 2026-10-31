/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Analysis.Meromorphic.Conj
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# Completed L-function data in the analytic normalization

An L-function in the analytic normalization is described by its Dirichlet coefficients
`a : ℕ → ℂ`, a positive integral conductor `N`, two multisets of gamma shifts `μ_j` and `ν_k`, a
root number `ε`, a completed function `Λ`, and a finitely supported polar divisor. The expected
shape of the theory is
```
Λ(s) = N^(s/2) γ(s) L(s),   γ(s) = ∏_j Γ_ℝ(s + μ_j) ∏_k Γ_ℂ(s + ν_k),
Λ(s) = ε · conj Λ(1 - conj s),
```
with the functional equation centred at `s = 1/2` and the conductor power included in `Λ`, so
that the functional equation carries no further constant. The structure
`TauCeti.LFunctions.AnalyticLFunctionData` records these data, and three `Prop`-valued
predicates record the properties a card is expected to have:

* `HasDirichletAgreement`: `a 1 = 1`, the degree is positive, and `Λ(s) = N^(s/2) γ(s) L(a, s)`
  on `Re s > 1`;
* `HasMeromorphicContinuation`: `Λ` is meromorphic on `ℂ`, has a pole of exactly the recorded
  order at every point of the polar divisor, and is analytic elsewhere;
* `HasFunctionalEquation`: `|ε| = 1`, the polar divisor is symmetric under `s ↦ 1 - conj s`, and
  `Λ(s) = ε Λ^∨(1 - s)` wherever both sides are regular.

The dual card `AnalyticLFunctionData.dual` conjugates the coefficients, the gamma shifts and the
root number, reflects the completed function to `s ↦ conj Λ(conj s)` and conjugates the polar
divisor. It is involutive, preserves the degree, conjugates the gamma factor, and preserves each
of the three predicates. Since Mathlib's value of a function at a pole carries no information, the
functional equation is asserted only off the polar loci; `HasFunctionalEquation.eventuallyEq`
upgrades it to an equality of punctured germs at every point.

The coefficient at `0`, which `LSeries` never reads, is deliberately left free: independently
defined analytic presentations may use different values there, so no global zero convention is
imposed on the analytic record.

## Main definitions

* `TauCeti.LFunctions.AnalyticLFunctionData`: the completed-function record.
* `AnalyticLFunctionData.degree`, `AnalyticLFunctionData.gammaFactor`: the degree
  `#μ + 2 #ν` and the gamma factor `γ(s)`.
* `AnalyticLFunctionData.dual`: the dual card.
* `AnalyticLFunctionData.HasDirichletAgreement`, `HasMeromorphicContinuation`,
  `HasFunctionalEquation`: the basic properties.

## Main results

* `AnalyticLFunctionData.dual_dual`, `degree_dual`, `gammaFactor_dual`.
* `HasDirichletAgreement.dual`, `HasMeromorphicContinuation.dual`, `HasFunctionalEquation.dual`.
* `HasFunctionalEquation.eventuallyEq`: the functional equation as germs at every point.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
-/

public section

open Complex ComplexConjugate Filter Topology

namespace TauCeti.LFunctions

/-- **Completed L-function data in the analytic normalization.** The Dirichlet coefficients
`coeff`, the conductor `N`, the real and complex gamma shifts, the root number `ε`, the completed
function `Λ`, and the polar divisor, intended to record the order of the pole of `Λ` at each point.
The intended properties of these data are the predicates `HasDirichletAgreement`,
`HasMeromorphicContinuation` and `HasFunctionalEquation`; the record itself imposes none of them.
-/
@[ext]
structure AnalyticLFunctionData where
  /-- The Dirichlet coefficients `a n`; the coefficient at `0` is never read by `LSeries`. -/
  coeff : ℕ → ℂ
  /-- The conductor `N`. -/
  conductor : ℕ+
  /-- The real gamma shifts `μ_j`, each contributing a factor `Γ_ℝ(s + μ_j)`. -/
  gammaR : Multiset ℂ
  /-- The complex gamma shifts `ν_k`, each contributing a factor `Γ_ℂ(s + ν_k)`. -/
  gammaC : Multiset ℂ
  /-- The root number `ε`. -/
  rootNumber : ℂ
  /-- The completed function `Λ`; `HasDirichletAgreement` asks that it equal
  `N^(s/2) γ(s) L(s)` on `Re s > 1`. -/
  completed : ℂ → ℂ
  /-- The intended polar divisor of `Λ`; `HasMeromorphicContinuation` asks that it record the
  exact pole orders. -/
  polarOrder : ℂ →₀ ℕ

namespace AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The **degree** `#μ + 2 #ν` of a card: a real gamma shift counts once and a complex gamma
shift twice, as `Γ_ℂ(s) = Γ_ℝ(s) Γ_ℝ(s + 1)`. -/
def degree : ℕ := d.gammaR.card + 2 * d.gammaC.card

theorem degree_def : d.degree = d.gammaR.card + 2 * d.gammaC.card := (rfl)

/-- The **gamma factor** `γ(s) = ∏_j Γ_ℝ(s + μ_j) ∏_k Γ_ℂ(s + ν_k)` of a card. -/
noncomputable def gammaFactor (s : ℂ) : ℂ :=
  (d.gammaR.map fun μ ↦ Gammaℝ (s + μ)).prod * (d.gammaC.map fun ν ↦ Gammaℂ (s + ν)).prod

theorem gammaFactor_def (s : ℂ) :
    d.gammaFactor s =
      (d.gammaR.map fun μ ↦ Gammaℝ (s + μ)).prod * (d.gammaC.map fun ν ↦ Gammaℂ (s + ν)).prod :=
  (rfl)

/-- The **dual card**: conjugate coefficients, conjugate gamma shifts, conjugate root number, the
reflected completed function `s ↦ conj Λ(conj s)`, and the conjugate polar divisor. The conductor
is unchanged. -/
noncomputable def dual : AnalyticLFunctionData where
  coeff n := conj (d.coeff n)
  conductor := d.conductor
  gammaR := d.gammaR.map conj
  gammaC := d.gammaC.map conj
  rootNumber := conj d.rootNumber
  completed := conj ∘ d.completed ∘ conj
  polarOrder := d.polarOrder.mapDomain conj

@[simp]
theorem dual_coeff (n : ℕ) : d.dual.coeff n = conj (d.coeff n) := (rfl)

@[simp]
theorem dual_conductor : d.dual.conductor = d.conductor := (rfl)

@[simp]
theorem dual_gammaR : d.dual.gammaR = d.gammaR.map conj := (rfl)

@[simp]
theorem dual_gammaC : d.dual.gammaC = d.gammaC.map conj := (rfl)

@[simp]
theorem dual_rootNumber : d.dual.rootNumber = conj d.rootNumber := (rfl)

@[simp]
theorem dual_completed : d.dual.completed = conj ∘ d.completed ∘ conj := (rfl)

theorem dual_completed_apply (s : ℂ) : d.dual.completed s = conj (d.completed (conj s)) := (rfl)

@[simp]
theorem dual_polarOrder_apply (s : ℂ) : d.dual.polarOrder s = d.polarOrder (conj s) := by
  conv_lhs => rw [← Complex.conj_conj s]
  exact Finsupp.mapDomain_apply_of_injective (starRingEnd ℂ).injective _ _

/-- Taking the dual card is involutive. -/
@[simp]
theorem dual_dual : d.dual.dual = d := by
  ext <;> simp [Function.comp_def]

theorem dual_involutive : Function.Involutive dual := dual_dual

@[simp]
theorem degree_dual : d.dual.degree = d.degree := by
  simp [degree_def]

/-- The gamma factor of the dual card is the reflected gamma factor. -/
theorem gammaFactor_dual (s : ℂ) : d.dual.gammaFactor s = conj (d.gammaFactor (conj s)) := by
  simp [gammaFactor_def, map_multiset_prod, Multiset.map_map,
    ← Complex.Gammaℝ_conj, ← Complex.Gammaℂ_conj]

/-- **Agreement with a Dirichlet series.** The first coefficient is `1`, the degree is positive,
and the completed function is `N^(s/2) γ(s) L(a, s)` on the half-plane `Re s > 1`. -/
structure HasDirichletAgreement : Prop where
  coeff_one : d.coeff 1 = 1
  degree_pos : 0 < d.degree
  completed_eq : ∀ s : ℂ, 1 < s.re →
    d.completed s = ((d.conductor : ℕ) : ℂ) ^ (s / 2) * d.gammaFactor s * LSeries d.coeff s

/-- **Meromorphic continuation with exact poles.** The completed function is meromorphic on `ℂ`,
has a pole of exactly the recorded order at each point of the polar divisor, and is analytic at
every other point. -/
structure HasMeromorphicContinuation : Prop where
  meromorphic : Meromorphic d.completed
  meromorphicOrderAt_eq : ∀ p : ℂ, d.polarOrder p ≠ 0 →
    meromorphicOrderAt d.completed p = (-(d.polarOrder p : ℤ) : WithTop ℤ)
  analyticAt : ∀ p : ℂ, d.polarOrder p = 0 → AnalyticAt ℂ d.completed p

/-- **The functional equation.** The root number has absolute value `1`, the polar divisor is
symmetric under the reflection `s ↦ 1 - conj s`, and `Λ(s) = ε Λ^∨(1 - s)` at every `s` at which
neither `s` nor `1 - conj s` is a pole. Here `Λ^∨(1 - s) = conj Λ(1 - conj s)` is the completed
function of the dual card. -/
structure HasFunctionalEquation : Prop where
  norm_rootNumber : ‖d.rootNumber‖ = 1
  polarOrder_one_sub_conj : ∀ s : ℂ, d.polarOrder (1 - conj s) = d.polarOrder s
  completed_eq : ∀ s : ℂ, d.polarOrder s = 0 → d.polarOrder (1 - conj s) = 0 →
    d.completed s = d.rootNumber * d.dual.completed (1 - s)

variable {d}

/-- The dual of a card that agrees with a Dirichlet series agrees with the conjugate series. -/
theorem HasDirichletAgreement.dual (h : d.HasDirichletAgreement) :
    d.dual.HasDirichletAgreement where
  coeff_one := by simp [h.coeff_one]
  degree_pos := by simpa using h.degree_pos
  completed_eq s hs := by
    have hLs : LSeries d.dual.coeff s = conj (LSeries d.coeff (conj s)) := by
      have hc : d.dual.coeff = star d.coeff := funext fun n ↦ by simp
      simpa [hc, Complex.star_def] using TauCeti.LSeries.LSeries_star d.coeff (conj s)
    have hN := TauCeti.ofReal_cpow_conj (d.conductor : ℕ).cast_nonneg (s / 2)
    rw [Complex.ofReal_natCast, map_div₀, map_ofNat] at hN
    rw [dual_completed_apply, h.completed_eq _ (by simpa using hs), map_mul, map_mul, hN,
      Complex.conj_conj, gammaFactor_dual, dual_conductor, hLs]

/-- The dual of a meromorphically continued card is meromorphically continued, with the
conjugate poles. -/
theorem HasMeromorphicContinuation.dual (h : d.HasMeromorphicContinuation) :
    d.dual.HasMeromorphicContinuation where
  meromorphic := h.meromorphic.conj_conj
  meromorphicOrderAt_eq p hp := by
    rw [dual_polarOrder_apply] at hp ⊢
    rw [dual_completed, meromorphicOrderAt_conj_conj, h.meromorphicOrderAt_eq _ hp]
  analyticAt p hp := by
    rw [dual_polarOrder_apply] at hp
    rw [dual_completed, analyticAt_conj_conj_iff]
    exact h.analyticAt _ hp

/-- The dual of a card with a functional equation has a functional equation, with the conjugate
root number. -/
theorem HasFunctionalEquation.dual (h : d.HasFunctionalEquation) :
    d.dual.HasFunctionalEquation where
  norm_rootNumber := by simpa using h.norm_rootNumber
  polarOrder_one_sub_conj s := by
    simpa using h.polarOrder_one_sub_conj (conj s)
  completed_eq s hs hs' := by
    simp only [dual_polarOrder_apply, map_sub, map_one, Complex.conj_conj] at hs hs'
    have h' := h.completed_eq (conj s) hs (by simpa using hs')
    simp [dual_completed_apply, h', map_sub]

/-- **The functional equation as germs.** If a card satisfies its functional equation off the
polar loci, then `Λ(z) = ε Λ^∨(1 - z)` on a punctured neighbourhood of every point, poles
included: the polar divisor is finitely supported, so both polar loci are finite. -/
theorem HasFunctionalEquation.eventuallyEq (h : d.HasFunctionalEquation) (s : ℂ) :
    d.completed =ᶠ[𝓝[≠] s] fun z ↦ d.rootNumber * d.dual.completed (1 - z) := by
  have hfin : (d.polarOrder.support : Set ℂ).Finite := d.polarOrder.support.finite_toSet
  have hfin' : ((fun z : ℂ ↦ 1 - conj z) ⁻¹' (d.polarOrder.support : Set ℂ)).Finite :=
    hfin.preimage (Function.Injective.injOn fun a b hab ↦
      (starRingEnd ℂ).injective (sub_right_injective hab))
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite univ_mem (hfin.union hfin').to_subtype]
    with z hz
  simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff,
    Set.mem_preimage, true_and, not_or, not_not] at hz
  exact h.completed_eq z hz.1 hz.2

end AnalyticLFunctionData

end TauCeti.LFunctions
