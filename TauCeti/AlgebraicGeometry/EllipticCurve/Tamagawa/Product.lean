/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Local
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.AlmostEverywhere
import TauCeti.NumberTheory.LocalField.Henselian

/-!
# The finite product of local Tamagawa numbers

For an elliptic curve over the fraction field of a Dedekind domain with finite residue fields,
the local Tamagawa numbers are computed on the actual completed fields. All but finitely many
are one, by `TauCeti.eventually_isElliptic_integralModel_adicCompletion`: an elliptic equation
itself has an elliptic integral model at almost every prime.
Their finite product is positive, is independent of the Weierstrass presentation, and can be
computed over any finite set outside which there is good reduction.

The completed indices are defined for arbitrary Weierstrass equations. The product is formed
over the finite multiplicative support proved for elliptic curves.

This supplies the finite-place product in the arithmetic Birch–Swinnerton-Dyer quotient,
in particular for elliptic curves over `ℚ` with the Dedekind domain `ℤ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.5–6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9.
-/

public section

open IsDedekindDomain ValuativeRel

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

-- The height-one-prime carrier supplies nonzeroness as a theorem, rather than a `NeZero` instance.
local instance (v : HeightOneSpectrum R) : Finite (R ⧸ v.asIdeal) :=
  Ring.HasFiniteQuotients.finiteQuotient v.ne_bot

/-- The minimal-equation index over the completed field at a finite prime. For elliptic curves
this is the local Tamagawa number. -/
noncomputable def tamagawaNumberAt (E : WeierstrassCurve K)
    (v : HeightOneSpectrum R) : ℕ :=
  (E.baseChange (v.adicCompletion K)).tamagawaNumber (valuation (v.adicCompletion K))

/-- The completed point-group Tamagawa number is the factor at the given prime. -/
theorem tamagawaNumberAt_def (E : WeierstrassCurve K)
    (v : HeightOneSpectrum R) : E.tamagawaNumberAt v =
      (E.baseChange (v.adicCompletion K)).tamagawaNumber (valuation (v.adicCompletion K)) :=
  (rfl)

/-- Each finite-place Tamagawa number is positive. -/
theorem tamagawaNumberAt_pos (E : WeierstrassCurve K) [E.IsElliptic]
    (v : HeightOneSpectrum R) : 0 < E.tamagawaNumberAt v := by
  let : HenselianLocalRing (valuation (v.adicCompletion K)).valuationSubring :=
    inferInstanceAs (HenselianLocalRing 𝒪[v.adicCompletion K])
  let : Finite (IsLocalRing.ResidueField (valuation (v.adicCompletion K)).valuationSubring) :=
    inferInstanceAs (Finite 𝓀[v.adicCompletion K])
  rw [tamagawaNumberAt_def]
  exact tamagawaNumber_pos _ _

/-- A finite-place Tamagawa number depends only on the curve's isomorphism class. -/
@[simp]
theorem tamagawaNumberAt_smul (E : WeierstrassCurve K) [E.IsElliptic]
    (C : VariableChange K) (v : HeightOneSpectrum R) :
    (C • E).tamagawaNumberAt v = E.tamagawaNumberAt v := by
  simp only [tamagawaNumberAt_def, ← baseChange_smul_baseChange, tamagawaNumber_smul]

/-- Good reduction in the completed field gives a local factor of one. -/
@[simp]
theorem tamagawaNumberAt_eq_one_of_hasGoodReduction (E : WeierstrassCurve K)
    (v : HeightOneSpectrum R)
    [(E.baseChange (v.adicCompletion K)).HasGoodReduction 𝒪[v.adicCompletion K]] :
    E.tamagawaNumberAt v = 1 := by
  have : (E.baseChange (v.adicCompletion K)).HasGoodReduction
      (valuation (v.adicCompletion K)).valuationSubring :=
    inferInstanceAs ((E.baseChange (v.adicCompletion K)).HasGoodReduction 𝒪[v.adicCompletion K])
  rw [tamagawaNumberAt_def, tamagawaNumber_eq_one_of_hasGoodReduction]

/-- Local Tamagawa numbers are one outside finitely many primes. -/
theorem hasFiniteMulSupport_tamagawaNumberAt (E : WeierstrassCurve K) [E.IsElliptic] :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦ E.tamagawaNumberAt v) := by
  have hmodel := TauCeti.eventually_isElliptic_integralModel_adicCompletion R E
  have hone : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, E.tamagawaNumberAt v = 1 := by
    filter_upwards [hmodel] with v hv
    obtain ⟨hI, hΔ⟩ := hv
    let := hI
    have : (E.baseChange (v.adicCompletion K)).HasGoodReduction 𝒪[v.adicCompletion K] :=
      (hasGoodReduction_iff_isUnit_integralModel_Δ _ _).2 hΔ.1
    exact E.tamagawaNumberAt_eq_one_of_hasGoodReduction v
  exact Filter.eventually_cofinite.mp hone

open scoped Classical in
/-- The product of local Tamagawa numbers over their finite multiplicative support. -/
noncomputable def tamagawaProduct (E : WeierstrassCurve K) [E.IsElliptic] : ℕ :=
  ∏ v ∈ (E.hasFiniteMulSupport_tamagawaNumberAt (R := R)).toFinset, E.tamagawaNumberAt v

/-- The Tamagawa product is the finite product of the completed local factors. -/
theorem tamagawaProduct_def (E : WeierstrassCurve K) [E.IsElliptic] :
    E.tamagawaProduct (R := R) = ∏ᶠ v : HeightOneSpectrum R, E.tamagawaNumberAt v :=
  (finprod_eq_prod _ E.hasFiniteMulSupport_tamagawaNumberAt).symm

/-- Any finite set containing the factors different from one computes the Tamagawa product. -/
theorem tamagawaProduct_eq_prod (E : WeierstrassCurve K) [E.IsElliptic]
    (S : Finset (HeightOneSpectrum R))
    (hS : ∀ v ∉ S, E.tamagawaNumberAt v = 1) :
    E.tamagawaProduct (R := R) = ∏ v ∈ S, E.tamagawaNumberAt v := by
  classical
  rw [tamagawaProduct_def]
  exact finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
    by_contra hnot
    exact hv (hS v hnot)

/-- The finite product of local Tamagawa numbers is positive. -/
theorem tamagawaProduct_pos (E : WeierstrassCurve K) [E.IsElliptic] :
    0 < E.tamagawaProduct (R := R) := by
  rw [tamagawaProduct_def]
  apply Nat.pos_of_ne_zero
  apply finprod_ne_zero
  intro v
  exact (E.tamagawaNumberAt_pos v).ne'

/-- The Tamagawa product is invariant under a change of Weierstrass variables. -/
@[simp]
theorem tamagawaProduct_smul (E : WeierstrassCurve K) [E.IsElliptic] (C : VariableChange K) :
    (C • E).tamagawaProduct (R := R) = E.tamagawaProduct (R := R) := by
  simp only [tamagawaProduct_def, tamagawaNumberAt_smul]

end WeierstrassCurve

end
