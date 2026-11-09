/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Eval
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial

/-!
# Evaluation along bounded coefficient homomorphisms

A coefficient homomorphism `φ : R →+* S` satisfying `‖φ r‖ ≤ C * ‖r‖` need not be
contractive. Nevertheless, restricted series at positive polyradii `c` can be evaluated at
arguments `a i` with `‖a i‖ ≤ c i`, provided `S` is complete and ultrametric. Evaluation has
bound `C` and is the unique continuous ring homomorphism with the prescribed values on
constants and variables.

`MvPowerSeries.restrictedEval₂OfBound` first applies the bounded coefficient map
`TauCeti.MvPowerSeries.restrictedMap`, then evaluates over `S` along its identity map using
`MvPowerSeries.restrictedEval₂`. Thus it uses the same convergent monomial sum as contractive
evaluation, and agrees with that evaluation whenever the coefficient map is contractive.
The construction commutes with bounded coefficient maps and continuous maps of target rings.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace MvPowerSeries

open TauCeti.Huber
open TauCeti.MvPowerSeries (restrictedMap coe_restrictedMap norm_restrictedMap_le
  continuous_restrictedMap polynomialToRestricted restrictedMap_polynomialToRestricted
  denseRange_polynomialToRestricted)

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  {c : Fin k → ℝ} (φ : R →+* S) (a : Fin k → S) {C : ℝ}
  (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ c i)

/-- Evaluate restricted series along a coefficient homomorphism bounded by `C`. The arguments
are bounded by the source polyradii; evaluation increases the Gauss norm by at most `C`. -/
noncomputable def restrictedEval₂OfBound : IsRestricted.subring (R := R) c →+* S :=
  (restrictedEval₂ (RingHom.id S) a (fun _ ↦ le_rfl) ha).comp (restrictedMap φ hφ)

/-- Bounded evaluation is the usual convergent monomial sum. -/
theorem restrictedEval₂OfBound_apply (f : IsRestricted.subring (R := R) c) :
    restrictedEval₂OfBound φ a hφ ha f = weightedEval φ a f := by
  simp only [restrictedEval₂OfBound, RingHom.comp_apply, restrictedEval₂_apply,
    weightedEval_def, coe_restrictedMap, weightedEvalTerm_def, coeff_map, RingHom.id_apply]

/-- The monomial sum converges to bounded evaluation. -/
theorem hasSum_restrictedEval₂OfBound (f : IsRestricted.subring (R := R) c) :
    HasSum (weightedEvalTerm φ a f) (restrictedEval₂OfBound φ a hφ ha f) := by
  have ht : weightedEvalTerm (RingHom.id S) a
      (restrictedMap φ hφ f : MvPowerSeries (Fin k) S) = weightedEvalTerm φ a f := by
    funext t
    simp only [weightedEvalTerm_def, coe_restrictedMap, coeff_map, RingHom.id_apply]
  simpa only [ht, restrictedEval₂OfBound, RingHom.comp_apply] using
    hasSum_restrictedEval₂ (RingHom.id S) a (fun _ ↦ le_rfl) ha (restrictedMap φ hφ f)

/-- Bounded evaluation extends the coefficient map on constants. -/
@[simp]
theorem restrictedEval₂OfBound_algebraMap (r : R) :
    restrictedEval₂OfBound φ a hφ ha (algebraMap R _ r) = φ r := by
  rw [restrictedEval₂OfBound_apply, coe_algebraMap_isRestrictedSubring, weightedEval_C]

/-- Bounded evaluation sends the variable `X i` to the specified argument. -/
@[simp]
theorem restrictedEval₂OfBound_X (i : Fin k) :
    restrictedEval₂OfBound φ a hφ ha ⟨X i, isRestricted_X c i⟩ = a i := by
  rw [restrictedEval₂OfBound_apply, weightedEval_X]

/-- On polynomials, bounded evaluation is polynomial evaluation. -/
@[simp]
theorem restrictedEval₂OfBound_polynomial (p : MvPolynomial (Fin k) R) :
    restrictedEval₂OfBound φ a hφ ha (polynomialToRestricted c p) =
      MvPolynomial.eval₂ φ a p := by
  rw [restrictedEval₂OfBound, RingHom.comp_apply, restrictedMap_polynomialToRestricted,
    TauCeti.MvPowerSeries.polynomialToRestricted_apply, restrictedEval₂_polynomial]
  simp only [MvPolynomial.eval₂_map, RingHom.id_comp]

/-- The bounded construction agrees with contractive evaluation when both apply. -/
theorem restrictedEval₂OfBound_eq_restrictedEval₂ (hφ' : ∀ r, ‖φ r‖ ≤ ‖r‖) :
    restrictedEval₂OfBound φ a hφ ha = restrictedEval₂ φ a hφ' ha := by
  ext f
  rw [restrictedEval₂OfBound_apply, restrictedEval₂_apply]

variable [∀ i, Fact (0 < c i)]

/-- Evaluation has the same bound as the coefficient homomorphism. No multiplicativity of
coefficient norms, norm-one hypothesis, or completeness of `R` is required. -/
theorem norm_restrictedEval₂OfBound_le (f : IsRestricted.subring (R := R) c) :
    ‖restrictedEval₂OfBound φ a hφ ha f‖ ≤ C * ‖f‖ :=
  (norm_restrictedEval₂_le (RingHom.id S) a (fun _ ↦ le_rfl) ha _).trans
    (norm_restrictedMap_le φ hφ f)

/-- Bounded evaluation is Lipschitz for the Gauss norm topology. -/
theorem lipschitzWith_restrictedEval₂OfBound :
    LipschitzWith (Real.toNNReal C) (restrictedEval₂OfBound φ a hφ ha) :=
  AddMonoidHomClass.lipschitz_of_bound _ C (norm_restrictedEval₂OfBound_le φ a hφ ha)

/-- Bounded evaluation is continuous for the Gauss norm topology. -/
@[continuity]
theorem continuous_restrictedEval₂OfBound : Continuous (restrictedEval₂OfBound φ a hφ ha) :=
  (lipschitzWith_restrictedEval₂OfBound φ a hφ ha).continuous

/-- A continuous homomorphism with the prescribed values on constants and variables is
bounded evaluation. Uniqueness requires continuity, but not a supplied norm bound on the map. -/
theorem eq_restrictedEval₂OfBound (ψ : IsRestricted.subring (R := R) c →+* S)
    (hψ : Continuous ψ) (hC : ∀ r, ψ (algebraMap R _ r) = φ r)
    (hX : ∀ i, ψ ⟨X i, isRestricted_X c i⟩ = a i) :
    ψ = restrictedEval₂OfBound φ a hφ ha := by
  have hp : ψ.comp (polynomialToRestricted c).toRingHom =
      (restrictedEval₂OfBound φ a hφ ha).comp (polynomialToRestricted c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [← MvPolynomial.algebraMap_eq, hC]
    · intro i
      simpa using (hX i).trans (restrictedEval₂OfBound_X φ a hφ ha i).symm
  exact DFunLike.coe_injective (denseRange_polynomialToRestricted.equalizer hψ
    (continuous_restrictedEval₂OfBound φ a hφ ha) (funext (DFunLike.congr_fun hp)))

include hφ ha in
/-- The universal property at bounded arguments for an arbitrary bounded coefficient map. -/
theorem existsUnique_continuous_ringHom_of_bound :
    ∃! ψ : IsRestricted.subring (R := R) c →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X c i⟩ = a i :=
  ⟨restrictedEval₂OfBound φ a hφ ha,
    ⟨continuous_restrictedEval₂OfBound φ a hφ ha,
      restrictedEval₂OfBound_algebraMap φ a hφ ha, restrictedEval₂OfBound_X φ a hφ ha⟩,
    fun ψ ⟨hψ, hC, hX⟩ ↦ eq_restrictedEval₂OfBound φ a hφ ha ψ hψ hC hX⟩

section Naturality

variable {T : Type*} [NormedCommRing T] [IsUltrametricDist T]

omit [∀ i, Fact (0 < c i)] in
/-- Bounded evaluation commutes with a bounded map of source coefficients. The bound on the
composite may be chosen independently of the bounds used to construct either map. -/
theorem restrictedEval₂OfBound_restrictedMap (θ : T →+* R) {D E : ℝ}
    (hθ : ∀ t, ‖θ t‖ ≤ D * ‖t‖) (hφθ : ∀ t, ‖(φ.comp θ) t‖ ≤ E * ‖t‖)
    (f : IsRestricted.subring (R := T) c) :
    restrictedEval₂OfBound φ a hφ ha (restrictedMap θ hθ f) =
      restrictedEval₂OfBound (φ.comp θ) a hφθ ha f := by
  simp only [restrictedEval₂OfBound_apply, coe_restrictedMap, weightedEval_def,
    weightedEvalTerm_def, coeff_map, RingHom.comp_apply]

variable [CompleteSpace T]

/-- Applying a continuous target homomorphism to an evaluated series agrees with evaluating
its images, whenever the composite coefficient map is bounded and the image arguments still
lie in the prescribed polydisc. -/
theorem map_restrictedEval₂OfBound (θ : S →+* T) (hθ : Continuous θ) {D : ℝ}
    (hθφ : ∀ r, ‖(θ.comp φ) r‖ ≤ D * ‖r‖) (hθa : ∀ i, ‖θ (a i)‖ ≤ c i)
    (f : IsRestricted.subring (R := R) c) :
    θ (restrictedEval₂OfBound φ a hφ ha f) =
      restrictedEval₂OfBound (θ.comp φ) (θ ∘ a) hθφ hθa f := by
  have h := eq_restrictedEval₂OfBound (θ.comp φ) (θ ∘ a) hθφ hθa
    (θ.comp (restrictedEval₂OfBound φ a hφ ha))
    (hθ.comp (continuous_restrictedEval₂OfBound φ a hφ ha))
    (fun r ↦ by simp) (fun i ↦ by simp)
  exact DFunLike.congr_fun h f

end Naturality

end MvPowerSeries
