/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Radius

/-!
# Bounded coefficient maps on overconvergent power series

A bounded ring homomorphism `φ : R →+* S` between ultrametric normed commutative rings, satisfying
`‖φ r‖ ≤ C * ‖r‖`, preserves restrictedness at every radius `ρ > 1`. It therefore induces a
coefficientwise ring homomorphism `washnitzerAlgebra.map φ hφ : R⟨X⟩† →+* S⟨X⟩†` between the
Monsky–Washnitzer algebras, compatible with the inclusions `ofRestricted` and `ofOneLt` from finite
polyradii and with `toTate` into the unit-radius Tate algebras.

For the unit Gauss norms, `map φ hφ` is bounded by the same constant `C`, hence Lipschitz and
continuous, and is an isometry when `φ` preserves norms. When every scalar in `S` admits a lift
along `φ` with linear norm control (`‖r‖ ≤ C' * ‖s‖`), lifting coefficients at a witness radius
`ρ > 1` shows that `map φ hφ` is surjective, so noetherianity of `R⟨X⟩†` passes to `S⟨X⟩†`.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.map`: the coefficientwise ring homomorphism
  `R⟨X⟩† →+* S⟨X⟩†` induced by a bounded ring homomorphism `φ : R →+* S`.

## Main results

* `TauCeti.Dagger.map_mem_washnitzerAlgebra`: bounded coefficient maps preserve overconvergence.
* `TauCeti.Dagger.washnitzerAlgebra.toTate_map`,
  `TauCeti.Dagger.washnitzerAlgebra.map_ofRestricted`, and
  `TauCeti.Dagger.washnitzerAlgebra.map_ofOneLt`: compatibility with `toTate` and polyradius
  inclusions.
* `TauCeti.Dagger.washnitzerAlgebra.norm_map_le`,
  `TauCeti.Dagger.washnitzerAlgebra.isometry_map`, and
  `TauCeti.Dagger.washnitzerAlgebra.continuous_map`: Gauss norm bound, isometric case, and
  continuity.
* `TauCeti.Dagger.washnitzerAlgebra.exists_map_eq_and_norm_coeff_le` and
  `TauCeti.Dagger.washnitzerAlgebra.map_surjective`: coefficientwise bounded lifts and
  surjectivity along strict surjections.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.
* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries
open TauCeti.MvPowerSeries (restrictedMap coe_restrictedMap coeff_restrictedMap
  norm_restrictedMap_le norm_restrictedMap restrictedMap_renameAlgEquiv
  exists_restrictedMap_eq_and_norm_coeff_le)

variable {σ R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S]

/-- **Bounded coefficient maps preserve overconvergence.** If `φ : R →+* S` satisfies
`‖φ r‖ ≤ C * ‖r‖`, then applying `φ` coefficientwise maps `R⟨X⟩†` into `S⟨X⟩†`. -/
theorem map_mem_washnitzerAlgebra (φ : R →+* S) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {f : MvPowerSeries σ R} (hf : f ∈ washnitzerAlgebra σ R) :
    _root_.MvPowerSeries.map φ f ∈ washnitzerAlgebra σ S := by
  obtain ⟨ρ, hρ, hf⟩ := mem_washnitzerAlgebra.mp hf
  exact mem_washnitzerAlgebra.mpr ⟨ρ, hρ, isRestricted_map _ φ hφ hf⟩

namespace washnitzerAlgebra

section Map

variable (φ : R →+* S) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

/-- **The coefficientwise map `R⟨X⟩† →+* S⟨X⟩†`** induced by a bounded ring homomorphism
`φ : R →+* S` satisfying `‖φ r‖ ≤ C * ‖r‖`. -/
noncomputable def map : washnitzerAlgebra σ R →+* washnitzerAlgebra σ S :=
  ((_root_.MvPowerSeries.map φ).comp (washnitzerAlgebra σ R).toSubring.subtype).codRestrict
    (washnitzerAlgebra σ S).toSubring fun f ↦ map_mem_washnitzerAlgebra φ hφ f.property

/-- `washnitzerAlgebra.map` acts as `MvPowerSeries.map` on the underlying formal power series. -/
@[simp]
theorem coe_map (f : washnitzerAlgebra σ R) :
    (map φ hφ f : MvPowerSeries σ S) = _root_.MvPowerSeries.map φ f :=
  (rfl)

/-- `washnitzerAlgebra.map` applies `φ` to each coefficient. -/
theorem coeff_map (f : washnitzerAlgebra σ R) (t : σ →₀ ℕ) :
    coeff t (map φ hφ f : MvPowerSeries σ S) = φ (coeff t (f : MvPowerSeries σ R)) := by
  rw [coe_map, _root_.MvPowerSeries.coeff_map]

/-- The induced map on `W` depends only on `φ`, not on the chosen norm-bound witness. -/
theorem map_eq_map {C' : ℝ} (hφ' : ∀ r, ‖φ r‖ ≤ C' * ‖r‖) :
    map (σ := σ) φ hφ = map φ hφ' :=
  RingHom.ext fun _ ↦ Subtype.ext (by simp)

/-- An overconvergent series lies in the kernel of `map φ hφ` iff all its coefficients lie in the
kernel of `φ`. -/
@[simp]
theorem map_eq_zero_iff (f : washnitzerAlgebra σ R) :
    map φ hφ f = 0 ↔ ∀ t, φ (coeff t (f : MvPowerSeries σ R)) = 0 := by
  refine ⟨fun h t ↦ ?_, fun h ↦ Subtype.ext <| MvPowerSeries.ext fun t ↦ ?_⟩
  · simpa only [coeff_map, ZeroMemClass.coe_zero, map_zero] using
      congrArg (fun g : washnitzerAlgebra σ S ↦ coeff t (g : MvPowerSeries σ S)) h
  · simpa only [coeff_map, ZeroMemClass.coe_zero, map_zero] using h t

/-- `washnitzerAlgebra.map` is functorial under composition of bounded ring homomorphisms. -/
theorem map_comp {T : Type*} [NormedCommRing T] [IsUltrametricDist T] (ψ : S →+* T)
    {C₂ C₃ : ℝ} (hψ : ∀ s, ‖ψ s‖ ≤ C₂ * ‖s‖) (hψφ : ∀ r, ‖ψ.comp φ r‖ ≤ C₃ * ‖r‖) :
    map (σ := σ) (ψ.comp φ) hψφ = (map ψ hψ).comp (map φ hφ) :=
  RingHom.ext fun _ ↦ Subtype.ext <| MvPowerSeries.ext fun _ ↦ by simp

/-- `washnitzerAlgebra.map` sends the constant `r` to the constant `φ r`. -/
@[simp]
theorem map_algebraMap (r : R) :
    map (σ := σ) φ hφ (algebraMap R _ r) = algebraMap S _ (φ r) :=
  Subtype.ext (by simp [MvPowerSeries.algebraMap_apply])

/-- `washnitzerAlgebra.map` sends each variable `Xᵢ` to `Xᵢ`. -/
@[simp]
theorem map_X (i : σ) : map φ hφ (X σ R i) = X σ S i :=
  Subtype.ext (by simp)

/-- `washnitzerAlgebra.map` sends a multivariate polynomial to its coefficientwise image. -/
@[simp]
theorem map_ofMvPolynomial (p : MvPolynomial σ R) :
    map φ hφ (ofMvPolynomial σ R p) = ofMvPolynomial σ S (MvPolynomial.map φ p) := by
  have h : (map (σ := σ) φ hφ).comp (ofMvPolynomial σ R).toRingHom =
      (ofMvPolynomial σ S).toRingHom.comp (MvPolynomial.map φ) :=
    MvPolynomial.ringHom_ext (fun r ↦ by simp [← MvPolynomial.algebraMap_eq]) (by simp)
  exact DFunLike.congr_fun h p

/-- `washnitzerAlgebra.map` sends a one-variable polynomial to its coefficientwise image. -/
@[simp]
theorem map_ofPolynomial (p : Polynomial R) :
    map φ hφ (ofPolynomial R p) = ofPolynomial S (Polynomial.map φ p) := by
  have h : (map (σ := Unit) φ hφ).comp (ofPolynomial R).toRingHom =
      (ofPolynomial S).toRingHom.comp (Polynomial.mapRingHom φ) :=
    Polynomial.ringHom_ext
      (fun r ↦ by
        simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
        rw [← DFunLike.congr_fun Polynomial.algebraMap_eq r,
          ← DFunLike.congr_fun Polynomial.algebraMap_eq (φ r)]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, map_algebraMap])
      (by simp)
  exact DFunLike.congr_fun h p

/-- Composing `washnitzerAlgebra.map` with `toTate` gives `restrictedMap` on unit-radius Tate
algebras. -/
@[simp]
theorem toTate_map (f : washnitzerAlgebra σ R) :
    toTate σ S (map φ hφ f) = restrictedMap φ hφ (toTate σ R f) :=
  Subtype.ext (by simp [coe_restrictedMap])

/-- `toTate` intertwines `washnitzerAlgebra.map` and `restrictedMap` as ring homomorphisms. -/
theorem toTate_comp_map :
    (toTate σ S).toRingHom.comp (map φ hφ) = (restrictedMap φ hφ).comp (toTate σ R).toRingHom :=
  RingHom.ext (toTate_map φ hφ)

/-- `washnitzerAlgebra.map` commutes with polyradius inclusions `ofRestricted`. -/
@[simp]
theorem map_ofRestricted {c : σ → ℝ} {ρ : ℝ} (hρ : 1 < ρ) (hc : ∀ i, ρ ≤ c i)
    (f : IsRestricted.subring (R := R) c) :
    map φ hφ (ofRestricted hρ hc f) = ofRestricted hρ hc (restrictedMap φ hφ f) :=
  Subtype.ext (by simp [coe_restrictedMap])

/-- `washnitzerAlgebra.map` commutes with finite-variable polyradius inclusions `ofOneLt`. -/
@[simp]
theorem map_ofOneLt [Finite σ] {c : σ → ℝ} (hc : ∀ i, 1 < c i)
    (f : IsRestricted.subring (R := R) c) :
    map φ hφ (ofOneLt hc f) = ofOneLt hc (restrictedMap φ hφ f) :=
  Subtype.ext (by simp [coe_restrictedMap])

/-- `washnitzerAlgebra.map` commutes with renaming the variables along an equivalence. -/
theorem map_renameAlgEquiv {τ : Type*} (e : σ ≃ τ) (f : washnitzerAlgebra σ R) :
    map φ hφ (renameAlgEquiv e f) = renameAlgEquiv e (map φ hφ f) := by
  apply toTate_injective
  have hL : toTate τ R (renameAlgEquiv e f) =
      IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ)) (toTate σ R f) :=
    Subtype.ext (by simp)
  have hR : toTate τ S (renameAlgEquiv e (map φ hφ f)) =
      IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ)) (toTate σ S (map φ hφ f)) :=
    Subtype.ext (by simp [coe_restrictedMap])
  rw [toTate_map, hL, hR, toTate_map, restrictedMap_renameAlgEquiv]

/-- `washnitzerAlgebra.map` increases the unit Gauss norm by at most the bound `C` on `φ`. -/
theorem norm_map_le (f : washnitzerAlgebra σ R) : ‖map φ hφ f‖ ≤ C * ‖f‖ := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  rw [← norm_toTate, ← norm_toTate, toTate_map]
  exact norm_restrictedMap_le φ hφ (toTate σ R f)

/-- A norm-preserving coefficient homomorphism induces a Gauss-norm-preserving map on `W`. -/
@[simp]
theorem norm_map (hφ' : ∀ r, ‖φ r‖ = ‖r‖) (f : washnitzerAlgebra σ R) :
    ‖map φ hφ f‖ = ‖f‖ := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  rw [← norm_toTate, ← norm_toTate, toTate_map, norm_restrictedMap φ hφ hφ']

/-- A norm-preserving coefficient homomorphism induces an isometry for the Gauss norms on `W`. -/
theorem isometry_map (hφ' : ∀ r, ‖φ r‖ = ‖r‖) : Isometry (map (σ := σ) φ hφ) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_map φ hφ hφ')

/-- Bounded coefficient maps on `W` are Lipschitz for the unit Gauss norms. -/
theorem lipschitzWith_map : LipschitzWith (Real.toNNReal C) (map (σ := σ) φ hφ) :=
  AddMonoidHomClass.lipschitz_of_bound _ C (norm_map_le φ hφ)

/-- Bounded coefficient maps on `W` are continuous for the unit Gauss norm topologies. -/
@[continuity]
theorem continuous_map : Continuous (map (σ := σ) φ hφ) :=
  (lipschitzWith_map φ hφ).continuous

/-- **Coefficientwise bounded lifts of overconvergent series.** If every `s ∈ S` lifts along `φ`
to some `r ∈ R` with `‖r‖ ≤ C' * ‖s‖`, then every `g ∈ S⟨X⟩†` lifts to some `f ∈ R⟨X⟩†` with the
same bound on every coefficient. -/
theorem exists_map_eq_and_norm_coeff_le {C' : ℝ}
    (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) (g : washnitzerAlgebra σ S) :
    ∃ f, map φ hφ f = g ∧ ∀ t,
      ‖coeff t (f : MvPowerSeries σ R)‖ ≤ C' * ‖coeff t (g : MvPowerSeries σ S)‖ := by
  obtain ⟨ρ, hρ, hg⟩ := mem_washnitzerAlgebra.mp g.property
  obtain ⟨f₀, hf₀, hcoeff⟩ :=
    exists_restrictedMap_eq_and_norm_coeff_le (c := fun _ : σ ↦ ρ) φ hφ hlift ⟨g, hg⟩
  refine ⟨ofRestricted hρ (fun _ ↦ le_rfl) f₀, ?_, fun t ↦ by simpa using hcoeff t⟩
  rw [map_ofRestricted, hf₀]
  exact Subtype.ext (by simp)

/-- **Surjectivity of `washnitzerAlgebra.map` along a strict surjection.** If every `s ∈ S` lifts
along `φ` to some `r ∈ R` with `‖r‖ ≤ C' * ‖s‖`, then `R⟨X⟩† → S⟨X⟩†` is surjective. -/
theorem map_surjective {C' : ℝ} (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) :
    Function.Surjective (map (σ := σ) φ hφ) := fun g ↦
  let ⟨f, hf, _⟩ := exists_map_eq_and_norm_coeff_le φ hφ hlift g
  ⟨f, hf⟩

include hφ in
/-- **Noetherianity of `W` passes along a strict surjection.** If `φ : R →+* S` is bounded and
admits linearly bounded lifts, then `S⟨X⟩†` is noetherian whenever `R⟨X⟩†` is. -/
theorem isNoetherianRing_of_surjective {C' : ℝ}
    (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖)
    [IsNoetherianRing (washnitzerAlgebra σ R)] :
    IsNoetherianRing (washnitzerAlgebra σ S) :=
  _root_.isNoetherianRing_of_surjective _ _ (map φ hφ) (map_surjective φ hφ hlift)

end Map

/-- The identity ring homomorphism induces the identity on `R⟨X⟩†`. -/
@[simp]
theorem map_id {C : ℝ} (hC : ∀ r : R, ‖RingHom.id R r‖ ≤ C * ‖r‖) :
    map (σ := σ) (RingHom.id R) hC = RingHom.id _ :=
  RingHom.ext fun _ ↦ Subtype.ext <| MvPowerSeries.ext fun _ ↦ by simp

end washnitzerAlgebra

end TauCeti.Dagger
