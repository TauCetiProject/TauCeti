/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Map
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.BoundedEval

/-!
# Evaluating overconvergent power series on the closed unit polydisc

Let `R` and `S` be ultrametric normed commutative rings with `S` complete, and let `a : Fin k → S`
have coordinates in the closed unit ball `‖a i‖ ≤ 1`. Every overconvergent power series
`f ∈ R⟨X₁, …, X_k⟩†` restricts via `toTate` to the unit-radius Tate algebra `R{X/1}`, so it can be
evaluated at `a` along any contractive (`‖φ r‖ ≤ ‖r‖`) or `C`-bounded (`‖φ r‖ ≤ C * ‖r‖`) ring
homomorphism `φ : R →+* S`.

Evaluating on `R⟨X⟩†` factors through `toTate`, agrees on every polyradius subring `R{X/c}`
(`c > 1`) with `restrictedEval₂` / `restrictedEval₂OfBound`, and has the universal property
among continuous ring homomorphisms `R⟨X⟩† →+* S` for the unit Gauss norm topology because
polynomials are dense in `R⟨X⟩†` (`TauCeti.Dagger.washnitzerAlgebra.denseRange_ofMvPolynomial`).

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.eval₂OfBound`: evaluation `R⟨X⟩† →+* S` at arguments
  `‖a i‖ ≤ 1` along `φ : R →+* S` satisfying `∀ r, ‖φ r‖ ≤ C * ‖r‖`.
* `TauCeti.Dagger.washnitzerAlgebra.eval₂`: contractive evaluation `R⟨X⟩† →+* S` at arguments
  `‖a i‖ ≤ 1` along `φ : R →+* S` satisfying `∀ r, ‖φ r‖ ≤ ‖r‖`, defined as the `C = 1`
  specialization of `eval₂OfBound`.
* `TauCeti.Dagger.washnitzerAlgebra.aeval`: contractive `R`-algebra evaluation `R⟨X⟩† →ₐ[R] S`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.eval₂OfBound_ofRestricted` and
  `TauCeti.Dagger.washnitzerAlgebra.eval₂_ofRestricted`: agreement with evaluation on
  polyradius subrings `R{X/c}` (`c > 1`).
* `TauCeti.Dagger.washnitzerAlgebra.norm_eval₂OfBound_le` and
  `TauCeti.Dagger.washnitzerAlgebra.norm_eval₂_le`: Gauss norm bounds and continuity.
* `TauCeti.Dagger.washnitzerAlgebra.eq_eval₂OfBound`,
  `TauCeti.Dagger.washnitzerAlgebra.existsUnique_continuous_ringHom_of_bound`, and
  `TauCeti.Dagger.washnitzerAlgebra.eq_eval₂`: universal property among continuous ring
  homomorphisms out of `R⟨X⟩†`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries TauCeti.Huber
open RingHom (restrictedEval₂OfBound restrictedEval₂OfBound_apply hasSum_restrictedEval₂OfBound
  restrictedEval₂OfBound_algebraMap restrictedEval₂OfBound_X restrictedEval₂OfBound_polynomial
  restrictedEval₂OfBound_eq_restrictedEval₂ norm_restrictedEval₂OfBound_le
  restrictedEval₂OfBound_restrictedMap map_restrictedEval₂OfBound)

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

section Bounded

variable (φ : R →+* S) (a : Fin k → S) {C : ℝ}
  (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1)

/-- **Bounded evaluation of overconvergent power series.** Evaluate `R⟨X⟩†` at arguments
`‖a i‖ ≤ 1` along a coefficient homomorphism `φ : R →+* S` bounded by `C`. -/
noncomputable def eval₂OfBound : washnitzerAlgebra (Fin k) R →+* S :=
  (restrictedEval₂OfBound φ a hφ ha).comp (toTate (Fin k) R).toRingHom

/-- `eval₂OfBound` factors through `toTate` and unit-radius `restrictedEval₂OfBound`. -/
theorem eval₂OfBound_eq_restrictedEval₂OfBound_toTate (f : washnitzerAlgebra (Fin k) R) :
    eval₂OfBound φ a hφ ha f = restrictedEval₂OfBound φ a hφ ha (toTate (Fin k) R f) :=
  (rfl)

/-- Bounded evaluation on `R⟨X⟩†` is the convergent monomial sum `weightedEval φ a f`. -/
theorem eval₂OfBound_apply (f : washnitzerAlgebra (Fin k) R) :
    eval₂OfBound φ a hφ ha f = weightedEval φ a f := by
  rw [eval₂OfBound_eq_restrictedEval₂OfBound_toTate, restrictedEval₂OfBound_apply, coe_toTate]

/-- The monomial sum converges to `eval₂OfBound φ a hφ ha f`. -/
theorem hasSum_eval₂OfBound (f : washnitzerAlgebra (Fin k) R) :
    HasSum (weightedEvalTerm φ a f) (eval₂OfBound φ a hφ ha f) := by
  simpa only [eval₂OfBound_eq_restrictedEval₂OfBound_toTate, coe_toTate] using
    hasSum_restrictedEval₂OfBound φ a hφ ha (toTate (Fin k) R f)

/-- `eval₂OfBound` extends `φ` on constants. -/
@[simp]
theorem eval₂OfBound_algebraMap (r : R) :
    eval₂OfBound φ a hφ ha (algebraMap R _ r) = φ r := by
  rw [eval₂OfBound_eq_restrictedEval₂OfBound_toTate, AlgHom.commutes,
    restrictedEval₂OfBound_algebraMap]

/-- `eval₂OfBound` sends `X i` to `a i`. -/
@[simp]
theorem eval₂OfBound_X (i : Fin k) :
    eval₂OfBound φ a hφ ha (X (Fin k) R i) = a i := by
  have h : toTate (Fin k) R (X (Fin k) R i) = ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ :=
    Subtype.ext (by simp)
  rw [eval₂OfBound_eq_restrictedEval₂OfBound_toTate, h, restrictedEval₂OfBound_X]

/-- `eval₂OfBound` extends polynomial evaluation `MvPolynomial.eval₂`. -/
@[simp]
theorem eval₂OfBound_ofMvPolynomial (p : MvPolynomial (Fin k) R) :
    eval₂OfBound φ a hφ ha (ofMvPolynomial (Fin k) R p) = MvPolynomial.eval₂ φ a p := by
  have h : toTate (Fin k) R (ofMvPolynomial (Fin k) R p) =
      TauCeti.MvPowerSeries.polynomialToRestricted (fun _ ↦ 1) p := Subtype.ext (by simp)
  rw [eval₂OfBound_eq_restrictedEval₂OfBound_toTate, h, restrictedEval₂OfBound_polynomial]

/-- Evaluating a series included via `ofRestricted` agrees with `restrictedEval₂OfBound` at that
polyradius. -/
@[simp]
theorem eval₂OfBound_ofRestricted {c : Fin k → ℝ} {ρ : ℝ} (hρ : 1 < ρ) (hc : ∀ i, ρ ≤ c i)
    (f : IsRestricted.subring (R := R) c) :
    eval₂OfBound φ a hφ ha (ofRestricted hρ hc f) =
      restrictedEval₂OfBound φ a hφ (fun i ↦ (ha i).trans (hρ.le.trans (hc i))) f := by
  rw [eval₂OfBound_apply, restrictedEval₂OfBound_apply, coe_ofRestricted]

/-- Evaluating a series included via `ofOneLt` agrees with `restrictedEval₂OfBound` at that
polyradius. -/
@[simp]
theorem eval₂OfBound_ofOneLt {c : Fin k → ℝ} (hc : ∀ i, 1 < c i)
    (f : IsRestricted.subring (R := R) c) :
    eval₂OfBound φ a hφ ha (ofOneLt hc f) =
      restrictedEval₂OfBound φ a hφ (fun i ↦ (ha i).trans (hc i).le) f := by
  rw [eval₂OfBound_apply, restrictedEval₂OfBound_apply, coe_ofOneLt]

/-- `eval₂OfBound` increases the unit Gauss norm by at most `C`. -/
theorem norm_eval₂OfBound_le (f : washnitzerAlgebra (Fin k) R) :
    ‖eval₂OfBound φ a hφ ha f‖ ≤ C * ‖f‖ := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  rw [eval₂OfBound_eq_restrictedEval₂OfBound_toTate, ← norm_toTate]
  exact norm_restrictedEval₂OfBound_le φ a hφ ha (toTate (Fin k) R f)

/-- `eval₂OfBound` is Lipschitz with constant `C` for the unit Gauss norm. -/
theorem lipschitzWith_eval₂OfBound :
    LipschitzWith (Real.toNNReal C) (eval₂OfBound φ a hφ ha) :=
  AddMonoidHomClass.lipschitz_of_bound _ C (norm_eval₂OfBound_le φ a hφ ha)

/-- `eval₂OfBound` is continuous for the unit Gauss norm topology. -/
@[continuity]
theorem continuous_eval₂OfBound : Continuous (eval₂OfBound φ a hφ ha) :=
  (lipschitzWith_eval₂OfBound φ a hφ ha).continuous

/-- A continuous ring homomorphism out of `R⟨X⟩†` with the prescribed values on constants and
variables equals `eval₂OfBound φ a hφ ha`. -/
theorem eq_eval₂OfBound (ψ : washnitzerAlgebra (Fin k) R →+* S) (hψ : Continuous ψ)
    (hC : ∀ r, ψ (algebraMap R _ r) = φ r) (hX : ∀ i, ψ (X (Fin k) R i) = a i) :
    ψ = eval₂OfBound φ a hφ ha := by
  have hp : ψ.comp (ofMvPolynomial (Fin k) R).toRingHom =
      (eval₂OfBound φ a hφ ha).comp (ofMvPolynomial (Fin k) R).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [← MvPolynomial.algebraMap_eq, hC]
    · intro i
      simpa using (hX i).trans (eval₂OfBound_X φ a hφ ha i).symm
  exact DFunLike.coe_injective (denseRange_ofMvPolynomial.equalizer hψ
    (continuous_eval₂OfBound φ a hφ ha) (funext (DFunLike.congr_fun hp)))

include hφ ha in
/-- **Universal property of `R⟨X⟩†` for bounded coefficient maps.** -/
theorem existsUnique_continuous_ringHom_of_bound :
    ∃! ψ : washnitzerAlgebra (Fin k) R →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧ ∀ i, ψ (X (Fin k) R i) = a i :=
  ⟨eval₂OfBound φ a hφ ha,
    ⟨continuous_eval₂OfBound φ a hφ ha, eval₂OfBound_algebraMap φ a hφ ha,
      eval₂OfBound_X φ a hφ ha⟩,
    fun ψ ⟨hψ, hC, hX⟩ ↦ eq_eval₂OfBound φ a hφ ha ψ hψ hC hX⟩

/-- `eval₂OfBound` commutes with `washnitzerAlgebra.map` on source coefficients. -/
theorem eval₂OfBound_map {T : Type*} [NormedCommRing T] [IsUltrametricDist T]
    (θ : T →+* R) {D E : ℝ} (hθ : ∀ t, ‖θ t‖ ≤ D * ‖t‖)
    (hφθ : ∀ t, ‖(φ.comp θ) t‖ ≤ E * ‖t‖) (f : washnitzerAlgebra (Fin k) T) :
    eval₂OfBound φ a hφ ha (map θ hθ f) = eval₂OfBound (φ.comp θ) a hφθ ha f := by
  rw [eval₂OfBound_eq_restrictedEval₂OfBound_toTate, toTate_map,
    restrictedEval₂OfBound_restrictedMap φ a hφ ha θ hθ hφθ,
    ← eval₂OfBound_eq_restrictedEval₂OfBound_toTate]

/-- Applying a continuous ring homomorphism of complete ultrametric target rings commutes with
`eval₂OfBound`. -/
theorem map_eval₂OfBound {T : Type*} [NormedCommRing T] [IsUltrametricDist T] [CompleteSpace T]
    (θ : S →+* T) (hθ : Continuous θ) {D : ℝ}
    (hθφ : ∀ r, ‖(θ.comp φ) r‖ ≤ D * ‖r‖) (hθa : ∀ i, ‖θ (a i)‖ ≤ 1)
    (f : washnitzerAlgebra (Fin k) R) :
    θ (eval₂OfBound φ a hφ ha f) = eval₂OfBound (θ.comp φ) (θ ∘ a) hθφ hθa f :=
  map_restrictedEval₂OfBound φ a hφ ha θ hθ hθφ hθa (toTate (Fin k) R f)

end Bounded

section Contractive

variable (φ : R →+* S) (a : Fin k → S) (hφ : ∀ r, ‖φ r‖ ≤ ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1)

/-- **Contractive evaluation of overconvergent power series.** For `φ : R →+* S` nonincreasing for
the norms and arguments `a i` in the closed unit ball of a complete ultrametric normed commutative
ring `S`, the ring homomorphism `R⟨X⟩† →+* S` sending `f` to `∑ₜ φ(fₜ) aᵗ`, defined as the `C = 1`
specialization of `eval₂OfBound`. -/
noncomputable def eval₂ : washnitzerAlgebra (Fin k) R →+* S :=
  eval₂OfBound (C := 1) φ a (fun r ↦ (hφ r).trans_eq (one_mul _).symm) ha

/-- `eval₂` factors through `toTate` and unit-radius `restrictedEval₂`. -/
theorem eval₂_eq_restrictedEval₂_toTate (f : washnitzerAlgebra (Fin k) R) :
    eval₂ φ a hφ ha f = restrictedEval₂ φ a hφ ha (toTate (Fin k) R f) := by
  rw [eval₂, eval₂OfBound_eq_restrictedEval₂OfBound_toTate,
    restrictedEval₂OfBound_eq_restrictedEval₂ _ _ _ _ hφ]

/-- `eval₂` is the weighted monomial sum `TauCeti.Huber.weightedEval φ a f`. -/
theorem eval₂_apply (f : washnitzerAlgebra (Fin k) R) :
    eval₂ φ a hφ ha f = weightedEval φ a f :=
  eval₂OfBound_apply φ a _ ha f

/-- The monomial values `φ(fₜ) aᵗ` sum to `eval₂ φ a hφ ha f`. -/
theorem hasSum_eval₂ (f : washnitzerAlgebra (Fin k) R) :
    HasSum (weightedEvalTerm φ a f) (eval₂ φ a hφ ha f) :=
  hasSum_eval₂OfBound φ a _ ha f

/-- `eval₂` extends `φ` on constants. -/
@[simp]
theorem eval₂_algebraMap (r : R) :
    eval₂ φ a hφ ha (algebraMap R _ r) = φ r :=
  eval₂OfBound_algebraMap φ a _ ha r

/-- `eval₂` sends the variable `X i` to `a i`. -/
@[simp]
theorem eval₂_X (i : Fin k) :
    eval₂ φ a hφ ha (X (Fin k) R i) = a i :=
  eval₂OfBound_X φ a _ ha i

/-- `eval₂` extends polynomial evaluation `MvPolynomial.eval₂`. -/
@[simp]
theorem eval₂_ofMvPolynomial (p : MvPolynomial (Fin k) R) :
    eval₂ φ a hφ ha (ofMvPolynomial (Fin k) R p) = MvPolynomial.eval₂ φ a p :=
  eval₂OfBound_ofMvPolynomial φ a _ ha p

/-- Evaluating a series included via `ofRestricted` agrees with `restrictedEval₂` at that
polyradius. -/
@[simp]
theorem eval₂_ofRestricted {c : Fin k → ℝ} {ρ : ℝ} (hρ : 1 < ρ) (hc : ∀ i, ρ ≤ c i)
    (f : IsRestricted.subring (R := R) c) :
    eval₂ φ a hφ ha (ofRestricted hρ hc f) =
      restrictedEval₂ φ a hφ (fun i ↦ (ha i).trans (hρ.le.trans (hc i))) f := by
  rw [eval₂, eval₂OfBound_ofRestricted, restrictedEval₂OfBound_eq_restrictedEval₂ _ _ _ _ hφ]

/-- Evaluating a series included via `ofOneLt` agrees with `restrictedEval₂` at that polyradius. -/
@[simp]
theorem eval₂_ofOneLt {c : Fin k → ℝ} (hc : ∀ i, 1 < c i)
    (f : IsRestricted.subring (R := R) c) :
    eval₂ φ a hφ ha (ofOneLt hc f) =
      restrictedEval₂ φ a hφ (fun i ↦ (ha i).trans (hc i).le) f := by
  rw [eval₂, eval₂OfBound_ofOneLt, restrictedEval₂OfBound_eq_restrictedEval₂ _ _ _ _ hφ]

/-- **Contractive evaluation does not increase the unit Gauss norm**: `‖f(a)‖ ≤ ‖f‖`. -/
theorem norm_eval₂_le (f : washnitzerAlgebra (Fin k) R) :
    ‖eval₂ φ a hφ ha f‖ ≤ ‖f‖ := by
  simpa only [eval₂, one_mul] using
    norm_eval₂OfBound_le (C := 1) φ a (fun r ↦ (hφ r).trans_eq (one_mul _).symm) ha f

/-- `eval₂` is `1`-Lipschitz for the unit Gauss norm. -/
theorem lipschitzWith_eval₂ : LipschitzWith 1 (eval₂ φ a hφ ha) := by
  simpa only [eval₂, Real.toNNReal_one] using
    lipschitzWith_eval₂OfBound (C := 1) φ a (fun r ↦ (hφ r).trans_eq (one_mul _).symm) ha

/-- `eval₂` is continuous for the unit Gauss norm topology. -/
@[continuity]
theorem continuous_eval₂ : Continuous (eval₂ φ a hφ ha) :=
  continuous_eval₂OfBound φ a _ ha

/-- **Uniqueness of continuous evaluation on `R⟨X⟩†`.** A continuous ring homomorphism out of
`R⟨X⟩†` extending `φ` on constants and sending each `X i` to `a i` is `eval₂ φ a hφ ha`. -/
theorem eq_eval₂ (ψ : washnitzerAlgebra (Fin k) R →+* S) (hψ : Continuous ψ)
    (hC : ∀ r, ψ (algebraMap R _ r) = φ r) (hX : ∀ i, ψ (X (Fin k) R i) = a i) :
    ψ = eval₂ φ a hφ ha :=
  eq_eval₂OfBound φ a _ ha ψ hψ hC hX

include hφ ha in
/-- **Universal property of `R⟨X⟩†` for contractive coefficient maps.** -/
theorem existsUnique_continuous_ringHom :
    ∃! ψ : washnitzerAlgebra (Fin k) R →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧ ∀ i, ψ (X (Fin k) R i) = a i :=
  existsUnique_continuous_ringHom_of_bound φ a (fun r ↦ (hφ r).trans_eq (one_mul _).symm) ha

end Contractive

/-- `eval₂OfBound` agrees with contractive `eval₂` whenever `φ` is norm-nonincreasing. -/
theorem eval₂OfBound_eq_eval₂ (φ : R →+* S) (a : Fin k → S) {C : ℝ}
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (ha : ∀ i, ‖a i‖ ≤ 1) (hφ' : ∀ r, ‖φ r‖ ≤ ‖r‖) :
    eval₂OfBound φ a hφ ha = eval₂ φ a hφ' ha :=
  eq_eval₂ φ a hφ' ha _ (continuous_eval₂OfBound φ a hφ ha)
    (eval₂OfBound_algebraMap φ a hφ ha) (eval₂OfBound_X φ a hφ ha)

section Aeval

variable [Algebra R S] (halg : ∀ r : R, ‖algebraMap R S r‖ ≤ ‖r‖)
  (a : Fin k → S) (ha : ∀ i, ‖a i‖ ≤ 1)

/-- **Contractive `R`-algebra evaluation of overconvergent power series** at arguments in the
closed unit ball of `S`. -/
noncomputable def aeval : washnitzerAlgebra (Fin k) R →ₐ[R] S where
  __ := eval₂ (algebraMap R S) a halg ha
  commutes' := eval₂_algebraMap (algebraMap R S) a halg ha

/-- `aeval` has underlying ring homomorphism `eval₂ (algebraMap R S) a halg ha`. -/
@[simp]
theorem coe_aeval :
    (aeval halg a ha : washnitzerAlgebra (Fin k) R →+* S) = eval₂ (algebraMap R S) a halg ha :=
  (rfl)

/-- `aeval` agrees with `eval₂ (algebraMap R S)` on every overconvergent series. -/
theorem aeval_apply (f : washnitzerAlgebra (Fin k) R) :
    aeval halg a ha f = eval₂ (algebraMap R S) a halg ha f :=
  (rfl)

/-- `aeval` sends `X i` to `a i`. -/
@[simp]
theorem aeval_X (i : Fin k) : aeval halg a ha (X (Fin k) R i) = a i :=
  eval₂_X (algebraMap R S) a halg ha i

/-- `aeval` extends `MvPolynomial.aeval`. -/
@[simp]
theorem aeval_ofMvPolynomial (p : MvPolynomial (Fin k) R) :
    aeval halg a ha (ofMvPolynomial (Fin k) R p) = MvPolynomial.aeval a p := by
  rw [aeval_apply, eval₂_ofMvPolynomial, MvPolynomial.aeval_def]

/-- `aeval` does not increase the unit Gauss norm. -/
theorem norm_aeval_le (f : washnitzerAlgebra (Fin k) R) :
    ‖aeval halg a ha f‖ ≤ ‖f‖ :=
  norm_eval₂_le (algebraMap R S) a halg ha f

/-- `aeval` is continuous for the unit Gauss norm topology. -/
@[continuity]
theorem continuous_aeval : Continuous (aeval halg a ha) :=
  continuous_eval₂ (algebraMap R S) a halg ha

/-- Any continuous `R`-algebra homomorphism `R⟨X⟩† →ₐ[R] S` sending `X i` to `a i` equals
`aeval halg a ha`. -/
theorem eq_aeval (ψ : washnitzerAlgebra (Fin k) R →ₐ[R] S) (hψ : Continuous ψ)
    (hX : ∀ i, ψ (X (Fin k) R i) = a i) : ψ = aeval halg a ha :=
  AlgHom.toRingHom_injective (eq_eval₂ (algebraMap R S) a halg ha ψ.toRingHom hψ ψ.commutes hX)

end Aeval

end TauCeti.Dagger.washnitzerAlgebra
