/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Eval
public import TauCeti.RingTheory.PowerSeries.Entire.Topology
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval

/-!
# Univariate overconvergent series and comparisons with entire and open-disc series

In one variable `Unit`, `MvPowerSeries Unit R` is definitionally `PowerSeries R` and
`MvPowerSeries.IsRestricted (fun _ : Unit ↦ ρ)` is `PowerSeries.IsRestricted ρ`. Over an
ultrametric normed commutative ring `R`, the univariate Monsky–Washnitzer algebra
`TauCeti.Dagger.washnitzerAlgebra Unit R` therefore sits in the chain of power-series subrings

```text
IsEntire.subring R ≤ (washnitzerAlgebra Unit R).toSubring
  ≤ IsRestricted.subring 1 ≤ OnOpenDisc.subring R 1 ≤ R⟦X⟧,
```

and a series is overconvergent iff it lies on the open disc of some radius `R₀ > 1`. Each
inclusion in this chain is uniformly continuous for the respective Gauss topologies (all positive
radii on entire series, the unit Gauss norm on overconvergent series, and all radii in `(0, 1)` on
the open unit disc), and all four algebras share `PowerSeries.evalAt` on the closed or open unit
disc.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.ofEntire`: inclusion of entire series into `R⟨X⟩†`.
* `TauCeti.Dagger.washnitzerAlgebra.ofOnOpenDisc`: inclusion of series on an open disc of radius
  `R₀ > 1` into `R⟨X⟩†`.
* `TauCeti.Dagger.washnitzerAlgebra.toOnOpenDiscOne`: inclusion of `R⟨X⟩†` into series on the open
  unit disc.
* `TauCeti.Dagger.washnitzerAlgebra.evalAtHom`: evaluation of `R⟨X⟩†` at `b` with `‖b‖ ≤ 1` in any
  complete ultrametric normed `R`-algebra (not necessarily commutative).

## Main results

* `TauCeti.Dagger.mem_washnitzerAlgebra_unit_iff` and
  `TauCeti.Dagger.mem_washnitzerAlgebra_unit_iff_exists_onOpenDisc`: univariate overconvergence
  via restrictedness at `ρ > 1` or analyticity on an open disc of radius `R₀ > 1`.
* `PowerSeries.IsEntire.mem_washnitzerAlgebra`, `PowerSeries.OnOpenDisc.mem_washnitzerAlgebra`,
  and `TauCeti.Dagger.onOpenDisc_one_of_mem_washnitzerAlgebra`: membership comparisons.
* `TauCeti.Dagger.mk_pow_mem_washnitzerAlgebra`: for `‖a‖ < 1`, the geometric series `∑ aⁿ Xⁿ` is
  overconvergent.
* `TauCeti.Dagger.washnitzerAlgebra.norm_unit_eq_gaussNorm`: the norm on `washnitzerAlgebra Unit R`
  is `PowerSeries.gaussNorm norm 1`.
* `TauCeti.Dagger.washnitzerAlgebra.uniformContinuous_ofEntire`,
  `TauCeti.Dagger.washnitzerAlgebra.uniformContinuous_ofOnOpenDisc`, and
  `TauCeti.Dagger.washnitzerAlgebra.uniformContinuous_toOnOpenDiscOne`: compatibility of the
  distinct Gauss topologies.
* `TauCeti.Dagger.washnitzerAlgebra.evalAtHom_comp_ofEntire`,
  `TauCeti.Dagger.washnitzerAlgebra.evalAtHom_comp_ofOnOpenDisc`,
  `TauCeti.Dagger.washnitzerAlgebra.onOpenDiscEvalAtHom_comp_toOnOpenDiscOne`, and
  `TauCeti.Dagger.washnitzerAlgebra.aeval_renameAlgEquiv_unit`: compatibility of evaluations.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.
-/

public section

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ} {f : R⟦X⟧}

/-- A power series on an open disc of radius `R₀ > 1` is overconvergent: it is restricted at any
radius strictly between `1` and `R₀`. -/
theorem OnOpenDisc.mem_washnitzerAlgebra (hf : f.OnOpenDisc R₀) (hR₀ : 1 < R₀) :
    f ∈ TauCeti.Dagger.washnitzerAlgebra Unit R := by
  obtain ⟨ρ, h1, hρR⟩ := exists_between hR₀
  exact TauCeti.Dagger.mem_washnitzerAlgebra.mpr
    ⟨ρ, h1, (onOpenDisc_iff.mp hf) ρ (zero_lt_one.trans h1) hρR⟩

/-- Every entire power series is overconvergent. -/
theorem IsEntire.mem_washnitzerAlgebra (hf : f.IsEntire) :
    f ∈ TauCeti.Dagger.washnitzerAlgebra Unit R :=
  (hf.onOpenDisc 2).mem_washnitzerAlgebra one_lt_two

end PowerSeries

namespace TauCeti.Dagger

open Filter Topology _root_.PowerSeries

section Membership

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ} {f : R⟦X⟧}

/-- A one-variable power series belongs to `washnitzerAlgebra Unit R` iff it is restricted at some
radius `ρ > 1`. -/
theorem mem_washnitzerAlgebra_unit_iff :
    f ∈ washnitzerAlgebra Unit R ↔ ∃ ρ > (1 : ℝ), f.IsRestricted ρ :=
  mem_washnitzerAlgebra

/-- **Open-disc characterisation of univariate overconvergence.** A one-variable power series is
overconvergent iff it lies on the open disc of some radius `R₀ > 1`. -/
theorem mem_washnitzerAlgebra_unit_iff_exists_onOpenDisc :
    f ∈ washnitzerAlgebra Unit R ↔ ∃ R₀ > (1 : ℝ), f.OnOpenDisc R₀ :=
  ⟨fun hf ↦ by
    obtain ⟨ρ, hρ, hfρ⟩ := mem_washnitzerAlgebra_unit_iff.mp hf
    exact ⟨ρ, hρ, IsRestricted.onOpenDisc hfρ⟩,
   fun ⟨_, hR₀, hf⟩ ↦ hf.mem_washnitzerAlgebra hR₀⟩

/-- Every univariate overconvergent series lies on the open unit disc. -/
theorem onOpenDisc_one_of_mem_washnitzerAlgebra (hf : f ∈ washnitzerAlgebra Unit R) :
    f.OnOpenDisc 1 :=
  IsRestricted.onOpenDisc (isRestricted_of_mem_washnitzerAlgebra hf zero_le_one le_rfl)

/-- For `‖a‖ < 1`, the geometric series `∑ aⁿ Xⁿ` is overconvergent. -/
theorem mk_pow_mem_washnitzerAlgebra {a : R} (ha : ‖a‖ < 1) :
    (PowerSeries.mk fun n ↦ a ^ n) ∈ washnitzerAlgebra Unit R := by
  rcases eq_or_ne a 0 with rfl | ha0
  · convert (washnitzerAlgebra Unit R).one_mem
    ext (_ | n) <;> simp
  · exact (onOpenDisc_mk_pow a).mem_washnitzerAlgebra
      (one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr ha0, ha⟩)

/-- The subring of entire series lies in the univariate Monsky–Washnitzer algebra. -/
theorem isEntireSubring_le_washnitzerAlgebra :
    IsEntire.subring R ≤ (washnitzerAlgebra Unit R).toSubring :=
  fun _ hf ↦ (IsEntire.mem_subring.mp hf).mem_washnitzerAlgebra

/-- For `1 < R₀`, the subring of series on the open disc of radius `R₀` lies in the univariate
Monsky–Washnitzer algebra. -/
theorem onOpenDiscSubring_le_washnitzerAlgebra (hR₀ : 1 < R₀) :
    OnOpenDisc.subring R R₀ ≤ (washnitzerAlgebra Unit R).toSubring :=
  fun _ hf ↦ (OnOpenDisc.mem_subring.mp hf).mem_washnitzerAlgebra hR₀

/-- The univariate Monsky–Washnitzer algebra lies in the subring of series on the open unit disc. -/
theorem washnitzerAlgebra_unit_toSubring_le_onOpenDisc :
    (washnitzerAlgebra Unit R).toSubring ≤ OnOpenDisc.subring R 1 :=
  fun _ hf ↦ OnOpenDisc.mem_subring.mpr (onOpenDisc_one_of_mem_washnitzerAlgebra hf)

end Membership

namespace washnitzerAlgebra

section Inclusions

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {R₀ : ℝ}

local instance (r : Set.Ioo (0 : ℝ) 1) : Fact (0 < (r : ℝ)) := ⟨r.property.1⟩

/-- The unit Gauss norm on `washnitzerAlgebra Unit R` agrees with the univariate unit Gauss norm
`PowerSeries.gaussNorm norm 1`. -/
theorem norm_unit_eq_gaussNorm (f : washnitzerAlgebra Unit R) :
    ‖f‖ = PowerSeries.gaussNorm norm 1 (f : R⟦X⟧) :=
  norm_eq_gaussNorm f

/-- The ring homomorphism including entire series into `R⟨X⟩†`. -/
noncomputable def ofEntire : IsEntire.subring R →+* washnitzerAlgebra Unit R :=
  Subring.inclusion isEntireSubring_le_washnitzerAlgebra

/-- `ofEntire` leaves the underlying formal power series unchanged. -/
@[simp]
theorem coe_ofEntire (f : IsEntire.subring R) :
    (ofEntire f : R⟦X⟧) = f :=
  (rfl)

/-- `ofEntire` is injective. -/
theorem ofEntire_injective : Function.Injective (ofEntire (R := R)) :=
  fun _ _ h ↦ Subtype.ext (congrArg (fun g : washnitzerAlgebra Unit R ↦ (g : R⟦X⟧)) h)

/-- `ofEntire` commutes with polynomial inclusions. -/
@[simp]
theorem ofEntire_polynomialHom (p : Polynomial R) :
    ofEntire (IsEntire.polynomialHom p) = ofPolynomial R p :=
  Subtype.ext (by simp)

/-- On an entire series, the unit Gauss norm in `R⟨X⟩†` equals the norm of its unit-disc
restriction. -/
theorem norm_ofEntire (f : IsEntire.subring R) :
    ‖ofEntire f‖ = ‖TauCeti.PowerSeries.IsEntire.restrict ⟨1, zero_lt_one⟩ f‖ := by
  rw [norm_unit_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm,
    TauCeti.PowerSeries.IsEntire.coe_restrict, coe_ofEntire]

/-- The inclusion of entire series into `R⟨X⟩†` is uniformly continuous from the family of all
positive-radius Gauss norms to the unit Gauss norm. -/
theorem uniformContinuous_ofEntire : UniformContinuous (ofEntire (R := R)) := by
  refine uniformContinuous_of_continuousAt_zero (ofEntire (R := R)) ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  have h := (TauCeti.PowerSeries.IsEntire.uniformContinuous_restrict
    (R := R) ⟨1, zero_lt_one⟩).continuous.tendsto 0
  rw [map_zero, tendsto_zero_iff_norm_tendsto_zero] at h
  simpa only [norm_ofEntire] using h

/-- The inclusion of entire series into `R⟨X⟩†` is continuous. -/
@[continuity]
theorem continuous_ofEntire : Continuous (ofEntire (R := R)) :=
  uniformContinuous_ofEntire.continuous

/-- For `1 < R₀`, the ring homomorphism including series on the open disc of radius `R₀` into
`R⟨X⟩†`. -/
noncomputable def ofOnOpenDisc (hR₀ : 1 < R₀) :
    OnOpenDisc.subring R R₀ →+* washnitzerAlgebra Unit R :=
  Subring.inclusion (onOpenDiscSubring_le_washnitzerAlgebra hR₀)

/-- `ofOnOpenDisc` leaves the underlying formal power series unchanged. -/
@[simp]
theorem coe_ofOnOpenDisc (hR₀ : 1 < R₀) (f : OnOpenDisc.subring R R₀) :
    (ofOnOpenDisc hR₀ f : R⟦X⟧) = f :=
  (rfl)

/-- `ofOnOpenDisc` is injective. -/
theorem ofOnOpenDisc_injective (hR₀ : 1 < R₀) : Function.Injective (ofOnOpenDisc (R := R) hR₀) :=
  fun _ _ h ↦ Subtype.ext (congrArg (fun g : washnitzerAlgebra Unit R ↦ (g : R⟦X⟧)) h)

/-- `ofOnOpenDisc` commutes with polynomial inclusions. -/
@[simp]
theorem ofOnOpenDisc_polynomialHom (hR₀ : 1 < R₀) (p : Polynomial R) :
    ofOnOpenDisc hR₀ (OnOpenDisc.polynomialHom p) = ofPolynomial R p :=
  Subtype.ext (by simp)

/-- On a series on the open disc of radius `R₀ > 1`, the unit Gauss norm in `R⟨X⟩†` equals the norm
of its unit-disc restriction. -/
theorem norm_ofOnOpenDisc (hR₀ : 1 < R₀) (f : OnOpenDisc.subring R R₀) :
    ‖ofOnOpenDisc hR₀ f‖ =
      ‖TauCeti.PowerSeries.OnOpenDisc.restrict ⟨1, zero_lt_one, hR₀⟩ f‖ := by
  rw [norm_unit_eq_gaussNorm, TauCeti.PowerSeries.norm_eq_gaussNorm,
    TauCeti.PowerSeries.OnOpenDisc.coe_restrict, coe_ofOnOpenDisc]

/-- For `1 < R₀`, the inclusion of series on the open disc of radius `R₀` into `R⟨X⟩†` is uniformly
continuous from the open-disc Gauss topology to the unit Gauss norm. -/
theorem uniformContinuous_ofOnOpenDisc (hR₀ : 1 < R₀) :
    UniformContinuous (ofOnOpenDisc (R := R) hR₀) := by
  refine uniformContinuous_of_continuousAt_zero (ofOnOpenDisc (R := R) hR₀) ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  have h := (TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_restrict
    (R := R) ⟨1, zero_lt_one, hR₀⟩).continuous.tendsto 0
  rw [map_zero, tendsto_zero_iff_norm_tendsto_zero] at h
  simpa only [norm_ofOnOpenDisc hR₀] using h

/-- For `1 < R₀`, the inclusion of series on the open disc of radius `R₀` into `R⟨X⟩†` is
continuous. -/
@[continuity]
theorem continuous_ofOnOpenDisc (hR₀ : 1 < R₀) : Continuous (ofOnOpenDisc (R := R) hR₀) :=
  (uniformContinuous_ofOnOpenDisc hR₀).continuous

/-- The ring homomorphism including `R⟨X⟩†` into series on the open unit disc. -/
noncomputable def toOnOpenDiscOne : washnitzerAlgebra Unit R →+* OnOpenDisc.subring R 1 :=
  Subring.inclusion washnitzerAlgebra_unit_toSubring_le_onOpenDisc

/-- `toOnOpenDiscOne` leaves the underlying formal power series unchanged. -/
@[simp]
theorem coe_toOnOpenDiscOne (f : washnitzerAlgebra Unit R) :
    (toOnOpenDiscOne f : R⟦X⟧) = f :=
  (rfl)

/-- `toOnOpenDiscOne` is injective. -/
theorem toOnOpenDiscOne_injective : Function.Injective (toOnOpenDiscOne (R := R)) :=
  fun _ _ h ↦ Subtype.ext (congrArg (fun g : OnOpenDisc.subring R 1 ↦ (g : R⟦X⟧)) h)

/-- `toOnOpenDiscOne` commutes with polynomial inclusions. -/
@[simp]
theorem toOnOpenDiscOne_ofPolynomial (p : Polynomial R) :
    toOnOpenDiscOne (ofPolynomial R p) = OnOpenDisc.polynomialHom p :=
  Subtype.ext (by simp)

/-- The inclusion of `R⟨X⟩†` into series on the open unit disc is uniformly continuous from the unit
Gauss norm to the open-disc Gauss topology. -/
theorem uniformContinuous_toOnOpenDiscOne : UniformContinuous (toOnOpenDiscOne (R := R)) := by
  refine TauCeti.PowerSeries.OnOpenDisc.uniformContinuous_iff.mpr fun r ↦ ?_
  refine AddMonoidHomClass.uniformContinuous_of_bound
    ((TauCeti.PowerSeries.OnOpenDisc.restrict r).toAddMonoidHom.comp
      (toOnOpenDiscOne (R := R)).toAddMonoidHom) 1 fun f ↦ ?_
  rw [one_mul, TauCeti.PowerSeries.norm_eq_gaussNorm, norm_unit_eq_gaussNorm]
  simpa only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass,
    Function.comp_apply, TauCeti.PowerSeries.OnOpenDisc.coe_restrict, coe_toOnOpenDiscOne] using
    TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) r.property.1.le
      r.property.2.le
      (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
        (isRestricted_of_mem_washnitzerAlgebra f.property zero_le_one le_rfl))

/-- The inclusion of `R⟨X⟩†` into series on the open unit disc is continuous. -/
@[continuity]
theorem continuous_toOnOpenDiscOne : Continuous (toOnOpenDiscOne (R := R)) :=
  uniformContinuous_toOnOpenDiscOne.continuous

end Inclusions

section EvalAt

variable {R A : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedRing A] [IsUltrametricDist A] [Algebra R A] [IsBoundedSMul R A] [CompleteSpace A]
  {R₀ : ℝ} {b : A}

/-- **Evaluation of univariate overconvergent series at `b`**, for `‖b‖ ≤ 1` in any complete
ultrametric normed `R`-algebra `A` (not necessarily commutative), via `PowerSeries.evalAt`. -/
noncomputable def evalAtHom (hb : ‖b‖ ≤ 1) : washnitzerAlgebra Unit R →+* A :=
  (IsRestricted.evalAtHom R hb).comp
    (Subring.inclusion (S := (washnitzerAlgebra Unit R).toSubring) (T := IsRestricted.subring 1)
      fun _ hf ↦ isRestricted_of_mem_washnitzerAlgebra hf zero_le_one le_rfl)

/-- `evalAtHom` evaluates the underlying formal power series at `b`. -/
@[simp]
theorem evalAtHom_apply (hb : ‖b‖ ≤ 1) (f : washnitzerAlgebra Unit R) :
    evalAtHom hb f = PowerSeries.evalAt (f : R⟦X⟧) b := by
  rw [evalAtHom, RingHom.comp_apply, IsRestricted.evalAtHom_apply]
  rfl

/-- On polynomials, `evalAtHom` agrees with `Polynomial.aeval`. -/
theorem evalAtHom_ofPolynomial (hb : ‖b‖ ≤ 1) (p : Polynomial R) :
    evalAtHom hb (ofPolynomial R p) = Polynomial.aeval b p := by
  rw [evalAtHom_apply, coe_ofPolynomial, PowerSeries.evalAt_coe]

/-- `evalAtHom` sends the variable `X` to `b`. -/
theorem evalAtHom_X (hb : ‖b‖ ≤ 1) :
    evalAtHom hb (X Unit R ()) = b := by
  rw [← ofPolynomial_X, evalAtHom_ofPolynomial, Polynomial.aeval_X]

/-- On entire series, `evalAtHom` agrees with `PowerSeries.IsEntire.evalAtHom`. -/
theorem evalAtHom_comp_ofEntire (hb : ‖b‖ ≤ 1) :
    (evalAtHom hb).comp (ofEntire (R := R)) = IsEntire.evalAtHom R b := by
  ext f
  simp

/-- On series analytic on an open disc of radius `R₀ > 1`, `evalAtHom` at `‖b‖ ≤ 1` agrees with
`PowerSeries.OnOpenDisc.evalAtHom`. -/
theorem evalAtHom_comp_ofOnOpenDisc (hR₀ : 1 < R₀) (hb : ‖b‖ ≤ 1) :
    (evalAtHom hb).comp (ofOnOpenDisc (R := R) hR₀) = OnOpenDisc.evalAtHom R (hb.trans_lt hR₀) := by
  ext f
  simp

/-- At points `‖b‖ < 1` of the open unit disc, evaluating an overconvergent series through
`toOnOpenDiscOne` agrees with `evalAtHom`. -/
theorem onOpenDiscEvalAtHom_comp_toOnOpenDiscOne (hb : ‖b‖ < 1) :
    (OnOpenDisc.evalAtHom R hb).comp (toOnOpenDiscOne (R := R)) = evalAtHom hb.le := by
  ext f
  simp

omit [CompleteSpace A] in
/-- Value bound for `PowerSeries.evalAt` on `R⟨X⟩†`: in an ultrametric normed `R`-algebra,
`‖f(b)‖ ≤ ‖(1 : A)‖ * ‖f‖` for `‖b‖ ≤ 1`. -/
theorem norm_evalAt_le_mul_norm (hb : ‖b‖ ≤ 1) (f : washnitzerAlgebra Unit R) :
    ‖PowerSeries.evalAt (f : R⟦X⟧) b‖ ≤ ‖(1 : A)‖ * ‖f‖ := by
  have halg (r : R) : ‖algebraMap R A r‖ ≤ ‖(1 : A)‖ * ‖r‖ := by
    rw [Algebra.algebraMap_eq_smul_one, mul_comm]
    exact norm_smul_le r (1 : A)
  rw [norm_unit_eq_gaussNorm]
  exact norm_evalAt_le_mul_gaussNorm_of_norm_algebraMap_le
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
      (isRestricted_of_mem_washnitzerAlgebra f.property zero_le_one le_rfl)) halg hb

omit [IsBoundedSMul R A] [CompleteSpace A] in
/-- In an ultrametric normed `R`-algebra with contractive `algebraMap`, `‖f(b)‖ ≤ ‖f‖` for
`‖b‖ ≤ 1`. -/
theorem norm_evalAt_le_of_norm_algebraMap_le (halg : ∀ r : R, ‖algebraMap R A r‖ ≤ ‖r‖)
    (hb : ‖b‖ ≤ 1) (f : washnitzerAlgebra Unit R) :
    ‖PowerSeries.evalAt (f : R⟦X⟧) b‖ ≤ ‖f‖ := by
  rw [norm_unit_eq_gaussNorm]
  exact norm_evalAt_le_gaussNorm_of_norm_algebraMap_le
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
      (isRestricted_of_mem_washnitzerAlgebra f.property zero_le_one le_rfl)) halg hb

/-- `evalAtHom` is continuous for the unit Gauss norm topology on `R⟨X⟩†`. -/
@[continuity]
theorem continuous_evalAtHom (hb : ‖b‖ ≤ 1) : Continuous (evalAtHom (R := R) hb) :=
  AddMonoidHomClass.continuous_of_bound (evalAtHom (R := R) hb) ‖(1 : A)‖ fun f ↦ by
    rw [evalAtHom_apply]
    exact norm_evalAt_le_mul_norm hb f

end EvalAt

/-- In a complete commutative ultrametric `R`-algebra with contractive `algebraMap`, multivariate
`washnitzerAlgebra.aeval` in one variable `Fin 1` agrees with univariate `PowerSeries.evalAt` under
the variable identification `Unit ≃ Fin 1`. -/
theorem aeval_renameAlgEquiv_unit {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
    [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S] [Algebra R S]
    (halg : ∀ r : R, ‖algebraMap R S r‖ ≤ ‖r‖) {s : S} (hs : ‖s‖ ≤ 1)
    (f : washnitzerAlgebra Unit R) :
    aeval halg (fun _ : Fin 1 ↦ s) (fun _ ↦ hs)
        (renameAlgEquiv (Equiv.ofUnique Unit (Fin 1)) f) =
      PowerSeries.evalAt (f : R⟦X⟧) s := by
  set e : Unit ≃ Fin 1 := Equiv.ofUnique Unit (Fin 1)
  rw [aeval_apply,
    ← (hasSum_eval₂ (algebraMap R S) (fun _ : Fin 1 ↦ s) halg (fun _ ↦ hs) _).tsum_eq,
    PowerSeries.evalAt_def, ← ((Finsupp.uniqueEquiv (0 : Fin 1)).symm.tsum_eq)]
  refine tsum_congr fun n ↦ ?_
  have hsingle : (Finsupp.uniqueEquiv (0 : Fin 1)).symm n = Finsupp.single 0 n :=
    Finsupp.ext fun i ↦ by rw [Subsingleton.elim i 0]; simp
  have hcoeff : MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n)
      (MvPowerSeries.rename e (f : MvPowerSeries Unit R)) = PowerSeries.coeff n (f : R⟦X⟧) := by
    have he : Finsupp.single (0 : Fin 1) n =
        Finsupp.embDomain e.toEmbedding (Finsupp.single () n) := by
      simp [Subsingleton.elim (e ()) 0]
    rw [he]
    exact MvPowerSeries.coeff_embDomain_rename e.toEmbedding (f : MvPowerSeries Unit R) _
  simp [TauCeti.Huber.weightedEvalTerm_def, hsingle, hcoeff, Algebra.smul_def]

end washnitzerAlgebra

end TauCeti.Dagger
