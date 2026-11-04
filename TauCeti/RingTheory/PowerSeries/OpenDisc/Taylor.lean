/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval
public import TauCeti.RingTheory.PowerSeries.Entire.Taylor

/-!
# Taylor translation on an open nonarchimedean disc

Over a complete ultrametric normed commutative ring with `‖1‖ = 1`, translation by a point `a`
with `‖a‖ < R₀` preserves the algebra of series on the open disc of radius `R₀`.
Its coefficients are the values at `a` of the Hasse derivatives, using the same
`PowerSeries.taylor` as for entire series. Translation is continuous for the topology of all
smaller-radius Gauss norms, composes by addition, and has inverse translation by `-a`.
Evaluation of the translate at `b` is evaluation of the original series at `b + a`.

The estimate at a closed radius `r` containing `a` is contractive whenever the weighted
coefficients are bounded. To prove open-disc restrictedness, apply that estimate at a slightly
larger radius still inside the open disc. No radius needs to be realized by a scalar and no
factorial is inverted. Translation preserves the Gauss norm on every closed disc of positive
radius `r` with `‖a‖ ≤ r < R₀`.

## Main definitions

* `TauCeti.PowerSeries.OnOpenDisc.taylorHom`: translation by an interior point as a ring
  homomorphism on the open-disc algebra.
* `TauCeti.PowerSeries.OnOpenDisc.taylorEquiv`: translation as a ring automorphism, with inverse
  translation by the negative centre.

## Main results

* `PowerSeries.OnOpenDisc.taylor`: translation preserves the open-disc radius condition.
* `TauCeti.PowerSeries.OnOpenDisc.continuous_taylorHom`: translation is continuous.
* `TauCeti.PowerSeries.OnOpenDisc.taylorHom_taylorHom`: translations compose by addition.
* `TauCeti.PowerSeries.OnOpenDisc.taylorHom_polynomialHom`: translation agrees with polynomial
  Taylor translation.
* `TauCeti.PowerSeries.OnOpenDisc.norm_restrict_taylorHom`: translation preserves the Gauss norm
  on every smaller positive-radius closed disc containing the centre.
* `TauCeti.PowerSeries.OnOpenDisc.evalAt_taylorHom`: evaluation at an algebra point `b` after
  translation is evaluation at `b + algebraMap R A a`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
* The coefficient construction is `PowerSeries.taylor` in
  `TauCeti.RingTheory.PowerSeries.Entire.Taylor`.
-/

public section

open Filter PowerSeries
open scoped Topology

namespace PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
  {f g : R⟦X⟧} {R₀ : ℝ} {a : R}

/-- Translation by an interior point preserves series on the open disc. -/
theorem OnOpenDisc.taylor (hf : f.OnOpenDisc R₀) (ha : ‖a‖ < R₀) :
    (taylor a f).OnOpenDisc R₀ := by
  refine onOpenDisc_iff.2 fun r hr hrR ↦ ?_
  obtain ⟨s, hs, hsR⟩ := exists_between (max_lt hrR ha)
  have hs0 : 0 < s := hr.trans (lt_of_le_of_lt (le_max_left _ _) hs)
  exact ((TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
    (hf.isRestricted (by rwa [abs_of_pos hs0]))).taylor hs0
    (le_max_right r ‖a‖ |>.trans hs.le)).onOpenDisc.isRestricted
      (by rw [abs_of_pos hr]; exact (le_max_left _ _).trans_lt hs)

variable [CompleteSpace R]

omit [IsUltrametricDist R] [NormOneClass R] in
/-- Taylor translation is additive on open-disc series. -/
theorem OnOpenDisc.taylor_add (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀)
    (ha : ‖a‖ < R₀) :
    PowerSeries.taylor a (f + g) = PowerSeries.taylor a f + PowerSeries.taylor a g :=
  taylor_add_of_summable_norm (fun n ↦ (hf.hasseDeriv n).summable_norm_smul_pow ha)
    (fun n ↦ (hg.hasseDeriv n).summable_norm_smul_pow ha)

omit [IsUltrametricDist R] [NormOneClass R] in
/-- Taylor translation is multiplicative on open-disc series. -/
theorem OnOpenDisc.taylor_mul (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀)
    (ha : ‖a‖ < R₀) :
    PowerSeries.taylor a (f * g) = PowerSeries.taylor a f * PowerSeries.taylor a g :=
  taylor_mul_of_summable_norm (fun n ↦ (hf.hasseDeriv n).summable_norm_smul_pow ha)
    (fun n ↦ (hg.hasseDeriv n).summable_norm_smul_pow ha)

end PowerSeries

namespace TauCeti.PowerSeries.OnOpenDisc

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]
  [CompleteSpace R] {R₀ : ℝ} {a b : R}

attribute [local instance] radius_pos

/-- Translation `f(X) ↦ f(X + a)` on the open-disc algebra. -/
noncomputable def taylorHom (ha : ‖a‖ < R₀) :
    OnOpenDisc.subring R R₀ →+* OnOpenDisc.subring R R₀ where
  toFun f := ⟨taylor a f, OnOpenDisc.mem_subring.mpr <|
    (OnOpenDisc.mem_subring.mp f.2).taylor ha⟩
  map_one' := Subtype.ext (taylor_one a)
  map_zero' := Subtype.ext (taylor_zero_right a)
  map_add' f g := Subtype.ext <|
    (OnOpenDisc.mem_subring.mp f.2).taylor_add (OnOpenDisc.mem_subring.mp g.2) ha
  map_mul' f g := Subtype.ext <|
    (OnOpenDisc.mem_subring.mp f.2).taylor_mul (OnOpenDisc.mem_subring.mp g.2) ha

/-- The underlying formal series is the coefficient-defined Taylor translate. -/
@[simp]
theorem coe_taylorHom (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    (taylorHom ha f : R⟦X⟧) = taylor a (f : R⟦X⟧) := (rfl)

/-- On polynomials, analytic translation agrees with polynomial Taylor translation. -/
@[simp]
theorem taylorHom_polynomialHom (ha : ‖a‖ < R₀) (p : Polynomial R) :
    taylorHom ha (OnOpenDisc.polynomialHom p) =
      OnOpenDisc.polynomialHom (Polynomial.taylor a p) :=
  Subtype.ext (by simp)

/-- Translation on a smaller closed disc is controlled by any larger closed disc containing
its centre. -/
theorem norm_restrict_taylorHom_le (ha : ‖a‖ < R₀) (r s : Set.Ioo (0 : ℝ) R₀)
    (hrs : (r : ℝ) ≤ s) (has : ‖a‖ ≤ s) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (taylorHom ha f)‖ ≤ ‖restrict s f‖ := by
  refine (norm_le_iff (norm_nonneg _)).2 fun n ↦ ?_
  simp only [coe_restrict, coe_taylorHom]
  calc
    ‖coeff n (taylor a (f : R⟦X⟧))‖ * (r : ℝ) ^ n ≤
        ‖coeff n (taylor a (f : R⟦X⟧))‖ * (s : ℝ) ^ n := by
          gcongr
          exact r.2.1.le
    _ ≤ (f : R⟦X⟧).gaussNorm norm s := by
      have hf := hasGaussNorm_of_isRestricted (restrict s f).2
      rw [coe_restrict] at hf
      exact norm_coeff_taylor_mul_pow_le hf s.2.1 has n
    _ = ‖restrict s f‖ := by rw [norm_eq_gaussNorm, coe_restrict]

/-- Translation is continuous for all smaller-radius Gauss norms. -/
theorem continuous_taylorHom (ha : ‖a‖ < R₀) : Continuous (taylorHom ha) := by
  refine continuous_iff.2 fun r ↦ ?_
  obtain ⟨s, hs, hsR⟩ := exists_between (max_lt r.2.2 ha)
  let s' : Set.Ioo (0 : ℝ) R₀ :=
    ⟨s, r.2.1.trans ((le_max_left _ _).trans_lt hs), hsR⟩
  let φ := (restrict (R := R) r).comp (taylorHom ha)
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  let : Fact (0 < (s' : ℝ)) := ⟨s'.2.1⟩
  have h := (uniformContinuous_restrict (R := R) s').continuous.tendsto 0
  refine squeeze_zero_norm (fun f ↦ norm_restrict_taylorHom_le ha r s'
    ((le_max_left _ _).trans hs.le) ((le_max_right _ _).trans hs.le) f) ?_
  simpa only [map_zero, norm_zero] using h.norm

/-- Translations compose by addition of their centres. -/
theorem taylorHom_taylorHom (ha : ‖a‖ < R₀) (hb : ‖b‖ < R₀)
    (f : OnOpenDisc.subring R R₀) :
    taylorHom hb (taylorHom ha f) =
      taylorHom ((IsUltrametricDist.norm_add_le_max b a).trans_lt (max_lt hb ha)) f := by
  have : Fact (0 < R₀) := ⟨(norm_nonneg a).trans_lt ha⟩
  refine congrFun (((continuous_taylorHom hb).comp (continuous_taylorHom ha)).ext_on
    denseRange_polynomialHom (continuous_taylorHom _) ?_) f
  rintro _ ⟨p, rfl⟩
  simp [Polynomial.taylor_taylor, add_comm]

/-- Translation by zero is the identity. -/
@[simp]
theorem taylorHom_zero [Fact (0 < R₀)] (f : OnOpenDisc.subring R R₀) :
    taylorHom (a := 0) (by simpa using (Fact.out : 0 < R₀)) f = f :=
  Subtype.ext (by simp)

/-- Translation by an interior point, as an automorphism of the open-disc algebra. -/
noncomputable def taylorEquiv (ha : ‖a‖ < R₀) :
    OnOpenDisc.subring R R₀ ≃+* OnOpenDisc.subring R R₀ := by
  have : Fact (0 < R₀) := ⟨(norm_nonneg a).trans_lt ha⟩
  exact RingEquiv.ofRingHom (taylorHom ha) (taylorHom (a := -a) (by simpa using ha))
    (RingHom.ext fun f ↦ by simp [taylorHom_taylorHom])
    (RingHom.ext fun f ↦ by simp [taylorHom_taylorHom])

/-- The automorphism acts by Taylor translation. -/
@[simp]
theorem taylorEquiv_apply (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    taylorEquiv ha f = taylorHom ha f := (rfl)

/-- The inverse automorphism translates by the negative centre. -/
@[simp]
theorem taylorEquiv_symm_apply (ha : ‖a‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    (taylorEquiv ha).symm f = taylorHom (a := -a) (by simpa using ha) f := (rfl)

/-- On each smaller closed disc containing the centre, translation preserves the Gauss norm. -/
theorem norm_restrict_taylorHom (ha : ‖a‖ < R₀) (r : Set.Ioo (0 : ℝ) R₀)
    (har : ‖a‖ ≤ r) (f : OnOpenDisc.subring R R₀) :
    ‖restrict r (taylorHom ha f)‖ = ‖restrict r f‖ := by
  refine le_antisymm (norm_restrict_taylorHom_le ha r r le_rfl har f) ?_
  have h := norm_restrict_taylorHom_le (a := -a) (by simpa using ha)
    r r le_rfl (by simpa using har) (taylorHom ha f)
  have : Fact (0 < R₀) := ⟨r.2.1.trans r.2.2⟩
  simpa [taylorHom_taylorHom] using h

/-- Evaluating a translate at an algebra point `b` evaluates the original series at
`b + algebraMap R A a`. -/
theorem evalAt_taylorHom {A : Type*} [NormedRing A] [Algebra R A] [IsBoundedSMul R A]
    [CompleteSpace A] [IsUltrametricDist A] [NormOneClass A] {b : A}
    (ha : ‖a‖ < R₀) (hb : ‖b‖ < R₀) (f : OnOpenDisc.subring R R₀) :
    (taylorHom ha f : R⟦X⟧).evalAt b =
      (f : R⟦X⟧).evalAt (b + algebraMap R A a) := by
  have haA : ‖algebraMap R A a‖ < R₀ := by
    have h : ‖algebraMap R A a‖ ≤ ‖a‖ := by
      simpa only [Algebra.algebraMap_eq_smul_one, norm_one, mul_one] using
        (norm_smul_le a (1 : A))
    exact h.trans_lt ha
  have hba := (IsUltrametricDist.norm_add_le_max b (algebraMap R A a)).trans_lt
    (max_lt hb haA)
  have h := ((continuous_evalAtHom (R := R) hb).comp (continuous_taylorHom ha)).ext_on
    denseRange_polynomialHom (continuous_evalAtHom hba) (fun _ ⟨p, hp⟩ ↦ ?_)
  · simpa only [Function.comp_apply, OnOpenDisc.evalAtHom_apply] using congrFun h f
  · subst hp
    simp [Polynomial.taylor_apply, Polynomial.aeval_comp]

end TauCeti.PowerSeries.OnOpenDisc
