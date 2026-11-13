/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.Topology
public import TauCeti.RingTheory.LaurentSeries.Level.Transition
public import TauCeti.RingTheory.LaurentSeries.Puiseux.KaehlerDifferential.Basic

/-!
# Pullback of continuous one-forms between ramified levels

For `n ∣ m`, write `e = m / n`. The inclusion of ramified Laurent levels sends
`u_n` to `u_m ^ e`. Its pullback on continuous one-forms therefore sends
`f du_n` to `f (u_m ^ e) e u_m ^ (e - 1) du_m`.

We construct this as a continuous semilinear map over the existing level transition.
The maps compose, agree with pullback from the base Laurent field, and, in characteristic
zero, agree with the embeddings into the continuous differentials of the Puiseux field.
Their residues are multiplied by `e`, in every characteristic. In particular these are
pullbacks of differential forms, not just coefficientwise inclusions: in characteristic
dividing `e`, the pullback vanishes.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential

variable {K : Type*} [Field K] {n m l : ℕ+}

variable (K) in
/-- Pullback of continuous one-forms along `u_n = u_m ^ (m / n)`, semilinear over the
inclusion of ramified levels. -/
noncomputable def transition (h : n ∣ m) :
    Level.ContinuousKaehlerDifferential K n
      →ₛₗ[(Level.transition K h : Level K n →+* Level K m)]
        Level.ContinuousKaehlerDifferential K m where
  toFun ω := (addEquivContinuousKaehlerDifferential K m).symm
    (TauCeti.ContinuousKaehlerDifferential.subst (K := K)
      (φ := PowerSeries.X ^ (m.divExact n : ℕ)) (by simp)
      (pow_ne_zero _ PowerSeries.X_ne_zero)
      (addEquivContinuousKaehlerDifferential K n ω))
  map_add' ω η := by simp
  map_smul' f ω := by
    apply (addEquivContinuousKaehlerDifferential K m).injective
    simp [TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand]

/-- In the Laurent variable, pullback is substitution of `X ^ (m / n)` into forms. -/
@[simp]
theorem addEquivContinuousKaehlerDifferential_transition (h : n ∣ m)
    (ω : Level.ContinuousKaehlerDifferential K n) :
    addEquivContinuousKaehlerDifferential K m (transition K h ω) =
      TauCeti.ContinuousKaehlerDifferential.subst (K := K)
        (φ := PowerSeries.X ^ (m.divExact n : ℕ)) (by simp)
        (pow_ne_zero _ PowerSeries.X_ne_zero)
        (addEquivContinuousKaehlerDifferential K n ω) :=
  (addEquivContinuousKaehlerDifferential K m).apply_symm_apply _

/-- The coefficient of the pulled-back form is the expanded coefficient multiplied by
`e u_m ^ (e - 1)`, where `e = m / n`. -/
theorem ringEquivLaurentSeries_equivLevel_transition (h : n ∣ m)
    (ω : Level.ContinuousKaehlerDifferential K n) :
    ringEquivLaurentSeries K m (equivLevel K m (transition K h ω)) =
      _root_.LaurentSeries.expand K (m.divExact n)
          (ringEquivLaurentSeries K n (equivLevel K n ω)) *
        _root_.LaurentSeries.derivative K (single (m.divExact n : ℤ) 1) := by
  simp [TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_subst,
    TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand, single_pow]

/-- Pullback between levels commutes with the differential. -/
@[simp]
theorem transition_ofForm_D (h : n ∣ m) (f : K⸨X⸩) :
    transition K h (ofForm (d := n) (TauCeti.ContinuousKaehlerDifferential.D K f)) =
      ofForm (d := m) (TauCeti.ContinuousKaehlerDifferential.D K
        (_root_.LaurentSeries.expand K (m.divExact n) f)) := by
  apply (addEquivContinuousKaehlerDifferential K m).injective
  simp [TauCeti.LaurentSeries.substAlgHom_X_pow_eq_expand]

/-- Pullback between levels is continuous for the valuation topologies on one-forms. -/
theorem continuous_transition (h : n ∣ m) : Continuous (transition K h) := by
  apply (homeomorphForm K m).comp_continuous_iff.mp
  simpa only [Function.comp_def, homeomorphForm_apply,
    addEquivContinuousKaehlerDifferential_transition] using
    (TauCeti.ContinuousKaehlerDifferential.continuous_subst (K := K)
      (φ := PowerSeries.X ^ (m.divExact n : ℕ)) (by simp)
      (pow_ne_zero _ PowerSeries.X_ne_zero)).comp (homeomorphForm K n).continuous

/-- Pullback between levels multiplies the residue by the relative ramification index,
including when this index vanishes in the coefficient field. -/
theorem coeff_neg_one_transition (h : n ∣ m)
    (ω : Level.ContinuousKaehlerDifferential K n) :
    (ringEquivLaurentSeries K m (equivLevel K m (transition K h ω))).coeff (-1) =
      ((m : ℕ) / n) • (ringEquivLaurentSeries K n (equivLevel K n ω)).coeff (-1) := by
  rw [ringEquivLaurentSeries_equivLevel, addEquivContinuousKaehlerDifferential_transition,
    TauCeti.ContinuousKaehlerDifferential.coeff_neg_one_equivLaurentSeries_subst]
  simp [PowerSeries.order_X_pow, PNat.coe_divExact h]

/-- Pullback along an identity transition is the identity. -/
@[simp]
theorem transition_self (ω : Level.ContinuousKaehlerDifferential K n) :
    transition K (dvd_refl n) ω = ω := by
  have he : n.divExact n = 1 := by
    apply mul_left_cancel (a := n)
    rw [PNat.mul_div_exact (dvd_refl n), mul_one]
  apply (addEquivContinuousKaehlerDifferential K n).injective
  rw [addEquivContinuousKaehlerDifferential_transition]
  exact (TauCeti.ContinuousKaehlerDifferential.subst_congr _ _ (by simp [he])
    PowerSeries.constantCoeff_X PowerSeries.X_ne_zero _).trans
      (TauCeti.ContinuousKaehlerDifferential.subst_X _)

/-- Pullbacks of forms compose along divisibility of ramification indices. -/
@[simp]
theorem transition_transition (h₁ : n ∣ m) (h₂ : m ∣ l)
    (ω : Level.ContinuousKaehlerDifferential K n) :
    transition K h₂ (transition K h₁ ω) = transition K (h₁.trans h₂) ω := by
  have he : m.divExact n * l.divExact m = l.divExact n := by
    apply mul_left_cancel (a := n)
    rw [← mul_assoc, PNat.mul_div_exact h₁, PNat.mul_div_exact h₂,
      PNat.mul_div_exact (h₁.trans h₂)]
  apply (addEquivContinuousKaehlerDifferential K l).injective
  simp only [addEquivContinuousKaehlerDifferential_transition]
  have hpow : (PowerSeries.X ^ (m.divExact n : ℕ) : K⟦X⟧).subst
      (PowerSeries.X ^ (l.divExact m : ℕ) : K⟦X⟧) = PowerSeries.X ^ (l.divExact n : ℕ) := by
    simpa only [← PNat.mul_coe, he] using
      (PowerSeries.subst_X_pow_X_pow (R := K) (S := K) (m.divExact n : ℕ)
        (l.divExact m).ne_zero)
  rw [TauCeti.ContinuousKaehlerDifferential.subst_subst]
  exact TauCeti.ContinuousKaehlerDifferential.subst_congr _ _ hpow _ _ _

/-- Pullback from the base field followed by a transition is pullback to the larger level. -/
@[simp]
theorem transition_map (h : n ∣ m) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    transition K h (map K n ω) = map K m ω := by
  apply (addEquivContinuousKaehlerDifferential K m).injective
  simp only [addEquivContinuousKaehlerDifferential_transition,
    addEquivContinuousKaehlerDifferential_map]
  have hpow : (PowerSeries.X ^ (n : ℕ) : K⟦X⟧).subst
      (PowerSeries.X ^ (m.divExact n : ℕ) : K⟦X⟧) = PowerSeries.X ^ (m : ℕ) := by
    simpa only [← PNat.mul_coe, PNat.mul_div_exact h] using
      (PowerSeries.subst_X_pow_X_pow (R := K) (S := K) (n : ℕ) (m.divExact n).ne_zero)
  rw [TauCeti.ContinuousKaehlerDifferential.subst_subst]
  exact TauCeti.ContinuousKaehlerDifferential.subst_congr _ _ hpow _ _ _

/-- Pullback between levels vanishes exactly when the relative ramification index vanishes
in the coefficient field. -/
theorem transition_eq_zero_iff (h : n ∣ m) :
    transition K h = 0 ↔ ((m.divExact n : ℕ) : K) = 0 := by
  constructor
  · intro hz
    have hω := congrArg (fun ω ↦ ringEquivLaurentSeries K m (equivLevel K m ω))
      (LinearMap.congr_fun hz
        (ofForm (d := n) (TauCeti.ContinuousKaehlerDifferential.D K (single 1 1))))
    simpa [ringEquivLaurentSeries_equivLevel_transition] using hω
  · intro he
    apply LinearMap.ext
    intro ω
    apply (equivLevel K m).injective
    apply (ringEquivLaurentSeries K m).injective
    rw [ringEquivLaurentSeries_equivLevel_transition]
    simp [he]

/-- Pullback is injective whenever the relative ramification index is nonzero in `K`.
This includes separable transitions in positive characteristic. -/
theorem transition_injective (h : n ∣ m) [NeZero ((m.divExact n : ℕ) : K)] :
    Function.Injective (transition K h) := by
  intro ω η hω
  have hd : _root_.LaurentSeries.derivative K (single (m.divExact n : ℤ) (1 : K)) ≠ 0 := by
    simpa using (NeZero.ne ((m.divExact n : ℕ) : K))
  have hc := congrArg (fun ξ ↦ ringEquivLaurentSeries K m (equivLevel K m ξ)) hω
  rw [ringEquivLaurentSeries_equivLevel_transition,
    ringEquivLaurentSeries_equivLevel_transition, mul_left_inj' hd] at hc
  exact (equivLevel K n).injective <| (ringEquivLaurentSeries K n).injective <|
    _root_.LaurentSeries.expand_injective _ hc

section CharZero

variable [CharZero K]

/-- The embeddings of level one-forms into Puiseux one-forms agree along every transition. -/
theorem levelMap_transition (h : n ∣ m) (ω : Level.ContinuousKaehlerDifferential K n) :
    puiseuxField.ContinuousKaehlerDifferential.levelMap K m
        (addEquivContinuousKaehlerDifferential K m (transition K h ω)) =
      puiseuxField.ContinuousKaehlerDifferential.levelMap K n
        (addEquivContinuousKaehlerDifferential K n ω) := by
  rw [addEquivContinuousKaehlerDifferential_transition]
  have he := puiseuxField.ContinuousKaehlerDifferential.levelMap_subst_X_pow n (m.divExact n)
    (addEquivContinuousKaehlerDifferential K n ω)
  rw [PNat.mul_div_exact h] at he
  exact he

end CharZero

end TauCeti.LaurentSeries.Level.ContinuousKaehlerDifferential
