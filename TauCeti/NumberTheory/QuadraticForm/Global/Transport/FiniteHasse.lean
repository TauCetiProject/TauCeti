/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
public import TauCeti.NumberTheory.QuadraticForm.Global.FiniteHasse
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import TauCeti.NumberTheory.NumberField.FinitePlace.Transport
import TauCeti.NumberTheory.QuadraticForm.CompletionTransport

/-!
# Transporting local and finite Hasse invariants along field isomorphisms

A ring isomorphism `e : K ≃+* L` of number fields identifies the finite places of `K` with those of
`L` via `HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)`. At each pair of
corresponding finite places `v` and `w`, `adicCompletionCongr` extends `e` to a ring isomorphism
`K_v ≃+* L_w` that commutes with extending regular-form isometry classes to the completions and
therefore preserves the local Hasse invariant and the finite Hasse sign `QuadraticForm.finiteHasse`.

## Main results

* `TauCeti.RegularFormClass.localHasse_baseChange_adicCompletion_mapRingEquiv`: transporting a
  global regular-form class along a field isomorphism of number fields preserves its local Hasse
  invariant at corresponding finite places.
* `QuadraticForm.finiteHasse_eq_of_semilinearEquiv_of_valuation_eq`,
  `QuadraticForm.finiteHasse_eq_of_semilinearEquiv`,
  `QuadraticForm.finiteHasse_equivOfRingEquiv_of_semilinearEquiv`,
  `QuadraticForm.finiteHasse_transport_equivOfRingEquiv`: regular quadratic forms intertwined by
  a semilinear equivalence over an isomorphism of number fields have the same finite Hasse sign at
  corresponding finite places.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

namespace TauCeti

/-- For a ring isomorphism `e : K ≃+* L` of number fields carrying a finite place `v` to `w`, the
local Hasse invariant at `w` of a transported global regular-form class equals the local Hasse
invariant at `v` of the original class. -/
theorem RegularFormClass.localHasse_baseChange_adicCompletion_mapRingEquiv (e : K ≃+* L)
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hvw : w.asIdeal = Ideal.map (RingOfIntegers.mapRingEquiv e) v.asIdeal)
    (x : RegularFormClass K) :
    letI : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    letI : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    RegularFormClass.localHasse
        (RegularFormClass.baseChange (w.adicCompletion L) (RegularFormClass.mapRingEquiv e x)) =
      RegularFormClass.localHasse (RegularFormClass.baseChange (v.adicCompletion K) x) := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  exact RegularFormClass.localHasse_baseChange_adicCompletion_mapRingEquiv_of_valuation_eq
    (e.valuation_apply_of_asIdeal_eq hvw) x

end TauCeti

namespace QuadraticForm

open TauCeti

section SemilinearEquiv

variable {σ : K →+* L} {σ' : L →+* K} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type*} [AddCommGroup W] [Module L W] [FiniteDimensional L W]

/-- Regular quadratic forms over number fields intertwined by a semilinear equivalence
`f : V ≃ₛₗ[σ] W` (`Q' (f u) = σ (Q u)`) have the same finite Hasse sign at finite places `v` and
`w` whose valuations are intertwined by `σ`. -/
theorem finiteHasse_eq_of_semilinearEquiv_of_valuation_eq
    {Q : _root_.QuadraticForm K V} {Q' : _root_.QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ u, Q' (f u) = σ (Q u))
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (he : ∀ a, w.valuation L (σ a) = v.valuation K a) :
    Q'.finiteHasse hQ' w = Q.finiteHasse hQ v := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  let _ : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  rw [finiteHasse_eq_localHasse_baseChange, finiteHasse_eq_localHasse_baseChange,
    formClass_eq_mapRingEquiv_of_semilinearEquiv hQ hQ' f hf]
  exact RegularFormClass.localHasse_baseChange_adicCompletion_mapRingEquiv_of_valuation_eq
    (e := RingHomInvPair.toRingEquiv σ σ')
    (fun a ↦ by rw [RingHomInvPair.toRingEquiv_apply]; exact he a) (formClass Q hQ)

/-- Regular quadratic forms over number fields intertwined by a semilinear equivalence
`f : V ≃ₛₗ[σ] W` carrying a finite place `v` to `w` have the same finite Hasse sign at `w` and
`v`. -/
theorem finiteHasse_eq_of_semilinearEquiv
    {Q : _root_.QuadraticForm K V} {Q' : _root_.QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ u, Q' (f u) = σ (Q u))
    {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hvw : w.asIdeal =
      Ideal.map (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) v.asIdeal) :
    Q'.finiteHasse hQ' w = Q.finiteHasse hQ v :=
  finiteHasse_eq_of_semilinearEquiv_of_valuation_eq hQ hQ' f hf
    ((RingHomInvPair.toRingEquiv σ σ').valuation_apply_of_asIdeal_eq hvw)

/-- Specialization of `finiteHasse_eq_of_semilinearEquiv` when the place of `L` is the image of `v`
under `HeightOneSpectrum.equivOfRingEquiv` along `RingHomInvPair.toRingEquiv σ σ'`. -/
theorem finiteHasse_equivOfRingEquiv_of_semilinearEquiv
    {Q : _root_.QuadraticForm K V} {Q' : _root_.QuadraticForm L W}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate)
    (f : V ≃ₛₗ[σ] W) (hf : ∀ u, Q' (f u) = σ (Q u))
    (v : HeightOneSpectrum (𝓞 K)) :
    Q'.finiteHasse hQ'
        (HeightOneSpectrum.equivOfRingEquiv
          (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) v) =
      Q.finiteHasse hQ v :=
  finiteHasse_eq_of_semilinearEquiv hQ hQ' f hf
    (asIdeal_equivOfRingEquiv (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) v)

/-- The finite Hasse sign of a semilinearly transported regular form `Q.transport f` at the image
finite place equals the finite Hasse sign of `Q` at `v`. -/
@[simp↓]
theorem finiteHasse_transport_equivOfRingEquiv
    {Q : _root_.QuadraticForm K V} {f : V ≃ₛₗ[σ] W}
    (h : (Q.transport f).Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    (Q.transport f).finiteHasse h
        (HeightOneSpectrum.equivOfRingEquiv
          (RingOfIntegers.mapRingEquiv (RingHomInvPair.toRingEquiv σ σ')) v) =
      Q.finiteHasse ((QuadraticMap.nondegenerate_transport_iff f Q).mp h) v :=
  finiteHasse_equivOfRingEquiv_of_semilinearEquiv _ h f
    (QuadraticMap.transport_apply_apply f Q) v

end SemilinearEquiv

end QuadraticForm
