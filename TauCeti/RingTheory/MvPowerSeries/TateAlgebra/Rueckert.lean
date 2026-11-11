/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Polynomial
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient
public import TauCeti.RingTheory.Polynomial.Rueckert

/-!
# Tate algebras satisfy the Rückert hypotheses

Let `K` be a complete nonarchimedean field and `T = K⟨X₁, …, Xₙ⟩` a Tate algebra. The inclusion
of polynomials `T[Y] → T⟨Y⟩` into the Tate algebra in one more variable satisfies the Rückert
hypotheses of `TauCeti.RingTheory.Polynomial.Rueckert`, with the Weierstrass polynomials as the
distinguished set: the monic polynomials `ω` which are distinguished of degree `deg ω` at the
unit radius, equivalently whose Gauss norm is one.

* Monic factors of Weierstrass polynomials are Weierstrass polynomials
  (`TauCeti.PowerSeries.IsDistinguished.of_dvd`).
* Weierstrass division identifies `T[Y] ⧸ (ω)` with `T⟨Y⟩ ⧸ (ω)`
  (`TauCeti.PowerSeries.IsDistinguished.polynomialQuotientEquiv`).
* After an automorphism of `K⟨X, Y⟩` every nonzero series is distinguished in `Y` with a unit
  dominant coefficient (`TauCeti.MvPowerSeries.exists_algEquiv_isDistinguished_isUnit`), and
  Weierstrass preparation makes it a unit multiple of a Weierstrass polynomial.

The general descent results then pass from `T` to `T⟨Y⟩`; this is how unique factorisation of
Tate algebras is proved (`TauCeti.MvPowerSeries.uniqueFactorizationMonoid`).

## Main results

* `TauCeti.MvPowerSeries.isRueckert_polynomialToRestricted`: the Rückert hypotheses for
  `T[Y] → T⟨Y⟩` and the Weierstrass polynomials.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §§5.2.1–5.2.5.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- **Tate algebras satisfy the Rückert hypotheses.** The inclusion of polynomials over the
Tate algebra `T = K⟨X₁, …, Xₙ⟩` into the Tate algebra `T⟨Y⟩` in one more variable satisfies the
Rückert hypotheses for the Weierstrass polynomials: the monic polynomials over `T` which are
distinguished of their degree at the unit radius. -/
theorem isRueckert_polynomialToRestricted {σ : Type*} [Finite σ] :
    (PowerSeries.polynomialToRestricted (R := Tate σ) 1 : Polynomial (Tate σ) →+*
        _root_.PowerSeries.IsRestricted.subring (R := Tate σ) 1).IsRueckert
      {p | p.Monic ∧ PowerSeries.IsDistinguished 1 p.natDegree (p : _root_.PowerSeries (Tate σ))}
    where
  injective := PowerSeries.polynomialToRestricted_injective 1
  monic hw := hw.1
  mem_of_dvd hw hp hpw := ⟨hp, hw.2.of_dvd one_pos ⟨rfl, hw.1⟩ hp hpw⟩
  dvd_iff hw p := hw.2.polynomialToRestricted_dvd_iff one_pos ⟨rfl, hw.1⟩ p
  exists_dvd_sub {w} hw b := by
    obtain ⟨x, hx⟩ := (hw.2.polynomialQuotientEquiv one_pos ⟨rfl, hw.1⟩).surjective
      (Ideal.Quotient.mk _ b)
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [PowerSeries.IsDistinguished.polynomialQuotientEquiv_mk] at hx
    exact ⟨p, Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hx.symm)⟩
  exists_mul_eq {b} hb := by
    -- `Φ` identifies `K⟨X, Y⟩` with `T⟨Y⟩`; let `f` be the series corresponding to `b`.
    let Φ := restrictedOptionEquiv (R := K) (σ := σ) (c := fun _ ↦ 1)
    have hf : Φ.symm b ≠ 0 := (map_ne_zero_iff _ Φ.symm.injective).mpr hb
    -- Make `f` distinguished in `Y` by an automorphism `e`.
    obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit _ hf
    -- Weierstrass preparation: `Φ (e f) = u * ω` with `u` a unit and `ω` monic.
    obtain ⟨u, ω, hu', hm, hmul⟩ :=
      hd.exists_isUnit_isMonicOfDegree_mul_eq hu zero_lt_one (Φ (e (Φ.symm b))).2
    have hg : Φ (e (Φ.symm b)) = u * PowerSeries.polynomialToRestricted 1 ω :=
      Subtype.ext (by rw [← hmul, Subring.coe_mul, PowerSeries.coe_polynomialToRestricted])
    have hω : PowerSeries.IsDistinguished 1 s (ω : _root_.PowerSeries (Tate σ)) :=
      (hmul.symm ▸ hd).of_isUnit_mul zero_lt_one hu'
    let α : _root_.PowerSeries.IsRestricted.subring (R := Tate σ) 1 ≃+* _ :=
      Φ.symm.toRingEquiv.trans (e.toRingEquiv.trans Φ.toRingEquiv)
    have hα : α b = Φ (e (Φ.symm b)) := by simp [α]
    refine ⟨α, hu'.unit⁻¹, ω, ⟨hm.monic, hm.natDegree_eq ▸ hω⟩, ?_⟩
    rw [hα, hg, ← mul_assoc, IsUnit.val_inv_mul, one_mul, AlgHom.coe_toRingHom]

end TauCeti.MvPowerSeries
