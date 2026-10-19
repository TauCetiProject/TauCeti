/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Jacobson.Ring
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Tate algebras are Jacobson rings

Over a complete nonarchimedean field `K`, the Tate algebra `K⟨X₁, …, Xₙ⟩` is a Jacobson ring:
every prime ideal is an intersection of maximal ideals. Together with the Nullstellensatz
`TauCeti.MvPowerSeries.finite_quotient_of_isMaximal`, this lets the maximal ideals, the classical
points of the affinoid space, detect every radical ideal of the Tate algebra and of its quotients.

The proof is by induction on the number of variables, writing `K⟨X, Y⟩` as the univariate Tate
algebra `K⟨X⟩⟨Y⟩` and applying `TauCeti.isJacobsonRing_of_quotient_span_singleton`.

* The Jacobson radical of `K⟨X⟩⟨Y⟩` vanishes. If `f` lies in it, then so does every multiple
  `f * a Y`, for `a ∈ K`, so `1 + f * a Y` is a unit and hence distinguished of degree `0`
  (`TauCeti.PowerSeries.isDistinguished_zero_of_isUnit`): all its positive-degree coefficients
  have norm smaller than `1`. Choosing `a` as the inverse of a nonzero coefficient of `f` produces
  a coefficient of norm at least `1`, unless `f = 0`.
* For a nonzero `f`, an automorphism makes `f` distinguished in `Y` with a unit dominant
  coefficient, and Weierstrass division makes `K⟨X⟩⟨Y⟩ ⧸ (f)` finite over `K⟨X⟩`, which is
  Jacobson by induction. Integral extensions of Jacobson rings are Jacobson.

The coefficient field need not be nontrivially normed: the rescaling uses only the inverse of a
coefficient of `f`.

## Main results

* `TauCeti.MvPowerSeries.isJacobsonRing`: the Tate algebra in finitely many variables over a
  complete nonarchimedean field is a Jacobson ring.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.2.5–5.2.6.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- The Jacobson radical of the univariate Tate algebra over a Tate algebra vanishes: a nonzero
element `f` has a multiple `f * a Y` for which `1 + f * a Y` has a positive-degree coefficient of
norm `1`, so it is not a unit. -/
private theorem jacobson_bot_restricted {σ : Type*} :
    (⊥ : Ideal (PowerSeries.IsRestricted.subring (R := Tate σ) 1)).jacobson = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ (Ideal.mem_bot).mpr ?_
  by_contra hf0
  obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k (f : PowerSeries (Tate σ)) ≠ 0 := by
    by_contra! h
    exact hf0 (Subtype.ext (PowerSeries.ext fun k ↦ by simpa using h k))
  set r : Tate σ := PowerSeries.coeff k (f : PowerSeries (Tate σ))
  obtain ⟨t, ht⟩ : ∃ t, coeff t (r : MvPowerSeries σ K) ≠ 0 := by
    by_contra! h
    exact hk (Subtype.ext (MvPowerSeries.ext fun t ↦ by simpa using h t))
  set b := coeff t (r : MvPowerSeries σ K)
  let a : Tate σ := algebraMap K (Tate σ) b⁻¹
  let y : PowerSeries.IsRestricted.subring (R := Tate σ) 1 :=
    ⟨PowerSeries.C a * PowerSeries.X, (PowerSeries.isRestricted_C 1 a).mul
      (PowerSeries.X_eq (R := Tate σ) ▸ PowerSeries.isRestricted_monomial 1 1 1)⟩
  have hd := PowerSeries.isDistinguished_zero_of_isUnit zero_lt_one
    ((Ideal.mem_jacobson_bot.mp hf) y)
  -- The constant coefficient of `1 + f * a Y` is `1`, and its coefficient in degree `k + 1`
  -- is `r * a`, whose coefficient at `t` is `b * b⁻¹ = 1`.
  have h0 : PowerSeries.coeff 0 ((f * y + 1 : PowerSeries.IsRestricted.subring (R := Tate σ) 1) :
      PowerSeries (Tate σ)) = 1 := by
    simp [y]
  have h1 : PowerSeries.coeff (k + 1)
      ((f * y + 1 : PowerSeries.IsRestricted.subring (R := Tate σ) 1) : PowerSeries (Tate σ)) =
      r * a := by
    simp [y, r, ← mul_assoc, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
  have hn : 1 ≤ ‖r * a‖ := by
    have h := norm_coeff_mul_prod_le (r * a) t
    simpa [a, coe_algebraMap_isRestrictedSubring, b, ht] using h
  have hlt := hd.norm_coeff_mul_pow_lt (k + 1) k.succ_pos
  rw [← hd.norm_coeff_mul_pow_eq, h0, h1] at hlt
  simp only [one_pow, mul_one, norm_one] at hlt
  exact hlt.not_ge hn

variable [CompleteSpace K]

/-- The inductive step: if the Tate algebra `K⟨X⟩` is Jacobson, so is `K⟨X, Y⟩`. -/
private theorem isJacobsonRing_option {σ : Type*} [Finite σ] [IsJacobsonRing (Tate σ)] :
    IsJacobsonRing (Tate (Option σ)) := by
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let Φ : Tate (Option σ) ≃+* S := Huber.restrictedOptionEquiv
  refine isJacobsonRing_of_quotient_span_singleton ?_ fun f hf ↦ ?_
  · -- Transport the vanishing of the Jacobson radical along `Φ`.
    refine eq_bot_iff.mpr fun g hg ↦ (Ideal.mem_bot).mpr <| Φ.injective ?_
    rw [map_zero, ← Ideal.mem_bot, ← jacobson_bot_restricted]
    refine Ideal.mem_jacobson_bot.mpr fun z ↦ ?_
    simpa using (Ideal.mem_jacobson_bot.mp hg (Φ.symm z)).map Φ
  · -- Make `f` distinguished in `Y`; then `S ⧸ (Φ (e f))` is finite over `R`.
    obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit f hf
    have := hd.finite_quotient zero_lt_one hu
    have : Algebra.IsIntegral R (S ⧸ Ideal.span {Φ (e f)}) := Algebra.IsIntegral.of_finite R _
    have : IsJacobsonRing (S ⧸ Ideal.span {Φ (e f)}) :=
      isJacobsonRing_of_isIntegral (R := R)
    let E : Tate (Option σ) ≃+* S := (e : Tate (Option σ) ≃+* Tate (Option σ)).trans Φ
    exact (isJacobsonRing_iso (Ideal.quotientEquiv _ _ E (by simp [Ideal.map_span, E]))).mpr this

/-- **Tate algebras are Jacobson rings.** Over a complete nonarchimedean field `K`, every prime
ideal of the Tate algebra `K⟨X₁, …, Xₙ⟩` in finitely many variables is the intersection of the
maximal ideals containing it. -/
instance isJacobsonRing {σ : Type*} [Finite σ] : IsJacobsonRing (Tate σ) := by
  refine Finite.induction_empty_option (P := fun σ ↦ IsJacobsonRing (Tate σ))
    (fun {α β} e _ ↦ ?_) ?_ (fun _ ↦ isJacobsonRing_option) σ
  · -- Renaming the variables along `e : α ≃ β` is a ring isomorphism of Tate algebras.
    exact (isJacobsonRing_iso (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1).toRingEquiv).mp
      ‹_›
  · -- Without variables every series is a constant, so the Tate algebra is a quotient of `K`.
    exact isJacobsonRing_of_surjective
      ⟨algebraMap K (Tate PEmpty), algebraMap_isRestrictedSubring_surjective⟩

end TauCeti.MvPowerSeries
