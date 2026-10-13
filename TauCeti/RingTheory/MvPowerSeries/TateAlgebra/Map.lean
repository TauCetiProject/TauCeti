/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Sum

/-!
# Restricted series along a strict surjection

A bounded ring homomorphism `φ : R → S` of ultrametric normed rings, `‖φ r‖ ≤ C ‖r‖`, maps
restricted series to restricted series coefficientwise, giving a ring homomorphism
`R{X/c} → S{X/c}`. If `φ` is moreover *strictly* surjective, that is, every `s ∈ S` lifts to some
`r` with `‖r‖ ≤ C' ‖s‖`, then lifting every coefficient shows that `R{X/c} → S{X/c}` is
surjective. The norm control is what makes the lifted coefficients still tend to zero.

Combined with the identification `R{X/c, Y/d} ≅ R{Y/d}{X/c}` of
`TauCeti.MvPowerSeries.restrictedSumEquiv`, this gives the form in which noetherianity passes to
restricted series over a strict quotient of a ring of restricted series: if
`ψ : R{Y/d} → S` is bounded and strictly surjective and `R{X/c, Y/d}` is noetherian, then
`S{X/c}` is noetherian, being a quotient of `R{Y/d}{X/c} ≅ R{X/c, Y/d}`. This is how Kedlaya
deduces the noetherianity of `B^I{X/c}` for the interval rings `B^I` of the Fargues–Fontaine
curve from that of restricted series over the radius rings `A^r` (Kedlaya, Theorem 3.2), through
presentations of `B^I` as strict quotients of `A^r{Y}` (Kedlaya, Lemma 4.9).

## Main definitions

* `TauCeti.MvPowerSeries.restrictedMap`: the coefficientwise map `R{X/c} →+* S{X/c}` induced by
  a bounded ring homomorphism `R →+* S`.

## Main results

* `MvPowerSeries.IsRestricted.map`: a bounded ring homomorphism preserves restrictedness, at
  arbitrary polyradii.
* `TauCeti.MvPowerSeries.restrictedMap_id` and `TauCeti.MvPowerSeries.restrictedMap_comp`:
  `restrictedMap` is functorial.
* `TauCeti.MvPowerSeries.norm_restrictedMap_le`: `restrictedMap` is bounded by the same constant.
* `TauCeti.MvPowerSeries.restrictedMap_surjective`: a strictly surjective `φ` induces a
  surjection `R{X/c} → S{X/c}`.
* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_surjective`: if `R{X/c}` is
  noetherian, so is `S{X/c}`.
* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_surjective_of_sumElim`: if
  `ψ : R{Y/d} → S` is bounded and strictly surjective and `R{X/c, Y/d}` is noetherian, then
  `S{X/c}` is noetherian.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Theorem 3.2, Lemma 4.9, Theorem 4.10 and Remark 4.11.
-/

public section

namespace MvPowerSeries

open Filter

variable {σ R S : Type*} [NormedRing R] [NormedRing S] {c : σ → ℝ}

/-- A bounded ring homomorphism `φ`, `‖φ r‖ ≤ C ‖r‖`, maps restricted series to restricted series
coefficientwise. -/
theorem IsRestricted.map {f : MvPowerSeries σ R} (hf : IsRestricted c f) (φ : R →+* S) {C : ℝ}
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) : IsRestricted c (MvPowerSeries.map φ f) := by
  rw [← isRestricted_abs_iff] at hf ⊢
  have h := hf.const_mul C
  rw [mul_zero] at h
  refine squeeze_zero (fun t ↦ mul_nonneg (norm_nonneg _) (prod_abs_pow_nonneg t)) (fun t ↦ ?_) h
  rw [coeff_map, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hφ _) (prod_abs_pow_nonneg t)

end MvPowerSeries

namespace TauCeti.MvPowerSeries

open Filter _root_.MvPowerSeries
open scoped Topology

section Map

variable {σ R S : Type*} [NormedRing R] [IsUltrametricDist R] [NormedRing S] [IsUltrametricDist S]
  {c : σ → ℝ} (φ : R →+* S) {C : ℝ} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)

/-- **The coefficientwise map `R{X/c} →+* S{X/c}`** induced by a bounded ring homomorphism
`φ : R →+* S`, `‖φ r‖ ≤ C ‖r‖`. -/
noncomputable def restrictedMap :
    IsRestricted.subring (R := R) c →+* IsRestricted.subring (R := S) c :=
  ((MvPowerSeries.map φ).comp (IsRestricted.subring (R := R) c).subtype).codRestrict _
    fun f ↦ f.2.map φ hφ

/-- `restrictedMap` acts as `MvPowerSeries.map` on the underlying series. -/
theorem coe_restrictedMap (f : IsRestricted.subring (R := R) c) :
    (restrictedMap φ hφ f : MvPowerSeries σ S) = MvPowerSeries.map φ f := (rfl)

/-- `restrictedMap` acts on each coefficient by `φ`. -/
@[simp]
theorem coeff_restrictedMap (f : IsRestricted.subring (R := R) c) (t : σ →₀ ℕ) :
    coeff t (restrictedMap φ hφ f : MvPowerSeries σ S) = φ (coeff t (f : MvPowerSeries σ R)) := by
  rw [coe_restrictedMap, coeff_map]

/-- The identity induces the identity on restricted series. -/
@[simp]
theorem restrictedMap_id {C : ℝ} (hC : ∀ r : R, ‖RingHom.id R r‖ ≤ C * ‖r‖) :
    restrictedMap (c := c) (RingHom.id R) hC = RingHom.id _ :=
  RingHom.ext fun _ ↦ Subtype.ext <| MvPowerSeries.ext fun _ ↦ by simp

/-- The map induced by a composite is the composite of the induced maps. -/
theorem restrictedMap_comp {T : Type*} [NormedRing T] [IsUltrametricDist T] (ψ : S →+* T)
    {C₂ C₃ : ℝ} (hψ : ∀ s, ‖ψ s‖ ≤ C₂ * ‖s‖) (hψφ : ∀ r, ‖ψ.comp φ r‖ ≤ C₃ * ‖r‖) :
    restrictedMap (c := c) (ψ.comp φ) hψφ = (restrictedMap ψ hψ).comp (restrictedMap φ hφ) :=
  RingHom.ext fun _ ↦ Subtype.ext <| MvPowerSeries.ext fun _ ↦ by simp

/-- Applying two induced maps in turn is applying the map induced by the composite. -/
@[simp]
theorem restrictedMap_restrictedMap {T : Type*} [NormedRing T] [IsUltrametricDist T]
    (ψ : S →+* T) {C₂ : ℝ} (hψ : ∀ s, ‖ψ s‖ ≤ C₂ * ‖s‖) (f : IsRestricted.subring (R := R) c) :
    restrictedMap ψ hψ (restrictedMap φ hφ f) =
      restrictedMap (ψ.comp φ) (C := max C₂ 0 * C) (fun r ↦ by
        rw [mul_assoc]
        exact (hψ (φ r)).trans <| (mul_le_mul_of_nonneg_right (le_max_left C₂ 0)
          (norm_nonneg _)).trans <| mul_le_mul_of_nonneg_left (hφ r) (le_max_right C₂ 0)) f :=
  Subtype.ext <| MvPowerSeries.ext fun _ ↦ by simp

/-- `restrictedMap` does not increase the Gauss norm by more than the bound on `φ`. -/
theorem norm_restrictedMap_le [∀ i, Fact (0 < c i)] (hC : 0 ≤ C)
    (f : IsRestricted.subring (R := R) c) :
    ‖restrictedMap φ hφ f‖ ≤ C * ‖f‖ := by
  rw [norm_le_iff (mul_nonneg hC (norm_nonneg f))]
  intro t
  rw [coeff_restrictedMap]
  exact (mul_le_mul_of_nonneg_right (hφ _) (prod_pow_pos t).le).trans
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le f t) hC)

/-- **Restricted series along a strict surjection.** If every `s ∈ S` lifts along `φ` to some
`r` with `‖r‖ ≤ C' ‖s‖`, then every restricted series over `S` lifts coefficientwise to a
restricted series over `R`, so `R{X/c} → S{X/c}` is surjective. -/
theorem restrictedMap_surjective {C' : ℝ} (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖) :
    Function.Surjective (restrictedMap (c := c) φ hφ) := by
  intro g
  choose r hr hrn using hlift
  have hg := ((isRestricted_abs_iff c _).mpr g.2).const_mul C'
  rw [mul_zero] at hg
  -- the coefficientwise lift of `g`
  let f : MvPowerSeries σ R := fun t ↦ r (coeff t (g : MvPowerSeries σ S))
  have hcoeff (t : σ →₀ ℕ) : coeff t f = r (coeff t (g : MvPowerSeries σ S)) := (rfl)
  have hf : IsRestricted c f := by
    rw [← isRestricted_abs_iff]
    refine squeeze_zero (fun t ↦ mul_nonneg (norm_nonneg _) (prod_abs_pow_nonneg t))
      (fun t ↦ ?_) hg
    rw [hcoeff, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hrn _) (prod_abs_pow_nonneg t)
  refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
  ext t
  rw [coeff_restrictedMap, hcoeff]
  exact hr _

end Map

section Noetherian

variable {σ τ R S : Type*} {c : σ → ℝ}

/-- **Noetherianity of restricted series passes along a strict surjection.** If `φ : R →+* S` is
bounded and every `s ∈ S` lifts to some `r` with `‖r‖ ≤ C' ‖s‖`, then `S{X/c}` is noetherian
whenever `R{X/c}` is. -/
theorem isNoetherianRing_isRestricted_subring_of_surjective [NormedRing R] [IsUltrametricDist R]
    [NormedRing S] [IsUltrametricDist S] (φ : R →+* S) {C C' : ℝ}
    (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (hlift : ∀ s, ∃ r, φ r = s ∧ ‖r‖ ≤ C' * ‖s‖)
    [IsNoetherianRing (IsRestricted.subring (R := R) c)] :
    IsNoetherianRing (IsRestricted.subring (R := S) c) :=
  isNoetherianRing_of_surjective _ _ (restrictedMap φ hφ) (restrictedMap_surjective φ hφ hlift)

/-- **Restricted series over a strict quotient of a ring of restricted series.** Let
`ψ : R{Y/d} → S` be a bounded ring homomorphism such that every `s ∈ S` lifts to some `f` with
`‖f‖ ≤ C' ‖s‖`. If the ring `R{X/c, Y/d}` of restricted series in both families of variables is
noetherian, then so is `S{X/c}`: it is a quotient of `R{Y/d}{X/c} ≅ R{X/c, Y/d}`. -/
theorem isNoetherianRing_isRestricted_subring_of_surjective_of_sumElim [NormedCommRing R]
    [IsUltrametricDist R] [NormedRing S] [IsUltrametricDist S] [∀ i, Fact (0 < c i)] {d : τ → ℝ}
    [∀ j, Fact (0 < d j)] (ψ : IsRestricted.subring (R := R) d →+* S) {C C' : ℝ}
    (hψ : ∀ f, ‖ψ f‖ ≤ C * ‖f‖) (hlift : ∀ s, ∃ f, ψ f = s ∧ ‖f‖ ≤ C' * ‖s‖)
    [IsNoetherianRing (IsRestricted.subring (R := R) (Sum.elim c d))] :
    IsNoetherianRing (IsRestricted.subring (R := S) c) :=
  have : IsNoetherianRing (IsRestricted.subring (R := IsRestricted.subring (R := R) d) c) :=
    isNoetherianRing_of_ringEquiv _ restrictedSumEquiv
  isNoetherianRing_isRestricted_subring_of_surjective ψ hψ hlift

end Noetherian

end TauCeti.MvPowerSeries
