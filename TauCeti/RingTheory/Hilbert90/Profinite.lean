/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Hilbert90.TameLevel
public import TauCeti.RingTheory.ProfiniteRing
import Mathlib.Algebra.BigOperators.Pi
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Hilbert's Theorem 90 at a congruence level over profinite rings

Let `R` be a profinite ring (`TauCeti.IsProfiniteRing R`) and `σ : R →+* R` tame at level `m`
with exponent `p` (`TauCeti.TameHilbert90.IsTameAtLevel σ p m`). This file extends the three
statements of `TauCeti.RingTheory.Hilbert90.TameLevel` from Artinian and finite rings to `R`:

* `TauCeti.TameHilbert90.IsTameAtLevel.exists_mul_map_eq_of_twistedNorm_eq_one_of_isProfiniteRing`:
  if `c : GL n R` satisfies `c = 1 + m • Y` and has twisted norm `1`, then `c * σ k = k` for some
  `k : GL n R` with `k = 1 + m • W`.
* `TauCeti.TameHilbert90.IsTameAtLevel.exists_mul_map_eq_of_prod_eq_one_of_isProfiniteRing`:
  if a unit `x ≡ 1 [mod m]` has orbit product `1`, then `x * σ g = g` for a unit `g ≡ 1 [mod m]`.
* `TauCeti.TameHilbert90.IsTameAtLevel.exists_prod_range_pow_eq_of_isProfiniteRing`: a `σ`-fixed
  unit `x ≡ 1 [mod m]` is the orbit product of a unit `z` with `z ≡ 1` and `z⁻¹ ≡ 1 [mod m]`.

The quotients `R ⧸ N! R` are finite (`TauCeti.IsProfiniteRing.finite_quotient`), hence Artinian,
and tameness passes to them (`TauCeti.TameHilbert90.IsTameAtLevel.quotientMap`). A solution over
each quotient gives a solution over the product of the quotients, and the ring homomorphism
`TauCeti.IsProfiniteRing.ultralimRingHom` from that product to `R` carries it to a solution over
`R`: it retracts the diagonal and commutes with `σ`.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §1.
* P. Scholze, *The Langlands–Kottwitz approach for some simple Shimura varieties*, Invent. Math.
  192 (2013), Lemma 2.2.
* The reduction of the profinite case to the finite quotients follows L. Alpöge and L. Sernau,
  Lean formalization of the Riemann Hypothesis for Dirichlet L-functions
  (`https://github.com/lsernau/grh-lean`, commit `72fead1`),
  `grh/src/Lib/GaloisRep/Hilbert90/TameActions.lean` (`New.IsTameAtLevel.hilbert90_gl`,
  `New.IsTameAtLevel.hilbert90_unit`, `New.IsTameAtLevel.exists_prod_range_pow_apply_eq`).
-/

public section

open Finset Matrix TauCeti.IsProfiniteRing

namespace TauCeti.TameHilbert90

variable {R : Type*} [CommRing R] [IsProfiniteRing R] {σ : R →+* R} {p : ℕ} {m : R}

variable (R) in
/-- The ideal `N! R`. -/
private abbrev facIdeal (N : ℕ) : Ideal R := Ideal.span {(N.factorial : R)}

variable (R) in
/-- The quotient `R ⧸ N! R`. -/
private abbrev FacQuot (N : ℕ) : Type _ := R ⧸ facIdeal R N

/-- The reduction map `R → R ⧸ N! R`. -/
private abbrev facMk (N : ℕ) : R →+* FacQuot R N := Ideal.Quotient.mk (facIdeal R N)

/-- The endomorphism of `R ⧸ N! R` induced by `σ`. -/
private noncomputable abbrev quotSigma (σ : R →+* R) (N : ℕ) : FacQuot R N →+* FacQuot R N :=
  Ideal.quotientMap _ σ Ideal.span_natCast_le_comap

private theorem isArtinianRing_quotient (N : ℕ) : IsArtinianRing (FacQuot R N) :=
  have := finite_quotient (R := R) N.factorial_ne_zero
  isArtinian_of_finite

/-- Hilbert's Theorem 90 for `GL n` over each quotient `R ⧸ N! R`. -/
private theorem exists_mul_map_eq_of_twistedNorm_eq_one_quotient {n : Type*} [Fintype n]
    [DecidableEq n] (h_tame : IsTameAtLevel σ p m) (c : GL n R) {Y : Matrix n n R}
    (hY : c.val = 1 + m • Y) (hc : MonoidHom.twistedNorm (GeneralLinearGroup.map σ) p c = 1)
    (N : ℕ) :
    ∃ k : GL n (FacQuot R N), ∃ W : Matrix n n (FacQuot R N),
      GeneralLinearGroup.map (facMk N) c * GeneralLinearGroup.map (quotSigma σ N) k = k ∧
        k.val = 1 + facMk N m • W := by
  have := isArtinianRing_quotient (R := R) N
  refine (h_tame.quotientMap _ _).exists_mul_map_eq_of_twistedNorm_eq_one _
    (Y := Y.map (facMk N)) ?_ ?_
  · ext i j
    simp [hY, Matrix.one_apply, apply_ite (facMk N)]
  · rw [← MonoidHom.map_twistedNorm (GeneralLinearGroup.map (facMk N))
      (τ := GeneralLinearGroup.map σ) (τ' := GeneralLinearGroup.map (quotSigma σ N))
      (fun g ↦ by ext i j; simp [Ideal.quotientMap_mk]), hc, map_one]

/-- **Hilbert's Theorem 90 for `GL n` at congruence level `m` over a profinite ring.** If `σ` is
tame at level `m` with exponent `p` and `c : GL n R` satisfies `c.val = 1 + m • Y` and
`MonoidHom.twistedNorm (GeneralLinearGroup.map σ) p c = 1`, then
`c * GeneralLinearGroup.map σ k = k` for some `k : GL n R` with `k.val = 1 + m • W`. -/
theorem IsTameAtLevel.exists_mul_map_eq_of_twistedNorm_eq_one_of_isProfiniteRing {n : Type*}
    [Fintype n] [DecidableEq n] (h_tame : IsTameAtLevel σ p m) (c : GL n R) {Y : Matrix n n R}
    (hY : c.val = 1 + m • Y) (hc : MonoidHom.twistedNorm (GeneralLinearGroup.map σ) p c = 1) :
    ∃ k : GL n R, ∃ W : Matrix n n R,
      c * GeneralLinearGroup.map σ k = k ∧ k.val = 1 + m • W := by
  choose k W hk hW using exists_mul_map_eq_of_twistedNorm_eq_one_quotient h_tame c hY hc
  -- Assemble the solutions over the quotients into one over their product, and map it to `R`.
  let Λ : (∀ N, FacQuot R N) →+* R := ultralimRingHom
  let δ : R →+* ∀ N, FacQuot R N := RingHom.pi fun N ↦ facMk N
  let σP : (∀ N, FacQuot R N) →+* ∀ N, FacQuot R N :=
    RingHom.pi fun N ↦ (quotSigma σ N).comp (Pi.evalRingHom (FacQuot R) N)
  let kP : GL n (∀ N, FacQuot R N) := (GeneralLinearGroup.piEquiv (FacQuot R)).symm k
  have h_eval (N : ℕ) : GeneralLinearGroup.map (Pi.evalRingHom (FacQuot R) N) kP = k N := by
    simpa only [GeneralLinearGroup.piEquiv_apply_eq_map_eval] using
      congrFun ((GeneralLinearGroup.piEquiv (FacQuot R)).apply_symm_apply k) N
  have hkP : GeneralLinearGroup.map δ c * GeneralLinearGroup.map σP kP = kP := by
    refine (GeneralLinearGroup.piEquiv (FacQuot R)).injective (funext fun N ↦ ?_)
    have h_δ : (Pi.evalRingHom (FacQuot R) N).comp δ = facMk N := RingHom.ext fun _ ↦ by simp [δ]
    have h_σ : (Pi.evalRingHom (FacQuot R) N).comp σP =
        (quotSigma σ N).comp (Pi.evalRingHom (FacQuot R) N) := RingHom.ext fun _ ↦ by simp [σP]
    simp only [GeneralLinearGroup.piEquiv_apply_eq_map_eval, map_mul]
    simp only [← GeneralLinearGroup.map_comp_apply, ← GeneralLinearGroup.map_comp, h_δ, h_σ]
    simp only [GeneralLinearGroup.map_comp, GeneralLinearGroup.map_comp_apply, h_eval, hk]
  have hΛδ : Λ.comp δ = RingHom.id R := RingHom.ext ultralimRingHom_mk
  have hΛσ : Λ.comp σP = σ.comp Λ := RingHom.ext fun a ↦ (RingHom.map_ultralimRingHom σ a).symm
  let WP : Matrix n n (∀ N, FacQuot R N) := Matrix.of fun i j N ↦ W N i j
  refine ⟨GeneralLinearGroup.map Λ kP, WP.map Λ, ?_, ?_⟩
  · simpa only [map_mul, ← GeneralLinearGroup.map_comp_apply, ← GeneralLinearGroup.map_comp,
      hΛδ, hΛσ, GeneralLinearGroup.map_id, MonoidHom.id_apply] using
      congrArg (GeneralLinearGroup.map Λ) hkP
  · ext i j
    have h_kP : kP i j = (1 : Matrix n n (∀ N, FacQuot R N)) i j + δ m * WP i j := by
      funext N
      have h_entry : (1 + facMk N m • W N) i j = (k N : Matrix n n (FacQuot R N)) i j := by
        rw [hW N]
      rw [← h_eval N, GeneralLinearGroup.map_apply, Pi.evalRingHom_apply] at h_entry
      rw [← h_entry]
      simp [Matrix.one_apply, apply_ite (fun f : ∀ N, FacQuot R N ↦ f N), δ, WP]
    rw [GeneralLinearGroup.map_apply, h_kP, map_add, map_mul, ← RingHom.comp_apply Λ δ, hΛδ]
    simp [Matrix.one_apply, apply_ite Λ, WP]

/-- **Hilbert's Theorem 90 for units at congruence level `m` over a profinite ring.** If `σ` is
tame at level `m` with exponent `p` and `x : Rˣ` satisfies `m ∣ (x : R) - 1` and
`∏ i ∈ range p, (σ ^ i) x = 1`, then `x * Units.map (σ : R →* R) g = g` for some `g : Rˣ` with
`m ∣ (g : R) - 1`. -/
theorem IsTameAtLevel.exists_mul_map_eq_of_prod_eq_one_of_isProfiniteRing
    (h_tame : IsTameAtLevel σ p m) {x : Rˣ} (hx_one : m ∣ (x : R) - 1)
    (hx_norm : ∏ i ∈ range p, (σ ^ i) (x : R) = 1) :
    ∃ g : Rˣ, m ∣ (g : R) - 1 ∧ x * Units.map (σ : R →* R) g = g := by
  have key (N : ℕ) : ∃ g : (FacQuot R N)ˣ, facMk N m ∣ (g : FacQuot R N) - 1 ∧
      facMk N (x : R) * quotSigma σ N g = g := by
    have := isArtinianRing_quotient (R := R) N
    obtain ⟨g, hg_one, hg⟩ :=
      (h_tame.quotientMap _ Ideal.span_natCast_le_comap).exists_mul_map_eq_of_prod_eq_one
        (x := Units.map (facMk (R := R) N : R →* FacQuot R N) x)
        (by simpa using map_dvd (facMk N) hx_one)
        (by
          have h := Ideal.Quotient.mk_prod_range_pow_quotientMap (facIdeal R N) σ
            Ideal.span_natCast_le_comap p (x : R)
          rw [hx_norm, map_one] at h
          simpa using h.symm)
    exact ⟨g, hg_one, by simpa using congrArg Units.val hg⟩
  choose g hg_one hg using key
  let Λ : (∀ N, FacQuot R N) →+* R := ultralimRingHom
  let G : Rˣ := ultralimUnitsHom g
  have hG : (G : R) = Λ fun N ↦ (g N : FacQuot R N) := coe_ultralimUnitsHom g
  refine ⟨G, ?_, Units.ext ?_⟩
  · exact dvd_ultralimUnitsHom_sub_one hg_one
  · calc ((x * Units.map (σ : R →* R) G : Rˣ) : R)
        = Λ (fun N ↦ facMk N (x : R)) * Λ (fun N ↦ quotSigma σ N (g N)) := by
          rw [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, ultralimRingHom_mk,
            ← RingHom.map_ultralimRingHom, ← hG]
      _ = G := by rw [← map_mul, hG]; exact congrArg Λ (funext hg)

/-- **Surjectivity of the orbit product on `σ`-fixed units at congruence level `m` over a profinite
ring.** If `σ` is tame at level `m` with exponent `p` and `x : Rˣ` is `σ`-fixed with
`m ∣ (x : R) - 1`, then `x = ∏ i ∈ range p, (σ ^ i) z` for a unit `z : Rˣ` with
`m ∣ (z : R) - 1` and `m ∣ ((z⁻¹ : Rˣ) : R) - 1`. -/
theorem IsTameAtLevel.exists_prod_range_pow_eq_of_isProfiniteRing (h_tame : IsTameAtLevel σ p m)
    {x : Rˣ} (hσx : σ x = x) (hx_one : m ∣ (x : R) - 1) :
    ∃ z : Rˣ, m ∣ (z : R) - 1 ∧ m ∣ ((z⁻¹ : Rˣ) : R) - 1 ∧
      ∏ i ∈ range p, (σ ^ i) (z : R) = x := by
  have key (N : ℕ) : ∃ z : (FacQuot R N)ˣ, facMk N m ∣ (z : FacQuot R N) - 1 ∧
      facMk N m ∣ ((z⁻¹ : (FacQuot R N)ˣ) : FacQuot R N) - 1 ∧
      ∏ i ∈ range p, (quotSigma σ N)^[i] (z : FacQuot R N) = facMk N (x : R) := by
    have := finite_quotient (R := R) N.factorial_ne_zero
    obtain ⟨z, hz_one, hz_inv, hz⟩ :=
      (h_tame.quotientMap _ Ideal.span_natCast_le_comap).exists_prod_range_pow_eq_of_finite
        (x := Units.map (facMk (R := R) N : R →* FacQuot R N) x)
        (by simpa [Ideal.quotientMap_mk] using congrArg (facMk N) hσx)
        (by simpa using map_dvd (facMk N) hx_one)
    exact ⟨z, hz_one, hz_inv, by simpa using hz⟩
  choose z hz_one hz_inv hz using key
  let Λ : (∀ N, FacQuot R N) →+* R := ultralimRingHom
  let Z : Rˣ := ultralimUnitsHom z
  have hZ : (Z : R) = Λ fun N ↦ (z N : FacQuot R N) := coe_ultralimUnitsHom z
  refine ⟨Z, ?_, ?_, ?_⟩
  · exact dvd_ultralimUnitsHom_sub_one hz_one
  · simpa only [← Pi.inv_def, map_inv] using dvd_ultralimUnitsHom_sub_one hz_inv
  · calc ∏ i ∈ range p, (σ ^ i) (Z : R)
        = Λ (∏ i ∈ range p, fun N ↦ (quotSigma σ N)^[i] (z N : FacQuot R N)) := by
          simp only [RingHom.coe_pow, hZ, Λ, RingHom.iterate_ultralimRingHom, map_prod]
      _ = Λ (fun N ↦ facMk N (x : R)) := by
          congr 1
          funext N
          rw [Finset.prod_apply, hz N]
      _ = x := ultralimRingHom_mk _

end TauCeti.TameHilbert90
