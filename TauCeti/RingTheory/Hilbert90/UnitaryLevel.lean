/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import TauCeti.RingTheory.Hilbert90.Profinite
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Hilbert's Theorem 90 for unitary matrices at a congruence level and common-divisor descent

This file builds on `TauCeti.RingTheory.Hilbert90.TameLevel` and
`TauCeti.RingTheory.Hilbert90.Profinite` to supply three algebraic steps for Hilbert's Theorem 90
on unitary groups over profinite rings and on finite ideles:

* `TauCeti.TameHilbert90.exists_adjoinRoot_map_comp`: if a polynomial `Q : O[X]` divides
  `(Q.map g).comp s`, then `q ↦ (q.map g).comp s` descends to an endomorphism of `AdjoinRoot Q`.
* `TauCeti.TameHilbert90.exists_unitary_mul_map_eq_of_twistedNorm_eq_one_of_isProfiniteRing`:
  over a profinite star-ring `O`, given fixed orthonormal frames for invertible `τ`-fixed
  hermitian matrices, a unitary cocycle `s ≡ 1 [mod m]` of twisted norm `1` splits as
  `s * τ g = g` for a unitary matrix `g ≡ 1 [mod m]`.
* `TauCeti.TameHilbert90.exists_unit_mul_eq_of_dvd_common`: in any commutative `L`-algebra `A`
  with a finite-order `σ`-semilinear endomorphism `φ` (`σ : L ≃ₐ[K] L`), if every pair of
  solutions to `u * φ x = x` admits a common divisor that is again a solution, then a unit
  solution exists.

## Provenance

Adapted from `New.exists_adjoinRoot_map_comp`, `New.unitary_hilbert90_at_level`, and
`New.hilbert90_finite_idele` in `grh/src/Lib/GaloisRep/Hilbert90/UnitaryGroups.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), commit
`72fead102f663d5c7a407964a13dc0cf9d977207` (Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti.TameHilbert90

open Matrix Polynomial

/-- If `g : O →+* O` and `s : O[X]` satisfy `Q ∣ (Q.map g).comp s`, then `q ↦ (q.map g).comp s`
descends to a ring endomorphism of `AdjoinRoot Q`. -/
theorem exists_adjoinRoot_map_comp {O : Type*} [CommRing O] {Q : O[X]} (g : O →+* O) (s : O[X])
    (hs : Q ∣ (Q.map g).comp s) :
    ∃ θ : AdjoinRoot Q →+* AdjoinRoot Q, ∀ q : O[X],
      θ (AdjoinRoot.mk Q q) = AdjoinRoot.mk Q ((q.map g).comp s) := by
  have h_le : _root_.Ideal.span {Q} ≤
      (_root_.Ideal.span {Q}).comap (s.compRingHom.comp (mapRingHom g)) := by
    simpa [_root_.Ideal.mem_span_singleton] using hs
  exact ⟨_root_.Ideal.quotientMap _ _ h_le, fun _ ↦ _root_.Ideal.quotientMap_mk⟩

/-- Reduction of unitary Hilbert 90 at level `m` over a profinite star-ring `O` to `GL_n`
Hilbert 90 and existence of `τ`-fixed orthonormal frames for invertible `τ`-fixed hermitian
matrices. -/
theorem exists_unitary_mul_map_eq_of_twistedNorm_eq_one_of_isProfiniteRing
    {O n : Type*} [CommRing O] [StarRing O] [IsProfiniteRing O] [Fintype n] [DecidableEq n]
    {τ : O →+* O} {p : ℕ} {m : O} (h_tame : IsTameAtLevel τ p m)
    (hm_star : star m = m) (hτ_star : ∀ x : O, τ (star x) = star (τ x))
    (h_frame : ∀ h : Matrix n n O, IsUnit h → hᴴ = h → h.map τ = h →
      ∃ g V : Matrix n n O, g = 1 + V * (h - 1) ∧ g.map τ = g ∧ gᴴ * h * g = 1)
    (s : GL n O) (hs_unitary : s.valᴴ * s.val = 1) {Y : Matrix n n O}
    (hs : s.val = 1 + m • Y)
    (hs_norm : MonoidHom.twistedNorm (GeneralLinearGroup.map τ) p s = 1) :
    ∃ (g : GL n O) (W : Matrix n n O),
      g.valᴴ * g.val = 1 ∧ s * GeneralLinearGroup.map τ g = g ∧ g.val = 1 + m • W := by
  obtain ⟨k, W, hk_cob, hk⟩ :=
    h_tame.exists_mul_map_eq_of_twistedNorm_eq_one_of_isProfiniteRing s hs hs_norm
  have h_cob : s.val * k.val.map τ = k.val := congrArg Units.val hk_cob
  have h_map_conj (M : Matrix n n O) : (M.map τ)ᴴ = Mᴴ.map τ := by
    ext i j
    simp [Matrix.conjTranspose_apply, hτ_star]
  have h_fix : (k.valᴴ * k.val).map τ = k.valᴴ * k.val := by
    rw [Matrix.map_mul, ← h_map_conj]
    calc (k.val.map τ)ᴴ * k.val.map τ
        = (k.val.map τ)ᴴ * (s.valᴴ * s.val) * k.val.map τ := by rw [hs_unitary, mul_one]
      _ = (s.val * k.val.map τ)ᴴ * (s.val * k.val.map τ) := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = k.valᴴ * k.val := by rw [h_cob]
  have hkk_unit : IsUnit (k.valᴴ * k.val) :=
    (isUnit_iff_exists_inv.mpr ⟨(k⁻¹).valᴴ, by
      rw [← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]⟩).mul k.isUnit
  have hkk_herm : (k.valᴴ * k.val)ᴴ = k.valᴴ * k.val := by simp
  obtain ⟨u, V, hu, hu_fix, hu_frame⟩ := h_frame (k.valᴴ * k.val) hkk_unit hkk_herm h_fix
  have h_ku_unitary : (k.val * u)ᴴ * (k.val * u) = 1 := by
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hu_frame
  have h_ku_unit : IsUnit (k.val * u) :=
    isUnit_iff_exists_inv.mpr ⟨(k.val * u)ᴴ, mul_eq_one_comm.mp h_ku_unitary⟩
  have h_lev : k.valᴴ * k.val - 1 = m • (W + Wᴴ * k.val) := by
    have h_kH : k.valᴴ = 1 + m • Wᴴ := by
      rw [hk, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
        hm_star]
    rw [h_kH, add_mul, one_mul, smul_mul_assoc, hk, add_assoc, add_sub_cancel_left, ← smul_add]
  refine ⟨h_ku_unit.unit, W + k.val * V * (W + Wᴴ * k.val), h_ku_unitary, ?_, ?_⟩
  · apply Units.ext
    change s.val * (k.val * u).map τ = k.val * u
    rw [Matrix.map_mul, hu_fix, ← Matrix.mul_assoc, h_cob]
  · change k.val * u = 1 + m • (W + k.val * V * (W + Wᴴ * k.val))
    calc k.val * u = k.val + m • (k.val * V * (W + Wᴴ * k.val)) := by
          rw [hu, mul_add, mul_one, h_lev, mul_smul_comm, mul_smul_comm, Matrix.mul_assoc]
      _ = 1 + m • (W + k.val * V * (W + Wᴴ * k.val)) := by rw [smul_add, ← add_assoc, ← hk]

/-- Galois-descent Hilbert 90 in a commutative `L`-algebra `A`: if `σ : L ≃ₐ[K] L` has finite
order `n`, `φ : A →+* A` is `σ`-semilinear, `x ↦ u * φ x` has period `n`, and any two solutions
to `u * φ x = x` have a common divisor that is again a solution, then a unit solution exists. -/
theorem exists_unit_mul_eq_of_dvd_common
    {K L A : Type*} [CommSemiring K] [Field L] [Algebra K L] [CommRing A] [Algebra L A]
    (σ : L ≃ₐ[K] L) (hσ : IsOfFinOrder σ) (φ : A →+* A)
    (hφ : ∀ (r : L) (x : A), φ (algebraMap L A r * x) = algebraMap L A (σ r) * φ x)
    {u : A} (h_period : ∀ x : A, (fun y ↦ u * φ y)^[orderOf σ] x = x)
    (h_common : ∀ a b : A, u * φ a = a → u * φ b = b →
      ∃ c : A, c ∣ a ∧ c ∣ b ∧ u * φ c = c) :
    ∃ c : A, IsUnit c ∧ u * φ c = c := by
  let τ : A →ₛₗ[(σ : L →+* L)] A :=
    { toFun := fun x ↦ u * φ x
      map_add' := fun x y ↦ by rw [map_add, mul_add]
      map_smul' := fun r x ↦ by simp [Algebra.smul_def, hφ, mul_left_comm] }
  obtain ⟨r, hr, h_span⟩ :=
    (σ.isTameAtLevel_orderOf hσ).exists_smul_mem_span_fixedPoints τ h_period ⊥ one_ne_zero
  have h_div : ∀ x ∈ Submodule.span L (Function.fixedPoints τ),
      ∃ c : A, c ∣ x ∧ u * φ c = c := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem c hc => exact ⟨c, dvd_rfl, hc⟩
    | zero => exact ⟨0, dvd_refl 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha_dvd, ha⟩ := hx
      obtain ⟨b, hb_dvd, hb⟩ := hy
      obtain ⟨c, hca, hcb, hc⟩ := h_common a b ha hb
      exact ⟨c, dvd_add (hca.trans ha_dvd) (hcb.trans hb_dvd), hc⟩
    | smul s x _ hx =>
      obtain ⟨c, hc_dvd, hc⟩ := hx
      exact ⟨c, by rw [Algebra.smul_def]; exact hc_dvd.mul_left _, hc⟩
  have h_one : (1 : A) ∈ Submodule.span L (Function.fixedPoints τ) := by
    simpa [smul_smul, _root_.Ideal.mem_bot.not.mp hr] using h_span (r⁻¹ • 1)
  obtain ⟨c, hc_dvd, hc⟩ := h_div 1 h_one
  exact ⟨c, isUnit_of_dvd_one hc_dvd, hc⟩

end TauCeti.TameHilbert90
