/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.UniformDerivativeDecay
import Mathlib.Data.Fintype.Order
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Analysis.Polynomial.SymmetricPower
import TauCeti.Analysis.PDE.Vortex.Divisor.JointSmooth
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Moduli

/-!
# Uniform bounds for the normalized plane vortices over compact divisor windows

For lower coefficients `a ∈ ℂᵐ`, `m ≥ 1`, let `P_a` be the monic polynomial with these
coefficients (`TauCeti.Polynomial.monicOfCoeff`), `x_a = TauCeti.Vortex.polynomialVortex P_a` the
plane vortex with zero divisor `P_a`, and `g_a = TauCeti.Vortex.polynomialGauge a` its
end-normalizing polynomial gauge. The normalized vortex `y_a = g_a · x_a` is smooth, and outside a
disc its section is `|α|` times the winding phase `(z / |z|)ᵐ`. Let `x_ref` be a smooth reference
field equal to `(-i m dθ, (z / |z|)ᵐ)` outside a disc (`TauCeti.Vortex.referenceField`).

For one vortex, every derivative of `y_a - x_ref` is `O(exp (-c |z|))` at infinity for every rate
`c < 1 / 2` (`TauCeti.Vortex.isBigO_iteratedFDeriv_sub_referenceField`). This file makes the
constant uniform over every bounded set of coefficients, and so over every compact set of divisors
in `Sym ℂ m`, collisions of zeros included, and over the whole plane:

* `exists_norm_iteratedFDeriv_gaugeTransform_sub_referenceField_le_mul_exp_of_isBounded` and
  `exists_norm_iteratedFDeriv_gaugeTransform_sub_referenceField_le_mul_exp_of_isCompact`: for
  every order `n` and rate `0 ≤ c < 1 / 2` there is `K ≥ 0` with
  `‖Dⁿ (y_a - x_ref) (z)‖ ≤ K exp (-c |z|)` for all `a` in the window and all `z ∈ ℂ`.

Since the reference field has bounded derivatives
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_referenceField_apply_le`), the normalized vortices
have uniformly bounded coordinates with all derivatives of bounded order:

* `exists_norm_iteratedFDeriv_gaugeTransform_apply_le_of_isBounded` and
  `exists_norm_iteratedFDeriv_gaugeTransform_apply_le_of_isCompact`: for every order `k` there is
  `B` with `‖Dⁿ (y_a)ᵢ (z)‖ ≤ B` for every coordinate `i`, every `n ≤ k`, every `a` in the window
  and every `z ∈ ℂ`.

The zeroth-order coefficients of the gauge-fixed operator `L_{y_a}` are built from the
coordinates of `y_a`, so these bounds control the coefficients of `L_{y_a}` uniformly over a
compact window of divisors, as elliptic estimates with window-uniform constants require.

The proof splits the plane. On a disc, `(a, z) ↦ y_a z` is jointly smooth
(`TauCeti.Vortex.contDiff_normalizedVortex_uncurry`), so its spatial
derivatives are bounded on the product of the closure of the window with the disc. Outside the
disc, `y_a - x_ref` is the end trivialization `u⁻¹ · y_a - (0, 1)`, `u` the winding phase, with its
section part multiplied by the reference section (`TauCeti.Vortex.sub_referenceField_apply_eq`);
the end trivialization decays uniformly over the window
(`exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded`), and the
reference section has bounded derivatives, so the Leibniz rule gives the bound
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_sub_referenceField_le_mul`).

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Metric Set
open TauCeti.Polynomial
open scoped ContDiff _root_.Polynomial

/-! ### Uniform decay of the normalized vortices -/

/-- **Uniform decay of the normalized vortices over a bounded window of coefficients.** Let
`m ≥ 1`, and for lower coefficients `a ∈ ℂᵐ` let `y_a = g_a · x_a` be the plane vortex whose zero
divisor is the monic polynomial `P_a` with these coefficients, normalized at its end by the
polynomial gauge `g_a`. For every bounded set `S` of coefficients, order `n` and rate
`0 ≤ c < 1 / 2` there is `K ≥ 0` such that `‖Dⁿ (y_a - x_ref) (z)‖ ≤ K exp (-c |z|)` for every
`a ∈ S` and every `z ∈ ℂ`. -/
theorem exists_norm_iteratedFDeriv_gaugeTransform_sub_referenceField_le_mul_exp_of_isBounded
    {m : ℕ} (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) {S : Set (Fin m → ℂ)}
    (hS : Bornology.IsBounded S) (n : ℕ) {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K, 0 ≤ K ∧ ∀ a ∈ S, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (gaugeTransform (polynomialGauge a)
          (polynomialVortex (monicOfCoeff a)) - referenceField f m) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  set y : (Fin m → ℂ) → ℂ → EuclideanSpace ℝ (Fin 4) := fun a ↦
    gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a))
  have hY : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ y p.1 p.2 :=
    by simpa only [normalizedVortex_def] using contDiff_normalizedVortex_uncurry
  -- Outside a disc: the end trivialization decays uniformly, with one constant for all orders
  -- at most `n`.
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_sub_referenceField_le_mul f m n
  choose K R _ h using fun i : Fin (n + 1) ↦
    exists_norm_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField_le_mul_exp_of_isBounded hm hS i
      hc₀ hc
  obtain ⟨K₁, hK₁⟩ := Finite.exists_le K
  obtain ⟨R₁, hR₁⟩ := Finite.exists_le R
  set R₂ := max (f.rOut + 1) R₁
  -- On the disc of radius `R₂`: joint smoothness in the coefficients and the point.
  have hYr : ContDiff ℝ ∞ (Function.uncurry fun a ↦ y a - referenceField f m) :=
    hY.sub ((contDiff_referenceField f m).comp contDiff_snd)
  have hYn : ContDiffOn ℝ n (Function.uncurry fun a ↦ y a - referenceField f m) univ :=
    (hYr.of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨A, hA0, hA⟩ := hYn.exists_nonneg_bound_iteratedFDeriv_uncurry_of_isOpen isOpen_univ
    hS.isCompact_closure (isCompact_closedBall 0 R₂) (subset_univ _)
  refine ⟨max (A * Real.exp (c * R₂)) (C * K₁), by positivity, fun a ha z ↦ ?_⟩
  have he : 0 < Real.exp (-(c * ‖z‖)) := Real.exp_pos _
  rcases le_or_gt ‖z‖ R₂ with hz | hz
  · have hb := (hA a (subset_closure ha) z (mem_closedBall_zero_iff.2 hz)).2 n le_rfl
    calc _ ≤ A := hb
      _ = A * Real.exp (c * R₂) * Real.exp (-(c * R₂)) := by
          rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ A * Real.exp (c * R₂) * Real.exp (-(c * ‖z‖)) := by
          gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hz1 : f.rOut + 1 < ‖z‖ := (le_max_left _ _).trans_lt hz
    have hz2 : f.rOut < ‖z‖ ^ 2 := by nlinarith [f.rOut_pos]
    -- Off the origin the winding phase, hence the end trivialization, is smooth.
    have hz0 : z ≠ 0 := fun h0 ↦ by simp [h0, f.rOut_pos.not_gt] at hz2
    have hya : ContDiff ℝ ∞ (y a) := hY.comp ((contDiff_const (c := a)).prodMk contDiff_id)
    have hvac : ContDiffAt ℝ n vacuumField z := by
      rw [show vacuumField = fun _ ↦ !₂[0, 0, 1 / 2, 0] from funext vacuumField_apply]
      exact contDiffAt_const
    have hG : ContDiffAt ℝ n
        (fun w ↦ gaugeTransform (windingPhase m)⁻¹ (y a) w - vacuumField w) z :=
      (contDiffAt_gaugeTransform (Circle.contDiffAt_coe_inv (contDiffAt_windingPhase m hz0))
        (hya.contDiffAt.of_le (by exact_mod_cast le_top))).sub hvac
    have hb := hC (y a) z hz2 hG (K₁ * Real.exp (-(c * ‖z‖))) fun i hi ↦
        (h ⟨i, Nat.lt_succ_iff.2 hi⟩ a ha z (((hR₁ _).trans (le_max_right _ _)).trans hz.le)).trans
          (mul_le_mul_of_nonneg_right (hK₁ _) he.le)
    calc _ ≤ C * (K₁ * Real.exp (-(c * ‖z‖))) := hb
      _ = C * K₁ * Real.exp (-(c * ‖z‖)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- **Uniform decay of the normalized vortices over a compact window of divisors.** For `m ≥ 1`,
a compact set `S` of divisors in `Sym ℂ m`, collisions of zeros included, an order `n` and a rate
`0 ≤ c < 1 / 2`, there is `K ≥ 0` such that the normalized vortex `y_D` with zero divisor `D`
satisfies `‖Dⁿ (y_D - x_ref) (z)‖ ≤ K exp (-c |z|)` for every `D ∈ S` and every `z ∈ ℂ`. -/
theorem exists_norm_iteratedFDeriv_gaugeTransform_sub_referenceField_le_mul_exp_of_isCompact
    {m : ℕ} (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) {S : Set (Sym ℂ m)} (hS : IsCompact S)
    (n : ℕ) {c : ℝ} (hc₀ : 0 ≤ c) (hc : c < 1 / 2) :
    ∃ K, 0 ≤ K ∧ ∀ D ∈ S, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (gaugeTransform (polynomialGauge (Sym.coeffEquiv ℂ m D))
          (polynomialVortex (Sym.toMonic D : ℂ[X])) - referenceField f m) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  have hS' : IsCompact (Sym.coeffEquiv ℂ m '' S) := by
    simpa only [Sym.coeffHomeomorph_apply] using hS.image (Sym.coeffHomeomorph ℂ m).continuous
  obtain ⟨K, hK, h⟩ :=
    exists_norm_iteratedFDeriv_gaugeTransform_sub_referenceField_le_mul_exp_of_isBounded hm f
      hS'.isBounded n hc₀ hc
  refine ⟨K, hK, fun D hD z ↦ ?_⟩
  rw [Sym.toMonic_eq_monicOfCoeff_coeffEquiv]
  exact h _ ⟨D, hD, rfl⟩ z

/-! ### Uniform bounds on the coordinates -/

/-- **Uniform bounds on the normalized vortices over a bounded window of coefficients.** For
`m ≥ 1`, a bounded set `S` of coefficients and an order `k`, there is `B` such that every
coordinate of every normalized vortex `y_a = g_a · x_a`, `a ∈ S`, has all derivatives of order at
most `k` bounded by `B` on the whole plane. -/
theorem exists_norm_iteratedFDeriv_gaugeTransform_apply_le_of_isBounded {m : ℕ} (hm : 0 < m)
    {S : Set (Fin m → ℂ)} (hS : Bornology.IsBounded S) (k : ℕ) :
    ∃ B, ∀ a ∈ S, ∀ i : Fin 4, ∀ n ≤ k, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z ↦ gaugeTransform (polynomialGauge a)
          (polynomialVortex (monicOfCoeff a)) z i) z‖ ≤ B := by
  set f : ContDiffBump (0 : ℝ) := default
  set y : (Fin m → ℂ) → ℂ → EuclideanSpace ℝ (Fin 4) := fun a ↦
    gaugeTransform (polynomialGauge a) (polynomialVortex (monicOfCoeff a))
  have hY : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × ℂ ↦ y p.1 p.2 :=
    by simpa only [normalizedVortex_def] using contDiff_normalizedVortex_uncurry
  -- Bounds for `y_a - x_ref` (rate `0`) and for the reference field, order by order.
  choose K _ hK using fun n : ℕ ↦
    exists_norm_iteratedFDeriv_gaugeTransform_sub_referenceField_le_mul_exp_of_isBounded hm f hS n
      le_rfl (by norm_num)
  choose Cr hCr using fun (i : Fin 4) (n : ℕ) ↦
    exists_norm_iteratedFDeriv_referenceField_apply_le f m i n
  obtain ⟨B, hB⟩ := Finite.exists_le fun p : Fin (k + 1) × Fin 4 ↦
    ‖EuclideanSpace.proj (𝕜 := ℝ) p.2‖ * K p.1 + Cr p.2 p.1
  refine ⟨B, fun a ha i n hn z ↦ ?_⟩
  have hya : ContDiff ℝ ∞ (y a) := hY.comp (contDiff_const.prodMk contDiff_id)
  have hd : ContDiff ℝ ∞ (y a - referenceField f m) := hya.sub (contDiff_referenceField f m)
  have hr : ContDiff ℝ ∞ fun z ↦ referenceField f m z i :=
    contDiff_euclidean.1 (contDiff_referenceField f m) i
  have hsplit : (fun z ↦ y a z i) =
      fun z ↦ EuclideanSpace.proj (𝕜 := ℝ) i ((y a - referenceField f m) z) +
        referenceField f m z i := by
    ext z
    simp
  have hp : ContDiff ℝ ∞ fun z ↦ EuclideanSpace.proj (𝕜 := ℝ) i ((y a - referenceField f m) z) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hd
  rw [hsplit, fun_iteratedFDeriv_add_apply (hp.contDiffAt.of_le (by exact_mod_cast le_top))
    (hr.contDiffAt.of_le (by exact_mod_cast le_top))]
  have h₁ := ((EuclideanSpace.proj (𝕜 := ℝ) i).norm_iteratedFDeriv_comp_left hd.contDiffAt
    (n := n) (by exact_mod_cast le_top)).trans
    (mul_le_mul_of_nonneg_left (hK n a ha z) (norm_nonneg _))
  rw [zero_mul, neg_zero, Real.exp_zero, mul_one] at h₁
  calc _ ≤ ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ * K n + Cr i n :=
        (norm_add_le _ _).trans (add_le_add h₁ (hCr i n z))
    _ ≤ B := hB (⟨n, Nat.lt_succ_iff.2 hn⟩, i)

/-- **Uniform bounds on the normalized vortices over a compact window of divisors.** For `m ≥ 1`,
a compact set `S` of divisors in `Sym ℂ m`, collisions of zeros included, and an order `k`, there
is `B` such that every coordinate of every normalized vortex `y_D`, `D ∈ S`, has all derivatives
of order at most `k` bounded by `B` on the whole plane. -/
theorem exists_norm_iteratedFDeriv_gaugeTransform_apply_le_of_isCompact {m : ℕ} (hm : 0 < m)
    {S : Set (Sym ℂ m)} (hS : IsCompact S) (k : ℕ) :
    ∃ B, ∀ D ∈ S, ∀ i : Fin 4, ∀ n ≤ k, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z ↦ gaugeTransform (polynomialGauge (Sym.coeffEquiv ℂ m D))
          (polynomialVortex (Sym.toMonic D : ℂ[X])) z i) z‖ ≤ B := by
  have hS' : IsCompact (Sym.coeffEquiv ℂ m '' S) := by
    simpa only [Sym.coeffHomeomorph_apply] using hS.image (Sym.coeffHomeomorph ℂ m).continuous
  obtain ⟨B, h⟩ := exists_norm_iteratedFDeriv_gaugeTransform_apply_le_of_isBounded hm
    hS'.isBounded k
  refine ⟨B, fun D hD i n hn z ↦ ?_⟩
  rw [Sym.toMonic_eq_monicOfCoeff_coeffEquiv]
  exact h _ ⟨D, hD, rfl⟩ i n hn z

end TauCeti.Vortex
