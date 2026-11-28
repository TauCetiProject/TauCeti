/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ParameterDerivative
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Weighted Sobolev estimates for the second parameter derivatives of the vortex splitting

At a smooth plane vortex `x` with `L∞` class `a`, the realization `L_a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the
gauge-fixed operator is Fredholm and onto, with kernel projection `π` along the `L²`-orthogonal
complement and right inverse `Q` with values in that complement. Along a family of coefficients
`a(p)`, `C²` at `p₀` with `a(p₀) = a`, write `Q''` and `π''` for the derivatives at `p₀` along `w`
of `p ↦ DQ(p) v` and `p ↦ Dπ(p) v`, and `a''` for that of `p ↦ Da(p) v`. Gluing plane vortices
into solutions of the four-dimensional equations along a family of divisors uses these second
derivatives on errors that decay exponentially away from the vortex cores, measured with the weight
`exp(c ρ)`, `ρ(z) = √(1 + |z|²)`, `|c| < 1/2`. Their weighted `L²` estimates are
`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le` and
`TauCeti.Vortex.exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le`.
This file proves the weighted Sobolev estimates, which gain one derivative.

Suppose the derivatives `Da(p₀) v`, `Da(p₀) w` and `a''` of the coefficient are the classes of
smooth fields whose coordinates have derivatives bounded through order `k` by `M_v`, `M_w` and
`M₂`. Then

* `‖exp(c ρ) Q'' f‖_(H^(k+1)) ≤ K (M₂ + M_v M_w) ‖exp(c ρ) f‖_(H^k)`
  (`TauCeti.Vortex.exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le`);
* `‖exp(c ρ) π'' e‖_(H^(k+1)) ≤ K (M₂ + M_v M_w) ‖exp(c ρ) e‖₂`
  (`TauCeti.Vortex.exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le`),

with `K` depending only on the degree `m`, a radius `R₀` containing the zeros, a bound `B` on the
derivatives of the vortex through order `k`, the rate `c` and the order `k`. They hold uniformly
over a window of divisors, collisions included.

Differentiating `L Q = 1` and `L π = 0` twice gives
`L_x (Q'' f) = -(Z(a'', Q f) + Z(Da v, Q'_w f) + Z(Da w, Q'_v f))`, and the same with `π e`,
`π'_w e`, `π'_v e` in place of `Q f`, `Q'_w f`, `Q'_v f`
(`ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply`,
`ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply`), where `Z`
is the zeroth-order part of the operator. The weighted Sobolev estimates for `Q f` and `π e` and
for the first derivatives (`TauCeti.Vortex.`
`exists_forall_norm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le` and its
analogue for `π`)
put the three arguments of `Z` in weighted `H^(k+1)`, so the right side is in weighted `H^k`. The
weighted elliptic estimate for solutions of `L_a y = -∑ⱼ Z(bⱼ, eⱼ)`
(`TauCeti.Vortex.exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_sum`),
with the weighted `L²` estimate for the second derivative, concludes.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace ContinuousLinearMap BesselPotentialSpace
open scoped ENNReal NNReal Topology ContDiff BesselPotentialSpace

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-- **The weighted Sobolev estimate for a solution of the twice differentiated equation.** For
every order `k`, bound `B` and rate `c` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth field with `L∞` class `a p₀` whose coordinates have
derivatives bounded by `B` through order `k`, and let `Da(p₀) v`, `Da(p₀) w` and the derivative
`a''` along `w` of `p ↦ Da(p) v` be the classes of smooth fields whose coordinates have derivatives
bounded through order `k` by `Mv`, `Mw` and `M₂`. Let `y` solve
`L_(a p₀) y = -(Z(a'', e₁) + Z(Da v, e₂) + Z(Da w, e₃))`, where the coordinates of `exp(c ρ) eⱼ`
are given by `uⱼ : Fin 4 → H^(k+1)(ℂ)` with `‖u₁‖ ≤ A N`, `‖u₂‖ ≤ S Mw N` and `‖u₃‖ ≤ S Mv N`,
and let `‖exp(c ρ) y‖₂ ≤ K₂ (‖a''‖∞ + ‖Da v‖∞ ‖Da w‖∞) ‖g‖₂` with `‖g‖₂ ≤ C N`. Then the
coordinates of `exp(c ρ) y` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with
`‖u‖ ≤ K (A + S + K₂ C) (M₂ + Mv Mw) N`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_add_add
    (k : ℕ) (B c : ℝ) :
    ∃ K ≥ 0, ∀ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
      ∀ (v w : X) (βv βw β₂ : ℂ → EuclideanSpace ℝ (Fin 4)) (Mv Mw M₂ : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] βv → fderiv ℝ a p₀ w =ᵐ[μ⊤] βw →
        fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w =ᵐ[μ⊤] β₂ →
        ContDiff ℝ ∞ βv → ContDiff ℝ ∞ βw → ContDiff ℝ ∞ β₂ →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βv z i) z‖ ≤ Mv) →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βw z i) z‖ ≤ Mw) →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₂ z i) z‖ ≤ M₂) →
      ∀ (e₁ e₂ e₃ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
        (u₁ u₂ u₃ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
        (∀ i, ⇑(inclusionLp (by positivity) (u₁ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e₁ z) i : ℂ)) →
        (∀ i, ⇑(inclusionLp (by positivity) (u₂ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e₂ z) i : ℂ)) →
        (∀ i, ⇑(inclusionLp (by positivity) (u₃ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e₃ z) i : ℂ)) →
        sobolevGaugeFixedOperator (a p₀) y =
          -(gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w)
              (sobolevFieldValues e₁) +
            gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v) (sobolevFieldValues e₂) +
            gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ w) (sobolevFieldValues e₃)) →
      ∀ (A S C N : ℝ), 0 ≤ A → 0 ≤ S → 0 ≤ C → 0 ≤ N → ‖u₁‖ ≤ A * N → ‖u₂‖ ≤ S * Mw * N →
        ‖u₃‖ ≤ S * Mv * N → ∀ (K₂ : ℝ≥0) (g : ℂ → EuclideanSpace ℝ (Fin 4)),
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2 volume ≤
          K₂ * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖₊ +
            ‖fderiv ℝ a p₀ v‖₊ * ‖fderiv ℝ a p₀ w‖₊) * eLpNorm g 2 volume →
        eLpNorm g 2 volume ≤ ENNReal.ofReal (C * N) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) i : ℂ)) ∧
        ‖u‖ ≤ K * (A + S + K₂ * C) * (M₂ + Mv * Mw) * N := by
  obtain ⟨K₃, hK₃, hK₃b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_sum k 3 B c
  refine ⟨4 * K₃, by positivity, ?_⟩
  intro x hx hxb X _ _ a p₀ hax v w βv βw β₂ Mv Mw M₂ hbv hbw hb₂ hβv hβw hβ₂ hβvb hβwb hβ₂b
    e₁ e₂ e₃ y u₁ u₂ u₃ hu₁ hu₂ hu₃ hTy A S C N hA hS hC hN hu₁n hu₂n hu₃n K₂ g hy hg
  -- Each `L∞` norm is at most twice the bound on the coordinates of its field.
  obtain ⟨hMv, hbv2⟩ :=
    nonneg_and_norm_le_two_mul_of_ae_eq_of_forall_norm_iteratedFDeriv_le hbv hβvb
  obtain ⟨hMw, hbw2⟩ :=
    nonneg_and_norm_le_two_mul_of_ae_eq_of_forall_norm_iteratedFDeriv_le hbw hβwb
  obtain ⟨hM₂, hb₂2⟩ :=
    nonneg_and_norm_le_two_mul_of_ae_eq_of_forall_norm_iteratedFDeriv_le hb₂ hβ₂b
  obtain ⟨hym, hyn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul
    (K := K₂ * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖₊ +
      ‖fderiv ℝ a p₀ v‖₊ * ‖fderiv ℝ a p₀ w‖₊)) (by positivity)
    (by simpa only [ENNReal.coe_mul, ENNReal.coe_add] using hy) hg
  -- The three terms as a sum over `Fin 3`.
  obtain ⟨u, hu, hun⟩ := hK₃b x hx hxb (a p₀) hax
    ![fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w, fderiv ℝ a p₀ v, fderiv ℝ a p₀ w] ![β₂, βv, βw]
    ![M₂, Mv, Mw] (fun j ↦ by fin_cases j; exacts [hb₂, hbv, hbw])
    (fun j ↦ by fin_cases j; exacts [hβ₂, hβv, hβw])
    (fun j ↦ by fin_cases j; exacts [hβ₂b, hβvb, hβwb]) ![e₁, e₂, e₃] y ![u₁, u₂, u₃]
    (fun j ↦ by fin_cases j; exacts [hu₁, hu₂, hu₃]) (by
      rw [hTy, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]) _
    hym hyn
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hun
  refine ⟨u, hu, hun.trans ?_⟩
  push_cast
  calc K₃ * (M₂ * ‖u₁‖ + Mv * ‖u₂‖ + Mw * ‖u₃‖ + K₂ * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖ +
        ‖fderiv ℝ a p₀ v‖ * ‖fderiv ℝ a p₀ w‖) * (C * N)) ≤
        K₃ * (M₂ * (A * N) + Mv * (S * Mw * N) + Mw * (S * Mv * N) +
          K₂ * (2 * M₂ + 2 * Mv * (2 * Mw)) * (C * N)) := by
        gcongr
    _ ≤ _ := by
        have hK₂C : 0 ≤ (K₂ : ℝ) * C := by positivity
        nlinarith [mul_nonneg (mul_nonneg hK₃ hN) (mul_nonneg hA hM₂),
          mul_nonneg (mul_nonneg hK₃ hN) (mul_nonneg hA (mul_nonneg hMv hMw)),
          mul_nonneg (mul_nonneg hK₃ hN) (mul_nonneg hS hM₂),
          mul_nonneg (mul_nonneg hK₃ hN) (mul_nonneg hS (mul_nonneg hMv hMw)),
          mul_nonneg (mul_nonneg hK₃ hN) (mul_nonneg hK₂C hM₂)]

/-- **The weighted Sobolev estimate for the second parameter derivative of the orthogonal right
inverses, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, bound `B`,
rate `|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order, bounded by `B` through order `k`. Let `a` be a family of `L∞` coefficients, `C²` at `p₀`,
with `a p₀` the class of `x`, and let `Q p` be the right inverse of the realization `L_(a p)` with
values `L²`-orthogonal to its kernel. Write `Q''` for the derivative at `p₀` along `w` of
`p ↦ DQ(p) v` and `a''` for that of `p ↦ Da(p) v`. Suppose `Da(p₀) v`, `Da(p₀) w` and `a''` are the
classes of smooth fields whose coordinates have derivatives bounded through order `k` by `Mv`, `Mw`
and `M₂`. If the coordinates of `exp(c ρ) f` are given by `u₀ : Fin 4 → H^k(ℂ)`, then those of
`exp(c ρ) Q'' f` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K (M₂ + Mv Mw) ‖u₀‖`. That
is,

`‖exp(c ρ) Q'' f‖_(H^(k+1)) ≤ K (M₂ + Mv Mw) ‖exp(c ρ) f‖_(H^k)`,

with `K` depending only on `m`, `R₀`, `B`, `c` and `k`. The weighted `L²` estimate is
`exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le`. -/
theorem exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le
    (m : ℕ) (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        ContDiffAt ℝ 2 a p₀ → ∀ (v w : X) (βv βw β₂ : ℂ → EuclideanSpace ℝ (Fin 4))
        (Mv Mw M₂ : ℝ), fderiv ℝ a p₀ v =ᵐ[μ⊤] βv → fderiv ℝ a p₀ w =ᵐ[μ⊤] βw →
        fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w =ᵐ[μ⊤] β₂ →
        ContDiff ℝ ∞ βv → ContDiff ℝ ∞ βw → ContDiff ℝ ∞ β₂ →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βv z i) z‖ ≤ Mv) →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βw z i) z‖ ≤ Mw) →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₂ z i) z‖ ≤ M₂) →
        ∀ (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (u₀ : Fin 4 → H^{(k : ℝ)}(ℂ)),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (u₀ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) i : ℂ)) →
        ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
              (fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
                (sobolevGaugeFixedOperator (a p))) p v f) p₀ w) z) i : ℂ)) ∧
          ‖u‖ ≤ K * (M₂ + Mv * Mw) * ‖u₀‖ := by
  obtain ⟨qc, hqc⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ hc
  obtain ⟨K₂, hK₂⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le m R₀ hc
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  obtain ⟨KS, hKS, hKSb⟩ :=
    exists_forall_norm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ B
      hc k
  obtain ⟨K₃, hK₃, hK₃b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_add_add k B c
  refine ⟨K₃ * (K₁ * (1 + 4 * qc) + KS + K₂ * 4), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v w βv βw β₂ Mv Mw M₂ hbv hbw hb₂
    hβv hβw hβ₂ hβvb hβwb hβ₂b f u₀ hu₀
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hd : DifferentiableAt ℝ a p₀ := ha.differentiableAt (by simp)
  have hQ := hT.isOrthogonalRightInverse_orthogonalRightInverse sobolevFieldValues_injective hsurj
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  have hf := eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hu₀
  -- `exp(c ρ) Q f` has coordinates `u₁` in `H^(k+1)`, since `Q f` solves `L_x Y = f` weakly.
  obtain ⟨hQm, hQn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul (by positivity)
    (hqc x D hx hsol hframe hD hD₀ (a p₀) hax f) hf
  obtain ⟨u₁, hu₁, hu₁n⟩ := hK₁b x hx hxb f _
    ((Lp.memLp f).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦ by
      rw [integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax (Q f) hη hηc,
        hQ.rightInverse f]) hQm u₀ hu₀
  -- `exp(c ρ) Q'_w f` and `exp(c ρ) Q'_v f` have coordinates `u₂`, `u₃` in `H^(k+1)`.
  obtain ⟨u₂, hu₂, hu₂n⟩ :=
    hKSb x D hx hbound hxb hsol hframe hD hD₀ hax hd w βw Mw hbw hβw hβwb f u₀ hu₀
  obtain ⟨u₃, hu₃, hu₃n⟩ :=
    hKSb x D hx hbound hxb hsol hframe hD hD₀ hax hd v βv Mv hbv hβv hβvb f u₀ hu₀
  -- `Q'' f` solves `L_x y = -(Z(a'', Q f) + Z(Da v, Q'_w f) + Z(Da w, Q'_v f))`.
  exact hK₃b x hx hxb hax v w βv βw β₂ Mv Mw M₂ hbv hbw hb₂ hβv hβw hβ₂ hβvb hβwb hβ₂b (Q f)
    (fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
      (sobolevGaugeFixedOperator (a p))) p₀ w f)
    (fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
      (sobolevGaugeFixedOperator (a p))) p₀ v f) _
    u₁ u₂ u₃ hu₁ hu₂ hu₃ (by
      rw [hT.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply
        (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj
        (contDiff_sobolevGaugeFixedOperator.contDiffAt.comp p₀ ha)]
      simp only [fderiv_fun_fderiv_sobolevGaugeFixedOperator_comp_apply ha,
        fderiv_sobolevGaugeFixedOperator_comp_apply hd, Q])
    _ _ 4 _ (by positivity) hKS (by norm_num) (norm_nonneg u₀)
    ((hu₁n.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hQn) hK₁)).trans_eq (by ring))
    hu₂n hu₃n K₂ _ (hK₂ x D hx hbound hsol hframe hD hD₀ hax ha v w f) hf

/-- **The weighted Sobolev estimate for the second parameter derivative of the orthogonal kernel
projections, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, bound `B`,
rate `|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order, bounded by `B` through order `k`. Let `a` be a family of `L∞` coefficients, `C²` at `p₀`,
with `a p₀` the class of `x`, and let `π p` be the projection of `H¹(ℂ)⁴` onto the kernel of the
realization `L_(a p)` along its `L²`-orthogonal complement. Write `π''` for the derivative at `p₀`
along `w` of `p ↦ Dπ(p) v` and `a''` for that of `p ↦ Da(p) v`. Suppose `Da(p₀) v`, `Da(p₀) w` and
`a''` are the classes of smooth fields whose coordinates have derivatives bounded through order `k`
by `Mv`, `Mw` and `M₂`. If `exp(c ρ) e` is square integrable, then the coordinates of
`exp(c ρ) π'' e` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with
`‖u‖ ≤ K (M₂ + Mv Mw) ‖exp(c ρ) e‖₂`. That is,

`‖exp(c ρ) π'' e‖_(H^(k+1)) ≤ K (M₂ + Mv Mw) ‖exp(c ρ) e‖₂`,

with `K` depending only on `m`, `R₀`, `B`, `c` and `k`. The weighted `L²` estimate is
`exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le`. -/
theorem exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le
    (m : ℕ) (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        ContDiffAt ℝ 2 a p₀ → ∀ (v w : X) (βv βw β₂ : ℂ → EuclideanSpace ℝ (Fin 4))
        (Mv Mw M₂ : ℝ), fderiv ℝ a p₀ v =ᵐ[μ⊤] βv → fderiv ℝ a p₀ w =ᵐ[μ⊤] βw →
        fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w =ᵐ[μ⊤] β₂ →
        ContDiff ℝ ∞ βv → ContDiff ℝ ∞ βw → ContDiff ℝ ∞ β₂ →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βv z i) z‖ ≤ Mv) →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βw z i) z‖ ≤ Mw) →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₂ z i) z‖ ≤ M₂) →
        ∀ e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
        MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 volume →
        ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
              (fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
                (sobolevGaugeFixedOperator (a p))) p v e) p₀ w) z) i : ℂ)) ∧
          ‖u‖ ≤ K * (M₂ + Mv * Mw) * (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            sobolevFieldValues e z) 2 volume).toReal := by
  obtain ⟨K₀, hK₀, hK₀b⟩ :=
    exists_forall_norm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀ B hc k
  obtain ⟨K₂, hK₂⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le m R₀ hc
  obtain ⟨KS, hKS, hKSb⟩ :=
    exists_forall_norm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀ B
      hc k
  obtain ⟨K₃, hK₃, hK₃b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_add_add k B c
  refine ⟨K₃ * (K₀ + KS + K₂ * 1), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v w βv βw β₂ Mv Mw M₂ hbv hbw hb₂
    hβv hβw hβ₂ hβvb hβwb hβ₂b e he
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hd : DifferentiableAt ℝ a p₀ := ha.differentiableAt (by simp)
  have := hT.finite_ker
  set π := orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  -- `exp(c ρ) π e` has coordinates `u₁` in `H^(k+1)`.
  obtain ⟨u₁, hu₁, hu₁n⟩ := hK₀b x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax e he
  -- `exp(c ρ) π'_w e` and `exp(c ρ) π'_v e` have coordinates `u₂`, `u₃` in `H^(k+1)`.
  obtain ⟨u₂, hu₂, hu₂n⟩ :=
    hKSb x D hx hbound hxb hsol hframe hD hD₀ hax hd w βw Mw hbw hβw hβwb e he
  obtain ⟨u₃, hu₃, hu₃n⟩ :=
    hKSb x D hx hbound hxb hsol hframe hD hD₀ hax hd v βv Mv hbv hβv hβvb e he
  -- `π'' e` solves `L_x y = -(Z(a'', π e) + Z(Da v, π'_w e) + Z(Da w, π'_v e))`.
  exact hK₃b x hx hxb hax v w βv βw β₂ Mv Mw M₂ hbv hbw hb₂ hβv hβw hβ₂ hβvb hβwb hβ₂b (π e)
    (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator (a p))) p₀ w e)
    (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator (a p))) p₀ v e) _
    u₁ u₂ u₃ hu₁ hu₂ hu₃ (by
      rw [hT.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply
        (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj
        (contDiff_sobolevGaugeFixedOperator.contDiffAt.comp p₀ ha)]
      simp only [fderiv_fun_fderiv_sobolevGaugeFixedOperator_comp_apply ha,
        fderiv_sobolevGaugeFixedOperator_comp_apply hd, π])
    _ _ 1 _ hK₀ hKS zero_le_one ENNReal.toReal_nonneg hu₁n hu₂n hu₃n K₂ _
    (hK₂ x D hx hbound hsol hframe hD hD₀ hax ha v w e)
    (by rw [one_mul]; exact (ENNReal.ofReal_toReal he.eLpNorm_lt_top.ne).ge)

end TauCeti.Vortex
