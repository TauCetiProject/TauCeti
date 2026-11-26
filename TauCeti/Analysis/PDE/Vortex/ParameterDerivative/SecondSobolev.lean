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

At a plane vortex `x` with `L∞` class `a`, the realization `L_a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the
gauge-fixed operator is Fredholm and onto, and every `y ∈ H¹` splits as `y = π y + Q (L_a y)`,
with `π` the projection onto the kernel along its `L²`-orthogonal complement and `Q` the right
inverse with values in that complement. Along a family of coefficients `a(p)`, `C²` at `p₀`,
write `Q''` and `π''` for the derivatives at `p₀` along `w` of `p ↦ DQ(p) v` and `p ↦ Dπ(p) v`,
and `a''` for that of `p ↦ Da(p) v`. Gluing plane vortices into solutions of the
four-dimensional equations differentiates the identities for these inverses and projections in
the parameters, and needs their second derivatives on errors decaying like `exp(-c ρ)`,
`ρ(z) = √(1 + |z|²)`, `|c| < 1/2`, in Sobolev norms. The weighted `L²` estimates
`‖exp(c ρ) Q'' f‖₂ ≤ K (‖a''‖∞ + ‖Da v‖∞ ‖Da w‖∞) ‖exp(c ρ) f‖₂` and the same for `π''`
are in `TauCeti.Analysis.PDE.Vortex.ParameterDerivative`. This file proves their weighted Sobolev
versions:

`‖exp(c ρ) Q'' f‖_(H^(k+1)) ≤ K (M₂ + M_v M_w) ‖exp(c ρ) f‖_(H^k)`
(`exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le`),

`‖exp(c ρ) π'' e‖_(H^(k+1)) ≤ K (M₂ + M_v M_w) ‖exp(c ρ) e‖₂`
(`exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le`),

when `a''`, `Da(p₀) v` and `Da(p₀) w` are the classes of smooth fields whose coordinates have
derivatives bounded through order `k` by `M₂`, `M_v` and `M_w`. The constant `K` depends only on
the degree `m`, a radius `R₀` containing the zeros of `x`, a bound `B` on the derivatives of `x`
through order `k`, the rate `c` and the order `k`, so the estimates hold uniformly over a window
of divisors, collisions included.

**The proof.** Differentiating `L Q = 1` and `L π = 0` twice gives
`L_a (Q'' f) = -(Z(a'', Q f) + Z(Da v, Q'_w f) + Z(Da w, Q'_v f))`
(`ContinuousLinearMap.IsFredholm.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply`), and the
same for `π''` with `π e`, `π'_w e`, `π'_v e` in place of `Q f`, `Q'_w f`, `Q'_v f`, where `Z` is
the zeroth-order part of the operator. The weighted Sobolev estimates for `Q f`, `π e` and the
first derivatives `Q'`, `π'` bound the right side in the weighted `H^k` norm, through
multiplication by the smooth coefficients on `H^k`. The weighted `L²` estimate for `Q'' f` or
`π'' e`, with the weighted elliptic estimate uniform in the field
(`exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul`), then raises it
to the weighted `H^(k+1)` norm. Sobolev norms are those of the coordinates in Mathlib's
Bessel-potential spaces `H^s(ℂ)`.

## Main results

* `TauCeti.Vortex.exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le`:
  the weighted Sobolev estimate for the second parameter derivative of the right inverses.
* `TauCeti.Vortex.exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le`:
  the weighted Sobolev estimate for the second parameter derivative of the kernel projections.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

open Complex MeasureTheory Filter TopologicalSpace ContinuousLinearMap BesselPotentialSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff BesselPotentialSpace

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

public section

noncomputable section

namespace TauCeti.Vortex


/-! ### Auxiliary facts -/

/-- The values of `Z(b, g)`, for the class `b` of a field `β`, are `Z(β z, g z)` almost
everywhere on `ℂ`. -/
private theorem holderL_ae_eq_gaugeFixedZerothOrder {b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
    {β : ℂ → EuclideanSpace ℝ (Fin 4)} (hb : b =ᵐ[μ⊤] β)
    (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    ⇑(gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b g) =ᵐ[volume]
      fun z ↦ gaugeFixedZerothOrder (β z) (g z) := by
  filter_upwards [(gaugeFixedZerothOrder.coeFn_holder (r := 2) b g).filter_mono
      (ae_mono (Measure.restrict_coe_opens_top _).ge),
    hb.filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z h₁ h₂
  rw [holderL_apply_apply, h₁, h₂]

/-- If `Wᵢ` are coordinates of `-Z(βᵢ, exp(c ρ) gᵢ)`, for the classes `bᵢ` of fields `βᵢ`, then
`W₀ + W₁ + W₂` are coordinates of `exp(c ρ) (-(Z(b₀, g₀) + Z(b₁, g₁) + Z(b₂, g₂)))`. -/
private theorem inclusionLp_add_add_ae_eq_exp_mul_smul_neg_add_add {s : ℝ} (hs : 0 ≤ s) {c : ℝ}
    {b₀ b₁ b₂ : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {β₀ β₁ β₂ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hb₀ : b₀ =ᵐ[μ⊤] β₀) (hb₁ : b₁ =ᵐ[μ⊤] β₁) (hb₂ : b₂ =ᵐ[μ⊤] β₂)
    {g₀ g₁ g₂ : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤} {W₀ W₁ W₂ : Fin 4 → H^{s}(ℂ)}
    (hW₀ : ∀ i, ⇑(inclusionLp hs (W₀ i)) =ᵐ[volume]
      fun z ↦ ((-gaugeFixedZerothOrder (β₀ z) (Real.exp (c * √(1 + ‖z‖ ^ 2)) • g₀ z)) i : ℂ))
    (hW₁ : ∀ i, ⇑(inclusionLp hs (W₁ i)) =ᵐ[volume]
      fun z ↦ ((-gaugeFixedZerothOrder (β₁ z) (Real.exp (c * √(1 + ‖z‖ ^ 2)) • g₁ z)) i : ℂ))
    (hW₂ : ∀ i, ⇑(inclusionLp hs (W₂ i)) =ᵐ[volume]
      fun z ↦ ((-gaugeFixedZerothOrder (β₂ z) (Real.exp (c * √(1 + ‖z‖ ^ 2)) • g₂ z)) i : ℂ))
    (i : Fin 4) :
    ⇑(inclusionLp hs ((W₀ + W₁ + W₂) i)) =ᵐ[volume] fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
      (-(gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₀ g₀ +
        gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₁ g₁ +
        gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₂ g₂)) z) i : ℂ) := by
  set H₀ := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₀ g₀
  set H₁ := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₁ g₁
  set H₂ := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₂ g₂
  rw [Pi.add_apply, Pi.add_apply, map_add, map_add]
  filter_upwards [Lp.coeFn_add (inclusionLp hs (W₀ i) + inclusionLp hs (W₁ i))
      (inclusionLp hs (W₂ i)), Lp.coeFn_add (inclusionLp hs (W₀ i)) (inclusionLp hs (W₁ i)),
    hW₀ i, hW₁ i, hW₂ i,
    (Lp.coeFn_neg (H₀ + H₁ + H₂)).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge),
    (Lp.coeFn_add (H₀ + H₁) H₂).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge),
    (Lp.coeFn_add H₀ H₁).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge),
    holderL_ae_eq_gaugeFixedZerothOrder hb₀ g₀, holderL_ae_eq_gaugeFixedZerothOrder hb₁ g₁,
    holderL_ae_eq_gaugeFixedZerothOrder hb₂ g₂]
    with z hW₀₁₂ hW₀₁ hW₀z hW₁z hW₂z hneg hH₀₁₂ hH₀₁ hH₀ hH₁ hH₂
  rw [hW₀₁₂, Pi.add_apply, hW₀₁, Pi.add_apply, hW₀z, hW₁z, hW₂z, hneg, Pi.neg_apply, hH₀₁₂,
    Pi.add_apply, hH₀₁, Pi.add_apply, hH₀, hH₁, hH₂]
  simp only [map_smul, smul_neg, smul_add, PiLp.neg_apply, PiLp.add_apply, ofReal_neg,
    ofReal_add, neg_add]

/-- An `L∞` class equal almost everywhere to a field whose coordinates have derivatives bounded by
`M` through order `k` has norm at most `2 M`, and `M` is nonnegative. -/
private theorem nonneg_and_norm_le_two_mul_of_ae_eq {k : ℕ}
    {b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {β : ℂ → EuclideanSpace ℝ (Fin 4)} {M : ℝ}
    (hb : b =ᵐ[μ⊤] β) (hβb : ∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) :
    0 ≤ M ∧ ‖b‖ ≤ 2 * M :=
  ⟨(norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0),
    norm_le_two_mul_of_ae_eq_of_forall_norm_apply_le hb fun i z ↦ by
      simpa only [norm_iteratedFDeriv_zero] using hβb i 0 (Nat.zero_le k) z⟩

/-- The arithmetic of the constants of the second-derivative estimates: for nonnegative reals,
`K₃ (M₂ A N + M_v B M_w N + M_w B M_v N + K₂ (2 M₂ + 4 M_v M_w) L N)` is at most
`K₃ (A + 2 B + 4 K₂ L) (M₂ + M_v M_w) N`. -/
private theorem mul_add_le_mul_add_mul_add_mul {A B K₂ K₃ L M₂ Mv Mw N : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) (hMv : 0 ≤ Mv)
    (hMw : 0 ≤ Mw) (hN : 0 ≤ N) :
    K₃ * (M₂ * (A * N) + Mv * (B * Mw * N) + Mw * (B * Mv * N) +
      K₂ * (2 * M₂ + 2 * Mv * (2 * Mw)) * (L * N)) ≤
      K₃ * (A + 2 * B + 4 * K₂ * L) * (M₂ + Mv * Mw) * N := by
  have : 0 ≤ K₃ * N * (A * (Mv * Mw) + 2 * B * M₂ + 2 * K₂ * L * M₂) := by positivity
  nlinarith

/-! ### The zeroth-order terms -/

/-- **The weighted Sobolev estimate for `Q f` over a window.** For every degree `m`, radius `R₀`,
bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following property. Let
`x` be a smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of
radius `R₀` and whose coordinates have derivatives bounded by `B` through order `k`, with `L∞`
class `a`, and let `Q` be the right inverse of `L_a` with values `L²`-orthogonal to its kernel. If
the coordinates of `exp(c ρ) f` are given by `g : Fin 4 → H^k(ℂ)`, then those of `exp(c ρ) Q f`
are given by some `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K ‖g‖`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_orthogonalRightInverse (m : ℕ) (R₀ B : ℝ)
    {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (g : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (g i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) i : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
            (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a) f) z) i :
              ℂ)) ∧
        ‖u‖ ≤ K * ‖g‖ := by
  obtain ⟨qc, hqc⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ hc
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  refine ⟨K₁ * (1 + 4 * qc), by positivity, ?_⟩
  intro x D hx hxb hsol hframe hD hD₀ a hax f g hg
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hQ := hT.isOrthogonalRightInverse_orthogonalRightInverse sobolevFieldValues_injective hsurj
  -- The values of `Q f` solve `L_x Y = f` weakly, with weighted `L²` norm at most `4 qc ‖g‖`.
  obtain ⟨hQm, hQn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul (by positivity)
    (hqc x D hx hsol hframe hD hD₀ a hax f)
    (eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hg)
  obtain ⟨u, hu, hun⟩ := hK₁b x hx hxb f _
    ((Lp.memLp f).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦ by
      rw [integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax _ hη hηc,
        hQ.rightInverse f]) hQm g hg
  exact ⟨u, hu, hun.trans (by nlinarith [norm_nonneg g])⟩

/-- **The weighted Sobolev estimate for `π e` over a window.** For every degree `m`, radius `R₀`,
bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following property. Let
`x` be a smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of
radius `R₀` and whose coordinates have bounded derivatives of every order, bounded by `B` through
order `k`, with `L∞` class `a`, and let `π` be the projection onto the kernel of `L_a` along its
`L²`-orthogonal complement. If `exp(c ρ) e` is square integrable, then the coordinates of
`exp(c ρ) π e` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K ‖exp(c ρ) e‖₂`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_orthogonalKerProjection (m : ℕ) (R₀ B : ℝ)
    {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ e : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
      MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2 volume →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
            (orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator a) e) z) i :
              ℂ)) ∧
        ‖u‖ ≤ K * (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
          sobolevFieldValues e z) 2 volume).toReal := by
  obtain ⟨kπ, hkπ⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀ hc
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  refine ⟨K₁ * kπ, by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ a hax e he
  obtain ⟨hT, -⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have := hT.finite_ker
  have hπ := isOrthogonalKerProjection_orthogonalKerProjection sobolevFieldValues_injective
    (sobolevGaugeFixedOperator a)
  have hπ0 : sobolevGaugeFixedOperator a (orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator a) e) = 0 := hπ.mem_ker e
  -- `π e` is a weak solution of `L_x Y = 0` with weighted `L²` norm at most `kπ ‖exp(c ρ) e‖₂`.
  obtain ⟨hπm, hπn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul (by positivity)
    (hkπ x D hx hbound hsol hframe hD hD₀ a hax e)
    (ENNReal.ofReal_toReal he.eLpNorm_lt_top.ne).ge
  obtain ⟨u, hu, hun⟩ := hK₁b x hx hxb (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) _
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦ by
      rw [integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax _ hη hηc,
        hπ0]) hπm 0 fun i ↦ .of_forall fun z ↦ by simp
  rw [norm_zero, zero_add] at hun
  exact ⟨u, hu, hun.trans (by rw [mul_assoc]; gcongr)⟩

/-! ### The elliptic step -/

/-- **The weighted Sobolev estimate for a solution of
`L_a y = -(Z(b₀, e₀) + Z(b₁, e₁) + Z(b₂, e₂))`.** For every order `k`, bound `B` and rate `c` there
is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth
field with `L∞` class `a` whose coordinates have derivatives bounded by `B` through order `k`, and
let each `bᵢ` be the class of a smooth field `βᵢ` whose coordinates have derivatives bounded by
`Mᵢ` through order `k`. Let `eᵢ, y ∈ H¹(ℂ)⁴` with `L_a y = -(Z(b₀, e₀) + Z(b₁, e₁) + Z(b₂, e₂))`,
where the coordinates of `exp(c ρ) eᵢ` are given by `uᵢ : Fin 4 → H^(k+1)(ℂ)` and
`‖exp(c ρ) y‖₂ ≤ N`. Then the coordinates of `exp(c ρ) y` are given by some
`u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K (M₀ ‖u₀‖ + M₁ ‖u₁‖ + M₂ ‖u₂‖ + N)`. This is the step
shared by the second parameter derivatives of the right inverse and of the kernel projection. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_add_add
    (k : ℕ) (B c : ℝ) :
    ∃ K ≥ 0, ∀ x : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ x →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ (b₀ b₁ b₂ : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
        (β₀ β₁ β₂ : ℂ → EuclideanSpace ℝ (Fin 4)) (M₀ M₁ M₂ : ℝ),
      b₀ =ᵐ[μ⊤] β₀ → ContDiff ℝ ∞ β₀ →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₀ z i) z‖ ≤ M₀) →
      b₁ =ᵐ[μ⊤] β₁ → ContDiff ℝ ∞ β₁ →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₁ z i) z‖ ≤ M₁) →
      b₂ =ᵐ[μ⊤] β₂ → ContDiff ℝ ∞ β₂ →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₂ z i) z‖ ≤ M₂) →
      ∀ (e₀ e₁ e₂ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
        (u₀ u₁ u₂ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
      (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e₀ z) i : ℂ)) →
      (∀ i, ⇑(inclusionLp (by positivity) (u₁ i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e₁ z) i : ℂ)) →
      (∀ i, ⇑(inclusionLp (by positivity) (u₂ i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e₂ z) i : ℂ)) →
      sobolevGaugeFixedOperator a y =
        -(gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₀ (sobolevFieldValues e₀) +
          gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₁ (sobolevFieldValues e₁) +
          gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b₂ (sobolevFieldValues e₂)) →
      ∀ N : ℝ, MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2 volume →
      (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2
        volume).toReal ≤ N →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) i : ℂ)) ∧
        ‖u‖ ≤ K * (M₀ * ‖u₀‖ + M₁ * ‖u₁‖ + M₂ * ‖u₂‖ + N) := by
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  obtain ⟨C, hC, hCb⟩ := exists_forall_exists_inclusionLp_ae_eq_neg_gaugeFixedZerothOrder k
  refine ⟨K₁ * (C + 1), by positivity, ?_⟩
  intro x hx hxb a hax b₀ b₁ b₂ β₀ β₁ β₂ M₀ M₁ M₂ hb₀ hβ₀ hβb₀ hb₁ hβ₁ hβb₁ hb₂ hβ₂ hβb₂
    e₀ e₁ e₂ y u₀ u₁ u₂ hu₀ hu₁ hu₂ hTy N hym hyn
  have hM₀ := (nonneg_and_norm_le_two_mul_of_ae_eq hb₀ hβb₀).1
  have hM₁ := (nonneg_and_norm_le_two_mul_of_ae_eq hb₁ hβb₁).1
  have hM₂ := (nonneg_and_norm_le_two_mul_of_ae_eq hb₂ hβb₂).1
  -- The coordinates `W₀ + W₁ + W₂` of `exp(c ρ) L_a y`, the sum of the `-Z(βᵢ, exp(c ρ) eᵢ)`.
  obtain ⟨W₀, hW₀, hW₀n⟩ := hCb β₀ hβ₀ M₀ hβb₀ _ u₀ hu₀
  obtain ⟨W₁, hW₁, hW₁n⟩ := hCb β₁ hβ₁ M₁ hβb₁ _ u₁ hu₁
  obtain ⟨W₂, hW₂, hW₂n⟩ := hCb β₂ hβ₂ M₂ hβb₂ _ u₂ hu₂
  -- `y` solves `L_x y = L_a y` weakly, and the weighted elliptic estimate concludes.
  obtain ⟨u, hu, hun⟩ := hK₁b x hx hxb (sobolevGaugeFixedOperator a y) _
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦
      integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax y hη hηc)
    hym _ (hTy ▸ inclusionLp_add_add_ae_eq_exp_mul_smul_neg_add_add _ hb₀ hb₁ hb₂ hW₀ hW₁ hW₂)
  refine ⟨u, hu, hun.trans ?_⟩
  have hW : ‖W₀ + W₁ + W₂‖ ≤ C * (M₀ * ‖u₀‖ + M₁ * ‖u₁‖ + M₂ * ‖u₂‖) :=
    norm_add₃_le.trans (by linarith)
  have : 0 ≤ M₀ * ‖u₀‖ + M₁ * ‖u₁‖ + M₂ * ‖u₂‖ := by positivity
  calc K₁ * (‖W₀ + W₁ + W₂‖ + _) ≤ K₁ * (C * (M₀ * ‖u₀‖ + M₁ * ‖u₁‖ + M₂ * ‖u₂‖) + N) := by
        gcongr
    _ ≤ K₁ * (C + 1) * (M₀ * ‖u₀‖ + M₁ * ‖u₁‖ + M₂ * ‖u₂‖ + N) := by
        rw [mul_assoc]; gcongr; nlinarith [ENNReal.toReal_nonneg.trans hyn]

/-! ### The weighted Sobolev estimates for the second parameter derivatives -/

/-- **The weighted Sobolev estimate for the second parameter derivative of the orthogonal right
inverses, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, bound `B`,
rate `|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order, bounded by `B` through order `k`. Let `a` be a family of `L∞` coefficients, `C²` at `p₀`,
with `a p₀` the class of `x`, and let `Q p` be the right inverse of the realization `L_(a p)` with
values `L²`-orthogonal to its kernel. Write `Q''` for the derivative at `p₀` along `w` of
`p ↦ DQ(p) v` and `a''` for that of `p ↦ Da(p) v`. Suppose `Da(p₀) v`, `Da(p₀) w` and `a''` are
the classes of smooth fields whose coordinates have derivatives bounded through order `k` by
`M_v`, `M_w` and `M₂`. If the coordinates of `exp(c ρ) f` are given by `g : Fin 4 → H^k(ℂ)`, then
those of `exp(c ρ) Q'' f` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with
`‖u‖ ≤ K (M₂ + M_v M_w) ‖g‖`. That is,

`‖exp(c ρ) Q'' f‖_(H^(k+1)) ≤ K (M₂ + M_v M_w) ‖exp(c ρ) f‖_(H^k)`,

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
        (Mv Mw M₂ : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] βv → ContDiff ℝ ∞ βv →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βv z i) z‖ ≤ Mv) →
        fderiv ℝ a p₀ w =ᵐ[μ⊤] βw → ContDiff ℝ ∞ βw →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βw z i) z‖ ≤ Mw) →
        fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w =ᵐ[μ⊤] β₂ → ContDiff ℝ ∞ β₂ →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₂ z i) z‖ ≤ M₂) →
        ∀ (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (g : Fin 4 → H^{(k : ℝ)}(ℂ)),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (g i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) i : ℂ)) →
        ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
              (fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
                (sobolevGaugeFixedOperator (a p))) p v f) p₀ w) z) i : ℂ)) ∧
          ‖u‖ ≤ K * (M₂ + Mv * Mw) * ‖g‖ := by
  obtain ⟨K₀, hK₀, hK₀b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_orthogonalRightInverse m R₀ B hc k
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_norm_exp_mul_smul_fderiv_orthogonalRightInverse_le_of_forall_mem_norm_le
      m R₀ B hc k
  obtain ⟨K₂, hK₂⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le m R₀ hc
  obtain ⟨K₃, hK₃, hK₃b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_add_add k B c
  refine ⟨K₃ * (K₀ + 2 * K₁ + 4 * K₂ * 4), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v w βv βw β₂ Mv Mw M₂
    hbv hβv hβvb hbw hβw hβwb hb₂ hβ₂ hβ₂b f g hg
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hd : DifferentiableAt ℝ a p₀ := ha.differentiableAt (by simp)
  obtain ⟨hMv, hbv2⟩ := nonneg_and_norm_le_two_mul_of_ae_eq hbv hβvb
  obtain ⟨hMw, hbw2⟩ := nonneg_and_norm_le_two_mul_of_ae_eq hbw hβwb
  obtain ⟨hM₂, hb₂2⟩ := nonneg_and_norm_le_two_mul_of_ae_eq hb₂ hβ₂b
  -- The coordinates of `exp(c ρ) Q f`, `exp(c ρ) Q'_v f` and `exp(c ρ) Q'_w f` in `H^(k+1)`.
  obtain ⟨u₀, hu₀, hu₀n⟩ := hK₀b x D hx hxb hsol hframe hD hD₀ (a p₀) hax f g hg
  obtain ⟨uv, huv, huvn⟩ :=
    hK₁b x D hx hbound hxb hsol hframe hD hD₀ hax hd v βv Mv hbv hβv hβvb f g hg
  obtain ⟨uw, huw, huwn⟩ :=
    hK₁b x D hx hbound hxb hsol hframe hD hD₀ hax hd w βw Mw hbw hβw hβwb f g hg
  -- The weighted `L²` norm of `y = Q'' f` is at most `K₂ (‖a''‖∞ + ‖Da v‖∞ ‖Da w‖∞) 4 ‖g‖`.
  obtain ⟨hym, hyn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul
    (K := K₂ * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖₊ +
      ‖fderiv ℝ a p₀ v‖₊ * ‖fderiv ℝ a p₀ w‖₊)) (by positivity)
    (by simpa only [ENNReal.coe_mul, ENNReal.coe_add] using
      hK₂ x D hx hbound hsol hframe hD hD₀ hax ha v w f)
    (eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hg)
  -- Differentiating `L Q = 1` twice: `L_x y = -(Z(a'', Q f) + Z(Da v, Q'_w f) + Z(Da w, Q'_v f))`.
  have hTy := hT.apply_fderiv_fun_fderiv_orthogonalRightInverse_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj
    (contDiff_sobolevGaugeFixedOperator.contDiffAt.comp p₀ ha) v w f
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply hd,
    fderiv_fun_fderiv_sobolevGaugeFixedOperator_comp_apply ha] at hTy
  obtain ⟨u, hu, hun⟩ := hK₃b x hx hxb (a p₀) hax _ _ _ β₂ βv βw M₂ Mv Mw hb₂ hβ₂ hβ₂b hbv hβv
    hβvb hbw hβw hβwb _ _ _ _ u₀ uw uv hu₀ huw huv hTy _ hym hyn
  refine ⟨u, hu, hun.trans ?_⟩
  push_cast
  calc _ ≤ K₃ * (M₂ * (K₀ * ‖g‖) + Mv * (K₁ * Mw * ‖g‖) + Mw * (K₁ * Mv * ‖g‖) +
        K₂ * (2 * M₂ + 2 * Mv * (2 * Mw)) * (4 * ‖g‖)) := by gcongr
    _ ≤ _ := mul_add_le_mul_add_mul_add_mul hK₀ hK₁ K₂.coe_nonneg hK₃ (by norm_num) hM₂ hMv hMw
        (norm_nonneg g)

/-- **The weighted Sobolev estimate for the second parameter derivative of the orthogonal kernel
projections, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, bound `B`,
rate `|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order, bounded by `B` through order `k`. Let `a` be a family of `L∞` coefficients, `C²` at `p₀`,
with `a p₀` the class of `x`, and let `π p` be the projection of `H¹(ℂ)⁴` onto the kernel of the
realization `L_(a p)` along its `L²`-orthogonal complement. Write `π''` for the derivative at `p₀`
along `w` of `p ↦ Dπ(p) v` and `a''` for that of `p ↦ Da(p) v`. Suppose `Da(p₀) v`, `Da(p₀) w`
and `a''` are the classes of smooth fields whose coordinates have derivatives bounded through
order `k` by `M_v`, `M_w` and `M₂`. If `exp(c ρ) e` is square integrable, then the coordinates of
`exp(c ρ) π'' e` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with
`‖u‖ ≤ K (M₂ + M_v M_w) ‖exp(c ρ) e‖₂`. That is,

`‖exp(c ρ) π'' e‖_(H^(k+1)) ≤ K (M₂ + M_v M_w) ‖exp(c ρ) e‖₂`,

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
        (Mv Mw M₂ : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] βv → ContDiff ℝ ∞ βv →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βv z i) z‖ ≤ Mv) →
        fderiv ℝ a p₀ w =ᵐ[μ⊤] βw → ContDiff ℝ ∞ βw →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βw z i) z‖ ≤ Mw) →
        fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w =ᵐ[μ⊤] β₂ → ContDiff ℝ ∞ β₂ →
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
    exists_forall_exists_inclusionLp_ae_eq_orthogonalKerProjection m R₀ B hc k
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_norm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le
      m R₀ B hc k
  obtain ⟨K₂, hK₂⟩ :=
    exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalKerProjection_le m R₀ hc
  obtain ⟨K₃, hK₃, hK₃b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_of_sobolevGaugeFixedOperator_eq_neg_add_add k B c
  refine ⟨K₃ * (K₀ + 2 * K₁ + 4 * K₂ * 1), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v w βv βw β₂ Mv Mw M₂
    hbv hβv hβvb hbw hβw hβwb hb₂ hβ₂ hβ₂b e he
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hd : DifferentiableAt ℝ a p₀ := ha.differentiableAt (by simp)
  obtain ⟨hMv, hbv2⟩ := nonneg_and_norm_le_two_mul_of_ae_eq hbv hβvb
  obtain ⟨hMw, hbw2⟩ := nonneg_and_norm_le_two_mul_of_ae_eq hbw hβwb
  obtain ⟨hM₂, hb₂2⟩ := nonneg_and_norm_le_two_mul_of_ae_eq hb₂ hβ₂b
  set N := (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues e z) 2
    volume).toReal
  -- The coordinates of `exp(c ρ) π e`, `exp(c ρ) π'_v e` and `exp(c ρ) π'_w e` in `H^(k+1)`.
  obtain ⟨u₀, hu₀, hu₀n⟩ := hK₀b x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax e he
  obtain ⟨uv, huv, huvn⟩ :=
    hK₁b x D hx hbound hxb hsol hframe hD hD₀ hax hd v βv Mv hbv hβv hβvb e he
  obtain ⟨uw, huw, huwn⟩ :=
    hK₁b x D hx hbound hxb hsol hframe hD hD₀ hax hd w βw Mw hbw hβw hβwb e he
  -- The weighted `L²` norm of `y = π'' e` is at most `K₂ (‖a''‖∞ + ‖Da v‖∞ ‖Da w‖∞) N`.
  obtain ⟨hym, hyn⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul
    (K := K₂ * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖₊ +
      ‖fderiv ℝ a p₀ v‖₊ * ‖fderiv ℝ a p₀ w‖₊)) ENNReal.toReal_nonneg
    (by simpa only [ENNReal.coe_mul, ENNReal.coe_add] using
      hK₂ x D hx hbound hsol hframe hD hD₀ hax ha v w e)
    (ENNReal.ofReal_toReal he.eLpNorm_lt_top.ne).ge
  -- Differentiating `L π = 0` twice: `L_x y = -(Z(a'', π e) + Z(Da v, π'_w e) + Z(Da w, π'_v e))`.
  have hTy := hT.apply_fderiv_fun_fderiv_orthogonalKerProjection_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj
    (contDiff_sobolevGaugeFixedOperator.contDiffAt.comp p₀ ha) v w e
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply hd,
    fderiv_fun_fderiv_sobolevGaugeFixedOperator_comp_apply ha] at hTy
  obtain ⟨u, hu, hun⟩ := hK₃b x hx hxb (a p₀) hax _ _ _ β₂ βv βw M₂ Mv Mw hb₂ hβ₂ hβ₂b hbv hβv
    hβvb hbw hβw hβwb _ _ _ _ u₀ uw uv hu₀ huw huv hTy _ hym hyn
  refine ⟨u, hu, hun.trans ?_⟩
  push_cast
  calc _ ≤ K₃ * (M₂ * (K₀ * N) + Mv * (K₁ * Mw * N) + Mw * (K₁ * Mv * N) +
        K₂ * (2 * M₂ + 2 * Mv * (2 * Mw)) * (1 * N)) := by rw [one_mul]; gcongr
    _ ≤ _ := mul_add_le_mul_add_mul_add_mul hK₀ hK₁ K₂.coe_nonneg hK₃ zero_le_one hM₂ hMv hMw
        ENNReal.toReal_nonneg

end TauCeti.Vortex
