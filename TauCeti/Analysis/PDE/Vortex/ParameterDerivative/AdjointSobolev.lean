/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ParameterDerivative
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
import TauCeti.MeasureTheory.Function.Lp.PiLp
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Weighted Sobolev estimates for the adjoints of the vortex right inverses

At a plane vortex `x` with `L∞` class `a`, let `Q` be the right inverse of the gauge-fixed
realization `L_a` with values `L²`-orthogonal to its kernel, read as an operator on `L²(ℂ; ℝ⁴)`
with Hilbert space adjoint `Q†`, as in `TauCeti.Analysis.PDE.Vortex.ParameterDerivative`.

`Q†` vanishes on the values of the kernel, so `Q† g = Q† (g - y₀)` for the kernel element
`y₀` whose values are the `L²`-orthogonal projection of `g` onto them. The decay of the kernel
bounds `exp(c ρ) y₀` in every `H^s` by `‖exp(c ρ) g‖₂`, and `g - y₀` is orthogonal to the kernel,
where the weighted Sobolev estimate for `Q†` of `TauCeti.Analysis.PDE.Vortex.WindowEstimate`
holds. This gives `‖exp(c ρ) Q† g‖_(H^(k+1)) ≤ K ‖exp(c ρ) g‖_(H^k)` for every `g ∈ L²`
(`exists_forall_norm_exp_mul_smul_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le`).
The derivative of the adjoints is again given through `Q†`: with `Z = Z(b, ·)`,

`(Q†)' g = Q† (Q (Z y₀) - Z† (Q† g))`,

since `Q' f = -Q (Z (Q f))` up to its kernel component, whose pairing with `y₀` is
`⟪Q f, Q (Z y₀)⟫`, and `Z†` is multiplication by the transposed matrix of `Z(β, ·)`. The
weighted Sobolev estimates for `Q` and `Q†` and multiplication by `β` on `H^k` then give
`‖exp(c ρ) (Q†)' g‖_(H^(k+1)) ≤ K M ‖exp(c ρ) g‖_(H^k)` (the same name with `fderiv_adjoint` in
place of `adjoint`).

The second derivative `(Q†)''` along `w` of `p ↦ D(Q†)(p) v`, along a family of coefficients `C²`
at `p₀`, is the adjoint of `Q''` (`inner_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_apply`),
so the weighted `L²` estimate for `Q''` at the rate `-c` gives
`‖exp(c ρ) (Q†)'' g‖₂ ≤ K (‖a''‖∞ + ‖Da v‖∞ ‖Da w‖∞) ‖exp(c ρ) g‖₂` by duality
(`exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_le`).
Pairing with the splitting of `Q''` into its component `-Q (Z₂ (Q f) + Z_v (Q'_w f) + Z_w (Q'_v f))`
orthogonal to the kernel and its kernel component expresses it through `Q`, `Q†` and the first
derivatives:

`(Q†)'' g = Q† (Q (Z₂ y₀ + Z_v (π'_w y₀) + Z_w (π'_v y₀)) - Z₂† (Q† g))`
`  - (Q†)'_w (Z_v† (Q† g) + π'_v y₀) - (Q†)'_v (Z_w† (Q† g) + π'_w y₀)`,

where `Z_u = Z(Da(p₀) u, ·)`, `Z₂ = Z(a'', ·)` for the derivative `a''` along `w` of
`p ↦ Da(p) v`, and `π'_u` is the derivative of the orthogonal kernel projections. The weighted
Sobolev estimates for `Q`, `Q†`, `π'_u` and `(Q†)'_u` then give
`‖exp(c ρ) (Q†)'' g‖_(H^(k+1)) ≤ K (M₂ + Mv Mw) ‖exp(c ρ) g‖_(H^k)`, where `Mv`, `Mw` and `M₂`
bound the derivatives through order `k` of `Da(p₀) v`, `Da(p₀) w` and `a''`
(`exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_le`).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace ContinuousLinearMap BesselPotentialSpace
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff BesselPotentialSpace

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### Weighted Sobolev estimates for the adjoints -/

/-- **The coordinates of the adjoint zeroth-order term.** For every order `k` there is a constant
`C` with the following property. Let `b` be the `L∞` class of a smooth field `β` whose coordinates
have derivatives bounded by `M` through order `k`, and let `u : Fin 4 → H^(k+1)(ℂ)` be coordinates
of `exp(c ρ) h` for some `h ∈ L²`, where `ρ(z) = √(1 + |z|²)`. Then `exp(c ρ) Z(b, ·)† h` has
coordinates `W : Fin 4 → H^k(ℂ)` with `‖W‖ ≤ C M ‖u‖`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_adjoint_holderL (k : ℕ) :
    ∃ C ≥ 0, ∀ (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (β : ℂ → EuclideanSpace ℝ (Fin 4))
      (M c : ℝ), b =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
      ∀ (h : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (u : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
      (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • h z) i : ℂ)) →
      ∃ W : Fin 4 → H^{(k : ℝ)}(ℂ),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (W i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
            ContinuousLinearMap.adjoint (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b) h z) i : ℂ)) ∧
        ‖W‖ ≤ C * M * ‖u‖ := by
  obtain ⟨C, hC, hCb⟩ := exists_forall_exists_inclusionLp_ae_eq_add_mulVec (le_refl k)
  refine ⟨C, hC, fun b β M c hb hβ hβb h u hu ↦ ?_⟩
  have hZ (i j : Fin 4) :=
    contDiff_and_norm_iteratedFDeriv_gaugeFixedZerothOrderMatrix_le hβ hβb j i
  have hk : (k : ℝ) ≤ k + 1 := by linarith
  obtain ⟨hun, hu'⟩ := norm_inclusion_le_and_ae_eq hk (Nat.cast_nonneg k) hu
  -- `exp(c ρ) Z(β, ·)† h` is `0 + A (exp(c ρ) h)` for the transposed matrix
  -- `A = (gaugeFixedZerothOrderMatrix β)ᵀ`.
  obtain ⟨W, hW, hWn⟩ := hCb (fun i j z ↦ gaugeFixedZerothOrderMatrix (β z) j i)
    (fun i j ↦ (hZ i j).1) M (fun i j ↦ (hZ i j).2) _ 0
    (fun i ↦ inclusion hk (u i)) 0 hu'
    (fun i ↦ by simpa [Pi.zero_def] using Lp.coeFn_zero ℂ 2 volume)
  refine ⟨W, fun i ↦ (hW i).trans ?_, hWn.trans ?_⟩
  · rw [adjoint_holderL_apply, holderL_apply_apply]
    filter_upwards [(coeFn_holder (r := 2) (adjointRealCLM ∘L gaugeFixedZerothOrder) b
      h).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge),
      hb.filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z h₁ h₂
    rw [h₁, h₂, comp_apply, adjointRealCLM_apply, ← map_smul]
    simp [adjoint_gaugeFixedZerothOrder_apply, Finset.mul_sum, mul_left_comm]
  · rw [norm_zero, zero_add]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
    gcongr

/-- Coordinates of `exp(c ρ) F` and `exp(c ρ) G` in `H^s(ℂ)` give coordinates of
`exp(c ρ) (F - G)`, for `F, G ∈ L²`. -/
private theorem coeFn_inclusionLp_sub_ae_eq_exp_mul_smul_sub {s c : ℝ} {hs : 0 ≤ s}
    {F G : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤} {v₁ v₂ : H^{s}(ℂ)} {i : Fin 4}
    (h₁ : ⇑(inclusionLp hs v₁) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • F z) i : ℂ))
    (h₂ : ⇑(inclusionLp hs v₂) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • G z) i : ℂ)) :
    ⇑(inclusionLp hs (v₁ - v₂)) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • (F - G) z) i : ℂ) := by
  filter_upwards [coeFn_inclusionLp_sub_ae_eq _ h₁ h₂,
    (Lp.coeFn_sub F G).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z hz hz'
  rw [hz, hz', Pi.sub_apply, smul_sub, PiLp.sub_apply, ofReal_sub]

/-- Coordinates of `exp(c ρ) F` and `exp(c ρ) G` in `H^s(ℂ)` give coordinates of
`exp(c ρ) (F + G)`, for `F, G ∈ L²`. -/
private theorem coeFn_inclusionLp_add_ae_eq_exp_mul_smul_add {s c : ℝ} {hs : 0 ≤ s}
    {F G : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤} {v₁ v₂ : H^{s}(ℂ)} {i : Fin 4}
    (h₁ : ⇑(inclusionLp hs v₁) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • F z) i : ℂ))
    (h₂ : ⇑(inclusionLp hs v₂) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • G z) i : ℂ)) :
    ⇑(inclusionLp hs (v₁ + v₂)) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • (F + G) z) i : ℂ) := by
  filter_upwards [coeFn_inclusionLp_add_ae_eq _ h₁ h₂,
    (Lp.coeFn_add F G).filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z hz hz'
  rw [hz, hz', Pi.add_apply, smul_add, PiLp.add_apply, ofReal_add]

/-- **The projection onto the values of the kernel, with weights.** For every degree `m`, radius
`R₀`, bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following
property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end
framing whose zeros lie in the closed disc of radius `R₀` and whose coordinates have bounded
derivatives of every order, bounded by `B` through order `k`, and let `a` be its `L∞` class. If the
coordinates of `exp(c ρ) g` are given by `w : Fin 4 → H^k(ℂ)`, then the kernel element `y₀` of the
realization `L_a` whose values are the `L²`-orthogonal projection of `g` onto the values of the
kernel has `exp(c ρ) y₀` with coordinates `u₀ : Fin 4 → H^(k+1)(ℂ)`, `‖u₀‖ ≤ K ‖w‖`. -/
private theorem exists_forall_exists_mem_ker_inner_sub_eq_zero_and_inclusionLp_ae_eq (m : ℕ)
    (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (w : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (w i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) i : ℂ)) →
      ∃ y₀ ∈ (sobolevGaugeFixedOperator a).ker,
        (∀ y ∈ (sobolevGaugeFixedOperator a).ker,
          ⟪g - sobolevFieldValues y₀, sobolevFieldValues y⟫ = 0) ∧
        ∃ u₀ : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y₀ z) i : ℂ)) ∧
          ‖u₀‖ ≤ K * ‖w‖ := by
  obtain ⟨kc, kn, _, _, hest⟩ := exists_forall_ker_and_orthogonalRightInverse_le m R₀ hc
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_and_norm_le_add_eLpNorm_exp_mul_smul k B c
  refine ⟨K₁ * (kc * kn * 4), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ a hax g w hw
  obtain ⟨hkc, hkn, -, -⟩ := hest x D hx hbound hsol hframe hD hD₀ a hax
  have := (isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax).1.finite_ker
  -- The values of `y₀` are the orthogonal projection of `g` onto the finite-dimensional space of
  -- the values of the kernel.
  set V := (sobolevGaugeFixedOperator a).ker.map
    (sobolevFieldValues : _ →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
  obtain ⟨y₀, hy₀, he⟩ := Submodule.mem_map.1 (V.starProjection_apply_mem g)
  have horth (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
      (hy : y ∈ (sobolevGaugeFixedOperator a).ker) :
      ⟪g - sobolevFieldValues y₀, sobolevFieldValues y⟫ = 0 := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := V) g
    rw [Submodule.mem_orthogonal'] at h
    simp only [coe_coe] at he
    rw [he]
    exact h _ (Submodule.mem_map_of_mem hy)
  -- `‖y₀‖₂² = ⟪y₀, g⟫`, so the decay of the kernel bounds `‖exp(c ρ) y₀‖₂` by `‖exp(c ρ) g‖₂`.
  have hinner : ‖sobolevFieldValues y₀‖ ^ 2 ≤ |⟪sobolevFieldValues y₀, g⟫| := by
    have h := horth y₀ hy₀
    rw [inner_sub_left, sub_eq_zero, real_inner_self_eq_norm_sq, real_inner_comm] at h
    rw [h]
    exact le_abs_self _
  have hec := TauCeti.eLpNorm_exp_mul_smul_le_of_sq_le_abs_inner (hkc y₀ hy₀) (hkn y₀ hy₀) hinner
  simp only [eLpNorm_restrict_coe_opens_top] at hec
  obtain ⟨hem, hen⟩ := memLp_and_toReal_eLpNorm_le_of_eLpNorm_le_mul (by positivity) hec
    (eLpNorm_le_of_forall_inclusionLp_ae_eq (Nat.cast_nonneg k) hw)
  -- `y₀` is a weak solution of `L_x Y = 0`, so the weighted elliptic estimate applies.
  obtain ⟨u₀, hu₀, hu₀n⟩ := hK₁b x hx hxb (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) _
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge)
    ((Lp.memLp _).mono_measure (Measure.restrict_coe_opens_top _).ge) (fun η hη hηc ↦ by
      rw [integral_inner_sobolevFieldValues_gaugeFixedAdjoint hx.continuous hax y₀ hη hηc,
        ← ContinuousLinearMap.coe_coe (sobolevGaugeFixedOperator a), LinearMap.mem_ker.1 hy₀]) hem 0
    fun i ↦ .of_forall fun z ↦ by simp
  refine ⟨y₀, hy₀, horth, u₀, hu₀, hu₀n.trans ?_⟩
  rw [norm_zero, zero_add, mul_assoc]
  gcongr
  exact hen.trans_eq (by push_cast; ring)

/-- `exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_norm_le` for a measure
equal to the volume, such as the volume restricted to the whole plane, in which the values of the
fields of `H¹(ℂ)⁴` are taken. -/
private theorem exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_eq_volume (m : ℕ)
    (r B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ a ∈ D, ‖a‖ ≤ r) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      ∀ {μ : Measure ℂ}, μ = volume →
      ∀ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ f w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, w z⟫ ∂μ = 0) →
      ∀ g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪g z, w z⟫ ∂μ = 0) →
      ∀ v : Fin 4 → H^{(k : ℝ)}(ℂ),
      (∀ a, ⇑(inclusionLp (Nat.cast_nonneg k) (v a)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) a : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ a, ⇑(inclusionLp (by positivity) (u a)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint Q g z) a : ℂ)) ∧
        ‖u‖ ≤ K * ‖v‖ := by
  obtain ⟨K, hK, h⟩ :=
    exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_norm_le m r B hc k
  refine ⟨K, hK, fun x D hx hsol hframe hD hDr hxb μ hμ ↦ ?_⟩
  subst hμ
  exact h x D hx hsol hframe hD hDr hxb

/-- **The weighted Sobolev estimate for the adjoint of the orthogonal right inverse, uniformly over
a window of divisors.** For every degree `m`, radius `R₀`, bound `B`, rate `|c| < 1/2` and order
`k` there is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a
smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of radius
`R₀` and whose coordinates have bounded derivatives of every order, bounded by `B` through order
`k`, let `a` be its `L∞` class, and let `Q` be the right inverse of the realization
`L_a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` with values `L²`-orthogonal to its kernel, read as an operator on
`L²(ℂ; ℝ⁴)` through the values of the fields. If the coordinates of `exp(c ρ) g` are given by
`w : Fin 4 → H^k(ℂ)`, then those of `exp(c ρ) Q† g` are given by some `u : Fin 4 → H^(k+1)(ℂ)`
with `‖u‖ ≤ K ‖w‖`. That is,

`‖exp(c ρ) Q† g‖_(H^(k+1)) ≤ K ‖exp(c ρ) g‖_(H^k)`

for every `g ∈ L²`, with `K` depending only on `m`, `R₀`, `B`, `c` and `k`. Unlike
`exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_forall_mem_norm_le`, `g` need not be
orthogonal to the kernel. -/
theorem exists_forall_norm_exp_mul_smul_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (w : Fin 4 → H^{(k : ℝ)}(ℂ)),
      (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (w i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) i : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.adjoint
            (sobolevFieldValues ∘L orthogonalRightInverse sobolevFieldValues
              (sobolevGaugeFixedOperator a)) g z) i : ℂ)) ∧
        ‖u‖ ≤ K * ‖w‖ := by
  obtain ⟨K₀, hK₀, hK₀b⟩ :=
    exists_forall_exists_mem_ker_inner_sub_eq_zero_and_inclusionLp_ae_eq m R₀ B hc k
  obtain ⟨K₂, hK₂, hK₂b⟩ :=
    exists_forall_norm_exp_mul_smul_adjoint_apply_le_mul_norm_of_eq_volume m R₀ B hc k
  refine ⟨K₂ * (1 + K₀), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ a hax g w hw
  obtain ⟨hT, hsurj⟩ := isFredholm_and_surjective_sobolevGaugeFixedOperator hx hsol hframe hax
  have hQ := hT.isOrthogonalRightInverse_orthogonalRightInverse sobolevFieldValues_injective hsurj
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a)
  obtain ⟨y₀, hy₀, horth, u₀, hu₀, hu₀n⟩ := hK₀b x D hx hbound hxb hsol hframe hD hD₀ a hax g w hw
  -- `Q†` vanishes on the values of the kernel, so `Q† g = Q† (g - y₀)`.
  have hQe : ContinuousLinearMap.adjoint (sobolevFieldValues ∘L Q) (sobolevFieldValues y₀) = 0 :=
    ext_inner_right ℝ fun f ↦ by
      rw [adjoint_inner_left, inner_zero_left, comp_apply, real_inner_comm,
        hQ.inner_eq_zero f y₀ hy₀]
  have hk1 : (k : ℝ) ≤ k + 1 := by linarith
  obtain ⟨hu₀n', hu₀'⟩ := norm_inclusion_le_and_ae_eq hk1 (Nat.cast_nonneg k) hu₀
  -- Weak solutions of `L_x w = 0` are values of the kernel, orthogonal to `g - y₀` and to `Q f`.
  obtain ⟨hweak, hQorth⟩ := integral_inner_gaugeFixedAdjoint_eq_and_integral_inner_eq_zero
    hx.continuous hax hQ
  obtain ⟨u, hu, hun⟩ := hK₂b x D hx hsol hframe hD hD₀ hxb (Measure.restrict_coe_opens_top _)
    (sobolevFieldValues ∘L Q) hweak hQorth (g - sobolevFieldValues y₀) (fun w' hw' ↦ by
      obtain ⟨y, hy, rfl⟩ := exists_mem_ker_sobolevFieldValues_eq hx.continuous hax hw'
      rw [← L2.inner_def]
      exact horth y hy)
    (fun i ↦ w i - inclusion hk1 (u₀ i)) fun i ↦ coeFn_inclusionLp_sub_ae_eq_exp_mul_smul_sub
      (hw i) (hu₀' i)
  refine ⟨u, fun i ↦ (hu i).trans (.of_forall fun z ↦ by rw [map_sub, hQe, sub_zero]),
    hun.trans ?_⟩
  calc K₂ * ‖fun i ↦ w i - inclusion hk1 (u₀ i)‖ ≤ K₂ * (‖w‖ + ‖u₀‖) := by
        gcongr
        exact (norm_sub_le w fun i ↦ inclusion hk1 (u₀ i)).trans (by gcongr)
    _ ≤ K₂ * (‖w‖ + K₀ * ‖w‖) := by gcongr
    _ = K₂ * (1 + K₀) * ‖w‖ := by ring

/-- **The derivative of the adjoints of the orthogonal right inverses.** Let `x` be a smooth plane
vortex with the degree-`m` end framing, `a` a family of `L∞` coefficients, differentiable at `p₀`,
with `a p₀` the class of `x`, and `Q p` the right inverse of the realization `L_(a p)` with values
`L²`-orthogonal to its kernel, read as an operator on `L²(ℂ; ℝ⁴)` through the values of the
fields. Let `Z = Z(b, ·)`, `b = Da(p₀) v`, be the derivative of the realizations along `v`, and
let `y₀` be a kernel element of `L_(a p₀)` whose values are the `L²`-orthogonal projection of `g`
onto the values of the kernel. Then the derivative of the adjoints along `v` is

`(Q†)' g = Q† (Q (Z y₀) - Z† (Q† g))`.

Indeed `Q' f = -Q (Z (Q f))` up to its kernel component, whose pairing with `y₀` is
`⟪Q f, Q (Z y₀)⟫`. -/
private theorem fderiv_adjoint_orthogonalRightInverse_apply_eq {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X} (hax : a p₀ =ᵐ[μ⊤] x)
    (ha : DifferentiableAt ℝ a p₀) (v : X) (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
    {y₀ : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2} (hy₀ : y₀ ∈ (sobolevGaugeFixedOperator (a p₀)).ker)
    (horth : ∀ y ∈ (sobolevGaugeFixedOperator (a p₀)).ker,
      ⟪g - sobolevFieldValues y₀, sobolevFieldValues y⟫ = 0) :
    fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
      orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p₀ v g =
      ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
        orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀)))
        (sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
          (sobolevGaugeFixedOperator (a p₀)) (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2
            (fderiv ℝ a p₀ v) (sobolevFieldValues y₀))) -
        ContinuousLinearMap.adjoint (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v))
          (ContinuousLinearMap.adjoint (sobolevFieldValues ∘L orthogonalRightInverse
            sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) g)) := by
  obtain ⟨hT, hsurj, hd, hπ⟩ :=
    isFredholm_and_differentiableAt_sobolevGaugeFixedOperator hx hsol hframe hax ha
  -- The derivative of `p ↦ (ι ∘ Q p)†` is `(ι ∘ Q')†`.
  rw [fderiv_adjoint_orthogonalRightInverse_apply hx hsol hframe hax ha]
  set Q' := fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p₀ v
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set A := sobolevFieldValues ∘L Q
  set S := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v)
  set π := orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  refine ext_inner_right ℝ fun f ↦ ?_
  have hsplit := hT.sub_orthogonalKerProjection_fderiv_orthogonalRightInverse_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hd v f
  have hpair := hT.inner_fderiv_orthogonalRightInverse_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hd v f hy₀
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply ha v] at hsplit hpair
  -- `ι (Q' f) = -Q (Z (Q f)) + ι (π (Q' f))`.
  have h1 : sobolevFieldValues (Q' f) = -A (S (A f)) + sobolevFieldValues (π (Q' f)) := by
    have h := congrArg sobolevFieldValues hsplit
    rw [map_sub, map_neg] at h
    exact sub_eq_iff_eq_add.1 h
  -- `g - y₀` is orthogonal to `ι (π (Q' f))`, and `ι (Q' f - π (Q' f))` to `y₀`.
  have h2 := horth _ (hπ.mem_ker (Q' f))
  have h3 := hπ.inner_sub_eq_zero (Q' f) y₀ hy₀
  rw [inner_sub_left] at h2
  rw [map_sub, inner_sub_left] at h3
  have h4 : ⟪g, A (S (A f))⟫ = ⟪ContinuousLinearMap.adjoint S
      (ContinuousLinearMap.adjoint A g), A f⟫ := by
    rw [adjoint_inner_left, adjoint_inner_left]
  have h5 : ⟪sobolevFieldValues (Q' f), sobolevFieldValues y₀⟫ =
      ⟪sobolevFieldValues (Q (S (sobolevFieldValues y₀))), A f⟫ :=
    hpair.trans (real_inner_comm _ _)
  have h6 : ⟪sobolevFieldValues y₀, sobolevFieldValues (π (Q' f))⟫ =
      ⟪sobolevFieldValues (π (Q' f)), sobolevFieldValues y₀⟫ := real_inner_comm _ _
  rw [adjoint_inner_left, adjoint_inner_left, ContinuousLinearMap.comp_apply, h1, inner_add_right,
    inner_neg_right, inner_sub_left, h4]
  linarith

/-- **The coordinates of `Q (Z y)`.** For every degree `m`, radius `R₀`, bound `B`, rate
`|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀`, with coordinates whose derivatives through order `k` are
bounded by `B`, and let `a` be its `L∞` class and `Q` the orthogonal right inverse of `L_a`. Let
`b` be the `L∞` class of a smooth field `β` whose coordinates have derivatives bounded by `M`
through order `k`. If `exp(c ρ) y` has coordinates `u₀ : Fin 4 → H^(k+1)(ℂ)`, then
`exp(c ρ) Q (Z(b, y))` has coordinates `u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K M ‖u₀‖`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_orthogonalRightInverse_holderL (m : ℕ)
    (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤, a =ᵐ[μ⊤] x →
      ∀ (b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) (β : ℂ → EuclideanSpace ℝ (Fin 4)) (M : ℝ),
      b =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
      ∀ (y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (u₀ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
      (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
        fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) i : ℂ)) →
      ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
        (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
            (orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a)
              (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b y)) z) i : ℂ)) ∧
        ‖u‖ ≤ K * M * ‖u₀‖ := by
  obtain ⟨KQ, hKQ, hKQb⟩ :=
    exists_forall_norm_exp_mul_smul_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ B hc k
  obtain ⟨C, hC, hCb⟩ := exists_forall_exists_inclusionLp_ae_eq_neg_gaugeFixedZerothOrder k
  refine ⟨KQ * C, by positivity, ?_⟩
  intro x D hx hxb hsol hframe hD hD₀ a hax b β M hb hβ hβb y u₀ hu₀
  set S := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 b
  -- The `H^k` coordinates `-W` of `exp(c ρ) Z(b, y)`.
  obtain ⟨W, hW, hWn⟩ := hCb β hβ M hβb _ u₀ hu₀
  have hSy (i : Fin 4) : ⇑(inclusionLp (Nat.cast_nonneg k) ((-W) i)) =ᵐ[volume]
      fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • S y z) i : ℂ) := by
    rw [Pi.neg_apply]
    filter_upwards [coeFn_inclusionLp_neg_ae_eq _ (hW i),
      (coeFn_holder (r := 2) gaugeFixedZerothOrder b y).filter_mono
        (ae_mono (Measure.restrict_coe_opens_top _).ge),
      hb.filter_mono (ae_mono (Measure.restrict_coe_opens_top _).ge)] with z h₁ h₂ h₃
    rw [h₁, holderL_apply_apply, h₂, h₃, map_smul, PiLp.neg_apply, ofReal_neg, neg_neg]
  -- The weighted Sobolev estimate for `Q` applies.
  obtain ⟨u, hu, hun⟩ := hKQb x D hx hxb hsol hframe hD hD₀ a hax (S y) _ hSy
  refine ⟨u, hu, hun.trans ?_⟩
  calc KQ * ‖-W‖ ≤ KQ * (C * M * ‖u₀‖) := by rw [norm_neg]; gcongr
    _ = KQ * C * M * ‖u₀‖ := by ring

/-- **The weighted Sobolev estimate for the parameter derivative of the adjoints of the orthogonal
right inverses, uniformly over a window of divisors.** For every degree `m`, radius `R₀`, bound
`B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following property, where
`ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end framing whose zeros
lie in the closed disc of radius `R₀` and whose coordinates have bounded derivatives of every
order, bounded by `B` through order `k`. Let `a` be a family of `L∞` coefficients, differentiable
at `p₀`, with `a p₀` the class of `x`, and let `Q p` be the right inverse of the realization
`L_(a p)` with values `L²`-orthogonal to its kernel, read as an operator on `L²(ℂ; ℝ⁴)` through
the values of the fields. Suppose the derivative `Da(p₀) v` of the coefficient is the class of a
smooth field `β` whose coordinates have derivatives bounded by `M` through order `k`. If the
coordinates of `exp(c ρ) g` are given by `w : Fin 4 → H^k(ℂ)`, then those of `exp(c ρ) (Q†)' g`,
for the derivative `(Q†)'` of the adjoints at `p₀` in the direction `v`, are given by some
`u : Fin 4 → H^(k+1)(ℂ)` with `‖u‖ ≤ K M ‖w‖`. That is,

`‖exp(c ρ) (Q†)' g‖_(H^(k+1)) ≤ K M ‖exp(c ρ) g‖_(H^k)`,

with `K` depending only on `m`, `R₀`, `B`, `c` and `k`. The weighted `L²` estimate is
`exists_forall_eLpNorm_exp_mul_smul_fderiv_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le`.
-/
theorem
  exists_forall_norm_exp_mul_smul_fderiv_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le
    (m : ℕ) (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (v : X) (β : ℂ → EuclideanSpace ℝ (Fin 4)) (M : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
        ∀ (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (w : Fin 4 → H^{(k : ℝ)}(ℂ)),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (w i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) i : ℂ)) →
        ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
              fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
                orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p₀ v
                  g z) i : ℂ)) ∧
          ‖u‖ ≤ K * M * ‖w‖ := by
  obtain ⟨KA, hKA, hKAb⟩ :=
    exists_forall_norm_exp_mul_smul_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ B
      hc k
  obtain ⟨K₀, hK₀, hK₀b⟩ :=
    exists_forall_exists_mem_ker_inner_sub_eq_zero_and_inclusionLp_ae_eq m R₀ B hc k
  obtain ⟨KS, hKS, hKSb⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_orthogonalRightInverse_holderL m R₀ B hc k
  obtain ⟨Ct, hCt, hCtb⟩ := exists_forall_exists_inclusionLp_ae_eq_adjoint_holderL k
  refine ⟨KA * (KS * K₀ + Ct * KA), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v β M hb hβ hβb g w hw
  have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
  have hk1 : (k : ℝ) ≤ k + 1 := by linarith
  -- The projection `y₀` of `g` onto the values of the kernel, `Q (Z y₀)`, `Q† g` and `Z† (Q† g)`.
  obtain ⟨y₀, hy₀, horth, u₀, hu₀, hu₀n⟩ :=
    hK₀b x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax g w hw
  obtain ⟨uS, huS, huSn⟩ :=
    hKSb x D hx hxb hsol hframe hD hD₀ (a p₀) hax _ β M hb hβ hβb _ u₀ hu₀
  obtain ⟨ug, hug, hugn⟩ := hKAb x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax g w hw
  obtain ⟨W, hW, hWn⟩ := hCtb _ β M c hb hβ hβb _ ug hug
  obtain ⟨huSn', huS'⟩ := norm_inclusion_le_and_ae_eq hk1 (Nat.cast_nonneg k) huS
  -- `(Q†)' g = Q† (Q (Z y₀) - Z† (Q† g))`, and the estimate for `Q†` applies.
  obtain ⟨u, hu, hun⟩ := hKAb x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax _
    (fun i ↦ inclusion hk1 (uS i) - W i) fun i ↦ coeFn_inclusionLp_sub_ae_eq_exp_mul_smul_sub
      (huS' i) (hW i)
  refine ⟨u, fun i ↦ (hu i).trans (.of_forall fun z ↦ ?_), hun.trans ?_⟩
  · rw [fderiv_adjoint_orthogonalRightInverse_apply_eq hx hsol hframe hax ha v g hy₀ horth]
  calc KA * ‖fun i ↦ inclusion hk1 (uS i) - W i‖ ≤ KA * (‖uS‖ + ‖W‖) := by
        gcongr
        exact (norm_sub_le (fun i ↦ inclusion hk1 (uS i)) W).trans (by gcongr)
    _ ≤ KA * (KS * M * (K₀ * ‖w‖) + Ct * M * (KA * ‖w‖)) := by
        gcongr
        · exact huSn.trans (by gcongr)
        · exact hWn.trans (by gcongr)
    _ = KA * (KS * K₀ + Ct * KA) * M * ‖w‖ := by ring

/-! ### The second parameter derivative of the adjoints -/

/-- **The second parameter derivative of the adjoints of the orthogonal right inverses.** Let `x`
be a smooth plane vortex with the degree-`m` end framing, `a` a family of `L∞` coefficients, `C²`
at `p₀`, with `a p₀` the class of `x`, and `Q p` the right inverse of the realization `L_(a p)`
with values `L²`-orthogonal to its kernel, read as an operator `ι ∘ Q p` on `L²(ℂ; ℝ⁴)` through
the values `ι` of the fields. Write `(Q†)''` for the derivative at `p₀` along `w` of
`p ↦ D(Q†)(p) v`, and `Q''` for that of `p ↦ DQ(p) v`. Then `(Q†)''` is the adjoint of `ι ∘ Q''`:
`⟪(Q†)'' g, f⟫ = ⟪g, ι (Q'' f)⟫`. -/
theorem inner_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_apply {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X} (hax : a p₀ =ᵐ[μ⊤] x)
    (ha : ContDiffAt ℝ 2 a p₀) (v w : X) (g f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    ⟪fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
      orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p v g) p₀ w,
        f⟫ =
      ⟪g, sobolevFieldValues (fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalRightInverse
        sobolevFieldValues (sobolevGaugeFixedOperator (a p))) p v f) p₀ w)⟫ := by
  obtain ⟨hQ2, hA2⟩ := contDiffAt_adjoint_orthogonalRightInverse hx hsol hframe hax ha
  set Q := fun p ↦ orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p))
  -- Both sides are second derivatives of `p ↦ ⟪(ι ∘ Q p)† g, f⟫ = ⟪g, ι (Q p f)⟫`.
  set Φ₁ := (innerSL ℝ f).comp (ContinuousLinearMap.apply ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) g)
  set Φ₂ := (innerSL ℝ g).comp (sobolevFieldValues.comp
    (ContinuousLinearMap.apply ℝ (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) f))
  have hΦ : (fun p ↦ Φ₁ (ContinuousLinearMap.adjoint (sobolevFieldValues ∘L Q p))) =
      fun p ↦ Φ₂ (Q p) := by
    funext p
    simp only [Φ₁, Φ₂, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
  have h₁ := Φ₁.fderiv_fderiv_comp_apply hA2 w v
  have h₂ := Φ₂.fderiv_fderiv_comp_apply hQ2 w v
  rw [hΦ, h₂] at h₁
  have hA' := (hA2.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hQ' := (hQ2.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  rw [fderiv_clm_apply_const_apply₂ hA', fderiv_clm_apply_const_apply₂ hQ', real_inner_comm]
  simpa only [Φ₁, Φ₂, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.apply_apply] using h₁.symm

/-- **The weighted estimate for the second parameter derivative of the adjoints of the orthogonal
right inverses, uniformly over a window of divisors.** For every degree `m`, radius `R₀` and rate
`|c| < 1/2` there is a constant `K` with the following property, where `ρ(z) = √(1 + |z|²)`. Let
`x` be a smooth plane vortex with the degree-`m` end framing whose zeros lie in the closed disc of
radius `R₀` and whose coordinates have bounded derivatives of every order. Let `a` be a family of
`L∞` coefficients, `C²` at `p₀`, with `a p₀` the class of `x`, and let `Q p` be the right inverse
of the realization `L_(a p)` with values `L²`-orthogonal to its kernel, read as an operator on
`L²(ℂ; ℝ⁴)` through the values of the fields. Write `(Q†)''` for the derivative at `p₀` along `w`
of `p ↦ D(Q†)(p) v` and `a''` for that of `p ↦ Da(p) v`. Then

`‖exp(c ρ) (Q†)'' g‖₂ ≤ K (‖a''‖∞ + ‖Da(p₀) v‖∞ ‖Da(p₀) w‖∞) ‖exp(c ρ) g‖₂`

for every `g ∈ L²`, where either side may be infinite. -/
theorem exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_le
    (m : ℕ) (R₀ : ℝ) {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        ContDiffAt ℝ 2 a p₀ → ∀ (v w : X) (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤),
        eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) •
          fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
            orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p v g)
              p₀ w z) 2 volume ≤
          K * (‖fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w‖₊ +
            ‖fderiv ℝ a p₀ v‖₊ * ‖fderiv ℝ a p₀ w‖₊) *
            eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) 2 volume := by
  obtain ⟨K, hK⟩ := exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_orthogonalRightInverse_le
    m R₀ (c := -c) (by rwa [abs_neg])
  refine ⟨K, fun x D hx hbound hsol hframe hD hD₀ X _ _ a p₀ hax ha v w g ↦ ?_⟩
  obtain ⟨-, hA2⟩ := contDiffAt_adjoint_orthogonalRightInverse hx hsol hframe hax ha
  set A := fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
    orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))
  -- `(Q†)''` is the operator `P = (P†)†`, and `P† = ι ∘ Q''` is estimated at the rate `-c`.
  set P := fderiv ℝ (fun p ↦ fderiv ℝ A p v) p₀ w
  have hP (g' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      fderiv ℝ (fun p ↦ fderiv ℝ A p v g') p₀ w = P g' :=
    fderiv_clm_apply_const_apply ((((hA2.fderiv_right (m := 1) le_rfl).differentiableAt
      one_ne_zero).clm_apply (differentiableAt_const v))) g' w
  have hP' (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) : ContinuousLinearMap.adjoint P f =
      sobolevFieldValues (fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalRightInverse
        sobolevFieldValues (sobolevGaugeFixedOperator (a p))) p v f) p₀ w) :=
    ext_inner_left ℝ fun g' ↦ by
      rw [adjoint_inner_right, ← hP,
        inner_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_apply hx hsol hframe hax ha]
  rw [hP, ← ContinuousLinearMap.adjoint_adjoint P, ← eLpNorm_restrict_coe_opens_top
    (volume : Measure ℂ), ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)]
  refine ContinuousLinearMap.eLpNorm_exp_mul_smul_adjoint_apply_le _ (fun f ↦ ?_) g
  have h := hK x D hx hbound hsol hframe hD hD₀ hax ha v w f
  rw [← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ),
    ← eLpNorm_restrict_coe_opens_top (volume : Measure ℂ)] at h
  simpa only [hP'] using h

/-- **The second derivative of the adjoints of the orthogonal right inverses.** Let `x` be a smooth
plane vortex with the degree-`m` end framing, `a` a family of `L∞` coefficients, `C²` at `p₀`, with
`a p₀` the class of `x`, and `Q p` the right inverse of the realization `L_(a p)` with values
`L²`-orthogonal to its kernel, read as an operator on `L²(ℂ; ℝ⁴)` through the values of the
fields. Write `(Q†)'_u` and `π'_u` for the derivatives at `p₀` along `u` of the adjoints and of the
orthogonal kernel projections, `Z_u = Z(Da(p₀) u, ·)`, and `Z₂ = Z(a'', ·)` for the derivative
`a''` along `w` of `p ↦ Da(p) v`. Let `y₀` be a kernel element of `L_(a p₀)` whose values are the
`L²`-orthogonal projection of `g` onto the values of the kernel. Then the derivative `(Q†)''`
along `w` of `p ↦ D(Q†)(p) v` is

`(Q†)'' g = Q† (Q (Z₂ y₀ + Z_v (π'_w y₀) + Z_w (π'_v y₀)) - Z₂† (Q† g))`
`  - (Q†)'_w (Z_v† (Q† g) + π'_v y₀) - (Q†)'_v (Z_w† (Q† g) + π'_w y₀)`. -/
private theorem fderiv_fun_fderiv_adjoint_orthogonalRightInverse_apply_eq {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X} (hax : a p₀ =ᵐ[μ⊤] x)
    (ha : ContDiffAt ℝ 2 a p₀) (v w : X) (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
    {y₀ : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2} (hy₀ : y₀ ∈ (sobolevGaugeFixedOperator (a p₀)).ker)
    (horth : ∀ y ∈ (sobolevGaugeFixedOperator (a p₀)).ker,
      ⟪g - sobolevFieldValues y₀, sobolevFieldValues y⟫ = 0) :
    fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
      orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p v g) p₀ w =
      ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
          orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀)))
          (sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
            (sobolevGaugeFixedOperator (a p₀))
            (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w)
                (sobolevFieldValues y₀) +
              gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v)
                (sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
                  (sobolevGaugeFixedOperator (a p))) p₀ w y₀)) +
              gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ w)
                (sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
                  (sobolevGaugeFixedOperator (a p))) p₀ v y₀)))) -
            ContinuousLinearMap.adjoint (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2
              (fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w))
              (ContinuousLinearMap.adjoint (sobolevFieldValues ∘L orthogonalRightInverse
                sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) g)) -
        fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
          orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p₀ w
          (ContinuousLinearMap.adjoint (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v))
              (ContinuousLinearMap.adjoint (sobolevFieldValues ∘L orthogonalRightInverse
                sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) g) +
            sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
              (sobolevGaugeFixedOperator (a p))) p₀ v y₀)) -
        fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
          orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p₀ v
          (ContinuousLinearMap.adjoint (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ w))
              (ContinuousLinearMap.adjoint (sobolevFieldValues ∘L orthogonalRightInverse
                sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) g) +
            sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
              (sobolevGaugeFixedOperator (a p))) p₀ w y₀)) := by
  have hd : DifferentiableAt ℝ a p₀ := ha.differentiableAt (by simp)
  obtain ⟨hT, hsurj, -, hπ⟩ :=
    isFredholm_and_differentiableAt_sobolevGaugeFixedOperator hx hsol hframe hax hd
  have hT2 : ContDiffAt ℝ 2 (fun p ↦ sobolevGaugeFixedOperator (a p)) p₀ :=
    contDiff_sobolevGaugeFixedOperator.contDiffAt.comp p₀ ha
  refine ext_inner_right ℝ fun f ↦ ?_
  have hsplit := hT.sub_orthogonalKerProjection_fderiv_fun_fderiv_orthogonalRightInverse_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hT2 v w f
  have hpair := hT.inner_fderiv_fun_fderiv_orthogonalRightInverse_apply
    (T := fun p ↦ sobolevGaugeFixedOperator (a p)) sobolevFieldValues_injective hsurj hT2 v w f hy₀
  simp only [fderiv_sobolevGaugeFixedOperator_comp_apply hd,
    fderiv_fun_fderiv_sobolevGaugeFixedOperator_comp_apply ha] at hsplit hpair
  rw [inner_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_apply hx hsol hframe hax ha,
    fderiv_adjoint_orthogonalRightInverse_apply hx hsol hframe hax hd,
    fderiv_adjoint_orthogonalRightInverse_apply hx hsol hframe hax hd]
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set π := orthogonalKerProjection sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))
  set S₂ := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w)
  set Sv := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v)
  set Sw := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ w)
  set Q'v := fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p₀ v
  set Q'w := fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p₀ w
  set π'v := fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p₀ v
  set π'w := fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p₀ w
  set Q'' := fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ orthogonalRightInverse sobolevFieldValues
    (sobolevGaugeFixedOperator (a p))) p v f) p₀ w
  set ι := (sobolevFieldValues : (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
  -- `g - y₀` is orthogonal to `ι (π Q'' f)`, and `ι (Q'' f - π Q'' f)` to `y₀`.
  have h2 := horth _ (hπ.mem_ker Q'')
  have h3 := hπ.inner_sub_eq_zero Q'' y₀ hy₀
  rw [inner_sub_left] at h2
  rw [map_sub, inner_sub_left] at h3
  -- `ι Q'' f` is `-ι Q (Z₂ (ι Q f) + Z_v (ι Q'_w f) + Z_w (ι Q'_v f))` plus a kernel element.
  rw [← sub_add_cancel Q'' (π Q''), hsplit]
  simp only [map_add, map_neg, inner_add_right, inner_neg_right, inner_sub_left, inner_add_left,
    adjoint_inner_left, ContinuousLinearMap.comp_apply]
  simp only [map_add, inner_add_right] at hpair
  linarith [real_inner_comm (ι y₀) (ι (π Q'')), real_inner_comm (ι (Q f)) (ι (Q (S₂ (ι y₀)))),
    real_inner_comm (ι (Q f)) (ι (Q (Sv (ι (π'w y₀))))),
    real_inner_comm (ι (Q f)) (ι (Q (Sw (ι (π'v y₀))))),
    real_inner_comm (ι (Q'v f)) (ι (π'w y₀)), real_inner_comm (ι (Q'w f)) (ι (π'v y₀))]

/-- **The derivatives of the kernel projections on a kernel element, in Sobolev coordinates.** For
every degree `m`, radius `R₀`, bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K`
with the following property, in the setting of
`exists_forall_norm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le`. If
`exp(c ρ) y` has coordinates `u₀ : Fin 4 → H^(k+1)(ℂ)`, then `exp(c ρ) π'_u y` has coordinates
`U : Fin 4 → H^(k+1)(ℂ)` with `‖U‖ ≤ K M ‖u₀‖`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_fderiv_orthogonalKerProjection (m : ℕ)
    (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (u : X) (β : ℂ → EuclideanSpace ℝ (Fin 4)) (M : ℝ),
        fderiv ℝ a p₀ u =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
        ∀ (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (u₀ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
        (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) i : ℂ)) →
        ∃ U : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (U i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues
              (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
                (sobolevGaugeFixedOperator (a p))) p₀ u y) z) i : ℂ)) ∧
          ‖U‖ ≤ K * M * ‖u₀‖ := by
  obtain ⟨Kπ, hKπ, hKπb⟩ :=
    exists_forall_norm_exp_mul_smul_fderiv_orthogonalKerProjection_le_of_forall_mem_norm_le m R₀ B
      hc k
  refine ⟨4 * Kπ, by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax hd u β M hb hβ hβb y u₀ hu₀
  have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
  -- The weighted `L²` norm of `y` is at most `4 ‖u₀‖`.
  have hn : (eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) 2
      volume).toReal ≤ 4 * ‖u₀‖ :=
    ENNReal.toReal_le_of_le_ofReal (by positivity)
      (eLpNorm_le_of_forall_inclusionLp_ae_eq (by positivity) hu₀)
  obtain ⟨U, hU, hUn⟩ := hKπb x D hx hbound hxb hsol hframe hD hD₀ hax hd u β M hb hβ hβb y
    (memLp_of_forall_inclusionLp_ae_eq (by positivity) hu₀)
  refine ⟨U, hU, hUn.trans ?_⟩
  calc Kπ * M * _ ≤ Kπ * M * (4 * ‖u₀‖) := by gcongr
    _ = 4 * Kπ * M * ‖u₀‖ := by ring

/-- **The first-derivative terms of the second derivative of the adjoints.** For every degree `m`,
radius `R₀`, bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following
property. In the setting of
`exists_forall_norm_exp_mul_smul_fderiv_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le`,
let `Da(p₀) u` and `Da(p₀) u'` be the classes of smooth fields whose coordinates have derivatives
bounded through order `k` by `M` and `M'`, and write `Z_u' = Z(Da(p₀) u', ·)`. If `exp(c ρ) g` has
coordinates `G : Fin 4 → H^k(ℂ)` and `exp(c ρ) y` has coordinates `u₀ : Fin 4 → H^(k+1)(ℂ)`, then
`exp(c ρ) (Q†)'_u (Z_u'† (Q† g) + π'_u' y)` has coordinates `U : Fin 4 → H^(k+1)(ℂ)` with
`‖U‖ ≤ K M M' (‖G‖ + ‖u₀‖)`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_fderiv_adjoint_add (m : ℕ) (R₀ B : ℝ)
    {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (u u' : X) (β β' : ℂ → EuclideanSpace ℝ (Fin 4)) (M M' : ℝ),
        fderiv ℝ a p₀ u =ᵐ[μ⊤] β → ContDiff ℝ ∞ β →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β z i) z‖ ≤ M) →
        fderiv ℝ a p₀ u' =ᵐ[μ⊤] β' → ContDiff ℝ ∞ β' →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β' z i) z‖ ≤ M') →
        ∀ (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (G : Fin 4 → H^{(k : ℝ)}(ℂ)),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (G i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) i : ℂ)) →
        ∀ (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (u₀ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
        (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) i : ℂ)) →
        ∃ U : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (U i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
              fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
                orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p₀ u
                (ContinuousLinearMap.adjoint (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2
                    (fderiv ℝ a p₀ u'))
                  (ContinuousLinearMap.adjoint (sobolevFieldValues ∘L orthogonalRightInverse
                    sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) g) +
                  sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection sobolevFieldValues
                    (sobolevGaugeFixedOperator (a p))) p₀ u' y)) z) i : ℂ)) ∧
          ‖U‖ ≤ K * M * M' * (‖G‖ + ‖u₀‖) := by
  obtain ⟨KA, hKA, hKAb⟩ :=
    exists_forall_norm_exp_mul_smul_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ B
      hc k
  obtain ⟨Ct, hCt, hCtb⟩ := exists_forall_exists_inclusionLp_ae_eq_adjoint_holderL k
  obtain ⟨Kπ, hKπ, hKπb⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_fderiv_orthogonalKerProjection m R₀ B hc k
  obtain ⟨K₁, hK₁, hK₁b⟩ :=
    exists_forall_norm_exp_mul_smul_fderiv_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le
      m R₀ B hc k
  refine ⟨K₁ * (Ct * KA + Kπ), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax hd u u' β β' M M' hb hβ hβb hb' hβ'
    hβ'b g G hG y u₀ hu₀
  have hM : 0 ≤ M := (norm_nonneg _).trans (hβb 0 0 (Nat.zero_le k) 0)
  have hM' : 0 ≤ M' := (norm_nonneg _).trans (hβ'b 0 0 (Nat.zero_le k) 0)
  -- `Z_u'† (Q† g)` and `π'_u' y`, then the estimate for `(Q†)'_u`.
  obtain ⟨ug, hug, hugn⟩ := hKAb x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax g G hG
  obtain ⟨W, hW, hWn⟩ := hCtb _ β' M' c hb' hβ' hβ'b _ ug hug
  obtain ⟨uπ, huπ, huπn⟩ :=
    hKπb x D hx hbound hxb hsol hframe hD hD₀ hax hd u' β' M' hb' hβ' hβ'b y u₀ hu₀
  obtain ⟨huπn', huπ'⟩ := norm_inclusion_le_and_ae_eq (by linarith : (k : ℝ) ≤ k + 1)
    (Nat.cast_nonneg k) huπ
  obtain ⟨U, hU, hUn⟩ := hK₁b x D hx hbound hxb hsol hframe hD hD₀ hax hd u β M hb hβ hβb _
    (fun i ↦ W i + inclusion (by linarith : (k : ℝ) ≤ k + 1) (uπ i))
    fun i ↦ coeFn_inclusionLp_add_ae_eq_exp_mul_smul_add (hW i) (huπ' i)
  refine ⟨U, hU, hUn.trans ?_⟩
  have hG : ‖G‖ ≤ ‖G‖ + ‖u₀‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hu : ‖u₀‖ ≤ ‖G‖ + ‖u₀‖ := le_add_of_nonneg_left (norm_nonneg _)
  calc K₁ * M * ‖fun i ↦ W i + inclusion (by linarith : (k : ℝ) ≤ k + 1) (uπ i)‖ ≤
        K₁ * M * (Ct * M' * (KA * (‖G‖ + ‖u₀‖)) + Kπ * M' * (‖G‖ + ‖u₀‖)) := by
        gcongr
        refine (norm_add_le W _).trans ?_
        gcongr
        · exact hWn.trans (by gcongr; exact hugn.trans (by gcongr))
        · exact huπn'.trans (huπn.trans (by gcongr))
    _ = K₁ * (Ct * KA + Kπ) * M * M' * (‖G‖ + ‖u₀‖) := by ring

/-- **The `Q` part of the second derivative of the adjoints.** For every degree `m`, radius `R₀`,
bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following property. In
the setting of
`exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_le`,
if `exp(c ρ) y` has coordinates `u₀ : Fin 4 → H^(k+1)(ℂ)`, then
`exp(c ρ) (Q (Z₂ y) + Q (Z_v (π'_w y)) + Q (Z_w (π'_v y)))` has coordinates
`U : Fin 4 → H^(k+1)(ℂ)` with `‖U‖ ≤ K (M₂ + Mv Mw) ‖u₀‖`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_orthogonalRightInverse_add (m : ℕ)
    (R₀ B : ℝ) {c : ℝ} (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (v w : X) (βv βw β₂ : ℂ → EuclideanSpace ℝ (Fin 4))
          (Mv Mw M₂ : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] βv → ContDiff ℝ ∞ βv →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βv z i) z‖ ≤ Mv) →
        fderiv ℝ a p₀ w =ᵐ[μ⊤] βw → ContDiff ℝ ∞ βw →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βw z i) z‖ ≤ Mw) →
        fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w =ᵐ[μ⊤] β₂ → ContDiff ℝ ∞ β₂ →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₂ z i) z‖ ≤ M₂) →
        ∀ (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (u₀ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
        (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) i : ℂ)) →
        ∃ U : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (U i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
              (sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
                    (sobolevGaugeFixedOperator (a p₀))
                    (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w)
                        (sobolevFieldValues y))) +
                  sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
                    (sobolevGaugeFixedOperator (a p₀))
                    (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v)
                      (sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection
                        sobolevFieldValues (sobolevGaugeFixedOperator (a p))) p₀ w y)))) +
                  sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
                    (sobolevGaugeFixedOperator (a p₀))
                    (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ w)
                      (sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection
                        sobolevFieldValues (sobolevGaugeFixedOperator (a p))) p₀ v y)))))
                z) i : ℂ)) ∧
          ‖U‖ ≤ K * (M₂ + Mv * Mw) * ‖u₀‖ := by
  obtain ⟨KS, hKS, hKSb⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_orthogonalRightInverse_holderL m R₀ B hc k
  obtain ⟨Kπ, hKπ, hKπb⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_fderiv_orthogonalKerProjection m R₀ B hc k
  refine ⟨KS * (1 + 2 * Kπ), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax hd v w βv βw β₂ Mv Mw M₂ hbv hβv hβvb
    hbw hβw hβwb hb₂ hβ₂ hβ₂b y u₀ hu₀
  have hMv : 0 ≤ Mv := (norm_nonneg _).trans (hβvb 0 0 (Nat.zero_le k) 0)
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hβwb 0 0 (Nat.zero_le k) 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hβ₂b 0 0 (Nat.zero_le k) 0)
  obtain ⟨uπv, huπv, huπvn⟩ :=
    hKπb x D hx hbound hxb hsol hframe hD hD₀ hax hd v βv Mv hbv hβv hβvb y u₀ hu₀
  obtain ⟨uπw, huπw, huπwn⟩ :=
    hKπb x D hx hbound hxb hsol hframe hD hD₀ hax hd w βw Mw hbw hβw hβwb y u₀ hu₀
  obtain ⟨uS₂, huS₂, huS₂n⟩ :=
    hKSb x D hx hxb hsol hframe hD hD₀ (a p₀) hax _ β₂ M₂ hb₂ hβ₂ hβ₂b _ u₀ hu₀
  obtain ⟨uSv, huSv, huSvn⟩ :=
    hKSb x D hx hxb hsol hframe hD hD₀ (a p₀) hax _ βv Mv hbv hβv hβvb _ uπw huπw
  obtain ⟨uSw, huSw, huSwn⟩ :=
    hKSb x D hx hxb hsol hframe hD hD₀ (a p₀) hax _ βw Mw hbw hβw hβwb _ uπv huπv
  refine ⟨uS₂ + uSv + uSw, fun i ↦ coeFn_inclusionLp_add_ae_eq_exp_mul_smul_add
    (coeFn_inclusionLp_add_ae_eq_exp_mul_smul_add (huS₂ i) (huSv i)) (huSw i), ?_⟩
  calc ‖uS₂ + uSv + uSw‖ ≤ ‖uS₂‖ + ‖uSv‖ + ‖uSw‖ := norm_add₃_le
    _ ≤ KS * M₂ * ‖u₀‖ + KS * Mv * (Kπ * Mw * ‖u₀‖) + KS * Mw * (Kπ * Mv * ‖u₀‖) := by
        gcongr
        · exact huSvn.trans (by gcongr)
        · exact huSwn.trans (by gcongr)
    _ = KS * M₂ * ‖u₀‖ + 2 * KS * Kπ * (Mv * Mw) * ‖u₀‖ := by ring
    _ ≤ KS * (M₂ + Mv * Mw) * ‖u₀‖ + 2 * KS * Kπ * (M₂ + Mv * Mw) * ‖u₀‖ := by
        gcongr
        · exact le_add_of_nonneg_right (by positivity)
        · exact le_add_of_nonneg_left hM₂
    _ = KS * (1 + 2 * Kπ) * (M₂ + Mv * Mw) * ‖u₀‖ := by ring

/-- **The `Q†` term of the second derivative of the adjoints.** For every degree `m`, radius `R₀`,
bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following property. In
the setting of
`exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_le`,
if `exp(c ρ) g` has coordinates `G : Fin 4 → H^k(ℂ)` and `exp(c ρ) y` has coordinates
`u₀ : Fin 4 → H^(k+1)(ℂ)`, then
`exp(c ρ) Q† (Q (Z₂ y + Z_v (π'_w y) + Z_w (π'_v y)) - Z₂† (Q† g))` has coordinates
`U : Fin 4 → H^(k+1)(ℂ)` with `‖U‖ ≤ K (M₂ + Mv Mw) (‖G‖ + ‖u₀‖)`. -/
private theorem exists_forall_exists_inclusionLp_ae_eq_adjoint_sub (m : ℕ) (R₀ B : ℝ) {c : ℝ}
    (hc : |c| < 1 / 2) (k : ℕ) :
    ∃ K ≥ 0, ∀ (x : ℂ → EuclideanSpace ℝ (Fin 4)) (D : Multiset ℂ), ContDiff ℝ ∞ x →
      (∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) →
      (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ B) →
      (∀ z, equation x z = 0) →
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) →
      IsZeroMultiplicity (sectionValue x) (fun z ↦ D.count z) → (∀ b ∈ D, ‖b‖ ≤ R₀) →
      ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}, a p₀ =ᵐ[μ⊤] x →
        DifferentiableAt ℝ a p₀ → ∀ (v w : X) (βv βw β₂ : ℂ → EuclideanSpace ℝ (Fin 4))
          (Mv Mw M₂ : ℝ),
        fderiv ℝ a p₀ v =ᵐ[μ⊤] βv → ContDiff ℝ ∞ βv →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βv z i) z‖ ≤ Mv) →
        fderiv ℝ a p₀ w =ᵐ[μ⊤] βw → ContDiff ℝ ∞ βw →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ βw z i) z‖ ≤ Mw) →
        fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w =ᵐ[μ⊤] β₂ → ContDiff ℝ ∞ β₂ →
        (∀ i, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ β₂ z i) z‖ ≤ M₂) →
        ∀ (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (G : Fin 4 → H^{(k : ℝ)}(ℂ)),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (G i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) i : ℂ)) →
        ∀ (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) (u₀ : Fin 4 → H^{(k : ℝ) + 1}(ℂ)),
        (∀ i, ⇑(inclusionLp (by positivity) (u₀ i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • sobolevFieldValues y z) i : ℂ)) →
        ∃ U : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (U i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
              ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
                orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p₀)))
                (sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
                    (sobolevGaugeFixedOperator (a p₀))
                    (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w)
                        (sobolevFieldValues y))) +
                  sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
                    (sobolevGaugeFixedOperator (a p₀))
                    (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v)
                      (sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection
                        sobolevFieldValues (sobolevGaugeFixedOperator (a p))) p₀ w y)))) +
                  sobolevFieldValues (orthogonalRightInverse sobolevFieldValues
                    (sobolevGaugeFixedOperator (a p₀))
                    (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ w)
                      (sobolevFieldValues (fderiv ℝ (fun p ↦ orthogonalKerProjection
                        sobolevFieldValues (sobolevGaugeFixedOperator (a p))) p₀ v y)))) -
                  ContinuousLinearMap.adjoint (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2
                    (fderiv ℝ (fun p ↦ fderiv ℝ a p v) p₀ w))
                    (ContinuousLinearMap.adjoint (sobolevFieldValues ∘L orthogonalRightInverse
                      sobolevFieldValues (sobolevGaugeFixedOperator (a p₀))) g)) z) i : ℂ)) ∧
          ‖U‖ ≤ K * (M₂ + Mv * Mw) * (‖G‖ + ‖u₀‖) := by
  obtain ⟨KA, hKA, hKAb⟩ :=
    exists_forall_norm_exp_mul_smul_adjoint_orthogonalRightInverse_le_of_forall_mem_norm_le m R₀ B
      hc k
  obtain ⟨KS, hKS, hKSb⟩ :=
    exists_forall_exists_inclusionLp_ae_eq_orthogonalRightInverse_add m R₀ B hc k
  obtain ⟨Ct, hCt, hCtb⟩ := exists_forall_exists_inclusionLp_ae_eq_adjoint_holderL k
  refine ⟨KA * (KS + Ct * KA), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax hd v w βv βw β₂ Mv Mw M₂ hbv hβv hβvb
    hbw hβw hβwb hb₂ hβ₂ hβ₂b g G hG y u₀ hu₀
  have hMv : 0 ≤ Mv := (norm_nonneg _).trans (hβvb 0 0 (Nat.zero_le k) 0)
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hβwb 0 0 (Nat.zero_le k) 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hβ₂b 0 0 (Nat.zero_le k) 0)
  have hk1 : (k : ℝ) ≤ k + 1 := by linarith
  -- The `Q` part, `Z₂† (Q† g)`, and the estimate for `Q†`.
  obtain ⟨uS, huS, huSn⟩ := hKSb x D hx hbound hxb hsol hframe hD hD₀ hax hd v w βv βw β₂ Mv Mw M₂
    hbv hβv hβvb hbw hβw hβwb hb₂ hβ₂ hβ₂b y u₀ hu₀
  obtain ⟨huSn', huS'⟩ := norm_inclusion_le_and_ae_eq hk1 (Nat.cast_nonneg k) huS
  obtain ⟨ug, hug, hugn⟩ := hKAb x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax g G hG
  obtain ⟨W₂, hW₂, hW₂n⟩ := hCtb _ β₂ M₂ c hb₂ hβ₂ hβ₂b _ ug hug
  obtain ⟨U, hU, hUn⟩ := hKAb x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax _
    (fun i ↦ inclusion hk1 (uS i) - W₂ i)
    fun i ↦ coeFn_inclusionLp_sub_ae_eq_exp_mul_smul_sub (huS' i) (hW₂ i)
  refine ⟨U, hU, hUn.trans ?_⟩
  calc KA * ‖fun i ↦ inclusion hk1 (uS i) - W₂ i‖ ≤ KA * (‖uS‖ + ‖W₂‖) := by
        gcongr
        exact (norm_sub_le (fun i ↦ inclusion hk1 (uS i)) W₂).trans (by gcongr)
    _ ≤ KA * (KS * (M₂ + Mv * Mw) * ‖u₀‖ + Ct * M₂ * (KA * ‖G‖)) := by
        gcongr
        exact hW₂n.trans (by gcongr)
    _ ≤ KA * (KS * (M₂ + Mv * Mw) * (‖G‖ + ‖u₀‖) +
        Ct * (M₂ + Mv * Mw) * (KA * (‖G‖ + ‖u₀‖))) := by
        gcongr
        · exact le_add_of_nonneg_left (norm_nonneg _)
        · exact le_add_of_nonneg_right (by positivity)
        · exact le_add_of_nonneg_right (norm_nonneg _)
    _ = KA * (KS + Ct * KA) * (M₂ + Mv * Mw) * (‖G‖ + ‖u₀‖) := by ring

/-- **The weighted Sobolev estimate for the second parameter derivative of the adjoints of the
orthogonal right inverses, uniformly over a window of divisors.** For every degree `m`, radius
`R₀`, bound `B`, rate `|c| < 1/2` and order `k` there is a constant `K` with the following
property, where `ρ(z) = √(1 + |z|²)`. Let `x` be a smooth plane vortex with the degree-`m` end
framing whose zeros lie in the closed disc of radius `R₀` and whose coordinates have bounded
derivatives of every order, bounded by `B` through order `k`. Let `a` be a family of `L∞`
coefficients, `C²` at `p₀`, with `a p₀` the class of `x`, and let `Q p` be the right inverse of the
realization `L_(a p)` with values `L²`-orthogonal to its kernel, read as an operator on
`L²(ℂ; ℝ⁴)` through the values of the fields. Write `(Q†)''` for the derivative at `p₀` along `w`
of `p ↦ D(Q†)(p) v` and `a''` for that of `p ↦ Da(p) v`. Suppose `Da(p₀) v`, `Da(p₀) w` and `a''`
are the classes of smooth fields whose coordinates have derivatives bounded through order `k` by
`Mv`, `Mw` and `M₂`. If the coordinates of `exp(c ρ) g` are given by `G : Fin 4 → H^k(ℂ)`, then
those of `exp(c ρ) (Q†)'' g` are given by some `u : Fin 4 → H^(k+1)(ℂ)` with
`‖u‖ ≤ K (M₂ + Mv Mw) ‖G‖`. That is,

`‖exp(c ρ) (Q†)'' g‖_(H^(k+1)) ≤ K (M₂ + Mv Mw) ‖exp(c ρ) g‖_(H^k)`,

with `K` depending only on `m`, `R₀`, `B`, `c` and `k`. The weighted `L²` estimate is
`exists_forall_eLpNorm_exp_mul_smul_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_le`. -/
theorem exists_forall_norm_exp_mul_smul_fderiv_fun_fderiv_adjoint_orthogonalRightInverse_le
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
        ∀ (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (G : Fin 4 → H^{(k : ℝ)}(ℂ)),
        (∀ i, ⇑(inclusionLp (Nat.cast_nonneg k) (G i)) =ᵐ[volume]
          fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) • g z) i : ℂ)) →
        ∃ u : Fin 4 → H^{(k : ℝ) + 1}(ℂ),
          (∀ i, ⇑(inclusionLp (by positivity) (u i)) =ᵐ[volume]
            fun z ↦ ((Real.exp (c * √(1 + ‖z‖ ^ 2)) •
              fderiv ℝ (fun p ↦ fderiv ℝ (fun p ↦ ContinuousLinearMap.adjoint (sobolevFieldValues ∘L
                orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator (a p)))) p v g)
                  p₀ w z) i : ℂ)) ∧
          ‖u‖ ≤ K * (M₂ + Mv * Mw) * ‖G‖ := by
  obtain ⟨K₀, hK₀, hK₀b⟩ :=
    exists_forall_exists_mem_ker_inner_sub_eq_zero_and_inclusionLp_ae_eq m R₀ B hc k
  obtain ⟨K₁, hK₁, hK₁b⟩ := exists_forall_exists_inclusionLp_ae_eq_adjoint_sub m R₀ B hc k
  obtain ⟨K₂, hK₂, hK₂b⟩ := exists_forall_exists_inclusionLp_ae_eq_fderiv_adjoint_add m R₀ B hc k
  refine ⟨(K₁ + 2 * K₂) * (1 + K₀), by positivity, ?_⟩
  intro x D hx hbound hxb hsol hframe hD hD₀ X _ _ a p₀ hax ha v w βv βw β₂ Mv Mw M₂ hbv hβv hβvb
    hbw hβw hβwb hb₂ hβ₂ hβ₂b g G hG
  have hd : DifferentiableAt ℝ a p₀ := ha.differentiableAt (by simp)
  have hMv : 0 ≤ Mv := (norm_nonneg _).trans (hβvb 0 0 (Nat.zero_le k) 0)
  have hMw : 0 ≤ Mw := (norm_nonneg _).trans (hβwb 0 0 (Nat.zero_le k) 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (hβ₂b 0 0 (Nat.zero_le k) 0)
  -- The projection `y₀` of `g` onto the values of the kernel, and the three terms of `(Q†)'' g`.
  obtain ⟨y₀, hy₀, horth, u₀, hu₀, hu₀n⟩ :=
    hK₀b x D hx hbound hxb hsol hframe hD hD₀ (a p₀) hax g G hG
  obtain ⟨u₁, hu₁, hu₁n⟩ := hK₁b x D hx hbound hxb hsol hframe hD hD₀ hax hd v w βv βw β₂ Mv Mw M₂
    hbv hβv hβvb hbw hβw hβwb hb₂ hβ₂ hβ₂b g G hG y₀ u₀ hu₀
  obtain ⟨u₂, hu₂, hu₂n⟩ := hK₂b x D hx hbound hxb hsol hframe hD hD₀ hax hd w v βw βv Mw Mv
    hbw hβw hβwb hbv hβv hβvb g G hG y₀ u₀ hu₀
  obtain ⟨u₃, hu₃, hu₃n⟩ := hK₂b x D hx hbound hxb hsol hframe hD hD₀ hax hd v w βv βw Mv Mw
    hbv hβv hβvb hbw hβw hβwb g G hG y₀ u₀ hu₀
  refine ⟨u₁ - u₂ - u₃, fun i ↦ ((coeFn_inclusionLp_sub_ae_eq_exp_mul_smul_sub
    (coeFn_inclusionLp_sub_ae_eq_exp_mul_smul_sub (hu₁ i) (hu₂ i)) (hu₃ i))).trans
      (.of_forall fun z ↦ ?_), ?_⟩
  · rw [fderiv_fun_fderiv_adjoint_orthogonalRightInverse_apply_eq hx hsol hframe hax ha v w g hy₀
      horth]
    simp only [map_add]
  have hu₀G : ‖G‖ + ‖u₀‖ ≤ (1 + K₀) * ‖G‖ := by linarith
  calc ‖u₁ - u₂ - u₃‖ ≤ ‖u₁‖ + ‖u₂‖ + ‖u₃‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ K₁ * (M₂ + Mv * Mw) * (‖G‖ + ‖u₀‖) + K₂ * Mw * Mv * (‖G‖ + ‖u₀‖) +
        K₂ * Mv * Mw * (‖G‖ + ‖u₀‖) := add_le_add (add_le_add hu₁n hu₂n) hu₃n
    _ = (K₁ * (M₂ + Mv * Mw) + 2 * K₂ * (Mv * Mw)) * (‖G‖ + ‖u₀‖) := by ring
    _ ≤ (K₁ * (M₂ + Mv * Mw) + 2 * K₂ * (M₂ + Mv * Mw)) * ((1 + K₀) * ‖G‖) := by
        gcongr
        linarith
    _ = (K₁ + 2 * K₂) * (1 + K₀) * (M₂ + Mv * Mw) * ‖G‖ := by ring

end TauCeti.Vortex
