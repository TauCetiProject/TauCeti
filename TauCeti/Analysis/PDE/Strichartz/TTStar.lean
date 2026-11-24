/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Integral.RieszPotential.Basic
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Integral.Kernel.Pairing
import TauCeti.MeasureTheory.Integral.Prod

/-!
# The non-endpoint `TT*` argument

Let `U(t) : H → L²(X, μ)`, `t ∈ ℝ`, be a family of bounded operators from a Hilbert space into
an `L²` space, for instance a unitary propagator `exp(itΔ)` on `H = L²(ℝⁿ)`. Strichartz estimates
bound `t ↦ U(t) f` in the mixed norm `L^q_t L^r_x`. By duality, they are equivalent to bounds on
`∫ U(s)* F(s) ds` in `H` for `F` in the dual mixed norm `L^{q'}_t L^{r'}_x`, and the `TT*`
argument reduces those to the time pairings `U(s) U(t)*`:

`‖∫ U(s)* F(s) ds‖² = ∫∫ ⟪U(s)* F(s), U(t)* F(t)⟫ ds dt = ∫∫ ⟪F(s), U(s) U(t)* F(t)⟫ ds dt`.

Suppose these pairings decay like `|s - t| ^ (-2 / q)` from `L^{r'}` to `L^r`:

`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}`,  `s ≠ t`.

For a family with the energy bound `‖U(t)‖ ≤ 1` and the dispersive bound
`‖U(s) U(t)* g‖_∞ ≤ |s - t| ^ (-σ) ‖g‖₁`, Riesz–Thorin interpolation gives this with
`2 / q = σ (1 - 2 / r)`, which is exactly the condition `1 / q + σ / r = σ / 2` that `(q, r)` be
`σ`-admissible. For the Schrödinger propagator on `ℝⁿ`, `σ = n / 2`.

Hölder's inequality in space then bounds each pairing by
`A |s - t| ^ (-2 / q) ‖F(s)‖_{r'} ‖G(t)‖_{r'}`, and when `2 < q < ∞` the time integral of this
kernel is a fractional integral of order `1 - 2 / q` on `ℝ`. The Hardy–Littlewood–Sobolev
inequality maps `L^{q'}` to `L^q` under it, and in its bilinear form
(`TauCeti.exists_lintegral_lintegral_mul_enorm_sub_rpow_mul_le`) the double integral is at most
`C A ‖F‖_{L^{q'} L^{r'}} ‖G‖_{L^{q'} L^{r'}}`, with `C` independent of the family `U`, of `A`
and of `F` and `G`. The bound is on the double integral of the absolute values of the pairings, so
it also controls every truncation of the double integral, for instance to `s < t`, which is the
form taken by retarded (Duhamel) estimates.

The mixed norm of a function `F : ℝ → L²(X, μ)` is written
`eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p volume`; for almost everywhere strongly measurable `F` the
inner norm is an almost everywhere measurable function of time
(`MeasureTheory.AEStronglyMeasurable.aemeasurable_eLpNorm_Lp`).

The endpoint `q = 2`, where the time kernel `|s - t| ^ (-1)` is not locally integrable and
Hardy–Littlewood–Sobolev fails, needs the Keel–Tao argument instead.

At the other end, `q = ∞`, only the pairings at equal times matter. A single bounded operator
`U` with `‖U U* g‖_r ≤ A ‖g‖_{r'}` satisfies `‖U* g‖² = ⟪g, U U* g⟫ ≤ A ‖g‖_{r'}²`, so `U*` maps
`L^{r'}` to `H` with norm at most `A ^ (1 / 2)`; for a family `U(t)` with this bound at every time,
Minkowski's inequality in time gives the dual and homogeneous estimates with `L¹` in time on the
dual side.

## Main declarations

* `TauCeti.exists_lintegral_lintegral_enorm_inner_le`: the bilinear estimate
  `∫∫ |⟪F(s), T(s, t) G(t)⟫| ds dt ≤ C A ‖F‖_{L^{q'} L^{r'}} ‖G‖_{L^{q'} L^{r'}}` for any two-time
  family `T(s, t)` decaying like `A |s - t| ^ (-2 / q)` from `L^{r'}` to `L^r`.
* `TauCeti.enorm_inner_le_of_eLpNorm_le_rpow`: a single pairing of such a family,
  `|⟪f, T(s, t) g⟫| ≤ A |s - t| ^ (-γ) ‖f‖_{r'} ‖g‖_{r'}`.
* `TauCeti.exists_lintegral_lintegral_enorm_inner_adjoint_le`: the bilinear `TT*` estimate
  `∫∫ |⟪U(s)* F(s), U(t)* G(t)⟫| ds dt ≤ C A ‖F‖_{L^{q'} L^{r'}} ‖G‖_{L^{q'} L^{r'}}`.
* `TauCeti.enorm_integral_setIntegral_Iio_le_lintegral_lintegral_enorm`: the truncation to
  `s < t` of a pairing integral is bounded by the full integral of its absolute value, which
  reduces retarded estimates to the bilinear one.
* `TauCeti.enorm_integral_le_sqrt_mul_of_enorm_integral_inner_le`: `TT*` for a time integral, a
  bound on `∫∫ ⟪u(s), u(t)⟫ ds dt` bounds `‖∫ u‖`.
* `TauCeti.exists_enorm_integral_adjoint_le`: the dual homogeneous estimate
  `‖∫ U(s)* F(s) ds‖ ≤ C A ^ (1 / 2) ‖F‖_{L^{q'} L^{r'}}`.
* `TauCeti.exists_enorm_integral_inner_apply_le`: the homogeneous estimate in weak form,
  `|∫ ⟪U(t) f, G(t)⟫ dt| ≤ C A ^ (1 / 2) ‖f‖ ‖G‖_{L^{q'} L^{r'}}`.
* `TauCeti.enorm_adjoint_apply_le`: the `TT*` argument for a single operator,
  `‖U* g‖ ≤ A ^ (1 / 2) ‖g‖_{r'}`.
* `TauCeti.enorm_integral_adjoint_le_eLpNorm_one` and
  `TauCeti.enorm_integral_inner_apply_le_eLpNorm_one`: the dual and homogeneous estimates at
  `q = ∞`, `‖∫ U(s)* F(s) ds‖ ≤ A ^ (1 / 2) ‖F‖_{L¹ L^{r'}}` and
  `|∫ ⟪U(t) f, G(t)⟫ dt| ≤ A ^ (1 / 2) ‖f‖ ‖G‖_{L¹ L^{r'}}`.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
* J. Ginibre and G. Velo, *The global Cauchy problem for the nonlinear Schrödinger equation
  revisited*, Ann. Inst. H. Poincaré Anal. Non Linéaire 2 (1985), 309–327.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

variable {𝕜 X E H : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {r r' : ℝ≥0∞} [r'.HolderConjugate r]

/-- A single pairing of a decaying two-time family: Hölder's inequality in space and the decay
`‖T(s, t) g‖_r ≤ A |s - t| ^ (-γ) ‖g‖_{r'}` bound `|⟪f, T(s, t) g⟫|` by
`A |s - t| ^ (-γ) ‖f‖_{r'} ‖g‖_{r'}`. -/
theorem enorm_inner_le_of_eLpNorm_le_rpow {T : ℝ → ℝ → Lp E 2 μ → Lp E 2 μ} {A : ℝ≥0∞} {γ : ℝ}
    (hT : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (T s t g) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {s t : ℝ} (hst : s ≠ t) (f g : Lp E 2 μ) :
    ‖⟪f, T s t g⟫_𝕜‖ₑ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm f r' μ * eLpNorm g r' μ := by
  rw [L2.inner_def]
  calc _ ≤ eLpNorm f r' μ * eLpNorm (T s t g) r μ := enorm_integral_inner_le
    _ ≤ eLpNorm f r' μ * (A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ) := by
        gcongr
        exact hT s t hst g
    _ = _ := by ring

/-- **The bilinear estimate for a decaying two-time family.** Let `2 < q < ∞` with Hölder
conjugate `p`, and let `T(s, t)` act on `L²(X, μ)` with decay from `L^{r'}` to `L^r`,
`‖T(s, t) g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for almost everywhere strongly
measurable `F, G : ℝ → L²(X, μ)`,

`∫∫ |⟪F(s), T(s, t) G(t)⟫| ds dt ≤ C A ‖F‖_{L^p L^{r'}} ‖G‖_{L^p L^{r'}}`,

with `C` independent of the family `T`, of `A` and of `F` and `G`. The time pairings
`T(s, t) = U(s) U(t)*` of the `TT*` argument are one instance
(`TauCeti.exists_lintegral_lintegral_enorm_inner_adjoint_le`); Duhamel kernels such as
`T(s, t) = W(s - t) P` for a propagator `W` and a fixed operator `P` are another. Since the
integrand is the absolute value of the pairing, the same bound holds for the integral over any
part of the `(s, t)` plane, such as `s < t`. -/
theorem exists_lintegral_lintegral_enorm_inner_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (T : ℝ → ℝ → Lp E 2 μ → Lp E 2 μ) (A : ℝ≥0∞),
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (T s t g) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ F G : ℝ → Lp E 2 μ, AEStronglyMeasurable F → AEStronglyMeasurable G →
        ∫⁻ s, ∫⁻ t, ‖⟪F s, T s t (G t)⟫_𝕜‖ₑ ≤
          C * A * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p *
            eLpNorm (fun t ↦ eLpNorm (G t) r' μ) p := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast zero_lt_two.trans hq
  -- The time exponents fit the bilinear Hardy–Littlewood–Sobolev inequality of order
  -- `1 - 2 / q` on `ℝ`, whose kernel is `|s - t| ^ (-2 / q)`.
  have hpq' : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - (1 - 2 / q) / Module.finrank ℝ ℝ := by
    have h := hpq.coe.inv_add_inv_eq_one
    rw [Module.finrank_self, Nat.cast_one, div_one]
    field_simp at h ⊢
    linarith
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_mul_enorm_sub_rpow_mul_le (volume : Measure ℝ)
    (α := 1 - 2 / q) (by rw [sub_pos, div_lt_one hq0]; exact_mod_cast hq) hpq.lt hpq' hpq
  rw [Module.finrank_self, Nat.cast_one, sub_sub_cancel_left] at hC
  refine ⟨C, fun T A hT F G hF hG => ?_⟩
  calc ∫⁻ s, ∫⁻ t, ‖⟪F s, T s t (G t)⟫_𝕜‖ₑ
      ≤ ∫⁻ s, ∫⁻ t,
          eLpNorm (F s) r' μ * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * (A * eLpNorm (G t) r' μ) := by
        refine lintegral_mono fun s ↦ lintegral_mono_ae ?_
        -- The diagonal `t = s` is a null set.
        filter_upwards [ae_iff.2 (by simp : volume {t : ℝ | ¬ t ≠ s} = 0)] with t ht
        exact (enorm_inner_le_of_eLpNorm_le_rpow hT (Ne.symm ht) _ _).trans_eq (by ring)
    _ ≤ C * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p *
          eLpNorm (fun t ↦ A * eLpNorm (G t) r' μ) p := by
        -- Hardy–Littlewood–Sobolev in time, for the mixed-norm profiles of `F` and `A G`.
        exact hC _ _ (hF.aemeasurable_eLpNorm_Lp .rfl r')
          ((hG.aemeasurable_eLpNorm_Lp .rfl r').const_mul A)
    _ = _ := by
        rw [eLpNorm_const_mul_ennreal_of_pos (by exact_mod_cast hpq.pos)]
        ring

/-- The reduction of a retarded estimate to the bilinear one: the pairing integrated over the
region `s < t` is bounded by the integral of its absolute value over the whole `(s, t)` plane. -/
theorem enorm_integral_setIntegral_Iio_le_lintegral_lintegral_enorm {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : ℝ → ℝ → V) :
    ‖∫ t, ∫ s in Set.Iio t, f s t‖ₑ ≤ ∫⁻ t, ∫⁻ s, ‖f s t‖ₑ :=
  enorm_integral_setIntegral_le_lintegral_lintegral f

variable [CompleteSpace E]

/-- A single time pairing: Hölder's inequality in space and the decay of `U(s) U(t)*` bound
`|⟪U(s)* f, U(t)* g⟫|` by `A |s - t| ^ (-γ) ‖f‖_{r'} ‖g‖_{r'}`. -/
theorem enorm_inner_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞} {γ : ℝ}
    (hU : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm g r' μ)
    {s t : ℝ} (hst : s ≠ t) (f g : Lp E 2 μ) :
    ‖⟪((U s)†) f, ((U t)†) g⟫_𝕜‖ₑ ≤ A * ‖s - t‖ₑ ^ (-γ) * eLpNorm f r' μ * eLpNorm g r' μ := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact enorm_inner_le_of_eLpNorm_le_rpow (T := fun s t g ↦ U s (((U t)†) g)) hU hst f g

/-- **The `TT*` argument at a single time.** If `U : H → L²(X, μ)` is bounded and `U U*` maps
`L^{r'}` to `L^r`, `‖U U* g‖_r ≤ A ‖g‖_{r'}` for every `g ∈ L²(X, μ)`, then `U*` maps `L^{r'}` to
`H`: `‖U* g‖ ≤ A ^ (1 / 2) ‖g‖_{r'}`. Indeed `‖U* g‖² = ⟪g, U U* g⟫ ≤ ‖g‖_{r'} ‖U U* g‖_r` by
Hölder's inequality in space. -/
theorem enorm_adjoint_apply_le {U : H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    (hU : ∀ g : Lp E 2 μ, eLpNorm (U ((U†) g)) r μ ≤ A * eLpNorm g r' μ) (g : Lp E 2 μ) :
    ‖(U†) g‖ₑ ≤ A ^ (2⁻¹ : ℝ) * eLpNorm g r' μ := by
  have hsq : ‖(U†) g‖ₑ ^ (2 : ℝ) ≤ A * eLpNorm g r' μ * eLpNorm g r' μ := by
    calc ‖(U†) g‖ₑ ^ (2 : ℝ) = ‖⟪(U†) g, (U†) g⟫_𝕜‖ₑ := by
          rw [inner_self_eq_norm_sq_to_K, eNorm_pow, ← ENNReal.rpow_natCast]
          simp
      _ = ‖∫ x, ⟪g x, U ((U†) g) x⟫_𝕜 ∂μ‖ₑ := by
          rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
      _ ≤ eLpNorm g r' μ * eLpNorm (U ((U†) g)) r μ := enorm_integral_inner_le
      _ ≤ eLpNorm g r' μ * (A * eLpNorm g r' μ) := by
          gcongr
          exact hU g
      _ = _ := by ring
  have hrhs : (A ^ (2⁻¹ : ℝ) * eLpNorm g r' μ) ^ (2 : ℝ) =
      A * eLpNorm g r' μ * eLpNorm g r' μ := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one, ENNReal.rpow_two]
    ring
  rwa [← ENNReal.rpow_le_rpow_iff (z := 2) two_pos, hrhs]

/-- **The bilinear `TT*` estimate.** Let `2 < q < ∞` with Hölder conjugate `p`, and let
`U(t) : H → L²(X, μ)` be bounded operators whose time pairings decay from `L^{r'}` to `L^r`,
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for almost everywhere strongly
measurable `F, G : ℝ → L²(X, μ)`,

`∫∫ |⟪U(s)* F(s), U(t)* G(t)⟫| ds dt ≤ C A ‖F‖_{L^p L^{r'}} ‖G‖_{L^p L^{r'}}`,

with `C` independent of the family `U`, of `A` and of `F` and `G`. This is the case
`T(s, t) = U(s) U(t)*` of `TauCeti.exists_lintegral_lintegral_enorm_inner_le`. Since the
integrand is the absolute value of the pairing, the same bound holds for the integral over any
part of the `(s, t)` plane, such as `s < t`. -/
theorem exists_lintegral_lintegral_enorm_inner_adjoint_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A : ℝ≥0∞),
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ F G : ℝ → Lp E 2 μ, AEStronglyMeasurable F → AEStronglyMeasurable G →
        ∫⁻ s, ∫⁻ t, ‖⟪((U s)†) (F s), ((U t)†) (G t)⟫_𝕜‖ₑ ≤
          C * A * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p *
            eLpNorm (fun t ↦ eLpNorm (G t) r' μ) p := by
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_le (𝕜 := 𝕜) (E := E) (μ := μ)
    (r := r) (r' := r') hq hpq
  refine ⟨C, fun U A hU F G hF hG => ?_⟩
  simp_rw [ContinuousLinearMap.adjoint_inner_left]
  exact hC (fun s t g ↦ U s (((U t)†) g)) A hU F G hF hG

variable [NormedSpace ℝ H]

omit [CompleteSpace E] in
/-- **`TT*` for a time integral.** For an integrable `u : ℝ → H`, `‖∫ u‖²` is the integral of the
pairings `⟪u(s), u(t)⟫` over the plane, so a bound `|∫∫ ⟪u(s), u(t)⟫ ds dt| ≤ C a²` gives
`‖∫ u‖ ≤ √C a`. -/
theorem enorm_integral_le_sqrt_mul_of_enorm_integral_inner_le {u : ℝ → H} (hu : Integrable u)
    {C : ℝ≥0} {a : ℝ≥0∞}
    (h : ‖∫ z, ⟪u z.1, u z.2⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤ C * a * a) :
    ‖∫ t, u t‖ₑ ≤ NNReal.sqrt C * a := by
  have hsq : ‖∫ t, u t‖ₑ ^ (2 : ℝ) ≤ C * a * a := by
    calc ‖∫ t, u t‖ₑ ^ (2 : ℝ) = ‖⟪∫ s, u s, ∫ t, u t⟫_𝕜‖ₑ := by
          rw [inner_self_eq_norm_sq_to_K, eNorm_pow, ← ENNReal.rpow_natCast]
          simp
      _ = ‖∫ z, ⟪u z.1, u z.2⟫_𝕜 ∂(volume.prod volume)‖ₑ := by
          rw [inner_integral_integral_eq_integral_prod hu hu]
      _ ≤ C * a * a := h
  have hrhs : ((NNReal.sqrt C : ℝ≥0∞) * a) ^ (2 : ℝ) = C * a * a := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ENNReal.rpow_two, ENNReal.rpow_two,
      ← ENNReal.coe_pow, NNReal.sq_sqrt, sq]
    ring
  rwa [← ENNReal.rpow_le_rpow_iff (z := 2) two_pos, hrhs]

/-- **The dual homogeneous `TT*` estimate.** Let `2 < q < ∞` with Hölder conjugate `p`, and let
`U(t) : H → L²(X, μ)` be bounded operators with
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for every almost everywhere
strongly measurable `F : ℝ → L²(X, μ)`,

`‖∫ U(s)* F(s) ds‖ ≤ C A ^ (1 / 2) ‖F‖_{L^p L^{r'}}`,

with `C` independent of the family `U`, of `A` and of `F`. No integrability of `s ↦ U(s)* F(s)` is
assumed: without it the Bochner integral is `0`. -/
theorem exists_enorm_integral_adjoint_le {p q : ℝ≥0} (hq : 2 < q) (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A : ℝ≥0∞),
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ F : ℝ → Lp E 2 μ, AEStronglyMeasurable F →
        ‖∫ s, ((U s)†) (F s)‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p := by
  obtain ⟨C, hC⟩ := exists_lintegral_lintegral_enorm_inner_adjoint_le (𝕜 := 𝕜) (H := H)
    (E := E) (μ := μ) (r := r) (r' := r') hq hpq
  refine ⟨NNReal.sqrt C, fun U A hU F hF => ?_⟩
  by_cases hUF : Integrable fun s ↦ ((U s)†) (F s)
  swap
  · rw [integral_undef hUF, eNorm_zero]
    exact zero_le
  set a := eLpNorm (fun s ↦ eLpNorm (F s) r' μ) p
  have hA : A ^ (2⁻¹ : ℝ) * A ^ (2⁻¹ : ℝ) = A := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  -- `TT*`, with `A ^ (1 / 2) a` in place of `a`.
  rw [mul_assoc]
  refine enorm_integral_le_sqrt_mul_of_enorm_integral_inner_le (𝕜 := 𝕜) hUF ?_
  calc _ ≤ ∫⁻ z, ‖⟪((U z.1)†) (F z.1), ((U z.2)†) (F z.2)⟫_𝕜‖ₑ ∂(volume.prod volume) :=
        eNorm_integral_le_lintegral_eNorm _
    _ = ∫⁻ s, ∫⁻ t, ‖⟪((U s)†) (F s), ((U t)†) (F t)⟫_𝕜‖ₑ :=
        lintegral_prod _ (hUF.inner_fst_snd hUF).aestronglyMeasurable.eNorm
    _ ≤ C * A * a * a := hC U A hU F F hF hF
    _ = C * (A ^ (2⁻¹ : ℝ) * a) * (A ^ (2⁻¹ : ℝ) * a) := by
        nth_rw 1 [← hA]
        ring

/-- **The homogeneous `TT*` estimate in weak form.** Let `2 < q < ∞` with Hölder conjugate `p`,
and let `U(t) : H → L²(X, μ)` be bounded operators with
`‖U(s) U(t)* g‖_r ≤ A |s - t| ^ (-2 / q) ‖g‖_{r'}` for `s ≠ t`. Then for every `f ∈ H` and every
almost everywhere strongly measurable `G : ℝ → L²(X, μ)` for which `t ↦ U(t)* G(t)` is
integrable,

`|∫ ⟪U(t) f, G(t)⟫ dt| ≤ C A ^ (1 / 2) ‖f‖ ‖G‖_{L^p L^{r'}}`,

with `C` independent of the family `U`, of `A`, of `f` and of `G`. This is the estimate
`‖U(·) f‖_{L^q L^r} ≤ C A ^ (1 / 2) ‖f‖` tested against `G`. -/
theorem exists_enorm_integral_inner_apply_le {p q : ℝ≥0} (hq : 2 < q)
    (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0, ∀ (U : ℝ → H →L[𝕜] Lp E 2 μ) (A : ℝ≥0∞),
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) r μ ≤ A * ‖s - t‖ₑ ^ (-(2 / q : ℝ)) * eLpNorm g r' μ) →
      ∀ (f : H) (G : ℝ → Lp E 2 μ), AEStronglyMeasurable G →
        Integrable (fun t ↦ ((U t)†) (G t)) →
        ‖∫ t, ⟪U t f, G t⟫_𝕜‖ₑ ≤
          C * A ^ (2⁻¹ : ℝ) * ‖f‖ₑ * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) p := by
  obtain ⟨C, hC⟩ := exists_enorm_integral_adjoint_le (𝕜 := 𝕜) (H := H) (E := E) (μ := μ)
    (r := r) (r' := r') hq hpq
  refine ⟨C, fun U A hU f G hG hUG => ?_⟩
  simp_rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [integral_inner hUG]
  calc _ ≤ ‖f‖ₑ * ‖∫ t, ((U t)†) (G t)‖ₑ := eNorm_inner_le_eNorm _ _
    _ ≤ ‖f‖ₑ * (C * A ^ (2⁻¹ : ℝ) * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) p) := by
        gcongr
        exact hC U A hU G hG
    _ = _ := by ring

/-- **The dual `TT*` estimate at `q = ∞`.** Let `U(t) : H → L²(X, μ)` be bounded operators with
`‖U(t) U(t)* g‖_r ≤ A ‖g‖_{r'}` for every time `t` and every `g ∈ L²(X, μ)`. Then for every
almost everywhere strongly measurable `F : ℝ → L²(X, μ)`,

`‖∫ U(s)* F(s) ds‖ ≤ A ^ (1 / 2) ‖F‖_{L¹ L^{r'}}`.

Unlike the estimates for `2 < q < ∞`, this needs no decay of the pairings `U(s) U(t)*` for
`s ≠ t`: the bound at equal times and Minkowski's inequality suffice. -/
theorem enorm_integral_adjoint_le_eLpNorm_one {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    (hU : ∀ t (g : Lp E 2 μ), eLpNorm (U t (((U t)†) g)) r μ ≤ A * eLpNorm g r' μ)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) :
    ‖∫ s, ((U s)†) (F s)‖ₑ ≤ A ^ (2⁻¹ : ℝ) * eLpNorm (fun s ↦ eLpNorm (F s) r' μ) 1 := by
  calc ‖∫ s, ((U s)†) (F s)‖ₑ ≤ ∫⁻ s, ‖((U s)†) (F s)‖ₑ := eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ s, A ^ (2⁻¹ : ℝ) * eLpNorm (F s) r' μ :=
        lintegral_mono fun s ↦ enorm_adjoint_apply_le (hU s) (F s)
    _ = _ := by
        have h := hF.aemeasurable_eLpNorm_Lp .rfl r'
        rw [lintegral_const_mul'' _ h, eLpNorm_one_eq_lintegral_eNorm h.aestronglyMeasurable]
        simp only [eNorm_eq_self]

omit [NormedSpace ℝ H] in
/-- **The homogeneous `TT*` estimate at `q = ∞`**, in weak form. Let `U(t) : H → L²(X, μ)` be
bounded operators with `‖U(t) U(t)* g‖_r ≤ A ‖g‖_{r'}` for every time `t` and every
`g ∈ L²(X, μ)`. Then for every `f ∈ H` and every almost everywhere strongly measurable
`G : ℝ → L²(X, μ)`,

`|∫ ⟪U(t) f, G(t)⟫ dt| ≤ A ^ (1 / 2) ‖f‖ ‖G‖_{L¹ L^{r'}}`.

This is the estimate `‖U(·) f‖_{L^∞ L^r} ≤ A ^ (1 / 2) ‖f‖` tested against `G`. -/
theorem enorm_integral_inner_apply_le_eLpNorm_one {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0∞}
    (hU : ∀ t (g : Lp E 2 μ), eLpNorm (U t (((U t)†) g)) r μ ≤ A * eLpNorm g r' μ) (f : H)
    {G : ℝ → Lp E 2 μ} (hG : AEStronglyMeasurable G) :
    ‖∫ t, ⟪U t f, G t⟫_𝕜‖ₑ ≤ A ^ (2⁻¹ : ℝ) * ‖f‖ₑ * eLpNorm (fun t ↦ eLpNorm (G t) r' μ) 1 := by
  calc ‖∫ t, ⟪U t f, G t⟫_𝕜‖ₑ ≤ ∫⁻ t, ‖⟪U t f, G t⟫_𝕜‖ₑ := eNorm_integral_le_lintegral_eNorm _
    _ ≤ ∫⁻ t, A ^ (2⁻¹ : ℝ) * ‖f‖ₑ * eLpNorm (G t) r' μ := by
        refine lintegral_mono fun t ↦ ?_
        rw [← ContinuousLinearMap.adjoint_inner_right]
        calc _ ≤ ‖f‖ₑ * ‖((U t)†) (G t)‖ₑ := eNorm_inner_le_eNorm _ _
          _ ≤ ‖f‖ₑ * (A ^ (2⁻¹ : ℝ) * eLpNorm (G t) r' μ) := by
              gcongr
              exact enorm_adjoint_apply_le (hU t) (G t)
          _ = _ := by ring
    _ = _ := by
        have h := hG.aemeasurable_eLpNorm_Lp .rfl r'
        rw [lintegral_const_mul'' _ h, eLpNorm_one_eq_lintegral_eNorm h.aestronglyMeasurable]
        simp only [eNorm_eq_self]

end TauCeti
