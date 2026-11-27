/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev

/-!
# Lower-order terms of the divergence-form energy form on `H¹(Ω)`

With bounded drift `b` and mass `c`, the energy form

`a(u, v) = ∫_Ω aⁱʲ ∂ⱼu ∂ᵢv + bⁱ ∂ᵢu v + c u v`

of `TauCeti.Analysis.PDE.EnergyForm.Sobolev` splits into its principal part and the `L²` pairing
of `⟪b, ∇u⟫ + c u` with `v`. This file records that split and moves the lower-order terms
between the two sides of a weak equation.

## Main results

* `TauCeti.PDE.energyFormH1_eq_principal_add_setIntegral`: with bounded lower-order
  coefficients the energy form is that of its principal part plus the `L²` pairing of
  `⟪b, ∇u⟫ + c u` with `v`; `TauCeti.PDE.memLp_inner_gradient` and
  `TauCeti.PDE.memLp_lowerOrder`: `⟪b, ∇u⟫ ∈ L²(Ω)` and `⟪b, ∇u⟫ + c u ∈ L²(Ω)`.
* `TauCeti.PDE.energyFormH1_eq_energyFormH1_zero_add_setIntegral_inner`: with bounded lower-order
  coefficients the energy form is that of the operator without drift plus the pairing
  `∫_Ω ⟪b, ∇u⟫ v`.
* `TauCeti.PDE.lowerOrderL`: the lower-order part `u ↦ ⟪b, ∇u⟫ + c u` as a bounded operator
  `H¹(Ω) → L²(Ω)`, with norm at most `(‖b‖_∞ + ‖c‖_∞) ‖J‖` for the jet map `J`
  (`TauCeti.PDE.norm_lowerOrderL_le_eLpNorm`), hence at most `(|β| + |γ|) ‖J‖` for bounds
  `‖b‖ ≤ β`, `|c| ≤ γ` (`TauCeti.PDE.norm_lowerOrderL_le`), and
  `TauCeti.PDE.energyFormH1_eq_principal_add_inner_lowerOrderL`: tested against `H¹₀(Ω)`, the
  energy form is that of its principal part plus the `L²` pairing of `TauCeti.PDE.lowerOrderL`
  with the value.
* `TauCeti.PDE.energyFormH1_principal_eq_setIntegral_sub` and
  `TauCeti.PDE.exists_forcing_energyFormH1_principal_eq`: a weak equation with bounded
  lower-order coefficients gives a weak equation for its principal part with the `L²` forcing
  `f - ⟪b, ∇u⟫ - c u`; `TauCeti.PDE.energyFormH1_eq_setIntegral_of_principal_eq_sub` is the
  converse.
* `TauCeti.PDE.eLpNorm_sub_inner_gradient_sub_mul_value_le`: the bound
  `‖f - ⟪b, ∇u⟫ - c u‖₂ ≤ ‖f‖₂ + ‖b‖_∞ ‖∇u‖₂ + ‖c‖_∞ ‖u‖₂` on that forcing.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.2; D. Gilbarg and N. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Chapter 8.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- A bounded drift paired with the gradient of an `H¹` function is square integrable. -/
theorem memLp_inner_gradient {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hb : MemLp b ⊤ (mu.restrict Omega)) (u : W1p mu Omega 2) :
    MemLp (fun x => ⟪b x, W1p.gradient u x⟫_ℝ) 2 (mu.restrict Omega) :=
  MemLp.of_bilin (inner ℝ) 1 hb (Lp.memLp _) continuous_inner
    (.of_forall fun x => by simpa using nnNorm_inner_le_nnNorm (b x) (W1p.gradient u x))

/-- With bounded lower-order coefficients, `⟪b, ∇u⟫ + c u` is square integrable. -/
theorem memLp_lowerOrder {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ} (hb : MemLp b ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (u : W1p mu Omega 2) :
    MemLp (fun x => ⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x) 2 (mu.restrict Omega) :=
  (memLp_inner_gradient hb u).add (hc.fun_mul (Lp.memLp _))

/-- With bounded lower-order coefficients, the forcing `f - ⟪b, ∇u⟫ - c u` of the principal
equation is square integrable. -/
private theorem memLp_forcing_principal {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ} (hb : MemLp b ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) :
    MemLp (fun x => f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x) 2
      (mu.restrict Omega) :=
  ((Lp.memLp f).sub (memLp_lowerOrder hb hc u)).ae_eq
    (.of_forall fun _ => sub_add_eq_sub_sub _ _ _)

/-- **Splitting off the lower-order terms.** With an essentially bounded principal energy density
and bounded lower-order coefficients, the energy form of `-∂ᵢ(aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u` is that of
its principal part plus the `L²` pairing of `⟪b, ∇u⟫ + c u` with `v`:

`a(u, v) = ∫_Ω ⟨∇v, a ∇u⟩ + ∫_Ω (⟪b, ∇u⟫ + c u) v`. -/
theorem energyFormH1_eq_principal_add_setIntegral {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    (u v : W1p mu Omega 2) :
    energyFormH1 a b c u v = energyFormH1 a 0 0 u v +
      ∫ x in Omega, (⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x) * W1p.value v x ∂mu := by
  -- The energy form splits drift and mass apart, so each needs its own integrability; their sum
  -- `⟪b, ∇u⟫ + c u` is `TauCeti.PDE.memLp_lowerOrder`.
  have hv := Lp.memLp (W1p.value v)
  have hBv : Integrable (fun x => ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value v x)
      (mu.restrict Omega) := (memLp_inner_gradient hb u).integrable_mul hv
  have hC : MemLp (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) := hc.fun_mul (Lp.memLp _)
  have hCv : Integrable (fun x => (c x * W1p.value u x) * W1p.value v x) (mu.restrict Omega) :=
    hC.integrable_mul hv
  -- The drift and mass densities are integrable, so the energy form splits into its pieces.
  have hdrift : Integrable (fun x => energyIntegrand 0 (b x) 0 (jetField u x) (jetField v x))
      (mu.restrict Omega) := by
    simpa [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply] using hBv
  have hmass : Integrable (fun x => energyIntegrand 0 0 (c x) (jetField u x) (jetField v x))
      (mu.restrict Omega) := by
    simpa [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply] using hCv
  have hdrift_eq : energyFormIntegral (mu.restrict Omega) (fun _ => 0) b (fun _ => 0)
      (jetField u) (jetField v) =
        ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value v x ∂mu := by
    rw [energyFormIntegral_def]
    simp [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply]
  have hmass_eq : energyFormIntegral (mu.restrict Omega) (fun _ => 0) (fun _ => 0) c
      (jetField u) (jetField v) = ∫ x in Omega, (c x * W1p.value u x) * W1p.value v x ∂mu := by
    rw [energyFormIntegral_def]
    simp [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply]
  -- Both forms are read as `energyFormIntegral`. The split lemma writes the vanishing lower-order
  -- coefficients as `fun _ => 0`, so the goal's `0` is put in that form by `Pi.zero_def`.
  rw [energyFormH1_def, ← energyFormIntegral_def, energyFormIntegral_principal_drift_mass _ _ _ _
    _ _ (integrable_energyIntegrand_jetField ha u _) hdrift hmass, hdrift_eq, hmass_eq,
    energyFormH1_def, ← energyFormIntegral_def, Pi.zero_def, Pi.zero_def, add_assoc,
    ← integral_add hBv hCv]
  simp only [add_mul]

/-- **Splitting off the drift.** With an essentially bounded principal energy density and bounded
lower-order coefficients, the energy form of `-∂ᵢ(aⁱʲ ∂ⱼ·) + bⁱ ∂ᵢ + c` is that of
`-∂ᵢ(aⁱʲ ∂ⱼ·) + c` plus the drift pairing:

`a_{b,c}(u, v) = a_{0,c}(u, v) + ∫_Ω ⟪b, ∇u⟫ v`. -/
theorem energyFormH1_eq_energyFormH1_zero_add_setIntegral_inner
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    (u v : W1p mu Omega 2) :
    energyFormH1 a b c u v = energyFormH1 a 0 c u v +
      ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value v x ∂mu := by
  have hv := Lp.memLp (W1p.value v)
  have hBv : Integrable (fun x => ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value v x) (mu.restrict Omega) :=
    (memLp_inner_gradient hb u).integrable_mul hv
  have hC : MemLp (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) := hc.fun_mul (Lp.memLp _)
  have hCv : Integrable (fun x => c x * W1p.value u x * W1p.value v x) (mu.restrict Omega) :=
    hC.integrable_mul hv
  rw [energyFormH1_eq_principal_add_setIntegral ha hb hc,
    energyFormH1_eq_principal_add_setIntegral ha MemLp.zero hc, add_assoc]
  congr 1
  rw [← integral_add (hCv.congr (ae_of_all _ fun x => by simp)) hBv]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Pi.zero_apply, inner_zero_left, zero_add]
  ring

/-- **Moving the lower-order terms to the right-hand side.** If `u ∈ H¹(Ω)` is a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u = f` in `Ω`, with an essentially bounded principal energy density,
bounded lower-order coefficients and `f ∈ L²(Ω)`, then `u` is a weak solution of the principal
equation `-∂ᵢ(aⁱʲ ∂ⱼu) = f - ⟪b, ∇u⟫ - c u`: for every `v ∈ H¹₀(Ω)`,

`∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω (f - ⟪b, ∇u⟫ - c u) v`.

Neither ellipticity nor a boundary condition on the solution is required. The converse is
`TauCeti.PDE.energyFormH1_eq_setIntegral_of_principal_eq_sub`. -/
theorem energyFormH1_principal_eq_setIntegral_sub {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (v : W1p0 mu Omega 2) :
    energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, (f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x) *
        W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hv := Lp.memLp (W1p.value (v : W1p mu Omega 2))
  have hF : Integrable (fun x => f x * W1p.value (v : W1p mu Omega 2) x)
      (mu.restrict Omega) := (Lp.memLp f).integrable_mul hv
  have hL : Integrable (fun x => (⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x) *
      W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) :=
    (memLp_lowerOrder hb hc u).integrable_mul hv
  have h := hu v
  rw [energyFormH1_eq_principal_add_setIntegral ha hb hc] at h
  rw [eq_sub_of_add_eq h, ← integral_sub hF hL]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **Moving the lower-order terms to the left-hand side.** If `u ∈ H¹(Ω)` is a weak solution of
the principal equation `-∂ᵢ(aⁱʲ ∂ⱼu) = f - ⟪b, ∇u⟫ - c u` in `Ω`, with an essentially bounded
principal energy density, bounded lower-order coefficients and `f ∈ L²(Ω)`, then `u` is a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u = f`: for every `v ∈ H¹₀(Ω)`, `B(u, v) = ∫_Ω f v`.
This is the converse of `TauCeti.PDE.energyFormH1_principal_eq_setIntegral_sub`. -/
theorem energyFormH1_eq_setIntegral_of_principal_eq_sub {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, (f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x) *
          W1p.value (v : W1p mu Omega 2) x ∂mu)
    (v : W1p0 mu Omega 2) :
    energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hv := Lp.memLp (W1p.value (v : W1p mu Omega 2))
  have hF : Integrable (fun x => f x * W1p.value (v : W1p mu Omega 2) x)
      (mu.restrict Omega) := hf.integrable_mul hv
  have hL : Integrable (fun x => (⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x) *
      W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) :=
    (memLp_lowerOrder hb hc u).integrable_mul hv
  have hG : Integrable (fun x => (f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x) *
      W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) :=
    (hF.sub hL).congr (.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  rw [energyFormH1_eq_principal_add_setIntegral ha hb hc, hu v, ← integral_add hG hL]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-- **The size of the forcing of the principal equation.** For `f ∈ L²(Ω)`, `u ∈ H¹(Ω)` and
essentially bounded `b, c`, the forcing `f - ⟪b, ∇u⟫ - c u` of the principal equation satisfies

`‖f - ⟪b, ∇u⟫ - c u‖_{L²(Ω)} ≤ ‖f‖_{L²(Ω)} + ‖b‖_{L∞(Ω)} ‖∇u‖_{L²(Ω)} + ‖c‖_{L∞(Ω)} ‖u‖_{L²(Ω)}`. -/
theorem eLpNorm_sub_inner_gradient_sub_mul_value_le {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ} (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega)) (f : EuclideanSpace ℝ ι → ℝ)
    (u : W1p mu Omega 2) :
    eLpNorm (fun x => f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x) 2
        (mu.restrict Omega) ≤ eLpNorm f 2 (mu.restrict Omega) +
      eLpNorm b ⊤ (mu.restrict Omega) * eLpNorm (W1p.gradient u) 2 (mu.restrict Omega) +
      eLpNorm c ⊤ (mu.restrict Omega) * eLpNorm (W1p.value u) 2 (mu.restrict Omega) := by
  have h2 : eLpNorm (fun x => ⟪b x, W1p.gradient u x⟫_ℝ) 2 (mu.restrict Omega) ≤
      ((1 : NNReal) : ENNReal) * eLpNorm b ⊤ (mu.restrict Omega) *
        eLpNorm (W1p.gradient u) 2 (mu.restrict Omega) :=
    eLpNorm_le_eLpNorm_top_mul_eLpNorm 2 (fun v w => ⟪v, w⟫_ℝ) 1 continuous_inner hb
      (.of_forall fun x => by simpa using nnNorm_inner_le_nnNorm (b x) (W1p.gradient u x))
  have h3 : eLpNorm (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) ≤
      eLpNorm c ⊤ (mu.restrict Omega) * eLpNorm (W1p.value u) 2 (mu.restrict Omega) :=
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hc
  refine (eLpNorm_sub_le one_le_two).trans (add_le_add ((eLpNorm_sub_le one_le_two).trans
    (add_le_add le_rfl (h2.trans_eq (by rw [ENNReal.coe_one, one_mul])))) h3)

/-- A weak equation with an essentially bounded principal energy density and bounded
lower-order coefficients admits an `L²` forcing `g` for its principal part alone, with

`‖g‖_{L²(Ω)} ≤ ‖f‖_{L²(Ω)} + ‖b‖_{L∞(Ω)} ‖∇u‖_{L²(Ω)} + ‖c‖_{L∞(Ω)} ‖u‖_{L²(Ω)}`.

Neither ellipticity nor a boundary condition on the solution is required. The forcing is
`f - ⟪b, ∇u⟫ - c u` (`TauCeti.PDE.energyFormH1_principal_eq_setIntegral_sub`). -/
theorem exists_forcing_energyFormH1_principal_eq {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ g : Lp ℝ 2 (mu.restrict Omega), (∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu) ∧
      ‖g‖ ≤ ‖f‖ + (eLpNorm b ⊤ (mu.restrict Omega)).toReal * ‖W1p.gradient u‖ +
        (eLpNorm c ⊤ (mu.restrict Omega)).toReal * ‖W1p.value u‖ := by
  have hG := memLp_forcing_principal hb hc f u
  refine ⟨hG.toLp _, fun v => ?_, ?_⟩
  · rw [energyFormH1_principal_eq_setIntegral_sub ha hb hc hu v]
    refine integral_congr_ae ?_
    filter_upwards [hG.coeFn_toLp] with x hx
    rw [hx]
  have hbfin := hb.eLpNorm_lt_top.ne
  have hcfin := hc.eLpNorm_lt_top.ne
  rw [Lp.norm_toLp, Lp.norm_def, Lp.norm_def, Lp.norm_def]
  refine (ENNReal.toReal_mono (by finiteness) (eLpNorm_sub_inner_gradient_sub_mul_value_le
    hb.aestronglyMeasurable hc.aestronglyMeasurable f u)).trans_eq ?_
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness)
    (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul]

/-- The lower-order part `u ↦ ⟪b, ∇u⟫ + c u` of a divergence-form operator with bounded
coefficients, as a bounded operator `H¹(Ω) → L²(Ω)`. Its values are characterised by
`TauCeti.PDE.lowerOrderL_apply_ae`. -/
def lowerOrderL (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega)) :
    W1p mu Omega 2 →L[ℝ] Lp ℝ 2 (mu.restrict Omega) :=
  LinearMap.mkContinuous
    { toFun u := (memLp_lowerOrder hb hc u).toLp _
      map_add' u v := by
        refine Lp.ext ?_
        filter_upwards [(memLp_lowerOrder hb hc (u + v)).coeFn_toLp,
          Lp.coeFn_add ((memLp_lowerOrder hb hc u).toLp _) ((memLp_lowerOrder hb hc v).toLp _),
          (memLp_lowerOrder hb hc u).coeFn_toLp, (memLp_lowerOrder hb hc v).coeFn_toLp,
          W1p.value_add_ae u v, Lp.coeFn_add (W1p.gradient u) (W1p.gradient v)]
          with x h1 h2 h3 h4 h5 h6
        rw [h1, h2, Pi.add_apply, h3, h4, h5, W1p.gradient_add, h6]
        simp only [Pi.add_apply, inner_add_right]
        ring
      map_smul' r u := by
        refine Lp.ext ?_
        filter_upwards [(memLp_lowerOrder hb hc (r • u)).coeFn_toLp,
          Lp.coeFn_smul r ((memLp_lowerOrder hb hc u).toLp _),
          (memLp_lowerOrder hb hc u).coeFn_toLp,
          W1p.value_smul_ae r u, Lp.coeFn_smul r (W1p.gradient u)] with x h1 h2 h3 h4 h5
        rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, W1p.gradient_smul, h5]
        simp only [Pi.smul_apply, smul_eq_mul, inner_smul_right]
        ring }
    (((eLpNorm b ⊤ (mu.restrict Omega)).toReal + (eLpNorm c ⊤ (mu.restrict Omega)).toReal) *
      ‖(jetLpL : W1p mu Omega 2 →L[ℝ] _)‖) fun u => by
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_assoc]
      refine (Lp.norm_le_mul_norm_of_ae_le_mul ?_).trans
        (mul_le_mul_of_nonneg_left (jetLpL.le_opNorm u) (by positivity))
      -- The coefficients are bounded almost everywhere by their `L^∞` norms.
      filter_upwards [(memLp_lowerOrder hb hc u).coeFn_toLp, jetLpL_apply_ae u,
        ae_le_eLpNormEssSup (f := b), ae_le_eLpNormEssSup (f := c)] with x h1 h2 hbx hcx
      rw [← eLpNorm_exponent_top hb.aestronglyMeasurable] at hbx
      rw [← eLpNorm_exponent_top hc.aestronglyMeasurable] at hcx
      rw [h1, h2, jetField_apply, Prod.norm_def, Real.norm_eq_abs]
      calc |⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x|
          ≤ ‖b x‖ * ‖W1p.gradient u x‖ + ‖c x‖ * ‖W1p.value u x‖ := by
            refine (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _) ?_)
            rw [abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ (eLpNorm b ⊤ (mu.restrict Omega)).toReal * ‖W1p.gradient u x‖ +
              (eLpNorm c ⊤ (mu.restrict Omega)).toReal * ‖W1p.value u x‖ := by
            rw [← toReal_eNorm (b x), ← toReal_eNorm (c x)]
            gcongr
            exacts [hb.eLpNorm_ne_top, hc.eLpNorm_ne_top]
        _ ≤ ((eLpNorm b ⊤ (mu.restrict Omega)).toReal +
              (eLpNorm c ⊤ (mu.restrict Omega)).toReal) *
                max ‖W1p.value u x‖ ‖W1p.gradient u x‖ := by
            rw [add_mul]
            gcongr
            · exact le_max_right _ _
            · exact le_max_left _ _

/-- The operator norm of the lower-order operator is at most `(‖b‖_∞ + ‖c‖_∞) ‖J‖`, where
`J = TauCeti.PDE.jetLpL` sends an `H¹` function to its value-gradient jet in `L²`: this is the
bound `TauCeti.PDE.lowerOrderL` is built with. -/
theorem norm_lowerOrderL_le_eLpNorm (hb : MemLp b ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) :
    ‖lowerOrderL hb hc‖ ≤
      ((eLpNorm b ⊤ (mu.restrict Omega)).toReal + (eLpNorm c ⊤ (mu.restrict Omega)).toReal) *
        ‖(jetLpL : W1p mu Omega 2 →L[ℝ] Lp (ℝ × EuclideanSpace ℝ ι) 2 (mu.restrict Omega))‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The lower-order operator is almost everywhere `⟪b, ∇u⟫ + c u`. -/
theorem lowerOrderL_apply_ae (hb : MemLp b ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (u : W1p mu Omega 2) :
    lowerOrderL hb hc u =ᵐ[mu.restrict Omega]
      fun x => ⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x :=
  (memLp_lowerOrder hb hc u).coeFn_toLp

/-- The operator norm of the lower-order operator is at most `(|β| + |γ|) ‖J‖` when `‖b‖ ≤ β` and
`|c| ≤ γ` almost everywhere on `Ω`, where `J = TauCeti.PDE.jetLpL` sends an `H¹` function to its
value-gradient jet in `L²`. -/
theorem norm_lowerOrderL_le (hb : MemLp b ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) {beta gamma : ℝ}
    (hb_bound : ∀ᵐ x ∂mu.restrict Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂mu.restrict Omega, ‖c x‖ ≤ gamma) :
    ‖lowerOrderL hb hc‖ ≤ (|beta| + |gamma|) *
      ‖(jetLpL : W1p mu Omega 2 →L[ℝ] Lp (ℝ × EuclideanSpace ℝ ι) 2 (mu.restrict Omega))‖ := by
  -- An almost everywhere bound `|f| ≤ r` bounds the essential supremum of `f`; it is applied to
  -- the pointwise norms of `b` and `c`, which have the same `L^∞` norms.
  have hsup {f : EuclideanSpace ℝ ι → ℝ} {r : ℝ} (hf : AEStronglyMeasurable f (mu.restrict Omega))
      (hr : ∀ᵐ x ∂mu.restrict Omega, ‖f x‖ ≤ r) :
      (eLpNorm f ⊤ (mu.restrict Omega)).toReal ≤ |r| := by
    rw [eLpNorm_exponent_top hf]
    exact ENNReal.toReal_le_of_le_ofReal (abs_nonneg _)
      (eLpNormEssSup_le_of_ae_bound (hr.mono fun x hx => hx.trans (le_abs_self _)))
  have hb' := hsup hb.aestronglyMeasurable.norm (by simpa using hb_bound)
  have hc' := hsup hc.aestronglyMeasurable.norm (by simpa using hc_bound)
  rw [eLpNorm_norm b hb.aestronglyMeasurable] at hb'
  rw [eLpNorm_norm c hc.aestronglyMeasurable] at hc'
  exact (norm_lowerOrderL_le_eLpNorm hb hc).trans
    (mul_le_mul_of_nonneg_right (add_le_add hb' hc') (ContinuousLinearMap.opNorm_nonneg _))

/-- Paired with the value of a function in `H¹₀(Ω)`, the lower-order operator gives the
lower-order terms of the energy form. -/
theorem inner_lowerOrderL_valueL (hb : MemLp b ⊤ (mu.restrict Omega))
    (hc : MemLp c ⊤ (mu.restrict Omega)) (u : W1p mu Omega 2)
    (v : W1p0 mu Omega 2) :
    ⟪lowerOrderL hb hc u, W1p0.valueL v⟫_ℝ =
      ∫ x in Omega, (⟪b x, W1p.gradient u x⟫_ℝ + c x * W1p.value u x) *
        W1p.value (v : W1p mu Omega 2) x ∂mu := by
  rw [MeasureTheory.L2.inner_def, W1p0.valueL_apply]
  refine integral_congr_ae ?_
  filter_upwards [lowerOrderL_apply_ae hb hc u] with x hx
  rw [hx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- **The lower-order terms as an `L²` pairing.** With an essentially bounded principal energy
density and bounded lower-order coefficients, the energy form is that of its principal part plus
the `L²` pairing of the lower-order operator `TauCeti.PDE.lowerOrderL` with the value of a
function in `H¹₀(Ω)`:

`a(u, v) = ∫_Ω ⟨∇v, a ∇u⟩ + ⟪⟪b, ∇u⟫ + c u, v⟫_{L²}`. -/
theorem energyFormH1_eq_principal_add_inner_lowerOrderL
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    (u : W1p mu Omega 2) (v : W1p0 mu Omega 2) :
    energyFormH1 a b c u (v : W1p mu Omega 2) =
      energyFormH1 a 0 0 u (v : W1p mu Omega 2) + ⟪lowerOrderL hb hc u, W1p0.valueL v⟫_ℝ := by
  rw [energyFormH1_eq_principal_add_setIntegral ha hb hc, inner_lowerOrderL_valueL hb hc]

end Domain

end PDE

end TauCeti
