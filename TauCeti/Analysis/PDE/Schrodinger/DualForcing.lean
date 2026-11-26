/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import TauCeti.Analysis.PDE.Schrodinger.MixedNorm
import TauCeti.Analysis.PDE.Schrodinger.EnergyPair
import TauCeti.Analysis.PDE.Schrodinger.Endpoint
import TauCeti.Analysis.PDE.Schrodinger.WeakSolution
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.LpValuedRepresentative
import TauCeti.MeasureTheory.Function.Lp.MixedNorm
import TauCeti.MeasureTheory.Function.Lp.MixedNorm.Bounded

/-!
# The Schrödinger equation with forcing in a dual Strichartz space

On a finite-dimensional real inner product space `E` of dimension `n`, let `S(t) = exp(itΔ)` be the
Schrödinger propagator and let `(q₁, r₁)` be an admissible pair with a finite time exponent:
`2 ≤ q₁ < ∞` and `2 / q₁ + n / r₁ = n / 2`, with `n ≥ 3` when `q₁ = 2`. Write `p₁` and `r₁'` for
the Hölder conjugates of `q₁` and `r₁`, so that `L^{p₁}_t L^{r₁'}_x` is the dual Strichartz space
of `(q₁, r₁)`. Duhamel's formula `TauCeti.schrodingerDuhamel` solves `i ∂ₜu + Δu = F`,
`u(0) = f`, for forcings `F : ℝ → L²(E)` that are integrable in time, so that
`∫_0^t S(t - s) F(s) ds` is a Bochner integral in `L²`. The Strichartz estimates
(`TauCeti.exists_eLpNorm_eLpNorm_schrodingerDuhamel_le`) only see the norm of `F` in
`L^{p₁}_t L^{r₁'}_x`, and this file extends the solution to every forcing in that space, by
completion.

The forcing space is the Bochner space `L^{p₁}(I; L^{r₁'}(E))` on a measurable set of times `I`,
`Lp (Lp ℂ r₁' volume) p₁ (volume.restrict I)`. Its elements need not take values in `L²`. Those
that have an `L²`-valued representative integrable on `I` are dense, since `r₁'` and `p₁` are
finite: the indicators `1_A c` of sets of finite measure span a dense subspace, and every
`c ∈ L^{r₁'}` is a limit of Schwartz functions (`MeasureTheory.Lp.dense_integrableRepSubmodule`).
On them the retarded integral
`t ↦ ∫_{s < t} S(t - s) (1_I F)(s) ds` is a bounded continuous function of time with values in
`L²`, and its supremum is at most `C ‖F‖_{L^{p₁}(I; L^{r₁'})}`
(`TauCeti.exists_enorm_setIntegral_schrodingerPropagator_sub_le`). So it extends uniquely to a
continuous linear map

`TauCeti.schrodingerRetardedL p₁ r₁' I : L^{p₁}(I; L^{r₁'}) →L[ℂ] (ℝ →ᵇ L²(E))`.

For a second admissible pair `(q, r)` with a finite time exponent, the retarded Strichartz estimate
`‖schrodingerRetardedL p₁ r₁' I Φ‖_{L^q_t L^r_x} ≤ C ‖Φ‖_{L^{p₁}(I; L^{r₁'})}` passes from the dense
subspace to every `Φ` by duality: the solution is tested against bounded `L²`-valued functions of
time, and the pairing is continuous in `Φ`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_bounded_le`).

For `I = (0, T]` and `f ∈ L²(E)`, the function `u(t) = S(t) f - i schrodingerRetardedL p₁ r₁' I Φ t`
is therefore continuous in time with values in `L²`, satisfies
`sup_t ‖u(t)‖₂ ≤ ‖f‖₂ + C ‖Φ‖_{L^{p₁}((0, T]; L^{r₁'})}` and
`‖u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖₂ + ‖Φ‖_{L^{p₁}((0, T]; L^{r₁'})})` with `C` independent of `T`,
and is Duhamel's formula, with the forcing cut off to `(0, T]`, whenever `Φ` has an integrable
`L²`-valued representative.

It solves `i ∂ₜu + Δu = Φ`, `u(0) = f`, in the sense of distributions in space: for every Schwartz
function `φ`, which lies in `L^{r₁}` and so pairs with the values `Φ(s) ∈ L^{r₁'}` of the forcing,
and every `t ≥ 0`,

`⟪φ, u t⟫ = ⟪φ, f⟫ + i (∫_{(0,t]} ⟪Δφ, u s⟫ ds - ∫_{(0,t] ∩ (0,T]} ∫ ⟪φ(x), Φ(s)(x)⟫ dx ds)`

(`TauCeti.inner_toLp_schrodingerPropagator_sub_smul_schrodingerRetardedL`). Both sides are
continuous in `Φ`, and on forcings with an integrable `L²`-valued representative this is the weak
formulation of Duhamel's formula, `TauCeti.inner_toLp_schrodingerDuhamel`. Conversely, a function
continuous on `[0, T₀]` with values in `L²` that satisfies this identity for `t ∈ [0, T₀]` is `u`
there
(`TauCeti.eqOn_schrodingerPropagator_sub_smul_schrodingerRetardedL_of_forall_inner_toLp_eq`), by
the uniqueness of weak solutions of the free equation tested against Schwartz functions,
`TauCeti.eqOn_zero_of_forall_inner_toLp_eq_I_mul_setIntegral_inner_toLp_laplacian`. So the Cauchy
problem with forcing in the dual Strichartz space is uniquely solvable in `C([0, T₀]; L²)`.

## Main declarations

* `TauCeti.schrodingerRetardedL`: the retarded integral on `L^p(I; L^{r'})`.
* `TauCeti.schrodingerRetardedL_apply_of_ae_eq`: it is the Bochner integral
  `∫_{s < t} S(t - s) (1_I F)(s) ds` when `Φ` has an `L²`-valued representative `F` integrable on
  `I`.
* `TauCeti.eq_schrodingerRetardedL`: it is the only continuous linear map with this property.
* `TauCeti.exists_norm_schrodingerRetardedL_le`: the energy bound
  `sup_t ‖schrodingerRetardedL p₁ r₁' I Φ t‖₂ ≤ C ‖Φ‖`, uniformly in `I`.
* `TauCeti.exists_eLpNorm_eLpNorm_schrodingerRetardedL_le`: the retarded Strichartz estimate in
  `L^q_t L^r_x`, uniformly in `I`.
* `TauCeti.schrodingerDuhamel_eq_sub_smul_schrodingerRetardedL`: for `t ≥ 0`, Duhamel's formula
  with the forcing cut off to `(0, T]` is `S(t) f - i schrodingerRetardedL p₁ r₁' (0, T] Φ t`.
* `TauCeti.exists_eLpNorm_eLpNorm_schrodingerPropagator_sub_smul_schrodingerRetardedL_le`: the
  Strichartz estimate for this solution on `[0, T]`, uniformly in `T`.
* `TauCeti.inner_toLp_schrodingerPropagator_sub_smul_schrodingerRetardedL`: this solution solves
  the equation in the sense of distributions in space.
* `TauCeti.eqOn_schrodingerPropagator_sub_smul_schrodingerRetardedL_of_forall_inner_toLp_eq`: it is
  the only such solution continuous in time with values in `L²`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.3 and Section 2.3.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Theorem 1.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction Laplacian SchwartzMap

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The retarded integral of an integrable forcing -/

section Integrable

variable {μ : Measure ℝ} {H : ℝ → Lp ℂ 2 (volume : Measure E)}

open scoped Classical in
variable (μ) in
/-- The retarded integral `t ↦ ∫_{s < t} S(t - s) H(s) dμ(s)` of an integrable forcing `H`, as a
bounded continuous function of time; `0` if `H` is not integrable. -/
private def retardedBCF [NullSingletonClass μ] (H : ℝ → Lp ℂ 2 (volume : Measure E)) :
    ℝ →ᵇ Lp ℂ 2 (volume : Measure E) :=
  if hH : Integrable H μ then
    .ofNormedAddCommGroup (fun t ↦ ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (H s) ∂μ)
      (continuous_setIntegral_Iio_phasePropagator_sub _ hH) _
      (norm_setIntegral_Iio_phasePropagator_sub_le _ hH)
  else 0

private theorem retardedBCF_apply [NullSingletonClass μ] (hH : Integrable H μ) (t : ℝ) :
    retardedBCF μ H t = ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (H s) ∂μ := by
  simp [retardedBCF, hH]

private theorem retardedBCF_congr [NullSingletonClass μ] {H' : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hH : Integrable H μ) (h : H =ᵐ[μ] H') : retardedBCF μ H = retardedBCF μ H' := by
  ext1 t
  rw [retardedBCF_apply hH, retardedBCF_apply (hH.congr h)]
  exact setIntegral_congr_ae₀ nullMeasurableSet_Iio (h.mono fun s hs _ ↦ by rw [hs])

private theorem retardedBCF_add [NullSingletonClass μ] {H' : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hH : Integrable H μ) (hH' : Integrable H' μ) :
    retardedBCF μ (H + H') = retardedBCF μ H + retardedBCF μ H' := by
  ext1 t
  rw [add_apply, retardedBCF_apply (hH.add hH'), retardedBCF_apply hH,
    retardedBCF_apply hH', ← integral_add]
  · simp
  · exact (integrable_phasePropagator_apply _ (by fun_prop) hH).integrableOn
  · exact (integrable_phasePropagator_apply _ (by fun_prop) hH').integrableOn

private theorem retardedBCF_smul [NullSingletonClass μ] (hH : Integrable H μ) (c : ℂ) :
    retardedBCF μ (c • H) = c • retardedBCF μ H := by
  ext1 t
  rw [smul_apply, retardedBCF_apply (hH.smul c), retardedBCF_apply hH,
    ← integral_smul]
  simp

/-- On a measurable set of times `I`, the retarded integral against `volume` restricted to `I` is
the retarded integral of the forcing cut off to `I`. -/
private theorem setIntegral_Iio_restrict_eq_indicator {I : Set ℝ} (hI : MeasurableSet I)
    (F : ℝ → Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (F s) ∂volume.restrict I =
      ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (I.indicator F s) := by
  have hind (s : ℝ) : schrodingerPropagator ℂ (t - s) (I.indicator F s) =
      I.indicator (fun s ↦ schrodingerPropagator ℂ (t - s) (F s)) s := by
    by_cases hs : s ∈ I <;> simp [hs]
  simp_rw [Measure.restrict_restrict measurableSet_Iio, hind, setIntegral_indicator hI]

end Integrable


/-! ### Forcings with an integrable `L²`-valued representative -/

section Lift

variable (p r' : ℝ≥0∞) [Fact (1 ≤ r')] (I : Set ℝ)

variable (E) in
/-- The forcings `Φ ∈ L^p(I; L^{r'})` with an integrable `L²`-valued representative: some
`F : ℝ → L²`, integrable on `I`, with `Φ(s) = F(s)` almost everywhere for almost every `s ∈ I`. -/
private abbrev liftSubmodule :
    Submodule ℂ (Lp (Lp ℂ r' (volume : Measure E)) p (volume.restrict I)) :=
  Lp.integrableRepSubmodule ℂ ℂ r' volume p (volume.restrict I) 2

variable {p r' I}

/-- A chosen integrable `L²`-valued representative of a forcing in `liftSubmodule`. -/
private def lift (Φ : liftSubmodule E p r' I) : ℝ → Lp ℂ 2 (volume : Measure E) :=
  (Lp.mem_integrableRepSubmodule_iff.1 Φ.property).choose

private theorem integrableOn_lift (Φ : liftSubmodule E p r' I) : IntegrableOn (lift Φ) I :=
  (Lp.mem_integrableRepSubmodule_iff.1 Φ.property).choose_spec.1

private theorem ae_eq_lift (Φ : liftSubmodule E p r' I) :
    ∀ᵐ s ∂volume.restrict I, ((Φ : Lp (Lp ℂ r' (volume : Measure E)) p
      (volume.restrict I)) s : E → ℂ) =ᵐ[volume] lift Φ s :=
  (Lp.mem_integrableRepSubmodule_iff.1 Φ.property).choose_spec.2

variable (p r' I) in
/-- The retarded integral of a forcing in `liftSubmodule`, computed from its `L²`-valued
representative. -/
private def retardedOnLift :
    liftSubmodule E p r' I →ₗ[ℂ] ℝ →ᵇ Lp ℂ 2 (volume : Measure E) where
  toFun Φ := retardedBCF (volume.restrict I) (lift Φ)
  map_add' Φ Ψ := by
    rw [← retardedBCF_add (integrableOn_lift Φ) (integrableOn_lift Ψ)]
    exact retardedBCF_congr (integrableOn_lift _) (Lp.ae_eq_of_ae_ae_eq (ae_eq_lift (Φ + Ψ))
      (Lp.ae_ae_eq_add (ae_eq_lift Φ) (ae_eq_lift Ψ)))
  map_smul' c Φ := by
    rw [RingHom.id_apply, ← retardedBCF_smul (integrableOn_lift Φ)]
    exact retardedBCF_congr (integrableOn_lift _) (Lp.ae_eq_of_ae_ae_eq (ae_eq_lift (c • Φ))
      (Lp.ae_ae_eq_smul (ae_eq_lift Φ) c))

private theorem retardedOnLift_apply (Φ : liftSubmodule E p r' I) :
    retardedOnLift p r' I Φ = retardedBCF (volume.restrict I) (lift Φ) :=
  rfl

private theorem retardedOnLift_apply_of_ae_eq
    {Φ : liftSubmodule E p r' I} {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : IntegrableOn F I)
    (hΦF : ∀ᵐ s ∂volume.restrict I, ((Φ : Lp (Lp ℂ r' (volume : Measure E)) p
      (volume.restrict I)) s : E → ℂ) =ᵐ[volume] F s) (t : ℝ) :
    retardedOnLift p r' I Φ t =
      ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (F s) ∂volume.restrict I := by
  rw [retardedOnLift_apply,
    retardedBCF_congr (integrableOn_lift Φ) (Lp.ae_eq_of_ae_ae_eq (ae_eq_lift Φ) hΦF),
    retardedBCF_apply hF]

/-! ### Density -/

private theorem denseRange_subtype_liftSubmodule [Fact (1 ≤ p)] (hp : p ≠ ∞) (hr' : r' ≠ ∞) :
    DenseRange (liftSubmodule E p r' I).subtype :=
  (Lp.dense_integrableRepSubmodule (𝕜 := ℂ) (μ := (volume : Measure E)) (ρ := volume.restrict I)
    (s := 2) hp hr').denseRange_subtypeVal

/-! ### The retarded integral on the dual Strichartz space -/

variable (p r' I) in
/-- **The retarded Duhamel integral with forcing in `L^p(I; L^{r'})`.** For a forcing
`F : ℝ → L²(E)` integrable on `I`, the retarded integral `t ↦ ∫_{s < t} S(t - s) (1_I F)(s) ds` is
a bounded continuous function of time with values in `L²`. When `p` and `r'` are the Hölder
conjugates of an admissible pair `(q, r)` with a finite time exponent, its supremum is bounded by
`C ‖F‖_{L^p(I; L^{r'})}` (`TauCeti.exists_enorm_setIntegral_schrodingerPropagator_sub_le`), and
such forcings are dense in `L^p(I; L^{r'})`; `schrodingerRetardedL p r' I` is then the continuous
linear extension of the retarded integral to all of `L^p(I; L^{r'})`. It agrees with the Bochner
integral on forcings with an integrable `L²`-valued representative
(`TauCeti.schrodingerRetardedL_apply_of_ae_eq`) and is the only continuous linear map that does
(`TauCeti.eq_schrodingerRetardedL`). For other exponents its value carries no meaning. -/
def schrodingerRetardedL [Fact (1 ≤ p)] :
    Lp (Lp ℂ r' (volume : Measure E)) p (volume.restrict I) →L[ℂ]
      ℝ →ᵇ Lp ℂ 2 (volume : Measure E) :=
  (retardedOnLift p r' I).extendOfNorm (liftSubmodule E p r' I).subtype

section Estimates

variable {p₁ q₁ : ℝ≥0} {r₁ r₁' : ℝ≥0∞} [Fact (1 ≤ (p₁ : ℝ≥0∞))] [Fact (1 ≤ r₁')]
  [r₁'.HolderConjugate r₁]

/-- The energy bound `sup_t ‖∫_{s < t} S(t - s) (1_I F)(s) ds‖₂ ≤ C ‖F‖_{L^{p₁}(I; L^{r₁'})}` on
the forcings with an integrable `L²`-valued representative. -/
private theorem exists_norm_retardedOnLift_le (hq₁ : 2 ≤ q₁)
    (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ {I : Set ℝ}, MeasurableSet I → ∀ Φ : liftSubmodule E p₁ r₁' I,
      ‖retardedOnLift (p₁ : ℝ≥0∞) r₁' I Φ‖ ≤ C * ‖(liftSubmodule E p₁ r₁' I).subtype Φ‖ := by
  obtain ⟨C, hC⟩ := exists_enorm_setIntegral_schrodingerPropagator_sub_le (E := E) (r' := r₁')
    hq₁ hn₁ hpq₁ hqr₁
  refine ⟨C, fun {I} hI Φ ↦ (BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_⟩
  rw [Submodule.subtype_apply]
  obtain ⟨F, hF : IntegrableOn F I volume, hΦF⟩ :=
    Lp.mem_integrableRepSubmodule_iff.1 Φ.property
  have h := hC F ((measurableSet_Iio (a := t)).inter hI)
    (hF.mono_set inter_subset_right).aestronglyMeasurable
    (IntegrableOn.mono_set (integrable_phasePropagator_apply laplacianSymbol
      continuous_neg.aestronglyMeasurable hF) inter_subset_right) t
  rw [← Measure.restrict_restrict measurableSet_Iio, ← retardedOnLift_apply_of_ae_eq hF hΦF] at h
  have h₂ : eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁
      ((volume.restrict I).restrict (Iio t)) ≤
        ‖(Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I))‖ₑ :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans_eq
      (eLpNorm_eLpNorm_eq_eNorm_of_ae_eq hΦF)
  have h₃ : ‖retardedOnLift (p₁ : ℝ≥0∞) r₁' I Φ t‖ₑ ≤
      C * ‖(Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I))‖ₑ :=
    h.trans (by gcongr)
  simpa [ENNReal.toReal_mul] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top eNorm_ne_top) h₃

/-- **The retarded integral with forcing in a dual Strichartz space agrees with the Bochner
integral** on `L²`-valued forcings. Let `p₁` and `r₁'` be the Hölder conjugates of an admissible
pair `(q₁, r₁)` with a finite time exponent, `2 ≤ q₁ < ∞` and `2 / q₁ + n / r₁ = n / 2`, with
`n ≥ 3` when `q₁ = 2`. If `Φ ∈ L^{p₁}(I; L^{r₁'})` is represented on `I` by an `F : ℝ → L²(E)`
integrable on `I`, then for every `t`

`schrodingerRetardedL p₁ r₁' I Φ t = ∫_{s < t} S(t - s) (1_I F)(s) ds`. -/
theorem schrodingerRetardedL_apply_of_ae_eq (hq₁ : 2 ≤ q₁)
    (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2)
    (hI : MeasurableSet I) {Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I)}
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : IntegrableOn F I)
    (hΦF : ∀ᵐ s ∂volume.restrict I, (Φ s : E → ℂ) =ᵐ[volume] F s) (t : ℝ) :
    schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' I Φ t =
      ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (I.indicator F s) := by
  have hmem : Φ ∈ liftSubmodule E p₁ r₁' I := Lp.mem_integrableRepSubmodule_iff.2 ⟨F, hF, hΦF⟩
  obtain ⟨C, hC⟩ := exists_norm_retardedOnLift_le (r₁' := r₁') hq₁ hn₁ hpq₁ hqr₁
  have h := LinearMap.extendOfNorm_eq (f := retardedOnLift (p₁ : ℝ≥0∞) r₁' I)
    (e := (liftSubmodule E p₁ r₁' I).subtype)
    (denseRange_subtype_liftSubmodule ENNReal.coe_ne_top
      (ne_top_of_admissible (zero_lt_two.trans_le hq₁) hqr₁))
    ⟨C, hC hI⟩ ⟨Φ, hmem⟩
  -- `Φ` is the image of `⟨Φ, hmem⟩` under the inclusion of the submodule, by `Subtype.coe_mk`.
  rw [show Φ = (liftSubmodule E p₁ r₁' I).subtype ⟨Φ, hmem⟩ from rfl, schrodingerRetardedL, h,
    retardedOnLift_apply_of_ae_eq hF hΦF, setIntegral_Iio_restrict_eq_indicator hI]

/-- **`schrodingerRetardedL` is the completion of the retarded integral.** Under the hypotheses of
`TauCeti.schrodingerRetardedL_apply_of_ae_eq`, a continuous linear map on `L^{p₁}(I; L^{r₁'})` that
agrees with the retarded integral `t ↦ ∫_{s < t} S(t - s) (1_I F)(s) ds` on every forcing with an
integrable `L²`-valued representative `F` is `schrodingerRetardedL p₁ r₁' I`. -/
theorem eq_schrodingerRetardedL (hq₁ : 2 ≤ q₁)
    (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2)
    (hI : MeasurableSet I)
    (V : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I) →L[ℂ]
      ℝ →ᵇ Lp ℂ 2 (volume : Measure E))
    (hV : ∀ (Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I))
      (F : ℝ → Lp ℂ 2 (volume : Measure E)), IntegrableOn F I →
      (∀ᵐ s ∂volume.restrict I, (Φ s : E → ℂ) =ᵐ[volume] F s) → ∀ t,
        V Φ t = ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (I.indicator F s)) :
    V = schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' I := by
  obtain ⟨C, hC⟩ := exists_norm_retardedOnLift_le (r₁' := r₁') hq₁ hn₁ hpq₁ hqr₁
  refine (LinearMap.extendOfNorm_unique (f := retardedOnLift (p₁ : ℝ≥0∞) r₁' I)
    (e := (liftSubmodule E p₁ r₁' I).subtype)
    (denseRange_subtype_liftSubmodule ENNReal.coe_ne_top
      (ne_top_of_admissible (zero_lt_two.trans_le hq₁) hqr₁)) C
    (hC hI) V
    ?_).symm
  ext1 Φ
  obtain ⟨F, hF : IntegrableOn F I volume, hΦF⟩ :=
    Lp.mem_integrableRepSubmodule_iff.1 Φ.property
  ext1 t
  rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
    hV _ F hF hΦF, retardedOnLift_apply_of_ae_eq hF hΦF, setIntegral_Iio_restrict_eq_indicator hI]

/-- On a forcing with an integrable `L²`-valued representative, a weak retarded Strichartz
estimate with constant `C` bounds the pairing of `schrodingerRetardedL p₁ r₁' I Φ` with an
integrable `G : ℝ → L²` by `C ‖Φ‖ ‖G‖_{L^p_t L^{r'}_x}`. -/
private theorem enorm_integral_inner_schrodingerRetardedL_le (hq₁ : 2 ≤ q₁)
    (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2)
    (hI : MeasurableSet I) {p : ℝ≥0} {r' : ℝ≥0∞} {C : ℝ≥0}
    (hC : ∀ F G : ℝ → Lp ℂ 2 (volume : Measure E), AEStronglyMeasurable F →
      AEStronglyMeasurable G → Integrable (fun s ↦ schrodingerPropagator ℂ (-s) (F s)) →
      Integrable (fun t ↦ schrodingerPropagator ℂ (-t) (G t)) →
      ‖∫ t, ∫ s in Iio t, ⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ‖ₑ ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume *
          eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume)
    {Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I)}
    (hΦ : Φ ∈ liftSubmodule E p₁ r₁' I) {G : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hG : Integrable G) :
    ‖∫ t, ⟪schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' I Φ t, G t⟫_ℂ‖ₑ ≤
      C * ‖Φ‖ₑ * eLpNorm (fun t ↦ eLpNorm (G t) r' volume) p volume := by
  obtain ⟨F, hF : IntegrableOn F I volume, hΦF⟩ := Lp.mem_integrableRepSubmodule_iff.1 hΦ
  have hFI : Integrable (I.indicator F) := hF.integrable_indicator hI
  have hW (t : ℝ) : ⟪schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' I Φ t, G t⟫_ℂ =
      ∫ s in Iio t, ⟪schrodingerPropagator ℂ (t - s) (I.indicator F s), G t⟫_ℂ := by
    rw [schrodingerRetardedL_apply_of_ae_eq hq₁ hn₁ hpq₁ hqr₁ hI hF hΦF,
      inner_setIntegral_Iio_phasePropagator_sub laplacianSymbol hFI]
  have hnorm : eLpNorm (fun s ↦ eLpNorm (I.indicator F s : Lp ℂ 2 (volume : Measure E)) r₁'
      volume) p₁ volume = ‖Φ‖ₑ := by
    rw [← eLpNorm_eLpNorm_eq_eNorm_of_ae_eq hΦF]
    exact eLpNorm_eLpNorm_apply_indicator (T := id) rfl hI.nullMeasurableSet F
  simp_rw [hW]
  rw [← hnorm]
  exact hC _ G hFI.aestronglyMeasurable hG.aestronglyMeasurable
    (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hFI)
    (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hG)

/-- **The retarded Strichartz estimate with forcing in a dual Strichartz space**, in every
dimension `n`, for any two admissible pairs with finite time exponents: `2 ≤ q, q₁ < ∞` with
`2 / q + n / r = n / 2` and `2 / q₁ + n / r₁ = n / 2`, and `n ≥ 3` when `q = 2` or `q₁ = 2`, where
`p₁` and `r₁'` are the Hölder conjugates of `q₁` and `r₁`. There is `C` such that for every
measurable set of times `I` and every forcing `Φ ∈ L^{p₁}(I; L^{r₁'})`,

`‖schrodingerRetardedL p₁ r₁' I Φ‖_{L^q_t L^r_x} ≤ C ‖Φ‖_{L^{p₁}(I; L^{r₁'})}`.

The constant does not depend on `I`. For `Φ` with an integrable `L²`-valued representative this is
`TauCeti.exists_eLpNorm_eLpNorm_setIntegral_Iio_schrodingerPropagator_sub_le`; the bound extends
to all of `L^{p₁}(I; L^{r₁'})` by density, tested against bounded `L²`-valued functions of time. -/
theorem exists_eLpNorm_eLpNorm_schrodingerRetardedL_le {p q : ℝ≥0} {r : ℝ≥0∞} (hq : 2 ≤ q)
    (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hq₁ : 2 ≤ q₁) (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ {I : Set ℝ}, MeasurableSet I →
      ∀ Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I),
        eLpNorm (fun t ↦ eLpNorm (schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' I Φ t) r volume) q volume ≤
          C * ‖Φ‖ₑ := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun _ _ ↦ by simp [eLpNorm_exponent_zero (Lp.aestronglyMeasurable _)]⟩
  have hr2 := two_le_of_admissible (zero_lt_two.trans_le hq) hr0 hqr
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  have := hpq.symm.coe_ennreal
  obtain ⟨C, hC⟩ :=
    exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_of_integrable
      (r' := (1 - r⁻¹)⁻¹) (r₁' := r₁') hq hn hpq hqr hq₁ hn₁ hpq₁ hqr₁
  refine ⟨C + 1, fun {I} hI Φ ↦ ?_⟩
  set W := schrodingerRetardedL (E := E) (p₁ : ℝ≥0∞) r₁' I
  refine AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_bounded_le
    (W Φ).continuous.aestronglyMeasurable
    (𝕜 := ℂ) (p' := p) (q' := (1 - r⁻¹)⁻¹) fun G A hA hGA hG ↦ ?_
  have hGi : Integrable G := memLp_one_iff_integrable.1
    (hG.mono_exponent_of_measure_support_ne_top hGA hA le_top)
  set M := eLpNorm (fun t ↦ eLpNorm (G t) (1 - r⁻¹)⁻¹ volume) p volume
  rcases eq_or_ne M ∞ with hM | hM
  · rcases eq_or_ne Φ 0 with rfl | hΦ
    · simp
    · rw [hM, ENNReal.mul_top (mul_ne_zero (by simp) (eNorm_ne_zero.2 hΦ))]
      exact le_top
  -- The pairing with `G` is continuous in the forcing.
  have hcont : Continuous fun Φ ↦ ‖(memLp_one_iff_integrable.2 hGi).innerLpCLM ℂ (q' := ∞)
      (BoundedContinuousFunction.toLpTop volume ℂ (W Φ))‖ₑ := by
    fun_prop
  -- The bound holds on the dense subspace of forcings with an `L²`-valued representative, and
  -- both sides are continuous in the forcing.
  refine (Lp.dense_integrableRepSubmodule (𝕜 := ℂ) (μ := (volume : Measure E))
    (ρ := volume.restrict I) (s := 2) ENNReal.coe_ne_top
    (ne_top_of_admissible (zero_lt_two.trans_le hq₁) hqr₁)).induction
    (P := fun Φ ↦ ‖∫ t, ⟪W Φ t, G t⟫_ℂ‖ₑ ≤ (C + 1) * ‖Φ‖ₑ * M) (fun Φ hΦ ↦ ?_)
    (isClosed_le (hcont.congr fun Φ ↦ by
        rw [MemLp.innerLpCLM_apply, enorm_integral_inner_comm]
        exact congrArg _ (integral_congr_ae (by
          filter_upwards [BoundedContinuousFunction.coeFn_toLpTop (𝕜 := ℂ) volume (W Φ)] with t ht
          rw [ht])))
      ((ENNReal.continuous_mul_const hM).comp
        ((ENNReal.continuous_const_mul (by simp)).comp continuous_eNorm))) Φ
  exact (enorm_integral_inner_schrodingerRetardedL_le hq₁ hn₁ hpq₁ hqr₁ hI hC hΦ hGi).trans
    (by gcongr; exact le_self_add)

/-- **The energy bound with forcing in a dual Strichartz space.** Under the hypotheses of
`TauCeti.schrodingerRetardedL_apply_of_ae_eq`, there is `C` such that for every measurable set of
times `I` and every `Φ ∈ L^{p₁}(I; L^{r₁'})`,

`sup_t ‖schrodingerRetardedL p₁ r₁' I Φ t‖₂ ≤ C ‖Φ‖_{L^{p₁}(I; L^{r₁'})}`.

The constant does not depend on `I`. -/
theorem exists_norm_schrodingerRetardedL_le (hq₁ : 2 ≤ q₁)
    (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ {I : Set ℝ}, MeasurableSet I →
      ∀ Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I),
        ‖schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' I Φ‖ ≤ C * ‖Φ‖ := by
  obtain ⟨C, hC⟩ := exists_norm_retardedOnLift_le (r₁' := r₁') hq₁ hn₁ hpq₁ hqr₁
  refine ⟨C, fun {I} hI Φ ↦ ?_⟩
  rw [schrodingerRetardedL]
  exact LinearMap.norm_extendOfNorm_apply_le (f := retardedOnLift (p₁ : ℝ≥0∞) r₁' I)
    (e := (liftSubmodule E p₁ r₁' I).subtype)
    (denseRange_subtype_liftSubmodule ENNReal.coe_ne_top
      (ne_top_of_admissible (zero_lt_two.trans_le hq₁) hqr₁)) C
    (hC hI) Φ

/-- **Duhamel's formula through the retarded integral on the dual Strichartz space.** Under the
hypotheses of `TauCeti.schrodingerRetardedL_apply_of_ae_eq`, if `Φ ∈ L^{p₁}((0, T]; L^{r₁'})` is
represented on `(0, T]` by an `F : ℝ → L²(E)` integrable there, then for every `t ≥ 0` the mild
solution `u = TauCeti.schrodingerDuhamel f ((Ioc 0 T).indicator F)` of `i ∂ₜu + Δu = F` on `(0, T]`,
`i ∂ₜu + Δu = 0` after `T`, `u(0) = f`, is

`u(t) = S(t) f - i schrodingerRetardedL p₁ r₁' (0, T] Φ t`.

So `t ↦ S(t) f - i schrodingerRetardedL p₁ r₁' (0, T] Φ t`, which is defined and continuous with
values in `L²` for every `Φ ∈ L^{p₁}((0, T]; L^{r₁'})`, extends Duhamel's formula to forcings in
the dual Strichartz space. -/
theorem schrodingerDuhamel_eq_sub_smul_schrodingerRetardedL (hq₁ : 2 ≤ q₁)
    (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) {T : ℝ}
    {Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict (Ioc 0 T))}
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : IntegrableOn F (Ioc 0 T))
    (hΦF : ∀ᵐ s ∂volume.restrict (Ioc 0 T), (Φ s : E → ℂ) =ᵐ[volume] F s)
    (f : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    schrodingerDuhamel f ((Ioc 0 T).indicator F) t = schrodingerPropagator ℂ t f -
      Complex.I • schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ t := by
  rw [schrodingerDuhamel_eq_sub_setIntegral_Iio f _ (T := max t T) ⟨ht, le_max_left t T⟩,
    schrodingerRetardedL_apply_of_ae_eq hq₁ hn₁ hpq₁ hqr₁ measurableSet_Ioc hF hΦF,
    indicator_indicator, inter_eq_right.2 (Ioc_subset_Ioc_right (le_max_right t T))]

/-- **The Strichartz estimate for the inhomogeneous Schrödinger equation with forcing in a dual
Strichartz space**, in every dimension `n`, for any two admissible pairs with finite time
exponents: `2 ≤ q, q₁ < ∞` with `2 / q + n / r = n / 2` and `2 / q₁ + n / r₁ = n / 2`, and `n ≥ 3`
when `q = 2` or `q₁ = 2`, where `p₁` and `r₁'` are the Hölder conjugates of `q₁` and `r₁`. There is
`C` such that for every `T`, every `f ∈ L²(E)` and every `Φ ∈ L^{p₁}((0, T]; L^{r₁'})`, the solution
`u(t) = S(t) f - i schrodingerRetardedL p₁ r₁' (0, T] Φ t` satisfies

`‖u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖₂ + ‖Φ‖_{L^{p₁}((0, T]; L^{r₁'})})`.

The constant does not depend on `T`. For forcings with an integrable `L²`-valued representative
`u` is Duhamel's formula (`TauCeti.schrodingerDuhamel_eq_sub_smul_schrodingerRetardedL`) and this
is `TauCeti.exists_eLpNorm_eLpNorm_schrodingerDuhamel_le`. -/
theorem exists_eLpNorm_eLpNorm_schrodingerPropagator_sub_smul_schrodingerRetardedL_le
    {p q : ℝ≥0} {r : ℝ≥0∞} (hq : 2 ≤ q) (hn : q = 2 → 2 < Module.finrank ℝ E)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hq₁ : 2 ≤ q₁) (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (f : Lp ℂ 2 (volume : Measure E)) (T : ℝ)
      (Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict (Ioc 0 T))),
      eLpNorm (fun t ↦ eLpNorm ((schrodingerPropagator ℂ t f -
          Complex.I • schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ t :
            Lp ℂ 2 (volume : Measure E)) : E → ℂ) r volume) q
          (volume.restrict (Icc 0 T)) ≤ C * (‖f‖ₑ + ‖Φ‖ₑ) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · have h0 (g : Lp ℂ 2 (volume : Measure E)) : eLpNorm g 0 volume = 0 :=
      eLpNorm_exponent_zero (Lp.aestronglyMeasurable g)
    exact ⟨0, fun _ _ _ ↦ by simp only [h0]; simp⟩
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_eLpNorm_schrodingerPropagator_le hq hn hpq hqr
  obtain ⟨C₂, hC₂⟩ := exists_eLpNorm_eLpNorm_schrodingerRetardedL_le (r₁' := r₁') hq hn hpq hqr
    hq₁ hn₁ hpq₁ hqr₁
  refine ⟨C₁ + C₂, fun f T Φ ↦ ?_⟩
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast one_le_two.trans hq
  have hr2 := two_le_of_admissible (zero_lt_two.trans_le hq) hr0 hqr
  set W := schrodingerRetardedL (E := E) (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ
  -- The `Lʳ` norm of `u(t)` is at most that of `S(t) f` plus that of `W(t)`.
  have hle (t : ℝ) : eLpNorm ((schrodingerPropagator ℂ t f - Complex.I • W t :
      Lp ℂ 2 (volume : Measure E)) : E → ℂ) r volume ≤
      eLpNorm (schrodingerPropagator ℂ t f) r volume + eLpNorm (W t) r volume := by
    rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    refine (eLpNorm_sub_le (one_le_two.trans hr2)).trans_eq ?_
    rw [eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, ← ofReal_norm, Complex.norm_I,
      ENNReal.ofReal_one, one_mul]
  calc _ ≤ eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume +
          eLpNorm (W t) r volume) q (volume.restrict (Icc 0 T)) :=
        eLpNorm_mono_eNorm (AEStronglyMeasurable.aemeasurable_eLpNorm_Lp
          ((continuous_phasePropagator_apply laplacianSymbol f).sub
            (W.continuous.const_smul Complex.I)).aestronglyMeasurable .rfl r).aestronglyMeasurable
          fun t ↦ by simpa using hle t
    _ ≤ eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume) q volume +
          eLpNorm (fun t ↦ eLpNorm (W t) r volume) q volume :=
        (eLpNorm_add_le hq1).trans (add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (eLpNorm_mono_measure _ Measure.restrict_le_self))
    _ ≤ C₁ * ‖f‖ₑ + C₂ * ‖Φ‖ₑ := add_le_add (hC₁ f) (hC₂ measurableSet_Ioc Φ)
    _ ≤ _ := by
        rw [ENNReal.coe_add, add_mul, mul_add, mul_add]
        gcongr
        · exact le_self_add
        · exact le_add_self

/-! ### The weak formulation and uniqueness -/

/-- The time integral over `(0, t]` of the pairing of `Δφ` with the solution, split into the free
part and the retarded part. -/
private theorem setIntegral_inner_sub_smul_eq (W : ℝ →ᵇ Lp ℂ 2 (volume : Measure E))
    (f χ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ∫ s in Ioc 0 t, ⟪χ, schrodingerPropagator ℂ s f - Complex.I • W s⟫_ℂ =
      ⟪χ, ∫ s in Ioc 0 t, schrodingerPropagator ℂ s f⟫_ℂ -
        Complex.I * ⟪χ, ∫ s in Ioc 0 t, W s⟫_ℂ := by
  have hS : IntegrableOn (fun s ↦ schrodingerPropagator ℂ s f) (Ioc 0 t) :=
    (continuous_phasePropagator_apply laplacianSymbol f).integrableOn_Ioc
  have hW : IntegrableOn (fun s ↦ Complex.I • W s) (Ioc 0 t) :=
    W.continuous.integrableOn_Ioc.smul Complex.I
  have hSW : IntegrableOn (fun s ↦ schrodingerPropagator ℂ s f - Complex.I • W s) (Ioc 0 t) :=
    hS.sub hW
  rw [integral_inner hSW, integral_sub hS hW, integral_smul, inner_sub_right, inner_smul_right]

/-- The time integral over `(0, t]` of the pairing of `χ` with `S(s) f - i h(s)` depends
continuously on the bounded continuous function of time `h`. -/
private theorem continuous_setIntegral_inner_sub_smul (f χ : Lp ℂ 2 (volume : Measure E))
    (t : ℝ) :
    Continuous fun h : ℝ →ᵇ Lp ℂ 2 (volume : Measure E) ↦
      ∫ s in Ioc 0 t, ⟪χ, schrodingerPropagator ℂ s f - Complex.I • h s⟫_ℂ := by
  have hint : Continuous fun h : ℝ →ᵇ Lp ℂ 2 (volume : Measure E) ↦ ∫ s in Ioc 0 t, h s :=
    (continuous_integral.comp
      (BoundedContinuousFunction.toLp (E := Lp ℂ 2 (volume : Measure E)) 1
        (volume.restrict (Ioc 0 t)) ℂ).continuous).congr fun h ↦
      integral_congr_ae (BoundedContinuousFunction.coeFn_toLp _ _ _ h)
  simp_rw [setIntegral_inner_sub_smul_eq]
  exact continuous_const.sub (continuous_const.mul (continuous_const.inner hint))

/-- The forcing term `∫_{(0,t] ∩ I} ∫ ⟪φ(x), Φ(s)(x)⟫ dx ds` of the weak formulation is continuous
in `Φ ∈ L^{p₁}(I; L^{r₁'})`: it is the pairing of `s ↦ ∫ ⟪φ, Φ(s)⟫ ∈ L^{p₁}(I)` with the indicator
of `(0, t]`. -/
private theorem continuous_setIntegral_integral_inner {r : ℝ≥0∞} [r.HolderConjugate r₁']
    (hpq₁ : p₁.HolderConjugate q₁) (I : Set ℝ) (φ : 𝓢(E, ℂ)) (t : ℝ) :
    Continuous fun Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict I) ↦
      ∫ s in Ioc 0 t, (∫ x, ⟪φ x, (Φ s : E → ℂ) x⟫_ℂ) ∂volume.restrict I := by
  have : Fact (1 ≤ (q₁ : ℝ≥0∞)) := ⟨by exact_mod_cast hpq₁.symm.lt.le⟩
  have := hpq₁.coe_ennreal
  set L := (φ.memLp r).innerLpCLM ℂ (q' := r₁')
  refine (((Lp.toDual ℂ (volume.restrict I) p₁ q₁).continuous.comp
    (L.compLpL p₁ (volume.restrict I)).continuous).clm_apply
      (continuous_const (y := indicatorConstLp q₁ (measurableSet_Ioc (a := 0) (b := t))
        ((Measure.restrict_apply_le I _).trans_lt measure_Ioc_lt_top).ne (1 : ℂ)))).congr
    fun Φ ↦ ?_
  rw [Function.comp_apply, Lp.toDual_indicatorConstLp, mul_one]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := p₁) (μ := volume.restrict I) L Φ]
    with s hs
  rw [hs, MemLp.innerLpCLM_apply]

/-- **The solution with forcing in a dual Strichartz space is a weak solution.** Let `p₁` and `r₁'`
be the Hölder conjugates of an admissible pair `(q₁, r₁)` with a finite time exponent,
`2 ≤ q₁ < ∞` and `2 / q₁ + n / r₁ = n / 2`, with `n ≥ 3` when `q₁ = 2`. Let `f ∈ L²(E)`, let
`Φ ∈ L^{p₁}((0, T]; L^{r₁'})` and let `u(t) = S(t) f - i schrodingerRetardedL p₁ r₁' (0, T] Φ t`.
Then `u` solves `i ∂ₜu + Δu = Φ`, `u(0) = f`, in the sense of distributions in space: for every
Schwartz function `φ` and every `t ≥ 0`,

`⟪φ, u t⟫ = ⟪φ, f⟫ + i (∫_{(0,t]} ⟪Δφ, u s⟫ ds - ∫_{(0,t] ∩ (0,T]} ∫ ⟪φ(x), Φ(s)(x)⟫ dx ds)`.

The forcing need not take values in `L²`: `Φ(s)` is paired with `φ ∈ L^{r₁}`. For forcings with an
integrable `L²`-valued representative this is `TauCeti.inner_toLp_schrodingerDuhamel`. -/
theorem inner_toLp_schrodingerPropagator_sub_smul_schrodingerRetardedL (hq₁ : 2 ≤ q₁)
    (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) {T : ℝ}
    (f : Lp ℂ 2 (volume : Measure E))
    (Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict (Ioc 0 T))) (φ : 𝓢(E, ℂ))
    {t : ℝ} (ht : 0 ≤ t) :
    ⟪φ.toLp 2, schrodingerPropagator ℂ t f -
        Complex.I • schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ t⟫_ℂ =
      ⟪φ.toLp 2, f⟫_ℂ + Complex.I * ((∫ s in Ioc 0 t, ⟪(Δ φ).toLp 2, schrodingerPropagator ℂ s f -
          Complex.I • schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ s⟫_ℂ) -
        ∫ s in Ioc 0 t, (∫ x, ⟪φ x, (Φ s : E → ℂ) x⟫_ℂ) ∂volume.restrict (Ioc 0 T)) := by
  have : r₁.HolderConjugate r₁' := (inferInstance : r₁'.HolderConjugate r₁).symm
  -- Both sides are continuous in `Φ`, so it suffices to treat forcings with an integrable
  -- `L²`-valued representative, for which `u` is Duhamel's formula.
  refine (denseRange_subtype_liftSubmodule ENNReal.coe_ne_top
    (ne_top_of_admissible (zero_lt_two.trans_le hq₁) hqr₁)).induction_on Φ
    (isClosed_eq (by fun_prop) (continuous_const.add (continuous_const.mul
      (((continuous_setIntegral_inner_sub_smul f _ t).comp
        (schrodingerRetardedL (E := E) (p₁ : ℝ≥0∞) r₁' (Ioc 0 T)).continuous).sub
        (continuous_setIntegral_integral_inner (r := r₁) hpq₁ _ φ t)))))
    fun Ψ ↦ ?_
  rw [Submodule.subtype_apply]
  obtain ⟨F, hF : IntegrableOn F (Ioc 0 T) volume, hΨF⟩ :=
    Lp.mem_integrableRepSubmodule_iff.1 Ψ.property
  have hu (s : ℝ) (hs : 0 ≤ s) :=
    (schrodingerDuhamel_eq_sub_smul_schrodingerRetardedL hq₁ hn₁ hpq₁ hqr₁ hF hΨF f hs).symm
  rw [hu t ht, inner_toLp_schrodingerDuhamel
    ((hF.integrable_indicator measurableSet_Ioc).locallyIntegrable.locallyIntegrableOn _) φ ht]
  congr 3
  · exact setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ by rw [hu s hs.1.le]
  · -- The forcing pairings agree for almost every time in `(0, t] ∩ (0, T]`.
    have hind (s : ℝ) : ⟪φ.toLp 2, (Ioc 0 T).indicator F s⟫_ℂ =
        (Ioc 0 T).indicator (fun s ↦ ⟪φ.toLp 2, F s⟫_ℂ) s := by
      by_cases hs : s ∈ Ioc 0 T <;> simp [hs]
    simp_rw [hind]
    rw [setIntegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right hΨF] with s hs
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2, hs] with x h₁ h₂
    rw [h₁, h₂]

/-- **Uniqueness for the Schrödinger equation with forcing in a dual Strichartz space.** Under the
hypotheses of `TauCeti.inner_toLp_schrodingerPropagator_sub_smul_schrodingerRetardedL`, let `v`
be continuous on `[0, T₀]` with values in `L²(E)`. If `v` solves
`i ∂ₜv + Δv = Φ`, `v(0) = f`, in the sense of distributions in space on `[0, T₀]`: for every
Schwartz function `φ` and every `t ∈ [0, T₀]`,

`⟪φ, v t⟫ = ⟪φ, f⟫ + i (∫_{(0,t]} ⟪Δφ, v s⟫ ds - ∫_{(0,t] ∩ (0,T]} ∫ ⟪φ(x), Φ(s)(x)⟫ dx ds)`,

then `v(t) = S(t) f - i schrodingerRetardedL p₁ r₁' (0, T] Φ t` on `[0, T₀]`. So the Cauchy problem
is uniquely solvable in `C([0, T₀]; L²)`, and its solution satisfies the Strichartz estimates of
`TauCeti.exists_eLpNorm_eLpNorm_schrodingerPropagator_sub_smul_schrodingerRetardedL_le`. -/
theorem eqOn_schrodingerPropagator_sub_smul_schrodingerRetardedL_of_forall_inner_toLp_eq
    (hq₁ : 2 ≤ q₁) (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) {T T₀ : ℝ}
    (f : Lp ℂ 2 (volume : Measure E))
    (Φ : Lp (Lp ℂ r₁' (volume : Measure E)) p₁ (volume.restrict (Ioc 0 T)))
    {v : ℝ → Lp ℂ 2 (volume : Measure E)} (hv : ContinuousOn v (Icc 0 T₀))
    (h : ∀ φ : 𝓢(E, ℂ), ∀ t ∈ Icc 0 T₀, ⟪φ.toLp 2, v t⟫_ℂ = ⟪φ.toLp 2, f⟫_ℂ +
      Complex.I * ((∫ s in Ioc 0 t, ⟪(Δ φ).toLp 2, v s⟫_ℂ) -
        ∫ s in Ioc 0 t, (∫ x, ⟪φ x, (Φ s : E → ℂ) x⟫_ℂ) ∂volume.restrict (Ioc 0 T))) :
    EqOn v (fun t ↦ schrodingerPropagator ℂ t f -
      Complex.I • schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ t) (Icc 0 T₀) := by
  set u : ℝ → Lp ℂ 2 (volume : Measure E) := fun t ↦ schrodingerPropagator ℂ t f -
    Complex.I • schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ t
  have hu : Continuous u := (continuous_phasePropagator_apply laplacianSymbol f).sub
    ((schrodingerRetardedL (p₁ : ℝ≥0∞) r₁' (Ioc 0 T) Φ).continuous.const_smul Complex.I)
  -- The difference `v - u` is a weak solution of the free equation with zero initial value.
  have h0 := eqOn_zero_of_forall_inner_toLp_eq_I_mul_setIntegral_inner_toLp_laplacian
      (hv.sub hu.continuousOn) fun φ t ht ↦ by
    have hint (g : ℝ → Lp ℂ 2 (volume : Measure E)) (hg : ContinuousOn g (Icc 0 T₀)) :
        IntegrableOn (fun s ↦ ⟪(Δ φ).toLp 2, g s⟫_ℂ) (Ioc 0 t) :=
      ((continuous_const.inner continuous_id).comp_continuousOn
        (hg.mono (Icc_subset_Icc_right ht.2))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    simp only [Pi.sub_apply, inner_sub_right]
    rw [integral_sub (hint v hv) (hint u hu.continuousOn), h φ t ht,
      inner_toLp_schrodingerPropagator_sub_smul_schrodingerRetardedL hq₁ hn₁ hpq₁ hqr₁ f Φ φ ht.1]
    ring
  exact fun t ht ↦ sub_eq_zero.1 (h0 ht)

end Estimates

end Lift

end TauCeti
