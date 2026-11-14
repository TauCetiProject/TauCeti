/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The `W^{k,p}` and `H^{k,p}` norms are equivalent on the whole space

For `1 < p < ∞` and a natural number `k`, Calderón's theorem
(`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`) says that a real `Lᵖ` function on
a finite-dimensional real inner product space `E` is the value of an element of the
weak-derivative Sobolev space `W^{k,p}(E)` exactly when its complexification lies in Mathlib's
Bessel-potential space `H^{k,p}(E)`. This file upgrades that identification of sets to an
identification of Banach spaces: the map

`TauCeti.Wkp.toBesselPotentialSpace : W^{k,p}(E) →L[ℝ] H^{k,p}(E, ℂ)`,

sending `u` to its complexified value, is a real-linear isomorphism onto the closed subspace of
the elements of `H^{k,p}(E, ℂ)` represented by real functions, so that the two norms are
equivalent: `‖u‖_{W^{k,p}} ≤ C ‖u‖_{H^{k,p}} ≤ C' ‖u‖_{W^{k,p}}` with `C, C'` depending only on `E`,
`k` and `p`.

The identification commutes with derivatives: the value of `d ∈ W^{j,q}(E)` is a weak directional
derivative of the value of `u ∈ W^{k,p}(E)` exactly when the tempered distribution of `d` is the
corresponding derivative of the tempered distribution of `u`.

## The argument

Both spaces are complete, and both embed continuously into the tempered distributions, the
Sobolev space through its value in `Lᵖ` and the Bessel-potential space through its tempered
distribution (`BesselPotentialSpace.continuous_toDistr`). The map agrees with these embeddings, so
its graph is closed and the closed graph theorem makes it continuous
(`BesselPotentialSpace.continuous_of_continuous_toDistr`).
It is injective, since an `Lᵖ` function is determined by its tempered distribution. Its range is
closed: by Calderón's theorem it is the preimage, under the continuous inclusion
`H^{k,p} ⊆ H^{0,p} = Lᵖ` (`BesselPotentialSpace.inclusionLp`), of the complexified real functions,
which are closed in `Lᵖ(E, ℂ)` since taking real parts is a continuous retraction onto them. The
open mapping theorem then bounds the inverse on the range
(`ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`).

No explicit value of the constants is claimed. The statements are for Lebesgue measure `volume`,
the measure of Mathlib's Bessel-potential spaces.

## Main declarations

* `TauCeti.Wkp.toBesselPotentialSpace`: the identification `W^{k,p}(E) →L[ℝ] H^{k,p}(E, ℂ)`.
* `TauCeti.Wkp.toDistr_toBesselPotentialSpace_apply`,
  `TauCeti.Wkp.toDistr_toBesselPotentialSpace_of_ae_eq`: its tempered distribution is the
  complexified value.
* `TauCeti.Wkp.toBesselPotentialSpace_injective`: it is injective.
* `TauCeti.Wkp.toBesselPotentialSpace_eq_iff`: it is characterised by its image in `Lᵖ`.
* `TauCeti.Wkp.inclusion_toBesselPotentialSpace`: it is compatible with lowering the order.
* `TauCeti.Wkp.exists_toBesselPotentialSpace_eq_iff`: its range consists of the elements of
  `H^{k,p}(E, ℂ)` given by real `Lᵖ` functions.
* `TauCeti.Wkp.inclusionLp_toBesselPotentialSpace_of_ae_eq`,
  `TauCeti.Wkp.coeFn_inclusionLp_toBesselPotentialSpace`: through the inclusion `H^{k,p} ⊆ Lᵖ` it
  is the complexified value.
* `TauCeti.Wkp.isClosed_range_toBesselPotentialSpace`: the range is closed.
* `TauCeti.Wkp.exists_norm_le_mul_norm_toBesselPotentialSpace`: the reverse bound
  `‖u‖_{W^{k,p}} ≤ C ‖u‖_{H^{k,p}}`, so that the two norms are equivalent.
* `TauCeti.Wkp.hasWeakLineDerivOn_iff_lineDerivOp_toDistr_toBesselPotentialSpace`,
  `TauCeti.Wkp.lineDerivOp_toDistr_toBesselPotentialSpace_of_hasWeakLineDerivOn`: the
  identification commutes with directional derivatives.

## References

* A.-P. Calderón, *Lebesgue spaces of differentiable functions and distributions*, Proc. Sympos.
  Pure Math. **4** (1961), 33–49.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3,
  Theorem 3.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution TopologicalSpace Filter Topology
open scoped ENNReal LineDeriv SchwartzMap BesselPotentialSpace

namespace TauCeti.Wkp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The value of a Sobolev function on the whole space, as a real `Lᵖ` function for `volume`. -/
private def realValue (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    Lp ℝ p (volume : Measure E) :=
  castLpₗᵢ (𝕜 := ℝ) (Measure.restrict_coe_opens_top volume) (value k u)

private theorem value_ae_eq_realValue (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    (value k u : E → ℝ) =ᵐ[volume] realValue k u :=
  .of_forall fun x ↦ (coeFn_castLpₗᵢ _ (value k u) x).symm

/-- The value of a Sobolev function on the whole space, as a complex `Lᵖ` function for `volume`. -/
private def complexValue (k : ℕ) :
    Wkp (volume : Measure E) ⊤ p k →L[ℝ] Lp ℂ p (volume : Measure E) :=
  (Complex.ofRealCLM.compLpL p volume).comp
    ((castLpₗᵢ (𝕜 := ℝ) (Measure.restrict_coe_opens_top volume)).toContinuousLinearEquiv
      |>.toContinuousLinearMap.comp (valueL k))

private theorem complexValue_apply (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    complexValue k u = Complex.ofRealCLM.compLp (realValue k u) := by
  simp only [complexValue, realValue, ContinuousLinearMap.comp_apply, valueL_apply,
    ContinuousLinearMap.compLpL_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The tempered distribution of the complexified value of a Sobolev function. -/
private def toDistrValue (k : ℕ) : Wkp (volume : Measure E) ⊤ p k →L[ℝ] 𝓢'(E, ℂ) :=
  ((Lp.toTemperedDistributionCLM ℂ volume p).restrictScalars ℝ).comp (complexValue k)

private theorem toDistrValue_apply (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    toDistrValue k u = complexValue k u :=
  rfl

/-- The complexified value of `u` agrees almost everywhere with the value of `u`. -/
private theorem complexValue_ae_eq (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    complexValue k u =ᵐ[volume] fun x ↦ (value k u x : ℂ) := by
  rw [complexValue_apply]
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) (realValue k u),
    value_ae_eq_realValue k u] with x hx hu
  rw [hx, Complex.ofRealCLM_apply, hu]

variable (hp : 1 < p) (hp_top : p ≠ ∞)
include hp hp_top

/-- By Calderón's theorem, the complexified value of a `W^{k,p}` function lies in `H^{k,p}`. -/
private theorem memSobolev_complexValue (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    MemSobolev k p (complexValue k u : 𝓢'(E, ℂ)) := by
  rw [complexValue_apply]
  exact (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k _).2
    ⟨u, value_ae_eq_realValue k u⟩

/-- **The identification `W^{k,p}(E) = H^{k,p}(E)`.** For `1 < p < ∞`, the map sending a real
`W^{k,p}` function on the whole space to its complexification, as an element of Mathlib's
Bessel-potential space `H^{k,p}(E, ℂ)`. It is continuous, injective with closed range, and
bounded below (`TauCeti.Wkp.exists_norm_le_mul_norm_toBesselPotentialSpace`), so the `W^{k,p}`
and `H^{k,p}` norms are equivalent. -/
def toBesselPotentialSpace (k : ℕ) : Wkp (volume : Measure E) ⊤ p k →L[ℝ] H^{k, p}(E, ℂ) :=
  let L : Wkp (volume : Measure E) ⊤ p k →ₗ[ℝ] H^{k, p}(E, ℂ) :=
    { toFun u := (memSobolev_complexValue hp hp_top k u).toBesselPotentialSpace
      map_add' u v := BesselPotentialSpace.ext <| by
        simpa only [BesselPotentialSpace.toDistr_add, MemSobolev.toBesselPotentialSpace_toDistr,
          toDistrValue_apply] using map_add (toDistrValue k) u v
      map_smul' c u := BesselPotentialSpace.ext <| by
        simpa only [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ) c,
          BesselPotentialSpace.toDistr_smul, MemSobolev.toBesselPotentialSpace_toDistr,
          toDistrValue_apply] using map_smul (toDistrValue k) c u }
  { L with
    cont := BesselPotentialSpace.continuous_of_continuous_toDistr
      (X := Wkp (volume : Measure E) ⊤ p k) L <|
      (toDistrValue (E := E) (p := p) k).continuous.congr fun u ↦ by
        rw [toDistrValue_apply]
        exact (MemSobolev.toBesselPotentialSpace_toDistr _).symm }

private theorem toDistr_toBesselPotentialSpace (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    (toBesselPotentialSpace hp hp_top k u).toDistr = complexValue k u :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- The tempered distribution of `toBesselPotentialSpace u` pairs a Schwartz function `φ` with
`u` by integration: it is `φ ↦ ∫ φ u`. -/
@[simp]
theorem toDistr_toBesselPotentialSpace_apply (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k)
    (φ : 𝓢(E, ℂ)) :
    (toBesselPotentialSpace hp hp_top k u).toDistr φ = ∫ x, φ x * (value k u x : ℂ) := by
  rw [toDistr_toBesselPotentialSpace, Lp.toTemperedDistribution_apply]
  exact integral_congr_ae ((complexValue_ae_eq k u).mono fun x hx ↦ by simp [hx])

/-- The tempered distribution of `toBesselPotentialSpace u` is the complexification of any real
`L^q` function agreeing almost everywhere with the value of `u`, for any exponent `1 ≤ q ≤ ∞`. -/
theorem toDistr_toBesselPotentialSpace_of_ae_eq {k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {q : ℝ≥0∞} [Fact (1 ≤ q)] {g : Lp ℝ q (volume : Measure E)}
    (hg : (value k u : E → ℝ) =ᵐ[volume] g) :
    (toBesselPotentialSpace hp hp_top k u).toDistr =
      Lp.toTemperedDistribution (Complex.ofRealCLM.compLp g) := by
  ext φ
  rw [toDistr_toBesselPotentialSpace_apply, Lp.toTemperedDistribution_ofRealCLM_compLp_apply]
  exact integral_congr_ae (hg.mono fun x hx ↦ by simp [hx])

/-- The identification `W^{k,p}(E) → H^{k,p}(E, ℂ)` is injective. -/
theorem toBesselPotentialSpace_injective (k : ℕ) :
    Function.Injective (toBesselPotentialSpace (E := E) hp hp_top k) := by
  intro u v huv
  have h := congrArg BesselPotentialSpace.toDistr huv
  rw [toDistr_toBesselPotentialSpace, toDistr_toBesselPotentialSpace] at h
  have hc : complexValue k u = complexValue k v :=
    LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot h
  refine ext k (Lp.ext ?_)
  filter_upwards [ae_restrict_of_ae (complexValue_ae_eq k u),
    ae_restrict_of_ae (complexValue_ae_eq k v), ae_restrict_of_ae (Lp.ext_iff.1 hc)]
    with x hu hv hx
  exact_mod_cast hu.symm.trans (hx.trans hv)

/-- **The range of the identification.** An element of `H^{k,p}(E, ℂ)` comes from `W^{k,p}(E)`
exactly when its tempered distribution is the complexification of a real `Lᵖ` function. -/
theorem exists_toBesselPotentialSpace_eq_iff (k : ℕ) (h : H^{k, p}(E, ℂ)) :
    (∃ u, toBesselPotentialSpace hp hp_top k u = h) ↔
      ∃ g : Lp ℝ p (volume : Measure E),
        h.toDistr = Lp.toTemperedDistribution (Complex.ofRealCLM.compLp g) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨realValue k u,
      toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top (value_ae_eq_realValue k u)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨u, hu⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k g).1
      (hg ▸ h.memSobolev_toDistr)
    exact ⟨u, BesselPotentialSpace.ext (by rw [toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top hu,
      hg])⟩

/-- Through the inclusion `H^{k,p} ⊆ Lᵖ`, `toBesselPotentialSpace u` is the complexification of any
real `Lᵖ` function agreeing almost everywhere with the value of `u`. -/
theorem inclusionLp_toBesselPotentialSpace_of_ae_eq {k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {g : Lp ℝ p (volume : Measure E)} (hg : (value k u : E → ℝ) =ᵐ[volume] g) :
    BesselPotentialSpace.inclusionLp (Nat.cast_nonneg k) (toBesselPotentialSpace hp hp_top k u) =
      Complex.ofRealCLM.compLp g :=
  (BesselPotentialSpace.inclusionLp_eq_iff _).2
    (toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top hg).symm

/-- Through the inclusion `H^{k,p} ⊆ Lᵖ`, `toBesselPotentialSpace u` is almost everywhere the
complexified value of `u`. -/
theorem coeFn_inclusionLp_toBesselPotentialSpace (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    BesselPotentialSpace.inclusionLp (Nat.cast_nonneg k) (toBesselPotentialSpace hp hp_top k u)
      =ᵐ[volume] fun x ↦ (value k u x : ℂ) := by
  rw [inclusionLp_toBesselPotentialSpace_of_ae_eq hp hp_top (value_ae_eq_realValue k u),
    ← complexValue_apply]
  exact complexValue_ae_eq k u

/-- `toBesselPotentialSpace u` is the element of `H^{k,p}(E, ℂ)` that is almost everywhere the
complexified value of `u` through the inclusion `H^{k,p} ⊆ Lᵖ`. -/
theorem toBesselPotentialSpace_eq_iff {k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {h : H^{k, p}(E, ℂ)} :
    toBesselPotentialSpace hp hp_top k u = h ↔
      BesselPotentialSpace.inclusionLp (Nat.cast_nonneg k) h
        =ᵐ[volume] fun x ↦ (value k u x : ℂ) := by
  refine ⟨fun hu ↦ hu ▸ coeFn_inclusionLp_toBesselPotentialSpace hp hp_top k u, fun hh ↦ ?_⟩
  refine BesselPotentialSpace.inclusionLp_injective (Nat.cast_nonneg k) (Lp.ext ?_)
  exact (coeFn_inclusionLp_toBesselPotentialSpace hp hp_top k u).trans hh.symm

/-- The identification is compatible with lowering the order: the inclusion
`H^{k+1,p} ⊆ H^{k,p}` of `toBesselPotentialSpace u` is `toBesselPotentialSpace` of the lower-order
part of `u`. -/
theorem inclusion_toBesselPotentialSpace (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p (k + 1)) :
    BesselPotentialSpace.inclusion (Nat.cast_le.2 k.le_succ)
        (toBesselPotentialSpace hp hp_top (k + 1) u) =
      toBesselPotentialSpace hp hp_top k (lowerOrder k u) :=
  BesselPotentialSpace.ext <| by
    ext φ
    rw [BesselPotentialSpace.toDistr_inclusion, toDistr_toBesselPotentialSpace_apply,
      toDistr_toBesselPotentialSpace_apply, value_succ]

/-- The range of the identification `W^{k,p}(E) → H^{k,p}(E, ℂ)` is closed. -/
theorem isClosed_range_toBesselPotentialSpace (k : ℕ) :
    IsClosed (Set.range (toBesselPotentialSpace (E := E) hp hp_top k)) := by
  -- The complexified real functions are closed in `Lᵖ(E, ℂ)`: taking real parts is a retraction.
  have hclosed : IsClosed (Set.range (Complex.ofRealCLM.compLpL p (volume : Measure E))) := by
    refine Function.LeftInverse.isClosed_range (f := Complex.reCLM.compLpL p volume)
      (fun g ↦ Lp.ext ?_) (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
    simp only [ContinuousLinearMap.compLpL_apply]
    filter_upwards [Complex.reCLM.coeFn_compLp (p := p) (μ := volume)
      (Complex.ofRealCLM.compLp g), Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) g]
      with x h₁ h₂
    simp [h₁, h₂]
  -- By Calderón's theorem, the range is the preimage of this set under the inclusion into `Lᵖ`.
  convert hclosed.preimage (BesselPotentialSpace.inclusionLp (Nat.cast_nonneg k)).continuous
    using 1
  ext h
  simp only [Set.mem_preimage, Set.mem_range, ContinuousLinearMap.compLpL_apply,
    exists_toBesselPotentialSpace_eq_iff hp hp_top k h]
  refine exists_congr fun g ↦ ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · exact ((BesselPotentialSpace.inclusionLp_eq_iff _).2 hg.symm).symm
  · rw [hg, BesselPotentialSpace.toTemperedDistribution_inclusionLp]

/-- **The `W^{k,p}` and `H^{k,p}` norms are equivalent.** For `1 < p < ∞` there is `C` such that
`‖u‖_{W^{k,p}} ≤ C ‖u‖_{H^{k,p}}` for every `u ∈ W^{k,p}(E)`; the reverse bound
`‖u‖_{H^{k,p}} ≤ ‖toBesselPotentialSpace‖ ‖u‖_{W^{k,p}}` is the continuity of
`TauCeti.Wkp.toBesselPotentialSpace`. -/
theorem exists_norm_le_mul_norm_toBesselPotentialSpace (k : ℕ) :
    ∃ C : ℝ, ∀ u : Wkp (volume : Measure E) ⊤ p k,
      ‖u‖ ≤ C * ‖toBesselPotentialSpace hp hp_top k u‖ := by
  obtain ⟨K, hK⟩ :=
    (toBesselPotentialSpace (E := E) hp hp_top k).antilipschitz_of_injective_of_isClosed_range
      (toBesselPotentialSpace_injective hp hp_top k)
      (isClosed_range_toBesselPotentialSpace hp hp_top k)
  exact ⟨K, fun u ↦ by simpa using hK.le_mul_dist u 0⟩

/-- **The identification commutes with derivatives.** The value of `d ∈ W^{j,q}(E)` is a weak
derivative in direction `v` of the value of `u ∈ W^{k,p}(E)` exactly when the tempered distribution
of `d` is the derivative in direction `v` of the tempered distribution of `u`. -/
theorem hasWeakLineDerivOn_iff_lineDerivOp_toDistr_toBesselPotentialSpace {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : 1 < q) (hq_top : q ≠ ∞) {j k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {d : Wkp (volume : Measure E) ⊤ q j} {v : E} :
    HasWeakLineDerivOn volume ⊤ (value k u) (value j d) v ↔
      ∂_{v} (toBesselPotentialSpace hp hp_top k u).toDistr =
        (toBesselPotentialSpace hq hq_top j d).toDistr := by
  have hg := value_ae_eq_realValue k u
  have hg' := value_ae_eq_realValue j d
  rw [toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top hg,
    toDistr_toBesselPotentialSpace_of_ae_eq hq hq_top hg',
    ← hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq]
  exact ⟨fun hd ↦ (hd.congr_ae (by simpa using hg)).congr_ae_deriv (by simpa using hg'),
    fun hd ↦ (hd.congr_ae (by simpa using hg.symm)).congr_ae_deriv (by simpa using hg'.symm)⟩

/-- **The identification commutes with derivatives.** If the value of `d ∈ W^{j,q}(E)` is a weak
derivative in direction `v` of the value of `u ∈ W^{k,p}(E)`, then the tempered distribution of
`d` is the derivative in direction `v` of the tempered distribution of `u`. -/
theorem lineDerivOp_toDistr_toBesselPotentialSpace_of_hasWeakLineDerivOn {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞) {j k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {d : Wkp (volume : Measure E) ⊤ q j} {v : E}
    (hd : HasWeakLineDerivOn volume ⊤ (value k u) (value j d) v) :
    ∂_{v} (toBesselPotentialSpace hp hp_top k u).toDistr =
      (toBesselPotentialSpace hq hq_top j d).toDistr :=
  (hasWeakLineDerivOn_iff_lineDerivOp_toDistr_toBesselPotentialSpace hp hp_top hq hq_top).1 hd

end TauCeti.Wkp
