/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

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

The identification commutes with derivatives: a weak directional derivative of the value of
`u ∈ W^{k,p}(E)` that is the value of `d ∈ W^{j,p}(E)` is the corresponding derivative of the
tempered distribution of `u`.

## The argument

Both spaces are complete, and both embed continuously into the tempered distributions, the
Sobolev space through its value in `Lᵖ` and the Bessel-potential space through its tempered
distribution (`BesselPotentialSpace.continuous_toDistr`). The map agrees with these embeddings, so
its graph is closed and the closed graph theorem makes it continuous
(`BesselPotentialSpace.continuous_of_continuous_toDistr`).
It is injective, since an `Lᵖ` function is determined by its tempered distribution. Its range is
closed: the inclusion `H^{k,p} ⊆ H^{0,p} = Lᵖ` is continuous
(`BesselPotentialSpace.inclusionOfOneLt`), so a limit of complexified real functions is again a
complexified real function, which lies in the range by Calderón's theorem. The open mapping
theorem then bounds the inverse on the range
(`ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range`).

No explicit value of the constants is claimed. The statements are for Lebesgue measure `volume`,
the measure of Mathlib's Bessel-potential spaces.

## Main declarations

* `TauCeti.Wkp.toBesselPotentialSpace`: the identification `W^{k,p}(E) →L[ℝ] H^{k,p}(E, ℂ)`.
* `TauCeti.Wkp.toDistr_toBesselPotentialSpace_apply`,
  `TauCeti.Wkp.toDistr_toBesselPotentialSpace_of_ae_eq`: its tempered distribution is the
  complexified value.
* `TauCeti.Wkp.injective_toBesselPotentialSpace`: it is injective.
* `TauCeti.Wkp.exists_toBesselPotentialSpace_eq_iff`: its range consists of the elements of
  `H^{k,p}(E, ℂ)` given by real `Lᵖ` functions.
* `TauCeti.Wkp.isClosed_range_toBesselPotentialSpace`: the range is closed.
* `TauCeti.Wkp.exists_norm_le_mul_norm_toBesselPotentialSpace`: the reverse bound
  `‖u‖_{W^{k,p}} ≤ C ‖u‖_{H^{k,p}}`, so that the two norms are equivalent.
* `TauCeti.Wkp.lineDerivOp_toDistr_toBesselPotentialSpace`: the identification commutes with
  directional derivatives.

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

/-- Restricting `volume` to the whole space does not change it. -/
private theorem volume_restrict_top :
    (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume := by
  simp

/-- The value of a Sobolev function on the whole space, as a complex `Lᵖ` function for `volume`. -/
private def complexValue (k : ℕ) :
    Wkp (volume : Measure E) ⊤ p k →L[ℝ] Lp ℂ p (volume : Measure E) :=
  (Complex.ofRealCLM.compLpL p volume).comp
    ((castLpₗᵢ (𝕜 := ℝ) volume_restrict_top).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (valueL k))

/-- The bundled and unbundled complexifications of a real `Lᵖ` function agree. -/
private theorem compLpL_ofRealCLM (g : Lp ℝ p (volume : Measure E)) :
    Complex.ofRealCLM.compLpL p volume g = Complex.ofRealCLM.compLp g :=
  Lp.ext <| by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (p := p) (μ := volume) g,
      Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) g] with x h₁ h₂
    rw [h₁, h₂]

private theorem complexValue_apply (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    complexValue k u =
      Complex.ofRealCLM.compLp (castLpₗᵢ (𝕜 := ℝ) volume_restrict_top (value k u)) := by
  rw [complexValue, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, valueL_apply,
    compLpL_ofRealCLM, ContinuousLinearEquiv.coe_coe,
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
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume)
    (castLpₗᵢ (𝕜 := ℝ) volume_restrict_top (value k u))] with x hx
  rw [hx, Complex.ofRealCLM_apply, coeFn_castLpₗᵢ]

/-- If the value of `u` agrees almost everywhere with a real `Lᵖ` function `g`, then the
complexified value of `u` is the complexification of `g`. -/
private theorem complexValue_eq_of_ae_eq {k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {g : Lp ℝ p (volume : Measure E)} (hg : (value k u : E → ℝ) =ᵐ[volume] g) :
    complexValue k u = Complex.ofRealCLM.compLp g := by
  refine Lp.ext ?_
  filter_upwards [complexValue_ae_eq k u, Complex.ofRealCLM.coeFn_compLp (p := p) (μ := volume) g,
    hg] with x h₁ h₂ h₃
  rw [h₁, h₂, Complex.ofRealCLM_apply, h₃]

variable (hp : 1 < p) (hp_top : p ≠ ∞)
include hp hp_top

/-- By Calderón's theorem, the complexified value of a `W^{k,p}` function lies in `H^{k,p}`. -/
private theorem memSobolev_complexValue (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    MemSobolev k p (complexValue k u : 𝓢'(E, ℂ)) := by
  rw [complexValue_apply]
  refine (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k _).2 ⟨u, ?_⟩
  exact .of_forall fun x ↦ (coeFn_castLpₗᵢ volume_restrict_top (value k u) x).symm

/-- **The identification `W^{k,p}(E) = H^{k,p}(E)`.** For `1 < p < ∞`, the map sending a real
`W^{k,p}` function on the whole space to its complexification, as an element of Mathlib's
Bessel-potential space `H^{k,p}(E, ℂ)`. It is continuous, injective with closed range, and
bounded below (`TauCeti.Wkp.exists_norm_le_mul_norm_toBesselPotentialSpace`), so the `W^{k,p}`
and `H^{k,p}` norms are equivalent. -/
def toBesselPotentialSpace (k : ℕ) : Wkp (volume : Measure E) ⊤ p k →L[ℝ] H^{k, p}(E, ℂ) :=
  let L : Wkp (volume : Measure E) ⊤ p k →ₗ[ℝ] H^{k, p}(E, ℂ) :=
    { toFun u := (memSobolev_complexValue hp hp_top k u).toBesselPotentialSpace
      map_add' u v := BesselPotentialSpace.ext <| by
        rw [BesselPotentialSpace.toDistr_add, MemSobolev.toBesselPotentialSpace_toDistr,
          MemSobolev.toBesselPotentialSpace_toDistr, MemSobolev.toBesselPotentialSpace_toDistr]
        exact map_add (toDistrValue k) u v
      map_smul' c u := BesselPotentialSpace.ext <| by
        rw [RingHom.id_apply, MemSobolev.toBesselPotentialSpace_toDistr, ← toDistrValue_apply,
          map_smul, RCLike.real_smul_eq_coe_smul (K := ℂ) c (MemSobolev.toBesselPotentialSpace _),
          BesselPotentialSpace.toDistr_smul, MemSobolev.toBesselPotentialSpace_toDistr,
          toDistrValue_apply]
        exact RCLike.real_smul_eq_coe_smul (K := ℂ) c _ }
  { L with
    cont := BesselPotentialSpace.continuous_of_continuous_toDistr
      (X := Wkp (volume : Measure E) ⊤ p k) L <|
      (toDistrValue (E := E) (p := p) k).continuous.congr fun u ↦ by
        rw [toDistrValue_apply]
        exact (MemSobolev.toBesselPotentialSpace_toDistr _).symm }

private theorem toDistr_toBesselPotentialSpace (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k) :
    (toBesselPotentialSpace hp hp_top k u).toDistr = complexValue k u :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- The tempered distribution of `toBesselPotentialSpace u` is the complexification of any real
`Lᵖ` function agreeing almost everywhere with the value of `u`. -/
theorem toDistr_toBesselPotentialSpace_of_ae_eq {k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {g : Lp ℝ p (volume : Measure E)} (hg : (value k u : E → ℝ) =ᵐ[volume] g) :
    (toBesselPotentialSpace hp hp_top k u).toDistr =
      Lp.toTemperedDistribution (Complex.ofRealCLM.compLp g) := by
  rw [toDistr_toBesselPotentialSpace, complexValue_eq_of_ae_eq hg]

/-- The tempered distribution of `toBesselPotentialSpace u` pairs a Schwartz function `φ` with
`u` by integration: it is `φ ↦ ∫ φ u`. -/
theorem toDistr_toBesselPotentialSpace_apply (k : ℕ) (u : Wkp (volume : Measure E) ⊤ p k)
    (φ : 𝓢(E, ℂ)) :
    (toBesselPotentialSpace hp hp_top k u).toDistr φ = ∫ x, φ x * (value k u x : ℂ) := by
  rw [toDistr_toBesselPotentialSpace, Lp.toTemperedDistribution_apply]
  exact integral_congr_ae ((complexValue_ae_eq k u).mono fun x hx ↦ by simp [hx])

/-- The identification `W^{k,p}(E) → H^{k,p}(E, ℂ)` is injective. -/
theorem injective_toBesselPotentialSpace (k : ℕ) :
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
    exact ⟨castLpₗᵢ (𝕜 := ℝ) volume_restrict_top (value k u),
      toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top
        (.of_forall fun x ↦ (coeFn_castLpₗᵢ volume_restrict_top (value k u) x).symm)⟩
  · rintro ⟨g, hg⟩
    obtain ⟨u, hu⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k g).1
      (hg ▸ h.memSobolev_toDistr)
    exact ⟨u, BesselPotentialSpace.ext (by rw [toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top hu,
      hg])⟩

/-- The `Lᵖ` function underlying an element of `H^{k,p}(E, ℂ)`, through the continuous inclusion
`H^{k,p} ⊆ H^{0,p} = Lᵖ`. -/
private def toLpOfNat (k : ℕ) : H^{k, p}(E, ℂ) →L[ℂ] Lp ℂ p (volume : Measure E) :=
  (BesselPotentialSpace.toLpₗᵢ E ℂ 0 p).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (BesselPotentialSpace.inclusionOfOneLt hp hp_top (Nat.cast_nonneg k))

private theorem toTemperedDistribution_toLpOfNat (k : ℕ) (h : H^{k, p}(E, ℂ)) :
    (toLpOfNat hp hp_top k h : 𝓢'(E, ℂ)) = h.toDistr := by
  have := BesselPotentialSpace.besselPotential_neg_toLp_eq
    (f := BesselPotentialSpace.inclusionOfOneLt hp hp_top (Nat.cast_nonneg k) h)
  simpa [toLpOfNat] using this

/-- The range of the identification `W^{k,p}(E) → H^{k,p}(E, ℂ)` is closed. -/
theorem isClosed_range_toBesselPotentialSpace (k : ℕ) :
    IsClosed (Set.range (toBesselPotentialSpace (E := E) hp hp_top k)) := by
  refine isClosed_of_closure_subset fun h hh ↦ ?_
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.1 hh
  choose u hu using hw
  set g : ℕ → Lp ℝ p (volume : Measure E) :=
    fun n ↦ castLpₗᵢ (𝕜 := ℝ) volume_restrict_top (value k (u n))
  -- Through the continuous inclusion into `Lᵖ`, the approximants are complexified real functions.
  have hT (n : ℕ) : toLpOfNat hp hp_top k (w n) = Complex.ofRealCLM.compLp (g n) := by
    refine LinearMap.ker_eq_bot.1 Lp.ker_toTemperedDistributionCLM_eq_bot ?_
    simp only [ContinuousLinearMap.coe_coe, Lp.toTemperedDistributionCLM_apply,
      toTemperedDistribution_toLpOfNat, ← hu n]
    exact toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top
      (.of_forall fun x ↦ (coeFn_castLpₗᵢ volume_restrict_top (value k (u n)) x).symm)
  have hT' : Tendsto (fun n ↦ Complex.ofRealCLM.compLpL p volume (g n)) atTop
      (𝓝 (toLpOfNat hp hp_top k h)) :=
    (((toLpOfNat hp hp_top k).continuous.tendsto h).comp hlim).congr fun n ↦ hT n
  -- Taking real parts, the real functions converge, and their limit represents `h`.
  have hre : Tendsto g atTop
      (𝓝 (Complex.reCLM.compLpL p volume (toLpOfNat hp hp_top k h))) := by
    refine (((Complex.reCLM.compLpL p volume).continuous.tendsto _).comp hT').congr fun n ↦ ?_
    refine Lp.ext ?_
    filter_upwards [Complex.reCLM.coeFn_compLpL (p := p) (μ := volume)
      (Complex.ofRealCLM.compLpL p volume (g n)),
      Complex.ofRealCLM.coeFn_compLpL (p := p) (μ := volume) (g n)] with x h₁ h₂
    simp [h₁, h₂]
  have hlim' := tendsto_nhds_unique
    (((Complex.ofRealCLM.compLpL p volume).continuous.tendsto _).comp hre) hT'
  refine (exists_toBesselPotentialSpace_eq_iff hp hp_top k h).2
    ⟨Complex.reCLM.compLpL p volume (toLpOfNat hp hp_top k h), ?_⟩
  rw [← compLpL_ofRealCLM, hlim', toTemperedDistribution_toLpOfNat]

/-- **The `W^{k,p}` and `H^{k,p}` norms are equivalent.** For `1 < p < ∞` there is `C` such that
`‖u‖_{W^{k,p}} ≤ C ‖u‖_{H^{k,p}}` for every `u ∈ W^{k,p}(E)`; the reverse bound
`‖u‖_{H^{k,p}} ≤ ‖toBesselPotentialSpace‖ ‖u‖_{W^{k,p}}` is the continuity of
`TauCeti.Wkp.toBesselPotentialSpace`. -/
theorem exists_norm_le_mul_norm_toBesselPotentialSpace (k : ℕ) :
    ∃ C : ℝ, ∀ u : Wkp (volume : Measure E) ⊤ p k,
      ‖u‖ ≤ C * ‖toBesselPotentialSpace hp hp_top k u‖ := by
  obtain ⟨K, hK⟩ :=
    (toBesselPotentialSpace (E := E) hp hp_top k).antilipschitz_of_injective_of_isClosed_range
      (injective_toBesselPotentialSpace hp hp_top k)
      (isClosed_range_toBesselPotentialSpace hp hp_top k)
  exact ⟨K, fun u ↦ by simpa using hK.le_mul_dist u 0⟩

/-- **The identification commutes with derivatives.** If the value of `d ∈ W^{j,p}(E)` is a weak
derivative in direction `v` of the value of `u ∈ W^{k,p}(E)`, then the tempered distribution of
`d` is the derivative in direction `v` of the tempered distribution of `u`. -/
theorem lineDerivOp_toDistr_toBesselPotentialSpace {j k : ℕ} {u : Wkp (volume : Measure E) ⊤ p k}
    {d : Wkp (volume : Measure E) ⊤ p j} {v : E}
    (hd : HasWeakLineDerivOn volume ⊤ (value k u) (value j d) v) :
    ∂_{v} (toBesselPotentialSpace hp hp_top k u).toDistr =
      (toBesselPotentialSpace hp hp_top j d).toDistr := by
  set g := castLpₗᵢ (𝕜 := ℝ) volume_restrict_top (value k u)
  set g' := castLpₗᵢ (𝕜 := ℝ) volume_restrict_top (value j d)
  have hg : (value k u : E → ℝ) =ᵐ[volume] g :=
    .of_forall fun x ↦ (coeFn_castLpₗᵢ volume_restrict_top (value k u) x).symm
  have hg' : (value j d : E → ℝ) =ᵐ[volume] g' :=
    .of_forall fun x ↦ (coeFn_castLpₗᵢ volume_restrict_top (value j d) x).symm
  rw [toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top hg,
    toDistr_toBesselPotentialSpace_of_ae_eq hp hp_top hg']
  refine (hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq g g' v).1 ?_
  exact (hd.congr_ae (by simpa using hg)).congr_ae_deriv (by simpa using hg')

end TauCeti.Wkp
