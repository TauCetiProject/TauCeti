/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Integral
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Contour
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz

/-!
# Quantization of contour integrals of parameter-dependent symbols

Let `a` be a parameter-dependent symbol of order `m` (`TauCeti.ParameterSymbol`), `γ` a path in its
set of spectral parameters going to infinity at least linearly and `g` a weight with
`‖g t‖ ≤ C (|t| ^ σ + (1 + |t|) ^ σ)`, where `-1 < σ` and `m + 2 σ + 2 < 0`. The contour integral
`c(x, ξ) = ∫ g(t) a(x, ξ, γ(t)) dt` is a symbol of order `m + 2 σ + 2`
(`TauCeti.ParameterSymbol.contourIntegral`). This file shows that its quantization is the integral
of the quantizations along the path:

`Op(c) = ∫ g(t) Op(a(γ t)) dt`.

This is how Seeley's construction of the complex powers of an elliptic operator `A` passes from
symbols to operators: the power `A^{-σ}` is an integral of the resolvents `(A - λ)⁻¹` along a
contour, these are quantizations of a resolvent parametrix `b(λ)` up to remainders decaying in `λ`,
and the integral of the quantizations `Op(b(λ))` is the quantization of the contour integral of
`b`.

* On a Schwartz function `u`, at each position `x`, the identity
  `Op(c) u (x) = ∫ g(t) Op(a(γ t)) u (x) dt` holds with an integrable right side
  (`TauCeti.ParameterSymbol.quantizeSchwartzValue_contourIntegral`,
  `TauCeti.ParameterSymbol.integrable_smul_quantizeSchwartzValue_toSymbol`). This is the
  exchange of quantization and a parameter integral with an integrable majorant
  (`TauCeti.quantizeSchwartzValue_integral_of_integrable_bound`): the coefficients
  `g(t) a(x, ξ, γ(t))` are dominated by `G(t)` with `G` integrable, uniformly in the frequency,
  because a symbol of order `m ≤ 0` has size at most a multiple of `(1 + ‖z‖ ^ (1 / 2)) ^ m` at the
  spectral parameter `z`
  (`TauCeti.ParameterSymbol.exists_integrable_norm_mul_one_add_sqrt_rpow_le`).
* If `a` vanishes at the positions outside a compact set `K`, the same holds after pairing with an
  integrable function `φ` of the position
  (`TauCeti.ParameterSymbol.integral_smul_quantizeSchwartzValue_contourIntegral`); this is the
  identity of tempered distributions on Schwartz input.
* For such `a`, between Sobolev spaces of Hilbert-space-valued functions, the identity holds as a
  Bochner integral of bounded operators `H^s → H^{s - m'}` for every order `m'` with
  `m + 2 σ + 2 < m' ≤ 0` (`TauCeti.ParameterSymbol.quantizeSobolev_contourIntegral`). The operators
  `Op(a(γ t))` depend continuously on `t` in operator norm, because `z ↦ a(z)` is continuous into
  the symbols of order `m' > m` (`TauCeti.ParameterSymbol.continuousOn_inclusion_toSymbol`), and
  their norms are at most `C (1 + ‖γ t‖ ^ (1 / 2)) ^ (m - m')`
  (`TauCeti.ParameterSymbol.exists_norm_quantizeSobolev_inclusion_toSymbol_le`), which is
  integrable against `g` since `m + 2 σ + 2 < m'`. At the order `m' = m + 2 σ + 2` of the contour
  integral itself, this bound against the weight `|t| ^ σ` decays only like `|t| ^ (-1)`, which is
  not integrable.

## References

* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, second edition, Springer
  (2001), Chapter II, §§10–11.
-/

public section

noncomputable section

open MeasureTheory Set Real FourierTransform
open scoped FourierTransform SchwartzMap RealInnerProductSpace BesselPotentialSpace

namespace TauCeti

namespace ParameterSymbol

/-! ### Schwartz input -/

section Schwartz

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m σ : ℝ}
  (a : ParameterSymbol n Λ V W m) {γ g : ℝ → ℂ} (hγ : Continuous γ) (hγΛ : ∀ t, γ t ∈ Λ)
  (hg : AEStronglyMeasurable g) (hγc : ∃ c, ∀ t, 1 + |t| ≤ c * (1 + ‖γ t‖))
  (hgσ : ∃ C, ∀ t, ‖g t‖ ≤ C * (|t| ^ σ + (1 + |t|) ^ σ)) (hσ : -1 < σ)
  (hm : m + 2 * σ + 2 < 0)

include hγΛ hγc hgσ hσ hm in
/-- The integrand `g(t) a(x, ξ, γ(t))` of a contour integral is bounded, uniformly in the
positions of a compact set and in the frequency, by an integrable function of the time. -/
private theorem exists_integrable_norm_mul_norm_coefficient_le {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      ∀ t, ∀ x ∈ K, ∀ ξ, ‖g t‖ * ‖a.coefficient ((x, ξ), γ t)‖ ≤ G t := by
  have hm0 : m ≤ 0 := by linarith
  obtain ⟨D, hD0, hD⟩ := a.exists_norm_mixedDeriv_coefficient_le hK [] []
  obtain ⟨G, hG, hGb⟩ :=
    exists_integrable_norm_mul_one_add_sqrt_rpow_le hγc hgσ hσ hm0 (by linarith)
  refine ⟨fun t ↦ D * G t, hG.const_mul D,
    fun t ↦ mul_nonneg hD0 ((by positivity : (0 : ℝ) ≤ _).trans (hGb t)), fun t x hx ξ ↦ ?_⟩
  have h := hD x hx ξ (γ t) (hγΛ t)
  simp only [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero] at h
  calc ‖g t‖ * ‖a.coefficient ((x, ξ), γ t)‖
      ≤ ‖g t‖ * (D * (1 + Real.sqrt ‖γ t‖) ^ m) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left
          (parameterWeight_rpow_le_one_add_sqrt_rpow ξ (γ t) hm0) hD0)) (norm_nonneg _)
    _ = D * (‖g t‖ * (1 + Real.sqrt ‖γ t‖) ^ m) := by ring
    _ ≤ D * G t := mul_le_mul_of_nonneg_left (hGb t) hD0

include hγ hγΛ in
/-- The coefficient of `a` along the path, at positions and frequencies depending continuously on
a parameter, is continuous. -/
private theorem continuous_coefficient_comp {X : Type*} [TopologicalSpace X]
    {q : X → CoordinateSpace n × CoordinateSpace n} (hq : Continuous q) {τ : X → ℝ}
    (hτ : Continuous τ) :
    Continuous fun y ↦ a.coefficient (q y, γ (τ y)) :=
  a.contDiffOn_coefficient.continuousOn.comp_continuous (hq.prodMk (hγ.comp hτ))
    fun _ ↦ ⟨mem_univ _, hγΛ _⟩

include hγ hγΛ hg in
/-- The weighted coefficients `g(t) a((x, ξ), γ(t))` along the path are jointly measurable in the
time and the frequency. -/
private theorem aestronglyMeasurable_smul_coefficient (x : CoordinateSpace n) :
    AEStronglyMeasurable (fun p : ℝ × CoordinateSpace n ↦ g p.1 • a.coefficient ((x, p.2), γ p.1))
      (volume.prod volume) :=
  hg.comp_fst.smul (a.continuous_coefficient_comp hγ hγΛ
    (by fun_prop : Continuous fun p : ℝ × CoordinateSpace n ↦ (x, p.2))
    continuous_fst).aestronglyMeasurable

variable (u : 𝓢(CoordinateSpace n, V))

/-- The weighted symbol at `γ t` quantizes to the weighted quantization. -/
private theorem quantizeSchwartzValue_smul_coefficient (t : ℝ) (y : CoordinateSpace n) :
    quantizeSchwartzValue (fun p ↦ g t • a.coefficient (p, γ t)) u y =
      g t • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u y := by
  rw [← quantizeSchwartzValue_smul_left]
  congr 1
  ext1 p
  simp

variable (x : CoordinateSpace n)

include hγ hγΛ hg hγc hgσ hσ hm in
/-- **The integrand is integrable.** For a Schwartz function `u` and a position `x`, the
quantizations of the symbols along the path, weighted by `g`, are integrable in the time. -/
theorem integrable_smul_quantizeSchwartzValue_toSymbol :
    Integrable fun t ↦ g t • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u x := by
  obtain ⟨G, hG, -, hGb⟩ := a.exists_integrable_norm_mul_norm_coefficient_le hγΛ hγc hgσ hσ hm
    (isCompact_singleton (x := x))
  simpa only [a.quantizeSchwartzValue_smul_coefficient u] using
    integrable_quantizeSchwartzValue_of_integrable_bound volume
      (fun t p ↦ g t • a.coefficient (p, γ t)) u x (m := 0)
      (a.aestronglyMeasurable_smul_coefficient hγ hγΛ hg x) hG fun t ξ ↦ by
        simpa [norm_smul] using hGb t x rfl ξ

/-- **Quantization of a contour integral, on Schwartz functions.** For a Schwartz function `u` and
a position `x`, the quantization of the contour integral `∫ g(t) a(·, ·, γ(t)) dt` is the integral
of the quantizations of the symbols along the path:

`Op(∫ g(t) a(γ t) dt) u (x) = ∫ g(t) Op(a(γ t)) u (x) dt`. -/
theorem quantizeSchwartzValue_contourIntegral :
    quantizeSchwartzValue (a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm).coefficient u x =
      ∫ t, g t • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u x := by
  obtain ⟨G, hG, -, hGb⟩ := a.exists_integrable_norm_mul_norm_coefficient_le hγΛ hγc hgσ hσ hm
    (isCompact_singleton (x := x))
  rw [quantizeSchwartzValue_congr_left (b := fun p ↦ ∫ t, g t • a.coefficient (p, γ t))
      (fun ξ ↦ coefficient_contourIntegral ..) u,
    quantizeSchwartzValue_integral_of_integrable_bound volume
      (fun t p ↦ g t • a.coefficient (p, γ t)) u x (m := 0)
      (a.aestronglyMeasurable_smul_coefficient hγ hγΛ hg x) hG fun t ξ ↦ by
        simpa [norm_smul] using hGb t x rfl ξ]
  simp only [a.quantizeSchwartzValue_smul_coefficient u]

include hγΛ hγc hgσ hσ hm in
/-- If `a` vanishes at the positions outside a compact set, the weighted quantizations
`g(t) Op(a(γ t)) u (y)` are bounded, uniformly in the position, by an integrable function of the
time. -/
private theorem exists_integrable_norm_smul_quantizeSchwartzValue_le {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (ha : ∀ x ∉ K, ∀ ξ z, a.coefficient ((x, ξ), z) = 0) :
    ∃ G : ℝ → ℝ, Integrable G ∧ ∀ t y,
      ‖g t • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u y‖ ≤ G t := by
  obtain ⟨G, hG, hG0, hGb⟩ :=
    a.exists_integrable_norm_mul_norm_coefficient_le hγΛ hγc hgσ hσ hm hK
  set M := ∫ ζ, (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((0 : ℝ) / 2) * ‖𝓕 u ζ‖
  refine ⟨fun t ↦ G t * M, hG.mul_const M, fun t y ↦ ?_⟩
  rw [← a.quantizeSchwartzValue_smul_coefficient u]
  by_cases hy : y ∈ K
  · exact norm_quantizeSchwartzValue_le (fun ξ ↦ by simpa [norm_smul] using hGb t y hy ξ) u
  · -- Outside `K` the symbol vanishes at the position `y`, so its quantization does.
    have h0 : quantizeSchwartzValue (fun p ↦ g t • a.coefficient (p, γ t)) u y = 0 := by
      simp [quantizeSchwartzValue_def, ha y hy]
    rw [h0, norm_zero]
    exact mul_nonneg (hG0 t) (integral_nonneg fun _ ↦ by positivity)

include hγ hγΛ hg in
/-- The weighted quantizations `g(t) Op(a(γ t)) u (y)` are jointly measurable in the position and
the time, as integrals in the frequency of a jointly measurable integrand. -/
private theorem aestronglyMeasurable_smul_quantizeSchwartzValue_toSymbol :
    AEStronglyMeasurable (fun p : CoordinateSpace n × ℝ ↦
      g p.2 • quantizeSchwartzValue (a.toSymbol (γ p.2)).coefficient u p.1)
      (volume.prod volume) := by
  have hc := a.continuous_coefficient_comp hγ hγΛ
    (by fun_prop : Continuous fun q : (CoordinateSpace n × ℝ) × CoordinateSpace n ↦
      (q.1.1, (2 * π) • q.2))
    (by fun_prop : Continuous fun q : (CoordinateSpace n × ℝ) × CoordinateSpace n ↦ q.1.2)
  have h : AEStronglyMeasurable (fun q : (CoordinateSpace n × ℝ) × CoordinateSpace n ↦
      𝐞 ⟪q.2, q.1.1⟫ • (g q.1.2 • a.coefficient ((q.1.1, (2 * π) • q.2), γ q.1.2)) (𝓕 u q.2))
      ((volume.prod volume).prod volume) :=
    (Real.continuous_fourierChar.comp (continuous_snd.inner (continuous_fst.comp continuous_fst))
      ).aestronglyMeasurable.smul (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        ((hg.comp_snd.comp_fst.smul hc.aestronglyMeasurable).prodMk
          ((𝓕 u).continuous.comp continuous_snd).aestronglyMeasurable))
  exact h.integral_prod_right'.congr (.of_forall fun p ↦ by
    dsimp only
    rw [← a.quantizeSchwartzValue_smul_coefficient u, quantizeSchwartzValue_def])

include hγ hγΛ hg hγc hgσ hσ hm in
/-- **Quantization of a contour integral, against a test function.** If `a` vanishes at the
positions outside a compact set, then for a Schwartz function `u` and an integrable function `φ`,

`∫ φ(x) Op(∫ g(t) a(γ t) dt) u (x) dx = ∫ g(t) ∫ φ(x) Op(a(γ t)) u (x) dx dt`.

For a Schwartz function `φ` both sides are pairings of tempered distributions. -/
theorem integral_smul_quantizeSchwartzValue_contourIntegral {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (ha : ∀ x ∉ K, ∀ ξ z, a.coefficient ((x, ξ), z) = 0)
    {φ : CoordinateSpace n → ℂ} (hφ : Integrable φ) :
    ∫ x, φ x • quantizeSchwartzValue (a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm).coefficient u x =
      ∫ t, g t • ∫ x, φ x • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u x := by
  obtain ⟨G, hG, hGb⟩ :=
    a.exists_integrable_norm_smul_quantizeSchwartzValue_le hγΛ hγc hgσ hσ hm u hK ha
  have hH : Integrable (fun p : CoordinateSpace n × ℝ ↦
      φ p.1 • g p.2 • quantizeSchwartzValue (a.toSymbol (γ p.2)).coefficient u p.1)
      (volume.prod volume) := by
    refine (hφ.norm.mul_prod hG).mono' (hφ.aestronglyMeasurable.comp_fst.smul
      (a.aestronglyMeasurable_smul_quantizeSchwartzValue_toSymbol hγ hγΛ hg u))
      (.of_forall fun p ↦ ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hGb p.2 p.1) (norm_nonneg _)
  calc ∫ x, φ x • quantizeSchwartzValue (a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm).coefficient u x
      = ∫ x, ∫ t, φ x • g t • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u x := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [a.quantizeSchwartzValue_contourIntegral hγ hγΛ hg hγc hgσ hσ hm u x, integral_smul]
    _ = ∫ t, ∫ x, φ x • g t • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u x :=
        integral_integral_swap hH
    _ = ∫ t, g t • ∫ x, φ x • quantizeSchwartzValue (a.toSymbol (γ t)).coefficient u x :=
        integral_congr_ae (.of_forall fun t ↦ by
          dsimp only
          rw [← integral_smul]
          exact integral_congr_ae (.of_forall fun x ↦ smul_comm _ _ _))

end Schwartz

/-! ### Sobolev spaces -/

section Sobolev

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] {m σ m' : ℝ} (a : ParameterSymbol n Λ V W m) {γ g : ℝ → ℂ}
  (hγ : Continuous γ) (hγΛ : ∀ t, γ t ∈ Λ) (hg : AEStronglyMeasurable g)
  (hγc : ∃ c, ∀ t, 1 + |t| ≤ c * (1 + ‖γ t‖))
  (hgσ : ∃ C, ∀ t, ‖g t‖ ≤ C * (|t| ^ σ + (1 + |t|) ^ σ)) (hσ : -1 < σ)
  (hm : m + 2 * σ + 2 < 0) (hm' : m + 2 * σ + 2 < m') (hm'0 : m' ≤ 0)
  (K : TopologicalSpace.Compacts (CoordinateSpace n))
  (ha : ∀ x ∉ K, ∀ ξ z, a.coefficient ((x, ξ), z) = 0) (s : ℝ)

include hγ hγΛ hg hγc hgσ hσ hm' hm'0 in
/-- **The quantized integrand is Bochner integrable.** If `a` vanishes at the positions outside a
compact set `K` and `m + 2 σ + 2 < m' ≤ 0`, the operators `g(t) Op(a(γ t)) : H^s → H^{s - m'}`
are integrable in operator norm. They depend continuously on `t`, and their norms are at most
`C ‖g t‖ (1 + ‖γ t‖ ^ (1 / 2)) ^ (m - m')`, which is integrable since `m + 2 σ + 2 < m'`. -/
theorem integrable_smul_quantizeSobolev_toSymbol :
    Integrable fun t ↦ g t •
      (Symbol.inclusion (m' := m') (by linarith) (a.toSymbol (γ t))).quantizeSobolev
      ((a.hasCompactSpatialSupport_toSymbol (γ t) K.isCompact fun x hx ξ ↦ ha x hx ξ _).inclusion
        (by linarith)) s := by
  have hmm' : m < m' := by linarith
  have hcont : Continuous fun t ↦ (Symbol.inclusion hmm'.le (a.toSymbol (γ t))).quantizeSobolev
      ((a.hasCompactSpatialSupport_toSymbol (γ t) K.isCompact fun x hx ξ ↦ ha x hx ξ _).inclusion
        hmm'.le) s :=
    Symbol.continuous_quantizeSobolev ((a.continuousOn_inclusion_toSymbol hmm').comp_continuous hγ
      hγΛ) (K := K) (fun t x hx ξ ↦ by
        simp only [Function.comp_apply, Symbol.coefficient_inclusion, coefficient_toSymbol,
          ha x hx]) s
  obtain ⟨C, hC0, hC⟩ := a.exists_norm_quantizeSobolev_inclusion_toSymbol_le hmm'.le hm'0 K ha s
  obtain ⟨G, hG, hGb⟩ := exists_integrable_norm_mul_one_add_sqrt_rpow_le hγc hgσ hσ
    (μ := m - m') (by linarith) (by linarith)
  refine (hG.const_mul C).mono' (hg.smul hcont.aestronglyMeasurable) (.of_forall fun t ↦ ?_)
  rw [norm_smul]
  calc ‖g t‖ * ‖(Symbol.inclusion hmm'.le (a.toSymbol (γ t))).quantizeSobolev
        ((a.hasCompactSpatialSupport_toSymbol (γ t) K.isCompact fun x hx ξ ↦
          ha x hx ξ _).inclusion hmm'.le) s‖
      ≤ ‖g t‖ * (C * (1 + Real.sqrt ‖γ t‖) ^ (m - m')) :=
        mul_le_mul_of_nonneg_left (hC (γ t) (hγΛ t)) (norm_nonneg _)
    _ = C * (‖g t‖ * (1 + Real.sqrt ‖γ t‖) ^ (m - m')) := by ring
    _ ≤ C * G t := mul_le_mul_of_nonneg_left (hGb t) hC0

include hγ hγΛ hg hγc hgσ hσ hm' hm'0 in
/-- **Quantization of a contour integral, on Sobolev spaces.** Let `a` vanish at the positions
outside a compact set `K`, and let `m + 2 σ + 2 < m' ≤ 0`. As bounded operators
`H^s → H^{s - m'}`, the quantization of the contour integral `∫ g(t) a(·, ·, γ(t)) dt` is the
Bochner integral of the quantizations of the symbols along the path:

`Op(∫ g(t) a(γ t) dt) = ∫ g(t) Op(a(γ t)) dt`. -/
theorem quantizeSobolev_contourIntegral :
    (Symbol.inclusion hm'.le (a.contourIntegral hγ hγΛ hg hγc hgσ hσ hm)).quantizeSobolev
        ((a.hasCompactSpatialSupport_contourIntegral hγ hγΛ hg hγc hgσ hσ hm K.isCompact
          ha).inclusion hm'.le) s =
      ∫ t, g t • (Symbol.inclusion (m' := m') (by linarith) (a.toSymbol (γ t))).quantizeSobolev
        ((a.hasCompactSpatialSupport_toSymbol (γ t) K.isCompact fun x hx ξ ↦ ha x hx ξ _).inclusion
          (by linarith)) s := by
  have hint := a.integrable_smul_quantizeSobolev_toSymbol hγ hγΛ hg hγc hgσ hσ hm' hm'0 K ha s
  refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ ?_
  refine BesselPotentialSpace.ext ?_
  ext φ
  -- Pairing with `φ` after evaluating at `u` is a continuous linear functional of the operator.
  set L := (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) W φ ∘L
    BesselPotentialSpace.toDistrCLM (CoordinateSpace n) W (s - m') 2) ∘L
      ContinuousLinearMap.apply ℂ _ (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)
  have hL (T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m'}(CoordinateSpace n, W)) :
      L T = (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      BesselPotentialSpace.evalCLM_comp_toDistrCLM_apply]
  rw [← hL, ← hL, ← L.integral_comp_comm hint]
  simp only [map_smul]
  simp only [hL, Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    Symbol.coefficient_inclusion]
  exact a.integral_smul_quantizeSchwartzValue_contourIntegral hγ hγΛ hg hγc hgσ hσ hm u
    K.isCompact ha φ.integrable

end Sobolev

end ParameterSymbol

end TauCeti
