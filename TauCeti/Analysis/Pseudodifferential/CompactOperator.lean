/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Recovery
public import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.Analysis.Normed.Operator.Compact.StrongConvergence
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Analysis.Sobolev.BesselPotential.Duality

/-!
# Compactness of quantizations with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` that vanishes for positions outside a compact set `K`.
Its quantization `Op(a)` is bounded from `H^s(ℝⁿ; V)` to `H^{s - m}(ℝⁿ; W)`
(`TauCeti.Symbol.quantizeSobolev`). This file shows that, for a finite-dimensional fibre `W`, it
is moreover **compact** as an operator `H^s → H^r` for every `r < s - m`. In particular:

* a symbol of negative order `m < 0` with compact spatial support quantizes to a compact operator
  `H^s → H^s` (`TauCeti.Symbol.exists_isCompactOperator_quantizeSobolev` with `r = s`);
* a smoothing symbol with compact spatial support quantizes to a compact operator `H^s → H^r` for
  all real `s` and `r` (`TauCeti.Symbol.IsSmoothing.exists_isCompactOperator_quantizeSobolev`).

These are the local compactness statements behind the Fredholm theory of elliptic operators: the
remainders of a parametrix are of negative order, hence compact. The hypothesis on the support
cannot be dropped: the constant symbol `1` of order `0` (or `⟨ξ⟩ ^ m`, of order `m`) quantizes to a
Fourier multiplier, which commutes with translations and is not compact.

For a classical symbol the principal symbol decides compactness at the critical order: with `W`
finite-dimensional, `Op(a) : H^s → H^{s - m}` is compact if and only if the principal symbol
`σ(a)` vanishes (`TauCeti.ClassicalSymbol.isCompactOperator_quantizeSobolev_iff`), whatever `s`.
If `σ(a) = 0`, then `a` has order `m - 1` and the statement above applies. Conversely, the wave
packets `u_t(y) = t ^ (-s) exp(i ⟪y, t ξ⟫) φ(y) v` are bounded in `H^s` and tend to `0` weakly as
`t → ∞`, so a compact `Op(a)` sends them to a sequence that tends to `0` in norm. Paired with the
test functions `t ^ (s - m) exp(-i ⟪x, t ξ⟫) ψ(x)`, which are bounded in `H^{m - s}`, the images
nevertheless converge to `∫ ψ(x) σ(a)(x, ξ) (φ(x) v) dx`
(`TauCeti.ClassicalSymbol.tendsto_integral_smul_quantizeSchwartzValue_cutoffExponential`), which
therefore vanishes for all `ψ`, `φ` and `v`.

The proof combines the Sobolev mapping theorem with the Rellich theorem for a common compact
support. Since `a(x, ξ) = 0` for `x ∉ K`, the function `Op(a) u` vanishes outside `K`, so
`φ · Op(a) u = Op(a) u` for every Schwartz function `φ` equal to `1` on `K`
(`TauCeti.Symbol.smulLeftCLM_comp_quantizeSobolev`). Hence the operator `H^s → H^r` factors as
`Op(a) : H^s → H^{s - m}` followed by `u ↦ φ u` from `H^{s - m}` to `H^r`, which is compact for
`r < s - m` (`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`).

## Main results

* `TauCeti.Symbol.smulLeftCLM_comp_quantizeSobolev`: multiplying `Op(a) u` by a Schwartz function
  equal to `1` on a set outside which `a` vanishes does not change it.
* `TauCeti.Symbol.isCompactOperator_inclusion_comp_quantizeSobolev`: `Op(a) : H^s → H^r` is
  compact for `r < s - m`, between complex Hilbert spaces `V` and `W` with `W` finite-dimensional.
* `TauCeti.Symbol.exists_isCompactOperator_quantizeSobolev`: the same for finite-dimensional
  complex normed `V` and `W`.
* `TauCeti.Symbol.IsSmoothing.exists_isCompactOperator_quantizeSobolev`: smoothing symbols with
  compact spatial support give compact operators between any two Bessel-potential spaces.
* `TauCeti.ClassicalSymbol.principal_eq_zero_of_isCompactOperator`: a classical symbol with
  compact spatial support whose quantization `H^s → H^{s - m}` is compact has vanishing principal
  symbol.
* `TauCeti.ClassicalSymbol.isCompactOperator_quantizeSobolev_iff`: for finite-dimensional `W`, the
  quantization `H^s → H^{s - m}` of a classical symbol of order `m` with compact spatial support is
  compact exactly when its principal symbol vanishes.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators I*, Ann. of Math. 87 (1968),
  (5.2) (operators of negative order on a compact manifold are compact on `H^s`; the operators of
  order `m` with vanishing principal symbol are the compact ones `H^s → H^{s - m}`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (testing
  pseudodifferential operators on high-frequency wave packets).
* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (Rellich's theorem).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BesselPotentialSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- **Locality of the quantization.** If the symbol `a` vanishes at every position outside `K`,
and the Schwartz function `φ` equals `1` on `K`, then multiplying `Op(a) u` by `φ` does not change
it: `φ · Op(a) = Op(a)` as operators `H^s → H^{s - m}`. -/
theorem smulLeftCLM_comp_quantizeSobolev (ha : a.HasCompactSpatialSupport) (s : ℝ)
    {K : Set (CoordinateSpace n)} (hK : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : EqOn φ 1 K) :
    BesselPotentialSpace.smulLeftCLM (s - m) φ ∘L a.quantizeSobolev ha s =
      a.quantizeSobolev ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  ext ψ
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_smulLeftCLM,
    TemperedDistribution.smulLeftCLM_apply_apply,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  rw [SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, smul_eq_mul]
  by_cases hx : x ∈ K
  · rw [hφ hx, Pi.one_apply, one_mul]
  · rw [quantizeSchwartzValue_congr_left (b := 0) (hK x hx), quantizeSchwartzValue_zero_left,
      smul_zero, smul_zero]

/-- **Compactness of quantizations with compact spatial support.** For a symbol `a` of order `m`
with compact spatial support and a finite-dimensional complex Hilbert space `W`, the quantization
`Op(a)`, followed by the inclusion `H^{s - m} ⊆ H^r`, is a compact operator `H^s → H^r` for every
`r < s - m`. For `m < 0` and `r = s` this says that operators of negative order are compact
on `H^s`. -/
theorem isCompactOperator_inclusion_comp_quantizeSobolev [FiniteDimensional ℂ W]
    (ha : a.HasCompactSpatialSupport) {r s : ℝ} (h : r < s - m) :
    IsCompactOperator (BesselPotentialSpace.inclusion h.le ∘L a.quantizeSobolev ha s) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  -- A Schwartz function `φ` equal to `1` on `K`, built from a bump function around a ball
  -- containing `K`.
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  let χ : ContDiffBump (0 : CoordinateSpace n) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  obtain ⟨φ, hφχ⟩ : ∃ φ : 𝓢(CoordinateSpace n, ℂ), ∀ x, φ x = (χ x : ℂ) :=
    ⟨HasCompactSupport.toSchwartzMap (χ.hasCompactSupport.comp_left Complex.ofReal_zero)
      (Complex.ofRealCLM.contDiff.comp χ.contDiff), HasCompactSupport.toSchwartzMap_toFun _ _⟩
  have hφ : EqOn φ 1 K := fun x hx ↦ by
    have hχ : χ x = 1 := χ.one_of_mem_closedBall
      (Metric.closedBall_subset_closedBall (by simp only [χ]; linarith [le_max_left R 0]) (hR hx))
    rw [hφχ, hχ, Pi.one_apply, Complex.ofReal_one]
  rw [← smulLeftCLM_comp_quantizeSobolev ha s hKa hφ, ← ContinuousLinearMap.comp_assoc]
  exact (BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM φ h).comp_clm _

end Hilbert

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Compactness of quantizations with compact spatial support.** For a symbol `a` of order `m`
with compact spatial support between finite-dimensional complex normed spaces, and real orders
`r < s - m`, the quantization `Op(a)` extends from Schwartz functions to a compact operator
`H^s(ℝⁿ; V) → H^r(ℝⁿ; W)`.

As in `TauCeti.Symbol.exists_quantizeSobolev`, isomorphisms `e₁ : V ≃L[ℂ] ℂ^k`,
`e₂ : W ≃L[ℂ] ℂ^l` reduce this to the Hilbert-space statement
`TauCeti.Symbol.isCompactOperator_inclusion_comp_quantizeSobolev`, through
`TauCeti.Symbol.toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply`. -/
theorem exists_isCompactOperator_quantizeSobolev (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) {r s : ℝ} (h : r < s - m) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W), IsCompactOperator T ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let Φ := (e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ
  refine ⟨BesselPotentialSpace.postcomp _ _ 2 (e₂.symm : _ →L[ℂ] W) ∘L
    (BesselPotentialSpace.inclusion h.le ∘L (a.map Φ).quantizeSobolev (ha.map Φ) s) ∘L
      BesselPotentialSpace.postcomp _ s 2 (e₁ : V →L[ℂ] _),
    ((isCompactOperator_inclusion_comp_quantizeSobolev (ha.map Φ) h).comp_clm _).clm_comp _,
    toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂ fun u φ ↦ ?_⟩
  rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply]

/-- **Smoothing operators with compact spatial support are compact.** If `a` is a smoothing
symbol with compact spatial support between finite-dimensional complex normed spaces, its
quantization `Op(a)` extends from Schwartz functions to a compact operator
`H^s(ℝⁿ; V) → H^r(ℝⁿ; W)` for all real `s` and `r`. -/
theorem IsSmoothing.exists_isCompactOperator_quantizeSobolev {a : Symbol n V W m}
    (ha : a.IsSmoothing) (hc : a.HasCompactSpatialSupport) (s r : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{r}(CoordinateSpace n, W), IsCompactOperator T ∧
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.mp ha (s - r - 1)
  rw [← hb]
  exact b.exists_isCompactOperator_quantizeSobolev (hc.of_coefficient_eq hb) (by linarith)

end FiniteDimensional

end Symbol

/-! ### Compactness and the principal symbol -/

namespace ClassicalSymbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  (a : ClassicalSymbol n V W m)

open Filter Topology

/-- The test functions `χ_k(x) = t_k ^ r exp(-i ⟪x, t_k ξ⟫) ψ(x)`, `t_k = k + 1`, against which
the quantizations of wave packets of frequency `t_k ξ` are paired. -/
private noncomputable def testPacket (ψ : 𝓢(CoordinateSpace n, ℂ)) (ξ : CoordinateSpace n)
    (r : ℝ) (k : ℕ) : 𝓢(CoordinateSpace n, ℂ) :=
  ((((k : ℝ) + 1) ^ r : ℝ) : ℂ) • ψ.cutoffExponential 1 (-(((k : ℝ) + 1) • ξ)) (1 : ℂ)

/-- The `H^{-r'}` norm of `χ_k` grows at most like `t_k ^ (r - r')`. -/
private lemma exists_norm_toBesselPotentialSpaceCLM_testPacket_le (ψ : 𝓢(CoordinateSpace n, ℂ))
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) (r r' : ℝ) :
    ∃ C, ∀ k : ℕ, ‖SchwartzMap.toBesselPotentialSpaceCLM (-r') 2 (testPacket ψ ξ r k)‖ ≤
      C * ((k : ℝ) + 1) ^ (r - r') := by
  obtain ⟨C, hC⟩ := SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_cutoffExponential_smul_le
    (-r') ψ (neg_ne_zero.2 hξ) (1 : ℂ)
  refine ⟨C, fun k ↦ ?_⟩
  have ht : (1 : ℝ) ≤ k + 1 := by simp
  calc ‖SchwartzMap.toBesselPotentialSpaceCLM (-r') 2 (testPacket ψ ξ r k)‖
      ≤ ((k : ℝ) + 1) ^ r * (C * ((k : ℝ) + 1) ^ (-r')) := by
        simp only [testPacket, map_smul, norm_smul, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity), ← smul_neg]
        gcongr
        exact hC _ ht
    _ = C * ((k : ℝ) + 1) ^ (r - r') := by
        rw [sub_eq_add_neg, Real.rpow_add (by positivity)]
        ring

/-- Pairing with `χ_k` as a continuous linear functional on `H^r`. -/
private noncomputable def testFunctional (ψ : 𝓢(CoordinateSpace n, ℂ)) (ξ : CoordinateSpace n)
    (r : ℝ) (k : ℕ) : H^{r}(CoordinateSpace n, W) →L[ℂ] W :=
  PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) W (testPacket ψ ξ r k) ∘L
    BesselPotentialSpace.toDistrCLM (CoordinateSpace n) W r 2

private lemma testFunctional_apply (ψ : 𝓢(CoordinateSpace n, ℂ)) (ξ : CoordinateSpace n)
    (r : ℝ) (k : ℕ) (f : H^{r}(CoordinateSpace n, W)) :
    testFunctional ψ ξ r k f = f.toDistr (testPacket ψ ξ r k) := by
  simp only [testFunctional, ContinuousLinearMap.comp_apply,
    BesselPotentialSpace.toDistrCLM_apply, PointwiseConvergenceCLM.evalCLM_apply]
  -- The two sides apply the tempered distribution through different, definitionally equal
  -- coercions to functions: that of `PointwiseConvergenceCLM.coeLMₛₗ` and the native one.
  rfl

/-- The pairings with `χ_k` are uniformly bounded on `H^r`. -/
private lemma exists_norm_testFunctional_le (ψ : 𝓢(CoordinateSpace n, ℂ))
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) (r : ℝ) :
    ∃ C, ∀ k, ‖testFunctional (W := W) ψ ξ r k‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_toBesselPotentialSpaceCLM_testPacket_le ψ hξ r r
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine ⟨C, fun k ↦ (testFunctional ψ ξ r k).opNorm_le_bound hC0 fun f ↦ ?_⟩
  rw [testFunctional_apply, mul_comm C]
  refine (BesselPotentialSpace.norm_toDistr_apply_le 2 f _).trans ?_
  gcongr
  simpa using hC k

/-- **High-frequency test functions tend weakly to zero.** The pairings with `χ_k` tend to `0`
on every element of `H^r`. -/
private lemma tendsto_testFunctional (ψ : 𝓢(CoordinateSpace n, ℂ)) {ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) {r : ℝ} (f : H^{r}(CoordinateSpace n, W)) :
    Tendsto (fun k ↦ testFunctional ψ ξ r k f) atTop (𝓝 0) := by
  -- Since the pairings are uniformly bounded, it suffices to treat the dense set of Schwartz
  -- functions. These lie in `H^{r + 1}`, where `χ_k` tends to `0` in the dual norm.
  obtain ⟨C, hC⟩ := exists_norm_testFunctional_le (W := W) ψ hξ r
  have hequi : Equicontinuous ((↑) ∘ fun k ↦ testFunctional (W := W) ψ ξ r k) :=
    ((NormedSpace.equicontinuous_tfae _).out 6 2).1
      (⟨C, hC⟩ : ∃ C, ∀ k, ‖testFunctional (W := W) ψ ξ r k‖ ≤ C)
  refine (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) r
    ENNReal.ofNat_ne_top).induction_on
    f (hequi.isClosed_setOfPred_tendsto continuous_const) fun h ↦ ?_
  obtain ⟨C', hC'⟩ := exists_norm_toBesselPotentialSpaceCLM_testPacket_le ψ hξ r (r + 1)
  have hle (k : ℕ) : ‖testFunctional ψ ξ r k (SchwartzMap.toBesselPotentialSpaceCLM r 2 h)‖ ≤
      ‖SchwartzMap.toBesselPotentialSpaceCLM (r + 1) 2 h‖ * C' * ((k : ℝ) + 1)⁻¹ := by
    rw [testFunctional_apply, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      ← SchwartzMap.toDistr_toBesselPotentialSpaceCLM (s := r + 1) (p := 2), mul_assoc]
    refine (BesselPotentialSpace.norm_toDistr_apply_le 2 _ _).trans ?_
    gcongr
    refine (hC' k).trans_eq ?_
    rw [show r - (r + 1) = -1 by ring, Real.rpow_neg_one]
  refine squeeze_zero_norm hle ?_
  simpa using (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1
    tendsto_natCast_atTop_atTop)).const_mul
      (‖SchwartzMap.toBesselPotentialSpaceCLM (r + 1) 2 h‖ * C')

/-- **Compact quantizations have vanishing principal symbol, tested against wave packets.** If
`Op(a) : H^s → H^{s - m}` is compact, then for every nonzero frequency `ξ`, Schwartz amplitude
`φ`, compactly supported Schwartz function `ψ` and `v ∈ V`,
`∫ ψ(x) σ(a)(x, ξ) (φ(x) v) dx = 0`. -/
private theorem integral_smul_principal_eq_zero_of_isCompactOperator
    (ha : a.toSymbol.HasCompactSpatialSupport) {s : ℝ}
    (hT : IsCompactOperator (a.toSymbol.quantizeSobolev ha s)) {ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) (φ : 𝓢(CoordinateSpace n, ℂ)) {ψ : 𝓢(CoordinateSpace n, ℂ)}
    (hψ : HasCompactSupport ψ) (v : V) :
    ∫ x, ψ x • a.principal.coefficient (x, ξ) (φ x • v) = 0 := by
  -- The rescaled wave packets `u_k = t_k ^ (-s) (y ↦ exp(i ⟪y, t_k ξ⟫) φ(y) v)`, `t_k = k + 1`,
  -- are bounded in `H^s`, and the pairings with `χ_k` are uniformly bounded functionals on
  -- `H^{s - m}` tending to `0` pointwise. After composition with the compact `Op(a)` they tend
  -- to `0` in norm, so the pairings of `Op(a) u_k` with `χ_k` tend to `0`; but their limit is
  -- `∫ ψ(x) σ(a)(x, ξ) (φ(x) v) dx`.
  have ht : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  -- The rescaled wave packets, bounded in `H^s`.
  set u : ℕ → H^{s}(CoordinateSpace n, V) := fun k ↦ ((((k : ℝ) + 1) ^ (-s) : ℝ) : ℂ) •
    SchwartzMap.toBesselPotentialSpaceCLM s 2 (φ.cutoffExponential 1 (((k : ℝ) + 1) • ξ) v)
  obtain ⟨C, hC⟩ :=
    SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_cutoffExponential_smul_le s φ hξ v
  have hu (k : ℕ) : ‖u k‖ ≤ C := by
    have ht0 : 0 < (k : ℝ) + 1 := by positivity
    calc ‖u k‖ ≤ ((k : ℝ) + 1) ^ (-s) * (C * ((k : ℝ) + 1) ^ s) := by
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          gcongr
          exact hC _ (by simp)
      _ = C := by rw [Real.rpow_neg ht0.le]; field_simp
  -- After the compact operator, the pairings tend to `0` uniformly on bounded sets.
  obtain ⟨C', hC'⟩ := exists_norm_testFunctional_le (W := W) ψ hξ (s - m)
  have hcomp := ContinuousLinearMap.tendsto_comp_zero_of_isCompactOperator hC'
    (tendsto_testFunctional ψ hξ) _ hT
  have h0 : Tendsto (fun k ↦ testFunctional ψ ξ (s - m) k (a.toSymbol.quantizeSobolev ha s (u k)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k ↦ ((testFunctional ψ ξ (s - m) k ∘L _).le_opNorm (u k)).trans
      (mul_le_mul_of_nonneg_left (hu k) (norm_nonneg _))) ?_
    simpa using (hcomp.norm.mul_const C)
  -- The same pairings recover the principal symbol.
  refine tendsto_nhds_unique ?_ h0
  refine ((a.tendsto_integral_smul_quantizeSchwartzValue_cutoffExponential hξ φ hψ v).comp
    ht).congr fun k ↦ ?_
  have hts : ((((k : ℝ) + 1) ^ (-s) : ℝ) : ℂ) * ((((k : ℝ) + 1) ^ (s - m) : ℝ) : ℂ) =
      ((((k : ℝ) + 1) ^ (-m) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
    ring_nf
  simp only [Function.comp_apply, testFunctional_apply, testPacket, u, map_smul,
    Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply, smul_smul]
  -- The scalars combine as `t ^ (-s) * t ^ (s - m) = t ^ (-m)`.
  rw [hts, Complex.coe_smul]

/-- **Compact quantizations have vanishing principal symbol.** If a classical symbol `a` of order
`m` with compact spatial support quantizes to a compact operator `Op(a) : H^s → H^{s - m}` for
some real `s`, then its principal symbol vanishes, so `a` has order `m - 1`
(`TauCeti.ClassicalSymbol.principal_eq_zero_iff_exists_inclusion`). -/
theorem principal_eq_zero_of_isCompactOperator (ha : a.toSymbol.HasCompactSpatialSupport) {s : ℝ}
    (hT : IsCompactOperator (a.toSymbol.quantizeSobolev ha s)) : a.principal = 0 := by
  refine HomogeneousSymbol.ext_of_ne_zero fun x₀ ξ hξ ↦ ContinuousLinearMap.ext fun v ↦ ?_
  rw [HomogeneousSymbol.coefficient_zero, Pi.zero_apply, zero_apply]
  -- A Schwartz amplitude `φ` equal to `1` near `x₀`.
  let b : ContDiffBump x₀ := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨φ, hφb⟩ : ∃ φ : 𝓢(CoordinateSpace n, ℂ), ∀ x, φ x = (b x : ℂ) :=
    ⟨HasCompactSupport.toSchwartzMap (b.hasCompactSupport.comp_left Complex.ofReal_zero)
      (Complex.ofRealCLM.contDiff.comp b.contDiff), HasCompactSupport.toSchwartzMap_toFun _ _⟩
  set g : CoordinateSpace n → W := fun x ↦ a.principal.coefficient (x, ξ) (φ x • v)
  have hσ : Continuous fun x ↦ a.principal.coefficient (x, ξ) :=
    a.principal.continuousOn_coefficient.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ ↦ hξ
  have hg : Continuous g := hσ.clm_apply (φ.continuous.smul continuous_const)
  -- `g` integrates to zero against every smooth compactly supported function, so it vanishes.
  have hae : ∀ᵐ x, g x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hg.locallyIntegrable fun ρ hρ hρc ↦ ?_
    have hψ : HasCompactSupport (fun x ↦ (ρ x : ℂ)) := hρc.comp_left Complex.ofReal_zero
    let ψ : 𝓢(CoordinateSpace n, ℂ) := hψ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hρ)
    have hψe : ⇑ψ = fun x ↦ (ρ x : ℂ) := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have h := integral_smul_principal_eq_zero_of_isCompactOperator a ha hT hξ φ (ψ := ψ)
      (by rw [hψe]; exact hψ) v
    rw [hψe] at h
    simp only [Complex.coe_smul] at h
    exact h
  have hg0 : g = 0 := (hg.ae_eq_iff_eq volume continuous_const).1 hae
  simpa [g, hφb, b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)] using
    congrFun hg0 x₀

/-- **Symbols of lower order give compact quantizations.** If the principal symbol of a classical
symbol `a` of order `m` with compact spatial support vanishes, then `a` has order `m - 1`, so
`Op(a) : H^s → H^{s - m}` is compact for every real `s`, for a finite-dimensional `W`. -/
theorem isCompactOperator_quantizeSobolev_of_principal_eq_zero [FiniteDimensional ℂ W]
    (ha : a.toSymbol.HasCompactSpatialSupport) (s : ℝ) (h : a.principal = 0) :
    IsCompactOperator (a.toSymbol.quantizeSobolev ha s) := by
  obtain ⟨b, hab⟩ := (principal_eq_zero_iff_exists_inclusion a).1 h
  have hcoef : a.toSymbol.coefficient = b.toSymbol.coefficient := by
    rw [← hab, toSymbol_inclusion, Symbol.coefficient_inclusion]
  have hb : b.toSymbol.HasCompactSpatialSupport := ha.of_coefficient_eq hcoef.symm
  have hr : s - m < s - (m - 1) := by linarith
  -- `Op(a)` is `Op(b) : H^s → H^{s - (m - 1)}` followed by the inclusion into `H^{s - m}`.
  have heq : a.toSymbol.quantizeSobolev ha s =
      BesselPotentialSpace.inclusion hr.le ∘L b.toSymbol.quantizeSobolev hb s := by
    refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
      BesselPotentialSpace.ext ?_
    rw [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion]
    exact Symbol.toDistr_quantizeSobolev_congr hcoef ha hb rfl
  rw [heq]
  exact b.toSymbol.isCompactOperator_inclusion_comp_quantizeSobolev hb hr

/-- **Compactness of quantizations and the principal symbol.** A classical symbol `a` of order `m`
on `ℝⁿ` with compact spatial support, with values in operators from a complex Hilbert space `V` to a
finite-dimensional one `W`, quantizes to a compact operator `Op(a) : H^s → H^{s - m}` if and only if
its principal symbol vanishes. In particular this does not depend on `s`. -/
theorem isCompactOperator_quantizeSobolev_iff [FiniteDimensional ℂ W]
    (ha : a.toSymbol.HasCompactSpatialSupport) (s : ℝ) :
    IsCompactOperator (a.toSymbol.quantizeSobolev ha s) ↔ a.principal = 0 :=
  ⟨a.principal_eq_zero_of_isCompactOperator ha,
    a.isCompactOperator_quantizeSobolev_of_principal_eq_zero ha s⟩

end ClassicalSymbol

end TauCeti
