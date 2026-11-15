/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.LineDeriv
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Pseudodifferential.EllipticRegularity
import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered

/-!
# Local elliptic regularity of distributions

Let `P = ∑ i ∈ t, c i g i ∂^{m i}` be a linear differential operator of order at most `k` on `ℝᵈ`,
with smooth real coefficient functions `g i`, complex constants `c i` and iterated derivatives
`∂^{m i}` of orders `n i ≤ k`, acting on the complex distributions on an open set `Ω ⊆ ℝᵈ`. It is
*elliptic* at a point `y` when its principal symbol, the polynomial
`∑ i ∈ t with n i = k, c i g i(y) ∏ j ⟪ξ, m i j⟫` made of its summands of order exactly `k`, has
no zero `ξ ≠ 0`. This file proves **local elliptic regularity** for distributions: if `P` is
elliptic at `x` and `P T` is `H^s` near `x`, then `T` is `H^(s + k)` near `x`
(`Distribution.IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp`). Since `P` maps
`H^(s + k)_loc` to `H^s_loc`
(`Distribution.IsLocallySobolevAt.sum_smul_smulLeftCLM_iteratedLineDerivOp`), an operator
elliptic on `Ω` shifts the `H^s` singular support exactly by its order:
`singsupp_s(P T) = singsupp_(s + k)(T)`
(`Distribution.sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_eq`).

The pseudodifferential input is the interior elliptic regularity on Bessel-potential spaces,
`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM`, applied to the cut-off distribution
`φ T ∈ H^r` (`Distribution.cutoffTempered`). Its Bessel-potential form needs the action of a
differential operator with coefficients of temperate growth on `H^r`, which is the differential
operator applied to tempered distributions
(`TauCeti.ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol`).

## Proof outline

Ellipticity is an open condition, by homogeneity of the principal symbol and compactness of the
unit sphere. Choose cutoffs `ψ ≺ χ ≺ φ` near `x`, each equal to `1` near the support of the
previous one, with `ψ x ≠ 0`, inside a ball on which `P` is elliptic and `P T` is `H^s`. The
tempered distribution `u = φ T` lies in some `H^r`. Near the support of `χ` the cutoff `φ` is `1`,
so `χ P T = ∑ i, c i (χ g i) ∂^{m i} u`
(`Distribution.cutoffTempered_sum_smul_smulLeftCLM_iteratedLineDerivOp`): this is the quantization
`Op(p) u` of the classical symbol `p` of the differential operator with the compactly supported
coefficients `c i χ g i`, and it lies in `H^s`.

The parametrix theorem needs a symbol elliptic at all positions which agrees with `p` near the
support of `ψ`. It is obtained by freezing the coefficients outside the ball: with a cutoff `ρ`
supported in the ball and equal to `1` near the support of `ψ`, the map
`γ y = x + ρ(y) (y - x)` takes values in the ball, is the identity near the support of `ψ` and is
constant equal to `x` outside the ball, and the differential operator with the coefficients
`c i g i ∘ γ` is elliptic above some radius uniformly in the position. Hence `ψ u = ψ T` lies in
`H^(s + k)`.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.29.
-/

public section

noncomputable section

open Filter Metric Set TopologicalSpace TestFunction
open scoped ContDiff Distributions LineDeriv RealInnerProductSpace SchwartzMap Topology
  BesselPotentialSpace

/-! ### Differential operators on Bessel-potential spaces -/

namespace TauCeti

namespace ClassicalSymbol

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {ι : Type*} {k : ι → ℕ}

/-- **Differential operators on Bessel-potential spaces.** For scalar coefficients `β i` of
temperate growth, the extension `H^r → H^(r - m)` of the quantization of the classical symbol of
the differential operator `u ↦ ∑ i ∈ s, β i ∂^{v i} u` is that differential operator applied to
tempered distributions. -/
theorem toDistr_quantizeSobolev_ofDifferentialSymbol (m : ℕ) (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) {β : ι → CoordinateSpace n → ℂ}
    (hβ : ∀ i ∈ s, (β i).HasTemperateGrowth) (hk : ∀ i ∈ s, k i ≤ m)
    (hp : (ofDifferentialSymbol m s v (fun i x ↦ β i x • ContinuousLinearMap.id ℂ V)
      (fun i hi ↦ (hβ i hi).1.smul contDiff_const) hk).toSymbol.HasCompactSpatialSupport)
    (r : ℝ) (u : H^{r}(CoordinateSpace n, V)) :
    ((ofDifferentialSymbol m s v (fun i x ↦ β i x • ContinuousLinearMap.id ℂ V)
      (fun i hi ↦ (hβ i hi).1.smul contDiff_const) hk).toSymbol.quantizeSobolev hp r u).toDistr =
      ∑ i ∈ s, TemperedDistribution.smulLeftCLM V (β i) (∂^{v i} u.toDistr) := by
  set p := (ofDifferentialSymbol m s v (fun i x ↦ β i x • ContinuousLinearMap.id ℂ V)
    (fun i hi ↦ (hβ i hi).1.smul contDiff_const) hk).toSymbol
  -- Both sides are continuous in `u` and agree on the dense subspace of Schwartz functions.
  have hL : Continuous fun u : H^{r}(CoordinateSpace n, V) ↦ (p.quantizeSobolev hp r u).toDistr :=
    BesselPotentialSpace.continuous_toDistr.comp (p.quantizeSobolev hp r).continuous
  have hR : Continuous fun u : H^{r}(CoordinateSpace n, V) ↦
      ∑ i ∈ s, TemperedDistribution.smulLeftCLM V (β i) (∂^{v i} u.toDistr) :=
    continuous_finsetSum _ fun i _ ↦ (TemperedDistribution.smulLeftCLM V (β i)).continuous.comp
      ((LineDeriv.continuous_iteratedLineDerivOp (v i)).comp
        BesselPotentialSpace.continuous_toDistr)
  refine congrFun ((SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) r
    ENNReal.ofNat_ne_top).equalizer hL hR (funext fun f ↦ ?_)) u
  -- On a Schwartz function both sides are the tempered distribution of `∑ i, β i ∂^{v i} f`.
  have hf : ∑ i ∈ s, TemperedDistribution.smulLeftCLM V (β i) (∂^{v i} (f : 𝓢'(_, V))) =
      ((∑ i ∈ s, SchwartzMap.smulLeftCLM V (β i) (∂^{v i} f) : 𝓢(_, V)) : 𝓢'(_, V)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq,
      TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq]
  simp only [Function.comp_apply, SchwartzMap.toDistr_toBesselPotentialSpaceCLM]
  rw [hf]
  ext φ
  rw [Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    SchwartzMap.coe_apply]
  refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [p, quantizeSchwartzValue_ofDifferentialSymbol, _root_.sum_apply,
    _root_.smul_apply, ContinuousLinearMap.id_apply]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ by rw [SchwartzMap.smulLeftCLM_apply_apply (hβ i hi)]

end ClassicalSymbol

end TauCeti

/-! ### Local elliptic regularity -/

namespace Distribution

open TauCeti

variable {d : ℕ} {ι : Type*}

/-- The differential symbol of the summands of order `k` of a differential operator with scalar
coefficients `b i` is `i^k` times their geometric polynomial symbol. -/
private theorem differentialSymbol_filter_smul_id (t : Finset ι) {n : ι → ℕ}
    (m : ∀ i, Fin (n i) → CoordinateSpace d) (k : ℕ) (b : ι → CoordinateSpace d → ℂ)
    (y ξ : CoordinateSpace d) :
    differentialSymbol {i ∈ t | n i = k} m (fun i y ↦ b i y • ContinuousLinearMap.id ℂ ℂ) (y, ξ) =
      (Complex.I ^ k * ∑ i ∈ t with n i = k, b i y * ∏ j, (⟪ξ, m i j⟫ : ℂ)) •
        ContinuousLinearMap.id ℂ ℂ := by
  refine ContinuousLinearMap.ext_ring ?_
  simp only [differentialSymbol_eq_sum_pow_mul, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [(Finset.mem_filter.1 hi).2]
  ring

/-- **Freezing the coefficients outside a ball.** Let the differential operator with smooth scalar
coefficients `b i` be elliptic at every point of the ball `B(x, ε)`, and let `K ⊆ B(x, ε)` be
compact. Then some symbol elliptic above a radius, with bounds uniform in the position, agrees
with the symbol of the operator near `K`: the symbol of the operator with the coefficients
`b i ∘ γ`, for a smooth map `γ` into the ball which is the identity near `K` and constant outside
the ball. -/
private theorem exists_isEllipticAbove_eventually_coefficient_eq {t : Finset ι} {n : ι → ℕ}
    (m : ∀ i, Fin (n i) → CoordinateSpace d) {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k)
    {b : ι → CoordinateSpace d → ℂ} (hb : ∀ i, ContDiff ℝ ∞ (b i)) {x : CoordinateSpace d}
    {ε : ℝ} (hε : 0 < ε)
    (hell : ∀ y ∈ ball x ε, ∀ ξ, ξ ≠ 0 → ∑ i ∈ t with n i = k, b i y * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0)
    {K : Set (CoordinateSpace d)} (hK : IsCompact K) (hKε : K ⊆ ball x ε) :
    ∃ (a : Symbol d ℂ ℂ k) (R : ℝ), a.IsEllipticAbove R ∧ ∀ᶠ y in 𝓝ˢ K, ∀ ξ,
      a.coefficient (y, ξ) =
        differentialSymbol t m (fun i y ↦ b i y • ContinuousLinearMap.id ℂ ℂ) (y, ξ) := by
  -- The map `γ y = x + ρ(y) (y - x)`, for a cutoff `ρ` equal to `1` near `K`.
  obtain ⟨ρ, hρ, hρ01, hρ1, -, hρW⟩ := hK.exists_contDiff_cutoff isOpen_ball hKε
  set γ : CoordinateSpace d → CoordinateSpace d := fun y ↦ x + ρ y • (y - x)
  have hγ : ContDiff ℝ ∞ γ := contDiff_const.add (hρ.smul (contDiff_id.sub contDiff_const))
  have hρ0 (y : CoordinateSpace d) (hy : y ∉ ball x ε) : ρ y = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hy (hρW h)
  have hγε (y : CoordinateSpace d) : γ y ∈ ball x ε := by
    by_cases hy : y ∈ ball x ε
    · rw [mem_ball, dist_eq_norm] at hy ⊢
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hρ01 ⟨y, rfl⟩).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hρ01 ⟨y, rfl⟩).2).trans_lt hy
    · simpa [γ, hρ0 y hy] using hε
  -- The operator with the coefficients `b i ∘ γ` is elliptic.
  set a := ClassicalSymbol.ofDifferentialSymbol k t m
    (fun i y ↦ b i (γ y) • ContinuousLinearMap.id ℂ ℂ)
    (fun i _ ↦ ((hb i).comp hγ).smul contDiff_const) hk
  have ha : a.IsElliptic := (ClassicalSymbol.isElliptic_ofDifferentialSymbol_iff ..).2
    fun y ξ hξ ↦ by
      rw [differentialSymbol_filter_smul_id t m k (fun i y ↦ b i (γ y)),
        ContinuousLinearMap.isInvertible_smul_iff
          (mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (hell _ (hγε y) ξ hξ))]
      simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ ℂ)
  obtain ⟨R, C, h⟩ := ha.exists_isInvertible_and_norm_inverse_le (isCompact_closedBall x ε)
  refine ⟨a.toSymbol, R, Symbol.isEllipticAbove_iff.2 fun _ _ ↦ ⟨C, fun y _ ξ hξ ↦ ?_⟩, ?_⟩
  · by_cases hy : y ∈ closedBall x ε
    · exact h y hy ξ hξ
    -- Outside the closed ball the coefficients are frozen at their values at `x`.
    have hyx : a.toSymbol.coefficient (y, ξ) = a.toSymbol.coefficient (x, ξ) := by
      simp [a, γ, differentialSymbol_def, hρ0 y fun h ↦ hy (ball_subset_closedBall h)]
    rw [hyx]
    exact h x (mem_closedBall_self hε.le) ξ hξ
  · filter_upwards [subset_interior_iff_mem_nhdsSet.1 hρ1] with y hy ξ
    simp [a, γ, differentialSymbol_def, show ρ y = 1 from hy]

/-- The principal symbol `∑ i ∈ t with n i = k, b i y ∏ j ⟪ξ, m i j⟫` is homogeneous of degree `k`
in the frequency. -/
private theorem sum_filter_mul_prod_inner_smul (t : Finset ι) {n : ι → ℕ}
    (m : ∀ i, Fin (n i) → CoordinateSpace d) (k : ℕ) (b : ι → CoordinateSpace d → ℂ)
    (y ξ : CoordinateSpace d) (r : ℝ) :
    ∑ i ∈ t with n i = k, b i y * ∏ j, (⟪r • ξ, m i j⟫ : ℂ) =
      (r : ℂ) ^ k * ∑ i ∈ t with n i = k, b i y * ∏ j, (⟪ξ, m i j⟫ : ℂ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [real_inner_smul_left, Complex.ofReal_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, (Finset.mem_filter.1 hi).2]
  ring

/-- **Ellipticity is an open condition.** If the principal symbol has no zero `ξ ≠ 0` at `x`, the
same holds at every point near `x`: by homogeneity it suffices to consider the compact unit
sphere. -/
private theorem eventually_forall_sum_filter_mul_prod_inner_ne_zero (t : Finset ι) {n : ι → ℕ}
    (m : ∀ i, Fin (n i) → CoordinateSpace d) (k : ℕ) {b : ι → CoordinateSpace d → ℂ}
    (hb : ∀ i, Continuous (b i)) {x : CoordinateSpace d}
    (hx : ∀ ξ, ξ ≠ 0 → ∑ i ∈ t with n i = k, b i x * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∀ ξ, ξ ≠ 0 → ∑ i ∈ t with n i = k, b i y * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0 := by
  have hc : Continuous fun q : CoordinateSpace d × CoordinateSpace d ↦
      ∑ i ∈ t with n i = k, b i q.1 * ∏ j, (⟪q.2, m i j⟫ : ℂ) := by
    fun_prop
  have h := (isCompact_sphere (0 : CoordinateSpace d) 1).eventually_forall_of_forall_eventually
    (x₀ := x) (P := fun y ξ ↦ ∑ i ∈ t with n i = k, b i y * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0)
    fun ξ hξ ↦ hc.continuousAt.eventually_ne (hx ξ (ne_of_mem_sphere hξ one_ne_zero))
  filter_upwards [h] with y hy ξ hξ
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
  rw [← smul_inv_smul₀ hn ξ, sum_filter_mul_prod_inner_smul]
  refine mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hn)) (hy _ ?_)
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]

/-- **Local elliptic regularity on Bessel-potential spaces.** Let `φ = 1` on the supports of `χ`
and `ψ`, let `χ = 1` near the support of `ψ` and `χ P T ∈ H^s`, and let a symbol `a` elliptic above
some radius agree with the symbol of `P` near the support of `ψ`. Then `ψ T ∈ H^(s + k)`. -/
private theorem memSobolev_cutoffTempered_of_isEllipticAbove {Ω : Opens (CoordinateSpace d)}
    (T : 𝓓'(Ω, ℂ)) {s : ℝ} {t : Finset ι} {c : ι → ℂ} {g : ι → CoordinateSpace d → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {n : ι → ℕ} {m : ∀ i, Fin (n i) → CoordinateSpace d} {k : ℕ}
    (hk : ∀ i ∈ t, n i ≤ k) {ψ χ φ : 𝓓(Ω, ℂ)} (hφχ : EqOn φ 1 (tsupport χ))
    (hφψ : EqOn φ 1 (tsupport ψ)) (hχψ : ∀ᶠ y in 𝓝ˢ (tsupport ψ), χ y = 1)
    (hPχ : TemperedDistribution.MemSobolev s 2
      ((∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).cutoffTempered χ))
    {a : Symbol d ℂ ℂ k} {R : ℝ} (ha : a.IsEllipticAbove R)
    (haP : ∀ᶠ y in 𝓝ˢ (tsupport ψ), ∀ ξ, a.coefficient (y, ξ) =
      differentialSymbol t m (fun i y ↦ (c i * g i y) • ContinuousLinearMap.id ℂ ℂ) (y, ξ)) :
    TemperedDistribution.MemSobolev (s + k) 2 (T.cutoffTempered ψ) := by
  -- The cut-off distribution `u = φ T` lies in some `H^r₀`.
  obtain ⟨r₀, hS⟩ := T.exists_memSobolev_cutoffTempered φ
  set u := hS.toBesselPotentialSpace
  have hu : u.toDistr = T.cutoffTempered φ := hS.toBesselPotentialSpace_toDistr
  -- The localized symbol `p` with the compactly supported coefficients `c i g i χ`, and
  -- `Op(p) u = χ P T ∈ H^s`.
  set θ : ι → 𝓓(Ω, ℂ) := fun i ↦ c i • TestFunction.smulLeftCLM (hg i) χ
  have hβ : ∀ i ∈ t, (θ i : CoordinateSpace d → ℂ).HasTemperateGrowth := fun i _ ↦
    (θ i).hasCompactSupport.hasTemperateGrowth (θ i).contDiff
  set p := (ClassicalSymbol.ofDifferentialSymbol k t m
    (fun i y ↦ θ i y • ContinuousLinearMap.id ℂ ℂ) (fun i hi ↦ (hβ i hi).1.smul contDiff_const)
    hk).toSymbol
  have hp : p.HasCompactSpatialSupport :=
    ClassicalSymbol.hasCompactSpatialSupport_toSymbol_ofDifferentialSymbol _ _ _ _ _ _
      fun i _ ↦ (θ i).hasCompactSupport.smul_right
  have hpu : (p.quantizeSobolev hp r₀ u).toDistr.MemSobolev (s + k - k) 2 := by
    rwa [ClassicalSymbol.toDistr_quantizeSobolev_ofDifferentialSymbol (hβ := hβ), hu,
      add_sub_cancel_right, ← cutoffTempered_sum_smul_smulLeftCLM_iteratedLineDerivOp T hφχ]
  -- Near the support of `ψ`, where `χ = 1`, the symbol `p` agrees with `a`.
  set ψS : 𝓢(CoordinateSpace d, ℂ) := ψ.hasCompactSupport.toSchwartzMap ψ.contDiff
  have hψS : (ψS : CoordinateSpace d → ℂ) = ψ := rfl
  have hap : ∀ᶠ y in 𝓝ˢ (tsupport ψS), ∀ ξ, p.coefficient (y, ξ) = a.coefficient (y, ξ) := by
    rw [hψS]
    filter_upwards [hχψ.and haP] with y hy ξ
    rw [hy.2 ξ]
    simp [p, θ, differentialSymbol_def, hy.1, TestFunction.smulLeftCLM_apply]
  have key := ha.memSobolev_smulLeftCLM hp (hψS ▸ ψ.hasCompactSupport) hap hpu
  -- `ψ u = ψ T`, since `φ = 1` on the support of `ψ`.
  rwa [BesselPotentialSpace.toDistr_smulLeftCLM, hu, hψS,
    smulLeftCLM_cutoffTempered T φ (ψ.hasCompactSupport.hasTemperateGrowth ψ.contDiff)
      (θ := ψ) fun y ↦ ?_] at key
  by_cases hy : y ∈ tsupport ψ
  · rw [hφψ hy, Pi.one_apply, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- **Local elliptic regularity.** Let `P = ∑ i ∈ t, c i g i ∂^{m i}` be a differential operator of
order at most `k` on `ℝᵈ`, with smooth real coefficients `g i`, complex constants `c i` and
iterated derivatives `∂^{m i}` of orders `n i ≤ k`, which is elliptic at `x`: its principal
symbol `∑ i ∈ t with n i = k, c i g i(x) ∏ j ⟪ξ, m i j⟫` vanishes at no `ξ ≠ 0`. If `P T` is
`H^s` near `x`, then `T` is `H^(s + k)` near `x`. -/
theorem IsLocallySobolevAt.of_sum_smul_smulLeftCLM_iteratedLineDerivOp
    {Ω : Opens (CoordinateSpace d)} {T : 𝓓'(Ω, ℂ)} {x : CoordinateSpace d} {s : ℝ}
    {t : Finset ι} {c : ι → ℂ} {g : ι → CoordinateSpace d → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i))
    {n : ι → ℕ} {m : ∀ i, Fin (n i) → CoordinateSpace d} {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k)
    (hP : ∀ ξ, ξ ≠ 0 → ∑ i ∈ t with n i = k, c i * g i x * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0)
    (h : (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).IsLocallySobolevAt s x) :
    T.IsLocallySobolevAt (s + k) x := by
  have hb (i : ι) : ContDiff ℝ ∞ fun y ↦ c i * g i y :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hg i))
  -- A ball `B(x, ε)` inside `Ω` on which `P` is elliptic and `P T` is `H^s`.
  obtain ⟨U, hU, hPU⟩ := h.exists_nhds_forall_memSobolev_cutoffTempered
  obtain ⟨ε, hε, hεU⟩ :=
    Metric.mem_nhds_iff.1 (inter_mem (inter_mem hU
      (eventually_forall_sum_filter_mul_prod_inner_ne_zero t m k (fun i ↦ (hb i).continuous) hP))
      (Ω.isOpen.mem_nhds h.mem))
  set r := ε / 5 with hr
  have hr0 : 0 < r := by positivity
  have hWΩ (a : ℝ) (ha : a ≤ ε) : ball x a ⊆ Ω :=
    (ball_subset_ball ha).trans fun y hy ↦ (hεU hy).2
  -- Cutoffs `ψ ≺ χ ≺ φ`, each equal to `1` near the support of the previous one.
  obtain ⟨ψ, hψ1, hψW⟩ := exists_eventually_eq_tsupport_subset (n := ⊤) (W := ball x r)
    isCompact_singleton isOpen_ball (singleton_subset_iff.2 (mem_ball_self hr0))
    (hWΩ r (by linarith)) (1 : ℂ)
  obtain ⟨χ, hχ1, hχW⟩ := exists_eventually_eq_tsupport_subset (n := ⊤) (W := ball x (2 * r))
    (isCompact_closedBall x r) isOpen_ball (closedBall_subset_ball (by linarith))
    (hWΩ (2 * r) (by linarith)) (1 : ℂ)
  obtain ⟨φ, hφ1, -⟩ := exists_eventually_eq_tsupport_subset (n := ⊤) (W := ball x (3 * r))
    (isCompact_closedBall x (2 * r)) isOpen_ball (closedBall_subset_ball (by linarith))
    (hWΩ (3 * r) (by linarith)) (1 : ℂ)
  have hψr : tsupport ψ ⊆ closedBall x r := hψW.trans ball_subset_closedBall
  have hφχ : EqOn φ 1 (tsupport χ) := fun y hy ↦
    hφ1.self_of_nhdsSet y (ball_subset_closedBall (hχW hy))
  have hφψ : EqOn φ 1 (tsupport ψ) := fun y hy ↦
    hφ1.self_of_nhdsSet y (closedBall_subset_closedBall (by linarith) (hψr hy))
  -- A symbol elliptic at all positions which agrees with that of `P` near `closedBall x r`.
  obtain ⟨a, R, ha, haP⟩ := exists_isEllipticAbove_eventually_coefficient_eq m hk hb hε
    (fun y hy ↦ (hεU hy).1.2) (isCompact_closedBall x r) (closedBall_subset_ball (by linarith))
  refine isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
    ⟨ψ, by simp [hψ1.self_of_nhdsSet x rfl], ?_⟩
  exact memSobolev_cutoffTempered_of_isEllipticAbove T hg hk hφχ hφψ (nhdsSet_mono hψr hχ1)
    (hPU χ (hχW.trans fun y hy ↦ (hεU (ball_subset_ball (by linarith) hy)).1.1)) ha
    (nhdsSet_mono hψr haP)

/-- **Elliptic operators shift the `H^s` singular support exactly by their order.** For a
differential operator `P = ∑ i ∈ t, c i g i ∂^{m i}` of order at most `k` with smooth real
coefficients, elliptic at every point of `Ω`, `singsupp_s(P T) = singsupp_(s + k)(T)`. -/
theorem sobolevSingularSupport_sum_smul_smulLeftCLM_iteratedLineDerivOp_eq
    {Ω : Opens (CoordinateSpace d)} (s : ℝ) (t : Finset ι) (c : ι → ℂ)
    {g : ι → CoordinateSpace d → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) {n : ι → ℕ}
    (m : ∀ i, Fin (n i) → CoordinateSpace d) {k : ℕ} (hk : ∀ i ∈ t, n i ≤ k)
    (hP : ∀ y ∈ Ω, ∀ ξ, ξ ≠ 0 → ∑ i ∈ t with n i = k, c i * g i y * ∏ j, (⟪ξ, m i j⟫ : ℂ) ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ t, c i • Distribution.smulLeftCLM (hg i) (∂^{m i} T)).sobolevSingularSupport s =
      T.sobolevSingularSupport (s + k) := by
  ext y
  simp only [mem_sobolevSingularSupport_iff, and_congr_right_iff]
  refine fun hy ↦ not_congr ⟨fun h ↦ h.of_sum_smul_smulLeftCLM_iteratedLineDerivOp hg hk
    (hP y hy), fun h ↦ ?_⟩
  simpa only [add_sub_cancel_right] using h.sum_smul_smulLeftCLM_iteratedLineDerivOp t c hg m hk

end Distribution
