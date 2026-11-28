/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.InteriorRegularity
public import TauCeti.Analysis.Sobolev.BesselPotential.SupercriticalMultiplication
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Holder.Iterated
import TauCeti.Analysis.Sobolev.BesselPotential.Holder
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.MatrixMultiplier
import TauCeti.Analysis.Sobolev.BesselPotential.SobolevEmbedding
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Regularity of solutions of quadratic elliptic systems in dimension four

Let `D = Op(c)` be a pseudodifferential operator of order `1` on `ℝ⁴`, acting on functions with
values in a finite-dimensional complex Hilbert space `V`, and elliptic on an open set `U` in the
sense that on `U` its symbol agrees with a symbol `a` elliptic above some radius
(`TauCeti.Symbol.IsEllipticAbove`). The symbol `c` is asked to vanish at positions outside a
compact set, so that `Op(c)` acts on the Sobolev spaces `H^{s,p}`; on a bounded open set `U`, a
first-order elliptic system with smooth coefficients, cut off away from `U`, is of this kind. Let
`Q x : V × V → W` be real bilinear maps depending smoothly on the position `x`, as the chart
coefficients of a smooth fiberwise bilinear map do. This file proves that every solution
`f ∈ W^{1,3}(ℝ⁴; V)` of the quadratic equation

`D f = Q (f, f)` on `U`, where `Q (f, f) (x) = Q x (f x, f x)`,

is smooth on `U` (`TauCeti.Symbol.IsEllipticAbove.exists_contDiff_ae_eq_smul_of_eq_bilin`): for
every compactly supported Schwartz function `ψ` with support in `U`, the function `ψ f` lies in
every Sobolev space `H^{k,6}` (`TauCeti.Symbol.IsEllipticAbove.memSobolev_smulLeftCLM_of_eq_bilin`)
and agrees almost everywhere with a smooth function. The equation is imposed in the sense of
distributions on `U`, and `D f` is the image of `f ∈ H^{1,3}` under the bounded operator
`Op(c) : H^{1,3} → H^{0,3}` (`TauCeti.Symbol.quantizeUniformBesselPotentialSpace`).

The exponent `3` is below the dimension, so `W^{1,3}(ℝ⁴)` is not an algebra and `Q (f, f)` is a
priori only an `L^{3/2}` function. It is still subcritical for this equation (the critical space is
`W^{1,2}(ℝ⁴) ⊆ L^4`), so the Sobolev embedding into `L^{12}` starts a bootstrap with the exponents
`3 → 12 → 6`:

* the Sobolev embedding `H^{1,3}(ℝ⁴) ⊆ L^{12}` (`1 / 12 = 1 / 3 - 1 / 4`,
  `TemperedDistribution.MemSobolev.of_add_of_inv_eq`) puts `χ Q (f, f)` in `L^6`
  (`1 / 6 = 1 / 12 + 1 / 12`) for every compactly supported cutoff `χ`;
* interior elliptic regularity on `H^{s,6}`
  (`IsEllipticAbove.memSobolev_smulLeftCLM_of_memSobolev_quantizeUniformBesselPotentialSpace` in
  the namespace `TauCeti.Symbol`)
  then gives `ψ f ∈ H^{1,6}` for every cutoff `ψ` supported in `U`;
* since `6 > 4`, the space `H^{k,6}(ℝ⁴)`, `k ≥ 1`, is closed under bilinear products
  (`TemperedDistribution.MemSobolev.exists_memSobolev_bilin`), so `ψ f ∈ H^{k,6}` puts
  `ψ' Q (f, f)` in `H^{k,6}` for a smaller cutoff `ψ'` (writing `ψ' Q` in a real basis of the
  bilinear maps, with Schwartz coefficients), and elliptic regularity gains one derivative at
  each step;
* finally `H^{k + 2,6}(ℝ⁴) ⊆ C^k` (`TemperedDistribution.MemSobolev.exists_toLpTop_eq`).

Passing from the equation, an identity in `H^{0,3}`, to the regularity theorem on `H^{s,6}` uses
that `Op(c)` acts compatibly on the two scales
(`HasCompactSpatialSupport.toDistr_quantizeUniformBesselPotentialSpace_congr_exponent` in the
namespace `TauCeti.Symbol`).

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture II, (5.1)–(5.8) (the bootstrap for nonlinear elliptic equations).
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Theorem 4.12 (the Sobolev exponents).
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution Filter Set
open scoped ENNReal NNReal ContDiff SchwartzMap BesselPotentialSpace Topology

namespace TauCeti

namespace Symbol

local instance : Fact (1 ≤ ((3 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((6 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ((12 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [CompleteSpace W]

omit [FiniteDimensional ℂ V] in
/-- The Sobolev exponents of the bootstrap: `H^{1,3}(ℝ⁴) ⊆ L^{12}` and `H^{1,3}(ℝ⁴) ⊆ L^6`. -/
private theorem memSobolev_zero_twelve_and_six {f : 𝓢'(CoordinateSpace 4, V)}
    (hf : MemSobolev 1 (3 : ℝ≥0) f) :
    MemSobolev 0 (12 : ℝ≥0) f ∧ MemSobolev 0 (6 : ℝ≥0) f := by
  have hn : (Module.finrank ℝ (CoordinateSpace 4) : ℝ) = 4 := by simp
  refine ⟨MemSobolev.of_add_of_inv_eq (δ := 1) (p := 3) (q := 12) one_pos (by norm_num) ?_
      (by simpa using hf),
    MemSobolev.of_add_of_inv_eq (δ := 2 / 3) (p := 3) (q := 6) (by norm_num) (by norm_num) ?_
      ((by simpa using hf.of_le (by norm_num : (2 / 3 : ℝ) ≤ 1)))⟩ <;>
  · rw [hn]
    norm_num

variable {R : ℝ} {a c : Symbol 4 V W 1} {U : Set (CoordinateSpace 4)}
  {Q : CoordinateSpace 4 → V →L[ℝ] V →L[ℝ] W}
  {f : Lp V (3 : ℝ≥0) (volume : Measure (CoordinateSpace 4))}

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- **The localized right-hand side is in `L^6`.** For `f ∈ H^{1,3}`, a smooth family `Q` of
bilinear maps and a compactly supported cutoff `χ`, the function `χ Q (f, f)` is an `L^6`
function: `f ∈ L^{12}` and `χ Q` is bounded. -/
private theorem exists_lp_six_ae_eq (hQ : ContDiff ℝ ∞ Q)
    (hf : MemSobolev 1 (3 : ℝ≥0) (f : 𝓢'(CoordinateSpace 4, V))) {χ : 𝓢(CoordinateSpace 4, ℂ)}
    (hχ : HasCompactSupport χ) :
    ∃ q : Lp W (6 : ℝ≥0) (volume : Measure (CoordinateSpace 4)),
      q =ᵐ[volume] fun x ↦ χ x • Q x (f x) (f x) := by
  -- An `L^{12}` representative `g` of `f`.
  obtain ⟨g, hg⟩ := memSobolev_zero_iff.1 (memSobolev_zero_twelve_and_six hf).1
  have hfg : f =ᵐ[volume] g := Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.1 hg
  have h₁₂ : ((12 : ℝ≥0)⁻¹ + 12⁻¹ : ℝ≥0) = 6⁻¹ := by norm_num
  have : ENNReal.HolderTriple ((12 : ℝ≥0) : ℝ≥0∞) ((12 : ℝ≥0) : ℝ≥0∞) ((6 : ℝ≥0) : ℝ≥0∞) :=
    ⟨by exact_mod_cast h₁₂⟩
  have hg2 : MemLp (fun x ↦ ‖g x‖ * ‖g x‖) ((6 : ℝ≥0) : ℝ≥0∞) volume :=
    (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin _ (Lp.memLp g).norm (Lp.memLp g).norm
  -- `χ Q` is bounded by `M`.
  obtain ⟨C, hC⟩ := hχ.isCompact.exists_bound_of_continuousOn (f := Q) hQ.continuous.continuousOn
  set M := SchwartzMap.seminorm ℝ 0 0 χ * max C 0
  have hM (x) : ‖χ x‖ * ‖Q x‖ ≤ M := by
    by_cases hx : x ∈ tsupport χ
    · exact mul_le_mul (χ.norm_le_seminorm ℝ x) ((hC x hx).trans (le_max_left _ _))
        (norm_nonneg (Q x)) (apply_nonneg _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero, zero_mul]
      exact mul_nonneg (apply_nonneg _ _) (le_max_right _ _)
  have hmeas : AEStronglyMeasurable (fun x ↦ χ x • Q x (g x) (g x)) volume :=
    χ.continuous.aestronglyMeasurable.smul
      (((continuous_fst.clm_apply continuous_snd).clm_apply
        continuous_snd).comp_aestronglyMeasurable
          (hQ.continuous.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable g)))
  refine ⟨(hg2.of_le_mul (c := M) hmeas (.of_forall fun x ↦ ?_)).toLp _,
    (MemLp.coeFn_toLp _).trans ?_⟩
  · calc ‖χ x • Q x (g x) (g x)‖ ≤ ‖χ x‖ * (‖Q x‖ * ‖g x‖ * ‖g x‖) := by
          rw [norm_smul]
          gcongr
          exact (Q x).le_opNorm₂ _ _
      _ = ‖χ x‖ * ‖Q x‖ * ‖‖g x‖ * ‖g x‖‖ := by rw [norm_mul, norm_norm]; ring
      _ ≤ M * ‖‖g x‖ * ‖g x‖‖ := by
          gcongr
          exact hM x
  filter_upwards [hfg] with x hx
  rw [hx]

/-- **The localized equation on `H^{0,6}`.** If `Op(c) f = Q (f, f)` on `U`, then for a cutoff
`χ` supported in `U`, the operator with symbol `χ(x) c(x, ξ)` on `H^{0,6}` sends `f` to the `L^6`
function `χ Q (f, f)`. -/
private theorem toDistr_quantize_smulLeft_eq (hc : c.HasCompactSpatialSupport)
    (hf : MemSobolev 1 (3 : ℝ≥0) (f : 𝓢'(CoordinateSpace 4, V)))
    (heq : ∀ φ : 𝓢(CoordinateSpace 4, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (c.quantizeUniformBesselPotentialSpace hc.isUniform 1 (3 : ℝ≥0)
          hf.toBesselPotentialSpace).toDistr φ =
        ∫ x, φ x • Q x (f x) (f x))
    (hf6 : MemSobolev 0 (6 : ℝ≥0) (f : 𝓢'(CoordinateSpace 4, V))) {χ : 𝓢(CoordinateSpace 4, ℂ)}
    (hχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    {q : Lp W (6 : ℝ≥0) (volume : Measure (CoordinateSpace 4))}
    (hq : q =ᵐ[volume] fun x ↦ χ x • Q x (f x) (f x)) :
    ((smulLeft (χ.smooth ⊤) c).quantizeUniformBesselPotentialSpace
        (hc.smulLeft (χ.smooth ⊤)).isUniform 0 (6 : ℝ≥0) hf6.toBesselPotentialSpace).toDistr =
      (q : 𝓢'(CoordinateSpace 4, W)) := by
  rw [hc.toDistr_quantizeUniformBesselPotentialSpace_smulLeft _ χ.hasTemperateGrowth 0
    (by norm_num) ENNReal.coe_ne_top,
    ← hc.toDistr_quantizeUniformBesselPotentialSpace_congr_exponent hc rfl
      (by norm_num : (1 : ℝ≥0) < 3) (by norm_num : (1 : ℝ≥0) < 6)
      (u := hf.toBesselPotentialSpace)
      (by rw [MemSobolev.toBesselPotentialSpace_toDistr,
        MemSobolev.toBesselPotentialSpace_toDistr])]
  ext φ
  have hφ : HasCompactSupport (SchwartzMap.smulLeftCLM ℂ (χ : CoordinateSpace 4 → ℂ) φ) := by
    rw [SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth]
    exact hχ.smul_right
  have hφU : tsupport (SchwartzMap.smulLeftCLM ℂ (χ : CoordinateSpace 4 → ℂ) φ) ⊆ U := by
    rw [SchwartzMap.smulLeftCLM_apply χ.hasTemperateGrowth]
    exact (tsupport_smul_subset_left _ _).trans hχU
  rw [smulLeftCLM_apply_apply, heq _ hφ hφU, Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ?_
  filter_upwards [hq] with x hqx
  rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth, hqx, smul_eq_mul, mul_comm,
    mul_smul]

/-- **One step of the bootstrap.** If `χ Q (f, f) ∈ H^{k,6}` for every cutoff `χ` supported in
`U`, then `ψ f ∈ H^{k + 1,6}` for every cutoff `ψ` supported in `U`. -/
private theorem memSobolev_succ (ha : a.IsEllipticAbove R) (hc : c.HasCompactSpatialSupport)
    (hU : IsOpen U) (hca : ∀ x ∈ U, ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ))
    (hQ : ContDiff ℝ ∞ Q) (hf : MemSobolev 1 (3 : ℝ≥0) (f : 𝓢'(CoordinateSpace 4, V)))
    (heq : ∀ φ : 𝓢(CoordinateSpace 4, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (c.quantizeUniformBesselPotentialSpace hc.isUniform 1 (3 : ℝ≥0)
          hf.toBesselPotentialSpace).toDistr φ =
        ∫ x, φ x • Q x (f x) (f x))
    (hf6 : MemSobolev 0 (6 : ℝ≥0) (f : 𝓢'(CoordinateSpace 4, V))) {k : ℕ}
    (hk : ∀ χ : 𝓢(CoordinateSpace 4, ℂ), HasCompactSupport χ → tsupport χ ⊆ U →
      ∀ q : Lp W (6 : ℝ≥0) (volume : Measure (CoordinateSpace 4)),
        (q =ᵐ[volume] fun x ↦ χ x • Q x (f x) (f x)) →
        MemSobolev k (6 : ℝ≥0) (q : 𝓢'(CoordinateSpace 4, W)))
    {ψ : 𝓢(CoordinateSpace 4, ℂ)} (hψ : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    MemSobolev (k + 1 : ℕ) (6 : ℝ≥0)
      (smulLeftCLM V (ψ : CoordinateSpace 4 → ℂ) (f : 𝓢'(CoordinateSpace 4, V))) := by
  obtain ⟨χ, hχ, hχU, hχ1⟩ := hψ.isCompact.exists_schwartzMap_cutoff hU hψU
  obtain ⟨q, hq⟩ := exists_lp_six_ae_eq hQ hf hχ
  have h := ha.memSobolev_smulLeftCLM_of_memSobolev_quantizeUniformBesselPotentialSpace hψ
    (hc.smulLeft (χ.smooth ⊤)) ?_ (by norm_num) ENNReal.coe_ne_top hf6.toBesselPotentialSpace
    (s := k) (by rw [toDistr_quantize_smulLeft_eq hc hf heq hf6 hχ hχU hq]; exact hk χ hχ hχU q hq)
  · rwa [MemSobolev.toBesselPotentialSpace_toDistr, ← Nat.cast_succ] at h
  filter_upwards [hχ1, hU.mem_nhdsSet.2 hψU] with x hx hxU ξ
  rw [coefficient_smulLeft, hx, one_smul, hca x hxU ξ]

/-- **The right-hand side of the bootstrap.** If `ψ f ∈ H^{k,6}` for every cutoff `ψ` supported
in `U`, then `χ Q (f, f) ∈ H^{k,6}` for every cutoff `χ` supported in `U`. For `k = 0` this is
the `L^6` bound; for `k ≥ 1` it is the algebra property of `H^{k,6}` in dimension four, applied to
`ψ f` for a cutoff `ψ` equal to `1` near the support of `χ`, after writing `χ Q` in a real basis
of the bilinear maps with Schwartz coefficients. -/
private theorem memSobolev_bilin (hU : IsOpen U) (hQ : ContDiff ℝ ∞ Q) {k : ℕ}
    (hk : ∀ ψ : 𝓢(CoordinateSpace 4, ℂ), HasCompactSupport ψ → tsupport ψ ⊆ U →
      MemSobolev k (6 : ℝ≥0)
        (smulLeftCLM V (ψ : CoordinateSpace 4 → ℂ) (f : 𝓢'(CoordinateSpace 4, V))))
    {χ : 𝓢(CoordinateSpace 4, ℂ)} (hχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    {q : Lp W (6 : ℝ≥0) (volume : Measure (CoordinateSpace 4))}
    (hq : q =ᵐ[volume] fun x ↦ χ x • Q x (f x) (f x)) :
    MemSobolev k (6 : ℝ≥0) (q : 𝓢'(CoordinateSpace 4, W)) := by
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [Nat.cast_zero]
    exact memSobolev_zero_iff.2 ⟨q, rfl⟩
  obtain ⟨ψ, hψ, hψU, hψ1⟩ := hχ.isCompact.exists_schwartzMap_cutoff hU hχU
  -- `ψ f` is an `L^6` function `y` in `H^{k,6}`.
  obtain ⟨y, hy⟩ := memSobolev_zero_iff.1 ((hk ψ hψ hψU).of_le (Nat.cast_nonneg k))
  have hyS := hk ψ hψ hψU
  rw [hy] at hyS
  have hyf := (Lp.toTemperedDistribution_eq_smulLeftCLM_iff ψ.hasTemperateGrowth y f).1 hy.symm
  -- The coefficients of `Q` in a real basis `b`, times `χ`, are Schwartz functions `ψᵢ`.
  set b := Module.finBasis ℝ (V →L[ℝ] V →L[ℝ] W)
  have hcoef (i) : ContDiff ℝ ∞ fun x ↦ χ x * (b.coord i (Q x) : ℂ) :=
    (χ.smooth ⊤).mul ((hQ.continuousLinearMap_comp
      (b.coord i).toContinuousLinearMap).continuousLinearMap_comp Complex.ofRealCLM)
  let ψi (i) : 𝓢(CoordinateSpace 4, ℂ) := hχ.mul_right.toSchwartzMap (hcoef i)
  -- The products `bᵢ (y, y)`, in `H^{k,6}` since `6 > 4`, and their products with `ψᵢ`.
  choose w hw hwS using fun i ↦ hyS.exists_memSobolev_bilin (by norm_num)
    (by rw [finrank_euclideanSpace_fin]; norm_num) hk0 (b i) hyS
  choose v hv using fun i ↦ Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le
    (.of_forall fun x ↦ (ψi i).norm_le_seminorm ℝ x) (w i)
  have hvw (i) := (Lp.toTemperedDistribution_eq_smulLeftCLM_iff (ψi i).hasTemperateGrowth (v i)
    (w i)).1 (hv i).1.symm
  -- Near the support of `χ`, `ψ = 1`, so `q = ∑ᵢ ψᵢ bᵢ (y, y)`.
  have hqv : q =ᵐ[volume] ⇑(∑ i, v i) := by
    filter_upwards [hq, hyf, Lp.coeFn_fun_finsetSum Finset.univ v, ae_all_iff.2 hvw,
      ae_all_iff.2 hw] with x hqx hyx hsx hvx hwx
    rw [hqx, hsx]
    simp only [hvx, hwx, ψi, HasCompactSupport.toSchwartzMap_toFun]
    by_cases hχx : χ x = 0
    · simp [hχx]
    have hψx : ψ x = 1 := hψ1.self_of_nhdsSet x (subset_tsupport _ hχx)
    conv_lhs => rw [← b.sum_repr (Q x)]
    simp only [hyx, hψx, one_smul, FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
      Pi.smul_apply, Pi.mul_apply, Finset.smul_sum, mul_smul, Complex.coe_smul,
      Module.Basis.coord_apply]
  rw [Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.2 hqv, Lp.toTemperedDistribution_sum]
  exact MemSobolev.sum fun i _ ↦ (hv i).1 ▸
    (hwS i).smulLeftCLM_schwartzMap (by norm_num) ENNReal.coe_ne_top (ψi i)

/-- **Sobolev regularity of solutions of quadratic first-order elliptic systems in dimension
four.** Let `Op(c)` be an operator of order `1` on `ℝ⁴` whose symbol `c`, with compact spatial
support, agrees on an open set `U` with a symbol `a` elliptic above some radius, and let `Q` be a
smooth family of real bilinear maps `Q x`. If `f ∈ W^{1,3}(ℝ⁴; V)` solves
`Op(c) f = Q (f, f)`, that is `Op(c) f (x) = Q x (f x, f x)`, in the sense of distributions on
`U`, then `ψ f ∈ H^{k,6}` for every `k` and every compactly supported Schwartz function `ψ` with
support in `U`. -/
theorem IsEllipticAbove.memSobolev_smulLeftCLM_of_eq_bilin (ha : a.IsEllipticAbove R)
    (hc : c.HasCompactSpatialSupport) (hU : IsOpen U)
    (hca : ∀ x ∈ U, ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ)) (hQ : ContDiff ℝ ∞ Q)
    (hf : MemSobolev 1 (3 : ℝ≥0) (f : 𝓢'(CoordinateSpace 4, V)))
    (heq : ∀ φ : 𝓢(CoordinateSpace 4, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (c.quantizeUniformBesselPotentialSpace hc.isUniform 1 (3 : ℝ≥0)
          hf.toBesselPotentialSpace).toDistr φ =
        ∫ x, φ x • Q x (f x) (f x))
    (k : ℕ) {ψ : 𝓢(CoordinateSpace 4, ℂ)} (hψ : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    MemSobolev k (6 : ℝ≥0)
      (smulLeftCLM V (ψ : CoordinateSpace 4 → ℂ) (f : 𝓢'(CoordinateSpace 4, V))) := by
  obtain ⟨-, hf6⟩ := memSobolev_zero_twelve_and_six hf
  induction k generalizing ψ with
  | zero =>
    exact MemSobolev.smulLeftCLM_schwartzMap (by norm_num) ENNReal.coe_ne_top ψ
      (by rw [Nat.cast_zero]; exact hf6)
  | succ k ih =>
    exact memSobolev_succ ha hc hU hca hQ hf heq hf6
      (fun χ hχ hχU _ hq ↦ memSobolev_bilin hU hQ (fun ψ' h₁ h₂ ↦ ih h₁ h₂) hχ hχU hq) hψ hψU

/-- **Smoothness of solutions of quadratic first-order elliptic systems in dimension four.** Let
`Op(c)` be an operator of order `1` on `ℝ⁴` whose symbol `c`, with compact spatial support, agrees
on an open set `U` with a symbol `a` elliptic above some radius, and let `Q` be a smooth family
of real bilinear maps `Q x`. If `f ∈ W^{1,3}(ℝ⁴; V)` solves `Op(c) f = Q (f, f)`, that is
`Op(c) f (x) = Q x (f x, f x)`, in the sense of distributions on `U`, then `f` is smooth on `U`:
for every compactly supported Schwartz function `ψ` with support in `U`, the function `ψ f`
agrees almost everywhere with a smooth function. -/
theorem IsEllipticAbove.exists_contDiff_ae_eq_smul_of_eq_bilin (ha : a.IsEllipticAbove R)
    (hc : c.HasCompactSpatialSupport) (hU : IsOpen U)
    (hca : ∀ x ∈ U, ∀ ξ, c.coefficient (x, ξ) = a.coefficient (x, ξ)) (hQ : ContDiff ℝ ∞ Q)
    (hf : MemSobolev 1 (3 : ℝ≥0) (f : 𝓢'(CoordinateSpace 4, V)))
    (heq : ∀ φ : 𝓢(CoordinateSpace 4, ℂ), HasCompactSupport φ → tsupport φ ⊆ U →
      (c.quantizeUniformBesselPotentialSpace hc.isUniform 1 (3 : ℝ≥0)
          hf.toBesselPotentialSpace).toDistr φ =
        ∫ x, φ x • Q x (f x) (f x))
    {ψ : 𝓢(CoordinateSpace 4, ℂ)} (hψ : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
    ∃ g : CoordinateSpace 4 → V, ContDiff ℝ ∞ g ∧ (fun x ↦ ψ x • f x) =ᵐ[volume] g := by
  set T := smulLeftCLM V (ψ : CoordinateSpace 4 → ℂ) (f : 𝓢'(CoordinateSpace 4, V))
  -- For each `k`, the element of `H^{k + 2,6}` gives a `C^k` representative of `ψ f`.
  have hk (k : ℕ) := (ha.memSobolev_smulLeftCLM_of_eq_bilin hc hU hca hQ hf heq (k + 2) hψ
    hψU).exists_toLpTop_eq k (α := 1 / 2) (by norm_num) (by norm_num)
    (by simp only [finrank_euclideanSpace_fin, ENNReal.coe_toReal]; push_cast; linarith)
  choose F hF using hk
  -- These representatives are all the same function, which is therefore `C^k` for every `k`.
  have hFk (k : ℕ) : (F k : CoordinateSpace 4 → V) = F 0 := by
    have := BoundedContinuousFunction.toTemperedDistribution_toLpTop_injective (μ := volume)
      (a₁ := (F k).toBoundedContinuousFunction) (a₂ := (F 0).toBoundedContinuousFunction)
      ((hF k).trans (hF 0).symm)
    rw [← CkHolderSpace.coe_toBoundedContinuousFunction, this,
      CkHolderSpace.coe_toBoundedContinuousFunction]
  refine ⟨F 0, contDiff_infty.2 fun k ↦ ?_, ?_⟩
  · rw [← hFk k]
    exact (F k).contDiff
  -- `ψ f` and `F 0` have the same tempered distribution.
  obtain ⟨v, hv, -⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le
    (.of_forall fun x ↦ ψ.norm_le_seminorm ℝ x) f
  have h₁ := (Lp.toTemperedDistribution_eq_smulLeftCLM_iff ψ.hasTemperateGrowth v f).1 hv.symm
  have h₂ := Lp.toTemperedDistribution_eq_toTemperedDistribution_iff.1
    (hv.symm.trans (hF 0).symm)
  filter_upwards [h₁, h₂, BoundedContinuousFunction.coeFn_toLpTop (𝕜 := ℂ) volume
    (F 0).toBoundedContinuousFunction] with x hx₁ hx₂ hx₃
  rw [← hx₁, hx₂, hx₃, CkHolderSpace.coe_toBoundedContinuousFunction]

end Symbol

end TauCeti
