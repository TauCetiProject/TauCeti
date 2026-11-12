/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Haar measure under dilations and affine maps

The dimension root of outer volume scales by the absolute value of a real dilation
in a positive-dimensional real inner product space. The identity applies to arbitrary
sets and infinite outer volumes, and supplies the scaling law for volume inequalities.

An affine map of a finite-dimensional real normed space multiplies every additive Haar measure
by the absolute value of the determinant of its linear part
(`MeasureTheory.Measure.addHaar_image_affineMap`, and
`MeasureTheory.Measure.addHaar_image_affineEquiv` for affine equivalences), the affine form of
Mathlib's `MeasureTheory.Measure.addHaar_image_linearMap`. The affine dilation `y ↦ x + r • y`,
`r ≠ 0`, is quasi-measure-preserving for every additive Haar measure
(`MeasureTheory.Measure.quasiMeasurePreserving_add_smul`), and it scales measures by the
inverse dimension power of `|r|` (`MeasureTheory.Measure.addHaar_preimage_add_smul`), in
particular the measure of the part of a set in a ball or closed ball
(`MeasureTheory.Measure.addHaar_preimage_add_smul_inter_ball`,
`MeasureTheory.Measure.addHaar_preimage_add_smul_inter_closedBall`).

A linear map into a finite-dimensional real normed space that is not surjective has almost every
fibre empty for every additive Haar measure on the codomain
(`LinearMap.ae_preimage_singleton_eq_empty`), since its range is a strict subspace.

For an invertible real square matrix `A` and nonnegative bounds `a i`, the region
`{x | ∀ i, |(A *ᵥ x) i| ≤ a i}` cut out by the linear forms of `A` has volume
`2 ^ n * (∏ i, a i) / |det A|`, where `n` is the size of `A`
(`Matrix.volume_setOf_forall_abs_mulVec_le`). It is the preimage of a coordinate box under `A`;
this is the volume computation behind Minkowski's linear forms theorem.

We also bound the additive Haar measure of the closure of a set in a finite-dimensional real
normed space by the measure of the unit ball times the dimension power of its diameter. This is
the elementary estimate converting coverings by sets of small diameter into measure bounds.
Combined with the diameter bound for Lipschitz images, it bounds the measure of the closure of
the image of a set under a Lipschitz map.

An element of finite order acting linearly on a finite-dimensional real space preserves every
additive Haar measure, because its determinant has finite order and so absolute value one
(`MeasureTheory.Measure.addHaar_preimage_smul_of_isOfFinOrder`). Hence a finite group acting
linearly preserves every additive Haar measure
(`MeasureTheory.Measure.smulInvariantMeasure_addHaar`).

For a continuous linear form `ψ` and `t ≥ 0`, the vectors `v` with `|ψ v| ≤ t ‖v‖` form a closed
cone about the kernel of `ψ`. Its part in the closed ball of radius `R > 0` has measure
`R ^ dim E` times that of its part in the closed unit ball
(`MeasureTheory.Measure.addHaar_closedBall_inter_setOf_abs_le_mul_norm`). For `ψ ≠ 0` the kernel
is a proper subspace, hence null, and the latter measure tends to zero as `t → 0⁺`
(`MeasureTheory.Measure.tendsto_addHaar_closedBall_inter_setOf_abs_le_mul_norm`).
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Dimension-root volume scales linearly under every real dilation, including zero.
This identity holds for arbitrary sets and infinite outer volumes. -/
theorem volume_smul_rpow {A : Set E} (hn : Module.finrank ℝ E ≠ 0) (c : ℝ) :
    volume (c • A) ^ ((Module.finrank ℝ E : ℝ)⁻¹) =
      ENNReal.ofReal |c| * volume A ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  rw [Measure.addHaar_smul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    abs_pow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (abs_nonneg c) hn]

end TauCeti

namespace MeasureTheory.Measure

section Affine

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

/-- The image of a set under an affine map has Haar measure equal to the absolute value of the
determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineMap (f : F →ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f.linear| * μ s := by
  have hf : f '' s = (fun y ↦ y + f 0) '' (f.linear '' s) := by
    rw [image_image]
    exact image_congr fun x _ ↦ by simpa using f.map_vadd 0 x
  rw [hf, image_add_right, measure_preimage_add_right, addHaar_image_linearMap]

/-- The image of a set under an affine equivalence has Haar measure equal to the absolute value of
the determinant of the linear part times the measure of the set. -/
theorem addHaar_image_affineEquiv (f : F ≃ᵃ[ℝ] F) (s : Set F) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f.linear : F →ₗ[ℝ] F)| * μ s :=
  addHaar_image_affineMap μ (f : F →ᵃ[ℝ] F) s

/-- The affine dilation `y ↦ x + r • y` with `r ≠ 0` is quasi-measure-preserving for an additive
Haar measure, so preimages under it of null-measurable sets are null-measurable. -/
theorem quasiMeasurePreserving_add_smul (x : F) {r : ℝ} (hr : r ≠ 0) :
    QuasiMeasurePreserving (fun y ↦ x + r • y) μ μ :=
  (measurePreserving_add_left μ x).quasiMeasurePreserving.comp (quasiMeasurePreserving_smul μ hr)

/-- **The volume of a blow-up.** For `r ≠ 0`, the preimage of `s` under the affine dilation
`y ↦ x + r • y` has measure `|r| ^ (-n) μ s`, where `n = dim F`. -/
theorem addHaar_preimage_add_smul (x : F) {r : ℝ} (hr : r ≠ 0) (s : Set F) :
    μ ((fun y ↦ x + r • y) ⁻¹' s) = ENNReal.ofReal |(r ^ Module.finrank ℝ F)⁻¹| * μ s := by
  have h : (fun y ↦ x + r • y) ⁻¹' s = (r • ·) ⁻¹' ((fun y ↦ x + y) ⁻¹' s) := rfl
  rw [h, addHaar_preimage_smul μ hr, measure_preimage_add]

/-- **The volume of a blow-up in a ball.** For `r ≠ 0`, the preimage of `s` under the affine
dilation `y ↦ x + r • y` satisfies `μ(s_{x,r} ∩ ball 0 ρ) = |r| ^ (-n) μ(s ∩ ball x (|r| * ρ))`,
where `n = dim F`. -/
theorem addHaar_preimage_add_smul_inter_ball (x : F) {r : ℝ} (hr : r ≠ 0) (s : Set F) (ρ : ℝ) :
    μ ((fun y ↦ x + r • y) ⁻¹' s ∩ Metric.ball 0 ρ) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ F)⁻¹| * μ (s ∩ Metric.ball x (|r| * ρ)) := by
  have hball : (fun y ↦ x + r • y) ⁻¹' Metric.ball x (|r| * ρ) = Metric.ball 0 ρ := by
    simpa [vadd_eq_add, add_comm, Real.norm_eq_abs] using
      TauCeti.preimage_smul_vadd_ball_norm x (c := r) (norm_pos_iff.2 hr) ρ
  rw [← hball, ← preimage_inter, addHaar_preimage_add_smul μ x hr]

/-- **The volume of a blow-up in a closed ball.** For `r ≠ 0`, the preimage of `s` under the
affine dilation `y ↦ x + r • y` satisfies
`μ(s_{x,r} ∩ closedBall 0 ρ) = |r| ^ (-n) μ(s ∩ closedBall x (|r| * ρ))`, where `n = dim F`. -/
theorem addHaar_preimage_add_smul_inter_closedBall (x : F) {r : ℝ} (hr : r ≠ 0) (s : Set F)
    (ρ : ℝ) :
    μ ((fun y ↦ x + r • y) ⁻¹' s ∩ Metric.closedBall 0 ρ) =
      ENNReal.ofReal |(r ^ Module.finrank ℝ F)⁻¹| * μ (s ∩ Metric.closedBall x (|r| * ρ)) := by
  have hball : (fun y ↦ x + r • y) ⁻¹' Metric.closedBall x (|r| * ρ) = Metric.closedBall 0 ρ := by
    simpa [vadd_eq_add, add_comm, Real.norm_eq_abs] using
      TauCeti.preimage_smul_vadd_closedBall x (c := r) (norm_pos_iff.2 hr) ρ
  rw [← hball, ← preimage_inter, addHaar_preimage_add_smul μ x hr]

end Affine

section Diameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The closure of a set of diameter `d` in an `n`-dimensional real normed space has additive
Haar measure at most `μ (ball 0 1) * d ^ n`, since it lies in a closed ball of radius `d`.
This holds for every set, including empty and unbounded ones. -/
theorem addHaar_closure_le_mul_ediam_pow (μ : Measure E) [μ.IsAddHaarMeasure] (s : Set E) :
    μ (closure s) ≤ μ (Metric.ball 0 1) * Metric.ediam s ^ Module.finrank ℝ E := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  by_cases hs : Metric.ediam s = ∞
  · have hE : Module.finrank ℝ E ≠ 0 := by
      intro hE
      have : Subsingleton E := Module.finrank_zero_iff.1 hE
      rw [Metric.ediam_subsingleton Set.subsingleton_of_subsingleton] at hs
      exact ENNReal.zero_ne_top hs
    rw [hs, ENNReal.top_pow hE, ENNReal.mul_top (Metric.measure_ball_pos μ 0 one_pos).ne']
    exact le_top
  have hb : Bornology.IsBounded s := Metric.isBounded_iff_ediam_ne_top.2 hs
  have hsub : closure s ⊆ Metric.closedBall x (Metric.diam s) := fun y hy ↦ by
    rw [Metric.mem_closedBall, ← Metric.diam_closure]
    exact Metric.dist_le_diam_of_mem hb.closure hy (subset_closure hx)
  calc μ (closure s) ≤ μ (Metric.closedBall x (Metric.diam s)) := measure_mono hsub
    _ = μ (Metric.ball 0 1) * Metric.ediam s ^ Module.finrank ℝ E := by
      rw [addHaar_closedBall μ x Metric.diam_nonneg, mul_comm,
        ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam, ENNReal.ofReal_toReal hs]

end Diameter

section FiniteOrder

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- An element of finite order acting linearly on a finite-dimensional real space preserves
every additive Haar measure. Its determinant has finite order in `ℝ`, hence absolute value
one. -/
theorem addHaar_preimage_smul_of_isOfFinOrder [Monoid G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] {g : G} (hg : IsOfFinOrder g) (s : Set E) :
    μ ((g • ·) ⁻¹' s) = μ s := by
  set L := DistribMulAction.toModuleEnd ℝ E g
  have habs : |LinearMap.det L| = 1 :=
    ((((absHom (α := ℝ)).toMonoidHom).comp
      (LinearMap.det.comp (DistribMulAction.toModuleEnd ℝ E))).isOfFinOrder hg).eq_one
      (abs_nonneg _)
  have hdet : LinearMap.det L ≠ 0 := fun h => by simp [h] at habs
  have h := addHaar_preimage_linearMap μ hdet s
  rwa [abs_inv, habs, inv_one, ENNReal.ofReal_one, one_mul] at h

/-- A finite group acting linearly on a finite-dimensional real space preserves every additive
Haar measure. -/
theorem smulInvariantMeasure_addHaar [Group G] [Finite G] [DistribMulAction G E]
    [SMulCommClass G ℝ E] : SMulInvariantMeasure G E μ :=
  ⟨fun g s _ => addHaar_preimage_smul_of_isOfFinOrder μ (isOfFinOrder_of_finite g) s⟩

end FiniteOrder

section ThinCone

open Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The part of the cone `{v | |ψ v| ≤ t ‖v‖}` in the closed ball of radius `R > 0` is the
dilation by `R` of its part in the closed unit ball, so its measure is `R ^ dim E` times that
of the latter. -/
theorem addHaar_closedBall_inter_setOf_abs_le_mul_norm (ψ : E →L[ℝ] ℝ) (t : ℝ) {R : ℝ}
    (hR : 0 < R) :
    μ (closedBall (0 : E) R ∩ {v | |ψ v| ≤ t * ‖v‖}) =
      ENNReal.ofReal (R ^ Module.finrank ℝ E) *
        μ (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) := by
  have hset : closedBall (0 : E) R ∩ {v | |ψ v| ≤ t * ‖v‖} =
      R • (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}) := by
    ext v
    rw [mem_smul_set_iff_inv_smul_mem₀ hR.ne']
    simp only [mem_inter_iff, mem_ofPred_eq, mem_closedBall_zero_iff, map_smul, smul_eq_mul,
      norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hR]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [inv_mul_le_iff₀ hR]; linarith, ?_⟩
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hR.le)
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [inv_mul_le_iff₀ hR] at h1; linarith, ?_⟩
      rw [mul_left_comm] at h2
      exact le_of_mul_le_mul_left h2 (inv_pos.mpr hR)
  rw [hset, Measure.addHaar_smul, abs_of_pos (pow_pos hR _)]

/-- For a nonzero linear form `ψ`, the part of the cone `{v | |ψ v| ≤ t ‖v‖}` in the closed unit
ball has measure tending to zero as `t → 0⁺`: the cones shrink to the kernel of `ψ`, a proper
subspace and hence a null set. -/
theorem tendsto_addHaar_closedBall_inter_setOf_abs_le_mul_norm {ψ : E →L[ℝ] ℝ} (hψ : ψ ≠ 0) :
    Tendsto (fun t : ℝ ↦ μ (closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖})) (𝓝[>] 0) (𝓝 0) := by
  set C : ℝ → Set E := fun t ↦ closedBall (0 : E) 1 ∩ {v | |ψ v| ≤ t * ‖v‖}
  have hmono : Monotone C := fun s t hst v hv ↦
    ⟨hv.1, hv.2.trans (mul_le_mul_of_nonneg_right hst (norm_nonneg v))⟩
  -- The sequence of cones of aperture `1 / (n + 1)`.
  have hmeas (n : ℕ) : NullMeasurableSet (C (1 / (n + 1))) μ :=
    (isClosed_closedBall.inter (isClosed_le (by fun_prop) (by fun_prop))).measurableSet
      |>.nullMeasurableSet
  have hanti : Antitone fun n : ℕ ↦ C (1 / (n + 1)) := fun m n hmn ↦ hmono (by gcongr)
  have hfin : μ (C (1 / ((0 : ℕ) + 1))) ≠ ∞ :=
    (measure_mono inter_subset_left).trans_lt measure_closedBall_lt_top |>.ne
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, hfin⟩
  set W := LinearMap.ker (ψ : E →ₗ[ℝ] ℝ)
  have hker : ⋂ n : ℕ, C (1 / (n + 1)) ⊆ (W : Set E) := by
    intro v hv
    simp only [mem_iInter] at hv
    simp only [SetLike.mem_coe, W, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine abs_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun δ hδ ↦ ?_) (abs_nonneg _))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hv1 : ‖v‖ ≤ 1 := mem_closedBall_zero_iff.mp (hv n).1
    calc |ψ v| ≤ 1 / (n + 1) * ‖v‖ := (hv n).2
      _ ≤ 1 / (n + 1) * 1 := by gcongr
      _ ≤ 0 + δ := by linarith
  have hker0 : μ (W : Set E) = 0 := by
    refine Measure.addHaar_submodule _ _ fun htop ↦ hψ ?_
    ext v
    have hv : v ∈ W := htop ▸ Submodule.mem_top
    simpa [W] using hv
  rw [measure_mono_null hker hker0] at hlim
  -- Every small aperture is dominated by a term of the sequence.
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp hlim ε hε).exists
  filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < 1 / (n + 1))] with t ht
  exact (measure_mono (hmono ht.2.le)).trans hn

end ThinCone

end MeasureTheory.Measure

namespace LinearMap

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A linear map that is not surjective has almost every fibre empty, for every additive Haar
measure on its finite-dimensional codomain. -/
theorem ae_preimage_singleton_eq_empty (μ : Measure F) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] F)
    (hL : ¬Function.Surjective L) :
    ∀ᵐ y ∂μ, L ⁻¹' {y} = ∅ := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    (Measure.addHaar_submodule μ _ (mt range_eq_top.mp hL))] with y hy
  exact eq_empty_of_forall_notMem fun x hx ↦ hy ⟨x, hx⟩

end LinearMap

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The region cut out by the linear forms of an invertible real square matrix `A`: for
nonnegative bounds `a i`, the set of `x : ι → ℝ` with `|(A *ᵥ x) i| ≤ a i` for every `i` has
volume `2 ^ n * (∏ i, a i) / |det A|`, where `n` is the cardinality of `ι`. This includes the case
of an empty `ι`, where both sides are `1`. -/
theorem volume_setOf_forall_abs_mulVec_le (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) {a : ι → ℝ}
    (ha : 0 ≤ a) :
    volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| ≤ a i} =
      ENNReal.ofReal (2 ^ Fintype.card ι * (∏ i, a i) / |A.det|) := by
  have hS : {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| ≤ a i} = toLin' A ⁻¹' Icc (-a) a := by
    ext x
    simp [abs_le, Pi.le_def, forall_and]
  rw [hS, Measure.addHaar_preimage_linearMap _ (by rwa [LinearMap.det_toLin']),
    LinearMap.det_toLin', Real.volume_Icc_pi]
  simp_rw [Pi.neg_apply, sub_neg_eq_add, ← two_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ mul_nonneg zero_le_two (ha i),
    ← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, inv_mul_eq_div]

end Matrix

namespace LipschitzOnWith

open MeasureTheory
open scoped NNReal

variable {X E : Type*} [PseudoEMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The closure of the image of a set `A` under a `K`-Lipschitz map into an `n`-dimensional real
normed space has additive Haar measure at most `μ (ball 0 1) * K ^ n * ediam A ^ n`. -/
theorem addHaar_closure_image_le_mul_ediam_pow (μ : Measure E) [μ.IsAddHaarMeasure] {K : ℝ≥0}
    {f : X → E} {A : Set X} (hf : LipschitzOnWith K f A) :
    μ (closure (f '' A)) ≤
      μ (Metric.ball 0 1) * K ^ Module.finrank ℝ E * Metric.ediam A ^ Module.finrank ℝ E := by
  have hdiam : Metric.ediam (f '' A) ≤ K * Metric.ediam A :=
    Metric.ediam_image_le_iff.2 fun x hx x' hx' ↦
      (hf hx hx').trans (by gcongr; exact Metric.edist_le_ediam_of_mem hx hx')
  calc μ (closure (f '' A)) ≤ μ (Metric.ball 0 1) * Metric.ediam (f '' A) ^ Module.finrank ℝ E :=
        Measure.addHaar_closure_le_mul_ediam_pow μ _
    _ ≤ μ (Metric.ball 0 1) * (K * Metric.ediam A) ^ Module.finrank ℝ E := by gcongr
    _ = _ := by rw [mul_pow, mul_assoc]

end LipschitzOnWith
