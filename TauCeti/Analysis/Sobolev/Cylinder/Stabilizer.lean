/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.UniversalLevelSet
public import TauCeti.Analysis.Sobolev.Cylinder.Gluing
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Topology.Algebra.Order.Floor
import TauCeti.Analysis.Fredholm.Stabilization

/-!
# Smooth compactly supported stabilizers on the cylinder

Let `D : X → L²(ℝ × S¹, W)` be a Fredholm operator, for instance the realization
`W^{1,2} → L²` of a first-order operator on the cylinder whose ends are nondegenerate. A
*stabilizer* of `D` is a finite-dimensional space `S` of sections whose classes complement the
range of `D`. Adjoining it makes `D` onto: the operator `(ξ, σ) ↦ D ξ + σ` on `X × S` is
surjective, and since `S` meets the range of `D` only in `0` its kernel is `ker D × {0}`.

This file constructs stabilizers spanned by smooth sections supported in a compact piece
`[-T, T] × (0, 1)` of the cylinder, and feeds them to the linear gluing theorem on the cylinder.

* `TauCeti.CylinderSobolev.smoothSectionLp W T` is the space of classes in
  `L²(ℝ × S¹, W) = L²(ℝ × [0, 1], W)` of the smooth maps `ℝ × ℝ → W` whose support is a compact
  subset of `[-T, T] × (0, 1)`. Such a map vanishes near `t = 0` and `t = 1`, so its extension
  by periodicity in `t` is a smooth section of the cylinder vanishing for `|s| > T`
  (`TauCeti.CylinderSobolev.exists_periodic_of_mem_smoothSectionLp`). In particular the elements
  of `smoothSectionLp W T` vanish for `|s| > T`
  (`TauCeti.CylinderSobolev.ae_eq_zero_of_mem_smoothSectionLp`).
* These sections are dense in `L²` as `T` varies
  (`TauCeti.CylinderSobolev.dense_iUnion_smoothSectionLp`): smooth compactly supported maps on
  the plane are dense in `L²` of the strip (`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`),
  and multiplying them by cutoffs in `t` that vanish near `t = 0` and `t = 1` approximates them
  in `L²`.
* **Stabilizers.** Every Fredholm operator `D` with values in `L²(ℝ × S¹, W)` has a stabilizer
  in `smoothSectionLp W T` for some `T`
  (`TauCeti.CylinderSobolev.exists_le_smoothSectionLp_isTopCompl_range`): the stabilizer can be
  chosen inside any dense subspace of the target
  (`ContinuousLinearMap.IsFredholm.exists_le_isTopCompl_range_of_dense`), and its finitely
  many generators are supported in a common compact piece. Then `(ξ, σ) ↦ D ξ + σ` is onto,
  with kernel `ker D × {0}`.
* **Stabilized gluing of Fredholm pieces.** For two first-order operators `D₁` and `D₂` on the
  cylinder with matching ends that are Fredholm, the stabilized operators `D₁ + ι₁` and
  `D₂ + ι₂` with such stabilizers have bounded right inverses
  (`ContinuousLinearMap.IsFredholm.hasRightInverse_coprod`), and the stabilizers stay away from
  the glued ends. So the linear gluing theorem
  `TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff`
  applies: for every long enough neck the glued operator `D_R`, stabilized by the translates
  `j_R` of the two stabilizers, has a bounded right inverse of norm bounded independently of `R`
  (`exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm`).
  This is the uniformly surjective augmented operator `D_R ⊕ j_R` from which the kernel and
  cokernel of `D_R` are compared with those of `D₁` and `D₂`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix A.2 (stabilizing a Fredholm operator by a finite-dimensional space complementing
  its range), and Chapter 10 (linear gluing).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on gluing and the uniformly bounded right inverses of the glued
  linearized operators.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal ContDiff
open Submodule (IsTopCompl)

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### Smooth sections supported in a compact piece of the cylinder -/

variable (W) in
/-- The classes in `L²(ℝ × S¹, W)`, realized as `L²` of the strip `ℝ × [0, 1]`, of the smooth maps
`ξ : ℝ × ℝ → W` whose topological support lies in `[-T, T] × (0, 1)`. The support is then compact
and stays away from the lines `t = 0` and `t = 1`, so `ξ` is also a smooth section of the cylinder
`ℝ × S¹`, extended by periodicity in `t`. -/
def smoothSectionLp (T : ℝ) : Submodule ℝ (Lp W 2 stripMeasure) where
  carrier := {η | ∃ ξ : ℝ × ℝ → W, ContDiff ℝ ∞ ξ ∧ tsupport ξ ⊆ Icc (-T) T ×ˢ Ioo 0 1 ∧
    η =ᵐ[stripMeasure] ξ}
  zero_mem' := ⟨0, contDiff_const, by simp, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro η η' ⟨ξ, hξ, hξs, hη⟩ ⟨ξ', hξ', hξs', hη'⟩
    exact ⟨ξ + ξ', hξ.add hξ', (tsupport_add ξ ξ').trans (union_subset hξs hξs'),
      (Lp.coeFn_add η η').trans (hη.add hη')⟩
  smul_mem' := by
    rintro c η ⟨ξ, hξ, hξs, hη⟩
    exact ⟨c • ξ, contDiff_const.smul hξ, (tsupport_smul_subset_right _ _).trans hξs,
      (Lp.coeFn_smul c η).trans (hη.const_smul c)⟩

/-- Membership in `TauCeti.CylinderSobolev.smoothSectionLp`. -/
theorem mem_smoothSectionLp_iff {T : ℝ} {η : Lp W 2 stripMeasure} :
    η ∈ smoothSectionLp W T ↔ ∃ ξ : ℝ × ℝ → W, ContDiff ℝ ∞ ξ ∧
      tsupport ξ ⊆ Icc (-T) T ×ˢ Ioo 0 1 ∧ η =ᵐ[stripMeasure] ξ :=
  Iff.rfl

/-- The spaces of sections supported in `[-T, T] × (0, 1)` increase with `T`. -/
theorem smoothSectionLp_mono : Monotone (smoothSectionLp W) := by
  intro T T' h η ⟨ξ, hξ, hξs, hη⟩
  exact ⟨ξ, hξ, hξs.trans (prod_mono (Icc_subset_Icc (neg_le_neg h) h) le_rfl), hη⟩

/-- An element of `TauCeti.CylinderSobolev.smoothSectionLp W T` vanishes almost everywhere on
`|s| > T`. -/
theorem ae_eq_zero_of_mem_smoothSectionLp {T : ℝ} {η : Lp W 2 stripMeasure}
    (hη : η ∈ smoothSectionLp W T) : ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0 := by
  obtain ⟨ξ, -, hξs, hηξ⟩ := hη
  filter_upwards [hηξ] with z hz hT
  rw [hz]
  exact image_eq_zero_of_notMem_tsupport fun h ↦ (abs_le.2 (hξs h).1).not_gt hT

/-- **Periodic representatives.** An element of `TauCeti.CylinderSobolev.smoothSectionLp W T` is
the class of a smooth section of the cylinder vanishing for `|s| > T`: a smooth map
`ξ : ℝ × ℝ → W` of period one in `t` with `ξ (s, t) = 0` for `T < |s|`. -/
theorem exists_periodic_of_mem_smoothSectionLp {T : ℝ} {η : Lp W 2 stripMeasure}
    (hη : η ∈ smoothSectionLp W T) :
    ∃ ξ : ℝ × ℝ → W, ContDiff ℝ ∞ ξ ∧ (∀ s t, ξ (s, t + 1) = ξ (s, t)) ∧
      (∀ s t, T < |s| → ξ (s, t) = 0) ∧ η =ᵐ[stripMeasure] ξ := by
  obtain ⟨ξ, hξ, hξs, hηξ⟩ := hη
  have hξ0 {z : ℝ × ℝ} (hz : z ∉ tsupport ξ) : ξ z = 0 := image_eq_zero_of_notMem_tsupport hz
  -- The support of `ξ` is compact, so it stays below some level `t = 1 - ε`.
  have hK : IsCompact (tsupport ξ) := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
    (isClosed_tsupport ξ) (hξs.trans (prod_mono subset_rfl Ioo_subset_Icc_self))
  obtain ⟨ε, hε, hεK⟩ : ∃ ε > 0, ∀ z ∈ tsupport ξ, z.2 < 1 - ε := by
    rcases (tsupport ξ).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn h continuous_snd.continuousOn
    exact ⟨(1 - z₀.2) / 2, by linarith [(hξs hz₀).2.2], fun z hz ↦ by
      linarith [isMaxOn_iff.1 hmax z hz, (hξs hz₀).2.2]⟩
  -- Hence `ξ` vanishes, and so is periodic, on `ℝ × (-ε, 0)`.
  have hper (s : ℝ) {t : ℝ} (ht : -ε < t) (ht0 : t < 0) : ξ (s, t + 1) = ξ (s, t) := by
    rw [hξ0 fun h ↦ (hεK _ h).not_ge (by dsimp; linarith),
      hξ0 fun h ↦ (hξs h).2.1.not_gt (by dsimp; linarith)]
  refine ⟨fun z ↦ ξ (z.1, Int.fract z.2), contDiff_iff_contDiffAt.2 fun z ↦ ?_,
    fun s t ↦ by simp [Int.fract_add_one],
    fun s t hs ↦ hξ0 fun h ↦ (abs_le.2 (hξs h).1).not_gt hs, ?_⟩
  · have hc : ContDiff ℝ ∞ fun w : ℝ × ℝ ↦ ξ (w.1, w.2 - ⌊z.2⌋) :=
      hξ.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
    exact hc.contDiffAt.congr_of_eventuallyEq (apply_fract_snd_eventuallyEq hε hper z)
  · filter_upwards [hηξ, ae_mem_openStrip] with z hz hz'
    rw [hz, Int.fract_eq_self.2 ⟨hz'.2.1.le, hz'.2.2⟩]

/-- The cutoff `ψₙ(t) = β((n + 1) t - 1) β((n + 1) (1 - t) - 1)`, for `β` the smooth transition
from `0` to `1`: it vanishes for `t ≤ 1 / (n + 1)` and for `t ≥ 1 - 1 / (n + 1)`, and it takes
values in `[0, 1]`. -/
private def boundaryCutoff (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((n + 1) * t - 1) * Real.smoothTransition ((n + 1) * (1 - t) - 1)

private theorem contDiff_boundaryCutoff (n : ℕ) : ContDiff ℝ ∞ (boundaryCutoff n) := by
  unfold boundaryCutoff
  fun_prop

private theorem boundaryCutoff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ boundaryCutoff n t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

private theorem boundaryCutoff_le_one (n : ℕ) (t : ℝ) : boundaryCutoff n t ≤ 1 :=
  (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
    (Real.smoothTransition.nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The cutoff `ψₙ` vanishes outside `[1 / (n + 1), 1 - 1 / (n + 1)]`. -/
private theorem mem_Icc_of_boundaryCutoff_ne_zero {n : ℕ} {t : ℝ} (h : boundaryCutoff n t ≠ 0) :
    t ∈ Icc (1 / ((n : ℝ) + 1)) (1 - 1 / ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  constructor
  · by_contra ht
    refine h (mul_eq_zero_of_left (Real.smoothTransition.zero_of_nonpos ?_) _)
    have := (lt_div_iff₀' hn).1 (not_le.1 ht)
    linarith
  · by_contra ht
    refine h (mul_eq_zero_of_right _ (Real.smoothTransition.zero_of_nonpos ?_))
    have := (lt_div_iff₀' hn).1 (show 1 - t < 1 / (n + 1) by linarith [not_le.1 ht])
    linarith

/-- On the open interval `(0, 1)` the cutoffs `ψₙ` tend to `1`: they are eventually equal to it. -/
private theorem tendsto_boundaryCutoff {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n ↦ boundaryCutoff n t) atTop (𝓝 1) := by
  obtain ⟨ht0, ht1⟩ := ht
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 / t + 2 / (1 - t))]
    with n hn
  have h2t : 2 ≤ (n + 1) * t := by
    have := (div_le_iff₀ ht0).1 (le_trans (le_add_of_nonneg_right (by positivity)) hn)
    nlinarith
  have h21t : 2 ≤ (n + 1) * (1 - t) := by
    have := (div_le_iff₀ h1t).1 (le_trans (le_add_of_nonneg_left (by positivity)) hn)
    nlinarith
  rw [boundaryCutoff, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

variable (W) in
/-- **Density of smooth compactly supported sections.** The smooth sections supported in compact
pieces `[-T, T] × (0, 1)` of the cylinder are dense in `L²(ℝ × S¹, W)`. -/
theorem dense_iUnion_smoothSectionLp :
    Dense (⋃ T, (smoothSectionLp W T : Set (Lp W 2 stripMeasure))) := by
  -- Smooth maps of compact support on the plane are dense in `L²` of the strip; it remains to
  -- approximate each of them by sections vanishing near `t = 0` and `t = 1`.
  refine dense_closure.1 ((Lp.dense_hasCompactSupport_contDiff (F := W) (μ := stripMeasure)
    (p := 2) ENNReal.ofNat_ne_top).mono ?_)
  rintro f ⟨g, hfg, hgc, hg⟩
  obtain ⟨T, hT⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  have hus (n : ℕ) : ContDiff ℝ ∞ fun z : ℝ × ℝ ↦ boundaryCutoff n z.2 • g z :=
    ((contDiff_boundaryCutoff n).comp contDiff_snd).smul hg
  have hmem (n : ℕ) : MemLp (fun z : ℝ × ℝ ↦ boundaryCutoff n z.2 • g z) 2 stripMeasure :=
    (hus n).continuous.memLp_of_hasCompactSupport
      (hgc.mono' fun z hz ↦ subset_tsupport g (right_ne_zero_of_smul hz))
  -- The section `ψₙ(t) g(s, t)` is supported in `[-T, T] × [1 / (n + 1), 1 - 1 / (n + 1)]`.
  have hsupp (n : ℕ) :
      tsupport (fun z : ℝ × ℝ ↦ boundaryCutoff n z.2 • g z) ⊆ Icc (-T) T ×ˢ Ioo 0 1 := by
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine (closure_minimal (fun z hz ↦ ?_) (isClosed_Icc.prod isClosed_Icc)).trans
      (prod_mono subset_rfl (Icc_subset_Ioo hn (sub_lt_self 1 hn)))
    obtain ⟨hψ, hgz⟩ := smul_ne_zero_iff.1 (Function.mem_support.1 hz)
    have hzT : ‖z‖ ≤ T := mem_closedBall_zero_iff.1 (hT (subset_tsupport g hgz))
    exact ⟨abs_le.1 ((le_max_left _ _).trans hzT), mem_Icc_of_boundaryCutoff_ne_zero hψ⟩
  refine mem_closure_of_tendsto (tendsto_toLp_of_ae_tendsto_of_norm_le (l := atTop)
    ENNReal.ofNat_ne_top hmem hfg (fun n ↦ .of_forall fun z ↦ ?_) ?_)
    (.of_forall fun n ↦ mem_iUnion.2 ⟨T, _, hus n, hsupp n, (hmem n).coeFn_toLp⟩)
  · rw [norm_smul, Real.norm_of_nonneg (boundaryCutoff_nonneg n z.2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (boundaryCutoff_le_one n z.2)
  · filter_upwards [ae_mem_openStrip] with z hz
    simpa using (tendsto_boundaryCutoff hz.2).smul_const (g z)

/-! ### Stabilizers of Fredholm operators -/

/-- **Smooth compactly supported stabilizers.** For every Fredholm operator `D` with values in
`L²(ℝ × S¹, W)` there are a compact piece `[-T, T] × (0, 1)` of the cylinder and a
finite-dimensional space `S` of smooth sections supported in it which is a topological complement
of the range of `D`. Then `(ξ, σ) ↦ D ξ + σ` is onto, with kernel `ker D × {0}`. -/
theorem exists_le_smoothSectionLp_isTopCompl_range {X : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] {D : X →L[ℝ] Lp W 2 stripMeasure} (hD : D.IsFredholm) :
    ∃ T, ∃ S : Submodule ℝ (Lp W 2 stripMeasure), S ≤ smoothSectionLp W T ∧
      FiniteDimensional ℝ S ∧ IsTopCompl D.range S ∧
      Function.Surjective (D.coprod S.subtypeL) ∧
      (D.coprod S.subtypeL).ker = D.ker.prod ⊥ := by
  have hdense :
      Dense ((⨆ T, smoothSectionLp W T : Submodule ℝ _) : Set (Lp W 2 stripMeasure)) :=
    (dense_iUnion_smoothSectionLp W).mono
      (iUnion_subset fun T ↦ SetLike.coe_subset_coe.2 (le_iSup (smoothSectionLp W) T))
  obtain ⟨S, hSD, hSfin, hS, hsurj, hker⟩ := hD.exists_le_isTopCompl_range_of_dense hdense
  -- `S` is finitely generated, hence a compact element of the lattice of submodules, so it lies
  -- below one member of the directed family `smoothSectionLp W T`.
  obtain ⟨_, ⟨T, rfl⟩, hT⟩ := (isCompactElement_iff_le_of_directed_sSup_le _).1
    ((Submodule.fg_iff_compact S).1 ((Submodule.fg_iff_finiteDimensional S).2 hSfin))
    (range (smoothSectionLp W)) (range_nonempty _)
    smoothSectionLp_mono.directed_le.directedOn_range (by rwa [sSup_range])
  exact ⟨T, S, hT, hSfin, hS, hsurj, hker⟩

/-! ### Stabilized gluing of Fredholm operators -/

variable [CompleteSpace W]

/-- **Stabilized linear gluing of Fredholm operators.** Let `D₁` and `D₂` be the realizations
`W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, W)` of first-order operators with essentially bounded coefficient
fields `M₁` and `M₂` whose ends match, `M₁(s, ·) → M` as `s → +∞` and `M₂(s, ·) → M` as
`s → -∞`, and suppose that `D₁` and `D₂` are Fredholm. Then there are finite-dimensional spaces
`S₁` and `S₂` of smooth sections supported in a common compact piece `[-T, T] × (0, 1)` of the
cylinder, complementing the ranges of `D₁` and `D₂`, and a constant `C`, such that for every
sufficiently long neck `R` the glued operator `D_R` of
`TauCeti.gluedCoeff (Function.curry M₁) (Function.curry M₂) R`, stabilized by the translates
`j_R (σ₁, σ₂) = σ₁(· + R, ·) + σ₂(· - R, ·)`
(`TauCeti.CylinderSobolev.gluedStabilizer`), has a bounded right inverse of norm at most `C`. -/
theorem exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {M : ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    (hD₁ : ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).IsFredholm)
    (hD₂ : ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).IsFredholm) :
    ∃ T, ∃ S₁ S₂ : Submodule ℝ (Lp W 2 stripMeasure),
      S₁ ≤ smoothSectionLp W T ∧ S₂ ≤ smoothSectionLp W T ∧
      FiniteDimensional ℝ S₁ ∧ FiniteDimensional ℝ S₂ ∧
      IsTopCompl ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).range S₁ ∧
      IsTopCompl ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).range S₂ ∧
      ∃ C R₀ : ℝ, ∀ R ≥ R₀, ∃ Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂),
        (((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
            (H1 V).subtypeL).coprod (gluedStabilizer S₁.subtypeL S₂.subtypeL R)).comp Q =
            ContinuousLinearMap.id ℝ _ ∧
          ‖Q‖ ≤ C := by
  obtain ⟨T₁, S₁, hS₁T, hS₁fin, hS₁, hsurj₁, -⟩ := exists_le_smoothSectionLp_isTopCompl_range hD₁
  obtain ⟨T₂, S₂, hS₂T, hS₂fin, hS₂, hsurj₂, -⟩ := exists_le_smoothSectionLp_isTopCompl_range hD₂
  -- Both stabilizers are supported in `[-T, T] × (0, 1)` for `T = max T₁ T₂`.
  set T := max T₁ T₂
  have hS₁T' := hS₁T.trans (smoothSectionLp_mono (le_max_left T₁ T₂))
  have hS₂T' := hS₂T.trans (smoothSectionLp_mono (le_max_right T₁ T₂))
  have hQ₁ := hD₁.hasRightInverse_coprod hsurj₁
  have hQ₂ := hD₂.hasRightInverse_coprod hsurj₂
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff hM₁ hM₂
    h₁ h₂ (ι₁ := S₁.subtypeL) (ι₂ := S₂.subtypeL) (T := T)
    (fun σ ↦ (ae_eq_zero_of_mem_smoothSectionLp (hS₁T' σ.property)).mono fun z hz hzT ↦
      hz (hzT.trans_le (le_abs_self _)))
    (fun σ ↦ (ae_eq_zero_of_mem_smoothSectionLp (hS₂T' σ.property)).mono fun z hz hzT ↦
      hz (by linarith [neg_le_abs z.1]))
    (ContinuousLinearMap.ext hQ₁.rightInverse_rightInverse)
    (ContinuousLinearMap.ext hQ₂.rightInverse_rightInverse)
  exact ⟨T, S₁, S₂, hS₁T', hS₂T', hS₁fin, hS₂fin, hS₁, hS₂, _, R₀, hR₀⟩

end TauCeti.CylinderSobolev
