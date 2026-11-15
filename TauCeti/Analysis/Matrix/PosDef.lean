/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import TauCeti.Topology.Instances.Matrix

/-!
# The positive-definite cone in the space of all square matrices

The positive-definite cone of matrices over a star-ordered ring is convex over any star-ordered
scalar ring acting strictly monotonically on the entries; in particular, the cone of real or
complex matrices is convex over `ℝ`.

Positivity of the real part of `star x ⬝ᵥ M *ᵥ x` on nonzero vectors cuts out an open set
of real or complex square matrices, Hermitian or not.

The positive-definite cone itself is not open in the space of all square matrices — the
Hermitian condition cuts out a proper subspace once there are at least two rows. On the
Hermitian subspace over either `ℝ` or `ℂ`, the cone is open: positivity is uniform on the compact
unit sphere and persists under small perturbations.
For real matrices the cone is measurable ambiently, being the intersection of the closed
Hermitian condition with the open set of `isOpen_setOfPred_re_dotProduct_pos`.

Inverse segments between continuously varying positive-definite endpoints depend continuously
on the endpoints and the segment parameter. On a compact family, their entries have a common
bound. These inverse-segment arguments are adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).

## Main declarations

* `TauCeti.convex_setOfPred_posDef` — the positive-definite matrices form a convex set;
* `TauCeti.isOpen_setOfPred_re_dotProduct_pos` — positivity of the quadratic form on nonzero
  vectors is an open condition on real or complex square matrices;
* `TauCeti.measurableSet_setOfPred_posDef` — the positive-definite real matrices form a
  measurable set.
* `Matrix.isOpen_setOfPred_posDef_selfAdjoint` — the positive-definite cone is open in the
  Hermitian subspace over `ℝ` or `ℂ`;
* `TauCeti.continuousAt_inv_segment` and `TauCeti.continuous_inv_segment_pairs` — continuity
  of inverse segments with positive-definite endpoints;
* `TauCeti.exists_uniform_inv_segment_apply_bound` — a common entry bound on compact fields.
-/

public section

noncomputable section

open Topology

open scoped Matrix

namespace TauCeti

/-- The positive-definite matrices over a star-ordered ring `R` form a convex set over any
star-ordered scalar ring `𝕜` whose positive elements act strictly monotonically on `R`; for
instance, the positive-definite real or complex matrices form a convex set over `ℝ`. -/
theorem convex_setOfPred_posDef {𝕜 R n : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
    [StarRing 𝕜] [StarOrderedRing 𝕜] [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    [Algebra 𝕜 R] [StarModule 𝕜 R] [PosSMulStrictMono 𝕜 R] :
    Convex 𝕜 {A : Matrix n n R | A.PosDef} := by
  rw [convex_iff_forall_pos]
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

/-- Positivity of the real part of the quadratic form on nonzero vectors is an open condition
on square real or complex matrices, Hermitian or not. -/
theorem isOpen_setOfPred_re_dotProduct_pos {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜] :
    IsOpen {M : Matrix ι ι 𝕜 | ∀ x : ι → 𝕜, x ≠ 0 →
      0 < RCLike.re (star x ⬝ᵥ M *ᵥ x)} := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  -- By compactness of the unit sphere, positivity on it is stable under small perturbations.
  have key : ∀ᶠ N in 𝓝 M, ∀ x ∈ Metric.sphere (0 : ι → 𝕜) 1,
      0 < RCLike.re (star x ⬝ᵥ N *ᵥ x) := by
    refine (isCompact_sphere (0 : ι → 𝕜) 1).eventually_forall_of_forall_eventually
      fun y hy => ?_
    have hcont : Continuous fun z : Matrix ι ι 𝕜 × (ι → 𝕜) =>
        RCLike.re (star z.2 ⬝ᵥ z.1 *ᵥ z.2) := by
      fun_prop
    exact (hcont.tendsto (M, y)).eventually_const_lt
      (hM y (ne_zero_of_mem_sphere one_ne_zero ⟨y, hy⟩))
  -- Rescale a nonzero vector onto the unit sphere; the quadratic form scales by a positive factor.
  filter_upwards [key] with N hN x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h := hN (‖x‖⁻¹ • x) (by simp [norm_smul, hx0.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, RCLike.smul_re] at h
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp
    ((mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp h)

/-- The positive-definite real matrices form a measurable set. -/
theorem measurableSet_setOfPred_posDef {ι : Type*} [Finite ι] :
    MeasurableSet {A : Matrix ι ι ℝ | A.PosDef} := by
  have : Fintype ι := Fintype.ofFinite ι
  simp only [Matrix.posDef_iff_dotProduct_mulVec, star_trivial, Set.ofPred_and]
  exact (isClosed_eq continuous_id.matrix_conjTranspose continuous_id).measurableSet.inter
    (by simpa only [star_trivial, RCLike.re_to_real] using
      (isOpen_setOfPred_re_dotProduct_pos (𝕜 := ℝ) (ι := ι)).measurableSet)

end TauCeti

namespace Matrix

open scoped ComplexOrder

/-- Positive definiteness is open in the real vector space of Hermitian matrices, over either
the real or the complex scalars. -/
theorem isOpen_setOfPred_posDef_selfAdjoint {n 𝕜 : Type*} [Finite n]
    [RCLike 𝕜] :
    IsOpen {A : selfAdjoint (Matrix n n 𝕜) | (A : Matrix n n 𝕜).PosDef} := by
  classical
  let : Fintype n := Fintype.ofFinite n
  have hopen := (TauCeti.isOpen_setOfPred_re_dotProduct_pos (ι := n) (𝕜 := 𝕜)).preimage
    (continuous_subtype_val : Continuous (fun A : selfAdjoint (Matrix n n 𝕜) ↦
      (A : Matrix n n 𝕜)))
  convert hopen using 1
  ext A
  constructor
  · exact fun hA x hx ↦ hA.re_dotProduct_pos hx
  · intro hA
    have hAH := isHermitian_iff_isSelfAdjoint.mpr A.prop
    exact PosDef.of_dotProduct_mulVec_pos hAH fun x hx ↦
      RCLike.pos_iff.mpr ⟨hA x hx, hAH.im_star_dotProduct_mulVec_self x⟩

end Matrix

/-- Every real convex combination of positive-definite matrices is positive definite. -/
theorem Matrix.PosDef.one_sub_smul_add_smul {ι R : Type*} [Ring R] [PartialOrder R]
    [StarRing R] [AddLeftMono R] [Algebra ℝ R] [StarModule ℝ R] [PosSMulStrictMono ℝ R]
    {A B : Matrix ι ι R} (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ((1 - t) • A + t • B).PosDef :=
  TauCeti.convex_setOfPred_posDef hA hB (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)

namespace TauCeti

open Set
open scoped Matrix.Norms.Elementwise NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inversion is continuous along a continuously varying segment with positive-definite
endpoints, at every parameter in the unit interval. -/
theorem continuousAt_inv_segment {X : Type*} [TopologicalSpace X]
    {P Q : X → Matrix ι ι ℝ} {t : X → ℝ} {x : X}
    (hP : ContinuousAt P x) (hQ : ContinuousAt Q x) (ht : ContinuousAt t x)
    (hp : (P x).PosDef) (hq : (Q x).PosDef) (hx : t x ∈ Icc 0 1) :
    ContinuousAt (fun y => ((1 - t y) • P y + t y • Q y)⁻¹) x := by
  have hc : ContinuousAt (fun y => (1 - t y) • P y + t y • Q y) x := by fun_prop
  exact hc.matrix_inv (hp.one_sub_smul_add_smul hq hx).det_pos.ne'

section CompactPositiveFields

variable {X : Type*} [TopologicalSpace X]

/-- The inverse segment depends continuously on both endpoints in a positive-definite field
and on the unit-interval parameter. -/
theorem continuous_inv_segment_pairs {s : Set X} (H : X → Matrix ι ι ℝ)
    (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    Continuous (fun z : (s × s) × Icc (0 : ℝ) 1 =>
      ((1 - (z.2 : ℝ)) • H z.1.1 + (z.2 : ℝ) • H z.1.2)⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact continuousAt_inv_segment
    (hH.domRestrict.comp (continuous_fst.comp continuous_fst)).continuousAt
    (hH.domRestrict.comp (continuous_snd.comp continuous_fst)).continuousAt
    (continuous_subtype_val.comp continuous_snd).continuousAt
    (hpos z.1.1 z.1.1.property) (hpos z.1.2 z.1.2.property) z.2.property

/-- Inverse segments between all pairs in a compact positive-definite field have a common
strictly positive entry bound. -/
theorem exists_uniform_inv_segment_apply_bound (H : X → Matrix ι ι ℝ) {s : Set X} (hs : IsCompact s)
    (hH : ContinuousOn H s) (hpos : ∀ x ∈ s, (H x).PosDef) :
    ∃ L : ℝ≥0,
      0 < L ∧
        ∀ x ∈ s, ∀ y ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, |((1 - t) • H x + t • H y)⁻¹ i j| ≤ L := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hcompact := isCompact_range (continuous_inv_segment_pairs H hH hpos)
  obtain ⟨R, hR⟩ := hcompact.isBounded.exists_norm_le
  let L : ℝ≥0 := (max R 0 + 1).toNNReal
  have hL : (L : ℝ) = max R 0 + 1 := Real.coe_toNNReal _ (by positivity)
  have hLpos : (0 : ℝ) < (L : ℝ) := by rw [hL]; positivity
  refine ⟨L, by exact_mod_cast hLpos, ?_⟩
  intro x hx y hy t ht i j
  have hcap := hR _ ⟨((⟨x, hx⟩, ⟨y, hy⟩), ⟨t, ht⟩), rfl⟩
  rw [← Real.norm_eq_abs, hL]
  exact Matrix.norm_apply_le_norm _ |>.trans (hcap.trans (by linarith [le_max_left R 0]))

end CompactPositiveFields

end TauCeti
