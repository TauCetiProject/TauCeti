/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import TauCeti.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Topology.Algebra.Indicator

/-!
# Star projections from the continuous functional calculus

If a function `f` takes star projections as values on the spectrum of `a`, for instance a real
function taking only the values `0` and `1` there, then `cfc f a` is a star projection, for any
scalar semiring and predicate carrying a continuous functional calculus. When `f` is continuous on
the spectrum and `a` satisfies the predicate this follows from multiplicativity of the functional
calculus; otherwise `cfc f a` is the junk value `0`. In particular the spectral projector
`cfc (Ω.indicator 1) a` is a star projection for every set `Ω` of scalars and every `a`.

When `a` is self-adjoint and invertible, `0` is not in its spectrum, so the spectral projectors
`P₊ = cfc ((Ioi 0).indicator 1) a` and `P₋ = cfc ((Iio 0).indicator 1) a` onto the positive and
negative parts of the spectrum are complementary, `P₊ + P₋ = 1`.

In a complete normed algebra with an isometric functional calculus, such as a C⋆-algebra, the
spectral projector `cfc (Ω.indicator 1) a` depends continuously on the self-adjoint element `a`
wherever the spectrum of `a` avoids the frontier of `Ω`. For self-adjoint `a` in a C⋆-algebra with
`‖a * a - a‖ < 1 / 4`, `spectralProjectionIoiHalf a` satisfies `‖spectralProjectionIoiHalf a - a‖ ≤`
`2 * ‖a * a - a‖` and `cfcₙ ((Ioi (1 / 2)).indicator (√·)⁻¹) a` normalizes `a` to it.

## Main results

* `TauCeti.isStarProjection_cfc`, `TauCeti.isStarProjection_cfcₙ` — `cfc f a` and `cfcₙ f a` are
  star projections when the values of `f` on the (quasi)spectrum of `a` are star projections;
* `TauCeti.isStarProjection_cfc_indicator`, `TauCeti.isStarProjection_cfcₙ_indicator` — the
  spectral projectors `cfc (Ω.indicator 1) a` and `cfcₙ (Ω.indicator 1) a` are star projections;
* `TauCeti.cfc_indicator_mul_cfc_indicator` — the product of the spectral projectors for two
  sets is the spectral projector for their intersection;
* `IsUnit.continuousOn_indicator_spectrum` — at an invertible element, the indicator of a set
  whose frontier is contained in `{0}` is continuous on the spectrum;
* `TauCeti.cfc_indicator_Ioi_add_cfc_indicator_Iio` — for invertible self-adjoint `a`, the
  positive and negative spectral projectors add up to `1`;
* `IsSelfAdjoint.continuousWithinAt_cfc_indicator` — the spectral projector depends continuously
  on the self-adjoint element when the frontier of the set avoids the spectrum;
* `TauCeti.spectralProjectionIoiHalf`, `IsSelfAdjoint.norm_spectralProjectionIoiHalf_sub_le`,
  `IsSelfAdjoint.cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul`,
  `IsStarProjection.spectralProjectionIoiHalf_eq` — non-unital `(1 / 2, ∞)` spectral calculus.
-/

public section

open scoped NonUnitalContinuousFunctionalCalculus

namespace TauCeti

section NonUnital
variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalContinuousFunctionalCalculus R A p]
/-- If `f t` is a star projection at every point `t` of the quasispectrum of `a`, then `cfcₙ f a`
is a star projection. Over `ℝ` the hypothesis says that `f t` is idempotent, that is, `0` or `1`. -/
theorem isStarProjection_cfcₙ {f : R → R} {a : A}
    (hf : ∀ t ∈ quasispectrum R a, IsStarProjection (f t)) : IsStarProjection (cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (quasispectrum R a) ∧ f 0 = 0
  · refine ⟨?_, (cfcₙ_star f a).symm.trans (cfcₙ_congr fun t ht ↦ (hf t ht).isSelfAdjoint)⟩
    rw [IsIdempotentElem, ← cfcₙ_mul f f a h.2.1 h.2.2 h.2.1 h.2.2]
    exact cfcₙ_congr fun t ht ↦ (hf t ht).isIdempotentElem
  · rw [cfcₙ_apply_of_not_and_and a h]; exact .zero A
/-- The non-unital spectral projector `cfcₙ (Ω.indicator 1) a` is a star projection for every set
`Ω` of scalars. (When `a` does not satisfy `p`, `0 ∈ Ω`, or the indicator is not continuous on the
quasispectrum, `cfcₙ` returns the junk value `0`.) -/
theorem isStarProjection_cfcₙ_indicator (a : A) (Ω : Set R) :
    IsStarProjection (cfcₙ (Ω.indicator (1 : R → R)) a) :=
  isStarProjection_cfcₙ fun t _ ↦ by
    by_cases ht : t ∈ Ω <;> simp [ht, IsStarProjection.zero, IsStarProjection.one]
end NonUnital

section Semiring

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- If `f t` is a star projection at every point `t` of the spectrum of `a`, then `cfc f a` is a
star projection. Over `ℝ` the hypothesis says that `f t` is idempotent, that is, `0` or `1`. -/
theorem isStarProjection_cfc {f : R → R} {a : A}
    (hf : ∀ t ∈ spectrum R a, IsStarProjection (f t)) : IsStarProjection (cfc f a) := by
  refine ⟨?_, (cfc_star f a).symm.trans (cfc_congr fun t ht ↦ (hf t ht).isSelfAdjoint)⟩
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [IsIdempotentElem, ← cfc_mul f f a h.2 h.2]
    exact cfc_congr fun t ht ↦ (hf t ht).isIdempotentElem
  · rw [cfc_apply_of_not_and a h]
    exact .zero

/-- The spectral projector `cfc (Ω.indicator 1) a` is a star projection for every set `Ω` of
scalars. (When `a` does not satisfy the predicate of the functional calculus, or the indicator is
not continuous on its spectrum, it is the junk value `0`.) -/
theorem isStarProjection_cfc_indicator (a : A) (Ω : Set R) :
    IsStarProjection (cfc (Ω.indicator (1 : R → R)) a) :=
  isStarProjection_cfc fun t _ ↦ by
    by_cases ht : t ∈ Ω <;> simp [ht, IsStarProjection.zero, IsStarProjection.one]

/-- The product of the spectral projectors for `Ω` and `Ω'` is the spectral projector for
`Ω ∩ Ω'`, when both indicators are continuous on the spectrum. -/
theorem cfc_indicator_mul_cfc_indicator (a : A) {Ω Ω' : Set R}
    (hf : ContinuousOn (Ω.indicator (1 : R → R)) (spectrum R a))
    (hf' : ContinuousOn (Ω'.indicator (1 : R → R)) (spectrum R a)) :
    cfc (Ω.indicator (1 : R → R)) a * cfc (Ω'.indicator (1 : R → R)) a =
      cfc ((Ω ∩ Ω').indicator (1 : R → R)) a := by
  rw [← cfc_mul _ _ a hf hf', Set.inter_indicator_one]
  rfl

end Semiring

variable {A : Type*} [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

open Set

omit [StarRing A] [TopologicalSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] in
/-- At an invertible element, the indicator of a set whose frontier is contained in `{0}`, such as
a half-line ending at `0`, is continuous on the spectrum, since the spectrum avoids `0`. -/
theorem _root_.IsUnit.continuousOn_indicator_spectrum {a : A} (ha : IsUnit a) {Ω : Set ℝ}
    (hΩ : frontier Ω ⊆ {0}) : ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ a) := by
  classical
  rw [← piecewise_eq_indicator]
  refine ContinuousOn.piecewise (fun x hx ↦ ?_) continuousOn_const continuousOn_const
  exact absurd (mem_singleton_iff.mp (hΩ hx.2) ▸ hx.1) (spectrum.zero_notMem ℝ ha)

/-- For an invertible self-adjoint `a`, the spectral projectors onto the positive and the negative
parts of the spectrum add up to `1`. -/
theorem cfc_indicator_Ioi_add_cfc_indicator_Iio {a : A} (ha : IsUnit a)
    (ha' : IsSelfAdjoint a := by cfc_tac) :
    cfc ((Ioi (0 : ℝ)).indicator 1) a + cfc ((Iio (0 : ℝ)).indicator 1) a = 1 := by
  rw [← cfc_add (hf := ha.continuousOn_indicator_spectrum frontier_Ioi.subset)
    (hg := ha.continuousOn_indicator_spectrum frontier_Iio.subset), ← cfc_const_one ℝ a]
  refine cfc_congr fun x hx ↦ ?_
  rcases lt_or_gt_of_ne (ne_of_mem_of_not_mem hx (spectrum.zero_notMem ℝ ha)) with hx | hx <;>
    simp [hx, hx.not_gt]

end TauCeti

section Continuity

open Filter Set Topology

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [ContinuousStar A] [CompleteSpace A]

/-- The spectral projector for a set `Ω` depends continuously on the self-adjoint element at an
element whose spectrum avoids the frontier of `Ω`. -/
theorem IsSelfAdjoint.continuousWithinAt_cfc_indicator {a : A} (ha : IsSelfAdjoint a)
    {Ω : Set ℝ} (hΩ : Disjoint (frontier Ω) (spectrum ℝ a)) :
    ContinuousWithinAt (cfc (Ω.indicator (1 : ℝ → ℝ))) {b | IsSelfAdjoint b} a := by
  set t := {b : A | IsSelfAdjoint b ∧ spectrum ℝ b ⊆ (frontier Ω)ᶜ}
  have hcont : ContinuousOn (cfc (Ω.indicator (1 : ℝ → ℝ))) t :=
    ContinuousOn.cfc_of_mem_nhdsSet (a := id) _
      (isClosed_frontier.isOpen_compl.mem_nhdsSet.2 (iUnion₂_subset fun b hb ↦ hb.2))
      continuousOn_id (fun b hb ↦ hb.1)
      (continuousOn_const.continuousOn_indicator_of_disjoint_frontier disjoint_compl_right)
  refine (hcont.continuousWithinAt ⟨ha, hΩ.subset_compl_left⟩).mono_of_mem_nhdsWithin ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (spectrum.eventually_disjoint_of_isClosed isClosed_frontier hΩ)]
    with b hb hb'
  exact ⟨hb, hb'.subset_compl_left⟩

end Continuity

section SpectralProjectionIoiHalf
namespace TauCeti
variable {A : Type*} [NonUnitalCStarAlgebra A]
/-- `cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator 1) a`, the `(1 / 2, ∞)` spectral projection when `a` is
self-adjoint and `(Set.Ioi (1 / 2 : ℝ)).indicator 1` is continuous on `quasispectrum ℝ a` (in
particular whenever `1 / 2 ∉ quasispectrum ℝ a`), and the junk value `0` otherwise. -/
noncomputable def spectralProjectionIoiHalf (a : A) : A :=
  cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a
/-- Unfold `TauCeti.spectralProjectionIoiHalf`. -/
theorem spectralProjectionIoiHalf_def (a : A) :
    spectralProjectionIoiHalf a = cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) a := (rfl)
/-- `spectralProjectionIoiHalf a` is always a star projection. -/
@[simp] theorem isStarProjection_spectralProjectionIoiHalf (a : A) :
    IsStarProjection (spectralProjectionIoiHalf a) :=
  isStarProjection_cfcₙ_indicator a (Set.Ioi (1 / 2 : ℝ))
/-- The `(1 / 2, ∞)` spectral projection of `0` is `0` (not `@[simp]`: `simp` already closes this
via `IsStarProjection.zero` and `IsStarProjection.spectralProjectionIoiHalf_eq`). -/
theorem spectralProjectionIoiHalf_zero : spectralProjectionIoiHalf (0 : A) = 0 := by
  simp [spectralProjectionIoiHalf_def]
/-- `spectralProjectionIoiHalf a` belongs to every closed non-unital `𝕜'`-`⋆`-subalgebra containing
`a` (for any scalar action `𝕜'` over `ℝ`, including `ℝ` and `ℂ`). -/
theorem spectralProjectionIoiHalf_mem {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
    [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {a : A} (ha : a ∈ s) :
    spectralProjectionIoiHalf a ∈ s :=
  spectralProjectionIoiHalf_def a ▸ cfcₙ_mem (𝕜 := ℝ) (𝕜' := 𝕜') _ ha
end TauCeti

namespace IsSelfAdjoint
open TauCeti
variable {A : Type*} [NonUnitalCStarAlgebra A] {a : A}
/-- Pointwise quasispectral estimate `|t * t - t| ≤ ‖a * a - a‖` for self-adjoint `a`. -/
theorem abs_mul_self_sub_le_norm (ha : IsSelfAdjoint a) {t : ℝ} (ht : t ∈ quasispectrum ℝ a) :
    |t * t - t| ≤ ‖a * a - a‖ := by
  have hsq : ContinuousOn (fun x : ℝ ↦ x * x) (quasispectrum ℝ a) := by fun_prop
  have hcfc : cfcₙ (fun x : ℝ ↦ x * x - x) a = a * a - a := by
    rw [cfcₙ_sub (fun x : ℝ ↦ x * x) (fun x : ℝ ↦ x) a hsq (mul_zero 0) continuousOn_id rfl,
      cfcₙ_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x) a continuousOn_id rfl continuousOn_id rfl,
      cfcₙ_id' ℝ a]
  have hle :=
    norm_apply_le_norm_cfcₙ (fun x : ℝ ↦ x * x - x) a ht (hsq.sub continuousOn_id) (by simp) ha
  rw [hcfc] at hle
  simpa only [Real.norm_eq_abs] using hle
/-- When `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem half_notMem_quasispectrum_of_norm_mul_self_sub_lt (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) : (1 / 2 : ℝ) ∉ quasispectrum ℝ a := fun hmem ↦ by
  have hle := ha.abs_mul_self_sub_le_norm hmem; norm_num at hle; linarith
/-- Continuity of `indicator (Ioi (1 / 2)) 1` on `quasispectrum ℝ a` when `‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half_quasispectrum (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
  continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
    simpa [frontier_Ioi] using ha.half_notMem_quasispectrum_of_norm_mul_self_sub_lt h
/-- Continuous non-unital `𝕜'`-`⋆`-algebra homomorphisms (over any `ℝ`-algebra `𝕜'`, including `ℝ`
and `ℂ`) preserve `TauCeti.spectralProjectionIoiHalf` whenever `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem map_spectralProjectionIoiHalf {𝕜' B F : Type*} [CommRing 𝕜'] [Algebra ℝ 𝕜']
    [NonUnitalCStarAlgebra B] [Module 𝕜' A] [Module 𝕜' B] [IsScalarTower ℝ 𝕜' A]
    [IsScalarTower ℝ 𝕜' B] [FunLike F A B] [NonUnitalAlgHomClass F 𝕜' A B] [StarHomClass F A B]
    (ha : IsSelfAdjoint a) (h : (1 / 2 : ℝ) ∉ quasispectrum ℝ a) (φ : F) (hφ : Continuous φ) :
    φ (spectralProjectionIoiHalf a) = spectralProjectionIoiHalf (φ a) :=
  NonUnitalStarAlgHomClass.map_cfcₙ (S := 𝕜') φ _ a
    (continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
      rwa [frontier_Ioi, Set.disjoint_singleton_left]) (by simp) hφ ha (ha.map φ)
/-- Sharp bound `‖spectralProjectionIoiHalf a - a‖ ≤ 2 * ‖a * a - a‖` when `‖a * a - a‖ < 1 / 4`. -/
theorem norm_spectralProjectionIoiHalf_sub_le (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖spectralProjectionIoiHalf a - a‖ ≤ 2 * ‖a * a - a‖ := by
  set f : ℝ → ℝ := (Set.Ioi (1 / 2 : ℝ)).indicator 1
  have hcfc : cfcₙ f a - a = cfcₙ (fun t : ℝ ↦ f t - t) a := by
    rw [cfcₙ_sub f (fun t : ℝ ↦ t) a (ha.continuousOn_indicator_Ioi_half_quasispectrum h)
      (by simp [f]) continuousOn_id rfl, cfcₙ_id' ℝ a]
  rw [spectralProjectionIoiHalf_def, hcfc]
  refine norm_cfcₙ_le fun t ht ↦ ?_; rw [Real.norm_eq_abs]; dsimp only [f]
  have hprod : |t| * |1 - t| ≤ ‖a * a - a‖ := by
    simpa [abs_sub_comm, ← abs_mul, mul_sub] using ha.abs_mul_self_sub_le_norm ht
  by_cases hgt : (1 / 2 : ℝ) < t
  · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hgt), Pi.one_apply]
    nlinarith [abs_of_pos (by linarith : 0 < t), abs_nonneg (1 - t)]
  · simp only [Set.indicator_of_notMem (Set.mem_Ioi.not.mpr hgt), zero_sub, abs_neg]
    nlinarith [abs_of_pos (by linarith : 0 < 1 - t), abs_nonneg t]
/-- Continuity of `(Set.Ioi (1 / 2)).indicator fun t ↦ (√t)⁻¹` on `quasispectrum ℝ a` when
`‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ioi_half_inv_sqrt_quasispectrum (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) (quasispectrum ℝ a) :=
  ContinuousOn.continuousOn_indicator_of_disjoint_frontier
    (Real.continuous_sqrt.continuousOn.inv₀ fun _ ht ↦
      (Real.sqrt_pos.mpr (by linarith [Set.mem_Ioi.mp (interior_subset ht)])).ne')
    (by simpa [frontier_Ioi] using ha.half_notMem_quasispectrum_of_norm_mul_self_sub_lt h)
/-- For self-adjoint `a` with `‖a * a - a‖ < 1 / 4`, `w = cfcₙ ((Ioi (1 / 2)).indicator (√·)⁻¹) a`
satisfies `w * a * w = spectralProjectionIoiHalf a`. -/
theorem cfcₙ_indicator_Ioi_half_inv_sqrt_mul_self_mul (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a * a *
        cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a =
      spectralProjectionIoiHalf a := by
  have hg := ha.continuousOn_indicator_Ioi_half_inv_sqrt_quasispectrum h
  rw [spectralProjectionIoiHalf_def]; conv_lhs => lhs; rhs; rw [← cfcₙ_id' ℝ a]
  rw [← cfcₙ_mul _ (fun t : ℝ ↦ t) a hg (by simp) continuousOn_id rfl,
    ← cfcₙ_mul _ _ a (hg.fun_mul (continuousOn_id' _)) (by simp) hg (by simp)]
  refine cfcₙ_congr fun t _ ↦ ?_; by_cases ht : (1 / 2 : ℝ) < t
  · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr ht), Pi.one_apply]
    field_simp [(Real.sqrt_pos.mpr (by linarith)).ne']; exact (Real.sq_sqrt (by linarith)).symm
  · simp only [Set.indicator_of_notMem (Set.mem_Ioi.not.mpr ht), zero_mul]
/-- Estimate `‖cfcₙ ((Ioi (1 / 2)).indicator (√·)⁻¹) a - spectralProjectionIoiHalf a‖ ≤`
`4 * ‖a * a - a‖` for self-adjoint `a` with `‖a * a - a‖ < 1 / 4`. -/
theorem norm_cfcₙ_indicator_Ioi_half_inv_sqrt_sub_spectralProjectionIoiHalf_le
    (ha : IsSelfAdjoint a) (h : ‖a * a - a‖ < 1 / 4) :
    ‖cfcₙ ((Set.Ioi (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a - spectralProjectionIoiHalf a‖ ≤
      4 * ‖a * a - a‖ := by
  rw [spectralProjectionIoiHalf_def, ← cfcₙ_sub _ _ a
    (ha.continuousOn_indicator_Ioi_half_inv_sqrt_quasispectrum h) (by simp)
    (ha.continuousOn_indicator_Ioi_half_quasispectrum h) (by simp)]
  refine norm_cfcₙ_le fun t ht ↦ ?_; rw [Real.norm_eq_abs]; by_cases hgt : (1 / 2 : ℝ) < t
  · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr hgt), Pi.one_apply]
    have hsq : √t * √t = t := Real.mul_self_sqrt (by linarith)
    have hfactor : t * t - t = -(((√t)⁻¹ - 1) * (t * √t * (1 + √t))) := by
      field_simp [(Real.sqrt_pos.mpr (by linarith : 0 < t)).ne']; nlinarith
    have hpos_prod : 0 < t * √t * (1 + √t) := by positivity
    have h1 : |t * t - t| = |(√t)⁻¹ - 1| * (t * √t * (1 + √t)) := by
      rw [hfactor, abs_neg, abs_mul, abs_of_pos hpos_prod]
    have hnonneg : 0 ≤ t * √t := by positivity
    have hquarter : (1 / 4 : ℝ) ≤ t * √t * (1 + √t) := by nlinarith
    nlinarith [ha.abs_mul_self_sub_le_norm ht, abs_nonneg ((√t)⁻¹ - 1)]
  · simp only [Set.indicator_of_notMem (Set.mem_Ioi.not.mpr hgt), sub_self, abs_zero]; positivity
end IsSelfAdjoint
/-- Every star projection `p` is fixed by `TauCeti.spectralProjectionIoiHalf`. -/
@[simp] theorem IsStarProjection.spectralProjectionIoiHalf_eq {A : Type*} [NonUnitalCStarAlgebra A]
    {p : A} (hp : IsStarProjection p) : TauCeti.spectralProjectionIoiHalf p = p := by
  simpa [hp.isIdempotentElem.eq, sub_eq_zero] using
    hp.isSelfAdjoint.norm_spectralProjectionIoiHalf_sub_le (by simp [hp.isIdempotentElem.eq])
end SpectralProjectionIoiHalf
