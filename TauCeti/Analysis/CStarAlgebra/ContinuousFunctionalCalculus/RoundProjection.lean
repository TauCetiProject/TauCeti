/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import TauCeti.Topology.Algebra.NonUnitalStarAlgebra
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import TauCeti.Analysis.CStarAlgebra.Basic
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Topology.Algebra.Indicator

/-!
# Rounding an almost-projection

The rounding `Q = χ_{[1/2, ∞)}(h)` of an element `h` of a (not necessarily unital) C⋆-algebra
(`TauCeti.roundProjection`) is a star projection commuting with `h`. If `‖h * h - h‖ ≤ δ` (or
`‖h - h²‖ ≤ δ` in a unital Banach algebra), every point `t` of the real (quasi)spectrum of `h`
has `|t - t²| ≤ δ`, so `t` lies within `2δ` of `0` (when `t < 1/2`) or of `1` (when `t ≥ 1/2`).
For `δ < 1/4` the (quasi)spectrum therefore avoids `1/2`, the indicator of `[1/2, ∞)` is continuous
on it, and for self-adjoint `h` we get `‖h - Q‖ ≤ 2δ` and (in the unital case) `‖(1 - Q)h‖ ≤ 2δ`,
as well as normalizing `h` to `Q` in closed corners via `cfcₙ ((Ici (1/2)).indicator (√·)⁻¹) h`.
The bound `δ < 1/4` is sharp: for `h = id` in `C([0, 1], ℂ)`, `‖h - h²‖ = 1/4` and the rounding is
the junk value `0`.

## Main declarations

* `TauCeti.roundProjection`, `TauCeti.isStarProjection_roundProjection`,
  `TauCeti.commute_roundProjection`, `TauCeti.roundProjection_zero`,
  `TauCeti.roundProjection_mem`, `TauCeti.continuousOn_roundProjection`: the rounding.
* `TauCeti.lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum`,
  `IsSelfAdjoint.lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_quasispectrum`: the spectral
  dichotomy.
* `TauCeti.continuousOn_roundProjection_indicator`,
  `IsSelfAdjoint.continuousOn_roundProjection_indicator_quasispectrum`: continuity of the indicator
  of `[1/2, ∞)` on the (quasi)spectrum of an almost-projection.
* `IsSelfAdjoint.norm_sub_roundProjection_le`, `TauCeti.norm_sub_roundProjection_le`,
  `TauCeti.norm_one_sub_roundProjection_mul_le`: `‖h - Q‖ ≤ 2δ` and `‖(1 - Q)h‖ ≤ 2δ`.
* `IsSelfAdjoint.cfcₙ_indicator_Ici_half_inv_sqrt_mul_self_mul`,
  `IsSelfAdjoint.roundProjection_eq_of_mul_eq`, `IsSelfAdjoint.exists_mem_corner_of_norm_sub_le`,
  `IsStarProjection.roundProjection_eq`: corner normalization and projection fixed-point property.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Lemma 2.7. The rounding is the
  spectral-projection step of the operator-norm version of its unitalization.
-/

public section

open scoped CStarAlgebra NonUnitalContinuousFunctionalCalculus

namespace TauCeti

private theorem lt_and_abs_le_or_le_and_abs_one_sub_le {t δ : ℝ} (ht : |t - t ^ 2| ≤ δ) :
    (t < 1 / 2 ∧ |t| ≤ 2 * δ) ∨ (1 / 2 ≤ t ∧ |1 - t| ≤ 2 * δ) := by
  rw [abs_le] at ht
  rcases lt_or_ge t (1 / 2) with h | h
  · refine .inl ⟨h, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · refine .inr ⟨h, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [HasSummableGeomSeries A] {h : A} {δ : ℝ}

/-- **Spectrum of an almost-projection.** If `‖h - h²‖ ≤ δ`, every point `t` of the real spectrum
of `h` lies within `2δ` of `0`, if `t < 1/2`, or of `1`, if `t ≥ 1/2`. -/
theorem lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum (hδ : ‖h - h ^ 2‖ ≤ δ) {t : ℝ}
    (ht : t ∈ spectrum ℝ h) :
    (t < 1 / 2 ∧ |t| ≤ 2 * δ) ∨ (1 / 2 ≤ t ∧ |1 - t| ≤ 2 * δ) := by
  refine lt_and_abs_le_or_le_and_abs_one_sub_le (le_trans ?_ hδ)
  have hp := spectrum.subset_polynomial_aeval h (Polynomial.X - Polynomial.X ^ 2) ⟨t, ht, rfl⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow, map_sub,
    Polynomial.aeval_X, map_pow] at hp
  exact quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ _ hp)

/-- If `‖h - h²‖ ≤ δ < 1/4`, the spectrum of `h` avoids `1/2`, so the indicator of `[1/2, ∞)`
defining `TauCeti.roundProjection h` is continuous on it. -/
theorem continuousOn_roundProjection_indicator (hδ : ‖h - h ^ 2‖ ≤ δ) (hδ4 : δ < 1 / 4) :
    ContinuousOn ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (spectrum ℝ h) := by
  refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
  rw [frontier_Ici, Set.disjoint_singleton_left]
  intro ht
  rcases lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum hδ ht with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1.false
  · rw [abs_le] at h2
    linarith

end Banach

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- The **rounding** of `h` to a projection: the spectral projection `χ_{[1/2, ∞)}(h)`. For a
self-adjoint `h` with `‖h * h - h‖ ≤ δ < 1/4` it is a star projection within `2δ` of `h`
(`IsSelfAdjoint.norm_sub_roundProjection_le`). -/
noncomputable def roundProjection (h : A) : A :=
  cfcₙ ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) h

/-- Unfolding lemma for `roundProjection`. -/
theorem roundProjection_def (h : A) :
    roundProjection h = cfcₙ ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) h :=
  (rfl)

/-- The rounding of `h` is always a star projection. -/
@[simp]
theorem isStarProjection_roundProjection (h : A) : IsStarProjection (roundProjection h) :=
  isStarProjection_cfcₙ_indicator h _

/-- The rounding of `h` commutes with `h`. -/
theorem commute_roundProjection (h : A) : Commute (roundProjection h) h :=
  Commute.cfcₙ_real (Commute.refl h) _

/-- The rounding of `0` is `0` (not `@[simp]`: `simp` already closes this via
`IsStarProjection.zero` and `IsStarProjection.roundProjection_eq`). -/
theorem roundProjection_zero : roundProjection (0 : A) = 0 := by
  simp [roundProjection_def]

/-- `roundProjection a` belongs to every closed non-unital `𝕜'`-`⋆`-subalgebra containing `a`
(for any scalar action `𝕜'` over `ℝ`, including `ℝ` and `ℂ`). -/
theorem roundProjection_mem {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A]
    [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A]
    [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {a : A} (ha : a ∈ s) :
    roundProjection a ∈ s :=
  roundProjection_def a ▸ cfcₙ_mem (𝕜 := ℝ) (𝕜' := 𝕜') _ ha

/-- `TauCeti.roundProjection` is continuous on the self-adjoint elements whose real quasispectrum
avoids `1 / 2`. -/
theorem continuousOn_roundProjection :
    ContinuousOn (roundProjection (A := A))
      {a : A | IsSelfAdjoint a ∧ (1 / 2 : ℝ) ∉ quasispectrum ℝ a} := by
  have hcont : ContinuousOn (fun a : A ↦ a)
      {a : A | IsSelfAdjoint a ∧ (1 / 2 : ℝ) ∉ quasispectrum ℝ a} := continuousOn_id
  refine hcont.cfcₙ_of_mem_nhdsSet (𝕜 := ℝ) (p := IsSelfAdjoint) (s := {(1 / 2 : ℝ)}ᶜ)
    ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) ?_ (fun _ ha ↦ ha.1)
    (continuousOn_const.continuousOn_indicator_of_disjoint_frontier (by simp))
    (by simp)
  exact isClosed_singleton.isOpen_compl.mem_nhdsSet.2
    (Set.iUnion₂_subset fun _ ha t ht hmem ↦ ha.2 (Set.mem_singleton_iff.mp hmem ▸ ht))

end NonUnitalCStarAlgebra

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

/-- **Quasispectrum of a self-adjoint almost-projection.** If `‖a * a - a‖ ≤ δ`, every point `t`
of the real quasispectrum of `a` lies within `2δ` of `0` (if `t < 1/2`) or of `1` (if `1/2 ≤ t`). -/
theorem lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_quasispectrum (ha : IsSelfAdjoint a)
    {δ : ℝ} (hδ : ‖a * a - a‖ ≤ δ) {t : ℝ} (ht : t ∈ quasispectrum ℝ a) :
    (t < 1 / 2 ∧ |t| ≤ 2 * δ) ∨ (1 / 2 ≤ t ∧ |1 - t| ≤ 2 * δ) :=
  TauCeti.lt_and_abs_le_or_le_and_abs_one_sub_le <| by
    simpa only [sq, abs_sub_comm] using (ha.abs_mul_self_sub_le_norm ht).trans hδ

/-- When `IsSelfAdjoint a` and `‖a * a - a‖ < 1 / 4`, `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem half_notMem_quasispectrum_of_norm_mul_self_sub_lt (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) : (1 / 2 : ℝ) ∉ quasispectrum ℝ a := fun hmem ↦ by
  have hle := ha.abs_mul_self_sub_le_norm hmem; norm_num at hle; linarith

/-- Continuity of `indicator (Ici (1 / 2)) 1` on `quasispectrum ℝ a` when `‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_roundProjection_indicator_quasispectrum (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (quasispectrum ℝ a) :=
  continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
    simpa [frontier_Ici] using ha.half_notMem_quasispectrum_of_norm_mul_self_sub_lt h

/-- Continuous non-unital `𝕜'`-`⋆`-algebra homomorphisms (over any `ℝ`-algebra `𝕜'`, including `ℝ`
and `ℂ`) preserve `TauCeti.roundProjection` whenever `1 / 2 ∉ quasispectrum ℝ a`. -/
theorem map_roundProjection {𝕜' B F : Type*} [CommRing 𝕜'] [Algebra ℝ 𝕜']
    [NonUnitalCStarAlgebra B] [Module 𝕜' A] [Module 𝕜' B] [IsScalarTower ℝ 𝕜' A]
    [IsScalarTower ℝ 𝕜' B] [FunLike F A B] [NonUnitalAlgHomClass F 𝕜' A B] [StarHomClass F A B]
    (ha : IsSelfAdjoint a) (h : (1 / 2 : ℝ) ∉ quasispectrum ℝ a) (φ : F) (hφ : Continuous φ) :
    φ (roundProjection a) = roundProjection (φ a) :=
  NonUnitalStarAlgHomClass.map_cfcₙ (S := 𝕜') φ _ a
    (continuousOn_const.continuousOn_indicator_of_disjoint_frontier <| by
      rwa [frontier_Ici, Set.disjoint_singleton_left]) (by simp) hφ ha (ha.map φ)

/-- **Rounding an almost-projection (non-unital).** If `a` is self-adjoint with
`‖a * a - a‖ ≤ δ < 1/4`, then its rounding `χ_{[1/2, ∞)}(a)` is within `2δ` of `a`. -/
theorem norm_sub_roundProjection_le (ha : IsSelfAdjoint a) {δ : ℝ} (hδ : ‖a * a - a‖ ≤ δ)
    (hδ4 : δ < 1 / 4) : ‖a - roundProjection a‖ ≤ 2 * δ := by
  have hc := ha.continuousOn_roundProjection_indicator_quasispectrum (hδ.trans_lt hδ4)
  have he : cfcₙ (fun t : ℝ ↦ t - (Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ) t) a =
      a - roundProjection a := by
    rw [cfcₙ_sub (fun t : ℝ ↦ t) _ a continuousOn_id rfl hc (by simp), cfcₙ_id' ℝ a,
      roundProjection_def]
  rw [← he]
  refine norm_cfcₙ_le fun t ht ↦ ?_
  rcases ha.lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_quasispectrum hδ ht with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rwa [Set.indicator_of_notMem (by simpa using h1), sub_zero, Real.norm_eq_abs]
  · rwa [Set.indicator_of_mem (by simpa using h1), Pi.one_apply, Real.norm_eq_abs, abs_sub_comm]

/-- Continuity of `(Set.Ici (1 / 2)).indicator fun t ↦ (√t)⁻¹` on `quasispectrum ℝ a` when
`‖a * a - a‖ < 1 / 4`. -/
theorem continuousOn_indicator_Ici_half_inv_sqrt_quasispectrum (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    ContinuousOn ((Set.Ici (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) (quasispectrum ℝ a) :=
  ContinuousOn.continuousOn_indicator_of_disjoint_frontier
    (Real.continuous_sqrt.continuousOn.inv₀ fun _ ht ↦
      (Real.sqrt_pos.mpr (by linarith [Set.mem_Ici.mp (interior_subset ht)])).ne')
    (by simpa [frontier_Ici] using ha.half_notMem_quasispectrum_of_norm_mul_self_sub_lt h)

/-- For self-adjoint `a` with `‖a * a - a‖ < 1 / 4`, `w = cfcₙ ((Ici (1 / 2)).indicator (√·)⁻¹) a`
satisfies `w * a * w = roundProjection a`. -/
theorem cfcₙ_indicator_Ici_half_inv_sqrt_mul_self_mul (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    cfcₙ ((Set.Ici (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a * a *
        cfcₙ ((Set.Ici (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a =
      roundProjection a := by
  have hg := ha.continuousOn_indicator_Ici_half_inv_sqrt_quasispectrum h
  rw [roundProjection_def]; conv_lhs => lhs; rhs; rw [← cfcₙ_id' ℝ a]
  rw [← cfcₙ_mul _ (fun t : ℝ ↦ t) a hg (by simp) continuousOn_id rfl,
    ← cfcₙ_mul _ _ a (hg.fun_mul (continuousOn_id' _)) (by simp) hg (by simp)]
  refine cfcₙ_congr fun t _ ↦ ?_; by_cases ht : (1 / 2 : ℝ) ≤ t
  · simp only [Set.indicator_of_mem (Set.mem_Ici.mpr ht), Pi.one_apply]
    field_simp [(Real.sqrt_pos.mpr (by linarith)).ne']; exact (Real.sq_sqrt (by linarith)).symm
  · simp only [Set.indicator_of_notMem (Set.mem_Ici.not.mpr ht), zero_mul]

/-- Estimate `‖cfcₙ ((Ici (1 / 2)).indicator (√·)⁻¹) a - roundProjection a‖ ≤ 4 * ‖a * a - a‖`
for self-adjoint `a` with `‖a * a - a‖ < 1 / 4`. -/
theorem norm_cfcₙ_indicator_Ici_half_inv_sqrt_sub_roundProjection_le (ha : IsSelfAdjoint a)
    (h : ‖a * a - a‖ < 1 / 4) :
    ‖cfcₙ ((Set.Ici (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹) a - roundProjection a‖ ≤
      4 * ‖a * a - a‖ := by
  rw [roundProjection_def, ← cfcₙ_sub _ _ a
    (ha.continuousOn_indicator_Ici_half_inv_sqrt_quasispectrum h) (by simp)
    (ha.continuousOn_roundProjection_indicator_quasispectrum h) (by simp)]
  refine norm_cfcₙ_le fun t ht ↦ ?_; rw [Real.norm_eq_abs]; by_cases hge : (1 / 2 : ℝ) ≤ t
  · simp only [Set.indicator_of_mem (Set.mem_Ici.mpr hge), Pi.one_apply]
    have hsq : √t * √t = t := Real.mul_self_sqrt (by linarith)
    have hfactor : t * t - t = -(((√t)⁻¹ - 1) * (t * √t * (1 + √t))) := by
      field_simp [(Real.sqrt_pos.mpr (by linarith : 0 < t)).ne']; nlinarith
    have hpos_prod : 0 < t * √t * (1 + √t) := by positivity
    have h1 : |t * t - t| = |(√t)⁻¹ - 1| * (t * √t * (1 + √t)) := by
      rw [hfactor, abs_neg, abs_mul, abs_of_pos hpos_prod]
    have hnonneg : 0 ≤ t * √t := by positivity
    have hquarter : (1 / 4 : ℝ) ≤ t * √t * (1 + √t) := by nlinarith
    nlinarith [ha.abs_mul_self_sub_le_norm ht, abs_nonneg ((√t)⁻¹ - 1)]
  · simp only [Set.indicator_of_notMem (Set.mem_Ici.not.mpr hge), sub_self, abs_zero]; positivity

/-- If `a` is self-adjoint, satisfies `p * a = a` for a star projection `p`, and
`‖a - p‖ ≤ 1 / 5`, then `TauCeti.roundProjection a = p`. -/
theorem roundProjection_eq_of_mul_eq {p : A} (ha : IsSelfAdjoint a) (hp : IsStarProjection p)
    (hpa : p * a = a) (hdist : ‖a - p‖ ≤ 1 / 5) : roundProjection a = p := by
  have hap : a * p = a := by
    simpa [hp.isSelfAdjoint.star_eq, ha.star_eq] using congrArg star hpa
  have ha_lt : ‖a * a - a‖ < 1 / 4 := by
    have := _root_.IsIdempotentElem.norm_mul_self_sub_le_of_mul_eq hp.isIdempotentElem hpa hap
    nlinarith [norm_nonneg (a - p)]
  have hsp_mul_p : roundProjection a * p = roundProjection a := by
    have ha_corner : a ∈ (⊤ : NonUnitalStarSubalgebra ℝ A).corner hp.isSelfAdjoint :=
      NonUnitalStarSubalgebra.mem_corner.mpr ⟨NonUnitalStarAlgebra.mem_top, hpa, hap⟩
    exact (NonUnitalStarSubalgebra.mem_corner.mp (roundProjection_mem (𝕜' := ℝ) ha_corner)).2.2
  refine (isStarProjection_roundProjection a).eq_of_mul_eq_left_of_norm_sub_lt_one hp hsp_mul_p ?_
  have := ha.norm_sub_roundProjection_le le_rfl ha_lt
  rw [norm_sub_rev] at this
  linarith [norm_sub_le_norm_sub_add_norm_sub (roundProjection a) a p]

/-- For a star projection `p` and a self-adjoint element `a ∈ s.corner hp.isSelfAdjoint` of a
closed nonunital `⋆`-subalgebra with `‖a - p‖ ≤ 1 / 5`, there exists a self-adjoint normalizing
element `w ∈ s.corner hp.isSelfAdjoint` satisfying `w * a * w = p` and
`‖w - p‖ ≤ 4 * (‖a - p‖ ^ 2 + ‖a - p‖)`. -/
theorem exists_mem_corner_of_norm_sub_le {𝕜' : Type*} [CommRing 𝕜'] [Module 𝕜' A]
    [IsScalarTower 𝕜' A A] [SMulCommClass 𝕜' A A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
    {s : NonUnitalStarSubalgebra 𝕜' A} [IsClosed (s : Set A)] {p : A}
    (ha : IsSelfAdjoint a) (hp : IsStarProjection p)
    (ha_corner : a ∈ s.corner hp.isSelfAdjoint) (hdist : ‖a - p‖ ≤ 1 / 5) :
    ∃ w ∈ s.corner hp.isSelfAdjoint, IsSelfAdjoint w ∧ w * a * w = p ∧
      ‖w - p‖ ≤ 4 * (‖a - p‖ ^ 2 + ‖a - p‖) := by
  have : SMulMemClass (NonUnitalStarSubalgebra 𝕜' A) ℝ A :=
    SMulMemClass.ofIsScalarTower _ ℝ 𝕜' A
  obtain ⟨-, hpa, hap⟩ := NonUnitalStarSubalgebra.mem_corner.mp ha_corner
  have ha_defect : ‖a * a - a‖ ≤ ‖a - p‖ ^ 2 + ‖a - p‖ :=
    _root_.IsIdempotentElem.norm_mul_self_sub_le_of_mul_eq hp.isIdempotentElem hpa hap
  have ha_lt_quarter : ‖a * a - a‖ < 1 / 4 := by nlinarith [norm_nonneg (a - p)]
  have hsp_eq_p : roundProjection a = p := ha.roundProjection_eq_of_mul_eq hp hpa hdist
  set g : ℝ → ℝ := (Set.Ici (1 / 2 : ℝ)).indicator fun t ↦ (√t)⁻¹
  refine ⟨cfcₙ g a, cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℝ) g ha_corner, cfcₙ_predicate g a, ?_, ?_⟩
  · simpa [g, hsp_eq_p] using ha.cfcₙ_indicator_Ici_half_inv_sqrt_mul_self_mul ha_lt_quarter
  · have hw_sub_p : ‖cfcₙ g a - p‖ ≤ 4 * ‖a * a - a‖ := by
      simpa [g, hsp_eq_p] using
        ha.norm_cfcₙ_indicator_Ici_half_inv_sqrt_sub_roundProjection_le ha_lt_quarter
    linarith

end IsSelfAdjoint

/-- Every star projection `p` is fixed by `TauCeti.roundProjection`. -/
@[simp]
theorem IsStarProjection.roundProjection_eq {A : Type*} [NonUnitalCStarAlgebra A] {p : A}
    (hp : IsStarProjection p) : TauCeti.roundProjection p = p := by
  have h := hp.isSelfAdjoint.norm_sub_roundProjection_le (δ := 0) (by simp [hp.isIdempotentElem.eq])
    (by norm_num)
  rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at h
  exact h.symm

namespace TauCeti

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] {h : A} {δ : ℝ}

/-- In a unital C⋆-algebra, `roundProjection h` agrees with the unital functional calculus
`cfc ((Set.Ici (1 / 2 : ℝ)).indicator 1) h`. -/
theorem roundProjection_eq_cfc (h : A) :
    roundProjection h = cfc ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) h := by
  set f : ℝ → ℝ := (Set.Ici (1 / 2 : ℝ)).indicator 1
  by_cases hh : IsSelfAdjoint h
  · by_cases hc : ContinuousOn f (spectrum ℝ h)
    · have hcq : ContinuousOn f (quasispectrum ℝ h) := by
        rw [quasispectrum_eq_spectrum_union_zero]
        intro x hx
        rcases lt_or_ge x (1 / 2) with hx_lt | hx_ge
        · have hev : f =ᶠ[nhds x] 0 :=
            Filter.eventually_of_mem (Iio_mem_nhds hx_lt) fun y hy ↦
              Set.indicator_of_notMem (not_le.mpr hy) _
          exact hev.continuousAt.continuousWithinAt
        · have hx_pos : 0 < x := by linarith
          have hx_spec : x ∈ spectrum ℝ h :=
            hx.resolve_right fun hx0 ↦ by rw [hx0] at hx_pos; exact lt_irrefl 0 hx_pos
          have hsub : (spectrum ℝ h ∪ {0}) ∩ Set.Ioi (0 : ℝ) = spectrum ℝ h ∩ Set.Ioi 0 := by
            ext y; simp (config := { contextual := true }) [ne_of_gt]
          exact (continuousWithinAt_inter (isOpen_Ioi.mem_nhds hx_pos)).mp
            (by rw [hsub]; exact (hc x hx_spec).mono Set.inter_subset_left)
      exact cfcₙ_eq_cfc hcq (by simp)
    · have hcq : ¬ ContinuousOn f (quasispectrum ℝ h) :=
        fun hcq ↦ hc (hcq.mono (spectrum_subset_quasispectrum ℝ h))
      rw [roundProjection_def, cfcₙ_apply_of_not_continuousOn _ hcq,
        cfc_apply_of_not_continuousOn _ hc]
  · rw [roundProjection_def, cfcₙ_apply_of_not_predicate _ hh, cfc_apply_of_not_predicate _ hh]

/-- **Rounding an almost-projection.** If `h` is self-adjoint with `‖h - h²‖ ≤ δ < 1/4`, then its
rounding `χ_{[1/2, ∞)}(h)` is within `2δ` of `h`. -/
theorem norm_sub_roundProjection_le (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ4 : δ < 1 / 4) : ‖h - roundProjection h‖ ≤ 2 * δ :=
  hh.norm_sub_roundProjection_le (by rwa [← sq, norm_sub_rev]) hδ4

/-- If `h` is self-adjoint with `‖h - h²‖ ≤ δ < 1/4`, then `h` is within `2δ` of `0` off its
rounding: `‖(1 - χ_{[1/2, ∞)}(h)) h‖ ≤ 2δ`. -/
theorem norm_one_sub_roundProjection_mul_le (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ4 : δ < 1 / 4) : ‖(1 - roundProjection h) * h‖ ≤ 2 * δ := by
  have hQ := isStarProjection_roundProjection h
  have he : (1 - roundProjection h) * h = (1 - roundProjection h) * (h - roundProjection h) := by
    simp [mul_sub, sub_mul, hQ.isIdempotentElem.eq]
  rw [he]
  exact (norm_mul_le_of_norm_le_one_left hQ.one_sub.norm_le _).trans
    (norm_sub_roundProjection_le hh hδ hδ4)

end CStarAlgebra

end TauCeti
