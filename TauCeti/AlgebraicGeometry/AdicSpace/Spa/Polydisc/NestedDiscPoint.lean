/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Subdisc

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Classification

import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.Analysis.Normed.Group.Ultra

/-!
# Points of the closed unit disc attached to decreasing sequences of discs

Let `K` be a complete nontrivially normed nonarchimedean field and `K⟨T⟩` the coordinate ring of
the closed unit disc `closedPolydisc 1 K`. A decreasing sequence of closed discs in the unit disc

```text
D(a₀, |c₀|) ⊇ D(a₁, |c₁|) ⊇ D(a₂, |c₂|) ⊇ ⋯,      ‖aₙ₊₁ - aₙ‖ ≤ ‖cₙ‖,   ‖cₙ₊₁‖ ≤ ‖cₙ‖,
```

gives a point `η` of the disc, the limit of the Gauss norms of the discs:

```text
η : f ↦ inf_n |f|_{D(aₙ, |cₙ|)} = lim_n |f|_{D(aₙ, |cₙ|)}.
```

When `K` is algebraically closed and the discs have no common point in `K`, these are the points
of type (4) in Wedhorn's description of the closed unit disc (Example 7.57). Decreasing sequences
of discs with no common point exist exactly when `K` is not spherically complete. This is the case
for every algebraically closed separable `K`, such as `ℂ_p`: its norms decrease strictly to a
positive limit along a sequence, and discs with these radii can avoid the points of a dense
sequence one at a time. The comparisons with the other points hold over every complete `K`;
recognising `η` among all points needs `K` to be algebraically closed.

The Gauss norms of `f` on the discs decrease, since the Gauss norm of radius `r` is unchanged by
moving the centre within the disc of radius `r` and increases with the radius. A decreasing limit
of multiplicative ultrametric norms is again one, so `η` is a valuation with values in `ℝ≥0`. It is
bounded by the Gauss norm of the whole disc, which makes it continuous and at most one on
power-bounded elements.

The point `η` lies in a disc `D(b, |d|)` exactly when `d ≠ 0` and
`inf_n max(‖cₙ‖, ‖aₙ - b‖) ≤ ‖d‖`; in particular it lies in every `D(aₙ, |cₙ|)`. This determines
how it relates to the other points of the disc.

* If the discs have a common point `b ∈ K` and their radii have a positive infimum `ρ`, then `η` is
  the point `η_{b,ρ}` of the disc `D(b, ρ)`, and `η` is a point `η_{b,s}` in no other case.
* If the discs have no common point in `K`, then `η` is not a classical point (type (1)), not a
  point `η_{b,s}` (types (2) and (3)), and not one of the rank-two points `η_{b,s⁻}` and
  `η_{b,s⁺}` (type (5)).

If the discs have no common point in `K`, then for every `b` some disc `D(aₙ, |cₙ|)` avoids `b`,
and every point `x` of that disc takes the value `x(aₙ - b)` of a constant on `T - b`. So
`b ↦ η(T - b)` attains no minimum, and, over an algebraically closed `K`, `η` is the only point
lying in every disc: two points that take the value of one nonzero constant on each `T - b` agree
on polynomials, which split into linear factors, and polynomials are dense. Conversely, if
`b ↦ x(T - b)` attains no minimum, then every value `x(T - b)` is the value `x(e)` of a constant,
the norms `‖e‖` have an infimum which is not attained, and the discs `D(b, |e|)` along a sequence
of norms decreasing to it have no common point and contain `x`. So the points of type (4) are
exactly the points at which `b ↦ x(T - b)` attains no minimum.

The support of `η` is not computed here, and the points at which `b ↦ x(T - b)` attains a minimum
are not sorted into Wedhorn's types here.

## Main definitions

* `TauCeti.ValuationSpectrum.nestedDiscValuation`: the infimum of the Gauss norms on a decreasing
  sequence of discs, as a valuation on `K⟨T⟩` with values in `ℝ≥0`.
* `TauCeti.ValuationSpectrum.nestedDiscPoint`: the corresponding point of the closed unit disc.

## Main results

* `TauCeti.ValuationSpectrum.tendsto_nestedDiscValuation`: the Gauss norms of `f` on the discs
  tend to `η(f)`.
* `TauCeti.ValuationSpectrum.nestedDiscPoint_mem_closedSubdisc_iff`: `η` lies in `D(b, |d|)`
  exactly when `d ≠ 0` and `inf_n max(‖cₙ‖, ‖aₙ - b‖) ≤ ‖d‖`; in particular
  `TauCeti.ValuationSpectrum.nestedDiscPoint_mem_closedSubdisc`, `η` lies in every `D(aₙ, |cₙ|)`.
* `TauCeti.ValuationSpectrum.nestedDiscPoint_eq_discPoint_iff`: `η = η_{b,s}` exactly when `b`
  lies in every disc and `s` is the infimum of the radii.
* `TauCeti.ValuationSpectrum.nestedDiscPoint_ne_classicalPoint`,
  `TauCeti.ValuationSpectrum.nestedDiscPoint_ne_discPoint`,
  `TauCeti.ValuationSpectrum.nestedDiscPoint_ne_discPointBelow` and
  `TauCeti.ValuationSpectrum.nestedDiscPoint_ne_discPointAbove`: when the discs have no common
  point in `K`, `η` is none of the points of types (1), (2), (3), or (5).
* `TauCeti.ValuationSpectrum.not_exists_forall_nestedDiscPoint_vle`: when the discs have no common
  point in `K`, `b ↦ η(T - b)` attains no minimum.
* `TauCeti.ValuationSpectrum.eq_nestedDiscPoint_iff`: over an algebraically closed `K`, when the
  discs have no common point, `η` is the only point lying in every `D(aₙ, |cₙ|)`.
* `TauCeti.ValuationSpectrum.exists_eq_nestedDiscPoint_iff`: over an algebraically closed `K`, the
  points of type (4) are exactly the points `x` at which `b ↦ x(T - b)` attains no minimum.
* `TauCeti.ValuationSpectrum.exists_seq_forall_exists_lt_norm_sub`: over an algebraically closed
  separable `K`, such as `ℂ_p`, there is a decreasing sequence of discs with no common point.
* `exists_forall_ne_classicalPoint_discPoint_discPointAbove_discPointBelow`, in the namespace
  `TauCeti.ValuationSpectrum`: hence the closed unit disc over such `K` has a point of type (4),
  one that is not of types (1), (2), (3), or (5).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* V. G. Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.4.4, for the points attached to
  decreasing sequences of discs.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Example 2.20.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3, for the separability of `ℂ_p` and its failure to be spherically complete.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Filter Topology
open scoped NNReal

local notation "𝒯" K => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set _)) isWeightFamily_one_weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  [CompleteSpace K]

omit [IsUltrametricDist K] in
/-- Translations by equal tuples agree, whatever the power-boundedness proofs. -/
private theorem taylorHom_congr {x y : Fin 1 → K} (h : x = y) (hx : ∀ i, IsPowerBounded (x i))
    (hy : ∀ i, IsPowerBounded (y i)) (f : 𝒯 K) : taylorHom x hx f = taylorHom y hy f := by
  subst h
  rfl

variable (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℕ → K) (hc₀ : ∀ n, c n ≠ 0)
  (hc₁ : ∀ n, ‖c n‖ ≤ 1)

/-! ### The valuation -/

/-- The Gauss norm on the disc `D(aₙ, |cₙ|)`: the Gauss norm of radius `‖cₙ‖` about `aₙ`. -/
private noncomputable def discGauss (n : ℕ) : Valuation (𝒯 K) ℝ≥0 :=
  (closedDiscGaussValuation (norm_pos_iff.mpr (hc₀ n)) (hc₁ n)).comap
    (taylorHom (fun _ ↦ a n) fun _ ↦ isPowerBounded_iff_norm_le_one.mpr (ha n))

/-- The Gauss norm on `D(aₙ, |cₙ|)` can be computed about any centre `b` of the disc. -/
private theorem discGauss_eq {n : ℕ} {b : K} (hb : ‖b‖ ≤ 1) (hbn : ‖b - a n‖ ≤ ‖c n‖)
    (f : 𝒯 K) :
    discGauss a ha c hc₀ hc₁ n f = closedDiscGaussValuation (norm_pos_iff.mpr (hc₀ n)) (hc₁ n)
      (taylorHom (fun _ ↦ b) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb) f) := by
  have hd : ‖b - a n‖ ≤ 1 := hbn.trans (hc₁ n)
  rw [discGauss, Valuation.comap_apply, ← closedDiscGaussValuation_taylorHom _ _
    (fun _ ↦ b - a n) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hd) hbn, taylorHom_taylorHom,
    taylorHom_congr (x := (fun _ ↦ b - a n) + fun _ ↦ a n)
      (funext fun _ ↦ sub_add_cancel b (a n)) _
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb)]

variable (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖) (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖)

include hac hcc in
/-- The Gauss norms of `f` on the decreasing discs decrease: recentre the larger disc at the
centre of the smaller one, then shrink the radius. -/
private theorem antitone_discGauss (f : 𝒯 K) :
    Antitone fun n ↦ discGauss a ha c hc₀ hc₁ n f :=
  antitone_nat_of_succ_le fun n ↦ by
    rw [discGauss_eq a ha c hc₀ hc₁ (ha (n + 1)) (hac n), discGauss, Valuation.comap_apply]
    exact closedDiscGaussValuation_le_closedDiscGaussValuation_of_le _ _ (hc₁ n) (hcc n) _

include hac hcc in
private theorem tendsto_discGauss (f : 𝒯 K) :
    Tendsto (fun n ↦ discGauss a ha c hc₀ hc₁ n f) atTop
      (𝓝 (⨅ n, discGauss a ha c hc₀ hc₁ n f)) :=
  tendsto_atTop_ciInf (antitone_discGauss a ha c hc₀ hc₁ hac hcc f) (OrderBot.bddBelow _)

/-- **The valuation of a decreasing sequence of discs** `D(aₙ, |cₙ|)` in the closed unit disc:
`f ↦ inf_n |f|_{D(aₙ, |cₙ|)}`, the infimum of the Gauss norms of radius `‖cₙ‖` about `aₙ`. The
hypotheses `‖aₙ₊₁ - aₙ‖ ≤ ‖cₙ‖` and `‖cₙ₊₁‖ ≤ ‖cₙ‖` say that the discs decrease, which makes the
infimum a limit and hence multiplicative. -/
noncomputable def nestedDiscValuation : Valuation (𝒯 K) ℝ≥0 where
  toFun f := ⨅ n, discGauss a ha c hc₀ hc₁ n f
  map_zero' := by simp
  map_one' := by simp
  map_mul' f g := by
    refine tendsto_nhds_unique ?_ ((tendsto_discGauss a ha c hc₀ hc₁ hac hcc f).mul
      (tendsto_discGauss a ha c hc₀ hc₁ hac hcc g))
    simpa only [map_mul] using tendsto_discGauss a ha c hc₀ hc₁ hac hcc (f * g)
  map_add_le_max' f g :=
    le_of_tendsto_of_tendsto' (tendsto_discGauss a ha c hc₀ hc₁ hac hcc (f + g))
      ((tendsto_discGauss a ha c hc₀ hc₁ hac hcc f).max
        (tendsto_discGauss a ha c hc₀ hc₁ hac hcc g)) fun _ ↦ Valuation.map_add _ _ _

/-- The valuation of the discs is the infimum of the Gauss norms of radius `‖cₙ‖` about `aₙ`. -/
theorem nestedDiscValuation_apply (f : 𝒯 K) :
    nestedDiscValuation a ha c hc₀ hc₁ hac hcc f =
      ⨅ n, closedDiscGaussValuation (norm_pos_iff.mpr (hc₀ n)) (hc₁ n)
        (taylorHom (fun _ ↦ a n) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr (ha n)) f) :=
  (rfl)

/-- **The Gauss norms of `f` on the discs tend to its valuation.** -/
theorem tendsto_nestedDiscValuation (f : 𝒯 K) :
    Tendsto (fun n ↦ closedDiscGaussValuation (norm_pos_iff.mpr (hc₀ n)) (hc₁ n)
        (taylorHom (fun _ ↦ a n) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr (ha n)) f))
      atTop (𝓝 (nestedDiscValuation a ha c hc₀ hc₁ hac hcc f)) :=
  tendsto_discGauss a ha c hc₀ hc₁ hac hcc f

/-- The valuation of the discs takes the value `‖x‖` on the constant `x`. -/
@[simp]
theorem nestedDiscValuation_weightedC (x : K) :
    nestedDiscValuation a ha c hc₀ hc₁ hac hcc (C x) = ‖x‖₊ := by
  simp [nestedDiscValuation_apply]

/-- The valuation of the discs takes the value `inf_n max(‖cₙ‖, ‖aₙ - b‖)` on `T - b`. -/
@[simp]
theorem coe_nestedDiscValuation_weightedX_sub_weightedC (b : K) :
    (nestedDiscValuation a ha c hc₀ hc₁ hac hcc (T - C b) : ℝ) = ⨅ n, max ‖c n‖ ‖a n - b‖ := by
  rw [nestedDiscValuation_apply, NNReal.coe_iInf]
  refine iInf_congr fun n ↦ ?_
  simp only [map_sub, taylorHom_weightedX, taylorHom_weightedC]
  rw [show T + C (a n) - C b = T - C (b - a n) by rw [map_sub]; ring,
    coe_closedDiscGaussValuation_weightedX_sub_weightedC, norm_sub_rev b (a n)]

/-- The valuation of the discs is bounded by the Gauss norm of the whole disc. -/
private theorem nestedDiscValuation_le_closedDiscGaussValuation (f : 𝒯 K) :
    nestedDiscValuation a ha c hc₀ hc₁ hac hcc f ≤ closedDiscGaussValuation one_pos le_rfl f := by
  refine (ciInf_le (OrderBot.bddBelow _) 0).trans ?_
  rw [discGauss, Valuation.comap_apply,
    ← closedDiscGaussValuation_taylorHom one_pos le_rfl (fun _ ↦ a 0)
      (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr (ha 0)) (ha 0) f]
  exact closedDiscGaussValuation_le_closedDiscGaussValuation_of_le _ _ le_rfl (hc₁ 0) _

/-- **The valuation of the discs is continuous**, since it is bounded by the Gauss norm of the
whole disc. -/
theorem isContinuous_nestedDiscValuation :
    (nestedDiscValuation a ha c hc₀ hc₁ hac hcc).IsContinuous := by
  refine Valuation.isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  have hγ₀ : (0 : ℝ) < γ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (Metric.ball_mem_nhds (0 : K) (half_pos hγ₀))
  refine AddSubgroup.isOpen_mono
    (H₂ := (nestedDiscValuation a ha c hc₀ hc₁ hac hcc).ltAddSubgroup (Units.mk0 γ hγ))
    (fun f hf ↦ ?_) (isOpen_weightedNhd isWeightFamily_one_weight U.isOpen)
  have hle := closedDiscGaussValuation_le_of_forall_norm_coeff_le one_pos le_rfl (f := f) fun ν ↦
    (mem_ball_zero_iff.mp (hU (by simpa using mem_weightedNhd.mp hf ν))).le
  exact NNReal.coe_lt_coe.mp
    (((NNReal.coe_le_coe.mpr (nestedDiscValuation_le_closedDiscGaussValuation a ha c hc₀ hc₁
      hac hcc f)).trans hle).trans_lt (half_lt_self hγ₀))

/-- **The valuation of the discs is at most one on power-bounded elements** of `K⟨T⟩`. -/
theorem nestedDiscValuation_le_one_of_isPowerBounded {f : 𝒯 K} (hf : IsPowerBounded f) :
    nestedDiscValuation a ha c hc₀ hc₁ hac hcc f ≤ 1 :=
  (nestedDiscValuation_le_closedDiscGaussValuation a ha c hc₀ hc₁ hac hcc f).trans
    (closedDiscGaussValuation_le_one_of_isPowerBounded one_pos le_rfl hf)

/-! ### The point -/

/-- **The point of the closed unit disc attached to a decreasing sequence of discs**
`D(aₙ, |cₙ|)`: the point of `Spa (K⟨T⟩, K⟨T⟩°)` given by `f ↦ inf_n |f|_{D(aₙ, |cₙ|)}`. When `K`
is algebraically closed and the discs have no common point in `K`, it is a point of type (4). -/
noncomputable def nestedDiscPoint : closedPolydisc 1 K :=
  ⟨ofValuation (nestedDiscValuation a ha c hc₀ hc₁ hac hcc), (mem_closedPolydisc_iff _ _ _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_nestedDiscValuation a ha c hc₀ hc₁ hac hcc),
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact nestedDiscValuation_le_one_of_isPowerBounded a ha c hc₀ hc₁ hac hcc
          (mem_powerBoundedSubring.mp hf)⟩⟩

/-- The underlying point in `Spv K⟨T⟩` is defined by the valuation of the discs. -/
theorem nestedDiscPoint_val :
    (nestedDiscPoint a ha c hc₀ hc₁ hac hcc).1 =
      ofValuation (nestedDiscValuation a ha c hc₀ hc₁ hac hcc) :=
  (rfl)

/-- The point compares two series by the valuation of the discs. -/
@[simp]
theorem nestedDiscPoint_vle_iff (f g : 𝒯 K) :
    (nestedDiscPoint a ha c hc₀ hc₁ hac hcc).1.toValuativeRel.vle f g ↔
      nestedDiscValuation a ha c hc₀ hc₁ hac hcc f ≤ nestedDiscValuation a ha c hc₀ hc₁ hac hcc g :=
  by rw [nestedDiscPoint_val, vle_ofValuation]

/-- **The point lies in `D(b, |d|)` exactly when `inf_n max(‖cₙ‖, ‖aₙ - b‖) ≤ ‖d‖` and
`d ≠ 0`.** -/
theorem nestedDiscPoint_mem_closedSubdisc_iff (b d : K) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc ∈ closedSubdisc b d ↔
      ⨅ n, max ‖c n‖ ‖a n - b‖ ≤ ‖d‖ ∧ d ≠ 0 := by
  rw [mem_closedSubdisc, nestedDiscPoint_vle_iff, nestedDiscPoint_vle_iff, map_zero, le_zero_iff,
    nestedDiscValuation_weightedC, nnnorm_eq_zero, ← NNReal.coe_le_coe,
    coe_nestedDiscValuation_weightedX_sub_weightedC, coe_nnnorm]

/-- **The point lies in every disc `D(aₙ, |cₙ|)` of the sequence.** -/
theorem nestedDiscPoint_mem_closedSubdisc (n : ℕ) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc ∈ closedSubdisc (a n) (c n) :=
  (nestedDiscPoint_mem_closedSubdisc_iff a ha c hc₀ hc₁ hac hcc (a n) (c n)).mpr
    ⟨(ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ (norm_nonneg _).trans (le_max_left _ _)⟩
      n).trans (by simp), hc₀ n⟩

/-! ### Comparison with the other points of the disc -/

/-- If `b` lies in every disc and the radii have a positive infimum `ρ`, the valuation of the discs
is the Gauss norm of radius `ρ` about `b`. -/
private theorem nestedDiscValuation_eq_closedDiscGaussValuation {b : K} (hb : ‖b‖ ≤ 1)
    (hbn : ∀ n, ‖b - a n‖ ≤ ‖c n‖) (hρ₀ : 0 < ⨅ n, ‖c n‖) (hρ₁ : ⨅ n, ‖c n‖ ≤ 1) (f : 𝒯 K) :
    nestedDiscValuation a ha c hc₀ hc₁ hac hcc f = closedDiscGaussValuation hρ₀ hρ₁
      (taylorHom (fun _ ↦ b) (fun _ ↦ isPowerBounded_iff_norm_le_one.mpr hb) f) := by
  have hbdd : BddBelow (Set.range fun n ↦ ‖c n‖) :=
    ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
  refine tendsto_nhds_unique (tendsto_discGauss a ha c hc₀ hc₁ hac hcc f) ?_
  simp only [discGauss_eq a ha c hc₀ hc₁ hb (hbn _)]
  exact tendsto_closedDiscGaussValuation hρ₀ (fun n ↦ ciInf_le hbdd n) hc₁
    (tendsto_atTop_ciInf (antitone_nat_of_succ_le hcc) hbdd) _

/-- **The point is the point `η_{b,s}` of the disc `D(b, s)` exactly when `b` lies in every disc
`D(aₙ, |cₙ|)` and `s` is the infimum of their radii.** -/
theorem nestedDiscPoint_eq_discPoint_iff {s : ℝ} (b : K) (hb : ‖b‖ ≤ 1) (hs₀ : 0 < s)
    (hs₁ : s ≤ 1) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc = discPoint b hb hs₀ hs₁ ↔
      (∀ n, ‖b - a n‖ ≤ ‖c n‖) ∧ s = ⨅ n, ‖c n‖ := by
  have hbdd : BddBelow (Set.range fun n ↦ ‖c n‖) :=
    ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
  -- the reverse direction, at the infimum `ρ` of the radii
  have key (hbn : ∀ n, ‖b - a n‖ ≤ ‖c n‖) (hρ₀ : 0 < ⨅ n, ‖c n‖) :
      nestedDiscPoint a ha c hc₀ hc₁ hac hcc =
        discPoint b hb hρ₀ ((ciInf_le hbdd 0).trans (hc₁ 0)) :=
    Subtype.ext <| ext' fun f g ↦ by
      rw [nestedDiscPoint_vle_iff, discPoint_vle_iff,
        nestedDiscValuation_eq_closedDiscGaussValuation a ha c hc₀ hc₁ hac hcc hb hbn hρ₀,
        nestedDiscValuation_eq_closedDiscGaussValuation a ha c hc₀ hc₁ hac hcc hb hbn hρ₀]
  refine ⟨fun h ↦ ?_, fun ⟨hbn, hs⟩ ↦ by subst hs; exact key hbn hs₀⟩
  -- `η_{b,s}` lies in every `D(aₙ, |cₙ|)`, so `b` does and `s ≤ ρ`; then `η_{b,s} = η_{b,ρ}`
  have hmem n := (discPoint_mem_closedSubdisc_iff b hb hs₀ hs₁ (a n) (c n)).mp
    (h ▸ nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n)
  have hbn n := (hmem n).1
  have hsρ : s ≤ ⨅ n, ‖c n‖ := le_ciInf fun n ↦ (hmem n).2
  exact ⟨hbn, ((discPoint_eq_discPoint_iff hb hb hs₀ hs₁ _ _).mp
    (h.symm.trans (key hbn (hs₀.trans_le hsρ)))).1⟩

variable {a c}

/-- **With no common point of the discs in `K`, the point is not a point `η_{b,s}`** (types (2) and
(3)). -/
theorem nestedDiscPoint_ne_discPoint (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) {s : ℝ} (b : K)
    (hb : ‖b‖ ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc ≠ discPoint b hb hs₀ hs₁ := fun h ↦ by
  obtain ⟨n, hn⟩ := hempty b
  exact hn.not_ge (((nestedDiscPoint_eq_discPoint_iff a ha c hc₀ hc₁ hac hcc b hb hs₀ hs₁).mp
    h).1 n)

/-- **With no common point of the discs in `K`, the point is not classical** (type (1)): a
classical point `x_b` lies only in the discs containing `b`. -/
theorem nestedDiscPoint_ne_classicalPoint (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖)
    (x : spa (powerBoundedSubring K)) (b : Fin 1 → K) (hb : ∀ i, IsPowerBounded (b i)) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc ≠ classicalPoint x b hb := fun h ↦ by
  obtain ⟨n, hn⟩ := hempty (b 0)
  exact hn.not_ge ((classicalPoint_mem_closedSubdisc_iff x b hb (a n) (c n)).mp
    (h ▸ nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n)).1

/-- With no common point of the discs in `K`, the point is no specialization of a point `η_{b,r}`:
the discs are open, so `η_{b,r}` would lie in all of them, and then so would `b`. -/
private theorem nestedDiscPoint_ne_of_discPoint_specializes
    (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) {r : ℝ} (b : K) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) {y : closedPolydisc 1 K} (hy : discPoint b hb hr₀ hr₁ ⤳ y) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc ≠ y := fun h ↦ by
  obtain ⟨n, hn⟩ := hempty b
  have hmem := hy.mem_open (isOpen_closedSubdisc (a n) (c n))
    (h ▸ nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n)
  exact hn.not_ge ((discPoint_mem_closedSubdisc_iff b hb hr₀ hr₁ _ _).mp hmem).1

/-- **With no common point of the discs in `K`, the point is not a rank-two point `η_{b,r⁻}`**
just below a point `η_{b,r}` (type (5)). -/
theorem nestedDiscPoint_ne_discPointBelow (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) {r : ℝ}
    (b : K) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc ≠ discPointBelow b hb hr₀ hr₁ :=
  nestedDiscPoint_ne_of_discPoint_specializes ha hc₀ hc₁ hac hcc hempty b hb hr₀ hr₁
    (discPoint_specializes_discPointBelow b hb hr₀ hr₁)

/-- **With no common point of the discs in `K`, the point is not a rank-two point `η_{b,r⁺}`**
just above a point `η_{b,r}` (type (5)). -/
theorem nestedDiscPoint_ne_discPointAbove (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) {r : ℝ}
    (b : K) (hb : ‖b‖ ≤ 1) (hr₀ : 0 < r) (hr₁ : r < 1) :
    nestedDiscPoint a ha c hc₀ hc₁ hac hcc ≠ discPointAbove b hb hr₀ hr₁ :=
  nestedDiscPoint_ne_of_discPoint_specializes ha hc₀ hc₁ hac hcc hempty b hb hr₀ hr₁.le
    (discPoint_specializes_discPointAbove b hb hr₀ hr₁)

/-! ### Existence of points of type (4) -/

omit [NonarchimedeanRing K] [CompleteSpace K] in
variable (K) in
/-- **Decreasing sequences of discs with no common point exist** over an algebraically closed
separable field `K`, such as `ℂ_p` (`PadicComplex.separableSpace`): there are discs
`D(aₙ, |cₙ|)` in the closed unit disc satisfying the hypotheses of `nestedDiscPoint` such that
every `b ∈ K` lies outside one of them. In other words, `K` is not spherically complete. This
specialises `IsUltrametricDist.exists_antitone_closedBall_iInter_eq_empty` to the unit disc. -/
theorem exists_seq_forall_exists_lt_norm_sub [IsAlgClosed K]
    [TopologicalSpace.SeparableSpace K] :
    ∃ a c : ℕ → K, (∀ n, ‖a n‖ ≤ 1) ∧ (∀ n, c n ≠ 0) ∧ (∀ n, ‖c n‖ ≤ 1) ∧
      (∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖) ∧ (∀ n, ‖c (n + 1)‖ ≤ ‖c n‖) ∧
      ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖ := by
  obtain ⟨c, hc, hcI⟩ := NormedField.exists_strictAnti_norm_mem_Ioo_of_isAlgClosed K
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨a, ha₀, hanti, hempty⟩ := IsUltrametricDist.exists_antitone_closedBall_iInter_eq_empty
    hc (by norm_num : (0 : ℝ) < 1 / 2) (fun n ↦ (hcI n).1.le) 0
  -- each centre lies in the ball before it, and so in the first ball `D(0, |c₀|)`
  have hmem {m n : ℕ} (hmn : m ≤ n) : a n ∈ Metric.closedBall (a m) ‖c m‖ :=
    hanti hmn (Metric.mem_closedBall_self (norm_nonneg _))
  refine ⟨a, c, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ (hcI n).2.le, fun n ↦ ?_,
    fun n ↦ (hc n.lt_succ_self).le, fun b ↦ ?_⟩
  · have h := hmem (Nat.zero_le n)
    rw [ha₀, mem_closedBall_zero_iff] at h
    exact h.trans (hcI 0).2.le
  · exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans (hcI n).1)
  · rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp (hmem n.le_succ)
  · have hb : b ∉ ⋂ n, Metric.closedBall (a n) ‖c n‖ := hempty ▸ Set.notMem_empty b
    simpa only [Set.mem_iInter, Metric.mem_closedBall, dist_eq_norm, not_forall, not_le] using hb

variable (K) in
/-- **The closed unit disc over an algebraically closed separable field has points of type (4)**,
for instance over `ℂ_p`: there is a point that is not classical (type (1)), not a point `η_{b,s}`
(types (2) and (3)), and not a rank-two point `η_{b,s⁺}` or `η_{b,s⁻}` (type (5)). It is the point
of a decreasing sequence of discs with no common point (`exists_seq_forall_exists_lt_norm_sub`). -/
theorem exists_forall_ne_classicalPoint_discPoint_discPointAbove_discPointBelow [IsAlgClosed K]
    [TopologicalSpace.SeparableSpace K] :
    ∃ x : closedPolydisc 1 K,
      (∀ y b hb, x ≠ classicalPoint y b hb) ∧
      (∀ (b : K) (hb : ‖b‖ ≤ 1) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s ≤ 1), x ≠ discPoint b hb hs₀ hs₁) ∧
      (∀ (b : K) (hb : ‖b‖ ≤ 1) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1),
        x ≠ discPointAbove b hb hs₀ hs₁) ∧
      ∀ (b : K) (hb : ‖b‖ ≤ 1) (s : ℝ) (hs₀ : 0 < s) (hs₁ : s ≤ 1),
        x ≠ discPointBelow b hb hs₀ hs₁ := by
  obtain ⟨a, c, ha, hc₀, hc₁, hac, hcc, hempty⟩ := exists_seq_forall_exists_lt_norm_sub K
  exact ⟨nestedDiscPoint a ha c hc₀ hc₁ hac hcc,
    nestedDiscPoint_ne_classicalPoint ha hc₀ hc₁ hac hcc hempty,
    fun b hb _ hs₀ hs₁ ↦ nestedDiscPoint_ne_discPoint ha hc₀ hc₁ hac hcc hempty b hb hs₀ hs₁,
    fun b hb _ hs₀ hs₁ ↦ nestedDiscPoint_ne_discPointAbove ha hc₀ hc₁ hac hcc hempty b hb hs₀ hs₁,
    fun b hb _ hs₀ hs₁ ↦ nestedDiscPoint_ne_discPointBelow ha hc₀ hc₁ hac hcc hempty b hb hs₀ hs₁⟩

/-! ### Recognising the point -/

/-- **With no common point of the discs in `K`, `b ↦ η(T - b)` attains no minimum**: if the disc
`D(aₙ, |cₙ|)` avoids `a`, then `η(T - aₙ) ≤ ‖cₙ‖ < ‖aₙ - a‖ = η(T - a)`. -/
theorem not_exists_forall_nestedDiscPoint_vle (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) :
    ¬ ∃ a₀ : K, ∀ b : K,
      (nestedDiscPoint a ha c hc₀ hc₁ hac hcc).1.toValuativeRel.vle (T - C a₀) (T - C b) := by
  rintro ⟨a₀, hmin⟩
  obtain ⟨n, hn⟩ := hempty a₀
  have hmem := nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n
  have h := (valuation_le_iff _ _ _).mpr (hmin (a n))
  rw [valuation_weightedX_sub_weightedC_of_mem_closedSubdisc hmem hn] at h
  have h' := (closedPolydisc_valuation_weightedC_le_iff _ _ _).mp
    (h.trans ((valuation_le_iff _ _ _).mpr ((mem_closedSubdisc _ _ _).mp hmem).1))
  rw [norm_sub_rev] at h'
  exact hn.not_ge h'

/-- **With no common point of the discs in `K`, the point is the only point lying in all of them**,
over an algebraically closed field: a point `x` of the closed unit disc is `η` if and only if
`x ∈ D(aₙ, |cₙ|)` for every `n`. These are the points of type (4) in Wedhorn's Example 7.57. -/
theorem eq_nestedDiscPoint_iff [IsAlgClosed K] (hempty : ∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖)
    (x : closedPolydisc 1 K) :
    x = nestedDiscPoint a ha c hc₀ hc₁ hac hcc ↔ ∀ n, x ∈ closedSubdisc (a n) (c n) := by
  refine ⟨fun h n ↦ h ▸ nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n,
    fun hx ↦ eq_of_forall_valuation_weightedX_sub_weightedC_eq fun b ↦ ?_⟩
  -- a disc `D(aₙ, |cₙ|)` avoiding `b` makes both points take the value of `aₙ - b` on `T - b`
  obtain ⟨n, hn⟩ := hempty b
  refine ⟨a n - b, sub_ne_zero.mpr fun h ↦ ?_,
    valuation_weightedX_sub_weightedC_of_mem_closedSubdisc (hx n) hn,
    valuation_weightedX_sub_weightedC_of_mem_closedSubdisc
      (nestedDiscPoint_mem_closedSubdisc a ha c hc₀ hc₁ hac hcc n) hn⟩
  rw [h, sub_self, norm_zero] at hn
  exact (norm_nonneg _).not_gt hn

/-! ### Points without a minimum on linear polynomials -/

/-- **The points of type (4) of the closed unit disc**, over an algebraically closed complete
nonarchimedean field: a point `x` is the point attached to a decreasing sequence of discs with no
common point in `K` if and only if `b ↦ x(T - b)` attains no minimum. -/
theorem exists_eq_nestedDiscPoint_iff [IsAlgClosed K] (x : closedPolydisc 1 K) :
    (∃ (a : ℕ → K) (ha : ∀ n, ‖a n‖ ≤ 1) (c : ℕ → K) (hc₀ : ∀ n, c n ≠ 0)
      (hc₁ : ∀ n, ‖c n‖ ≤ 1) (hac : ∀ n, ‖a (n + 1) - a n‖ ≤ ‖c n‖)
      (hcc : ∀ n, ‖c (n + 1)‖ ≤ ‖c n‖),
      (∀ b : K, ∃ n, ‖c n‖ < ‖b - a n‖) ∧ x = nestedDiscPoint a ha c hc₀ hc₁ hac hcc) ↔
    ¬ ∃ a₀ : K, ∀ b : K, x.1.toValuativeRel.vle (T - C a₀) (T - C b) := by
  refine ⟨fun ⟨a, ha, c, hc₀, hc₁, hac, hcc, hempty, hx⟩ ↦ ?_, fun hmin ↦ ?_⟩
  · subst hx
    exact not_exists_forall_nestedDiscPoint_vle ha hc₀ hc₁ hac hcc hempty
  obtain ⟨a, c, ha, hc₀, hc₁, hac, hcc, hempty, hx⟩ := exists_forall_mem_closedSubdisc hmin
  exact ⟨a, ha, c, hc₀, hc₁, hac, hcc, hempty,
    (eq_nestedDiscPoint_iff ha hc₀ hc₁ hac hcc hempty x).mpr hx⟩

end TauCeti.ValuationSpectrum
