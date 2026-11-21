/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Piecewise smooth paths in a manifold

This file defines piecewise `C^n` regularity for a path on a compact real interval using a finite
strict partition. The predicate retains the partition only existentially. Thus two proofs using
different partitions are proofs of the same property of the underlying path, rather than distinct
bundled paths carrying irrelevant partition data.

## Main definitions

* `TauCeti.Manifold.IsPiecewiseContMDiffOn`: a path is `C^n` on the pieces of some finite strict
  partition of `[a, b]`.

## Main results

* `TauCeti.Manifold.IsPiecewiseContMDiffOn.exists_partition`: extract a witnessing strict
  partition and the piecewise regularity facts.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.of_partition`: construct piecewise regularity from a
  strict partition and regularity on each piece.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.induction_on`: prove an interval-indexed property by
  checking it on `C^n` pieces and gluing it across adjacent intervals.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.continuousOn`: piecewise `C^n` regularity implies
  continuity on the whole interval.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.trans_contMDiffOn` and
  `TauCeti.Manifold.IsPiecewiseContMDiffOn.mono`: appending a `C^n` piece and restricting to a
  nondegenerate subinterval preserve piecewise `C^n` regularity.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.trans`: glue adjacent piecewise restrictions.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.congr`: piecewise `C^n` regularity on `[a, b]` only
  depends on the values of the path on `[a, b]`.
* `TauCeti.Manifold.eventually_isPiecewiseContMDiffOn_of_two_pieces`: the nearby curves of a
  family of curves broken at one parameter, whose two pieces are jointly `C^k` along the central
  curve for a natural number `k`, are piecewise `C^k`.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.prodMk`: pair curves with possibly different
  witnessing partitions, obtaining a common smooth partition for both.

This is a metric-independent finite-partition regularity API for curves in a manifold: it only
involves the differentiable structure, so that Riemannian length and distance comparisons can be
built on top of it by integrating along the pieces. The induction over an explicit partition
follows the pattern of the Apache-2.0
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
formalization, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, as used in
`TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 1, Definition 2.9 and Chapter 7, Section 2.
-/

public section

open Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {γ : ℝ → M} {a b : ℝ}

/-- A path is piecewise `C^n` on `[a, b]` if there is a nonempty finite strict partition from
`a` to `b` such that the path is `C^n` on every closed piece. The partition has `k + 1` pieces
and `k + 2` vertices, so the definition includes the one-piece case but excludes a vacuous
zero-piece witness.

The partition is existential data because it witnesses a property of `γ`; it is not part of the
identity of a path. In particular, refining a partition does not create a different object. -/
def IsPiecewiseContMDiffOn (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∃ (k : ℕ) (τ : Fin (k + 2) → ℝ),
    τ 0 = a ∧
      τ (Fin.last (k + 1)) = b ∧
      (∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) ∧
      ∀ i : Fin (k + 1),
        ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc (τ i.castSucc) (τ i.succ))

/-- Extract a strict partition witnessing piecewise `C^n` regularity, together with the
`C^n` restriction on each closed piece. -/
theorem IsPiecewiseContMDiffOn.exists_partition (h : IsPiecewiseContMDiffOn I n γ a b) :
    ∃ (k : ℕ) (τ : Fin (k + 2) → ℝ),
      τ 0 = a ∧
        τ (Fin.last (k + 1)) = b ∧
        (∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) ∧
        ∀ i : Fin (k + 1),
          ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc (τ i.castSucc) (τ i.succ)) :=
  h

/-- A strict finite partition on whose pieces a path is `C^n` witnesses piecewise `C^n`
regularity. -/
theorem IsPiecewiseContMDiffOn.of_partition {k : ℕ} (τ : Fin (k + 2) → ℝ)
    (hτa : τ 0 = a) (hτb : τ (Fin.last (k + 1)) = b)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ)
    (hγ : ∀ i : Fin (k + 1),
      ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc (τ i.castSucc) (τ i.succ))) :
    IsPiecewiseContMDiffOn I n γ a b :=
  ⟨k, τ, hτa, hτb, hτ, hγ⟩

/-- A `C^n` path on a nondegenerate interval is piecewise `C^n`, witnessed by the partition
consisting only of its two endpoints. -/
theorem IsPiecewiseContMDiffOn.of_contMDiffOn (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc a b)) :
    IsPiecewiseContMDiffOn I n γ a b :=
  ⟨0, ![a, b], rfl, rfl, Fin.forall_fin_one.2 (by simpa), Fin.forall_fin_one.2 (by simpa)⟩

/-- Restricting the requested differentiability order preserves piecewise smoothness. -/
theorem IsPiecewiseContMDiffOn.of_le {m : ℕ∞ω} (h : IsPiecewiseContMDiffOn I n γ a b)
    (hmn : m ≤ n) : IsPiecewiseContMDiffOn I m γ a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hγ⟩ := h
  exact ⟨k, τ, hτa, hτb, hτ, fun i ↦ (hγ i).of_le hmn⟩

/-- Induction over the smooth pieces of a piecewise `C^n` curve. The property may depend
on the interval, and the gluing step has strictly ordered endpoints. -/
@[elab_as_elim]
theorem IsPiecewiseContMDiffOn.induction_on {P : ℝ → ℝ → Prop}
    (h : IsPiecewiseContMDiffOn I n γ a b)
    (single : ∀ u v, u < v → ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc u v) → P u v)
    (join : ∀ u v w, u < v → v < w → P u v → P v w → P u w) : P a b := by
  obtain ⟨k, τ, rfl, rfl, hτ, hγ⟩ := h
  induction k with
  | zero => exact single _ _ (hτ 0) (hγ 0)
  | succ k ih =>
      -- split off the last piece; the remaining vertices form a partition with one piece less
      rw [← Fin.succ_last]
      refine join _ (τ (Fin.last (k + 1)).castSucc) _
        (Fin.strictMono_iff_lt_succ.mpr hτ (Fin.castSucc_pos Fin.last_pos'))
        (hτ (Fin.last (k + 1))) ?_ (single _ _ (hτ (Fin.last (k + 1))) (hγ (Fin.last (k + 1))))
      exact ih (fun i ↦ τ i.castSucc)
        (fun i ↦ by simpa only [Fin.succ_castSucc] using hτ i.castSucc)
        fun i ↦ by simpa only [Fin.succ_castSucc] using hγ i.castSucc

/-- The endpoints of a piecewise smooth path are strictly ordered. -/
theorem IsPiecewiseContMDiffOn.lt (h : IsPiecewiseContMDiffOn I n γ a b) : a < b :=
  h.induction_on (fun _ _ huv _ ↦ huv) fun _ _ _ huv hvw _ _ ↦ huv.trans hvw

/-- Piecewise `C^n` regularity implies continuity on the whole interval. -/
theorem IsPiecewiseContMDiffOn.continuousOn (h : IsPiecewiseContMDiffOn I n γ a b) :
    ContinuousOn γ (Icc a b) :=
  h.induction_on (fun _ _ _ hγ ↦ hγ.continuousOn) fun _ _ _ huv hvw h₁ h₂ ↦
    Icc_union_Icc_eq_Icc huv.le hvw.le ▸ h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc

/-- Appending a `C^n` piece to a piecewise `C^n` path gives a piecewise `C^n` path: the new
vertex is added at the end of a witnessing partition. -/
theorem IsPiecewiseContMDiffOn.trans_contMDiffOn (h : IsPiecewiseContMDiffOn I n γ a b) {c : ℝ}
    (hbc : b < c) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc b c)) :
    IsPiecewiseContMDiffOn I n γ a c := by
  obtain ⟨k, τ, hτa, hτb, hτ, hpieces⟩ := h
  refine ⟨k + 1, Fin.snoc τ c, ?_, ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · simpa only [← Fin.castSucc_zero, Fin.snoc_castSucc] using hτa
  · exact Fin.snoc_last _ _
  · refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last, hτb] using hbc
    · simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using hτ j
  · refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last, hτb] using hγ
    · simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using hpieces j

/-- Concatenating adjacent piecewise `C^n` restrictions of the same curve preserves
piecewise `C^n` regularity. The witnessing partitions may be different. -/
theorem IsPiecewiseContMDiffOn.trans {c : ℝ} (h : IsPiecewiseContMDiffOn I n γ a b)
    (h' : IsPiecewiseContMDiffOn I n γ b c) : IsPiecewiseContMDiffOn I n γ a c :=
  h'.induction_on
    (P := fun u v ↦ IsPiecewiseContMDiffOn I n γ a u → IsPiecewiseContMDiffOn I n γ a v)
    (fun _ _ huv hγ h ↦ h.trans_contMDiffOn huv hγ)
    (fun _ _ _ _ _ ih₁ ih₂ h ↦ ih₂ (ih₁ h)) h

/-- A piecewise `C^n` path is piecewise `C^n` on every nondegenerate subinterval of its parameter
interval. -/
theorem IsPiecewiseContMDiffOn.mono (h : IsPiecewiseContMDiffOn I n γ a b) {s t : ℝ}
    (has : a ≤ s) (hst : s < t) (htb : t ≤ b) : IsPiecewiseContMDiffOn I n γ s t :=
  h.induction_on
    (P := fun u v ↦ ∀ s t, u ≤ s → s < t → t ≤ v → IsPiecewiseContMDiffOn I n γ s t)
    (fun _ _ _ hγ s t hus hst htv ↦ .of_contMDiffOn hst (hγ.mono (Icc_subset_Icc hus htv)))
    (fun _ v _ _ _ ih₁ ih₂ s t hus hst htw ↦ by
      rcases le_or_gt t v with htv | hvt
      · exact ih₁ s t hus hst htv
      rcases le_or_gt v s with hvs | hsv
      · exact ih₂ s t hvs hst htw
      · exact (ih₁ s v hus hsv le_rfl).trans (ih₂ v t le_rfl hvt htw))
    s t has hst htb

/-- Piecewise `C^n` regularity on `[a, b]` only depends on the values of the path on `[a, b]`. -/
theorem IsPiecewiseContMDiffOn.congr {δ : ℝ → M} (h : IsPiecewiseContMDiffOn I n γ a b)
    (he : EqOn δ γ (Icc a b)) : IsPiecewiseContMDiffOn I n δ a b :=
  h.induction_on (P := fun u v ↦ EqOn δ γ (Icc u v) → IsPiecewiseContMDiffOn I n δ u v)
    (fun _ _ huv hγ he ↦ .of_contMDiffOn huv (hγ.congr fun _ ht ↦ he ht))
    (fun _ _ _ huv hvw ih₁ ih₂ he ↦ (ih₁ (he.mono (Icc_subset_Icc le_rfl hvw.le))).trans
      (ih₂ (he.mono (Icc_subset_Icc huv.le le_rfl)))) he

/-- Let `G₁` and `G₂` be two-parameter families of curves which are jointly `C^k`, for a natural
number `k`, along their central curves on `[a, c]` and on `[c, b]` respectively, where
`a < c < b`. If for parameters `q` near `0` the curve `F q` agrees with `G₁ q` on `[a, c]` and
with `G₂ q` on `[c, b]`, then `F q` is piecewise `C^k` on `[a, b]` for `q` near `0`. -/
theorem eventually_isPiecewiseContMDiffOn_of_two_pieces {k : ℕ} [IsManifold I k M]
    {F G₁ G₂ : ℝ → ℝ → M} {c : ℝ} (hac : a < c) (hcb : c < b)
    (hG₁ : ∀ t ∈ uIcc a c,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I k (fun z : ℝ × ℝ ↦ G₁ z.1 z.2) (0, t))
    (hG₂ : ∀ t ∈ uIcc c b,
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I k (fun z : ℝ × ℝ ↦ G₂ z.1 z.2) (0, t))
    (hF : ∀ᶠ q in 𝓝 0, EqOn (F q) (G₁ q) (uIcc a c) ∧ EqOn (F q) (G₂ q) (uIcc c b)) :
    ∀ᶠ q in 𝓝 0, IsPiecewiseContMDiffOn I k (F q) a b := by
  obtain ⟨U₁, V₁, hU₁, -, h0U₁, hsub₁, hUV₁⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hG₁
  obtain ⟨U₂, V₂, hU₂, -, h0U₂, hsub₂, hUV₂⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn isCompact_uIcc (by simp) hG₂
  filter_upwards [hU₁.mem_nhds h0U₁, hU₂.mem_nhds h0U₂, hF] with q hq₁ hq₂ hqF
  have h₁ : ContMDiffOn 𝓘(ℝ, ℝ) I k (G₁ q) (Icc a c) :=
    hUV₁.comp (contDiff_prodMk_right q).contMDiff.contMDiffOn
      fun t ht ↦ ⟨hq₁, hsub₁ (by rwa [uIcc_of_le hac.le])⟩
  have h₂ : ContMDiffOn 𝓘(ℝ, ℝ) I k (G₂ q) (Icc c b) :=
    hUV₂.comp (contDiff_prodMk_right q).contMDiff.contMDiffOn
      fun t ht ↦ ⟨hq₂, hsub₂ (by rwa [uIcc_of_le hcb.le])⟩
  rw [uIcc_of_le hac.le, uIcc_of_le hcb.le] at hqF
  exact ((IsPiecewiseContMDiffOn.of_contMDiffOn hac h₁).congr hqF.1).trans
    ((IsPiecewiseContMDiffOn.of_contMDiffOn hcb h₂).congr hqF.2)

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {η : ℝ → N}

/-- Pairing a `C^n` curve with a piecewise `C^n` curve gives a piecewise `C^n` curve. -/
private theorem IsPiecewiseContMDiffOn.prodMk_of_contMDiffOn
    (hη : IsPiecewiseContMDiffOn J n η a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc a b)) :
    IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) a b :=
  hη.induction_on (P := fun u v ↦ ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc u v) →
      IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) u v)
    (fun _ _ huv hη hγ ↦ .of_contMDiffOn huv (hγ.prodMk hη))
    (fun _ _ _ huv hvw ih₁ ih₂ hγ ↦ (ih₁ (hγ.mono (Icc_subset_Icc le_rfl hvw.le))).trans
      (ih₂ (hγ.mono (Icc_subset_Icc huv.le le_rfl)))) hγ

/-- Pairing piecewise `C^n` curves preserves piecewise regularity, without requiring their
original partitions to agree. The paired curve supplies a common smooth partition. -/
theorem IsPiecewiseContMDiffOn.prodMk (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hη : IsPiecewiseContMDiffOn J n η a b) :
    IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) a b :=
  hγ.induction_on (P := fun u v ↦ IsPiecewiseContMDiffOn J n η u v →
      IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) u v)
    (fun _ _ _ hγ hη ↦ hη.prodMk_of_contMDiffOn hγ)
    (fun _ _ _ huv hvw ih₁ ih₂ hη ↦ (ih₁ (hη.mono le_rfl huv hvw.le)).trans
      (ih₂ (hη.mono huv.le hvw le_rfl))) hη

end TauCeti.Manifold
