/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

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
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.continuousOn`: piecewise `C^n` regularity implies
  continuity on the whole interval.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.trans_contMDiffOn` and
  `TauCeti.Manifold.IsPiecewiseContMDiffOn.mono`: appending a `C^n` piece and restricting to a
  nondegenerate subinterval preserve piecewise `C^n` regularity.

* `TauCeti.Manifold.IsPiecewiseContMDiffOn.trans`: glue adjacent piecewise restrictions.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.prodMk`: pair curves with possibly different
  witnessing partitions, obtaining a common smooth partition for both.

This is a metric-independent finite-partition regularity API for curves in a manifold: it only
involves the differentiable structure, so that Riemannian length and distance comparisons can be
built on top of it by integrating along the pieces. The explicit-partition subinterval induction
follows the pattern of the Apache-2.0
[`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
formalization, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, as used in
`TauCeti/Geometry/Manifold/Riemannian/EDistComparison.lean`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 1, Definition 2.9 and Chapter 7, Section 2.
-/

public section

open Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
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
        ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ (Icc (τ i.castSucc) (τ i.succ))

/-- Extract a strict partition witnessing piecewise `C^n` regularity, together with the
`C^n` restriction on each closed piece. -/
theorem IsPiecewiseContMDiffOn.exists_partition (h : IsPiecewiseContMDiffOn I n γ a b) :
    ∃ (k : ℕ) (τ : Fin (k + 2) → ℝ),
      τ 0 = a ∧
        τ (Fin.last (k + 1)) = b ∧
        (∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) ∧
        ∀ i : Fin (k + 1),
          ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ
            (Icc (τ i.castSucc) (τ i.succ)) :=
  h

/-- A strict finite partition on whose pieces a path is `C^n` witnesses piecewise `C^n`
regularity. -/
theorem IsPiecewiseContMDiffOn.of_partition {k : ℕ} (τ : Fin (k + 2) → ℝ)
    (hτa : τ 0 = a) (hτb : τ (Fin.last (k + 1)) = b)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ)
    (hγ : ∀ i : Fin (k + 1),
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ (Icc (τ i.castSucc) (τ i.succ))) :
    IsPiecewiseContMDiffOn I n γ a b :=
  ⟨k, τ, hτa, hτb, hτ, hγ⟩

/-- The endpoints of a piecewise smooth path are strictly ordered. -/
theorem IsPiecewiseContMDiffOn.lt (h : IsPiecewiseContMDiffOn I n γ a b) : a < b := by
  obtain ⟨k, τ, rfl, rfl, hτ, -⟩ := h
  exact (Fin.strictMono_iff_lt_succ.mpr hτ) Fin.last_pos'

/-- A `C^n` path on a nondegenerate interval is piecewise `C^n`, witnessed by the partition
consisting only of its two endpoints. -/
theorem IsPiecewiseContMDiffOn.of_contMDiffOn (hab : a < b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ (Icc a b)) :
    IsPiecewiseContMDiffOn I n γ a b := by
  let τ : Fin 2 → ℝ := ![a, b]
  refine ⟨0, τ, ?_, ?_, ?_, ?_⟩
  · simp [τ]
  · simp [τ]
  · intro i
    fin_cases i
    simpa [τ] using hab
  · intro i
    fin_cases i
    simpa [τ] using hγ

/-- Restricting the requested differentiability order preserves piecewise smoothness. -/
theorem IsPiecewiseContMDiffOn.of_le {m : ℕ∞ω} (h : IsPiecewiseContMDiffOn I n γ a b)
    (hmn : m ≤ n) : IsPiecewiseContMDiffOn I m γ a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hγ⟩ := h
  exact ⟨k, τ, hτa, hτb, hτ, fun i ↦ (hγ i).of_le hmn⟩

/-- Continuity glues across a finite ordered partition. This is the induction underlying
`IsPiecewiseContMDiffOn.continuousOn`. -/
private theorem continuousOn_Icc_of_partition
    {r : ℕ} (τ : Fin (r + 1) → ℝ)
    (hτ : ∀ i : Fin r, τ i.castSucc ≤ τ i.succ)
    (hγ : ∀ i : Fin r, ContinuousOn γ (Icc (τ i.castSucc) (τ i.succ))) :
    ContinuousOn γ (Icc (τ 0) (τ (Fin.last r))) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hτmono : Monotone τ := Fin.monotone_iff_le_succ.mpr hτ
      have hfirst : τ 0 ≤ τ (Fin.last r).castSucc := hτmono (Fin.zero_le _)
      rw [← Fin.succ_last r]
      rw [← Icc_union_Icc_eq_Icc
        hfirst (hτ (Fin.last r))]
      rw [continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc]
      refine ⟨ih (fun i ↦ τ i.castSucc) (fun i ↦ ?_) (fun i ↦ ?_), ?_⟩
      · simpa only [Fin.succ_castSucc] using hτ i.castSucc
      · simpa only [Fin.succ_castSucc] using hγ i.castSucc
      · simpa using hγ (Fin.last r)

/-- Piecewise `C^n` regularity implies continuity on the whole interval. -/
theorem IsPiecewiseContMDiffOn.continuousOn (h : IsPiecewiseContMDiffOn I n γ a b) :
    ContinuousOn γ (Icc a b) := by
  obtain ⟨k, τ, hτa, hτb, hτ, hγ⟩ := h
  rw [← hτa, ← hτb]
  exact continuousOn_Icc_of_partition τ (fun i ↦ (hτ i).le)
    (fun i ↦ (hγ i).continuousOn)

/-- Appending a `C^n` piece to a piecewise `C^n` path gives a piecewise `C^n` path: the new
vertex is added at the end of a witnessing partition. -/
theorem IsPiecewiseContMDiffOn.trans_contMDiffOn (h : IsPiecewiseContMDiffOn I n γ a b) {c : ℝ}
    (hbc : b < c) (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ (Icc b c)) :
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

/-- Restriction to a subinterval, along an explicit partition. This is the induction underlying
`IsPiecewiseContMDiffOn.mono`. -/
private theorem isPiecewiseContMDiffOn_of_partition_of_subset :
    ∀ {k : ℕ} (τ : Fin (k + 2) → ℝ), (∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) →
      (∀ i : Fin (k + 1),
        ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ (Icc (τ i.castSucc) (τ i.succ))) →
      ∀ {s t : ℝ}, τ 0 ≤ s → s < t → t ≤ τ (Fin.last (k + 1)) →
        IsPiecewiseContMDiffOn I n γ s t := by
  intro k
  induction k with
  | zero =>
      intro τ _ hγ s t hs hst ht
      exact .of_contMDiffOn hst
        ((hγ 0).mono (Icc_subset_Icc (by simpa using hs) (by simpa using ht)))
  | succ k ih =>
      intro τ hτ hγ s t hs hst ht
      have ht' : t ≤ τ (Fin.last (k + 1)).succ := by simpa only [Fin.succ_last] using ht
      -- the partition with its last vertex removed
      have hτ' : ∀ i : Fin (k + 1), τ i.castSucc.castSucc < τ i.castSucc.succ := fun i ↦ by
        simpa only [Fin.succ_castSucc] using hτ i.castSucc
      have hγ' : ∀ i : Fin (k + 1), ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ
          (Icc (τ i.castSucc.castSucc) (τ i.castSucc.succ)) := fun i ↦ by
        simpa only [Fin.succ_castSucc] using hγ i.castSucc
      rcases le_or_gt t (τ (Fin.last (k + 1)).castSucc) with htm | hmt
      · exact ih (fun i ↦ τ i.castSucc) hτ' hγ' hs hst htm
      rcases le_or_gt (τ (Fin.last (k + 1)).castSucc) s with hms | hsm
      · exact .of_contMDiffOn hst ((hγ (Fin.last (k + 1))).mono (Icc_subset_Icc hms ht'))
      · exact (ih (fun i ↦ τ i.castSucc) hτ' hγ' hs hsm le_rfl).trans_contMDiffOn hmt
          ((hγ (Fin.last (k + 1))).mono (Icc_subset_Icc le_rfl ht'))

/-- A piecewise `C^n` path is piecewise `C^n` on every nondegenerate subinterval of its parameter
interval. -/
theorem IsPiecewiseContMDiffOn.mono (h : IsPiecewiseContMDiffOn I n γ a b) {s t : ℝ}
    (has : a ≤ s) (hst : s < t) (htb : t ≤ b) : IsPiecewiseContMDiffOn I n γ s t := by
  obtain ⟨k, τ, hτa, hτb, hτ, hγ⟩ := h
  exact isPiecewiseContMDiffOn_of_partition_of_subset τ hτ hγ (hτa ▸ has) hst (hτb ▸ htb)

/-- Induction over the smooth pieces of a piecewise `C^n` curve. The property may depend
on the interval, and the gluing step has strictly ordered endpoints. -/
@[elab_as_elim]
theorem IsPiecewiseContMDiffOn.induction_on {P : ℝ → ℝ → Prop}
    (h : IsPiecewiseContMDiffOn I n γ a b)
    (single : ∀ u v, u < v → ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc u v) → P u v)
    (join : ∀ u v w, u < v → v < w → P u v → P v w → P u w) : P a b := by
  obtain ⟨k, τ, rfl, rfl, hτ, hγ⟩ := h
  suffices ∀ (k : ℕ) (τ : Fin (k + 2) → ℝ),
      (∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) →
      (∀ i : Fin (k + 1), ContMDiffOn 𝓘(ℝ, ℝ) I n γ
        (Icc (τ i.castSucc) (τ i.succ))) → P (τ 0) (τ (Fin.last (k + 1))) from
    this k τ hτ hγ
  intro k
  induction k with
  | zero =>
      intro τ hτ hγ
      exact single _ _ (hτ 0) (hγ 0)
  | succ k ih =>
      intro τ hτ hγ
      have hmono := Fin.strictMono_iff_lt_succ.mpr hτ
      have hfirst : τ 0 < τ (Fin.last (k + 1)).castSucc :=
        hmono (by simp only [Fin.lt_def, Fin.val_zero, Fin.val_castSucc, Fin.val_last]; omega)
      apply join _ (τ (Fin.last (k + 1)).castSucc) _
        hfirst (by simpa using hτ (Fin.last (k + 1)))
      · apply ih (fun i ↦ τ i.castSucc)
        · intro i
          simpa only [Fin.succ_castSucc] using hτ i.castSucc
        · intro i
          simpa only [Fin.succ_castSucc] using hγ i.castSucc
      · exact single _ _ (hτ (Fin.last (k + 1))) (hγ (Fin.last (k + 1)))

/-- Concatenating adjacent piecewise `C^n` restrictions of the same curve preserves
piecewise `C^n` regularity. The witnessing partitions may be different. -/
theorem IsPiecewiseContMDiffOn.trans {c : ℝ} (h : IsPiecewiseContMDiffOn I n γ a b)
    (h' : IsPiecewiseContMDiffOn I n γ b c) : IsPiecewiseContMDiffOn I n γ a c := by
  exact h'.induction_on
    (P := fun u v ↦ IsPiecewiseContMDiffOn I n γ a u → IsPiecewiseContMDiffOn I n γ a v)
    (fun _ _ huv hγ h ↦ h.trans_contMDiffOn huv hγ)
    (fun _ _ _ _ _ ih₁ ih₂ h ↦ ih₂ (ih₁ h)) h

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {η : ℝ → N}

/-- Pairing a `C^n` curve with a piecewise `C^n` curve gives a piecewise `C^n` curve. -/
private theorem IsPiecewiseContMDiffOn.prodMk_of_contMDiffOn
    (hη : IsPiecewiseContMDiffOn J n η a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc a b)) :
    IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) a b := by
  have h : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc a b) →
      IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) a b := by
    refine hη.induction_on (P := fun u v ↦
      ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc u v) →
        IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) u v) ?_ ?_
    · exact fun _ _ huv hη hγ ↦ .of_contMDiffOn huv (hγ.prodMk hη)
    · intro u v w huv hvw ih₁ ih₂ hγ
      exact (ih₁ (hγ.mono (Icc_subset_Icc le_rfl hvw.le))).trans
        (ih₂ (hγ.mono (Icc_subset_Icc huv.le le_rfl)))
  exact h hγ

/-- Pairing piecewise `C^n` curves preserves piecewise regularity, without requiring their
original partitions to agree. The paired curve supplies a common smooth partition. -/
theorem IsPiecewiseContMDiffOn.prodMk (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hη : IsPiecewiseContMDiffOn J n η a b) :
    IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) a b := by
  have h : IsPiecewiseContMDiffOn J n η a b →
      IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) a b := by
    refine hγ.induction_on (P := fun u v ↦ IsPiecewiseContMDiffOn J n η u v →
      IsPiecewiseContMDiffOn (I.prod J) n (fun t ↦ (γ t, η t)) u v) ?_ ?_
    · exact fun _ _ _ hγ hη ↦ hη.prodMk_of_contMDiffOn hγ
    · intro u v w huv hvw ih₁ ih₂ hη
      exact (ih₁ (hη.mono le_rfl huv hvw.le)).trans
        (ih₂ (hη.mono huv.le hvw le_rfl))
  exact h hη

end TauCeti.Manifold
