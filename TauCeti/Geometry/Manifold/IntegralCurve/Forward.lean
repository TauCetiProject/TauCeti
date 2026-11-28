/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Geometry.Manifold.IntegralCurve.Transform
public import TauCeti.Geometry.Manifold.IntegralCurve.Interval

/-!
# Forward integral curves

On a manifold with boundary, the integral curves of a vector field pointing inward along the
boundary are naturally defined forward in time only: through a boundary point there is an integral
curve on `[0, ε)`, but none on `(-ε, 0]`. This file treats integral curves on the closed half-line
`[0, ∞)`, for any model with corners.

The **forward integral curve** `TauCeti.forwardIntegralCurve v x` is an integral curve of `v` on
`[0, ∞)` starting at `x`, whenever one exists (`TauCeti.isMIntegralCurveOn_forwardIntegralCurve`),
and the constant curve at `x` otherwise. For a separated manifold and a `C¹` field it is the only
one: every integral curve on `[0, ∞)` agrees with the forward integral curve through its starting
point (`IsMIntegralCurveOn.eqOn_forwardIntegralCurve`), and forward integral curves satisfy the
flow law (`TauCeti.forwardIntegralCurve_add`). Uniqueness of integral curves on intervals
with endpoints (`IsMIntegralCurveOn.eqOn_of_isPreconnected`) holds at boundary points, so no
interior-point hypothesis enters.

Forward integral curves exist once short ones exist for a uniform time. If every point is the
start of an integral curve on `[0, ε)` for one fixed `ε > 0`, then every point is the start of an
integral curve on `[0, ∞)`, obtained by restarting the short curves and gluing them by uniqueness
(`TauCeti.exists_isMIntegralCurveOn_Ici_of_forall_exists_isMIntegralCurveOn_Ico`). A set `S`
visited by the short curves at all positive times is visited by the long ones at all positive
times as well; for an inward field `S` is the interior of the manifold. This is the forward,
boundary-compatible form of the uniform-time argument of Mathlib's
`exists_isMIntegralCurve_of_isMIntegralCurveOn`.

A forward integral curve of `-v`, run backwards (`IsMIntegralCurveOn.comp_neg`), is a backward
integral curve of `v`.

## Main definitions

* `TauCeti.forwardIntegralCurve v x`: the integral curve of `v` on `[0, ∞)` starting at `x`, when
  one exists.

## Main results

* `TauCeti.isMIntegralCurveOn_forwardIntegralCurve`, `TauCeti.forwardIntegralCurve_zero` and
  `IsMIntegralCurveOn.eqOn_forwardIntegralCurve`: the forward integral curve is an integral curve
  on `[0, ∞)` from `x`, and the only one.
* `TauCeti.forwardIntegralCurve_add`: the flow law of forward integral curves.
* `TauCeti.exists_isMIntegralCurveOn_Ici_of_forall_exists_isMIntegralCurveOn_Ico`: a uniform time
  of forward existence gives forward integral curves on `[0, ∞)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9 (Lemma 9.15, the uniform time lemma).
-/

public noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {s : Set ℝ} {x : M}

namespace TauCeti

open Classical in
/-- The **forward integral curve** of `v` from `x`: an integral curve of `v` on `[0, ∞)` taking
the value `x` at time `0`, chosen arbitrarily, if one exists, and the constant curve at `x`
otherwise. Its values at negative times are not constrained. On a separated manifold with a `C¹`
field it is the unique such curve on `[0, ∞)` (`IsMIntegralCurveOn.eqOn_forwardIntegralCurve`). -/
def forwardIntegralCurve (v : (x : M) → TangentSpace I x) (x : M) : ℝ → M :=
  if h : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ici 0) then h.choose else fun _ ↦ x

/-- The forward integral curve from `x` starts at `x`. -/
@[simp]
theorem forwardIntegralCurve_zero (v : (x : M) → TangentSpace I x) (x : M) :
    forwardIntegralCurve v x 0 = x := by
  rw [forwardIntegralCurve]
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/-- If no integral curve of `v` on `[0, ∞)` starts at `x`, the forward integral curve is the
constant curve at `x`. -/
theorem forwardIntegralCurve_of_not_exists
    (h : ¬∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ici 0)) :
    forwardIntegralCurve v x = fun _ ↦ x := by
  rw [forwardIntegralCurve, dite_eq_right h]

/-- If some integral curve of `v` on `[0, ∞)` starts at `x`, then so does the forward integral
curve. -/
theorem isMIntegralCurveOn_forwardIntegralCurve
    (h : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ici 0)) :
    IsMIntegralCurveOn (forwardIntegralCurve v x) v (Ici 0) := by
  rw [forwardIntegralCurve, dite_eq_left h]
  exact h.choose_spec.2

end TauCeti

namespace IsMIntegralCurveOn

open TauCeti

/-- **Uniqueness of forward integral curves.** On a separated `C¹` manifold, possibly with
boundary, an integral curve of a `C¹` field on `[0, ∞)` agrees there with the forward integral
curve through its starting point. -/
theorem eqOn_forwardIntegralCurve [IsManifold I 1 M] [T2Space M]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ici 0)) :
    EqOn γ (forwardIntegralCurve v (γ 0)) (Ici 0) :=
  hγ.eqOn_of_isPreconnected (isMIntegralCurveOn_forwardIntegralCurve ⟨γ, rfl, hγ⟩)
    isPreconnected_Ici (mem_Ici.2 le_rfl) (fun _ _ ↦ hv _) (forwardIntegralCurve_zero v _).symm

end IsMIntegralCurveOn

namespace TauCeti

/-- **The flow law of forward integral curves.** On a separated `C¹` manifold, possibly with
boundary, if some integral curve of a `C¹` field `v` on `[0, ∞)` starts at `x`, then following the
forward integral curve from `x` for time `s ≥ 0` and then the one from the point reached for time
`t ≥ 0` is following the forward integral curve from `x` for time `s + t`. -/
theorem forwardIntegralCurve_add [IsManifold I 1 M] [T2Space M]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (h : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ici 0)) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    forwardIntegralCurve v (forwardIntegralCurve v x s) t = forwardIntegralCurve v x (s + t) := by
  -- The forward integral curve from `x`, restarted at time `s`, is an integral curve on `[0, ∞)`.
  have hγ : IsMIntegralCurveOn (forwardIntegralCurve v x ∘ (· + s)) v (Ici 0) :=
    ((isMIntegralCurveOn_forwardIntegralCurve h).comp_add s).mono fun r hr ↦
      show 0 ≤ r + s by linarith [mem_Ici.1 hr]
  have := hγ.eqOn_forwardIntegralCurve hv (mem_Ici.2 ht)
  rw [comp_apply, comp_apply, zero_add, add_comm t s] at this
  exact this.symm

section UniformTime

variable [IsManifold I 1 M] [T2Space M] {S : Set M} {ε : ℝ}

/-- One step of the uniform-time argument: an integral curve on `[0, (k + 1) c]` from every point,
with `c = ε / 2`, extends to an integral curve on `[0, (k + 2) c]` by starting with a short curve
and continuing from its value at time `c`. -/
private theorem exists_isMIntegralCurveOn_Ico_succ
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hε : 0 < ε)
    (h : ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ico 0 ε) ∧ MapsTo γ (Ioo 0 ε) S)
    {k : ℕ}
    (hk : ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ico 0 ((k + 1) * (ε / 2))) ∧
      MapsTo γ (Ioo 0 ((k + 1) * (ε / 2))) S) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ico 0 ((k + 1 + 1) * (ε / 2))) ∧
      MapsTo γ (Ioo 0 ((k + 1 + 1) * (ε / 2))) S := by
  set c := ε / 2 with hc
  have hc0 : 0 < c := half_pos hε
  have hkc : c ≤ (k + 1) * c := le_mul_of_one_le_left hc0.le (by linarith [k.cast_nonneg (α := ℝ)])
  obtain ⟨δ, hδ0, hδ, hδS⟩ := h x
  obtain ⟨γ, hγ0, hγ, hγS⟩ := hk (δ c)
  -- The restarted short curve agrees with the long curve from `δ c` on `[0, c)`.
  have hagree : EqOn (δ ∘ (· + c)) γ (Ico 0 c) := by
    refine IsMIntegralCurveOn.eqOn_of_isPreconnected ?_ (hγ.mono (Ico_subset_Ico_right hkc))
      isPreconnected_Ico (left_mem_Ico.2 hc0) (fun _ _ ↦ hv _) (by rw [comp_apply, zero_add, hγ0])
    exact (hδ.comp_add c).mono fun t ht ↦ ⟨by simp only [mem_Ico] at ht ⊢; linarith,
      by simp only [mem_Ico] at ht ⊢; linarith⟩
  -- The glued curve: the short curve up to time `ε`, the restarted long curve afterwards.
  let η : ℝ → M := fun t ↦ if t < ε then δ t else γ (t - c)
  have hηδ : EqOn η δ (Ico 0 ε) := fun t ht ↦ ite_eq_left ht.2
  have hηγ : EqOn η (γ ∘ (· + -c)) (Ico c ((k + 1 + 1) * c)) := by
    intro t ht
    by_cases htε : t < ε
    · simp only [η, ite_eq_left htε, comp_apply, ← sub_eq_add_neg]
      have := hagree (x := t - c) ⟨by linarith [ht.1], by linarith⟩
      simpa only [comp_apply, sub_add_cancel] using this
    · simp only [η, ite_eq_right htε, comp_apply, sub_eq_add_neg]
  have hγ' : IsMIntegralCurveOn (γ ∘ (· + -c)) v (Ico c ((k + 1 + 1) * c)) :=
    (hγ.comp_add (-c)).mono fun t ht ↦ ⟨by simp only [mem_Ico] at ht ⊢; linarith,
      by simp only [mem_Ico] at ht ⊢; linarith⟩
  refine ⟨η, by rw [hηδ ⟨le_rfl, hε⟩, hδ0], ?_, fun t ht ↦ ?_⟩
  · refine IsMIntegralCurveOn.of_forall_mem_nhdsWithin fun t ht ↦ ?_
    by_cases htε : t < ε
    · -- Near a time before `ε`, the glued curve is the short curve.
      refine ⟨Ico 0 ε, mem_nhdsWithin.2 ⟨Iio ε, isOpen_Iio, htε, fun r hr ↦ ⟨hr.2.1, hr.1⟩⟩,
        ⟨ht.1, htε⟩, hδ.congr hηδ⟩
    · -- Near a time after `c`, the glued curve is the restarted long curve.
      have hct : c < t := by linarith
      refine ⟨Ico c ((k + 1 + 1) * c), mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, hct,
        fun r hr ↦ ⟨le_of_lt hr.1, hr.2.2⟩⟩, ⟨hct.le, ht.2⟩, hγ'.congr hηγ⟩
  · by_cases htε : t < ε
    · rw [hηδ ⟨ht.1.le, htε⟩]
      exact hδS ⟨ht.1, htε⟩
    · rw [hηγ ⟨by linarith, ht.2⟩, comp_apply, ← sub_eq_add_neg]
      exact hγS ⟨by linarith, by linarith [ht.2]⟩

/-- **The uniform time lemma, forward in time.** On a separated `C¹` manifold, possibly with
boundary, let `v` be a `C¹` field such that every point is the start of an integral curve on
`[0, ε)`, for one `ε > 0`, which lies in `S` at the positive times. Then every point is the start
of an integral curve on `[0, ∞)` which lies in `S` at all positive times. -/
theorem exists_isMIntegralCurveOn_Ici_of_forall_exists_isMIntegralCurveOn_Ico
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hε : 0 < ε)
    (h : ∀ x, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ico 0 ε) ∧ MapsTo γ (Ioo 0 ε) S)
    (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ici 0) ∧ MapsTo γ (Ioi 0) S := by
  set c := ε / 2
  have hc0 : 0 < c := half_pos hε
  -- Integral curves on `[0, (k + 1) c)` from every point, by induction on `k`.
  have hstep (k : ℕ) (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurveOn γ v (Ico 0 ((k + 1) * c)) ∧ MapsTo γ (Ioo 0 ((k + 1) * c)) S := by
    induction k generalizing x with
    | zero =>
      obtain ⟨γ, hγ0, hγ, hγS⟩ := h x
      have hcε : c ≤ ε := (half_lt_self hε).le
      simp only [Nat.cast_zero, zero_add, one_mul]
      exact ⟨γ, hγ0, hγ.mono (Ico_subset_Ico_right hcε), hγS.mono_left (Ioo_subset_Ioo_right hcε)⟩
    | succ k ih =>
      push_cast
      exact exists_isMIntegralCurveOn_Ico_succ hv hε h ih x
  choose g hg0 hg hgS using fun k ↦ hstep k x
  -- Two of these curves agree on their common interval.
  have hgg {k m : ℕ} (hkm : k ≤ m) : EqOn (g k) (g m) (Ico 0 ((k + 1) * c)) :=
    (hg k).eqOn_of_isPreconnected ((hg m).mono (Ico_subset_Ico_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hkm) hc0.le)))
      isPreconnected_Ico (left_mem_Ico.2 (by positivity)) (fun _ _ ↦ hv _) (by rw [hg0, hg0])
  -- At time `t`, use the curve of index `⌈t / c⌉₊`, whose interval contains `t`.
  have hmem {t : ℝ} (ht : 0 ≤ t) : t ∈ Ico 0 ((⌈t / c⌉₊ + 1) * c) := by
    refine ⟨ht, ?_⟩
    have := Nat.le_ceil (t / c)
    rw [div_le_iff₀ hc0] at this
    nlinarith
  let γ : ℝ → M := fun t ↦ g ⌈t / c⌉₊ t
  have hγg (m : ℕ) : EqOn γ (g m) (Ico 0 ((m + 1) * c)) := by
    intro t ht
    rcases le_total ⌈t / c⌉₊ m with hkm | hmk
    · exact hgg hkm (hmem ht.1)
    · exact (hgg hmk ht).symm
  refine ⟨γ, by rw [hγg 0 ⟨le_rfl, by positivity⟩, hg0], ?_, fun t ht ↦ ?_⟩
  · refine IsMIntegralCurveOn.of_forall_mem_nhdsWithin fun t ht ↦ ?_
    -- Near `t`, the curve is the curve of index `⌈t / c⌉₊ + 1`, whose interval reaches past `t`.
    have hlt : t < (⌈t / c⌉₊ + 1 + 1) * c := by
      have := (hmem (show (0 : ℝ) ≤ t from ht)).2
      nlinarith
    refine ⟨Ico 0 ((⌈t / c⌉₊ + 1 + 1) * c), mem_nhdsWithin.2 ⟨Iio ((⌈t / c⌉₊ + 1 + 1) * c),
      isOpen_Iio, hlt, fun r hr ↦ ⟨hr.2, hr.1⟩⟩, ⟨ht, hlt⟩, ?_⟩
    have := (hg (⌈t / c⌉₊ + 1)).congr (hγg (⌈t / c⌉₊ + 1))
    simpa only [Nat.cast_add, Nat.cast_one] using this
  · rw [hγg _ (hmem (le_of_lt ht))]
    exact hgS _ ⟨ht, (hmem (le_of_lt ht)).2⟩

end UniformTime

end TauCeti
