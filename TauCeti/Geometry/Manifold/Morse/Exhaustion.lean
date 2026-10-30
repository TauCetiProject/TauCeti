/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Order.Interval.Set.Infinite

/-!
# Exhaustion by regular Morse sublevels

A proper Morse function bounded below admits a strictly increasing sequence of regular values
tending to infinity, starting below its global lower bound. Its closed sublevels form a native
`CompactExhaustion`, starting with the empty set and having finitely many critical points at
each stage. These are the levels at which finite critical-band attachments can be iterated.

No second-countability or compactness of the manifold is assumed. The regular values in each
bounded interval are obtained by avoiding the finitely many critical points in its compact
preimage, rather than by Sard's theorem. The exhaustion retains its actual sublevel sets, so
`CompactExhaustion.subset_interior_succ` gives the nesting and
`CompactExhaustion.exists_superset_of_isCompact` places every compact subset in a finite stage.

## Main results

* `TauCeti.IsMorse.exists_isRegularValue_mem_Ioo`: if the band `f ⁻¹' Icc a b` is compact and
  `a < b`, there is a regular value in `Ioo a b`.
* `TauCeti.IsMorse.exists_regular_sublevel_exhaustion`: the regular-level compact exhaustion of
  a proper bounded-below Morse function.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, Theorem 3.5.
-/

public section

open Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {f : M → ℝ}

/-- A compact band of a Morse function contains only finitely many critical values, so there is
a regular value strictly between `a` and `b` whenever `a < b`. -/
theorem IsMorse.exists_isRegularValue_mem_Ioo (hf : IsMorse I f) {a b : ℝ} (hab : a < b)
    (hcompact : IsCompact (f ⁻¹' Icc a b)) :
    ∃ c ∈ Ioo a b, IsRegularValue I 𝓘(ℝ) f c := by
  have hfinite := (hf.finite_criticalPoints_inter hcompact).image f
  obtain ⟨c, hc, hnot⟩ := ((Ioo_infinite hab).sdiff hfinite).nonempty
  refine ⟨c, hc, isRegularValue_iff_notMem_image_criticalPoints.2 ?_⟩
  rintro ⟨x, hx, rfl⟩
  exact hnot ⟨x, ⟨hx, hc.1.le, hc.2.le⟩, rfl⟩

/-- Choose the levels before constructing their compact exhaustion. -/
private theorem IsMorse.exists_regular_levels (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ a : ℕ → ℝ, StrictMono a ∧ Tendsto a atTop atTop ∧
      (∀ n, IsRegularValue I 𝓘(ℝ) f (a n)) ∧ ∀ x, a 0 < f x := by
  obtain ⟨b, hb⟩ := hbdd
  have hbound (x : M) : b ≤ f x := hb (mem_range_self x)
  -- Choose one regular value in each consecutive unit interval above the lower bound.
  have hex (n : ℕ) : ∃ c ∈ Ioo (b + n) (b + n + 1), IsRegularValue I 𝓘(ℝ) f c :=
    hf.exists_isRegularValue_mem_Ioo (by linarith)
      (hp.isCompact_preimage isCompact_Icc)
  choose c hc hcreg using hex
  let a : ℕ → ℝ := fun n ↦ Nat.casesOn n (b - 1) c
  have ha0 : a 0 = b - 1 := rfl
  have hasucc (n : ℕ) : a (n + 1) = c n := rfl
  have hmono : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    cases n with
    | zero => rw [ha0, hasucc]; linarith [(hc 0).1]
    | succ n =>
      rw [hasucc, hasucc]
      have h1 := (hc n).2
      have h2 := (hc (n + 1)).1
      push_cast at h2
      linarith
  have htop : Tendsto a atTop atTop := by
    refine tendsto_atTop_mono (fun n ↦ ?_)
      (tendsto_atTop_add_const_right atTop (b - 1) tendsto_natCast_atTop_atTop)
    cases n with
    | zero => simp [ha0]
    | succ n =>
      rw [hasucc]
      have := (hc n).1
      push_cast
      linarith
  have hreg (n : ℕ) : IsRegularValue I 𝓘(ℝ) f (a n) := by
    cases n with
    | zero =>
      apply isRegularValue_of_notMem_range
      rintro ⟨x, hx⟩
      rw [ha0] at hx
      linarith [hbound x]
    | succ n => exact hcreg n
  exact ⟨a, hmono, htop, hreg, fun x ↦ by rw [ha0]; linarith [hbound x]⟩

/-- The sublevels of a proper bounded-below Morse function admit a compact exhaustion at strictly
increasing regular values tending to infinity. The initial sublevel is empty, and every stage
contains only finitely many critical points. The equality with the actual sublevels retains the
level inclusions and function-value control. -/
theorem IsMorse.exists_regular_sublevel_exhaustion (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) :
    ∃ (a : ℕ → ℝ) (K : CompactExhaustion M), StrictMono a ∧ Tendsto a atTop atTop ∧
      (∀ n, IsRegularValue I 𝓘(ℝ) f (a n)) ∧ (∀ n, K n = f ⁻¹' Iic (a n)) ∧
      K 0 = ∅ ∧ ∀ n, (criticalPoints I f ∩ K n).Finite := by
  obtain ⟨a, hmono, htop, hreg, ha0⟩ := hf.exists_regular_levels hp hbdd
  obtain ⟨b, hb⟩ := hbdd
  have hcompact (n : ℕ) : IsCompact (f ⁻¹' Iic (a n)) := by
    have heq : f ⁻¹' Iic (a n) = f ⁻¹' Icc b (a n) := by
      ext x
      simp [hb (mem_range_self x)]
    rw [heq]
    exact hp.isCompact_preimage isCompact_Icc
  let K : CompactExhaustion M :=
    { toFun := fun n ↦ f ⁻¹' Iic (a n)
      isCompact' := hcompact
      subset_interior_succ' := fun n ↦ ?_
      iUnion_eq' := ?_ }
  · have hK : ∀ n, K n = f ⁻¹' Iic (a n) := fun _ ↦ rfl
    refine ⟨a, K, hmono, htop, hreg, hK, ?_, fun n ↦
      hf.finite_criticalPoints_inter (K.isCompact n)⟩
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    rw [hK, mem_preimage, mem_Iic] at hx
    exact (ha0 x).not_ge hx
  · intro x hx
    exact mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset
        ((hf.contMDiff.continuous.isOpen_preimage _ isOpen_Iio).mem_nhds
          (hx.trans_lt (hmono (Nat.lt_succ_self n))))
        (fun y hy ↦ hy.le)
  · apply iUnion_eq_univ_iff.2
    intro x
    obtain ⟨n, hn⟩ := (htop.eventually_ge_atTop (f x)).exists
    exact ⟨n, hn⟩

end TauCeti
