/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Limits of weighted extended-real sums

Weighted sums `s a + t b - r` with nonnegative real weights and a real correction preserve
limits when both endpoint limits are different from `⊤`. This allows convexity inequalities
for extended-real energies to pass to pointwise limits, including endpoint energies `⊥`.
-/

public section

open Filter Topology

namespace EReal

/-- Weighted sums with nonnegative real weights and a real subtrahend preserve limits when
both endpoint limits are different from `⊤`. Endpoint limits equal to `⊥` are allowed. -/
theorem tendsto_coe_mul_add_coe_mul_sub {ι : Type*} {l : Filter ι}
    {u v : ι → EReal} {a b : EReal} (hu : Tendsto u l (𝓝 a))
    (hv : Tendsto v l (𝓝 b)) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (r : ℝ) :
    Tendsto (fun i ↦ (s : EReal) * u i + (t : EReal) * v i - (r : EReal)) l
      (𝓝 ((s : EReal) * a + (t : EReal) * b - (r : EReal))) := by
  have hmul {c : ℝ} {w : ι → EReal} {d : EReal} (hw : Tendsto w l (𝓝 d)) :
      Tendsto (fun i ↦ (c : EReal) * w i) l (𝓝 ((c : EReal) * d)) :=
    EReal.Tendsto.const_mul hw (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))
  have hadd {u v : ι → EReal} {a b : EReal} (hu : Tendsto u l (𝓝 a))
      (hv : Tendsto v l (𝓝 b)) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
      Tendsto (fun i ↦ u i + v i) l (𝓝 (a + b)) :=
    (EReal.continuousAt_add (.inl ha) (.inr hb)).tendsto.comp (hu.prodMk_nhds hv)
  have hsa : (s : EReal) * a ≠ ⊤ := by simp [EReal.mul_ne_top, hs, ha]
  have htb : (t : EReal) * b ≠ ⊤ := by simp [EReal.mul_ne_top, ht, hb]
  -- Finite-above limits exclude the indeterminate sum `⊤ + ⊥`.
  have hR := hadd (hadd (hmul hu) (hmul hv) hsa htb)
    (tendsto_const_nhds (x := ((-r : ℝ) : EReal)))
    (EReal.add_ne_top hsa htb) (EReal.coe_ne_top _)
  simpa only [EReal.coe_neg, ← sub_eq_add_neg] using hR

end EReal
