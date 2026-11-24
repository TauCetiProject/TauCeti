/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended-real limits, `limsup`, and lower semicontinuity lemmas

Complements `Mathlib.Topology.Instances.EReal.Lemmas` with limit, `limsup`, and lower
semicontinuity lemmas for `EReal`-valued families:

* `EReal.tendsto_coe_mul_add_coe_mul_sub`: weighted sums `s a + t b - r` with nonnegative real
  weights and a real correction preserve limits when both endpoint limits are different from `⊤`
  (allowing endpoint limits equal to `⊥`).
* `EReal.limsup_mul_eq_of_tendsto_one`: multiplying an `EReal`-valued family by factors converging
  to `1` preserves its `limsup`.
* `LowerSemicontinuous.ereal_add`: sums of lower semicontinuous extended-real functions are lower
  semicontinuous.
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

/-- Multiplying an `EReal`-valued family by factors converging to `1` preserves its `limsup`. -/
theorem limsup_mul_eq_of_tendsto_one {ι : Type*} {l : Filter ι} {u b : ι → EReal}
    (hb : Tendsto b l (𝓝 1)) :
    limsup (u * b) l = limsup u l := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hb0 : 0 ≤ᶠ[l] b :=
    (hb.eventually (Ioi_mem_nhds (zero_lt_one (α := EReal)))).mono fun _ h ↦ h.le
  by_cases hu : ∃ᶠ n in l, 0 ≤ u n
  · exact le_antisymm
      ((EReal.limsup_mul_le hu hb0 (.inr (by rw [hb.limsup_eq]; exact EReal.coe_ne_top 1))
        (.inr (by simp [hb.limsup_eq]))).trans_eq (by rw [hb.limsup_eq, mul_one]))
      (by simpa [hb.liminf_eq] using EReal.le_limsup_mul hu hb0)
  · push Not at hu
    have hneg_u : 0 ≤ᶠ[l] -u := hu.mono fun _ hn ↦ by simpa using hn.le
    refine le_antisymm ?_ ?_
    · have h1 := EReal.le_liminf_mul hneg_u hb0
      have hneg : (-u) * b = -(u * b) := by ext n; simp [neg_mul]
      rwa [hb.liminf_eq, mul_one, hneg, EReal.liminf_neg, EReal.liminf_neg,
        EReal.neg_le_neg_iff] at h1
    · have h2 := EReal.liminf_mul_le hb0 hneg_u
        (.inl (by simp [hb.limsup_eq]))
        (.inl (by rw [hb.limsup_eq]; exact EReal.coe_ne_top 1))
      have hneg : b * (-u) = -(u * b) := by ext n; simp [mul_neg, mul_comm]
      rwa [hb.limsup_eq, one_mul, hneg, EReal.liminf_neg, EReal.liminf_neg,
        EReal.neg_le_neg_iff] at h2

end EReal

/-- The sum of two lower semicontinuous extended-real functions is lower semicontinuous. -/
theorem LowerSemicontinuous.ereal_add {X : Type*} [TopologicalSpace X] {f g : X → EReal}
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x ↦ f x + g x) := by
  intro x y hy
  have hfbot : f x ≠ ⊥ := by
    intro h
    simp [h] at hy
  have hgbot : g x ≠ ⊥ := by
    intro h
    simp [h] at hy
  exact LowerSemicontinuousAt.add' (hf x) (hg x)
    (EReal.continuousAt_add (.inr hgbot) (.inl hfbot)) y hy
