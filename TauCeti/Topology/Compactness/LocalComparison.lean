/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Clopen

/-!
# Uniform local comparisons on compact subsets

Eventual local multiplicative comparisons to a neighbourhood's centre propagate across
a preconnected set. On a compact subset, one constant and one set of indices work at every
point. A family with nonzero values at the base point can then be normalized by those values.

## Main results

* `IsPreconnected.exists_eventually_forall_le_mul_of_locally`: two-sided compact comparison.
* `IsPreconnected.exists_eventually_forall_inv_le_div_le_of_locally`: bounds after normalizing
  by the base value.
-/

public section

open Filter Set
open scoped Topology

variable {X ι R : Type*} [TopologicalSpace X]

section MonoidWithZero

variable [MonoidWithZero R]
  {s : Set X} {u : ι → X → R} {l : Filter ι}

private theorem IsPreconnected.exists_eventually_le_mul_of_locally
    [PartialOrder R] [PosMulStrictMono R]
    (hs : IsPreconnected s)
    (hloc : ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, ∃ C : R, 0 < C ∧
      ∀ᶠ i in l, ∀ y ∈ V, u i y ≤ C * u i x ∧ u i x ≤ C * u i y)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ∃ C : R, 0 < C ∧ ∀ᶠ i in l, u i x ≤ C * u i y := by
  let P (a b : X) := ∃ C : R, 0 < C ∧ ∀ᶠ i in l, u i a ≤ C * u i b
  refine hs.induction₂' P (fun a ha ↦ ?_) (fun a b c _ _ _ ↦ ?_) hx hy
  · obtain ⟨V, hV, C, hC, h⟩ := hloc a ha
    filter_upwards [hV] with b hb
    exact ⟨⟨C, hC, h.mono fun i hi ↦ (hi b hb).2⟩,
      ⟨C, hC, h.mono fun i hi ↦ (hi b hb).1⟩⟩
  · rintro ⟨A, hA, hab⟩ ⟨B, hB, hbc⟩
    refine ⟨A * B, ?_, ?_⟩
    · simpa only [mul_zero] using mul_lt_mul_of_pos_left hB hA
    · filter_upwards [hab, hbc] with i hi hj
      simpa only [mul_assoc] using hi.trans (mul_le_mul_of_nonneg_left hj hA.le)

/-- Eventual two-sided comparisons to each neighbourhood's centre propagate from a base point
where the values are eventually nonnegative. The comparison factor and the set of indices can
both be chosen uniformly over a compact subset. -/
theorem IsPreconnected.exists_eventually_forall_le_mul_of_locally
    [LinearOrder R] [PosMulStrictMono R] [MulPosMono R]
    (hs : IsPreconnected s) {K : Set X} (hK : IsCompact K) (hKs : K ⊆ s)
    {p : X} (hp : p ∈ s) (hbase : ∀ᶠ i in l, 0 ≤ u i p)
    (hloc : ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, ∃ C : R, 0 < C ∧
      ∀ᶠ i in l, ∀ y ∈ V, u i y ≤ C * u i x ∧ u i x ≤ C * u i y) :
    ∃ C : R, 1 ≤ C ∧ ∀ᶠ i in l, ∀ x ∈ K, u i x ≤ C * u i p ∧ u i p ≤ C * u i x := by
  let Q (t : R × ι) (x : K) := u t.2 x ≤ t.1 * u t.2 p ∧ u t.2 p ≤ t.1 * u t.2 x
  have hnear (x : K) : ∀ᶠ z : (R × ι) × K in (atTop ×ˢ l) ×ˢ 𝓝 x, Q z.1 z.2 := by
    obtain ⟨V, hV, A, hA, hlocal⟩ := hloc x (hKs x.property)
    obtain ⟨B, _, hxp⟩ := hs.exists_eventually_le_mul_of_locally hloc (hKs x.property) hp
    obtain ⟨D, hD, hpx⟩ := hs.exists_eventually_le_mul_of_locally hloc hp (hKs x.property)
    have hV' : ∀ᶠ y : K in 𝓝 x, (y : X) ∈ V := by
      have h := nhdsWithin_mono (x : X) hKs hV
      rwa [nhdsWithin_eq_map_subtypeVal x.property] at h
    have hC := eventually_ge_atTop (max (A * B) (D * A))
    filter_upwards [(hC.prod_mk (hbase.and (hlocal.and (hxp.and hpx)))).prod_mk hV'] with t ht
    obtain ⟨⟨hCt, hp0, hloc', hxp', hpx'⟩, hty⟩ := ht
    obtain ⟨hyx, hxy⟩ := hloc' t.2 hty
    have hforward : u t.1.2 t.2 ≤ (A * B) * u t.1.2 p := by
      rw [mul_assoc]
      exact hyx.trans (mul_le_mul_of_nonneg_left hxp' hA.le)
    have hback : u t.1.2 p ≤ (D * A) * u t.1.2 t.2 := by
      rw [mul_assoc]
      exact hpx'.trans (mul_le_mul_of_nonneg_left hxy hD.le)
    have hDA : 0 < D * A := by simpa only [mul_zero] using mul_lt_mul_of_pos_left hA hD
    have hy0 : 0 ≤ u t.1.2 t.2 := le_of_not_gt fun hy ↦
      (by simpa only [mul_zero] using mul_lt_mul_of_pos_left hy hDA :
        (D * A) * u t.1.2 t.2 < 0).not_ge (hp0.trans hback)
    exact ⟨hforward.trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans hCt) hp0),
      hback.trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans hCt) hy0)⟩
  let : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hAll : ∀ᶠ t : (R × ι) × K in (atTop ×ˢ l) ×ˢ 𝓝ˢ (univ : Set K), Q t.1 t.2 :=
    isCompact_univ.mem_prod_nhdsSet_of_forall fun x _ ↦ hnear x
  have hAll' : ∀ᶠ t in atTop ×ˢ l, ∀ x : K, Q t x :=
    hAll.curry.mono fun _ ht x ↦ ht.self_of_nhdsSet x (mem_univ x)
  obtain ⟨_, hC, _, hi, h⟩ := eventually_prod_iff.1 hAll'
  obtain ⟨C, hC1, hC'⟩ := ((eventually_ge_atTop (1 : R)).and hC).exists
  exact ⟨C, hC1, hi.mono fun _ hi' x hx ↦ h hC' hi' ⟨x, hx⟩⟩

end MonoidWithZero

/-- After normalizing by a nonzero value at the base point, local comparisons give a uniform
upper bound and a positive lower bound on every compact subset. -/
theorem IsPreconnected.exists_eventually_forall_inv_le_div_le_of_locally
    [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {s K : Set X} (hs : IsPreconnected s) (hK : IsCompact K) (hKs : K ⊆ s)
    {p : X} (hp : p ∈ s) {u : ι → X → R} {l : Filter ι}
    (hbase : ∀ᶠ i in l, u i p ≠ 0)
    (hloc : ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, ∃ C : R, 0 < C ∧
      ∀ᶠ i in l, ∀ y ∈ V, u i y ≤ C * u i x ∧ u i x ≤ C * u i y) :
    ∃ C : R, 1 ≤ C ∧ ∀ᶠ i in l, ∀ x ∈ K, C⁻¹ ≤ u i x / u i p ∧ u i x / u i p ≤ C := by
  let v i x := u i x / u i p
  let w i x := max (v i x) 0
  have hlocal : ∀ x ∈ s, ∃ V ∈ 𝓝[s] x, ∃ C : R, 0 < C ∧
      ∀ᶠ i in l, ∀ y ∈ V, w i y ≤ C * w i x ∧ w i x ≤ C * w i y := by
    intro x hx
    obtain ⟨V, hV, C, hC, h⟩ := hloc x hx
    let D := max C C⁻¹
    refine ⟨V, hV, D, hC.trans_le (le_max_left ..), ?_⟩
    filter_upwards [hbase, h] with i hi h
    intro y hy
    obtain ⟨hyx, hxy⟩ := h y hy
    have hmax {a b : X} {B : R} (hB : 0 ≤ B) (hBD : B ≤ D)
        (hab : v i a ≤ B * v i b) : w i a ≤ D * w i b := by
      calc
        w i a ≤ B * w i b := by
          change max (v i a) 0 ≤ B * max (v i b) 0
          rw [mul_max_of_nonneg _ _ hB, mul_zero]
          exact max_le_max hab le_rfl
        _ ≤ D * w i b := mul_le_mul_of_nonneg_right hBD (le_max_right ..)
    obtain hneg | hpos := lt_or_gt_of_ne hi
    · have hreverse {a b : X} (hab : u i a ≤ C * u i b) : v i b ≤ C⁻¹ * v i a := by
        apply (le_inv_mul_iff₀ hC).2
        simp only [v, div_eq_mul_inv, ← mul_assoc]
        exact mul_le_mul_of_nonpos_right hab (inv_nonpos.mpr hneg.le)
      exact ⟨hmax (inv_nonneg.mpr hC.le) (le_max_right ..) (hreverse hxy),
        hmax (inv_nonneg.mpr hC.le) (le_max_right ..) (hreverse hyx)⟩
    · have hforward {a b : X} (hab : u i a ≤ C * u i b) : v i a ≤ C * v i b := by
        simpa only [v, mul_div_assoc] using div_le_div_of_nonneg_right hab hpos.le
      exact ⟨hmax hC.le (le_max_left ..) (hforward hyx),
        hmax hC.le (le_max_left ..) (hforward hxy)⟩
  obtain ⟨C, hC, h⟩ := hs.exists_eventually_forall_le_mul_of_locally
    (u := w) hK hKs hp (.of_forall fun _ ↦ le_max_right ..) hlocal
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbase, h] with i hi h
  intro x hx
  have hp' : w i p = 1 := by simp [w, v, hi]
  obtain ⟨hu, hl⟩ := h x hx
  rw [hp', mul_one] at hu
  rw [hp'] at hl
  have hx' : 0 < v i x := by
    by_contra! hn
    rw [show w i x = 0 from max_eq_right hn, mul_zero] at hl
    exact (not_le_of_gt zero_lt_one) hl
  rw [show w i x = v i x from max_eq_left hx'.le] at hl hu
  exact ⟨(inv_le_iff_one_le_mul₀' (zero_lt_one.trans_le hC)).2 hl, hu⟩
