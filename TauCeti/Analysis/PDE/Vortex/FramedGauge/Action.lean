/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev gauge group acts on the framed field space

For a real order `s ≥ 2`, the Sobolev framed gauge group `G_(s+1)`
(`TauCeti.Vortex.sobolevGaugeGroup`) acts on the affine space `A_m^s = x_ref + H^s` of framed
degree-`m` plane vortex fields (`TauCeti.Vortex.framedFieldSpace`) by the charge-one gauge action
`(a, α) ↦ (a - u⁻¹ du, u α)` (`TauCeti.Vortex.gaugeTransform`). This is the gauge action of the
Sobolev completion: its elements are only `1 + h` with `h ∈ H^(s+1)`, not smooth gauges.

Write `u = 1 + h`. The difference `u • x - x_ref` splits as

* the linear action of `u` on `x - x_ref ∈ H^s`: it rotates the section by `u`, and
  `u y = y + h y` lies in `H^s` because `H^s(ℂ)` is an algebra for `s > 1`
  (`TauCeti.Vortex.gaugeLinearAction_mem_sobolevFields`);
* the displacement `u • x_ref - x_ref` of the reference field. Its connection part is
  `-Im (u⁻¹ du)`, whose coefficients lie in `H^s` since `u` is `C¹` for `s + 1 ≥ 3`
  (`TauCeti.Vortex.contDiff_of_mem_sobolevGaugeGroup`). Its section part is `h α_ref`, and
  multiplication by the smooth reference section, whose derivatives are all bounded, preserves
  `H^n` for the integer order `n = ⌈s⌉ ≤ s + 1`
  (`TauCeti.Vortex.gaugeTransform_referenceField_sub_mem_sobolevFields`).

The order `s ≥ 2` is what the integer-order Sobolev embedding `H^(j+2)(ℂ) ⊆ Cʲ` needs to make
the elements of `G_(s+1)` continuously differentiable. Together with the converse
`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`, a `C²` gauge carries a field of
`A_m^k`, `k ≥ 2`, back into `A_m^k` exactly when it lies in `G_(k+1)`
(`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`).

The action is free: a differentiable gauge tending to one at infinity that fixes a field is
trivial (`TauCeti.Vortex.eq_one_of_gaugeTransform_eq`).

## Main results

* `TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace`: `G_(s+1)` preserves `A_m^s` for `s ≥ 2`.
* `TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`: for a `C²` gauge `u` and `x ∈ A_m^k`,
  `k ≥ 2`, the field `u • x` lies in `A_m^k` if and only if `u ∈ G_(k+1)`.
* The instances `MulAction (sobolevGaugeGroup _) (framedFieldSpace f m s)` and
  `IsCancelSMul (sobolevGaugeGroup _) (framedFieldSpace f m s)`, under `Fact (2 ≤ s)`.

No topology on `G_(s+1)` or continuity of the action is treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex TemperedDistribution
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {u : ℂ → Circle}

/-- **The linear gauge action of `G_s` preserves `H^s`.** For `s > 1` and `u ∈ G_s`, rotating the
section of a field of `sobolevFields s` by `u` stays in `sobolevFields s`: with `u = 1 + h`, the
rotated section is `α + h α`, and `H^s(ℂ)` is an algebra. -/
theorem gaugeLinearAction_mem_sobolevFields {s : ℝ} {hs : 1 < s}
    (hu : u ∈ sobolevGaugeGroup hs) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields s) : gaugeLinearAction u y ∈ sobolevFields s := by
  obtain ⟨-, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hmul {g k : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ s 2)
      (hk : k ∈ realSobolevFunctions ℂ s 2) : g * k ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) hg hk
  have hc (i : Fin 4) := mem_sobolevFields.1 hy i
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [gaugeLinearAction_apply] using hc 0
  · simpa [gaugeLinearAction_apply] using hc 1
  · -- `Re u y₂ - Im u y₃ = y₂ + (Re u - 1) y₂ - Im u y₃`
    convert sub_mem (add_mem (hc 2) (hmul hu₁ (hc 2))) (hmul hu₂ (hc 3)) using 1
    ext z
    simp [gaugeLinearAction_apply]
    ring
  · -- `Im u y₂ + Re u y₃ = Im u y₂ + y₃ + (Re u - 1) y₃`
    convert add_mem (hmul hu₂ (hc 2)) (add_mem (hc 3) (hmul hu₁ (hc 3))) using 1
    ext z
    simp [gaugeLinearAction_apply]
    ring

/-- The coordinates of the reference field have all derivatives through order `n` bounded by a
single constant. -/
private theorem exists_forall_norm_iteratedFDeriv_referenceField_apply_le
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) (i : Fin 4) (n : ℕ) :
    ∃ M ≥ 0, ∀ j ≤ n, ∀ z, ‖iteratedFDeriv ℝ j (fun z ↦ referenceField f m z i) z‖ ≤ M := by
  choose C hC using exists_norm_iteratedFDeriv_referenceField_apply_le f m i
  refine ⟨∑ j ∈ Finset.range (n + 1), |C j|, by positivity, fun j hj z ↦ (hC j z).trans ?_⟩
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j ↦ |C j|)
    (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))

/-- **A Sobolev gauge displaces the reference field by a Sobolev field.** For `s ≥ 2` and
`u ∈ G_(s+1)`, the field `u • x_ref - x_ref` lies in `sobolevFields s`. Its connection part is
`-Im (u⁻¹ du)`, and its section part is `(u - 1) α_ref`, the product of `u - 1 ∈ H^(s+1)` with
the smooth reference section, whose derivatives are bounded. -/
theorem gaugeTransform_referenceField_sub_mem_sobolevFields {s : ℝ} (hs : 2 ≤ s)
    {hs' : 1 < s + 1} (hu : u ∈ sobolevGaugeGroup hs') :
    gaugeTransform u (referenceField f m) - referenceField f m ∈ sobolevFields s := by
  have hC1 : ContDiff ℝ 1 fun z ↦ (u z : ℂ) :=
    contDiff_of_mem_sobolevGaugeGroup hu (by push_cast; linarith)
  have hω (v : ℂ) := gaugeForm_apply_mem_realSobolevFunctions (by linarith) hu hC1 v
  obtain ⟨-, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs' u).1 hu
  -- The section part, at the integer order `n = ⌈s⌉`, between `s` and `s + 1`.
  set n := ⌈s⌉₊
  have hsn : s ≤ n := Nat.le_ceil s
  have hns : (n : ℝ) ≤ s + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num) hns
  have h0 : (fun _ : ℂ ↦ (0 : ℝ)) ∈ realSobolevFunctions ℂ n 2 := zero_mem _
  have hw₁ : (fun z ↦ !₂[0, 0, (u z : ℂ).re - 1, (u z : ℂ).im]) ∈ sobolevFields n := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [h0, h0, hmono hu₁, hmono hu₂]
  have hw₂ : (fun z ↦ !₂[0, 0, -(u z : ℂ).im, (u z : ℂ).re - 1]) ∈ sobolevFields n := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [h0, h0, neg_mem (hmono hu₂), hmono hu₁]
  have hr (i : Fin 4) : ContDiff ℝ ∞ fun z ↦ referenceField f m z i :=
    contDiff_euclidean.1 (contDiff_referenceField f m) i
  obtain ⟨M₂, hM₂, hb₂⟩ := exists_forall_norm_iteratedFDeriv_referenceField_apply_le f m 2 n
  obtain ⟨M₃, hM₃, hb₃⟩ := exists_forall_norm_iteratedFDeriv_referenceField_apply_le f m 3 n
  have hsec := sobolevFields_mono hsn (add_mem
    (smul_mem_sobolevFields_natCast n (hr 2) hM₂ hb₂ hw₁)
    (smul_mem_sobolevFields_natCast n (hr 3) hM₃ hb₃ hw₂))
  -- The connection part.
  have hconn : (fun z ↦ !₂[-gaugeForm u z 1, -gaugeForm u z I, 0, 0]) ∈ sobolevFields s := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    exacts [neg_mem (hω 1), neg_mem (hω I), zero_mem _, zero_mem _]
  convert add_mem hconn hsec using 1
  ext z i
  fin_cases i <;> simp [gaugeTransform_apply] <;> ring

/-- **The Sobolev gauge group preserves the framed field space.** For `s ≥ 2`, every
`u ∈ G_(s+1)` carries the affine space `A_m^s` of framed degree-`m` vortex fields to itself under
the gauge action `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
theorem gaugeTransform_mem_framedFieldSpace {s : ℝ} (hs : 2 ≤ s) {hs' : 1 < s + 1}
    (hu : u ∈ sobolevGaugeGroup hs') {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) : gaugeTransform u x ∈ framedFieldSpace f m s := by
  have hus : u ∈ sobolevGaugeGroup (s := s) (by linarith) :=
    sobolevGaugeGroup_mono (by linarith) (by linarith) hu
  have hlin := gaugeLinearAction_mem_sobolevFields hus (mem_framedFieldSpace.1 hx)
  rw [← gaugeTransform_sub_gaugeTransform] at hlin
  refine mem_framedFieldSpace.2 ?_
  convert add_mem hlin (gaugeTransform_referenceField_sub_mem_sobolevFields (f := f) (m := m)
    hs hu) using 1
  abel

/-- **Sobolev gauges are exactly the gauges preserving `A_m^k`.** For `k ≥ 2`, a field
`x ∈ A_m^k` and a `C²` gauge `u`, the transformed field `u • x` lies in `A_m^k` if and only if
`u ∈ G_(k+1)`. -/
theorem gaugeTransform_mem_framedFieldSpace_iff {k : ℕ} (hk : 1 < k)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k)
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) :
    gaugeTransform u x ∈ framedFieldSpace f m k ↔
      u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega) :=
  ⟨mem_sobolevGaugeGroup_of_mem_framedFieldSpace hk hx hu,
    fun h ↦ gaugeTransform_mem_framedFieldSpace (by exact_mod_cast hk) h hx⟩

/-! ### The bundled action -/

section Action

variable {s : ℝ} [Fact (2 ≤ s)] {hs : 1 < s + 1}

/-- For `s ≥ 2` the Sobolev gauge group `G_(s+1)` acts on the framed field space `A_m^s` by the
gauge action `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
instance : MulAction (sobolevGaugeGroup hs) (framedFieldSpace f m s) where
  smul u x := ⟨gaugeTransform u x, gaugeTransform_mem_framedFieldSpace Fact.out u.2 x.2⟩
  one_smul x := Subtype.ext (gaugeTransform_one x)
  mul_smul u v x := Subtype.ext (gaugeTransform_mul
    (differentiable_of_mem_sobolevGaugeGroup u.2 (by linarith [(Fact.out : 2 ≤ s)]))
    (differentiable_of_mem_sobolevGaugeGroup v.2 (by linarith [(Fact.out : 2 ≤ s)])) x)

/-- The bundled action of `G_(s+1)` on `A_m^s` is the charge-one gauge transformation. -/
@[simp]
theorem coe_sobolevGaugeGroup_smul (u : sobolevGaugeGroup hs) (x : framedFieldSpace f m s) :
    ((u • x : framedFieldSpace f m s) : ℂ → EuclideanSpace ℝ (Fin 4)) =
      gaugeTransform u x := (rfl)

/-- The action of `G_(s+1)` on `A_m^s` is free. -/
instance : IsCancelSMul (sobolevGaugeGroup hs) (framedFieldSpace f m s) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro u x hux
  exact Subtype.ext (eq_one_of_gaugeTransform_eq
    (differentiable_of_mem_sobolevGaugeGroup u.2 (by linarith [(Fact.out : 2 ≤ s)]))
    (tendsto_cocompact_of_mem_sobolevGaugeGroup u.2) (congrArg Subtype.val hux))

end Action

end TauCeti.Vortex
