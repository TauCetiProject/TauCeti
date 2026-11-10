/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
public import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev gauge group acts on the affine field space

The framed degree-`m` plane vortex fields form the affine space
`A_m^n = x_m + H^n(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`), and its gauge group is the
Sobolev framed gauge group `G_(n+1) = {1 + h : h ∈ H^(n+1)(ℂ; ℂ), |1 + h| = 1}`
(`TauCeti.Vortex.sobolevGaugeGroup`), acting by `(a, α) ↦ (a - u⁻¹ du, u α)`
(`TauCeti.Vortex.gaugeTransform`). This file shows that, for `n ≥ 2`, this action preserves
`A_m^n`:

* the linear part of a gauge `u ∈ G_s`, `s > 1`, which fixes connection variations and multiplies
  section variations by `u`, preserves the Sobolev fields `H^s`
  (`TauCeti.Vortex.gaugeLinearAction_mem_sobolevFields`): writing `u = 1 + h`, the section
  variation `δα` becomes `δα + h δα`, and `H^s(ℂ)` is an algebra;
* a `C¹` gauge `u ∈ G_(n+1)` maps `A_m^n` into itself
  (`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace`). The connection changes by
  `Im (u⁻¹ du) ∈ H^n`, and the section changes by `h α`, where `α` is the reference section,
  which is smooth with bounded derivatives, plus an `H^n` tail.

Together with `TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace` this characterizes
`G_(n+1)` among `C²` gauges: a `C²` gauge maps one field of `A_m^n` into `A_m^n` exactly when it
lies in `G_(n+1)` (`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`). The smooth elements
of `G_(n+1)` therefore act on `A_m^n` (`TauCeti.Vortex.framedFieldSubMulAction`), and two fields
of `A_m^n` lie in the same orbit of this action exactly when they lie in the same orbit of the
whole smooth framed gauge group (`TauCeti.Vortex.mem_orbit_framedFieldSubMulAction_iff`).

Elements of `G_(n+1)` are continuous, and the action uses their first derivatives. The membership
theorem assumes the gauge is `C¹`; no Sobolev embedding into `C¹` is proved here, so the bundled
action is stated for the smooth subgroup.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Module TemperedDistribution
open scoped ContDiff

/-- **Sobolev gauges act linearly on Sobolev fields.** For `s > 1` and `u ∈ G_s`, the linear part
of the gauge action, which fixes the connection variation and multiplies the section variation by
`u`, preserves `H^s`. Writing `u = 1 + h` with `h ∈ H^s`, it adds `h δα` to the section variation
`δα`, and `H^s(ℂ)` is an algebra. -/
theorem gaugeLinearAction_mem_sobolevFields {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields s) : gaugeLinearAction u y ∈ sobolevFields s := by
  obtain ⟨-, hre, him⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hc (i : Fin 4) := mem_sobolevFields.1 hy i
  have hmul {g k : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ s 2)
      (hk : k ∈ realSobolevFunctions ℂ s 2) : g * k ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) hg hk
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [gaugeLinearAction_apply] using hc 0
  · simpa [gaugeLinearAction_apply] using hc 1
  -- `Re u y₂ - Im u y₃ = y₂ + (Re u - 1) y₂ - Im u y₃`.
  · convert sub_mem (add_mem (hc 2) (hmul hre (hc 2))) (hmul him (hc 3)) using 1
    ext z
    simp only [gaugeLinearAction_apply, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply,
      Matrix.cons_val, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    ring
  -- `Im u y₂ + Re u y₃ = y₃ + Im u y₂ + (Re u - 1) y₃`.
  · convert add_mem (add_mem (hc 3) (hmul him (hc 2))) (hmul hre (hc 3)) using 1
    ext z
    simp only [gaugeLinearAction_apply, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply,
      Matrix.cons_val, Pi.add_apply, Pi.mul_apply]
    ring

/-- **Sobolev gauges preserve the framed field space.** For an integer `n ≥ 2`, a `C¹` gauge
`u ∈ G_(n+1)` maps `A_m^n` into itself. The connection changes by `Im (u⁻¹ du)`, which lies in
`H^n`, and with `u = 1 + h` the section changes by `h α`, which lies in `H^n` because `α` is the
smooth reference section, with bounded derivatives, plus an `H^n` tail. -/
theorem gaugeTransform_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m n : ℕ} (hn : 1 < n)
    {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup (s := n + 1) (by norm_cast; omega))
    (hC1 : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m n) : gaugeTransform u x ∈ framedFieldSpace f m n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨-, hre, him⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    (lt_add_one (n : ℝ)).le
  replace hre := hmono hre
  replace him := hmono him
  have hw (i : Fin 4) := mem_sobolevFields.1 (mem_framedFieldSpace.1 hx) i
  have hω (v : ℂ) := gaugeForm_apply_mem_realSobolevFunctions hn' hu hC1 v
  have hmul (i : Fin 4) {g : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ n 2) :=
    mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hn hx i hg
  refine mem_framedFieldSpace.2 (mem_sobolevFields.2 fun i ↦ ?_)
  fin_cases i
  · convert sub_mem (hw 0) (hω 1) using 1
    ext z
    simp only [Pi.sub_apply, gaugeTransform_apply, Fin.zero_eta, Fin.isValue, PiLp.sub_apply,
      Matrix.cons_val_zero]
    ring
  · convert sub_mem (hw 1) (hω I) using 1
    ext z
    simp only [Pi.sub_apply, gaugeTransform_apply, Fin.mk_one, Fin.isValue, PiLp.sub_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  -- `Re u x₂ - Im u x₃ - r₂ = (x₂ - r₂) + x₂ (Re u - 1) - x₃ Im u`.
  · convert sub_mem (add_mem (hw 2) (hmul 2 hre)) (hmul 3 him) using 1
    ext z
    simp only [Pi.sub_apply, gaugeTransform_apply, Fin.reduceFinMk, Fin.isValue, PiLp.sub_apply,
      Matrix.cons_val, Pi.add_apply]
    ring
  -- `Im u x₂ + Re u x₃ - r₃ = (x₃ - r₃) + x₂ Im u + x₃ (Re u - 1)`.
  · convert add_mem (add_mem (hw 3) (hmul 2 him)) (hmul 3 hre) using 1
    ext z
    simp only [Pi.sub_apply, gaugeTransform_apply, Fin.reduceFinMk, Fin.isValue, PiLp.sub_apply,
      Matrix.cons_val, Pi.add_apply]
    ring

/-- **The gauges preserving the framed field space.** For an integer `n ≥ 2`, a field `x ∈ A_m^n`
and a `C²` gauge `u`, the transformed field `u · x` lies in `A_m^n` exactly when `u ∈ G_(n+1)`. -/
theorem gaugeTransform_mem_framedFieldSpace_iff {f : ContDiffBump (0 : ℝ)} {m n : ℕ}
    (hn : 1 < n) {u : ℂ → Circle} (hC2 : ContDiff ℝ 2 (fun z ↦ (u z : ℂ)))
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m n) :
    gaugeTransform u x ∈ framedFieldSpace f m n ↔
      u ∈ sobolevGaugeGroup (s := n + 1) (by norm_cast; omega) :=
  ⟨mem_sobolevGaugeGroup_of_mem_framedFieldSpace hn hx hC2,
    fun hu ↦ gaugeTransform_mem_framedFieldSpace hn hu (hC2.of_le (by norm_num)) hx⟩

/-- **The action of the smooth Sobolev gauges on the framed field space.** For an integer
`n ≥ 2`, the smooth elements of `G_(n+1)`, a subgroup of the smooth framed gauge group, act on
the affine field space `A_m^n` by `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
def framedFieldSubMulAction (f : ContDiffBump (0 : ℝ)) (m : ℕ) {n : ℕ} (hn : 1 < n) :
    SubMulAction
      ((sobolevGaugeGroup (s := n + 1) (by norm_cast; omega)).subgroupOf framedGaugeGroup)
      (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := framedFieldSpace f m n
  smul_mem' u x hx := by
    rw [Subgroup.smul_def, framedGaugeGroup_smul]
    have hsmooth := ((mem_framedGaugeGroup _).1 (u : framedGaugeGroup).2).1
    exact gaugeTransform_mem_framedFieldSpace hn (Subgroup.mem_subgroupOf.1 u.2)
      (hsmooth.of_le (by simp)) hx

/-- The fields acted on by `framedFieldSubMulAction f m hn` are those of `A_m^n`. -/
@[simp]
theorem mem_framedFieldSubMulAction {f : ContDiffBump (0 : ℝ)} {m n : ℕ} {hn : 1 < n}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    x ∈ framedFieldSubMulAction f m hn ↔ x ∈ framedFieldSpace f m n :=
  Iff.rfl

/-- **Orbits in the framed field space.** For an integer `n ≥ 2`, two fields of `A_m^n` lie in the
same orbit of the smooth elements of `G_(n+1)` exactly when they lie in the same orbit of the
whole smooth framed gauge group. So the orbit space of `A_m^n` under the smooth Sobolev gauges
embeds in the space of smooth framed gauge orbits of fields. -/
theorem mem_orbit_framedFieldSubMulAction_iff {f : ContDiffBump (0 : ℝ)} {m n : ℕ}
    {hn : 1 < n} {x y : framedFieldSubMulAction f m hn} :
    y ∈ MulAction.orbit
        ((sobolevGaugeGroup (s := n + 1) (by norm_cast; omega)).subgroupOf framedGaugeGroup) x ↔
      (y : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ MulAction.orbit framedGaugeGroup
        (x : ℂ → EuclideanSpace ℝ (Fin 4)) := by
  simp only [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [SubMulAction.val_smul, Subgroup.smul_def]⟩
  · rintro ⟨u, hu⟩
    have hsmooth := ((mem_framedGaugeGroup _).1 u.2).1
    have hy : gaugeTransform u x ∈ framedFieldSpace f m n := by
      rw [← framedGaugeGroup_smul, hu]
      exact y.2
    refine ⟨⟨u, Subgroup.mem_subgroupOf.2 (mem_sobolevGaugeGroup_of_mem_framedFieldSpace hn x.2
      (hsmooth.of_le (by simp)) hy)⟩, Subtype.ext ?_⟩
    rw [SubMulAction.val_smul, Subgroup.smul_def, hu]

end TauCeti.Vortex
