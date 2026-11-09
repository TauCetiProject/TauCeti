/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# The Sobolev framed gauge group of plane vortices

For a real order `s > 1` the Sobolev framed gauge group `G_s` (`sobolevGaugeGroup`) consists of
the continuous circle-valued maps `u` on the plane with `u - 1 ∈ H^s(ℂ; ℂ)`: the real functions
`Re u - 1` and `Im u` lie in the Bessel-potential space `H^s`
(`TemperedDistribution.realSobolevFunctions`). Writing `u = 1 + h`, this is the group
`{1 + h : h ∈ H^s, |1 + h| = 1}`, with `u` the continuous representative. The gauge group of
the field space `A_m^k` of framed degree-`m` vortices (`TauCeti.Vortex.framedFieldSpace`) is
`G_(k+1)`.

Since `H^s(ℂ)` is an algebra for `s > 1`, the products `(1 + h)(1 + g) = 1 + (h + g + h g)` stay
in the group, and the inverse is the complex conjugate `1 + conj h`. The Sobolev embedding gives
the end condition `u → 1` at infinity, so the smooth elements of `G_s` are smooth framed gauges
(`TauCeti.Vortex.framedGaugeGroup`); they form the subgroup `G_s ⊓ framedGaugeGroup`. Conversely,
smooth gauges with `u - 1` compactly supported, such as `exp (i f)` for a smooth compactly
supported phase `f`, lie in every `G_s`. A smooth framed gauge need not lie in `G_s`: a phase
with a `1 / |z|` tail is not square integrable on the plane.

The Sobolev embedding of `H^s(ℂ)` into `C^k` for `s > k + 1` makes every element of `G_s` a
`C^k` map. In particular the elements of `G_(s+1)`, `s > 1`, are `C¹`, and the real one-form
`Im (u⁻¹ du)` (`TauCeti.Vortex.gaugeForm`) has coefficients in `H^s`. Its product with `i` is the
connection increment `u⁻¹ du` of the action `(a, α) ↦ (a - u⁻¹ du, u α)`.

For an integer `k > 1` this action of `G_(k+1)` maps the affine field space `A_m^k` to itself.
Writing `x = (a_m, α_m) + y` with `y ∈ H^k`, the transformed field is
`(a_m, α_m) + (y_a, u y_α) + (-u⁻¹ du, (u - 1) α_m)`. The rotated variation `u y_α` lies in
`H^k` because `H^k(ℂ)` is an algebra, and `(u - 1) α_m` lies in `H^k` because the reference
section is smooth with bounded derivatives. The integer order enters only through this last
multiplication. Composition of the action is multiplication of gauges
(`TauCeti.Vortex.gaugeTransform_mul`).

No topology or Banach Lie group charts on `G_s` are constructed here, and neither continuity nor
smoothness of the action is asserted.

## Main definitions

* `TauCeti.Vortex.sobolevGaugeGroup hs`: the group `G_s`, `s > 1`, as a subgroup of `ℂ → Circle`.

## Main results

* `TauCeti.Vortex.tendsto_cocompact_of_mem_sobolevGaugeGroup`: elements of `G_s` tend to one at
  infinity.
* `TauCeti.Vortex.mem_sobolevGaugeGroup_inf_framedGaugeGroup`: the smooth subgroup of `G_s` is
  `G_s ⊓ framedGaugeGroup`.
* `TauCeti.Vortex.mem_sobolevGaugeGroup_of_hasCompactSupport`,
  `TauCeti.Vortex.exp_mem_sobolevGaugeGroup`: compactly supported smooth gauges lie in `G_s`.
* `TauCeti.Vortex.contDiff_of_mem_sobolevGaugeGroup`: elements of `G_s` are `C^k` for
  `s > k + 1`.
* `TauCeti.Vortex.gaugeForm_apply_mem_realSobolevFunctions`: for a gauge in `G_(s+1)`,
  `Im (u⁻¹ du)` has coefficients in `H^s`.
* `TauCeti.Vortex.gaugeLinearAction_mem_sobolevFields_iff`: the linear action of `G_s` preserves
  `H^s` variations.
* `TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`: the action of `G_(k+1)` preserves the
  affine field space `A_m^k`, for every integer `k > 1`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter Module TemperedDistribution
open scoped ContDiff Topology

/-- **The Sobolev framed gauge group `G_s`**, `s > 1`: the continuous circle-valued maps `u` on
the plane with `u - 1 ∈ H^s(ℂ; ℂ)`, that is, with `Re u - 1` and `Im u` in `H^s`. -/
def sobolevGaugeGroup {s : ℝ} (hs : 1 < s) : Subgroup (ℂ → Circle) where
  carrier := {u | Continuous u ∧ (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
    (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2}
  one_mem' := by
    refine ⟨continuous_const, ?_, ?_⟩ <;>
    · convert zero_mem (realSobolevFunctions ℂ s 2) using 1
      ext z
      simp
  mul_mem' := by
    rintro u v ⟨hu, hu₁, hu₂⟩ ⟨hv, hv₁, hv₂⟩
    have hmul {f g : ℂ → ℝ} (hf : f ∈ realSobolevFunctions ℂ s 2)
        (hg : g ∈ realSobolevFunctions ℂ s 2) : f * g ∈ realSobolevFunctions ℂ s 2 :=
      mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) hf hg
    -- With `u = (1 + a) + i b` and `v = (1 + c) + i d`, the product is
    -- `(1 + (a c + a + c - b d)) + i (a d + d + b c + b)`.
    refine ⟨hu.mul hv, ?_, ?_⟩
    · convert add_mem (add_mem (add_mem (hmul hu₁ hv₁) hu₁) hv₁) (neg_mem (hmul hu₂ hv₂))
        using 1
      ext z
      simp only [Pi.mul_apply, Circle.coe_mul, mul_re, Pi.add_apply, Pi.neg_apply]
      ring
    · convert add_mem (add_mem (add_mem (hmul hu₁ hv₂) hv₂) (hmul hu₂ hv₁)) hu₂ using 1
      ext z
      simp only [Pi.mul_apply, Circle.coe_mul, mul_im, Pi.add_apply]
      ring
  inv_mem' := by
    rintro u ⟨hu, hu₁, hu₂⟩
    refine ⟨hu.inv, ?_, ?_⟩
    · simpa only [Pi.inv_apply, Circle.coe_inv_eq_conj, conj_re] using hu₁
    · convert neg_mem hu₂ using 1
      ext z
      simp

/-- Membership in `G_s`: continuity, and `Re u - 1`, `Im u` in `H^s`. -/
@[simp]
theorem mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) (u : ℂ → Circle) :
    u ∈ sobolevGaugeGroup hs ↔ Continuous u ∧
      (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ s 2 ∧
      (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ s 2 :=
  Iff.rfl

/-- The Sobolev gauge groups decrease as the order increases: `G_s ≤ G_s'` for `1 < s' ≤ s`. -/
theorem sobolevGaugeGroup_mono {s s' : ℝ} (hs' : 1 < s') (h : s' ≤ s) :
    sobolevGaugeGroup (hs'.trans_le h) ≤ sobolevGaugeGroup hs' := by
  intro u hu
  obtain ⟨hu, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num) h
  exact (mem_sobolevGaugeGroup _ u).2 ⟨hu, hmono hu₁, hmono hu₂⟩

/-- **Elements of `G_s` tend to one at infinity**, by the Sobolev embedding of `H^s`, `s > 1`, into
the continuous functions vanishing at infinity. -/
theorem tendsto_cocompact_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) : Tendsto u (cocompact ℂ) (𝓝 1) := by
  obtain ⟨hu, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hs' := finrank_real_complex_lt_two_mul hs
  have hre := tendsto_cocompact_of_mem_realSobolevFunctions hs' hu₁
    ((continuous_re.comp (continuous_subtype_val.comp hu)).sub continuous_const)
  have him := tendsto_cocompact_of_mem_realSobolevFunctions hs' hu₂
    (continuous_im.comp (continuous_subtype_val.comp hu))
  have h := (((continuous_ofReal.tendsto 0).comp hre).add
    (((continuous_ofReal.tendsto 0).comp him).mul_const I)).const_add (1 : ℂ)
  have hfun : (fun z ↦ (u z : ℂ)) =
      fun z ↦ 1 + ((((u z : ℂ).re - 1 : ℝ) : ℂ) + ((u z : ℂ).im : ℂ) * I) := by
    ext1 z
    nth_rewrite 1 [← re_add_im (u z : ℂ)]
    push_cast
    ring
  have hc : Tendsto (fun z ↦ (u z : ℂ)) (cocompact ℂ) (𝓝 1) := by
    rw [hfun]
    simpa using h
  exact tendsto_subtype_rng.2 (by simpa using hc)

/-- **Smooth elements of `G_s` are smooth framed gauges.** -/
theorem mem_framedGaugeGroup_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) :
    u ∈ framedGaugeGroup :=
  (mem_framedGaugeGroup u).2 ⟨hsmooth, tendsto_cocompact_of_mem_sobolevGaugeGroup hu⟩

/-- **The smooth subgroup of `G_s`** is its intersection with the smooth framed gauge group: it
consists of the elements of `G_s` that are smooth. -/
theorem mem_sobolevGaugeGroup_inf_framedGaugeGroup {s : ℝ} (hs : 1 < s) (u : ℂ → Circle) :
    u ∈ sobolevGaugeGroup hs ⊓ framedGaugeGroup ↔
      u ∈ sobolevGaugeGroup hs ∧ ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)) :=
  ⟨fun h ↦ ⟨Subgroup.mem_inf.1 h |>.1, ((mem_framedGaugeGroup u).1 (Subgroup.mem_inf.1 h).2).1⟩,
    fun h ↦ Subgroup.mem_inf.2 ⟨h.1, mem_framedGaugeGroup_of_mem_sobolevGaugeGroup h.1 h.2⟩⟩

/-- **Compactly supported smooth gauges lie in `G_s`**: if `u` is smooth and `u - 1` has compact
support, then `u` lies in every `G_s`. -/
theorem mem_sobolevGaugeGroup_of_hasCompactSupport {s : ℝ} (hs : 1 < s) {u : ℂ → Circle}
    (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)))
    (hc : HasCompactSupport (fun z ↦ (u z : ℂ) - 1)) : u ∈ sobolevGaugeGroup hs := by
  have hd : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ) - 1) := hsmooth.sub contDiff_const
  refine (mem_sobolevGaugeGroup hs u).2 ⟨continuous_induced_rng.2 hsmooth.continuous, ?_, ?_⟩
  · convert mem_realSobolevFunctions_of_hasCompactSupport (reCLM.contDiff.comp hd)
      (hc.comp_left (g := re) zero_re) s using 1
    ext z
    simp
  · convert mem_realSobolevFunctions_of_hasCompactSupport (imCLM.contDiff.comp hd)
      (hc.comp_left (g := im) zero_im) s using 1
    ext z
    simp

/-- A smooth compactly supported phase `f` gives the gauge `exp (i f)` in every `G_s`. -/
theorem exp_mem_sobolevGaugeGroup {s : ℝ} (hs : 1 < s) {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : (fun w ↦ Circle.exp (f w)) ∈ sobolevGaugeGroup hs := by
  refine mem_sobolevGaugeGroup_of_hasCompactSupport hs ?_ ?_
  · exact ((mem_framedGaugeGroup _).1 (exp_mem_framedGaugeGroup hf hc.is_zero_at_infty)).1
  · simpa only [Function.comp_def, Circle.coe_exp] using
      hc.comp_left (g := fun t : ℝ ↦ Complex.exp (t * I) - 1) (by simp)

/-- **Sobolev gauges are `C^k`.** For `s > k + 1`, every element of `G_s` is of class `C^k`, by
the Sobolev embedding of `H^s(ℂ)` into `C^k`. In particular the elements of `G_(s+1)`, `s > 1`, are
`C¹`, so their logarithmic derivative `u⁻¹ du` is defined classically. -/
theorem contDiff_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {k : ℕ} (hk : k + 1 < s)
    {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup hs) : ContDiff ℝ k (fun z ↦ (u z : ℂ)) := by
  obtain ⟨hu, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hk' : (finrank ℝ ℂ : ℝ) + 2 * k < 2 * s := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  have hre := contDiff_of_mem_realSobolevFunctions hk' hu₁
    ((continuous_re.comp (continuous_subtype_val.comp hu)).sub continuous_const)
  have him := contDiff_of_mem_realSobolevFunctions hk' hu₂
    (continuous_im.comp (continuous_subtype_val.comp hu))
  have hfun : (fun z ↦ (u z : ℂ)) =
      fun z ↦ ofRealCLM ((u z : ℂ).re - 1) + 1 + ofRealCLM (u z : ℂ).im * I := by
    ext1 z
    nth_rewrite 1 [← re_add_im (u z : ℂ)]
    simp
  rw [hfun]
  exact ((ofRealCLM.contDiff.comp hre).add contDiff_const).add
    ((ofRealCLM.contDiff.comp him).mul contDiff_const)

/-- **The connection increment of a Sobolev gauge.** For `s > 1` and a gauge `u ∈ G_(s+1)`, which
is `C¹` by `contDiff_of_mem_sobolevGaugeGroup`, the real one-form `Im (u⁻¹ du)` has coefficients in
`H^s`: in each direction `v`, `Im (u⁻¹ du) (v) = Re u · ∂_v Im u - Im u · ∂_v Re u`, a combination
of products of `H^s` functions. Hence the action `a ↦ a - u⁻¹ du` preserves connections whose
coefficients differ from a reference by `H^s` functions. -/
theorem gaugeForm_apply_mem_realSobolevFunctions {s : ℝ} (hs : 1 < s) {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup (hs.trans (lt_add_one s))) (v : ℂ) :
    (fun z ↦ gaugeForm u z v) ∈ realSobolevFunctions ℂ s 2 := by
  have hC1 := contDiff_of_mem_sobolevGaugeGroup (k := 1) (by push_cast; linarith) hu
  obtain ⟨-, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    (lt_add_one s).le
  have hmul {f g : ℂ → ℝ} (hf : f ∈ realSobolevFunctions ℂ s 2)
      (hg : g ∈ realSobolevFunctions ℂ s 2) : f * g ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) hf hg
  -- The directional derivatives of `Re u - 1` and `Im u` are those of `Re u` and `Im u`.
  have hre : ContDiff ℝ 1 (fun z ↦ (u z : ℂ).re - 1) :=
    (reCLM.contDiff.comp hC1).sub contDiff_const
  have him : ContDiff ℝ 1 (fun z ↦ (u z : ℂ).im) := imCLM.contDiff.comp hC1
  have hd (z : ℂ) := (hC1.differentiable one_ne_zero z).hasFDerivAt
  have hDre : (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ).re - 1) z v) =
      fun z ↦ (fderiv ℝ (fun z ↦ (u z : ℂ)) z v).re := by
    ext z
    have h : HasFDerivAt (fun z ↦ (u z : ℂ).re - 1)
        (reCLM.comp (fderiv ℝ (fun z ↦ (u z : ℂ)) z)) z :=
      (reCLM.hasFDerivAt.comp z (hd z)).sub_const 1
    simp [h.fderiv]
  have hDim : (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ).im) z v) =
      fun z ↦ (fderiv ℝ (fun z ↦ (u z : ℂ)) z v).im := by
    ext z
    have h : HasFDerivAt (fun z ↦ (u z : ℂ).im)
        (imCLM.comp (fderiv ℝ (fun z ↦ (u z : ℂ)) z)) z :=
      imCLM.hasFDerivAt.comp z (hd z)
    simp [h.fderiv]
  have hDre_mem := fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num)
    (by linarith) hre hu₁ v
  have hDim_mem := fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num)
    (by linarith) him hu₂ v
  rw [hDre] at hDre_mem
  rw [hDim] at hDim_mem
  -- `Im (conj u · du(v)) = (Re u - 1) ∂_v Im u + ∂_v Im u - Im u ∂_v Re u`.
  convert add_mem (add_mem (hmul (hmono hu₁) hDim_mem) hDim_mem)
    (neg_mem (hmul (hmono hu₂) hDre_mem)) using 1
  ext z
  simp only [gaugeForm_apply, mul_im, conj_re, conj_im, Pi.add_apply, Pi.neg_apply,
    Pi.mul_apply]
  ring

/-! ### The action on the affine field space -/

/-- **Sobolev gauges act on Sobolev variations.** For `s > 1`, the linear part of the action of
`u ∈ G_s`, which fixes the connection variation and multiplies the section variation by `u`,
preserves `H^s` fields: with `u = 1 + h`, the rotated section variation is `δα + h δα`, and
`H^s(ℂ)` is an algebra. -/
theorem gaugeLinearAction_mem_sobolevFields {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ sobolevFields s) : gaugeLinearAction u y ∈ sobolevFields s := by
  obtain ⟨-, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hmul {f g : ℂ → ℝ} (hf : f ∈ realSobolevFunctions ℂ s 2)
      (hg : g ∈ realSobolevFunctions ℂ s 2) : f * g ∈ realSobolevFunctions ℂ s 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs) hf hg
  have hc := mem_sobolevFields.1 hy
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · simpa [gaugeLinearAction_apply] using hc 0
  · simpa [gaugeLinearAction_apply] using hc 1
  · -- `Re u · δp - Im u · δq = (Re u - 1) δp + δp - Im u · δq`.
    convert add_mem (add_mem (hmul hu₁ (hc 2)) (hc 2)) (neg_mem (hmul hu₂ (hc 3))) using 1
    ext z
    simp [gaugeLinearAction_apply]
    ring
  · -- `Im u · δp + Re u · δq = Im u · δp + (Re u - 1) δq + δq`.
    convert add_mem (add_mem (hmul hu₂ (hc 2)) (hmul hu₁ (hc 3))) (hc 3) using 1
    ext z
    simp [gaugeLinearAction_apply]
    ring

/-- The linear action of `u ∈ G_s`, `s > 1`, preserves `H^s` fields in both directions. -/
@[simp]
theorem gaugeLinearAction_mem_sobolevFields_iff {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    gaugeLinearAction u y ∈ sobolevFields s ↔ y ∈ sobolevFields s :=
  ⟨fun h ↦ by simpa using gaugeLinearAction_mem_sobolevFields (inv_mem hu) h,
    gaugeLinearAction_mem_sobolevFields hu⟩

/-- **A Sobolev gauge moves the reference field by an `H^k` field.** For an integer `k > 1` and
`u ∈ G_(k+1)`, the field `u · (a_m, α_m) - (a_m, α_m)` lies in `H^k`. Its connection part is
`-u⁻¹ du`, whose coefficients lie in `H^k` (`gaugeForm_apply_mem_realSobolevFunctions`), and its
section part is `(u - 1) α_m`, the product of an `H^(k+1)` function with the smooth reference
section, all of whose derivatives are bounded. -/
theorem gaugeTransform_referenceField_sub_mem_sobolevFields {k : ℕ} (hk : 1 < k)
    {hs : 1 < (k : ℝ) + 1} {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup hs)
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    gaugeTransform u (referenceField f m) - referenceField f m ∈ sobolevFields k := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨-, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    (le_add_of_nonneg_right zero_le_one : (k : ℝ) ≤ k + 1)
  have hform (v : ℂ) := gaugeForm_apply_mem_realSobolevFunctions hk' hu v
  -- The connection part `-u⁻¹ du` and the two section fields multiplied by `α_m`.
  have h₀ : (fun z ↦ !₂[-gaugeForm u z 1, -gaugeForm u z I, 0, 0]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    · convert neg_mem (hform 1) using 1
      ext z
      simp [-gaugeForm_apply]
    · convert neg_mem (hform I) using 1
      ext z
      simp [-gaugeForm_apply]
    · exact zero_mem _
    · exact zero_mem _
  have h₁ : (fun z ↦ !₂[0, 0, (u z : ℂ).re - 1, (u z : ℂ).im]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    · exact zero_mem _
    · exact zero_mem _
    · simpa using hmono hu₁
    · simpa using hmono hu₂
  have h₂ : (fun z ↦ !₂[0, 0, -(u z : ℂ).im, (u z : ℂ).re - 1]) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    · exact zero_mem _
    · exact zero_mem _
    · convert neg_mem (hmono hu₂) using 1
      ext z
      simp
    · simpa using hmono hu₁
  -- The coordinates of the reference section are smooth with bounded derivatives.
  have hbound (i : Fin 4) : ∃ M, 0 ≤ M ∧
      ∀ j ≤ k, ∀ z, ‖iteratedFDeriv ℝ j (fun z ↦ referenceField f m z i) z‖ ≤ M := by
    choose C hC using fun j ↦ exists_norm_iteratedFDeriv_referenceField_apply_le f m j i
    refine ⟨∑ j ∈ Finset.range (k + 1), |C j|, by positivity, fun j hj z ↦ (hC j z).trans ?_⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j ↦ |C j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  have hsmul (i : Fin 4) {w : ℂ → EuclideanSpace ℝ (Fin 4)} (hw : w ∈ sobolevFields k) :
      (fun z ↦ referenceField f m z i • w z) ∈ sobolevFields k := by
    obtain ⟨M, hM, hMb⟩ := hbound i
    exact smul_mem_sobolevFields_natCast k (contDiff_euclidean.1 (contDiff_referenceField f m) i)
      hM hMb hw
  convert add_mem (add_mem h₀ (hsmul 2 h₁)) (hsmul 3 h₂) using 1
  ext z i
  fin_cases i <;> simp [gaugeTransform_apply] <;> ring

/-- **The Sobolev gauge group `G_(k+1)` acts on the affine field space `A_m^k`**, for every integer
`k > 1`: the charge-one action `(a, α) ↦ (a - u⁻¹ du, u α)` of `u ∈ G_(k+1)` maps `A_m^k` to
itself. Composition is multiplication of gauges (`gaugeTransform_mul`, which applies since the
elements of `G_(k+1)` are `C¹`). -/
theorem gaugeTransform_mem_framedFieldSpace {k : ℕ} (hk : 1 < k) {hs : 1 < (k : ℝ) + 1}
    {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup hs) {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    gaugeTransform u x ∈ framedFieldSpace f m k := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  rw [mem_framedFieldSpace] at hx ⊢
  have h : gaugeTransform u x - referenceField f m =
      gaugeLinearAction u (x - referenceField f m) +
        (gaugeTransform u (referenceField f m) - referenceField f m) := by
    rw [← gaugeTransform_sub_gaugeTransform]
    abel
  rw [h]
  exact add_mem (gaugeLinearAction_mem_sobolevFields
    (sobolevGaugeGroup_mono hk' (le_add_of_nonneg_right zero_le_one) hu) hx)
    (gaugeTransform_referenceField_sub_mem_sobolevFields hk hu f m)

/-- The action of `u ∈ G_(k+1)`, `k > 1`, preserves `A_m^k` in both directions. -/
@[simp]
theorem gaugeTransform_mem_framedFieldSpace_iff {k : ℕ} (hk : 1 < k) {hs : 1 < (k : ℝ) + 1}
    {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup hs) {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    gaugeTransform u x ∈ framedFieldSpace f m k ↔ x ∈ framedFieldSpace f m k := by
  refine ⟨fun h ↦ ?_, gaugeTransform_mem_framedFieldSpace hk hu⟩
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have hd {v : ℂ → Circle} (hv : v ∈ sobolevGaugeGroup hs) :
      Differentiable ℝ (fun z ↦ (v z : ℂ)) :=
    (contDiff_of_mem_sobolevGaugeGroup (k := 1) (by push_cast; linarith) hv).differentiable
      one_ne_zero
  have h' := gaugeTransform_mem_framedFieldSpace hk (inv_mem hu) h
  rwa [← gaugeTransform_mul (hd (inv_mem hu)) (hd hu), inv_mul_cancel, gaugeTransform_one] at h'

end TauCeti.Vortex
