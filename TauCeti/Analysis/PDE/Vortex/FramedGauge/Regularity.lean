/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Gauges between framed Sobolev fields are Sobolev gauges

A smooth framed gauge need not lie in the Sobolev gauge group `G_(k+1)`
(`TauCeti.Vortex.sobolevGaugeGroup`): a phase tending to one with a `1 / |z|` tail is not square
integrable on the plane. This file shows that such gauges never relate two fields of the affine
space `A_m^k` (`TauCeti.Vortex.framedFieldSpace`). If a `C²` gauge `u` carries a field `x` of
`A_m^k`, `k ≥ 2`, to another field of `A_m^k`, then `u ∈ G_(k+1)`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`). So two representatives in
`A_m^k` of the same smooth framed gauge orbit differ by an element of `G_(k+1)`: every smooth gauge
equivalence between points of `A_m^k` is already an equivalence under `G_(k+1)`.

The argument reads off `u` from the two fields, with `ω = Im (u⁻¹ du)` (`TauCeti.Vortex.gaugeForm`)
and `h = u - 1`:

* the connection forms differ by `ω`, so `ω ∈ H^k`
  (`TauCeti.Vortex.gaugeForm_apply_mem_realSobolevFunctions_of_mem_framedFieldSpace`);
* the sections differ by `h α_x`. Where the reference section has unit modulus,
  `|h| ≤ |h α_x| + 2 |α_x - α_ref|`, and the remaining disc is bounded, so `h ∈ L²`
  (`TauCeti.Vortex.memLp_coe_sub_one_of_mem_framedFieldSpace`);
* `dh = i u ω`, that is `∂_v Re u = -Im u · ω(v)` and `∂_v Im u = Re u · ω(v)`. Since `|u| = 1`,
  the first derivatives of `Re u · ω(v)` and `Im u · ω(v)` are bounded by
  `|∂ω(v)| + |ω(v) ω(w)|`, which lies in `L²` because `∂ω(v) ∈ H^(k-1)` and `H^k(ℂ)` is an
  algebra. Hence `h ∈ H²`. From there the algebra property of `H^j(ℂ)`, `j ≥ 2`, raises the order
  one step at a time up to `H^(k+1)`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} {u : ℂ → Circle}

/-- **The connection difference of two framed fields.** If a gauge `u` carries a field of `A_m^s`
to another field of `A_m^s`, then its logarithmic derivative `Im (u⁻¹ du)` is the difference of
the two connection forms, so its coefficients lie in `H^s`. -/
theorem gaugeForm_apply_mem_realSobolevFunctions_of_mem_framedFieldSpace {s : ℝ}
    (hx : x ∈ framedFieldSpace f m s) (hux : gaugeTransform u x ∈ framedFieldSpace f m s)
    (v : ℂ) : (fun z ↦ gaugeForm u z v) ∈ realSobolevFunctions ℂ s 2 := by
  have hd := mem_sobolevFields.1
    (sub_mem (mem_framedFieldSpace.1 hx) (mem_framedFieldSpace.1 hux))
  convert add_mem ((realSobolevFunctions ℂ s 2).smul_mem v.re (hd 0))
    ((realSobolevFunctions ℂ s 2).smul_mem v.im (hd 1)) using 1
  ext z
  have hv : gaugeForm u z v = v.re * gaugeForm u z 1 + v.im * gaugeForm u z I := by
    calc gaugeForm u z v = gaugeForm u z (v.re • (1 : ℂ) + v.im • I) := by
          rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      _ = _ := by simp only [map_add, map_smul, smul_eq_mul]
  simp only [hv, gaugeTransform_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

/-- **A gauge between two framed fields is square integrable about one.** If a continuous gauge
`u` carries a field `x` of `A_m^s` to another field of `A_m^s`, then `u - 1 ∈ L²`. Where the
reference section has unit modulus, `|u - 1| ≤ |(u - 1) α_x| + 2 |α_x - α_ref|`, and
`(u - 1) α_x` is the difference of the two sections; on the remaining disc `|u - 1| ≤ 2`. -/
theorem memLp_coe_sub_one_of_mem_framedFieldSpace {s : ℝ}
    (hx : x ∈ framedFieldSpace f m s) (hu : Continuous fun z ↦ (u z : ℂ))
    (hux : gaugeTransform u x ∈ framedFieldSpace f m s) :
    MemLp (fun z ↦ (u z : ℂ) - 1) 2 volume := by
  have hρ : MemLp (fun z ↦ 1 - ‖referenceSection f m z‖) 2 volume :=
    (continuous_const.sub (contDiff_referenceSection f m).continuous.norm)
      |>.memLp_of_hasCompactSupport (hasCompactSupport_one_sub_norm_referenceSection f m)
  have hdx := memLp_sectionValue_of_mem_sobolevFields (mem_framedFieldSpace.1 hx)
  have hdux := memLp_sectionValue_of_mem_sobolevFields (mem_framedFieldSpace.1 hux)
  have hg := (hdux.sub hdx).norm.add ((hdx.norm.const_mul 2).add (hρ.const_mul 2))
  refine hg.of_le (hu.sub continuous_const).aestronglyMeasurable (.of_forall fun z ↦ ?_)
  refine le_trans ?_ (Real.le_norm_self _)
  -- The sections differ by `(u - 1) α_x`, and `α_x - α_ref` is the section of `x - x_ref`.
  have hdiff : sectionValue (gaugeTransform u x - referenceField f m) z -
      sectionValue (x - referenceField f m) z = ((u z : ℂ) - 1) * sectionValue x z := by
    simp only [sectionValue_sub, sectionValue_gaugeTransform]
    ring
  have hxr : sectionValue (x - referenceField f m) z =
      sectionValue x z - referenceSection f m z := by
    simp [sectionValue_sub]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [hdiff, hxr, ← add_assoc]
  exact norm_sub_one_le_norm_sub_one_mul_add (Circle.norm_coe _)
    (norm_referenceSection_le_one f m z)

/-- With `|c| ≤ 1` and `dc = c' ω` for some `|c'| ≤ 1`, the product of `c` with a coefficient of
`ω = Im (u⁻¹ du) ∈ H^k`, `k ≥ 2`, lies in `H¹`: its derivative is `c ∂ω(v) + c' ω(v) ω(w)`, a sum
of an `H^(k-1)` function and a product of `H^k` functions, each times a bounded factor. This
applies to `c = Re u` and `c = Im u`. -/
private theorem mul_gaugeForm_mem_realSobolevFunctions_one {k : ℕ} (hk : 1 < k)
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ))
    (hω : ∀ v, (fun z ↦ gaugeForm u z v) ∈ realSobolevFunctions ℂ k 2)
    {c c' : ℂ → ℝ} (hc : ContDiff ℝ 1 c) (hcb : ∀ z, |c z| ≤ 1) (hc'b : ∀ z, |c' z| ≤ 1)
    (hdc : ∀ z w, fderiv ℝ c z w = c' z * gaugeForm u z w) (v : ℂ) :
    (fun z ↦ c z * gaugeForm u z v) ∈ realSobolevFunctions ℂ 1 2 := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have hmono : realSobolevFunctions ℂ k 2 ≤ realSobolevFunctions ℂ 0 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num) (by positivity)
  -- Each coefficient of `ω` is `C¹`, since `u` is `C²`.
  have hωC1 (v : ℂ) : ContDiff ℝ 1 fun z ↦ gaugeForm u z v := by
    simp only [gaugeForm_apply]
    exact imCLM.contDiff.comp ((conjCLE.contDiff.comp (hu.of_le (by norm_num))).mul
      ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const))
  have hωL2 (v : ℂ) := mem_realSobolevFunctions_zero_iff.1 (hmono (hω v))
  have hbound {g : ℂ → ℝ} {b : ℂ → ℝ} (hgc : Continuous g) (hb : MemLp b 2 volume)
      (hgb : ∀ z, |g z| ≤ b z) : g ∈ realSobolevFunctions ℂ 0 2 :=
    mem_realSobolevFunctions_zero_iff.2 (hb.of_le hgc.aestronglyMeasurable
      (.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using (hgb z).trans (le_abs_self _)))
  have hcω : (fun z ↦ c z * gaugeForm u z v) ∈ realSobolevFunctions ℂ 0 2 :=
    hbound (hc.continuous.mul (hωC1 v).continuous) (hωL2 v).abs fun z ↦ by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hcb z)
  convert mem_realSobolevFunctions_add_one_of_fderiv_apply (by norm_num) (by norm_num)
    (hc.mul (hωC1 v)) hcω fun w ↦ ?_ using 1
  · norm_num
  -- The derivative in direction `w` is `c ∂_w ω(v) + c' ω(v) ω(w)`.
  have hD : ∀ z, fderiv ℝ (fun z ↦ c z * gaugeForm u z v) z w =
      c z * fderiv ℝ (fun z ↦ gaugeForm u z v) z w +
        c' z * (gaugeForm u z v * gaugeForm u z w) := by
    intro z
    rw [fderiv_fun_mul (hc.differentiable one_ne_zero z)
      ((hωC1 v).differentiable one_ne_zero z)]
    simp only [add_apply, smul_apply, smul_eq_mul, hdc]
    ring
  have hdω : (fun z ↦ fderiv ℝ (fun z ↦ gaugeForm u z v) z w) ∈
      realSobolevFunctions ℂ ((k : ℝ) - 1) 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (by linarith) (hωC1 v)
      (by simpa using hω v) w
  have hωω : (fun z ↦ gaugeForm u z v * gaugeForm u z w) ∈ realSobolevFunctions ℂ k 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hk') (hω v) (hω w)
  have hdω0 := mem_realSobolevFunctions_zero_iff.1
    (realSobolevFunctions_mono (by norm_num) (by norm_num) (by linarith) hdω)
  have hωω0 := mem_realSobolevFunctions_zero_iff.1 (hmono hωω)
  refine hbound (((hc.mul (hωC1 v)).continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (hdω0.norm.add hωω0.norm) fun z ↦ ?_
  rw [hD, Pi.add_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (hcb z))
    (mul_le_of_le_one_left (abs_nonneg _) (hc'b z))

/-- The derivative of `Re u - 1` in direction `w` is `-Im u · ω(w)`, with `ω = Im (u⁻¹ du)`. -/
private theorem fderiv_re_sub_one_apply_eq (hu : Differentiable ℝ fun z ↦ (u z : ℂ)) (w : ℂ) :
    (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ).re - 1) z w) =
      -fun z ↦ (u z : ℂ).im * gaugeForm u z w := by
  ext z
  rw [fderiv_sub_const, fderiv_re_coe_eq_neg_im_mul_gaugeForm (hu z), Pi.neg_apply, neg_mul]

/-- **Order two.** If a `C²` gauge `u` carries a field of `A_m^k`, `k ≥ 2`, to another field of
`A_m^k`, then `Re u - 1` and `Im u` lie in `H²`. They lie in `L²`, and their derivatives
`-Im u · ω(w)` and `Re u · ω(w)` lie in `H¹`. -/
private theorem re_sub_one_mem_and_im_mem_realSobolevFunctions_two {k : ℕ} (hk : 1 < k)
    (hx : x ∈ framedFieldSpace f m k) (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ))
    (hux : gaugeTransform u x ∈ framedFieldSpace f m k) :
    (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ 2 2 ∧
      (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ 2 2 := by
  have hω := gaugeForm_apply_mem_realSobolevFunctions_of_mem_framedFieldSpace hx hux
  have hdu : Differentiable ℝ fun z ↦ (u z : ℂ) := hu.differentiable (by norm_num)
  have hre : ContDiff ℝ 1 fun z ↦ (u z : ℂ).re := reCLM.contDiff.comp (hu.of_le (by norm_num))
  have him : ContDiff ℝ 1 fun z ↦ (u z : ℂ).im := imCLM.contDiff.comp (hu.of_le (by norm_num))
  have hreb (z : ℂ) : |(u z : ℂ).re| ≤ 1 := (abs_re_le_norm _).trans_eq (Circle.norm_coe _)
  have himb (z : ℂ) : |(u z : ℂ).im| ≤ 1 := (abs_im_le_norm _).trans_eq (Circle.norm_coe _)
  have hreω (w : ℂ) : (fun z ↦ (u z : ℂ).re * gaugeForm u z w) ∈ realSobolevFunctions ℂ 1 2 :=
    mul_gaugeForm_mem_realSobolevFunctions_one hk hu hω hre hreb (c' := fun z ↦ -(u z : ℂ).im)
      (fun z ↦ by rw [abs_neg]; exact himb z)
      (fun z w ↦ fderiv_re_coe_eq_neg_im_mul_gaugeForm (hdu z) w) w
  have himω (w : ℂ) : (fun z ↦ (u z : ℂ).im * gaugeForm u z w) ∈ realSobolevFunctions ℂ 1 2 :=
    mul_gaugeForm_mem_realSobolevFunctions_one hk hu hω him himb hreb
      (fun z w ↦ fderiv_im_coe_eq_re_mul_gaugeForm (hdu z) w) w
  have hDim (w : ℂ) : (fun z ↦ fderiv ℝ (fun z ↦ (u z : ℂ).im) z w) =
      fun z ↦ (u z : ℂ).re * gaugeForm u z w :=
    funext fun z ↦ fderiv_im_coe_eq_re_mul_gaugeForm (hdu z) w
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    zero_le_one
  have hL2 := memLp_coe_sub_one_of_mem_framedFieldSpace hx hu.continuous hux
  have hstep {s : ℝ} {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hgs : g ∈ realSobolevFunctions ℂ s 2)
      (hdg : ∀ w, (fun z ↦ fderiv ℝ g z w) ∈ realSobolevFunctions ℂ s 2) :
      g ∈ realSobolevFunctions ℂ (s + 1) 2 :=
    mem_realSobolevFunctions_add_one_of_fderiv_apply (by norm_num) (by norm_num) hg hgs hdg
  have hre1 : ContDiff ℝ 1 fun z ↦ (u z : ℂ).re - 1 := hre.sub contDiff_const
  -- Order `0`, then orders `1` and `2`.
  have hre₀ := hstep hre1 (mem_realSobolevFunctions_zero_iff.2 (by simpa using hL2.re))
    fun w ↦ fderiv_re_sub_one_apply_eq hdu w ▸ neg_mem (hmono (himω w))
  have him₀ := hstep him (mem_realSobolevFunctions_zero_iff.2 (by simpa using hL2.im))
    fun w ↦ hDim w ▸ hmono (hreω w)
  rw [zero_add] at hre₀ him₀
  refine ⟨?_, ?_⟩
  · convert hstep hre1 hre₀ fun w ↦ fderiv_re_sub_one_apply_eq hdu w ▸ neg_mem (himω w) using 2
    norm_num
  · convert hstep him him₀ fun w ↦ hDim w ▸ hreω w using 2
    norm_num

/-- **Raising the order.** Let `u` be a `C¹` gauge with `ω = Im (u⁻¹ du) ∈ H^k`. If `Re u - 1`
and `Im u` lie in `H^j` for some `2 ≤ j ≤ k`, then they lie in `H^(j+1)`: their derivatives
`-Im u · ω(w)` and `(Re u - 1) ω(w) + ω(w)` lie in the algebra `H^j`. -/
private theorem re_sub_one_mem_and_im_mem_realSobolevFunctions_succ {k j : ℕ} (hj : 2 ≤ j)
    (hjk : j ≤ k) (hu : ContDiff ℝ 1 fun z ↦ (u z : ℂ))
    (hω : ∀ v, (fun z ↦ gaugeForm u z v) ∈ realSobolevFunctions ℂ k 2)
    (hre : (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ j 2)
    (him : (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ j 2) :
    (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ (j + 1 : ℕ) 2 ∧
      (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ (j + 1 : ℕ) 2 := by
  have hdu : Differentiable ℝ fun z ↦ (u z : ℂ) := hu.differentiable one_ne_zero
  have hωj (w : ℂ) : (fun z ↦ gaugeForm u z w) ∈ realSobolevFunctions ℂ j 2 :=
    realSobolevFunctions_mono (by norm_num) (by norm_num) (by exact_mod_cast hjk) (hω w)
  have hmul {g g' : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ j 2)
      (hg' : g' ∈ realSobolevFunctions ℂ j 2) : g * g' ∈ realSobolevFunctions ℂ j 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul
      (by exact_mod_cast (by omega : 1 < j))) hg hg'
  push_cast
  refine ⟨mem_realSobolevFunctions_add_one_of_fderiv_apply (by norm_num) (by norm_num)
    ((reCLM.contDiff.comp hu).sub contDiff_const) hre
    fun w ↦ fderiv_re_sub_one_apply_eq hdu w ▸ neg_mem (hmul him (hωj w)), ?_⟩
  refine mem_realSobolevFunctions_add_one_of_fderiv_apply (by norm_num) (by norm_num)
    (imCLM.contDiff.comp hu) him fun w ↦ ?_
  convert add_mem (hmul hre (hωj w)) (hωj w) using 1
  ext z
  simp only [fderiv_im_coe_eq_re_mul_gaugeForm (hdu z), Pi.add_apply, Pi.mul_apply]
  ring

/-- **Gauges between framed Sobolev fields are Sobolev gauges.** If a `C²` gauge `u` carries a
field `x` of `A_m^k`, `k ≥ 2`, to another field of `A_m^k`, then `u` lies in the Sobolev gauge
group `G_(k+1)`. In particular two fields of `A_m^k` related by a smooth framed gauge are related by
an element of `G_(k+1)`, although a smooth framed gauge need not lie in `G_(k+1)`. -/
theorem mem_sobolevGaugeGroup_of_mem_framedFieldSpace {k : ℕ} (hk : 1 < k)
    (hx : x ∈ framedFieldSpace f m k) (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ))
    (hux : gaugeTransform u x ∈ framedFieldSpace f m k) :
    u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega) := by
  have hω := gaugeForm_apply_mem_realSobolevFunctions_of_mem_framedFieldSpace hx hux
  have hind : ∀ j : ℕ, 2 ≤ j → j ≤ k + 1 →
      (fun z ↦ (u z : ℂ).re - 1) ∈ realSobolevFunctions ℂ j 2 ∧
        (fun z ↦ (u z : ℂ).im) ∈ realSobolevFunctions ℂ j 2 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      exact fun _ ↦ by
        simpa using re_sub_one_mem_and_im_mem_realSobolevFunctions_two hk hx hu hux
    | succ j hj ih =>
      intro hjk
      obtain ⟨hre, him⟩ := ih (by omega)
      exact re_sub_one_mem_and_im_mem_realSobolevFunctions_succ hj (by omega)
        (hu.of_le (by norm_num)) hω hre him
  obtain ⟨hre, him⟩ := hind (k + 1) (by omega) le_rfl
  push_cast at hre him
  exact (mem_sobolevGaugeGroup _ u).2 ⟨continuous_induced_rng.2 hu.continuous, hre, him⟩

end TauCeti.Vortex
