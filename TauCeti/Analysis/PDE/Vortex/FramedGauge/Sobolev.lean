/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.Wkp.ContDiffRepresentative

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
with a `1 / |z|` tail is not square integrable on the plane. By the Sobolev embedding, an element
of `G_s` is `Cʲ` whenever `j + 2 ≤ s`.

For a `C¹` gauge `u ∈ G_(s+1)`, the real one-form `Im (u⁻¹ du)` (`TauCeti.Vortex.gaugeForm`)
has coefficients in `H^s`. Its product with `i` is the connection increment `u⁻¹ du` of the
action `(a, α) ↦ (a - u⁻¹ du, u α)`, so the `C¹` elements of `G_(s+1)` preserve the connection
part of `A_m^s`.

For an integer `k ≥ 2`, the section part is preserved as well: `H^k` is an algebra, and it is
stable under multiplication by the reference section, whose derivatives are bounded. Hence the
charge-one action of `G_(k+1)` maps `A_m^k` into itself, giving an action of `G_(k+1)` on
`A_m^k`.

No topology or Banach Lie group charts on `G_s` are constructed here, and neither the slice
theorem nor the quotient is treated.

## Main definitions

* `TauCeti.Vortex.sobolevGaugeGroup hs`: the group `G_s`, `s > 1`, as a subgroup of `ℂ → Circle`.

## Main results

* `TauCeti.Vortex.tendsto_cocompact_of_mem_sobolevGaugeGroup`: elements of `G_s` tend to one at
  infinity.
* `TauCeti.Vortex.contDiff_of_mem_sobolevGaugeGroup`: elements of `G_s` are `Cʲ` for
  `j + 2 ≤ s`.
* `TauCeti.Vortex.mem_sobolevGaugeGroup_inf_framedGaugeGroup`: the smooth subgroup of `G_s` is
  `G_s ⊓ framedGaugeGroup`.
* `TauCeti.Vortex.mem_sobolevGaugeGroup_of_hasCompactSupport`,
  `TauCeti.Vortex.exp_mem_sobolevGaugeGroup`: compactly supported smooth gauges lie in `G_s`.
* `TauCeti.Vortex.gaugeForm_apply_mem_realSobolevFunctions`: for a `C¹` gauge in `G_(s+1)`,
  `Im (u⁻¹ du)` has coefficients in `H^s`.
* `TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace`: for `k ≥ 2`, the charge-one action of
  `G_(k+1)` preserves `A_m^k`; this gives a `MulAction` of `G_(k+1)` on `A_m^k`.

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

/-- **Regularity of Sobolev gauges.** By the Sobolev embedding, an element of `G_s` is `Cʲ`
whenever `j + 2 ≤ s`. -/
theorem contDiff_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) {j : ℕ} (hj : (j : ℝ) + 2 ≤ s) :
    ContDiff ℝ j (fun z ↦ (u z : ℂ)) := by
  obtain ⟨hu, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup hs u).1 hu
  have hc : Continuous (fun z ↦ (u z : ℂ)) := continuous_subtype_val.comp hu
  have hk : finrank ℝ ℂ < 2 * 2 := by
    exact_mod_cast finrank_real_complex_lt_two_mul (by norm_num : (1 : ℝ) < 2)
  have hj' : ((2 : ℕ) + j : ℝ) ≤ s := by push_cast; linarith
  have hre := (contDiff_of_mem_realSobolevFunctions hk hu₁
    ((continuous_re.comp hc).sub continuous_const) hj').add (contDiff_const (c := (1 : ℝ)))
  have him := contDiff_of_mem_realSobolevFunctions hk hu₂ (continuous_im.comp hc) hj'
  convert (ofRealCLM.contDiff.comp hre).add ((ofRealCLM.contDiff.comp him).mul
    (contDiff_const (c := I))) using 1
  ext1 z
  simp [re_add_im]

/-- An element of `G_s`, `s ≥ 3`, is differentiable. -/
theorem differentiable_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup hs) (h : 3 ≤ s) : Differentiable ℝ (fun z ↦ (u z : ℂ)) :=
  (contDiff_of_mem_sobolevGaugeGroup hu (j := 1) (by norm_num; linarith)).differentiable
    one_ne_zero

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

/-- **The connection increment of a Sobolev gauge.** For `s > 1` and a `C¹` gauge `u ∈ G_(s+1)`,
the real one-form `Im (u⁻¹ du)` has coefficients in `H^s`: in each direction `v`,
`Im (u⁻¹ du) (v) = Re u · ∂_v Im u - Im u · ∂_v Re u`, a combination of products of `H^s`
functions. Hence the action `a ↦ a - u⁻¹ du` preserves connections whose coefficients differ from
a reference by `H^s` functions. -/
theorem gaugeForm_apply_mem_realSobolevFunctions {s : ℝ} (hs : 1 < s) {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup (hs.trans (lt_add_one s)))
    (hC1 : ContDiff ℝ 1 (fun z ↦ (u z : ℂ))) (v : ℂ) :
    (fun z ↦ gaugeForm u z v) ∈ realSobolevFunctions ℂ s 2 := by
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

/-- A real-linear functional of the reference section has iterated derivatives bounded uniformly
through every finite order. -/
private theorem exists_bound_iteratedFDeriv_comp_referenceSection (f : ContDiffBump (0 : ℝ))
    (m : ℕ) (L : ℂ →L[ℝ] ℝ) (k : ℕ) :
    ∃ M ≥ 0, ∀ j ≤ k, ∀ z, ‖iteratedFDeriv ℝ j (L ∘ referenceSection f m) z‖ ≤ M := by
  choose C hC using exists_norm_iteratedFDeriv_referenceSection_le f m
  refine ⟨‖L‖ * ∑ j ∈ Finset.range (k + 1), |C j|, by positivity, fun j hj z ↦ ?_⟩
  refine (L.norm_iteratedFDeriv_comp_left
    ((contDiff_referenceSection f m).contDiffAt) (by exact_mod_cast le_top)).trans ?_
  refine mul_le_mul_of_nonneg_left ((hC j z).trans ((le_abs_self _).trans ?_)) (norm_nonneg _)
  exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (C i)) (Finset.mem_range.2 (by omega))

/-- Multiplication by a section coordinate of the reference field preserves integer-order
Sobolev functions. -/
private theorem referenceField_mul_mem_realSobolevFunctions (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (L : ℂ →L[ℝ] ℝ) (k : ℕ) {g : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ k 2) :
    (L ∘ referenceSection f m) * g ∈ realSobolevFunctions ℂ k 2 := by
  obtain ⟨M, hM, hbound⟩ := exists_bound_iteratedFDeriv_comp_referenceSection f m L k
  exact mul_mem_realSobolevFunctions_natCast k (L.contDiff.comp (contDiff_referenceSection f m))
    hM hbound hg

/-- **The Sobolev gauge action preserves the affine field space.** For `k ≥ 2`, the charge-one
action `(a, α) ↦ (a - u⁻¹ du, u α)` of `u ∈ G_(k+1)` maps `A_m^k` into itself. -/
theorem gaugeTransform_mem_framedFieldSpace {k : ℕ} (hk : 1 < k) {hs : 1 < (k : ℝ) + 1}
    {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup hs) {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    gaugeTransform u x ∈ framedFieldSpace f m k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hs' : (1 : ℝ) < k := by linarith
  have hC : ContDiff ℝ 1 (fun z ↦ (u z : ℂ)) :=
    contDiff_of_mem_sobolevGaugeGroup hu (j := 1) (by push_cast; linarith)
  have hmul {g h : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ k 2)
      (hh : h ∈ realSobolevFunctions ℂ k 2) : g * h ∈ realSobolevFunctions ℂ k 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul hs') hg hh
  have hω (v : ℂ) := gaugeForm_apply_mem_realSobolevFunctions hs' hu hC v
  rw [mem_framedFieldSpace, mem_sobolevFields] at hx ⊢
  obtain ⟨-, hA, hB⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    (lt_add_one (k : ℝ)).le
  replace hA := hmono hA
  replace hB := hmono hB
  have hσA := referenceField_mul_mem_realSobolevFunctions f m ((1 / 2 : ℝ) • reCLM) k hA
  have hσB := referenceField_mul_mem_realSobolevFunctions f m ((1 / 2 : ℝ) • reCLM) k hB
  have hτA := referenceField_mul_mem_realSobolevFunctions f m ((1 / 2 : ℝ) • imCLM) k hA
  have hτB := referenceField_mul_mem_realSobolevFunctions f m ((1 / 2 : ℝ) • imCLM) k hB
  intro i
  fin_cases i
  · convert sub_mem (hx 0) (hω 1) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert sub_mem (hx 1) (hω I) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert sub_mem (add_mem (add_mem hσA (hx 2)) (hmul hA (hx 2)))
      (add_mem hτB (hmul hB (hx 3))) using 1
    ext z
    simp [gaugeTransform_apply, referenceField_apply]
    ring
  · convert add_mem (add_mem (add_mem hσB (hx 3)) (hmul hB (hx 2)))
      (add_mem hτA (hmul hA (hx 3))) using 1
    ext z
    simp [gaugeTransform_apply, referenceField_apply]
    ring

/-- For `k ≥ 2`, the Sobolev gauge group `G_(k+1)` acts on the affine field space `A_m^k` by the
charge-one gauge action `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
instance {k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1} {f : ContDiffBump (0 : ℝ)} {m : ℕ} :
    MulAction (sobolevGaugeGroup hs) (framedFieldSpace f m k) where
  smul u x := ⟨gaugeTransform u x, gaugeTransform_mem_framedFieldSpace Fact.out u.2 x.2⟩
  one_smul x := Subtype.ext (gaugeTransform_one x)
  mul_smul u v x := by
    have h : (3 : ℝ) ≤ k + 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast (Fact.out : 1 < k)
      linarith
    exact Subtype.ext (gaugeTransform_mul (differentiable_of_mem_sobolevGaugeGroup u.2 h)
      (differentiable_of_mem_sobolevGaugeGroup v.2 h) x)

/-- The action of `G_(k+1)` on `A_m^k` is the charge-one gauge transformation. -/
@[simp]
theorem coe_sobolevGaugeGroup_smul {k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} (u : sobolevGaugeGroup hs)
    (x : framedFieldSpace f m k) :
    ((u • x : framedFieldSpace f m k) : ℂ → EuclideanSpace ℝ (Fin 4)) = gaugeTransform u x :=
  (rfl)

end TauCeti.Vortex
