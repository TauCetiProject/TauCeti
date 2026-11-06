/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.PDE.Vortex.Multiplier

/-!
# The Sobolev framed gauge group of plane vortices

For `s > 1` the Sobolev framed gauge group `G_s` (`TauCeti.Vortex.sobolevGaugeGroup s hs`)
consists of the continuous circle-valued maps `u = 1 + h` on the plane with `h ∈ H^s(ℂ; ℂ)`:
the real functions `Re u - 1` and `Im u` lie in `TauCeti.Vortex.sobolevFunctions s`. There is no
condition at a finite base point. The unit-modulus condition is imposed on the continuous
representative, as the values of `u` lie in the circle.

* `G_s` is a subgroup of the circle-valued maps. Products are closed because `H^s(ℂ)`, `s > 1`, is
  an algebra (`TauCeti.Vortex.mul_mem_sobolevFunctions`), and inverses because `u⁻¹ = conj u`.
* Every element tends to one at infinity (`TauCeti.Vortex.tendsto_of_mem_sobolevGaugeGroup`), by
  Sobolev embedding; this is the framing condition of the smooth framed gauge group
  `TauCeti.Vortex.framedGaugeGroup`, and the smooth elements of `G_s` belong to that group. An
  element of `G_s` is `Cʲ` whenever `j + 2 ≤ s`
  (`TauCeti.Vortex.contDiff_of_mem_sobolevGaugeGroup`).
* Conversely, a smooth gauge differing from one on a compact set lies in every `G_s`. A smooth
  framed gauge need not lie in `G_s`: a phase decaying like `1 / |z|` is not square integrable.
* For an integer `k ≥ 2`, the charge-one action `(a, α) ↦ (a - u⁻¹ du, u α)`
  (`TauCeti.Vortex.gaugeTransform`) of `G_(k+1)` preserves the affine field space `A_m^k`
  (`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace`). The logarithmic derivative
  `Im (u⁻¹ du)` lies in `H^k` (`TauCeti.Vortex.gaugeForm_apply_mem_sobolevFunctions`); the section
  term uses the algebra property together with the bounded derivatives of the reference section.
  This gives an action of `G_(k+1)` on `A_m^k`.

These are the gauge group and its action on the unweighted field space. The Banach manifold
structure of the group, the slice theorem and the quotient are not constructed here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

namespace TauCeti.Vortex

open Complex ComplexConjugate Filter
open scoped ContDiff Topology

/-- The Sobolev framed gauge group `G_s`, `s > 1`: continuous circle-valued maps `u` on the plane
with `u - 1 ∈ H^s(ℂ; ℂ)`, that is, with `Re u - 1` and `Im u` in `sobolevFunctions s`. -/
def sobolevGaugeGroup (s : ℝ) (hs : 1 < s) : Subgroup (ℂ → Circle) where
  carrier := {u | Continuous (fun z ↦ (u z : ℂ)) ∧
    (fun z ↦ (u z : ℂ).re - 1) ∈ sobolevFunctions s ∧ (fun z ↦ (u z : ℂ).im) ∈ sobolevFunctions s}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.one_apply, Circle.coe_one, one_re, sub_self, one_im]
    exact ⟨continuous_const, zero_mem _, zero_mem _⟩
  mul_mem' := by
    rintro u v ⟨hu, hur, hui⟩ ⟨hv, hvr, hvi⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [Pi.mul_apply, Circle.coe_mul]
      exact hu.mul hv
    · -- `Re (u v) - 1 = (Re u - 1)(Re v - 1) + (Re u - 1) + (Re v - 1) - Im u Im v`
      have h : (fun z ↦ ((u * v) z : ℂ).re - 1) =
          (fun z ↦ (u z : ℂ).re - 1) * (fun z ↦ (v z : ℂ).re - 1) + (fun z ↦ (u z : ℂ).re - 1) +
            (fun z ↦ (v z : ℂ).re - 1) - (fun z ↦ (u z : ℂ).im) * (fun z ↦ (v z : ℂ).im) := by
        ext z
        simp only [Pi.mul_apply, Circle.coe_mul, mul_re, Pi.add_apply, Pi.sub_apply]
        ring
      rw [h]
      exact sub_mem (add_mem (add_mem (mul_mem_sobolevFunctions hs hur hvr) hur) hvr)
        (mul_mem_sobolevFunctions hs hui hvi)
    · -- `Im (u v) = (Re u - 1) Im v + Im v + Im u (Re v - 1) + Im u`
      have h : (fun z ↦ ((u * v) z : ℂ).im) =
          (fun z ↦ (u z : ℂ).re - 1) * (fun z ↦ (v z : ℂ).im) + (fun z ↦ (v z : ℂ).im) +
            (fun z ↦ (u z : ℂ).im) * (fun z ↦ (v z : ℂ).re - 1) + (fun z ↦ (u z : ℂ).im) := by
        ext z
        simp only [Pi.mul_apply, Circle.coe_mul, mul_im, Pi.add_apply]
        ring
      rw [h]
      exact add_mem (add_mem (add_mem (mul_mem_sobolevFunctions hs hur hvi) hvi)
        (mul_mem_sobolevFunctions hs hui hvr)) hui
  inv_mem' := by
    rintro u ⟨hu, hur, hui⟩
    simp only [Set.mem_ofPred_eq, Pi.inv_apply, Circle.coe_inv_eq_conj, conj_re, conj_im]
    exact ⟨continuous_conj.comp hu, hur, neg_mem hui⟩

/-- Membership in `G_s`: continuity, and `Re u - 1`, `Im u ∈ H^s`. -/
@[simp]
theorem mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle} :
    u ∈ sobolevGaugeGroup s hs ↔ Continuous (fun z ↦ (u z : ℂ)) ∧
      (fun z ↦ (u z : ℂ).re - 1) ∈ sobolevFunctions s ∧
        (fun z ↦ (u z : ℂ).im) ∈ sobolevFunctions s := Iff.rfl

/-- The Sobolev gauge groups decrease as the order increases. -/
theorem sobolevGaugeGroup_mono {s s' : ℝ} {hs : 1 < s} {hs' : 1 < s'} (h : s' ≤ s) :
    sobolevGaugeGroup s hs ≤ sobolevGaugeGroup s' hs' :=
  fun _ hu ↦ ⟨hu.1, sobolevFunctions_mono h hu.2.1, sobolevFunctions_mono h hu.2.2⟩

/-- **Framing of Sobolev gauges.** Every element of `G_s` tends to one at infinity. -/
theorem tendsto_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s hs) : Tendsto u (cocompact ℂ) (𝓝 1) := by
  obtain ⟨hc, hr, hi⟩ := hu
  have hr0 := tendsto_cocompact_of_mem_sobolevFunctions hs hr (continuous_re.comp hc |>.sub
    continuous_const)
  have hi0 := tendsto_cocompact_of_mem_sobolevFunctions hs hi (continuous_im.comp hc)
  have h : Tendsto (fun z ↦ ((((u z : ℂ).re - 1 : ℝ) : ℂ) + 1) + (((u z : ℂ).im : ℝ) : ℂ) * I)
      (cocompact ℂ) (𝓝 ((((0 : ℝ) : ℂ) + 1) + ((0 : ℝ) : ℂ) * I)) :=
    (((continuous_ofReal.tendsto 0).comp hr0).add_const 1).add
      (((continuous_ofReal.tendsto 0).comp hi0).mul_const I)
  refine tendsto_subtype_rng.2 ?_
  simp only [ofReal_zero, zero_add, zero_mul, add_zero, ofReal_sub, ofReal_one, sub_add_cancel,
    re_add_im] at h
  simpa using h

/-- **Regularity of Sobolev gauges.** An element of `G_s` is `Cʲ` whenever `j + 2 ≤ s`. -/
theorem contDiff_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s hs) {j : ℕ} (hj : (j : ℝ) + 2 ≤ s) :
    ContDiff ℝ j (fun z ↦ (u z : ℂ)) := by
  obtain ⟨hc, hr, hi⟩ := hu
  have hr' := (contDiff_of_mem_sobolevFunctions hr ((continuous_re.comp hc).sub continuous_const)
    hj).add (contDiff_const (c := (1 : ℝ)))
  have hi' := contDiff_of_mem_sobolevFunctions hi (continuous_im.comp hc) hj
  have h := (ofRealCLM.contDiff.comp hr').add ((ofRealCLM.contDiff.comp hi').mul
    (contDiff_const (c := I)))
  convert h using 1
  ext1 z
  simp [re_add_im]

/-- An element of `G_s`, `s ≥ 3`, is differentiable. -/
theorem differentiable_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s hs) (h : 3 ≤ s) : Differentiable ℝ (fun z ↦ (u z : ℂ)) :=
  (contDiff_of_mem_sobolevGaugeGroup hu (j := 1) (by norm_num; linarith)).differentiable
    one_ne_zero

/-- A smooth element of `G_s` is a smooth framed gauge. -/
theorem mem_framedGaugeGroup_of_mem_sobolevGaugeGroup {s : ℝ} {hs : 1 < s} {u : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup s hs) (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ))) :
    u ∈ framedGaugeGroup :=
  (mem_framedGaugeGroup u).2 ⟨hsmooth, tendsto_of_mem_sobolevGaugeGroup hu⟩

/-- A smooth gauge equal to one outside a compact set lies in every Sobolev gauge group. -/
theorem mem_sobolevGaugeGroup_of_hasCompactSupport {u : ℂ → Circle}
    (hsmooth : ContDiff ℝ ∞ (fun z ↦ (u z : ℂ)))
    (hc : HasCompactSupport (fun z ↦ (u z : ℂ) - 1)) (s : ℝ) (hs : 1 < s) :
    u ∈ sobolevGaugeGroup s hs := by
  refine ⟨hsmooth.continuous, ?_, ?_⟩
  · have h := mem_sobolevFunctions_of_hasCompactSupport (reCLM.contDiff.comp
      (hsmooth.sub contDiff_const)) (hc.comp_left (g := re) zero_re) s
    simpa [Function.comp_def] using h
  · have h := mem_sobolevFunctions_of_hasCompactSupport (imCLM.contDiff.comp
      (hsmooth.sub contDiff_const)) (hc.comp_left (g := im) zero_im) s
    simpa [Function.comp_def] using h

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
private theorem referenceField_mul_mem_sobolevFunctions (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (L : ℂ →L[ℝ] ℝ) (k : ℕ) {g : ℂ → ℝ} (hg : g ∈ sobolevFunctions k) :
    (L ∘ referenceSection f m) * g ∈ sobolevFunctions k := by
  obtain ⟨M, hM, hbound⟩ := exists_bound_iteratedFDeriv_comp_referenceSection f m L k
  exact mul_mem_sobolevFunctions_natCast k (L.contDiff.comp (contDiff_referenceSection f m)) hM
    hbound hg

/-- **The logarithmic derivative of a Sobolev gauge.** For `k ≥ 2` and `u ∈ G_(k+1)`, every
coefficient `Im (u⁻¹ ∂ᵥu)` of the connection term of the gauge action lies in `H^k`. -/
theorem gaugeForm_apply_mem_sobolevFunctions {k : ℕ} (hk : 1 < k) {hs : 1 < (k : ℝ) + 1}
    {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup (k + 1) hs) (v : ℂ) :
    (fun z ↦ gaugeForm u z v) ∈ sobolevFunctions k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hC : ContDiff ℝ 1 (fun z ↦ (u z : ℂ)) :=
    contDiff_of_mem_sobolevGaugeGroup hu (j := 1) (by push_cast; linarith)
  obtain ⟨-, hA, hB⟩ := hu
  have hdA := fderiv_apply_mem_sobolevFunctions hA ((reCLM.contDiff.comp hC).sub contDiff_const) v
  have hdB := fderiv_apply_mem_sobolevFunctions hB (imCLM.contDiff.comp hC) v
  have hs' : (1 : ℝ) < k := by linarith
  -- `Im (conj u du) = ∂ Im u + (Re u - 1) ∂ Im u - Im u ∂ (Re u - 1)`
  have h : (fun z ↦ gaugeForm u z v) = (fun z ↦ fderiv ℝ (fun w ↦ (u w : ℂ).im) z v) +
      (fun z ↦ (u z : ℂ).re - 1) * (fun z ↦ fderiv ℝ (fun w ↦ (u w : ℂ).im) z v) -
        (fun z ↦ (u z : ℂ).im) * (fun z ↦ fderiv ℝ (fun w ↦ (u w : ℂ).re - 1) z v) := by
    ext z
    have hd := (hC.differentiable one_ne_zero z).hasFDerivAt
    have hre : HasFDerivAt (fun w ↦ (u w : ℂ).re - 1)
        (reCLM.comp (fderiv ℝ (fun w ↦ (u w : ℂ)) z)) z :=
      (reCLM.hasFDerivAt.comp z hd).sub_const 1
    have him : HasFDerivAt (fun w ↦ (u w : ℂ).im)
        (imCLM.comp (fderiv ℝ (fun w ↦ (u w : ℂ)) z)) z :=
      imCLM.hasFDerivAt.comp z hd
    simp only [gaugeForm_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, hre.fderiv, him.fderiv,
      ContinuousLinearMap.comp_apply, reCLM_apply, imCLM_apply, mul_im, conj_re, conj_im]
    ring
  rw [h]
  exact sub_mem (add_mem hdB (mul_mem_sobolevFunctions hs' (sobolevFunctions_mono (by linarith) hA)
    hdB)) (mul_mem_sobolevFunctions hs' (sobolevFunctions_mono (by linarith) hB) hdA)

/-- **The Sobolev gauge action preserves the affine field space.** For `k ≥ 2`, the charge-one
action of `u ∈ G_(k+1)` maps `A_m^k` into itself. -/
theorem gaugeTransform_mem_framedFieldSpace {k : ℕ} (hk : 1 < k) {hs : 1 < (k : ℝ) + 1}
    {u : ℂ → Circle} (hu : u ∈ sobolevGaugeGroup (k + 1) hs) {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k) :
    gaugeTransform u x ∈ framedFieldSpace f m k := by
  have hs' : (1 : ℝ) < k := by exact_mod_cast hk
  rw [mem_framedFieldSpace, mem_sobolevFields_iff] at hx ⊢
  have hA := sobolevFunctions_mono (by linarith) hu.2.1
  have hB := sobolevFunctions_mono (by linarith) hu.2.2
  have hσA := referenceField_mul_mem_sobolevFunctions f m ((1 / 2 : ℝ) • reCLM) k hA
  have hσB := referenceField_mul_mem_sobolevFunctions f m ((1 / 2 : ℝ) • reCLM) k hB
  have hτA := referenceField_mul_mem_sobolevFunctions f m ((1 / 2 : ℝ) • imCLM) k hA
  have hτB := referenceField_mul_mem_sobolevFunctions f m ((1 / 2 : ℝ) • imCLM) k hB
  intro i
  fin_cases i
  · convert sub_mem (hx 0) (gaugeForm_apply_mem_sobolevFunctions hk hu 1) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert sub_mem (hx 1) (gaugeForm_apply_mem_sobolevFunctions hk hu I) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert sub_mem (add_mem (add_mem hσA (hx 2)) (mul_mem_sobolevFunctions hs' hA (hx 2)))
      (add_mem hτB (mul_mem_sobolevFunctions hs' hB (hx 3))) using 1
    ext z
    simp [gaugeTransform_apply, referenceField_apply]
    ring
  · convert add_mem (add_mem (add_mem hσB (hx 3)) (mul_mem_sobolevFunctions hs' hB (hx 2)))
      (add_mem hτA (mul_mem_sobolevFunctions hs' hA (hx 3))) using 1
    ext z
    simp [gaugeTransform_apply, referenceField_apply]
    ring

/-- For `k ≥ 2`, the Sobolev gauge group `G_(k+1)` acts on the affine field space `A_m^k` by the
charge-one gauge action `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
noncomputable instance {k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1} {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} : MulAction (sobolevGaugeGroup (k + 1) hs) (framedFieldSpace f m k) where
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
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} (u : sobolevGaugeGroup (k + 1) hs)
    (x : framedFieldSpace f m k) :
    ((u • x : framedFieldSpace f m k) : ℂ → EuclideanSpace ℝ (Fin 4)) = gaugeTransform u x :=
  (rfl)

end TauCeti.Vortex
