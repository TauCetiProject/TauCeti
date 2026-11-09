/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FixingSubgroup
public import TauCeti.Topology.Compactification.OnePoint.MultipleTransitivity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Biholomorphisms of the Riemann sphere are Möbius transformations

Every biholomorphism `f` of the Riemann sphere `OnePoint ℂ` is a Möbius transformation
`x ↦ g • x` with `g ∈ GL(2, ℂ)` (`Diffeomorph.exists_coe_eq_smul`). Here a biholomorphism is a
`C^n` diffeomorphism over `ℂ` for some order `n ≠ 0`, so every such diffeomorphism is
holomorphic.

Consequently, on a manifold biholomorphic to the Riemann sphere, the biholomorphisms fixing three
distinct points form the trivial group (`Diffeomorph.fixingSubgroup_eq_bot_of_two_lt_encard`).
Together with `Diffeomorph.infinite_fixingSubgroup_of_encard_le_two`, the biholomorphisms fixing a
set `s` are finite exactly when `s` has at least three points
(`Diffeomorph.finite_fixingSubgroup_iff_two_lt_encard`). This is the stability criterion
`2 g - 2 + n > 0` for a component of genus zero of a marked nodal curve.

## Main results

* `Diffeomorph.exists_apply_coe_eq_mul_add`: a biholomorphism of the Riemann sphere fixing `∞` is
  `z ↦ a * z + b` on `ℂ`, with `a ≠ 0`.
* `Diffeomorph.eq_refl_of_apply_zero_one_infty_eq_self`: a biholomorphism of the Riemann sphere
  fixing `0`, `1` and `∞` is the identity.
* `Diffeomorph.exists_coe_eq_smul`: every biholomorphism of the Riemann sphere is a Möbius
  transformation.
* `Diffeomorph.fixingSubgroup_eq_bot_of_two_lt_encard` and
  `Diffeomorph.finite_fixingSubgroup_iff_two_lt_encard`: on a manifold biholomorphic to the
  Riemann sphere, the biholomorphisms fixing at least three points are trivial, and those fixing a
  set `s` are finite exactly when `s` has at least three points.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2, for the Möbius transformations of the Riemann sphere.
-/

public section

open Set Filter Topology OnePoint
open scoped Manifold

namespace Diffeomorph

variable {n : WithTop ℕ∞}

section Sphere

variable (f : OnePoint ℂ ≃ₘ^n⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ)

/-- Read in the inverted chart at `∞`, a biholomorphism of the Riemann sphere fixing `∞` is
differentiable at `0`. -/
private theorem differentiableAt_invChart_comp (hn : n ≠ 0) (hf : f ∞ = ∞) :
    DifferentiableAt ℂ (fun w : ℂ ↦ invChart (f (invChart.symm w))) 0 := by
  have h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun w : ℂ ↦ f (invChart.symm w)) 0 :=
    (f.contMDiff.mdifferentiable hn _).comp _
      (contMDiff_invChart_symm.mdifferentiable (by simp) _)
  exact mdifferentiableAt_iff_differentiableAt.mp
    ((mdifferentiableAt_iff_of_eq_infty (by simpa using hf)).mp h).2

/-- Read in the inverted chart at `∞`, a biholomorphism of the Riemann sphere fixing `∞` has a
nonzero derivative at `0`: the chart expression of its inverse is a local inverse. -/
private theorem exists_hasDerivAt_invChart_comp (hn : n ≠ 0) (hf : f ∞ = ∞) :
    ∃ a ≠ 0, HasDerivAt (fun w : ℂ ↦ invChart (f (invChart.symm w))) a 0 := by
  have hsymm : f.symm ∞ = ∞ :=
    congr(f.symm $hf).symm.trans (f.symm_apply_apply _)
  have h0 : invChart (f (invChart.symm 0)) = 0 := by simp [hf]
  -- Near `0`, the map avoids `0`, where the inverted chart is not defined.
  have hc : ContinuousAt (fun w : ℂ ↦ f (invChart.symm w)) 0 :=
    f.continuous.continuousAt.comp contMDiff_invChart_symm.continuous.continuousAt
  have hsrc : ∀ᶠ w in 𝓝 (0 : ℂ), f (invChart.symm w) ∈ invChart.source :=
    hc.preimage_mem_nhds (invChart.open_source.mem_nhds (by simp [hf]))
  have hleft : (fun w ↦ invChart (f.symm (invChart.symm (invChart (f (invChart.symm w)))))) =ᶠ[𝓝 0]
      id := by
    filter_upwards [hsrc] with w hw
    rw [invChart.left_inv hw, symm_apply_apply, invChart.right_inv (by simp), id]
  have hcomp := (h0 ▸ (differentiableAt_invChart_comp f.symm hn hsymm).hasDerivAt).comp 0
    (differentiableAt_invChart_comp f hn hf).hasDerivAt
  exact ⟨_, right_ne_zero_of_mul_eq_one
    (hcomp.unique ((hasDerivAt_id 0).congr_of_eventuallyEq hleft)), hasDerivAt_deriv_iff.mpr
      (differentiableAt_invChart_comp f hn hf)⟩

/- Proof sketch for the affine classification. The finite part `g` of `f` is an injective entire
function. Read in the inverted chart at `∞`, the map `f` becomes a holomorphic function `h` with
`h 0 = 0`, and `h' 0 ≠ 0` because the chart expression of `f.symm` is a local inverse of `h`.
Since `h w = (g w⁻¹)⁻¹`, the difference quotient `(g z - g 0) / z` tends to `(h' 0)⁻¹` as `z`
tends to infinity. It is entire by the removable singularity theorem, so it is constant by
Liouville's theorem, and `g` is affine. -/

/-- **A biholomorphism of the Riemann sphere fixing `∞` is affine.** It is `z ↦ a * z + b` on `ℂ`,
for some `a ≠ 0` and `b`. -/
theorem exists_apply_coe_eq_mul_add (hn : n ≠ 0) (hf : f ∞ = ∞) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, f z = ((a * z + b : ℂ) : OnePoint ℂ) := by
  -- The finite part `g` of `f` is entire.
  have hfin (z : ℂ) : f z ≠ ∞ := fun h ↦ coe_ne_infty z (f.injective (h.trans hf.symm))
  set g : ℂ → ℂ := fun z ↦ affineChart (f z)
  have hg (z : ℂ) : f z = (g z : OnePoint ℂ) := by
    obtain ⟨w, hw⟩ := ne_infty_iff_exists.mp (hfin z)
    simp [g, ← hw]
  have hgd : Differentiable ℂ g := fun z ↦ by
    have : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : ℂ ↦ (g z : OnePoint ℂ)) z := by
      simpa only [Function.comp_def, ← hg] using
        (f.contMDiff.mdifferentiable hn _).comp z (contMDiff_coe.mdifferentiable (by simp) z)
    exact mdifferentiableAt_iff_differentiableAt.mp (mdifferentiableAt_coe_comp_iff.mp this)
  -- At `∞`, `f` reads `w ↦ (g w⁻¹)⁻¹`, whose derivative `a` at `0` is nonzero.
  obtain ⟨a, ha, hda⟩ := exists_hasDerivAt_invChart_comp f hn hf
  have hinv {z : ℂ} (hz : z ≠ 0) : invChart (f (invChart.symm z⁻¹)) = (g z)⁻¹ := by
    rw [invChart_symm_of_ne_zero (inv_ne_zero hz), inv_inv, hg, invChart_coe]
  have hslope : Tendsto (fun w : ℂ ↦ w⁻¹ * invChart (f (invChart.symm w))) (𝓝[≠] 0) (𝓝 a) := by
    simpa [hf] using hda.tendsto_slope_zero
  -- Hence the difference quotient of `g` at `0` tends to `a⁻¹` at infinity.
  have hlim : Tendsto (dslope g 0) (cocompact ℂ) (𝓝 a⁻¹) := by
    rw [← Metric.cobounded_eq_cocompact]
    have h1 : Tendsto (fun z : ℂ ↦ (z * (g z)⁻¹)⁻¹) (Bornology.cobounded ℂ) (𝓝 a⁻¹) := by
      refine ((hslope.comp tendsto_inv₀_cobounded').congr' ?_).inv₀ ha
      filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz
      simp [hinv (norm_pos_iff.mp hz)]
    have h2 : Tendsto (fun z : ℂ ↦ z⁻¹ * g 0) (Bornology.cobounded ℂ) (𝓝 0) := by
      simpa using tendsto_inv₀_cobounded.mul_const (g 0)
    refine ((h1.sub h2).congr' ?_).trans (by simp)
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz
    rw [dslope_of_ne _ (norm_pos_iff.mp hz), slope_def_field, mul_inv, inv_inv]
    ring
  -- By Liouville's theorem the difference quotient is constant, so `g` is affine.
  have hconst (z : ℂ) : dslope g 0 z = a⁻¹ :=
    (differentiableOn_univ.mp ((Complex.differentiableOn_dslope univ_mem).mpr
      hgd.differentiableOn)).apply_eq_of_tendsto_cocompact z hlim
  refine ⟨a⁻¹, g 0, inv_ne_zero ha, fun z ↦ ?_⟩
  rw [hg, ← sub_add_cancel (g z) (g 0), ← sub_smul_dslope, hconst, sub_zero, smul_eq_mul,
    mul_comm]

/-- **A biholomorphism of the Riemann sphere fixing `0`, `1` and `∞` is the identity.** -/
theorem eq_refl_of_apply_zero_one_infty_eq_self (hn : n ≠ 0) (h0 : f (0 : ℂ) = (0 : ℂ))
    (h1 : f (1 : ℂ) = (1 : ℂ)) (hinf : f ∞ = ∞) : f = Diffeomorph.refl 𝓘(ℂ) (OnePoint ℂ) n := by
  obtain ⟨a, b, -, hab⟩ := f.exists_apply_coe_eq_mul_add hn hinf
  have hb : b = 0 := by simpa using (hab 0).symm.trans h0
  have ha : a = 1 := by simpa [hb] using (hab 1).symm.trans h1
  ext x
  induction x using OnePoint.rec with
  | infty => simpa using hinf
  | coe z => simp [hab, ha, hb]

/-- **Every biholomorphism of the Riemann sphere is a Möbius transformation**: it is
`x ↦ g • x` for some `g ∈ GL(2, ℂ)`. -/
theorem exists_coe_eq_smul (hn : n ≠ 0) :
    ∃ g : GL (Fin 2) ℂ, ⇑f = fun x ↦ g • x := by
  -- Move `0`, `1`, `∞` to `f 0`, `f 1`, `f ∞`; the composite `g⁻¹ • f` fixes `0`, `1`, `∞`.
  obtain ⟨g, h0, h1, hinf⟩ := exists_smul_zero_one_infty_eq
    (f.injective.ne (by simp : ((0 : ℂ) : OnePoint ℂ) ≠ (1 : ℂ)))
    (f.injective.ne (coe_ne_infty 0)) (f.injective.ne (coe_ne_infty 1))
  simp only [coe_toEquiv] at h0 h1 hinf
  have hid := (f.trans (constSmul 𝓘(ℂ) n g⁻¹)).eq_refl_of_apply_zero_one_infty_eq_self hn
    (by simp [inv_smul_eq_iff, h0]) (by simp [inv_smul_eq_iff, h1])
    (by simp [inv_smul_eq_iff, hinf])
  refine ⟨g, funext fun x ↦ ?_⟩
  have hx := congr($hid x)
  simp only [coe_trans, Function.comp_apply, constSmul_apply, coe_refl, id] at hx
  exact inv_smul_eq_iff.mp hx

end Sphere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Biholomorphisms fixing three points of the Riemann sphere are trivial.** If `M` is
biholomorphic to the Riemann sphere, the only biholomorphism of `M` fixing every point of a set
with at least three points is the identity. -/
theorem fixingSubgroup_eq_bot_of_two_lt_encard (e : M ≃ₘ^n⟮I, 𝓘(ℂ)⟯ OnePoint ℂ) (hn : n ≠ 0)
    {s : Set M} (hs : 2 < s.encard) : fixingSubgroup (I := I) (n := n) s = ⊥ := by
  -- Choose three distinct points `p`, `q`, `r` of `e '' s`.
  have himage : (e '' s).encard = s.encard := e.injective.encard_image s
  obtain ⟨t, hts, ht⟩ := exists_subset_encard_eq (s := e '' s) (k := 3)
    (himage ▸ Order.add_one_le_of_lt hs)
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := encard_eq_three.mp ht
  obtain ⟨g, h0, h1, hinf⟩ := exists_smul_zero_one_infty_eq hpq hpr hqr
  refine (Subgroup.eq_bot_iff_forall _).mpr fun φ hφ ↦ ?_
  have hfix {y : OnePoint ℂ} (hy : y ∈ e '' s) : e (φ (e.symm y)) = y := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [symm_apply_apply, apply_eq_of_mem_fixingSubgroup hφ hx]
  -- Conjugated by `e` and by `g`, the diffeomorphism `φ` fixes `0`, `1` and `∞`.
  have hid := ((constSmul 𝓘(ℂ) n g).trans ((e.symm.trans (φ.trans e)).trans
    (constSmul 𝓘(ℂ) n g⁻¹))).eq_refl_of_apply_zero_one_infty_eq_self hn
      (by simp [inv_smul_eq_iff, h0, hfix (hts (by simp : p ∈ {p, q, r}))])
      (by simp [inv_smul_eq_iff, h1, hfix (hts (by simp : q ∈ {p, q, r}))])
      (by simp [inv_smul_eq_iff, hinf, hfix (hts (by simp : r ∈ {p, q, r}))])
  ext x
  have hx := congr($hid (g⁻¹ • e x))
  simpa using hx

/-- **Stability of a rational component.** If `M` is biholomorphic to the Riemann sphere, the
biholomorphisms of `M` fixing every point of `s` form a finite group exactly when `s` has at least
three points. -/
theorem finite_fixingSubgroup_iff_two_lt_encard (e : M ≃ₘ^n⟮I, 𝓘(ℂ)⟯ OnePoint ℂ) (hn : n ≠ 0)
    {s : Set M} : Finite (fixingSubgroup (I := I) (n := n) s) ↔ 2 < s.encard := by
  refine ⟨fun h ↦ lt_of_not_ge fun hle ↦ ?_, fun hs ↦ ?_⟩
  · exact not_finite_iff_infinite.mpr (e.infinite_fixingSubgroup_of_encard_le_two hle) h
  · rw [fixingSubgroup_eq_bot_of_two_lt_encard e hn hs]
    infer_instance

end Diffeomorph
