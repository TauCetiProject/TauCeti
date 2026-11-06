/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import TauCeti.Analysis.PDE.Vortex.Reference
public import TauCeti.Analysis.PDE.Vortex.ScalarEquation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.Wkp.ContDiffRepresentative
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# The affine Sobolev space of framed plane vortex fields

Framed degree-`m` plane vortex fields form the affine space

  `A_m^s = (a_m, α_m) + (L² ∩ H^s)(ℂ; iT*ℂ ⊕ ℂ)`,

centered at a smooth reference pair equal to `(-i m dθ, exp (i m θ))` outside a disc. Every
coordinate of a field in the direction is an `L²` function, so for `s ≥ 0` the direction is the
full Sobolev space `H^s`, while for `s < 0` it is only the subspace `L² ∩ H^s`. This file builds
the space in the real coordinates `x = (b₁, b₂, p, q)` of `TauCeti.Vortex.equation`, which
represent `a = i (b₁ ds + b₂ dt)` and `α = 2 (p + i q)`.

* `referenceField f m` is the reference pair `(referenceConnection f m, referenceSection f m)` in
  these coordinates.
* `sobolevFunctions s` is the real space of pointwise representatives of real `L² ∩ H^s`
  functions on the plane: real `L²` functions whose complexified tempered distribution lies in
  Mathlib's Bessel-potential space `H^s`.
* `sobolevFields s` is the real space of pointwise representatives of `L² ∩ H^s` fields (all of
  `H^s` when `s ≥ 0`): each coordinate is a real `L²` function whose complexified tempered
  distribution lies in Mathlib's Bessel-potential space `H^s`
  (`TemperedDistribution.realSobolevSubmodule`). This is the componentwise complexification on
  which the tempered vacuum operator `TauCeti.Vortex.temperedVacuumOperator` acts.
* `framedFieldSpace f m s` is `A_m^s`, the affine subspace through `referenceField f m` with
  direction `sobolevFields s`.

Changing the radial cutoff changes the reference by a smooth compactly supported field, so the
affine space does not depend on the cutoff (`framedFieldSpace_eq`). The vacuum lies in `A_0^s`.
For `s > 1`, a continuous field in `A_m^s` tends to the reference field at infinity, by Sobolev
embedding into `C₀`. In particular its section satisfies the end framing
`α(z) (z / |z|)^(-m) → 1`, and its modulus tends to one; with the maximum principle this gives
`|α| ≤ 1` for every `C²` vortex in `A_m^s`. No equation map, gauge group, Fredholm property or
smooth structure on the quotient is constructed here.

A field lies in `sobolevFields s` exactly when each of its coordinates lies in
`sobolevFunctions s` (`mem_sobolevFields_iff`). The scalar space carries the operations of the
nonlinear theory:

* for `s > 1` it is closed under pointwise products (`mul_mem_sobolevFunctions`), since `H^s` is
  an algebra in dimension two;
* the classical directional derivatives of a `C¹` function in `sobolevFunctions (k + 1)` lie in
  `sobolevFunctions k` (`fderiv_apply_mem_sobolevFunctions`);
* a continuous function in `sobolevFunctions s` is `Cʲ` whenever `j + 2 ≤ s`
  (`contDiff_of_mem_sobolevFunctions`), and for `s > 1` it tends to zero at infinity
  (`tendsto_cocompact_of_mem_sobolevFunctions`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution
open scoped ContDiff Topology SchwartzMap

/-! ### The reference field -/

/-- The reference pair `(referenceConnection f m, referenceSection f m)` in the real field
coordinates of `Vortex.equation`, where `a = i (b₁ ds + b₂ dt)` and `α = 2 (p + i q)`. -/
def referenceField (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[(referenceConnection f m z 1).im, (referenceConnection f m z I).im,
    (referenceSection f m z).re / 2, (referenceSection f m z).im / 2]

/-- The coordinates of the reference field. -/
theorem referenceField_apply (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) :
    referenceField f m z =
      !₂[(referenceConnection f m z 1).im, (referenceConnection f m z I).im,
        (referenceSection f m z).re / 2, (referenceSection f m z).im / 2] := (rfl)

/-- The section of the reference field is the reference section. -/
@[simp]
theorem sectionValue_referenceField (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z : ℂ) :
    sectionValue (referenceField f m) z = referenceSection f m z := by
  conv_rhs => rw [← re_add_im (referenceSection f m z)]
  rw [sectionValue_apply, referenceField_apply]
  simp only [Fin.isValue, Matrix.cons_val, ofReal_div, ofReal_ofNat]
  ring

/-- The connection coordinates of the reference field represent the reference one-form:
`referenceConnection f m z = i (b₁ ds + b₂ dt)`. -/
theorem referenceConnection_apply_eq_I_mul (f : ContDiffBump (0 : ℝ)) (m : ℕ) (z v : ℂ) :
    referenceConnection f m z v =
      I * ((referenceField f m z 0 * v.re + referenceField f m z 1 * v.im : ℝ) : ℂ) := by
  have hv : (v / z).im = v.re * (1 / z).im + v.im * (I / z).im := by
    simp only [div_im, one_re, one_im, I_re, I_im]
    ring
  simp only [referenceField_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    referenceConnection_apply, hv, mul_re, mul_im, neg_re, neg_im, natCast_re, natCast_im, I_re,
    I_im, ofReal_re, ofReal_im, ofReal_add, ofReal_mul, ofReal_neg, ofReal_natCast, ofReal_zero,
    ofReal_one]
  ring

/-- The reference field is smooth. -/
theorem contDiff_referenceField (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    ContDiff ℝ ∞ (referenceField f m) := by
  have hc (v : ℂ) : ContDiff ℝ ∞ (fun z ↦ referenceConnection f m z v) :=
    (contDiff_referenceConnection f m).clm_apply contDiff_const
  have hs := contDiff_referenceSection f m
  refine contDiff_euclidean.2 fun i ↦ ?_
  fin_cases i
  · exact imCLM.contDiff.comp (hc 1)
  · exact imCLM.contDiff.comp (hc I)
  · exact (reCLM.contDiff.comp hs).div_const 2
  · exact (imCLM.contDiff.comp hs).div_const 2

/-- Changing the radial cutoff changes the reference field by a compactly supported field. -/
theorem hasCompactSupport_referenceField_sub (f g : ContDiffBump (0 : ℝ)) (m : ℕ) :
    HasCompactSupport (referenceField f m - referenceField g m) := by
  have hc := hasCompactSupport_referenceConnection_sub f g m
  have hs := hasCompactSupport_referenceSection_sub f g m
  refine HasCompactSupport.intro' (hc.isCompact.union hs.isCompact)
    ((isClosed_tsupport _).union (isClosed_tsupport _)) fun z hz ↦ ?_
  simp only [Set.mem_union, not_or] at hz
  have hcz := sub_eq_zero.1
    (image_eq_zero_of_notMem_tsupport (f := referenceConnection f m - referenceConnection g m) hz.1)
  have hsz := sub_eq_zero.1
    (image_eq_zero_of_notMem_tsupport (f := referenceSection f m - referenceSection g m) hz.2)
  simp only [Pi.sub_apply, referenceField_apply, hcz, hsz, sub_self]

/-- Off a large disc, points are nonzero and lie where the cutoff of the reference pair is
inactive. -/
private theorem eventually_ne_zero_and_rOut_le (f : ContDiffBump (0 : ℝ)) :
    ∀ᶠ z in cocompact ℂ, z ≠ 0 ∧ f.rOut ≤ ‖z‖ ^ 2 := by
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (f.rOut + 1)] with z hz
  have hr := f.rOut_pos
  exact ⟨norm_pos_iff.1 (by linarith), by nlinarith⟩

/-- The degree-zero reference field differs from the vacuum by a compactly supported field. -/
theorem hasCompactSupport_referenceField_zero_sub_vacuumField (f : ContDiffBump (0 : ℝ)) :
    HasCompactSupport (referenceField f 0 - vacuumField) := by
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact]
  filter_upwards [eventually_ne_zero_and_rOut_le f] with z hz
  have hf0 : f (‖z‖ ^ 2) = 0 :=
    f.zero_of_le_dist (by simpa [Real.dist_eq, abs_of_nonneg] using hz.2)
  ext i
  fin_cases i <;> simp [referenceField_apply, vacuumField_apply, hf0]

/-! ### Sobolev functions -/

/-- The real space of pointwise representatives of real `(L² ∩ H^s)(ℂ)` functions, which is the
Sobolev space `H^s(ℂ; ℝ)` when `s ≥ 0`: the values of real `L²` functions whose complexified
tempered distribution lies in the Bessel-potential space `H^s`. -/
def sobolevFunctions (s : ℝ) : Submodule ℝ (ℂ → ℝ) where
  carrier := {g | ∃ u : Lp ℝ 2 (volume : Measure ℂ), u =ᵐ[volume] g ∧
    u ∈ realSobolevSubmodule ℂ s 2}
  add_mem' := by
    rintro g₁ g₂ ⟨u₁, hu₁, hs₁⟩ ⟨u₂, hu₂, hs₂⟩
    refine ⟨u₁ + u₂, ?_, add_mem hs₁ hs₂⟩
    filter_upwards [Lp.coeFn_add u₁ u₂, hu₁, hu₂] with z h h₁ h₂
    rw [h, Pi.add_apply, h₁, h₂, Pi.add_apply]
  zero_mem' := ⟨0, Lp.coeFn_zero ℝ 2 (volume : Measure ℂ), zero_mem _⟩
  smul_mem' := by
    rintro c g ⟨u, hu, hs⟩
    refine ⟨c • u, ?_, Submodule.smul_mem _ c hs⟩
    filter_upwards [Lp.coeFn_smul c u, hu] with z h h'
    rw [h, Pi.smul_apply, h', Pi.smul_apply]

/-- Membership in `sobolevFunctions s` (`L² ∩ H^s`). -/
theorem mem_sobolevFunctions {s : ℝ} {g : ℂ → ℝ} :
    g ∈ sobolevFunctions s ↔ ∃ u : Lp ℝ 2 (volume : Measure ℂ), u =ᵐ[volume] g ∧
      MemSobolev s 2 (Lp.toTemperedDistribution (ofRealCLM.compLp u)) :=
  exists_congr fun _ ↦ and_congr_right' mem_realSobolevSubmodule

/-- The Sobolev function spaces decrease as the order increases. -/
theorem sobolevFunctions_mono {s s' : ℝ} (h : s' ≤ s) :
    sobolevFunctions s ≤ sobolevFunctions s' :=
  fun _ hg ↦ mem_sobolevFunctions.2 <| (mem_sobolevFunctions.1 hg).imp fun _ hu ↦
    ⟨hu.1, hu.2.mono h⟩

/-- A smooth compactly supported function lies in every Sobolev space. -/
theorem mem_sobolevFunctions_of_hasCompactSupport {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (s : ℝ) : g ∈ sobolevFunctions s := by
  have hm : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hc
  refine mem_sobolevFunctions.2 ⟨hm.toLp _, hm.coeFn_toLp, ?_⟩
  refine memSobolev_of_ae_eq_of_hasCompactSupport (u := fun z ↦ (g z : ℂ))
    (ofRealCLM.contDiff.comp hg) (hc.comp_left ofReal_zero) ?_
  filter_upwards [ofRealCLM.coeFn_compLp (hm.toLp _), hm.coeFn_toLp] with z h₁ h₂
  simp [h₁, h₂]

/-- The Sobolev-embedding threshold `dim ℂ < 2 s` of the plane. -/
private theorem finrank_lt_two_mul {s : ℝ} (hs : 1 < s) : (finrank ℝ ℂ : ℝ) < 2 * s := by
  rw [Complex.finrank_real_complex]
  push_cast
  linarith

/-- **Decay of continuous Sobolev functions.** For `s > 1`, a continuous function in
`sobolevFunctions s` tends to zero at infinity: by Sobolev embedding it agrees almost everywhere
with a continuous function vanishing at infinity, hence everywhere. -/
theorem tendsto_cocompact_of_mem_sobolevFunctions {s : ℝ} (hs : 1 < s) {g : ℂ → ℝ}
    (hg : g ∈ sobolevFunctions s) (hcont : Continuous g) :
    Tendsto g (cocompact ℂ) (𝓝 0) := by
  obtain ⟨u, hu, hS⟩ := mem_sobolevFunctions.1 hg
  obtain ⟨φ, hφ⟩ := MemSobolev.exists_zeroAtInftyContinuousMap_ae_eq (finrank_lt_two_mul hs) hS
  have hae : (fun z ↦ (g z : ℂ)) =ᵐ[volume] φ := by
    filter_upwards [ofRealCLM.coeFn_compLp u, hu, hφ] with z h₁ h₂ h₃
    rw [← h₃, h₁, h₂, ofRealCLM_apply]
  have heq := ((continuous_ofReal.comp hcont).ae_eq_iff_eq volume φ.continuous).1 hae
  have hφ0 : Tendsto (ofReal ∘ g) (cocompact ℂ) (𝓝 0) := heq ▸ φ.zero_at_infty'
  simpa [Function.comp_def] using (continuous_re.tendsto 0).comp hφ0

/-- **The Sobolev function spaces of order `s > 1` are algebras.** The pointwise product of two
functions in `sobolevFunctions s`, `s > 1`, lies in `sobolevFunctions s`. -/
theorem mul_mem_sobolevFunctions {s : ℝ} (hs : 1 < s) {g h : ℂ → ℝ}
    (hg : g ∈ sobolevFunctions s) (hh : h ∈ sobolevFunctions s) :
    g * h ∈ sobolevFunctions s := by
  obtain ⟨u, hu, huS⟩ := hg
  obtain ⟨v, hv, hvS⟩ := hh
  obtain ⟨w, hwS, hw⟩ := exists_mem_realSobolevSubmodule_ae_eq_mul (finrank_lt_two_mul hs) huS hvS
  refine ⟨w, ?_, hwS⟩
  filter_upwards [hw, hu, hv] with z hz hz₁ hz₂
  rw [hz, hz₁, hz₂, Pi.mul_apply]

/-- **Classical derivatives of Sobolev functions.** If a `C¹` function lies in
`sobolevFunctions (k + 1)`, then each of its classical directional derivatives lies in
`sobolevFunctions k`. -/
theorem fderiv_apply_mem_sobolevFunctions {k : ℕ} {g : ℂ → ℝ}
    (hg : g ∈ sobolevFunctions (k + 1)) (hC : ContDiff ℝ 1 g) (v : ℂ) :
    (fun z ↦ fderiv ℝ g z v) ∈ sobolevFunctions k := by
  obtain ⟨u, hu, huS⟩ := mem_sobolevFunctions.1 hg
  -- The distributional derivative `∂ᵥ u` lies in `H^k` and is represented by an `L²` function.
  have hd := ((memSobolev_natCast_add_one_iff (by norm_num) (by norm_num)).1 huS).2 v
  obtain ⟨u', hu'⟩ := Lp.exists_real_lp_lineDeriv_of_memSobolev_zero u v
    (hd.mono (Nat.cast_nonneg k))
  have hw : HasWeakLineDerivOn volume ⊤ g u' v :=
    ((hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq u u' v).2 hu').congr_ae
      (by rwa [TopologicalSpace.Opens.coe_top, Measure.restrict_univ])
  -- That weak derivative is the classical derivative.
  have hdiff : Differentiable ℝ g := hC.differentiable one_ne_zero
  have hcont : Continuous fun z ↦ lineDeriv ℝ g z v := by
    rw [funext fun z ↦ (hdiff z).lineDeriv_eq_fderiv]
    exact (hC.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hae := hw.ae_eq_lineDeriv (hcont.locallyIntegrable.locallyIntegrableOn _)
    fun z _ ↦ (hdiff z).lineDifferentiableAt
  refine mem_sobolevFunctions.2 ⟨u', ?_, hu' ▸ hd⟩
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hae
  filter_upwards [hae] with z hz
  rw [hz, (hdiff z).lineDeriv_eq_fderiv]

/-- **Sobolev embedding into `Cʲ`.** A continuous function in `sobolevFunctions s` is `Cʲ`
whenever `j + 2 ≤ s`. -/
theorem contDiff_of_mem_sobolevFunctions {s : ℝ} {g : ℂ → ℝ} (hg : g ∈ sobolevFunctions s)
    (hcont : Continuous g) {j : ℕ} (hj : (j : ℝ) + 2 ≤ s) : ContDiff ℝ j g := by
  obtain ⟨u, hu, huS⟩ := mem_sobolevFunctions.1 hg
  have huS' : MemSobolev ((2 + j : ℕ) : ℝ) 2
      (Lp.toTemperedDistribution (ofRealCLM.compLp u)) := huS.mono (by push_cast; linarith)
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq (by norm_num) (by norm_num)
    (2 + j) u).1 huS'
  obtain ⟨g', hg', hwg'⟩ := Wkp.exists_contDiffOn_ae_eq
    (Omega := ⊤) (by rw [Complex.finrank_real_complex]; norm_num) j w
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ, contDiffOn_univ] at hg' hwg'
  have heq : g = g' :=
    (hcont.ae_eq_iff_eq volume hg'.continuous).1 ((hu.symm.trans hw.symm).trans hwg')
  exact heq ▸ hg'

/-! ### Sobolev fields -/

/-- The real space of pointwise representatives of `(L² ∩ H^s)(ℂ; ℝ⁴)` fields, which is the
Sobolev space `H^s(ℂ; ℝ⁴)` when `s ≥ 0`: each coordinate is the value of a real `L²` function
whose complexified tempered distribution lies in the Bessel-potential space `H^s`. -/
def sobolevFields (s : ℝ) : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  carrier := {y | ∀ i, ∃ u : Lp ℝ 2 (volume : Measure ℂ), u =ᵐ[volume] (fun z ↦ y z i) ∧
    u ∈ realSobolevSubmodule ℂ s 2}
  add_mem' := by
    rintro y₁ y₂ h₁ h₂ i
    obtain ⟨u₁, hu₁, hs₁⟩ := h₁ i
    obtain ⟨u₂, hu₂, hs₂⟩ := h₂ i
    refine ⟨u₁ + u₂, ?_, add_mem hs₁ hs₂⟩
    filter_upwards [Lp.coeFn_add u₁ u₂, hu₁, hu₂] with z h h₁ h₂
    rw [h, Pi.add_apply, h₁, h₂, Pi.add_apply, PiLp.add_apply]
  zero_mem' := by
    intro i
    refine ⟨0, ?_, zero_mem _⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℂ)] with z h
    rw [h, Pi.zero_apply, Pi.zero_apply, PiLp.zero_apply]
  smul_mem' := by
    rintro c y h i
    obtain ⟨u, hu, hs⟩ := h i
    refine ⟨c • u, ?_, Submodule.smul_mem _ c hs⟩
    filter_upwards [Lp.coeFn_smul c u, hu] with z h h'
    rw [h, Pi.smul_apply, h', Pi.smul_apply, PiLp.smul_apply]

/-- Membership in `sobolevFields s` (`L² ∩ H^s`), coordinate by coordinate. -/
theorem mem_sobolevFields {s : ℝ} {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ sobolevFields s ↔ ∀ i, ∃ u : Lp ℝ 2 (volume : Measure ℂ),
      u =ᵐ[volume] (fun z ↦ y z i) ∧
        MemSobolev s 2 (Lp.toTemperedDistribution (ofRealCLM.compLp u)) :=
  forall_congr' fun _ ↦ exists_congr fun _ ↦ and_congr_right' mem_realSobolevSubmodule

/-- A field lies in `sobolevFields s` exactly when each of its coordinates lies in
`sobolevFunctions s`. -/
theorem mem_sobolevFields_iff {s : ℝ} {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ sobolevFields s ↔ ∀ i, (fun z ↦ y z i) ∈ sobolevFunctions s := Iff.rfl

/-- The Sobolev field spaces decrease as the order increases. -/
theorem sobolevFields_mono {s s' : ℝ} (h : s' ≤ s) : sobolevFields s ≤ sobolevFields s' :=
  fun _ hy ↦ mem_sobolevFields.2 fun i ↦
    (mem_sobolevFields.1 hy i).imp fun _ hu ↦ ⟨hu.1, hu.2.mono h⟩

/-- A smooth compactly supported field lies in every Sobolev space. -/
theorem mem_sobolevFields_of_hasCompactSupport {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ ∞ y) (hc : HasCompactSupport y) (s : ℝ) : y ∈ sobolevFields s :=
  mem_sobolevFields_iff.2 fun i ↦ mem_sobolevFunctions_of_hasCompactSupport
    (contDiff_euclidean.1 hy i)
    (hc.comp_left (g := fun v : EuclideanSpace ℝ (Fin 4) ↦ v i) rfl) s

/-- **Decay of continuous Sobolev fields.** For `s > 1`, a continuous field in `sobolevFields s`
tends to zero at infinity. -/
theorem tendsto_cocompact_of_mem_sobolevFields {s : ℝ} (hs : 1 < s)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields s) (hcont : Continuous y) :
    Tendsto y (cocompact ℂ) (𝓝 0) := by
  have h : Tendsto (fun z ↦ WithLp.ofLp (y z)) (cocompact ℂ) (𝓝 0) :=
    tendsto_pi_nhds.2 fun i ↦ tendsto_cocompact_of_mem_sobolevFunctions hs
      (mem_sobolevFields_iff.1 hy i) ((PiLp.continuous_apply 2 _ i).comp hcont)
  simpa [Function.comp_def] using ((PiLp.continuous_toLp 2 _).tendsto 0).comp h

/-! ### The affine field space -/

/-- The affine space `A_m^s = referenceField f m + sobolevFields s` of framed degree-`m` plane
vortex fields, whose direction is `L² ∩ H^s` (all of `H^s` when `s ≥ 0`). It does not depend on
the cutoff `f` (`framedFieldSpace_eq`). -/
def framedFieldSpace (f : ContDiffBump (0 : ℝ)) (m : ℕ) (s : ℝ) :
    AffineSubspace ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) :=
  AffineSubspace.mk' (referenceField f m) (sobolevFields s)

/-- A field lies in `A_m^s` exactly when its difference from the reference field lies in
`sobolevFields s`. -/
theorem mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} :
    x ∈ framedFieldSpace f m s ↔ x - referenceField f m ∈ sobolevFields s :=
  AffineSubspace.mem_mk'

/-- The space `A_m^s` is modeled on `sobolevFields s`. -/
@[simp]
theorem direction_framedFieldSpace (f : ContDiffBump (0 : ℝ)) (m : ℕ) (s : ℝ) :
    (framedFieldSpace f m s).direction = sobolevFields s :=
  AffineSubspace.direction_mk' _ _

/-- The reference field is a framed field of degree `m`. -/
theorem referenceField_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ)) (m : ℕ) (s : ℝ) :
    referenceField f m ∈ framedFieldSpace f m s :=
  AffineSubspace.self_mem_mk' _ _

/-- The affine field space does not depend on the radial cutoff of the reference field. -/
theorem framedFieldSpace_eq (f g : ContDiffBump (0 : ℝ)) (m : ℕ) (s : ℝ) :
    framedFieldSpace f m s = framedFieldSpace g m s :=
  AffineSubspace.mk'_eq_mk'_iff.2 <| mem_sobolevFields_of_hasCompactSupport
    ((contDiff_referenceField f m).sub (contDiff_referenceField g m))
    (hasCompactSupport_referenceField_sub f g m) s

/-- The affine field spaces decrease as the Sobolev order increases. -/
theorem framedFieldSpace_mono (f : ContDiffBump (0 : ℝ)) (m : ℕ) {s s' : ℝ} (h : s' ≤ s) :
    framedFieldSpace f m s ≤ framedFieldSpace f m s' :=
  (AffineSubspace.mk'_le_mk'_iff _).2 (sobolevFields_mono h)

/-- The vacuum is a framed field of degree zero. -/
theorem vacuumField_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ)) (s : ℝ) :
    vacuumField ∈ framedFieldSpace f 0 s := by
  rw [mem_framedFieldSpace, ← neg_sub]
  refine Submodule.neg_mem _ (mem_sobolevFields_of_hasCompactSupport ?_
    (hasCompactSupport_referenceField_zero_sub_vacuumField f) s)
  rw [funext vacuumField_apply]
  exact (contDiff_referenceField f 0).sub contDiff_const

/-! ### Behaviour at infinity -/

/-- For `s > 1`, a continuous field in `A_m^s` tends to the reference field at infinity. -/
theorem tendsto_sub_referenceField {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} (hs : 1 < s)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s)
    (hcont : Continuous x) :
    Tendsto (x - referenceField f m) (cocompact ℂ) (𝓝 0) :=
  tendsto_cocompact_of_mem_sobolevFields hs (mem_framedFieldSpace.1 hx)
    (hcont.sub (contDiff_referenceField f m).continuous)

/-- **End framing.** For `s > 1`, the section of a continuous field in `A_m^s` times the inverse
winding phase `(z / |z|)^(-m)` tends to one at infinity. -/
theorem tendsto_sectionValue_mul_inv_pow {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s)
    (hcont : Continuous x) :
    Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) := by
  -- The section defect `α - α_m` is the section of the field defect `x - x_m`.
  have hd : Tendsto (fun z ↦ sectionValue x z - referenceSection f m z) (cocompact ℂ) (𝓝 0) :=
    (tendsto_sectionValue_zero (tendsto_sub_referenceField hs hx hcont)).congr fun z ↦ by
      rw [sectionValue_sub, sectionValue_referenceField]
  -- Off a large disc the reference section is the unit winding phase.
  have hsmall : Tendsto (fun z ↦ (sectionValue x z - referenceSection f m z) *
      ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_norm_zero.comp hd)
    filter_upwards [eventually_ne_zero_and_rOut_le f] with z hz
    simp [norm_ne_zero_iff.2 hz.1]
  have := (tendsto_const_nhds (x := (1 : ℂ))).add hsmall
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ne_zero_and_rOut_le f] with z hz
  obtain ⟨hz0, hz2⟩ := hz
  have hphase : (z / (‖z‖ : ℂ)) ^ m ≠ 0 :=
    pow_ne_zero _ (div_ne_zero hz0 (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz0)))
  rw [referenceSection_eq_phase f m hz2, sub_mul, mul_inv_cancel₀ hphase]
  ring

/-- For `s > 1`, the squared modulus `|α|² = 4 (p² + q²)` of a continuous field in `A_m^s`
tends to one at infinity. -/
theorem tendsto_normSq_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s)
    (hcont : Continuous x) :
    Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1) :=
  tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow (tendsto_sectionValue_mul_inv_pow hs hx hcont)

/-- **The modulus bound in the affine field space.** For `s > 1`, every vortex in `A_m^s` with
differentiable connection and `C²` section satisfies `|α| ≤ 1` everywhere. -/
theorem normSq_le_one_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s)
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0) (z : ℂ) :
    4 * (x z 2 ^ 2 + x z 3 ^ 2) ≤ 1 := by
  have hcont : Continuous x := by
    refine contDiff_zero.1 (contDiff_euclidean.2 fun i ↦ contDiff_zero.2 ?_)
    fin_cases i
    exacts [hb₁.continuous, hb₂.continuous, hp.continuous, hq.continuous]
  exact normSq_le_one_of_tendsto hb₁ hb₂ hp hq hsol
    (tendsto_normSq_of_mem_framedFieldSpace hs hx hcont) z

end TauCeti.Vortex
