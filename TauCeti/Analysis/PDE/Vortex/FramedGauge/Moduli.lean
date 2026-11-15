/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Divisor
public import TauCeti.Analysis.PDE.Vortex.WindingPhase
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.PDE.Vortex.FramedGauge.DerivativeDecay
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Smooth framed vortices in the affine Sobolev field spaces

A smooth framed degree-`m` plane vortex is a smooth field `x` on `ℂ` solving the vortex
equations whose section satisfies `α(z) (z / |z|)⁻ᵐ → 1` at infinity
(`TauCeti.Vortex.framedVortexSubMulAction`). Its framed gauge orbits are classified by their
zero divisors (`TauCeti.Vortex.framedVortexModuliEquiv`). The Fredholm and slice theory of the
vortex equations is set up on the affine Sobolev space `A_m^k = x_m + H^k`
(`TauCeti.Vortex.framedFieldSpace`) with its gauge group `G_(k+1)`. This file compares the two
models: every smooth framed vortex orbit has a representative lying in `A_m^k` for every `k`.

A smooth framed vortex need not itself lie in `A_m^k`: the phase of its section may approach the
winding phase `(z / |z|)^m` only like `1 / |z|`, which is not square integrable on the plane.
A smooth framed gauge normalizes the phase, so that outside a compact set the section is `|α|`
times the winding phase (`TauCeti.Vortex.exists_framedGaugeGroup_sectionValue_smul_eq`). In the
winding end trivialization such a vortex tends to the vacuum together with all its derivatives,
at every exponential rate `c < 1 / 2`
(`TauCeti.Vortex.isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField`). Outside the cutoff
disc, `x - x_ref` is the rotation of the section part of that difference by the winding phase,
which equals the reference section `x_ref` uses there and has bounded derivatives. Hence every
derivative of `x - x_ref` decays exponentially (`isBigO_iteratedFDeriv_sub_referenceField`). A
smooth field with this decay lies in every `H^k`
(`mem_framedFieldSpace_of_isBigO_iteratedFDeriv_sub_referenceField`), by the classical
description of `H^k`
(`TemperedDistribution.mem_realSobolevFunctions_natCast_of_memLp_iteratedFDeriv`).

With Taubes's existence theorem (`TauCeti.Vortex.framedVortexDivisor_surjective`) this shows that
every effective divisor of degree `m` is the divisor of a smooth vortex of `A_m^k`
(`sobolevVortexDivisor_surjective`). For `k ≥ 4`, where `G_(k+1)` preserves the `C²` vortices of
`A_m^k`, the divisor therefore identifies the Sobolev moduli of framed vortices with `Sym ℂ m`
(`sobolevVortexModuliEquiv`), the Sobolev counterpart of `TauCeti.Vortex.framedVortexModuliEquiv`.
Conversely, a smooth framed gauge relating two fields of `A_m^k` lies in `G_(k+1)`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`).

## Main results

All in the namespace `TauCeti.Vortex`:

* `mem_framedFieldSpace_of_isBigO_iteratedFDeriv_sub_referenceField`: a smooth field all of whose
  derivatives of `x - x_ref` are `O(exp (-c |z|))`, `c > 0`, lies in `A_m^s` for every `s`.
* `isBigO_iteratedFDeriv_sub_referenceField`: for a smooth vortex normalized at its end, every
  derivative of `x - x_ref` is `O(exp (-c |z|))` for every `c < 1 / 2`.
* `exists_framedGaugeGroup_smul_mem_framedFieldSpace`: every smooth framed vortex has a smooth
  framed gauge representative lying in `A_m^s` for every `s`, with this decay.
* `sobolevVortexDivisor_surjective`: every point of `Sym ℂ m` is the divisor of a `C²` vortex of
  `A_m^k`.
* `sobolevVortexModuliEquiv`: for `k ≥ 4`, the Sobolev moduli of framed vortices are `Sym ℂ m`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Topology Asymptotics
open scoped ContDiff

variable {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Exponential decay implies Sobolev regularity -/

/-- **Exponentially decaying fields lie in every `A_m^s`.** A smooth field `x` such that every
derivative of `x - x_ref` is `O(exp (-c |z|))` at infinity, for some `c > 0`, lies in the affine
Sobolev space `A_m^s` for every real `s`. -/
theorem mem_framedFieldSpace_of_isBigO_iteratedFDeriv_sub_referenceField (hx : ContDiff ℝ ∞ x)
    {c : ℝ} (hc : 0 < c)
    (hdec : ∀ n : ℕ, iteratedFDeriv ℝ n (x - referenceField f m) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖))) (s : ℝ) :
    x ∈ framedFieldSpace f m s := by
  obtain ⟨k, hk⟩ := exists_nat_ge s
  refine framedFieldSpace_mono f m hk (mem_framedFieldSpace.2 (mem_sobolevFields.2 fun i ↦ ?_))
  have hy : ContDiff ℝ ∞ (x - referenceField f m) := hx.sub (contDiff_referenceField f m)
  have hyi : ContDiff ℝ ∞ fun z ↦ (x - referenceField f m) z i :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).contDiff.comp hy
  refine TemperedDistribution.mem_realSobolevFunctions_natCast_of_memLp_iteratedFDeriv
    (by norm_num) (by norm_num) (hyi.of_le (by exact_mod_cast le_top)) fun n _ ↦ ?_
  exact (hyi.continuous_iteratedFDeriv (by exact_mod_cast le_top)).memLp_of_isBigO_exp_neg_mul_norm
    hc ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).isBigO_iteratedFDeriv_comp_left
      hy (by exact_mod_cast le_top) (hdec n)) 2

/-! ### Exponential decay of all derivatives of `x - x_ref` -/

/-- Outside the cutoff disc, `x - x_ref` is the rotation of the section part of
`u⁻¹ · x - vacuum` by the winding phase `u`, which there equals the reference section `s`. In
coordinates it is `P (g w) + J (s w * Q (g w))`, where `g w = (u⁻¹ · x) w - vacuum`, `P` keeps the
connection coordinates, `Q` reads the section coordinates as a complex number and `J` writes a
complex number into the section coordinates. -/
private theorem sub_referenceField_apply_eq (f : ContDiffBump (0 : ℝ)) {w : ℂ}
    (hw : f.rOut ≤ ‖w‖ ^ 2) {g : EuclideanSpace ℝ (Fin 4)}
    (hg : gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w = g) :
    (x - referenceField f m) w =
      !₂[g 0, g 1, (referenceSection f m w).re * g 2 - (referenceSection f m w).im * g 3,
        (referenceSection f m w).im * g 2 + (referenceSection f m w).re * g 3] := by
  have hsub : x - referenceField f m = gaugeLinearAction (windingPhase m)
      (gaugeTransform (windingPhase m)⁻¹ x - gaugeTransform (windingPhase m)⁻¹ (referenceField f m))
      := by
    rw [gaugeTransform_sub_gaugeTransform, gaugeLinearAction_gaugeLinearAction_inv]
  have hs : referenceSection f m w = windingPhase m w := by
    rw [referenceSection_eq_phase f m hw, coe_windingPhase m (ne_zero_of_rOut_le_norm_sq f hw)]
  rw [hsub, gaugeLinearAction_apply, Pi.sub_apply,
    gaugeTransform_inv_windingPhase_referenceField f m hw, hg, hs]

/-- Near infinity, the winding end trivialization of a vortex normalized at its end, minus the
vacuum, agrees with a globally smooth field: outside a compact set it is
`(-(∂_I ℓ) / 2, (∂_1 ℓ) / 2, (exp (ℓ / 2) - 1) / 2, 0)` for a smooth `ℓ` equal to `log |α|²` there
(`TauCeti.Vortex.gaugeTransform_inv_apply_eq`). -/
private theorem exists_contDiff_eventuallyEq_endTrivialization
    (hp : ContDiff ℝ ∞ (fun z ↦ x z 2)) (hq : ContDiff ℝ ∞ (fun z ↦ x z 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z) :
    ∃ g : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ g ∧ ∀ᶠ z in cocompact ℂ,
      (fun w ↦ gaugeTransform (windingPhase m)⁻¹ x w - vacuumField w) =ᶠ[𝓝 z] g := by
  have hs : ContDiff ℝ ∞ (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) :=
    contDiff_const.mul ((hp.pow 2).add (hq.pow 2))
  have hpos : ∀ᶠ z in cocompact ℂ, 1 / 2 < 4 * (x z 2 ^ 2 + x z 3 ^ 2) :=
    hlim.eventually (lt_mem_nhds (by norm_num))
  -- A smooth `ℓ` on the plane which is `log |α|²` near every point outside a compact set.
  obtain ⟨ℓ, hℓ, hagree⟩ := exists_contDiff_eventually_eventuallyEq
    (f := fun z ↦ Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)))
    (hpos.mono fun z hz ↦ hs.contDiffAt.log (by linarith))
  obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := ℂ) ▸ hagree.and (hphase.and hpos))
  have hopen : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hDℓ : ContDiff ℝ ∞ (fderiv ℝ ℓ) := hℓ.fderiv_right (by norm_cast)
  refine ⟨fun w ↦ !₂[-(fderiv ℝ ℓ w I / 2), fderiv ℝ ℓ w 1 / 2, (Real.exp (ℓ w / 2) - 1) / 2, 0],
    contDiff_euclidean.2 fun i ↦ ?_, ?_⟩
  · fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val]
    · exact ((hDℓ.clm_apply contDiff_const).div_const 2).neg
    · exact (hDℓ.clm_apply contDiff_const).div_const 2
    · exact ((Real.contDiff_exp.comp (hℓ.div_const 2)).sub contDiff_const).div_const 2
    · exact contDiff_const
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hz
  filter_upwards [hopen.mem_nhds hz] with w (hw : R < ‖w‖)
  have hRw := hR hw.le
  rw [gaugeTransform_inv_apply_eq (hp.differentiable (by simp) w)
    (hq.differentiable (by simp) w) (fun h ↦ by linarith [hRw.2.2]) (by simp [hsol w])
    (by simp [hsol w])
    (eventually_of_mem (hopen.mem_nhds hw) fun v (hv : R < ‖v‖) ↦ (hR hv.le).2.1) hRw.1,
    vacuumField_apply]
  ext i
  fin_cases i <;> simp
  ring

/-- **Exponential decay of all derivatives of `x - x_ref`.** Let `x` be a plane vortex with smooth
section and `|α| → 1` at infinity whose section is `|α|` times the winding phase `(z / |z|)^m`
outside a compact set. Then for every order `n` and every rate `c < 1 / 2`, the `n`-th derivative
of `x - x_ref` is `O(exp (-c |z|))` at infinity. This extends the first-order estimate
`TauCeti.Vortex.exists_eventually_norm_fderiv_sub_referenceField_le_mul_exp` to every order. -/
theorem isBigO_iteratedFDeriv_sub_referenceField (f : ContDiffBump (0 : ℝ))
    (hp : ContDiff ℝ ∞ (fun z ↦ x z 2)) (hq : ContDiff ℝ ∞ (fun z ↦ x z 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hphase : ∀ᶠ z in cocompact ℂ, sectionValue x z = ‖sectionValue x z‖ * windingPhase m z)
    {c : ℝ} (hc : c < 1 / 2) (n : ℕ) :
    iteratedFDeriv ℝ n (x - referenceField f m) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨g, hg, hgx⟩ := exists_contDiff_eventuallyEq_endTrivialization hp hq hsol hlim hphase
  -- Every derivative of `g` decays, since `g` is the end trivialization minus the vacuum.
  have hgdec (i : ℕ) : iteratedFDeriv ℝ i g =O[cocompact ℂ] fun z ↦ Real.exp (-(c * ‖z‖)) :=
    (isBigO_iteratedFDeriv_gaugeTransform_inv_sub_vacuumField hp hq hsol hlim hphase hc
      i).congr' (hgx.mono fun _ hz ↦ (hz.iteratedFDeriv ℝ i).eq_of_nhds) EventuallyEq.rfl
  have hout : ∀ᶠ z in cocompact ℂ, ∀ᶠ w in 𝓝 z, f.rOut ≤ ‖w‖ ^ 2 := by
    filter_upwards [((tendsto_pow_atTop two_ne_zero).comp
      tendsto_norm_cocompact_atTop).eventually_gt_atTop f.rOut] with z hz
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.pow 2)).mem_nhds hz] with w hw
    exact hw.le
  -- The linear maps `P`, `Q`, `J` of `sub_referenceField_apply_eq`.
  set P : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single 0 1) +
      (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 1 1)
  set Q : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℂ :=
    (EuclideanSpace.proj 2).smulRight (1 : ℂ) + (EuclideanSpace.proj 3).smulRight I
  set J : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
    reCLM.smulRight (EuclideanSpace.single 2 1) + imCLM.smulRight (EuclideanSpace.single 3 1)
  have hsR : ContDiff ℝ ∞ (referenceSection f m) := contDiff_referenceSection f m
  have hQg : ContDiff ℝ ∞ fun w ↦ Q (g w) := Q.contDiff.comp hg
  have hprod : ContDiff ℝ ∞ fun w ↦ referenceSection f m w * Q (g w) := hsR.mul hQg
  have hPg : ContDiff ℝ ∞ fun w ↦ P (g w) := P.contDiff.comp hg
  have hJ : ContDiff ℝ ∞ fun w ↦ J (referenceSection f m w * Q (g w)) := J.contDiff.comp hprod
  -- Outside a compact set, `x - x_ref = P g + J (s Q g)` near every point.
  have hfor : ∀ᶠ z in cocompact ℂ, (x - referenceField f m) =ᶠ[𝓝 z]
      fun w ↦ P (g w) + J (referenceSection f m w * Q (g w)) := by
    filter_upwards [hgx, hout] with z hz hz'
    filter_upwards [hz, hz'] with w hw hw'
    rw [sub_referenceField_apply_eq f hw' hw]
    generalize referenceSection f m w = σ
    generalize g w = v
    ext i
    fin_cases i <;> simp [P, Q, J, add_comm]
  -- The reference section has bounded derivatives.
  have hsRb (i : ℕ) :
      iteratedFDeriv ℝ i (referenceSection f m) =O[cocompact ℂ] fun _ ↦ (1 : ℝ) := by
    obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceSection_le f m i
    exact IsBigO.of_bound C (.of_forall fun z ↦ by simpa using hC z)
  have hprodO : iteratedFDeriv ℝ n (fun w ↦ referenceSection f m w * Q (g w)) =O[cocompact ℂ]
      fun z ↦ Real.exp (-(c * ‖z‖)) := by
    simpa only [one_mul, ContinuousLinearMap.mul_apply'] using
      (ContinuousLinearMap.mul ℝ ℂ).isBigO_iteratedFDeriv_of_bilinear
      hsR hQg (n := n) (by exact_mod_cast le_top) (fun i _ ↦ hsRb i)
      fun i _ ↦ Q.isBigO_iteratedFDeriv_comp_left hg (by exact_mod_cast le_top) (hgdec i)
  refine (((P.isBigO_iteratedFDeriv_comp_left hg (by exact_mod_cast le_top) (hgdec n)).add
    (J.isBigO_iteratedFDeriv_comp_left hprod (by exact_mod_cast le_top) hprodO)).congr' ?_
    EventuallyEq.rfl)
  filter_upwards [hfor] with z hz
  rw [← fun_iteratedFDeriv_add_apply (hPg.contDiffAt.of_le (by exact_mod_cast le_top))
    (hJ.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (hz.iteratedFDeriv ℝ n).eq_of_nhds.symm

/-! ### Smooth framed vortices have representatives in `A_m^s` -/

/-- **Every smooth framed vortex orbit meets every `A_m^s`.** A smooth framed degree-`m` vortex
`x` is carried by a smooth framed gauge `u` to a field `u · x` lying in the affine Sobolev space
`A_m^s` for every real `s`, such that every derivative of `u · x - x_ref` is `O(exp (-c |z|))`
at infinity for every rate `c < 1 / 2`. -/
theorem exists_framedGaugeGroup_smul_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ))
    (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    ∃ u : framedGaugeGroup, (∀ s : ℝ, u • x ∈ framedFieldSpace f m s) ∧
      ∀ c < 1 / 2, ∀ n : ℕ, iteratedFDeriv ℝ n (u • x - referenceField f m) =O[cocompact ℂ]
        fun z ↦ Real.exp (-(c * ‖z‖)) := by
  obtain ⟨u, hu⟩ := exists_framedGaugeGroup_sectionValue_smul_eq hx hframe
  obtain ⟨huc, hu1⟩ := (mem_framedGaugeGroup _).1 u.property
  have hy : ContDiff ℝ ∞ (u • x) := contDiff_gaugeTransform (by simpa using huc) hx
  have hsol' (z : ℂ) : equation (u • x) z = 0 :=
    (equation_gaugeTransform_eq_zero_iff ((huc.of_le (by norm_cast)).contDiffAt)
      fun i ↦ ((contDiff_euclidean.1 hx i).differentiable (by simp)).differentiableAt).2 (hsol z)
  have hlim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow
    (tendsto_sectionValue_gaugeTransform hu1 hframe)
  have hdec := fun c (hc : c < 1 / 2) n ↦
    isBigO_iteratedFDeriv_sub_referenceField f (contDiff_euclidean.1 hy 2)
      (contDiff_euclidean.1 hy 3) hsol' hlim hu hc n
  exact ⟨u, mem_framedFieldSpace_of_isBigO_iteratedFDeriv_sub_referenceField hy (c := 1 / 4)
    (by norm_num) (hdec (1 / 4) (by norm_num)), hdec⟩

/-! ### The Sobolev moduli of framed vortices -/

variable {k : ℕ} [Fact (1 < k)]

/-- **Existence on the Sobolev scale.** For `k ≥ 2`, every effective divisor of degree `m`,
repeated points included, is the divisor of a `C²` vortex of `A_m^k`. -/
theorem sobolevVortexDivisor_surjective :
    Function.Surjective (sobolevVortexDivisor (f := f) (m := m) (k := k)) := fun D ↦ by
  obtain ⟨x, hx⟩ := framedVortexDivisor_surjective m D
  obtain ⟨hxc, hxsol, hxfr⟩ := mem_framedVortexSubMulAction.1 x.2
  obtain ⟨u, hu, -⟩ := exists_framedGaugeGroup_smul_mem_framedFieldSpace f hxc hxsol hxfr
  obtain ⟨hyc, hysol, -⟩ := mem_framedVortexSubMulAction.1 (u • x).2
  refine ⟨⟨⟨u • (x : ℂ → EuclideanSpace ℝ (Fin 4)), hu k⟩,
    mem_sobolevVortices.2 ⟨hyc.of_le (by simp), hysol⟩⟩, ?_⟩
  rw [sobolevVortexDivisor_eq_framedVortexDivisor _ (u • x) rfl, framedVortexDivisor_smul, hx]

/-- For `k ≥ 4`, every point of `Sym ℂ m` is the divisor of a `G_(k+1)`-orbit of `C²` vortices of
`A_m^k`. -/
theorem sobolevVortexModuliDivisor_surjective {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    Function.Surjective (sobolevVortexModuliDivisor (f := f) (m := m) (hs := hs) hk) := fun D ↦
  (sobolevVortexDivisor_surjective D).elim fun x hx ↦
    ⟨Quotient.mk'' ⟨x.1, mem_sobolevVortexSubMulAction.2 x.2⟩, by
      rw [sobolevVortexModuliDivisor_mk]
      exact hx⟩

/-- **The Sobolev moduli of framed vortices are `Sym ℂ m`** (Taubes). For `k ≥ 4`, the divisor
identifies the orbits of `G_(k+1)` on the `C²` vortices of `A_m^k` with the effective divisors of
degree `m`. -/
def sobolevVortexModuliEquiv {hs : 1 < (k : ℝ) + 1} (hk : 3 < k) :
    MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk) ≃ Sym ℂ m :=
  Equiv.ofBijective (sobolevVortexModuliDivisor hk)
    ⟨sobolevVortexModuliDivisor_injective hk, sobolevVortexModuliDivisor_surjective hk⟩

/-- The equivalence sends an orbit to the divisor of its vortices. -/
@[simp]
theorem sobolevVortexModuliEquiv_apply {hs : 1 < (k : ℝ) + 1} (hk : 3 < k)
    (q : MulAction.orbitRel.Quotient (sobolevGaugeGroup hs)
      (sobolevVortexSubMulAction (f := f) (m := m) (hs := hs) hk)) :
    sobolevVortexModuliEquiv hk q = sobolevVortexModuliDivisor hk q :=
  (rfl)

end TauCeti.Vortex
