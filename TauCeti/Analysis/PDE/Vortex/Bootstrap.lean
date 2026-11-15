/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EquationMap
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Sobolev
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Elliptic bootstrap for gauge-fixed plane vortices

The framed degree-`m` plane vortex fields form the affine space `A_m^k = x_m + H^k`
(`TauCeti.Vortex.framedFieldSpace`), and the vortex equation together with a gauge-fixing
condition is an elliptic system on it. This file proves the corresponding regularity: a `C¹` field
of `A_m^k`, `k ≥ 2`, whose equation and gauge-fixing defects lie in `H^k` lies in `A_m^(k+1)`.
Hence a `C¹` vortex of `A_m^k` in the Coulomb slice through a base field lying in every `A_m^j` lies
in every `A_m^j` and is smooth, so these solutions do not depend on the Sobolev order `k ≥ 2` used
to define the field space.

**The vacuum operator on classical fields.** At the vacuum `vacuumField` (`α = 1`, `a = 0`) the
gauge-fixed operator `L₀ = gaugeFixedOperator vacuumField` has constant coefficients, and on
tempered distributions it is a bijection `H^(s+1) → H^s` for every `s`
(`TauCeti.Vortex.memSobolev_temperedVacuumOperator_iff`). For a `C¹` field `y ∈ H^s`, `s ≥ 1`,
the classical first derivatives of `y` lie in `L²` and are its distributional derivatives
(`TauCeti.lineDerivOp_toTemperedDistribution_ofReal_eq_of_contDiff`), so the
classical expression `L₀ y` is the tempered vacuum operator applied to `y`. Consequently, if
`L₀ y ∈ H^s` then `y ∈ H^(s+1)` (`TauCeti.Vortex.mem_sobolevFields_add_one_of_gaugeFixedOperator`).

**The gauge-fixed vortex map.** At a field `x ∈ A_m^n`, `n ≥ 2`, the operator `L_x` differs from
`L₀` by a zeroth-order term whose coefficients are the coordinates of `x - vacuumField`. These are
reference coordinates, smooth with bounded derivatives, plus an `H^n` tail, so the difference maps
`H^n` to `H^n` (`TauCeti.Vortex.gaugeFixedOperator_sub_mem_sobolevFields`). Let `x₀ ∈ A_m^(k+1)` be
a `C¹` base field, for instance the reference field itself, and let `x ∈ A_m^k`, `k ≥ 2`, be
a `C¹` field. Write `y = x - x_m`. The exact quadratic expansion of the equation about the
reference field gives

`L_(x_m) y = (d₀*_(x_m) y, equation x - equation x_m - quadraticTerm y)`.

The equation defect of `x_m` is smooth with compact support and the quadratic term maps `H^k` to
`H^k`, since `H^k(ℂ)` is an algebra. The gauge-fixing row is controlled by the Coulomb condition
relative to `x₀`, since `d₀*_(x_m) y - d₀*_(x₀) (x - x₀)` is `d₀*_(x_m) (x₀ - x_m)` plus
products of `H^k` functions. Hence, if the equation defect of `x` and the gauge-fixing defect
`d₀*_(x₀) (x - x₀)` lie in `H^k`, then `L₀ y ∈ H^k`, and the vacuum regularity gives `y ∈ H^(k+1)`,
that is, `x ∈ A_m^(k+1)` (`TauCeti.Vortex.mem_framedFieldSpace_add_one_of_equation`).

For a solution of the vortex equation in the Coulomb slice through a base field lying in every
`A_m^j`, iterating gives `x ∈ A_m^j` for every `j`, and the Sobolev embedding makes `x` smooth
(`TauCeti.Vortex.mem_framedFieldSpace_of_equation_eq_zero`,
`TauCeti.Vortex.contDiff_of_equation_eq_zero`). The reference field is such a base field
(`TauCeti.Vortex.referenceField_mem_framedFieldSpace`).

These are regularity statements for fields already assumed `C¹`. No slice theorem, which would put
an arbitrary field of `A_m^k` into the Coulomb slice by a gauge transformation, is proved here.

## Main results

All in the namespace `TauCeti.Vortex`:

* `mem_sobolevFields_add_one_of_gaugeFixedOperator`: a `C¹` field `y ∈ H^s`, `s ≥ 1`, with
  `L₀ y ∈ H^s` lies in `H^(s+1)`.
* `gaugeFixedOperator_sub_mem_sobolevFields`: `L_x - L₀` maps `H^n` to `H^n` for `x ∈ A_m^n`.
* `mem_framedFieldSpace_add_one_of_equation`: a `C¹` field of `A_m^k`, `k ≥ 2`, whose equation
  defect and Coulomb defect relative to a base field of `A_m^(k+1)` lie in `H^k` lies in
  `A_m^(k+1)`.
* `mem_framedFieldSpace_of_equation_eq_zero`, `contDiff_of_equation_eq_zero`: a `C¹` vortex in
  `A_m^k`, `k ≥ 2`, in the Coulomb slice through a base field lying in every `A_m^j` lies in every
  `A_m^j` and is smooth.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution
open scoped ContDiff LineDeriv SchwartzMap

/-! ### Elliptic regularity of the vacuum operator on classical fields -/

/-- The complexified tempered distribution of a real `L²` function on the plane. -/
private abbrev toDistr : Lp ℝ 2 (volume : Measure ℂ) →ₗ[ℝ] 𝓢'(ℂ, ℂ) :=
  ((Lp.toTemperedDistributionCLM ℂ (volume : Measure ℂ) 2).restrictScalars ℝ).toLinearMap ∘ₗ
    Complex.ofRealCLM.compLpₗ (p := 2) (μ := (volume : Measure ℂ))

/-- The tempered vacuum operator of a `C¹` field, given by `L²` representatives `u` of its
coordinates and `u'` of their classical derivatives, is the distribution of an `L²` representative
of the classical `L₀ y`. -/
private theorem exists_temperedVacuumOperator_eq {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (u : Fin 4 → Lp ℝ 2 (volume : Measure ℂ)) (u' : Fin 4 → ℂ → Lp ℝ 2 (volume : Measure ℂ))
    (huy : ∀ i, u i =ᵐ[volume] fun z ↦ y z i)
    (hu'y : ∀ i v, u' i v =ᵐ[volume] fun z ↦ fderiv ℝ (fun w ↦ y w i) z v)
    (hD : ∀ i v, ∂_{v} (toDistr (u i)) = toDistr (u' i v)) (j : Fin 4) :
    ∃ g : Lp ℝ 2 (volume : Measure ℂ),
      g =ᵐ[volume] (fun z ↦ gaugeFixedOperator vacuumField y z j) ∧
        temperedVacuumOperator (fun i ↦ toDistr (u i)) j = toDistr g := by
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · refine ⟨u' 0 1 + u' 1 I + (1 / 2 : ℝ) • u 3, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add (u' 0 1 + u' 1 I) ((1 / 2 : ℝ) • u 3),
        Lp.coeFn_add (u' 0 1) (u' 1 I), Lp.coeFn_smul (1 / 2 : ℝ) (u 3), hu'y 0 1, hu'y 1 I,
        huy 3] with z h₁ h₂ h₃ h₄ h₅ h₆
      simp only [h₁, h₂, h₃, Pi.add_apply, Pi.smul_apply, h₄, h₅, h₆, smul_eq_mul]
      simp [gaugeAdjoint_def, vacuumField_apply]
    · rw [temperedVacuumOperator_apply_zero, hD, hD, map_add, map_add, map_smul]
  · refine ⟨u' 0 I - u' 1 1 + (1 / 2 : ℝ) • u 2, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add (u' 0 I - u' 1 1) ((1 / 2 : ℝ) • u 2),
        Lp.coeFn_sub (u' 0 I) (u' 1 1), Lp.coeFn_smul (1 / 2 : ℝ) (u 2), hu'y 0 I, hu'y 1 1,
        huy 2] with z h₁ h₂ h₃ h₄ h₅ h₆
      simp only [h₁, h₂, h₃, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, h₄, h₅, h₆,
        smul_eq_mul]
      simp [vacuumField_apply]
    · rw [temperedVacuumOperator_apply_one, hD, hD, map_add, map_sub, map_smul]
  · refine ⟨u' 2 1 - u' 3 I - (1 / 2 : ℝ) • u 1, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_sub (u' 2 1 - u' 3 I) ((1 / 2 : ℝ) • u 1),
        Lp.coeFn_sub (u' 2 1) (u' 3 I), Lp.coeFn_smul (1 / 2 : ℝ) (u 1), hu'y 2 1, hu'y 3 I,
        huy 1] with z h₁ h₂ h₃ h₄ h₅ h₆
      simp only [h₁, h₂, h₃, Pi.sub_apply, Pi.smul_apply, h₄, h₅, h₆, smul_eq_mul]
      simp [vacuumField_apply]
      ring
    · rw [temperedVacuumOperator_apply_two, hD, hD, map_sub, map_sub, map_smul]
  · refine ⟨u' 2 I + u' 3 1 + (1 / 2 : ℝ) • u 0, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add (u' 2 I + u' 3 1) ((1 / 2 : ℝ) • u 0),
        Lp.coeFn_add (u' 2 I) (u' 3 1), Lp.coeFn_smul (1 / 2 : ℝ) (u 0), hu'y 2 I, hu'y 3 1,
        huy 0] with z h₁ h₂ h₃ h₄ h₅ h₆
      simp only [h₁, h₂, h₃, Pi.add_apply, Pi.smul_apply, h₄, h₅, h₆, smul_eq_mul]
      simp [vacuumField_apply]
      ring
    · rw [temperedVacuumOperator_apply_three, hD, hD, map_add, map_add, map_smul]

/-- **Elliptic regularity of the vacuum operator.** A `C¹` field `y ∈ H^s`, `s ≥ 1`, whose image
under the vacuum operator `L₀ = gaugeFixedOperator vacuumField` lies in `H^s` lies in `H^(s+1)`. -/
theorem mem_sobolevFields_add_one_of_gaugeFixedOperator {s : ℝ} (hs : 1 ≤ s)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields s) (hyc : ContDiff ℝ 1 y)
    (hL : gaugeFixedOperator vacuumField y ∈ sobolevFields s) : y ∈ sobolevFields (s + 1) := by
  -- `L²` representatives of the coordinates and of their classical derivatives.
  choose u huy _ using fun i ↦ mem_realSobolevFunctions.1 (mem_sobolevFields.1 hy i)
  have hd (i : Fin 4) (v : ℂ) :
      (fun z ↦ fderiv ℝ (fun w ↦ y w i) z v) ∈ realSobolevFunctions ℂ (s - 1) 2 :=
    fderiv_apply_mem_realSobolevFunctions (by norm_num) (by norm_num) (by linarith)
      (contDiff_euclidean.1 hyc i) (by simpa using mem_sobolevFields.1 hy i) v
  choose u' hu'y _ using fun i v ↦ mem_realSobolevFunctions.1 (hd i v)
  -- The classical derivatives are the distributional derivatives, so `L₀` of the tempered field
  -- of `y` is the distribution of the classical `L₀ y`, which lies in `H^s`.
  have hD (i : Fin 4) (v : ℂ) : ∂_{v} (toDistr (u i)) = toDistr (u' i v) :=
    lineDerivOp_toTemperedDistribution_ofReal_eq_of_contDiff (contDiff_euclidean.1 hyc i)
      (huy i) (hu'y i v)
  have hLY (j : Fin 4) :
      MemSobolev (s + 1 - 1) 2 (temperedVacuumOperator (fun i ↦ toDistr (u i)) j) := by
    obtain ⟨g, hg, hgY⟩ := exists_temperedVacuumOperator_eq u u' huy hu'y hD j
    obtain ⟨w, hw, hwS⟩ := mem_realSobolevFunctions.1 (mem_sobolevFields.1 hL j)
    rw [hgY, Lp.ext (hg.trans hw.symm), add_sub_cancel_right]
    exact hwS
  -- The vacuum operator is a bijection `H^(s+1) → H^s` on tempered fields.
  have hY := memSobolev_temperedVacuumOperator_iff.1 hLY
  exact mem_sobolevFields.2 fun i ↦ mem_realSobolevFunctions.2 ⟨u i, huy i, hY i⟩

/-! ### The gauge-fixed operator at a framed field -/

/-- **`L_x - L₀` has order zero.** For a field `x ∈ A_m^n`, `n ≥ 2`, the gauge-fixed operators at
`x` and at the vacuum differ on `y ∈ H^n` by a field in `H^n`: their difference is multiplication of
`y` by the coordinates of `x - vacuumField`. -/
theorem gaugeFixedOperator_sub_mem_sobolevFields {f : ContDiffBump (0 : ℝ)} {m n : ℕ}
    (hn : 1 < n) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m n)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ sobolevFields n) :
    gaugeFixedOperator x y - gaugeFixedOperator vacuumField y ∈ sobolevFields n := by
  have hp (a b : Fin 4) : (fun z ↦ x z a * y z b) ∈ realSobolevFunctions ℂ n 2 :=
    mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hn hx a (mem_sobolevFields.1 hy b)
  have hc (b : Fin 4) : (fun z ↦ (1 / 2 : ℝ) * y z b) ∈ realSobolevFunctions ℂ n 2 :=
    Submodule.smul_mem _ (1 / 2 : ℝ) (mem_sobolevFields.1 hy b)
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert sub_mem (sub_mem (hp 2 3) (hp 3 2)) (hc 3) using 1
    ext z
    simp [gaugeAdjoint_def, vacuumField_apply]
    ring
  · convert sub_mem (add_mem (hp 2 2) (hp 3 3)) (hc 2) using 1
    ext z
    simp [vacuumField_apply]
    ring
  · convert add_mem (neg_mem (add_mem (add_mem (add_mem (hp 0 3) (hp 3 0)) (hp 1 2)) (hp 2 1)))
      (hc 1) using 1
    ext z
    simp [vacuumField_apply]
    ring
  · convert sub_mem (sub_mem (sub_mem (add_mem (hp 0 2) (hp 2 0)) (hp 1 3)) (hp 3 1)) (hc 0)
      using 1
    ext z
    simp [vacuumField_apply]
    ring

/-! ### The bootstrap -/

/-- The Coulomb defect relative to a base field `x₀ ∈ A_m^(k+1)` controls the Coulomb defect
relative to the reference field: if `d₀*_(x₀) (x - x₀) ∈ H^k` then `d₀*_(x_m) (x - x_m) ∈ H^k`. -/
private theorem gaugeAdjoint_referenceField_mem {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : x₀ ∈ framedFieldSpace f m (k + 1)) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x)
    (hgauge : gaugeAdjoint x₀ (x - x₀) ∈ realSobolevFunctions ℂ k 2) :
    gaugeAdjoint (referenceField f m) (x - referenceField f m) ∈ realSobolevFunctions ℂ k 2 := by
  set xm := referenceField f m
  have hxmc : ContDiff ℝ 1 xm := (contDiff_referenceField f m).of_le (by simp)
  set y₀ := x₀ - xm
  have hy₀ : y₀ ∈ sobolevFields (k + 1) := mem_framedFieldSpace.1 hx₀
  set w := x - x₀
  have hw : w ∈ sobolevFields k := by
    have : w = (x - xm) - y₀ := by simp [w, y₀]
    rw [this]
    exact sub_mem (mem_framedFieldSpace.1 hx) (sobolevFields_mono (by linarith) hy₀)
  have h₁ : gaugeAdjoint xm y₀ ∈ realSobolevFunctions ℂ k 2 :=
    gaugeAdjoint_mem_realSobolevFunctions (by omega) (referenceField_mem_framedFieldSpace f m _)
      (by exact_mod_cast hy₀) (hx₀c.sub hxmc)
  have hxw (a b : Fin 4) : (fun z ↦ y₀ z a * w z b) ∈ realSobolevFunctions ℂ k 2 :=
    mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul (by exact_mod_cast hk))
      (mem_sobolevFields.1 (sobolevFields_mono (by linarith) hy₀) a) (mem_sobolevFields.1 hw b)
  -- With `x - x_m = w + y₀` and `x₀ = x_m + y₀`, the two Coulomb defects differ by
  -- `d₀*_(x_m) y₀` and products of coordinates of `y₀` and `w`.
  have hsplit : x - xm = w + y₀ := by simp [w, y₀]
  have hdiff (v : ℂ → EuclideanSpace ℝ (Fin 4)) (hv : ContDiff ℝ 1 v) (i : Fin 4) (z : ℂ) :
      DifferentiableAt ℝ (fun w ↦ v w i) z :=
    (contDiff_euclidean.1 hv i).differentiable one_ne_zero z
  convert add_mem (sub_mem (add_mem hgauge (hxw 3 2)) (hxw 2 3)) h₁ using 1
  ext z
  have hx₀z (i : Fin 4) : x₀ z i = xm z i + y₀ z i := by simp [y₀]
  rw [hsplit]
  simp only [gaugeAdjoint_def, Pi.add_apply, Pi.sub_apply, PiLp.add_apply, hx₀z,
    fderiv_fun_add (hdiff w (hxc.sub hx₀c) 0 z) (hdiff y₀ (hx₀c.sub hxmc) 0 z),
    fderiv_fun_add (hdiff w (hxc.sub hx₀c) 1 z) (hdiff y₀ (hx₀c.sub hxmc) 1 z), FunLike.coe_add]
  ring

/-- The equation rows of `L_(x_m) (x - x_m)` lie in `H^k` when the equation defect of `x` does:
by the exact quadratic expansion they are `equation x - equation x_m - quadraticTerm (x - x_m)`. -/
private theorem linearizedEquation_referenceField_mem {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m k)
    (hxc : ContDiff ℝ 1 x) (heq : ∀ i, (fun z ↦ equation x z i) ∈ realSobolevFunctions ℂ k 2)
    (i : Fin 3) :
    (fun z ↦ linearizedEquation (referenceField f m) (x - referenceField f m) z i) ∈
      realSobolevFunctions ℂ k 2 := by
  set xm := referenceField f m
  have hxmc : ContDiff ℝ 1 xm := (contDiff_referenceField f m).of_le (by simp)
  set y := x - xm
  have hyc : ContDiff ℝ 1 y := hxc.sub hxmc
  have hexp (z : ℂ) : equation x z =
      equation xm z + linearizedEquation xm y z + quadraticTerm y z := by
    have h := equation_add_smul (z := z)
      (fun j ↦ (contDiff_euclidean.1 hxmc j).differentiable one_ne_zero z)
      (fun j ↦ (contDiff_euclidean.1 hyc j).differentiable one_ne_zero z) 1
    simpa only [one_smul, one_pow, y, add_sub_cancel] using h
  convert sub_mem
    (sub_mem (heq i) (equation_referenceField_apply_mem_realSobolevFunctions f m k i))
    (quadraticTerm_apply_mem_realSobolevFunctions (by exact_mod_cast hk)
      (mem_framedFieldSpace.1 hx) i) using 1
  ext z
  simp only [Pi.sub_apply, hexp z, PiLp.add_apply, xm]
  ring

/-- **Gauge-fixed fields gain one derivative.** Let `k ≥ 2`, let `x₀ ∈ A_m^(k+1)` be a `C¹` base
field and let `x ∈ A_m^k` be a `C¹` field. If the equation defect of `x` and its Coulomb defect
`d₀*_(x₀) (x - x₀)` relative to `x₀` lie in `H^k`, then `x ∈ A_m^(k+1)`. -/
theorem mem_framedFieldSpace_add_one_of_equation {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : x₀ ∈ framedFieldSpace f m (k + 1)) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x)
    (heq : ∀ i, (fun z ↦ equation x z i) ∈ realSobolevFunctions ℂ k 2)
    (hgauge : gaugeAdjoint x₀ (x - x₀) ∈ realSobolevFunctions ℂ k 2) :
    x ∈ framedFieldSpace f m (k + 1) := by
  have hy : x - referenceField f m ∈ sobolevFields k := mem_framedFieldSpace.1 hx
  -- `L_(x_m) (x - x_m) ∈ H^k`, row by row.
  have hL : gaugeFixedOperator (referenceField f m) (x - referenceField f m) ∈
      sobolevFields k := by
    have hrow := linearizedEquation_referenceField_mem hk hx hxc heq
    refine mem_sobolevFields.2 fun i ↦ ?_
    fin_cases i
    · simpa [-gaugeAdjoint_def] using
        gaugeAdjoint_referenceField_mem hk hx₀ hx₀c hx hxc hgauge
    · simpa using hrow 0
    · simpa using hrow 1
    · simpa using hrow 2
  -- `L₀ = L_(x_m) - (L_(x_m) - L₀)` and `L_(x_m) - L₀` has order zero.
  have hL₀ : gaugeFixedOperator vacuumField (x - referenceField f m) ∈ sobolevFields k := by
    convert sub_mem hL (gaugeFixedOperator_sub_mem_sobolevFields hk
      (referenceField_mem_framedFieldSpace f m k) hy) using 1
    exact (sub_sub_cancel _ _).symm
  exact mem_framedFieldSpace.2 <| mem_sobolevFields_add_one_of_gaugeFixedOperator
    (by exact_mod_cast hk.le) hy (hxc.sub ((contDiff_referenceField f m).of_le (by simp))) hL₀

/-- **Gauge-fixed vortices lie in every `A_m^j`.** Let `x₀` be a `C¹` base field lying in every
`A_m^j`, such as the reference field. A `C¹` solution `x ∈ A_m^k`, `k ≥ 2`, of the vortex equation
in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` lies in every `A_m^j`. -/
theorem mem_framedFieldSpace_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) (j : ℕ) :
    x ∈ framedFieldSpace f m j := by
  have hzero (s : ℝ) : (0 : ℂ → ℝ) ∈ realSobolevFunctions ℂ s 2 := zero_mem _
  -- Climb from `A_m^k` one order at a time.
  have hclimb (i : ℕ) : x ∈ framedFieldSpace f m (k + i : ℕ) := by
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      have h := mem_framedFieldSpace_add_one_of_equation (k := k + i) (by omega)
        (by exact_mod_cast hx₀ (k + i + 1)) hx₀c ih hxc
        (fun i ↦ by convert hzero _ using 1; ext z; simp [heq z])
        (by convert hzero _ using 1; ext z; exact hgauge z)
      exact_mod_cast h
  exact framedFieldSpace_mono f m (by exact_mod_cast (Nat.le_add_left j k)) (hclimb j)

/-- **Gauge-fixed vortices are smooth.** A `C¹` solution `x ∈ A_m^k`, `k ≥ 2`, of the vortex
equation in the Coulomb slice `d₀*_(x₀) (x - x₀) = 0` through a `C¹` base field `x₀` lying in every
`A_m^j` is smooth. -/
theorem contDiff_of_equation_eq_zero {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) : ContDiff ℝ ∞ x := by
  have hy : ContDiff ℝ ∞ (x - referenceField f m) := by
    refine contDiff_euclidean.2 fun i ↦ contDiff_infty.2 fun n ↦ ?_
    have hj := mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge (n + 2)
    refine contDiff_of_mem_realSobolevFunctions (s := ((n + 2 : ℕ) : ℝ)) ?_
      (mem_sobolevFields.1 (mem_framedFieldSpace.1 hj) i)
      (contDiff_euclidean.1 (hxc.sub ((contDiff_referenceField f m).of_le (by simp))) i).continuous
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  simpa using hy.add (contDiff_referenceField f m)

end TauCeti.Vortex
