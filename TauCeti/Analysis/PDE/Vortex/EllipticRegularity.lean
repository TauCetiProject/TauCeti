/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Sobolev
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.PDE.Vortex.Bootstrap
import TauCeti.Analysis.PDE.Vortex.KernelDimension
import TauCeti.Analysis.PDE.Vortex.Multiplier
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Elliptic regularity and weak-kernel comparison for the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴` with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a weak solution of `L_x y = f` if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for
every smooth compactly supported test field `η`; this is the notion of solution produced by the
weak right inverse of `TauCeti.Analysis.PDE.Vortex.RightInverse`. This file shows that weak
solutions gain derivatives on the Sobolev scale `sobolevFields s` of the framed field space,
upgrades weak solutions at smooth fields with bounded derivatives to smooth classical solutions,
and identifies the weak `L²` kernel `weakGaugeFixedKernel x` with the classical kernel
`gaugeFixedKernel x`, giving real dimension `2 m` at framed degree-`m` vortices.

The principal part of `L_x` is that of the vacuum operator `L₀` (`vacuumOperator`), and
`L_x - L₀` is multiplication by a matrix whose entries are coordinates of `x - vacuumField`. A weak
solution of `L_x y = f` is therefore a weak solution of `L₀ y = f - (L_x - L₀) y`. Its tempered
distribution solves this equation in the sense of distributions: real smooth compactly supported
test functions determine a tempered distribution (`TemperedDistribution.ext_real`), and on tempered
fields `L₀` is the transpose of `L₀*` on Schwartz fields (`sum_temperedVacuumOperator_apply`).
Since `L₀ : H^(s+1) → H^s` is bijective on tempered fields
(`memSobolev_temperedVacuumOperator_iff`), the weak solution lies in `H^(s+1)` as soon as the
right-hand side lies in `H^s`.

* `mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq`: at the vacuum,
  a weak `L²` solution of `L₀ y = g` with `g ∈ H^s` lies in `H^(s+1)`, for every real `s`.
* `mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`: at an essentially bounded
  measurable field `x`, a weak `L²` solution of `L_x y = f` with `f ∈ L²` lies in `H¹`. Applied to
  the weak right inverse `Q` of `exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`,
  it shows that `Q f ∈ H¹` at a bounded vortex, and with `f = 0` it shows that the weak `L²`
  kernel of `L_x` lies in `H¹`.
* `exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq`: at a bounded `C¹` plane
  vortex with `|α| → 1`, every `f ∈ L²` is `L_x y` weakly for some `y ∈ H¹`, so the `H¹ → L²`
  realization of `L_x` has zero cokernel.
* `mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`: the elliptic
  bootstrap. If `x` is smooth and its coordinates have bounded derivatives through order `k`, a
  weak `L²` solution of `L_x y = f` with `f ∈ H^k` lies in `H^(k+1)`. The multiplication by the
  coefficients of `L_x - L₀` preserves `H^k` (`mulVec_mem_sobolevFields_natCast`).
* `exists_contDiff_ae_eq_and_gaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`: if `x`
  is smooth with bounded derivatives of all orders and `f` is continuous in every `H^k`, every weak
  `L²` solution of `L_x y = f` agrees almost everywhere with a smooth field in every `H^s` solving
  `L_x w = f` classically.
* `weakGaugeFixedKernel x` and `gaugeFixedKernelEquivWeak`: the weak `L²` kernel of `L_x` and its
  linear isomorphism with `gaugeFixedKernel x` at any smooth field with bounded derivatives,
  giving exact real dimension `2 |D|` (`finrank_weakGaugeFixedKernel_eq_two_mul_card`) and `2 m`
  (`finrank_weakGaugeFixedKernel_eq_two_mul`).
* `mem_sobolevFields_one_of_mem_framedFieldSpace`,
  `exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields`,
  `finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero`, and
  `finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero`: on the framed Sobolev spaces
  `A_m^k` (`k ≥ 2`), the weak right inverse takes values in `H¹` and both classical and weak
  kernels at a `C¹` Coulomb-gauge vortex have real dimension `2 m`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (the Sobolev spaces `H^s`).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv RealInnerProductSpace ContDiff Topology

/-! ### The zeroth-order part of `L_x` -/

private theorem abs_gaugeFixedZerothOrderMatrix_le (w : EuclideanSpace ℝ (Fin 4)) (i j : Fin 4) :
    |gaugeFixedZerothOrderMatrix w i j| ≤ ‖w‖ := by
  have h (a : Fin 4) : |w a| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w a
  fin_cases i <;> fin_cases j <;> simp [gaugeFixedZerothOrderMatrix, h]

private theorem continuous_gaugeFixedZerothOrderMatrix_apply (i j : Fin 4) :
    Continuous fun w : EuclideanSpace ℝ (Fin 4) ↦ gaugeFixedZerothOrderMatrix w i j := by
  have h (a : Fin 4) : Continuous fun w : EuclideanSpace ℝ (Fin 4) ↦ w a := by fun_prop
  fin_cases i <;> fin_cases j <;> first | exact continuous_const | exact h _ | exact (h _).neg

/-! ### Real `L²` fields as tempered fields -/

/-- The `j`-th component of a real Schwartz field, as a complex Schwartz function. -/
private abbrev cpt (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (j : Fin 4) : 𝓢(ℂ, ℂ) :=
  η.postcompCLM (ofRealCLM ∘L EuclideanSpace.proj j)

/-- The `L²` pairing of a square-integrable field with a real Schwartz field, written as the sum
of the pairings of the components with the components of the tempered field. -/
private theorem integral_inner_eq_sum {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (u : Fin 4 → Lp ℝ 2 (volume : Measure ℂ)) (hu : ∀ j, u j =ᵐ[volume] fun z ↦ y z j)
    (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ((∫ z, ⟪y z, η z⟫ : ℝ) : ℂ) =
      ∑ j, Lp.toTemperedDistribution (ofRealCLM.compLp (u j)) (cpt η j) := by
  have hcpt (j : Fin 4) :
      cpt η j = (η.postcompCLM (EuclideanSpace.proj j)).postcompCLM ofRealCLM := by
    ext z
    simp
  have hint (j : Fin 4) : Integrable (fun z ↦ η z j * u j z) volume :=
    ((η.postcompCLM (EuclideanSpace.proj j)).memLp 2).integrable_mul (Lp.memLp (u j))
  simp_rw [hcpt, Lp.toTemperedDistribution_ofRealCLM_compLp_apply_postcompCLM, ← ofReal_sum]
  congr 1
  simp only [SchwartzMap.postcompCLM_apply, PiLp.proj_apply]
  rw [← integral_finsetSum _ fun j _ ↦ hint j]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hu] with z hz
  simp [PiLp.inner_apply, hz, mul_comm]

/-- The real Schwartz field `φ eᵢ` with the single nonzero component `φ` in position `i`. -/
private abbrev single (i : Fin 4) (φ : 𝓢(ℂ, ℝ)) : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) :=
  φ.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1))

private theorem sum_apply_cpt_single (F : Fin 4 → 𝓢'(ℂ, ℂ)) (i : Fin 4) (φ : 𝓢(ℂ, ℝ)) :
    ∑ j, F j (cpt (single i φ) j) = F i (φ.postcompCLM ofRealCLM) := by
  have h (j : Fin 4) : cpt (single i φ) j = if i = j then φ.postcompCLM ofRealCLM else 0 := by
    ext z
    split_ifs with hij <;> simp [hij, eq_comm]
  simp only [h, apply_ite, map_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ### Elliptic regularity -/

/-- **Elliptic regularity at the vacuum.** Let `y` be a square-integrable field which is a weak
solution of `L₀ y = g`, in the sense that `∫ ⟪y, L₀* η⟫ = ∫ ⟪g, η⟫` for every smooth compactly
supported test field `η`, where `g` lies in `L² ∩ H^s`. Then `y` lies in `H^(s+1)`. -/
theorem mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq {s : ℝ}
    {y g : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hg : g ∈ sobolevFields s)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint vacuumField η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields (s + 1) := by
  have hyj (j : Fin 4) : MemLp (fun z ↦ y z j) 2 volume := memLp_piLp_iff.1 hy j
  set u : Fin 4 → Lp ℝ 2 (volume : Measure ℂ) := fun j ↦ (hyj j).toLp _
  have hu (j : Fin 4) : u j =ᵐ[volume] fun z ↦ y z j := (hyj j).coeFn_toLp
  choose v hv hvs using fun j ↦ mem_realSobolevFunctions.1 (mem_sobolevFields.1 hg j)
  set Y : Fin 4 → 𝓢'(ℂ, ℂ) := fun j ↦ Lp.toTemperedDistribution (ofRealCLM.compLp (u j))
  set G : Fin 4 → 𝓢'(ℂ, ℂ) := fun j ↦ Lp.toTemperedDistribution (ofRealCLM.compLp (v j))
  -- The tempered field of `y` solves `L₀ Y = G`: test against `φ eᵢ` with `φ` compactly supported.
  have hL : temperedVacuumOperator Y = G := by
    funext i
    refine ext_real fun φ hφ ↦ ?_
    have hη : HasCompactSupport (single i φ) := by
      rw [show ⇑(single i φ) = _ ∘ φ from funext (SchwartzMap.postcompCLM_apply _ φ)]
      exact hφ.comp_left (map_zero _)
    rw [← sum_apply_cpt_single, ← sum_apply_cpt_single, sum_temperedVacuumOperator_apply,
      ← integral_inner_eq_sum u hu, ← integral_inner_eq_sum v hv]
    congr 1
    rw [← hweak _ ((single i φ).smooth ⊤) hη]
    simp_rw [gaugeFixedAdjoint_vacuumField]
  have hG (i : Fin 4) : MemSobolev (s + 1 - 1) 2 (temperedVacuumOperator Y i) := by
    rw [hL, add_sub_cancel_right]
    exact hvs i
  exact mem_sobolevFields.2 fun i ↦ mem_realSobolevFunctions.2
    ⟨u i, hu i, memSobolev_temperedVacuumOperator_iff.1 hG i⟩

/-- Square-integrable functions times essentially bounded zeroth-order coefficients are square
integrable. -/
private theorem memLp_gaugeFixedZerothOrder {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : AEStronglyMeasurable x volume) {C : ℝ} (hC : ∀ᵐ z ∂volume, ‖x z‖ ≤ C)
    (hy : MemLp y 2 volume) :
    MemLp (fun z ↦ gaugeFixedZerothOrder (x z - vacuumField z) (y z)) 2 volume := by
  have hw : AEStronglyMeasurable (fun z ↦ x z - vacuumField z) volume :=
    hx.sub (by rw [show vacuumField = _ from funext vacuumField_apply]; fun_prop)
  have hwC (z : ℂ) (hz : ‖x z‖ ≤ C) : ‖x z - vacuumField z‖ ≤ C + ‖vacuumField 0‖ := by
    rw [vacuumField_apply z, ← vacuumField_apply 0]
    exact (norm_sub_le _ _).trans (by gcongr)
  refine memLp_piLp_iff.2 fun i ↦ ?_
  simp only [gaugeFixedZerothOrder]
  refine memLp_finsetSum _ fun j _ ↦ ?_
  refine (memLp_piLp_iff.1 hy j).of_le_mul (c := C + ‖vacuumField 0‖)
    (((continuous_gaugeFixedZerothOrderMatrix_apply i j).comp_aestronglyMeasurable hw).mul
      (memLp_piLp_iff.1 hy j).aestronglyMeasurable) (hC.mono fun z hz ↦ ?_)
  rw [norm_mul]
  gcongr
  exact (abs_gaugeFixedZerothOrderMatrix_le _ i j).trans (hwC z hz)

/-- A weak solution of `L_x y = f` is a weak solution of `L₀ y = f - (L_x - L₀) y`. -/
private theorem integral_inner_gaugeFixedAdjoint_vacuumField_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hzo : MemLp (fun z ↦ gaugeFixedZerothOrder (x z - vacuumField z) (y z)) 2 volume)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hweak : ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∫ z, ⟪y z, gaugeFixedAdjoint vacuumField η z⟫ =
      ∫ z, ⟪f z - gaugeFixedZerothOrder (x z - vacuumField z) (y z), η z⟫ := by
  have hηL : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hc
  have hL : MemLp (gaugeFixedAdjoint vacuumField η) 2 volume :=
    (continuous_gaugeFixedAdjoint
      (by rw [show vacuumField = _ from funext vacuumField_apply]; fun_prop)
      (hη.of_le (by norm_cast))).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hc)
  simp_rw [inner_sub_left]
  rw [integral_sub (hf.integrable_inner hηL) (hzo.integrable_inner hηL), ← hweak]
  simp_rw [inner_gaugeFixedAdjoint_eq_add_inner_gaugeFixedZerothOrder x η _ (y _)]
  rw [integral_add (hy.integrable_inner hL) (hzo.integrable_inner hηL)]
  ring

/-- **Elliptic regularity of the gauge-fixed operator.** Let `x` be an essentially bounded
measurable field, and let `y` be a square-integrable weak solution of `L_x y = f` with `f ∈ L²`,
in the sense that `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every smooth compactly supported test field `η`.
Then `y` lies in `H¹`. -/
theorem mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : AEStronglyMeasurable x volume) {C : ℝ}
    (hC : ∀ᵐ z ∂volume, ‖x z‖ ≤ C) (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields 1 := by
  have hzo := memLp_gaugeFixedZerothOrder hx hC hy
  have hg : (fun z ↦ f z - gaugeFixedZerothOrder (x z - vacuumField z) (y z)) ∈ sobolevFields 0 :=
    mem_sobolevFields_zero_iff.2 (hf.sub hzo)
  simpa using mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq hy hg
    fun η hη hc ↦ integral_inner_gaugeFixedAdjoint_vacuumField_eq hy hf hzo hη hc (hweak η hη hc)

/-- **At a bounded plane vortex, every `L²` field is weakly the image of an `H¹` field under
`L_x`.** Let `x` be a bounded `C¹` solution of the plane vortex equation with `|α| → 1` at
infinity. For every `f ∈ L²(ℂ; ℝ⁴)` there is `y ∈ H¹(ℂ; ℝ⁴)` with `L_x y = f` weakly:
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly supported `C²` field `η`. -/
theorem exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq
    {x f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ 1 x) {C : ℝ} (hC : ∀ z, ‖x z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hf : MemLp f 2 volume) :
    ∃ y ∈ sobolevFields 1, ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η →
      HasCompactSupport η → ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫ := by
  obtain ⟨Q, hQ, -⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := volume) hx hsol hlim
  have hQf (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
      ∫ z, ⟪Q (hf.toLp f) z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫ := by
    rw [hQ _ η hη hηc]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
  exact ⟨_, mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
    hx.continuous.aestronglyMeasurable (.of_forall hC) (Lp.memLp _) hf
    fun η hη hηc ↦ hQf η (hη.of_le (by norm_cast)) hηc, hQf⟩

/-- The zeroth-order coefficients at a smooth field whose coordinates have bounded derivatives
through order `k` are smooth with bounded derivatives through order `k`. -/
private theorem contDiff_gaugeFixedZerothOrderMatrix_and_bounded {k : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun z ↦ gaugeFixedZerothOrderMatrix (x z - vacuumField z) i j) ∧
      ∃ M ≥ 0, ∀ n ≤ k, ∀ z,
        ‖iteratedFDeriv ℝ n (fun z ↦ gaugeFixedZerothOrderMatrix (x z - vacuumField z) i j) z‖ ≤
          M := by
  set P : (ℂ → ℝ) → Prop :=
    fun g ↦ ContDiff ℝ ∞ g ∧ ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ M
  have h0 : P 0 := ⟨contDiff_const, 0, le_rfl, fun n _ z ↦ by simp⟩
  have hneg {g : ℂ → ℝ} (hg : P g) : P (-g) :=
    ⟨hg.1.neg, hg.2.imp fun M hM ↦ ⟨hM.1, fun n hn z ↦ by
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hM.2 n hn z⟩⟩
  have hw (a : Fin 4) : P fun z ↦ (x z - vacuumField z) a := by
    have hxa : ContDiff ℝ ∞ fun z ↦ x z a := contDiff_euclidean.1 hx a
    have he : (fun z ↦ (x z - vacuumField z) a) = (fun z ↦ x z a) - fun _ ↦ vacuumField 0 a :=
      funext fun z ↦ by simp only [PiLp.sub_apply, Pi.sub_apply, vacuumField_apply]
    rw [he]
    -- A single bound for the derivatives through order `k`, summing the bounds for each order.
    choose! C hC using hbound a
    refine ⟨hxa.sub contDiff_const, ∑ n ∈ Finset.range (k + 1), |C n| + ‖vacuumField 0 a‖,
      by positivity, fun n hn z ↦ ?_⟩
    rw [iteratedFDeriv_sub_apply (hxa.contDiffAt.of_le (mod_cast le_top)) contDiffAt_const]
    refine (norm_sub_le _ _).trans (add_le_add ((hC n hn z).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun n ↦ |C n|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hn))))) ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [iteratedFDeriv_const_of_ne hn]
  fin_cases i <;> fin_cases j <;> first | exact h0 | exact hw _ | exact hneg (hw _)

/-- One step of the elliptic bootstrap: a weak solution in `H^k` of `L_x y = f ∈ H^k` lies in
`H^(k+1)`. -/
private theorem mem_sobolevFields_natCast_add_one_of_mem_sobolevFields {k : ℕ}
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : y ∈ sobolevFields k) (hf : f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields (k + 1) := by
  have hA := contDiff_gaugeFixedZerothOrderMatrix_and_bounded hx hbound
  have hzo : (fun z ↦ gaugeFixedZerothOrder (x z - vacuumField z) (y z)) ∈ sobolevFields k := by
    exact mulVec_mem_sobolevFields_natCast k
      (A := fun i j z ↦ gaugeFixedZerothOrderMatrix (x z - vacuumField z) i j)
      (fun i j ↦ (hA i j).1) (fun i j ↦ (hA i j).2) hy
  have hyL := memLp_of_mem_sobolevFields hy
  have hfL := memLp_of_mem_sobolevFields hf
  exact mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq hyL
    (sub_mem hf hzo) fun η hη hc ↦ integral_inner_gaugeFixedAdjoint_vacuumField_eq hyL hfL
      (memLp_of_mem_sobolevFields hzo) hη hc (hweak η hη hc)

/-- **The elliptic bootstrap for the gauge-fixed operator.** Let `x` be a smooth field whose
coordinates have bounded derivatives through order `k`, and let `y` be a square-integrable weak
solution of `L_x y = f` with `f ∈ H^k`, in the sense that `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every
smooth compactly supported test field `η`. Then `y` lies in `H^(k+1)`. -/
theorem mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq (k : ℕ)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields (k + 1) := by
  induction k with
  | zero =>
    exact mem_sobolevFields_natCast_add_one_of_mem_sobolevFields hx hbound
      (by simpa using hy) hf hweak
  | succ k ih =>
    have hy' : y ∈ sobolevFields (k + 1) :=
      ih (fun i n hn ↦ hbound i n (hn.trans k.le_succ))
        (sobolevFields_mono (by simp) hf)
    exact_mod_cast mem_sobolevFields_natCast_add_one_of_mem_sobolevFields hx hbound
      (by exact_mod_cast hy') hf hweak

/-! ### Smooth regularity and the weak `L²` kernel -/

/-- A field lying in `sobolevFields k` for every `k : ℕ` agrees almost everywhere with a smooth
field lying in `sobolevFields s` for every `s : ℝ`, with bounded derivatives of all orders and
vanishing at infinity. -/
private theorem exists_contDiff_ae_eq_of_forall_mem_sobolevFields
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ∀ k : ℕ, y ∈ sobolevFields k) :
    ∃ w : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ w ∧ y =ᵐ[volume] w ∧
      (∀ s : ℝ, w ∈ sobolevFields s) ∧
      (∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ w z i) z‖ ≤ C) ∧
      Tendsto w (cocompact ℂ) (𝓝 0) := by
  have hy_real (s : ℝ) : y ∈ sobolevFields s :=
    sobolevFields_mono (Nat.le_ceil s) (hy ⌈s⌉₊)
  have hy_i (i : Fin 4) : MemLp (fun z ↦ y z i) 2 volume :=
    memLp_piLp_iff.1 (memLp_of_mem_sobolevFields (hy 0)) i
  set u : Fin 4 → Lp ℝ 2 (volume : Measure ℂ) := fun i ↦ (hy_i i).toLp _
  have hu (i : Fin 4) : u i =ᵐ[volume] fun z ↦ y z i := (hy_i i).coeFn_toLp
  have hS (i : Fin 4) (s : ℝ) :
      MemSobolev s 2 (Lp.toTemperedDistribution (ofRealCLM.compLp (u i))) := by
    obtain ⟨u', hu', hS'⟩ := mem_realSobolevFunctions.1 (mem_sobolevFields.1 (hy_real s) i)
    have hu_eq : u' = u i := Lp.ext_iff.2 (hu'.trans (hu i).symm)
    exact hu_eq ▸ hS'
  choose g hg using fun i ↦
    (hS i 2).exists_zeroAtInftyContinuousMap_ae_eq (finrank_real_complex_lt_two_mul one_lt_two)
  have hg_smooth (i : Fin 4) : ContDiff ℝ ∞ (g i) :=
    contDiff_of_forall_memSobolev_of_ae_eq (hS i) (g i).continuous (hg i)
  set w : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun i ↦ (g i z).re
  have hw : ContDiff ℝ ∞ w := contDiff_euclidean.2 fun i ↦ reCLM.contDiff.comp (hg_smooth i)
  have huw (i : Fin 4) : u i =ᵐ[volume] fun z ↦ w z i := by
    filter_upwards [hg i, ofRealCLM.coeFn_compLp (u i)] with z hgz huz
    simpa [w] using congrArg Complex.re (huz.symm.trans hgz)
  have hyw : y =ᵐ[volume] w := by
    filter_upwards [ae_all_iff.2 fun i ↦ (hu i).symm.trans (huw i)] with z hz
    ext i
    exact hz i
  have hw_sob (s : ℝ) : w ∈ sobolevFields s :=
    mem_sobolevFields.2 fun i ↦ mem_realSobolevFunctions.2 ⟨u i, huw i, hS i s⟩
  have hw_bdd (i : Fin 4) (n : ℕ) : ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ w z i) z‖ ≤ C := by
    have hsn : (Module.finrank ℝ ℂ : ℝ) < 2 * (((n : ℝ) + 2) - n) :=
      finrank_real_complex_lt_two_mul (by linarith)
    obtain ⟨C, -, hC⟩ :=
      exists_norm_iteratedFDeriv_le_mul_norm_toBesselPotentialSpace (E := ℂ) (F := ℂ) hsn
    refine ⟨‖reCLM‖ * (C * ‖(hS i ((n : ℝ) + 2)).toBesselPotentialSpace‖), fun z ↦ ?_⟩
    have hcomp : (fun z ↦ w z i) = fun z ↦ reCLM (g i z) := rfl
    rw [hcomp]
    refine (reCLM.norm_iteratedFDeriv_comp_left (hg_smooth i).contDiffAt
      (by exact_mod_cast le_top)).trans ?_
    gcongr
    exact hC (hS i ((n : ℝ) + 2)) (g i).continuous (hg i) n le_rfl z
  exact ⟨w, hw, hyw, hw_sob, hw_bdd,
    tendsto_cocompact_of_mem_sobolevFields one_lt_two (hw_sob 2) hw.continuous⟩

/-- **Weak-to-classical smooth regularity of `L_x`.** Let `x` be a smooth field whose coordinates
have bounded derivatives of all orders, let `f` be continuous and lie in `sobolevFields k` for
every `k : ℕ`, and let `y` be a square-integrable weak solution of `L_x y = f`. Then `y` agrees
almost everywhere with a smooth field `w` lying in `sobolevFields s` for every `s : ℝ`, tending to
zero at infinity, and satisfying `L_x w = f` everywhere. -/
theorem exists_contDiff_ae_eq_and_gaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k) (hfc : Continuous f)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∃ w : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ w ∧ y =ᵐ[volume] w ∧
      (∀ s : ℝ, w ∈ sobolevFields s) ∧ Tendsto w (cocompact ℂ) (𝓝 0) ∧
      ∀ z, gaugeFixedOperator x w z = f z := by
  have hy_sob (k : ℕ) : y ∈ sobolevFields k :=
    sobolevFields_mono (by simp)
      (mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
        (fun i n _ ↦ hbound i n) hy (hf k) hweak)
  obtain ⟨w, hw, hyw, hw_sob, -, hw_lim⟩ := exists_contDiff_ae_eq_of_forall_mem_sobolevFields hy_sob
  have hLw_cont : Continuous (gaugeFixedOperator x w) :=
    continuous_gaugeFixedOperator hx.continuous (hw.of_le (by simp))
  have hae_top := TauCeti.ae_eq_of_forall_integral_inner_eq
    (Ω := (⊤ : TopologicalSpace.Opens ℂ)) (μ := volume)
    (hLw_cont.locallyIntegrable.locallyIntegrableOn _)
    (hfc.locallyIntegrable.locallyIntegrableOn _)
    fun φ ↦ by
      let η : ℂ → EuclideanSpace ℝ (Fin 4) := φ
      calc ∫ z, ⟪η z, gaugeFixedOperator x w z⟫
          = ∫ z, ⟪gaugeFixedOperator x w z, η z⟫ :=
            integral_congr_ae (.of_forall fun _ ↦ real_inner_comm _ _)
        _ = ∫ z, ⟪w z, gaugeFixedAdjoint x η z⟫ :=
            (integral_inner_gaugeFixedAdjoint hx.continuous (hw.of_le (by simp))
              (φ.contDiff.of_le (by simp)) φ.hasCompactSupport).symm
        _ = ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ :=
            integral_congr_ae (hyw.symm.mono fun _ hz ↦ by dsimp only; rw [hz])
        _ = ∫ z, ⟪f z, η z⟫ := hweak η φ.contDiff φ.hasCompactSupport
        _ = ∫ z, ⟪η z, f z⟫ :=
            integral_congr_ae (.of_forall fun _ ↦ real_inner_comm _ _)
  have hae : gaugeFixedOperator x w =ᵐ[volume] f := by
    simpa only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using hae_top
  exact ⟨w, hw, hyw, hw_sob, hw_lim, congrFun ((hLw_cont.ae_eq_iff_eq volume hfc).1 hae)⟩

/-- **Regularity of classical `C¹` kernel elements.** At a smooth field `x` whose coordinates have
bounded derivatives of all orders, every `C¹` square-integrable solution of `L_x y = 0` is smooth,
lies in `sobolevFields s` for every `s : ℝ`, and tends to zero at infinity. -/
theorem contDiff_and_mem_sobolevFields_of_gaugeFixedOperator_eq_zero
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : ContDiff ℝ 1 y) (hy₂ : MemLp y 2 volume) (hker : ∀ z, gaugeFixedOperator x y z = 0) :
    ContDiff ℝ ∞ y ∧ (∀ s : ℝ, y ∈ sobolevFields s) ∧ Tendsto y (cocompact ℂ) (𝓝 0) := by
  obtain ⟨w, hw, hyw, hw_sob, hw_lim, -⟩ :=
    exists_contDiff_ae_eq_and_gaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq hx
      hbound hy₂ (f := 0) (fun _ ↦ zero_mem _) continuous_const fun η hη hηc ↦ by
        rw [integral_inner_gaugeFixedAdjoint hx.continuous hy (hη.of_le (by simp)) hηc]
        simp [hker]
  have hy_eq : y = w := (hy.continuous.ae_eq_iff_eq volume hw.continuous).1 hyw
  exact hy_eq ▸ ⟨hw, hw_sob, hw_lim⟩

/-- At a smooth field `x` with bounded derivatives of all orders, every element of
`gaugeFixedKernel x` lies in `sobolevFields s` for every `s : ℝ`. -/
theorem mem_sobolevFields_of_mem_gaugeFixedKernel {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : y ∈ gaugeFixedKernel x) (s : ℝ) :
    y ∈ sobolevFields s := by
  obtain ⟨hyc, hy₂, hker⟩ := mem_gaugeFixedKernel.1 hy
  exact (contDiff_and_mem_sobolevFields_of_gaugeFixedOperator_eq_zero hx hbound
    (hyc.of_le one_le_two) hy₂ hker).2.1 s

/-- The weak `L²` kernel of the gauge-fixed operator `L_x`: those `u ∈ L²(ℂ; ℝ⁴)` whose pairing
with `L_x* η` is integrable and has zero integral for every smooth compactly supported test field
`η`. When `x` is continuous, `L_x* η` is continuous with compact support so the integrability
condition is automatic (`mem_weakGaugeFixedKernel_iff`). -/
def weakGaugeFixedKernel (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) where
  carrier := {u | ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
    Integrable (fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫) volume ∧
      ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0}
  add_mem' {u v} hu hv η hη hηc := by
    have hae : (fun z ↦ ⟪(u + v : Lp _ 2 _) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
        fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫ + ⟪v z, gaugeFixedAdjoint x η z⟫ :=
      (Lp.coeFn_add u v).mono fun z hz ↦ by dsimp only; rw [hz, Pi.add_apply, inner_add_left]
    refine ⟨((hu η hη hηc).1.add (hv η hη hηc).1).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_add (hu η hη hηc).1 (hv η hη hηc).1,
      (hu η hη hηc).2, (hv η hη hηc).2, add_zero]
  zero_mem' η _ _ := by
    have hae : (fun z ↦ ⟪(0 : Lp _ 2 _) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume] fun _ ↦ 0 :=
      (Lp.coeFn_zero _ 2 _).mono fun z hz ↦ by dsimp only; rw [hz, Pi.zero_apply, inner_zero_left]
    exact ⟨(integrable_zero _ _ _).congr hae.symm,
      (integral_congr_ae hae).trans (integral_zero _ _)⟩
  smul_mem' c {u} hu η hη hηc := by
    have hae : (fun z ↦ ⟪(c • u : Lp _ 2 _) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
        fun z ↦ c * ⟪u z, gaugeFixedAdjoint x η z⟫ :=
      (Lp.coeFn_smul c u).mono fun z hz ↦ by simp [hz, inner_smul_left]
    refine ⟨((hu η hη hηc).1.const_mul c).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_const_mul, (hu η hη hηc).2, mul_zero]

@[simp]
theorem mem_weakGaugeFixedKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        Integrable (fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫) volume ∧
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 :=
  Iff.rfl

/-- For a continuous field `x`, `u ∈ L²` lies in `weakGaugeFixedKernel x` if and only if
`∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly supported test field `η`. -/
theorem mem_weakGaugeFixedKernel_iff {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  refine ⟨fun hu η hη hηc ↦ (hu η hη hηc).2, fun hu η hη hηc ↦ ⟨?_, hu η hη hηc⟩⟩
  have hL : MemLp (gaugeFixedAdjoint x η) 2 volume :=
    (continuous_gaugeFixedAdjoint hx (hη.of_le (by simp))).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  exact (Lp.memLp u).integrable_inner hL

/-- For a continuous field `x`, the `L²` class of every classical kernel element lies in the weak
`L²` kernel. -/
theorem gaugeFixedKernelToLp_mem_weakGaugeFixedKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) (y : gaugeFixedKernel x) :
    gaugeFixedKernelToLp x y ∈ weakGaugeFixedKernel x := by
  rw [mem_weakGaugeFixedKernel_iff hx]
  intro η hη hηc
  obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 y.2
  have hae : (fun z ↦ ⟪gaugeFixedKernelToLp x y z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
      fun z ↦ ⟪(y : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ :=
    (coeFn_gaugeFixedKernelToLp y).mono fun z hz ↦ by dsimp only; rw [hz]
  rw [integral_congr_ae hae,
    integral_inner_gaugeFixedAdjoint hx (hyc.of_le one_le_two) (hη.of_le (by simp)) hηc]
  simp [hker]

/-- **Equivalence of the classical and weak `L²` kernels of `L_x`.** At any smooth field `x` whose
coordinates have bounded derivatives of all orders, passing to `L²` classes identifies
`gaugeFixedKernel x` linearly with `weakGaugeFixedKernel x`. -/
def gaugeFixedKernelEquivWeak {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel x :=
  LinearEquiv.ofBijective
    ((gaugeFixedKernelToLp x).codRestrict (weakGaugeFixedKernel x)
      (gaugeFixedKernelToLp_mem_weakGaugeFixedKernel hx.continuous))
    ⟨fun y₁ y₂ h ↦ gaugeFixedKernelToLp_injective x (congrArg Subtype.val h), fun ⟨u, hu⟩ ↦ by
      obtain ⟨w, hw, huw, hw_sob, -, hker⟩ :=
        exists_contDiff_ae_eq_and_gaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq hx
          hbound (Lp.memLp u) (f := 0) (fun _ ↦ zero_mem _) continuous_const fun η hη hηc ↦ by
            simpa using (hu η hη hηc).2
      have hwK : w ∈ gaugeFixedKernel x :=
        mem_gaugeFixedKernel.2 ⟨hw.of_le (by simp), memLp_of_mem_sobolevFields (hw_sob 0), hker⟩
      refine ⟨⟨w, hwK⟩, Subtype.ext (Lp.ext_iff.2 ?_)⟩
      exact (coeFn_gaugeFixedKernelToLp ⟨w, hwK⟩).trans huw.symm⟩

@[simp]
theorem coe_gaugeFixedKernelEquivWeak {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    (gaugeFixedKernelEquivWeak hx hbound y : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) =
      gaugeFixedKernelToLp x y := (rfl)

/-- At a smooth field `x` with bounded derivatives of all orders, testing against `C^k` compactly
supported fields for any `1 ≤ k ≤ ∞` (in particular `k = 1`, `k = 2`, or `k = ∞`) cuts out the
same weak `L²` kernel. -/
theorem mem_weakGaugeFixedKernel_iff_forall_contDiff {k : ℕ∞ω} (hk : 1 ≤ k) (hk' : k ≤ ∞)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel x ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ k η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  refine ⟨fun hu η hη hηc ↦ ?_, fun hu ↦ (mem_weakGaugeFixedKernel_iff hx.continuous).2
    fun η hη hηc ↦ hu η (hη.of_le hk') hηc⟩
  set y : gaugeFixedKernel x := (gaugeFixedKernelEquivWeak hx hbound).symm ⟨u, hu⟩
  have huy : u = gaugeFixedKernelToLp x y := by
    rw [← coe_gaugeFixedKernelEquivWeak hx hbound y]
    exact congrArg Subtype.val ((gaugeFixedKernelEquivWeak hx hbound).apply_symm_apply ⟨u, hu⟩).symm
  obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 y.2
  have hae : (fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
      fun z ↦ ⟪(y : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ := by
    rw [huy]
    exact (coeFn_gaugeFixedKernelToLp y).mono fun z hz ↦ by dsimp only; rw [hz]
  rw [integral_congr_ae hae,
    integral_inner_gaugeFixedAdjoint hx.continuous (hyc.of_le one_le_two) (hη.of_le hk) hηc]
  simp [hker]

/-- **Finite-dimensionality of the weak `L²` kernel.** At a smooth field `x` with bounded
derivatives of all orders, `∂bar_a α = 0`, `|α|² → 1` at infinity, and zero divisor `D`, the weak
`L²` kernel `weakGaugeFixedKernel x` is finite-dimensional. -/
theorem finiteDimensional_weakGaugeFixedKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    FiniteDimensional ℝ (weakGaugeFixedKernel x) := by
  have : FiniteDimensional ℝ (gaugeFixedKernel x) :=
    finiteDimensional_of_gaugeFixedOperator_eq_zero (hx.of_le (by simp)) hhol hlim hD
      fun _ hy ↦ mem_gaugeFixedKernel.1 hy
  exact (gaugeFixedKernelEquivWeak hx hbound).finiteDimensional

/-- **The weak `L²` kernel of `L_x` has real dimension `2 |D|`.** -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_card {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {D : Multiset ℂ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * Multiset.card D :=
  (gaugeFixedKernelEquivWeak hx hbound).symm.finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD)

/-- **The weak `L²` kernel of `L_x` at a framed degree-`m` field has real dimension `2 m`.** -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1)) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m :=
  (gaugeFixedKernelEquivWeak hx hbound).symm.finrank_eq.trans
    (finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe)

/-! ### Fields of `A_m^s` and plane vortices -/

/-- **Weak solutions at a field of `A_m^s` lie in `H¹`.** Let `x` be a continuous field of the
affine space `A_m^s`, `s > 1`, and `g ∈ L²(ℂ; ℝ⁴)`. Every `L²` weak solution of `L_x y = g` lies
in `H¹`; in particular the weak kernel of `L_x` lies in `H¹`. -/
theorem mem_sobolevFields_one_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ}
    (hs : 1 < s) {x y g : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s)
    (hcont : Continuous x) (hy : MemLp y 2 volume) (hg : MemLp g 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields 1 :=
  let ⟨_, hC⟩ := exists_norm_le_of_mem_framedFieldSpace hs hx hcont
  mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq hcont.aestronglyMeasurable
    (ae_of_all _ hC) hy hg hweak

/-- **The weak right inverse at a plane vortex takes values in `H¹`.** Let `x` be a `C¹` solution
of the plane vortex equation in the affine space `A_m^s`, `s > 1`. Then there is a bounded
operator `Q` on `L²(ℂ; ℝ⁴)` such that, for every `g ∈ L²`, `Q g` is a weak solution of
`L_x y = g`, orthogonal to the weak kernel of `L_x`, and lies in `H¹`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hx₁ : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      (∀ g η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q g z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) ∧
      (∀ g u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0) →
        ∫ z, ⟪Q g z, u z⟫ = 0) ∧
      ∀ g, (Q g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields 1 := by
  obtain ⟨Q, hQ, hQK⟩ := exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq
    (μ := volume) hx₁ hsol (tendsto_normSq_of_mem_framedFieldSpace hs hx hx₁.continuous)
  exact ⟨Q, hQ, hQK, fun g ↦ mem_sobolevFields_one_of_mem_framedFieldSpace hs hx hx₁.continuous
    (Lp.memLp _) (Lp.memLp g) fun η hη hc ↦ hQ g η (hη.of_le (by simp)) hc⟩

/-- A continuous field lying in `framedFieldSpace f m k` for every `k : ℕ` is smooth and has
bounded iterated derivatives of all orders. -/
theorem contDiff_and_exists_norm_iteratedFDeriv_apply_le_of_forall_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hcont : Continuous x) :
    ContDiff ℝ ∞ x ∧
      ∀ i : Fin 4, ∀ n : ℕ, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C := by
  obtain ⟨w, hw, hyw, -, hw_bdd, -⟩ :=
    exists_contDiff_ae_eq_of_forall_mem_sobolevFields fun k ↦ mem_framedFieldSpace.1 (hx k)
  have href : ContDiff ℝ ∞ (referenceField f m) := contDiff_referenceField f m
  have hy_eq : x - referenceField f m = w :=
    ((hcont.sub href.continuous).ae_eq_iff_eq volume hw.continuous).1 hyw
  have hx_eq : x = w + referenceField f m := by
    rw [← hy_eq, sub_add_cancel]
  refine ⟨hx_eq ▸ hw.add href, fun i n ↦ ?_⟩
  obtain ⟨C₁, hC₁⟩ := hw_bdd i n
  obtain ⟨C₂, hC₂⟩ := exists_norm_iteratedFDeriv_referenceField_apply_le f m i n
  have hwi : ContDiff ℝ ∞ fun z ↦ w z i := contDiff_euclidean.1 hw i
  have hri : ContDiff ℝ ∞ fun z ↦ referenceField f m z i := contDiff_euclidean.1 href i
  refine ⟨C₁ + C₂, fun z ↦ ?_⟩
  have hcoord : (fun z ↦ x z i) = (fun z ↦ w z i) + fun z ↦ referenceField f m z i := by
    funext z
    simp [hx_eq]
  rw [hcoord, iteratedFDeriv_add_apply (hwi.contDiffAt.of_le (by exact_mod_cast le_top))
    (hri.contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add (hC₁ z) (hC₂ z))

/-- **The kernel of `L_x` at a smooth field in `A_m^s` (`s > 1`) has real dimension `2 m`.** -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul hxs hhol
    (tendsto_sectionValue_mul_inv_pow hs hx hxs.continuous)

/-- **The weak `L²` kernel of `L_x` at a field in every `A_m^k` has real dimension `2 m`.** -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_forall_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ∀ k : ℕ, x ∈ framedFieldSpace f m k) (hcont : Continuous x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m := by
  obtain ⟨hxs, hbound⟩ :=
    contDiff_and_exists_norm_iteratedFDeriv_apply_le_of_forall_mem_framedFieldSpace hx hcont
  exact finrank_weakGaugeFixedKernel_eq_two_mul hxs hbound hhol
    (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hx 2) hcont)

/-- **The classical kernel of `L_x` at a `C¹` gauge-fixed vortex in `A_m^k` (`k ≥ 2`) has real
dimension `2 m`.** By the elliptic bootstrap (`contDiff_of_equation_eq_zero`), `x` is smooth. -/
theorem finrank_gaugeFixedKernel_eq_two_mul_of_equation_eq_zero
    {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (gaugeFixedKernel x) = 2 * m :=
  finrank_gaugeFixedKernel_eq_two_mul_of_mem_framedFieldSpace (by exact_mod_cast hk) hx
    (contDiff_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge)
    fun w ↦ ⟨by simp [heq w], by simp [heq w]⟩

/-- **The weak `L²` kernel of `L_x` at a `C¹` gauge-fixed vortex in `A_m^k` (`k ≥ 2`) has real
dimension `2 m`.** By the elliptic bootstrap (`mem_framedFieldSpace_of_equation_eq_zero`), `x` lies
in every `A_m^j` and is smooth with bounded derivatives of all orders. -/
theorem finrank_weakGaugeFixedKernel_eq_two_mul_of_equation_eq_zero
    {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (hk : 1 < k) {x₀ x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx₀ : ∀ j : ℕ, x₀ ∈ framedFieldSpace f m j) (hx₀c : ContDiff ℝ 1 x₀)
    (hx : x ∈ framedFieldSpace f m k) (hxc : ContDiff ℝ 1 x) (heq : ∀ z, equation x z = 0)
    (hgauge : ∀ z, gaugeAdjoint x₀ (x - x₀) z = 0) :
    Module.finrank ℝ (weakGaugeFixedKernel x) = 2 * m :=
  finrank_weakGaugeFixedKernel_eq_two_mul_of_forall_mem_framedFieldSpace
    (mem_framedFieldSpace_of_equation_eq_zero hk hx₀ hx₀c hx hxc heq hgauge) hxc.continuous
    fun w ↦ ⟨by simp [heq w], by simp [heq w]⟩

end TauCeti.Vortex
