/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Sobolev
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.PDE.Vortex.Multiplier

/-!
# Elliptic regularity of the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴` with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a weak solution of `L_x y = f` if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for
every smooth compactly supported test field `η`; this is the notion of solution produced by the
weak right inverse of `TauCeti.Analysis.PDE.Vortex.RightInverse`. This file shows that weak
solutions gain one derivative, measured on the Sobolev scale `sobolevFields s` of the framed field
space, and identifies the distributional `L²` kernel `weakGaugeFixedKernel` with the classical
kernel `gaugeFixedKernel x` when `x` is smooth with bounded derivatives.

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
* `exists_contDiff_ae_eq_and_gaugeFixedOperator_eq` and
  `exists_mem_sobolevFields_add_one_gaugeFixedOperator_eq`: for `k ≥ 2` and continuous `f ∈ H^k`,
  Sobolev embedding into `C^(k-1)` and integration by parts turn weak solutions into classical
  solutions of `L_x y₀ = f` in `H^(k+1)`, giving classical Sobolev solvability at a vortex.
* `weakGaugeFixedKernel` and `gaugeFixedKernelEquivWeak`: when `x` is smooth with bounded
  derivatives of all orders (for instance, a continuous field lying in every `A_m^j`), every
  element of the weak `L²` kernel agrees almost everywhere with a unique smooth element of
  `gaugeFixedKernel x` lying in every `sobolevFields s`.
* `mem_sobolevFields_one_of_mem_framedFieldSpace` and
  `exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_and_mem_sobolevFields`:
  regularity of weak solutions and of the weak right inverse `Q` at fields of `A_m^s`, `s > 1`.

These are regularity and classical-solvability statements. The dimension of the kernel is treated
in `TauCeti.Analysis.PDE.Vortex.KernelDimension`; the Fredholm property between completed Sobolev
spaces is not treated here.

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

/-- **Smooth elliptic bootstrap.** If `x` is smooth with bounded derivatives of all orders and `f`
lies in `H^k` for every natural `k`, then every `L²` weak solution of `L_x y = f` lies in
`sobolevFields s` for every real `s`. -/
theorem mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) (s : ℝ) :
    y ∈ sobolevFields s :=
  sobolevFields_mono (s := (⌈s⌉₊ : ℝ) + 1) (by linarith [Nat.le_ceil s])
    (mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq
      (⌈s⌉₊) hx (fun i n _ ↦ hbound i n) hy (hf ⌈s⌉₊) hweak)

/-- **Weak solutions of class `C¹` are classical solutions.** If `x` and `f` are continuous and
`y` is a `C¹` field satisfying `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every smooth compactly supported
test field `η`, then `L_x y = f` everywhere on `ℂ`. -/
theorem gaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) (hy : ContDiff ℝ 1 y)
    (hf : Continuous f)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) (z : ℂ) :
    gaugeFixedOperator x y z = f z := by
  have hLy : Continuous (gaugeFixedOperator x y) := continuous_gaugeFixedOperator hx hy
  have hae : gaugeFixedOperator x y =ᵐ[volume.restrict (⊤ : TopologicalSpace.Opens ℂ)] f :=
    TauCeti.ae_eq_of_forall_integral_inner_eq
      ((hLy.locallyIntegrable (μ := volume)).locallyIntegrableOn _)
      ((hf.locallyIntegrable (μ := volume)).locallyIntegrableOn _) fun φ ↦ by
        have h := integral_inner_gaugeFixedAdjoint (μ := volume) hx hy
          (φ.contDiff.of_le (mod_cast le_top)) φ.hasCompactSupport
        rw [hweak φ φ.contDiff φ.hasCompactSupport] at h
        simpa only [real_inner_comm] using h.symm
  rw [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hae
  exact congrFun ((hLy.ae_eq_iff_eq volume hf).1 hae) z

/-- **Classical regularity of weak solutions in `H^k`.** Let `k ≥ 2`, let `x` be a smooth field
whose coordinates have bounded derivatives through order `k`, and let `f` be a continuous field in
`H^k`. Every `L²` weak solution `y` of `L_x y = f` agrees almost everywhere with a `C^(k-1)` field
`y₀ ∈ H^(k+1)` satisfying `L_x y₀ = f` everywhere. -/
theorem exists_contDiff_ae_eq_and_gaugeFixedOperator_eq {k : ℕ} (hk : 1 < k)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : f ∈ sobolevFields k) (hfc : Continuous f)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∃ y₀ ∈ sobolevFields (k + 1), ContDiff ℝ (k - 1) y₀ ∧ y =ᵐ[volume] y₀ ∧
      ∀ z, gaugeFixedOperator x y₀ z = f z := by
  have hyS : y ∈ sobolevFields (k + 1) := by
    exact_mod_cast mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq k hx
      hbound hy hf hweak
  obtain ⟨y₀, hy₀S, hy₀c, hae⟩ := exists_contDiff_ae_eq_of_mem_sobolevFields (k := k - 1)
    (by push_cast [Nat.le_of_lt hk]; linarith) hyS
  have hy₀1 : ContDiff ℝ 1 y₀ := hy₀c.of_le (by norm_cast; omega)
  refine ⟨y₀, hy₀S, hy₀c, hae, gaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    hx.continuous hy₀1 hfc fun η hη hc ↦ ?_⟩
  rw [← hweak η hη hc]
  exact integral_congr_ae (hae.symm.mono fun z hz ↦ by simp only [hz])

/-- **Smooth classical representative of a weak solution.** If `x` is smooth with bounded
derivatives of all orders and `f` is a continuous field lying in `H^k` for every natural `k`, then
every `L²` weak solution `y` of `L_x y = f` agrees almost everywhere with a smooth field `y₀` lying
in every `sobolevFields s` and solving `L_x y₀ = f` everywhere. -/
theorem exists_contDiff_infty_ae_eq_and_gaugeFixedOperator_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : ∀ k : ℕ, f ∈ sobolevFields k) (hfc : Continuous f)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∃ y₀, (∀ s : ℝ, y₀ ∈ sobolevFields s) ∧ ContDiff ℝ ∞ y₀ ∧ y =ᵐ[volume] y₀ ∧
      ∀ z, gaugeFixedOperator x y₀ z = f z := by
  obtain ⟨y₀, hy₀s, hy₀c, hae⟩ := exists_contDiff_ae_eq_of_forall_mem_sobolevFields fun k ↦
    mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq hx hbound hy hf hweak k
  refine ⟨y₀, hy₀s, hy₀c, hae, gaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    hx.continuous (hy₀c.of_le (by simp)) hfc fun η hη hc ↦ ?_⟩
  rw [← hweak η hη hc]
  exact integral_congr_ae (hae.symm.mono fun z hz ↦ by simp only [hz])

/-- **Classical Sobolev solvability of `L_x` at a plane vortex.** Let `k ≥ 2`, and let `x` be a
smooth solution of the plane vortex equation with `|α| → 1` at infinity whose coordinates have
bounded derivatives through order `k`. For every continuous `f ∈ H^k(ℂ; ℝ⁴)` there is a `C^(k-1)`
field `y ∈ H^(k+1)(ℂ; ℝ⁴)` solving `L_x y = f` everywhere on `ℂ` and `L²`-orthogonal to
`gaugeFixedKernel x`. -/
theorem exists_mem_sobolevFields_add_one_gaugeFixedOperator_eq {k : ℕ} (hk : 1 < k)
    {x f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hf : f ∈ sobolevFields k) (hfc : Continuous f) :
    ∃ y ∈ sobolevFields (k + 1), ContDiff ℝ (k - 1) y ∧
      (∀ z, gaugeFixedOperator x y z = f z) ∧
      ∀ u ∈ gaugeFixedKernel x, ∫ z, ⟪y z, u z⟫ = 0 := by
  have hfL := memLp_of_mem_sobolevFields hf
  obtain ⟨Q, hQ, hQK⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := volume)
      (hx.of_le (by simp)) hsol hlim
  obtain ⟨y, hyS, hyc, hae, hLy⟩ := exists_contDiff_ae_eq_and_gaugeFixedOperator_eq hk hx hbound
    (Lp.memLp (Q (hfL.toLp f))) hf hfc fun η hη hc ↦ by
      rw [hQ _ η (hη.of_le (by simp)) hc]
      exact integral_congr_ae (hfL.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
  refine ⟨y, hyS, hyc, hLy, fun u hu ↦ ?_⟩
  obtain ⟨huc, huL, huk⟩ := mem_gaugeFixedKernel.1 hu
  have horth : ∫ z, ⟪Q (hfL.toLp f) z, (huL.toLp u) z⟫ = 0 :=
    hQK (hfL.toLp f) (huL.toLp u) fun η hη hc ↦ by
      calc ∫ z, ⟪(huL.toLp u) z, gaugeFixedAdjoint x η z⟫
          = ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ :=
            integral_congr_ae (huL.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
        _ = ∫ z, ⟪gaugeFixedOperator x u z, η z⟫ :=
            integral_inner_gaugeFixedAdjoint hx.continuous (huc.of_le one_le_two)
              (hη.of_le one_le_two) hc
        _ = 0 := by simp [huk]
  rw [← horth]
  exact integral_congr_ae (hae.symm.mp (huL.coeFn_toLp.mono fun z h₁ h₂ ↦ by simp only [h₁, h₂]))

/-! ### The weak kernel -/

/-- The distributional weak kernel of `L_x` in `L²(ℂ; ℝ⁴)` at a continuous field `x`: the
square-integrable fields `u` satisfying `∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly supported
test field `η`. -/
def weakGaugeFixedKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) :
    Submodule ℝ (Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) where
  carrier := {u | ∀ η : ℂ → EuclideanSpace ℝ (Fin 4),
    ContDiff ℝ ∞ η → HasCompactSupport η → ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0}
  add_mem' {u v} hu hv η hη hc := by
    have hL : MemLp (gaugeFixedAdjoint x η) 2 volume :=
      (continuous_gaugeFixedAdjoint hx (hη.of_le (mod_cast le_top))).memLp_of_hasCompactSupport
        (hasCompactSupport_gaugeFixedAdjoint hc)
    have hae : (fun z ↦ ⟪(u + v) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
        fun z ↦ ⟪u z, gaugeFixedAdjoint x η z⟫ + ⟪v z, gaugeFixedAdjoint x η z⟫ :=
      (Lp.coeFn_add u v).mono fun z hz ↦ by dsimp only; rw [hz, Pi.add_apply, inner_add_left]
    rw [integral_congr_ae hae, integral_add ((Lp.memLp u).integrable_inner hL)
      ((Lp.memLp v).integrable_inner hL), hu η hη hc, hv η hη hc, add_zero]
  zero_mem' η _ _ := by
    have hae : (fun z ↦ ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) z,
        gaugeFixedAdjoint x η z⟫) =ᵐ[volume] fun _ ↦ 0 :=
      (Lp.coeFn_zero _ _ _).mono fun z hz ↦ by dsimp only; rw [hz, Pi.zero_apply, inner_zero_left]
    rw [integral_congr_ae hae, integral_zero]
  smul_mem' c u hu η hη hc := by
    have hae : (fun z ↦ ⟪(c • u) z, gaugeFixedAdjoint x η z⟫) =ᵐ[volume]
        fun z ↦ c * ⟪u z, gaugeFixedAdjoint x η z⟫ :=
      (Lp.coeFn_smul c u).mono fun z hz ↦ by
        dsimp only; rw [hz, Pi.smul_apply, real_inner_smul_left]
    rw [integral_congr_ae hae, integral_const_mul, hu η hη hc, mul_zero]

/-- An `L²` field belongs to `weakGaugeFixedKernel hx` iff it pairs to zero with `L_x* η` for every
smooth compactly supported test field `η`. -/
@[simp]
theorem mem_weakGaugeFixedKernel {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel hx ↔ ∀ η : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ η → HasCompactSupport η → ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 :=
  Iff.rfl

/-- At a continuous field `x`, sending a classical `C²` kernel element to its `L²` class embeds
`gaugeFixedKernel x` into `weakGaugeFixedKernel hx`. -/
def gaugeFixedKernelToWeak {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) :
    gaugeFixedKernel x →ₗ[ℝ] weakGaugeFixedKernel hx where
  toFun y := ⟨(mem_gaugeFixedKernel.1 y.2).2.1.toLp y, fun η hη hc ↦ by
    obtain ⟨hyc, hyL, hyk⟩ := mem_gaugeFixedKernel.1 y.2
    calc ∫ z, ⟪(hyL.toLp (y : ℂ → EuclideanSpace ℝ (Fin 4))) z, gaugeFixedAdjoint x η z⟫
        = ∫ z, ⟪(y : ℂ → EuclideanSpace ℝ (Fin 4)) z, gaugeFixedAdjoint x η z⟫ :=
          integral_congr_ae (hyL.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
      _ = ∫ z, ⟪gaugeFixedOperator x y z, η z⟫ :=
          integral_inner_gaugeFixedAdjoint hx (hyc.of_le one_le_two)
            (hη.of_le (mod_cast le_top)) hc
      _ = 0 := by simp [hyk]⟩
  map_add' y v := Subtype.ext <| by
    simp only [Submodule.coe_add]
    rw [← MemLp.toLp_add]
  map_smul' c y := Subtype.ext <| by
    simp only [RingHom.id_apply, Submodule.coe_smul_of_tower]
    rw [← MemLp.toLp_const_smul]

/-- The underlying `L²` class of `gaugeFixedKernelToWeak hx y` is `toLp y`. -/
@[simp]
theorem coe_gaugeFixedKernelToWeak {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x)
    (y : gaugeFixedKernel x) :
    (gaugeFixedKernelToWeak hx y : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)) =
      (mem_gaugeFixedKernel.1 y.2).2.1.toLp y := (rfl)

/-- Sending a classical kernel element to its `L²` class is injective, by continuity. -/
theorem gaugeFixedKernelToWeak_injective {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x) :
    Function.Injective (gaugeFixedKernelToWeak hx) := fun y v h ↦ by
  have hLp := congrArg Subtype.val h
  simp only [coe_gaugeFixedKernelToWeak] at hLp
  have hae := (mem_gaugeFixedKernel.1 y.2).2.1.coeFn_toLp.symm.trans
    ((Lp.ext_iff.1 hLp).trans (mem_gaugeFixedKernel.1 v.2).2.1.coeFn_toLp)
  exact Subtype.ext (((mem_gaugeFixedKernel.1 y.2).1.continuous.ae_eq_iff_eq volume
    (mem_gaugeFixedKernel.1 v.2).1.continuous).1 hae)

/-- **Elliptic regularity of `C¹` `L²` kernel elements.** When `x` is smooth with bounded
derivatives of all orders, every `C¹` square-integrable solution of `L_x y = 0` is smooth and lies
in `sobolevFields s` for every real `s`. -/
theorem contDiff_and_mem_sobolevFields_of_gaugeFixedOperator_eq_zero
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : ContDiff ℝ 1 y) (hyL : MemLp y 2 volume)
    (hker : ∀ z, gaugeFixedOperator x y z = 0) :
    ContDiff ℝ ∞ y ∧ ∀ s : ℝ, y ∈ sobolevFields s := by
  have hyS (s : ℝ) : y ∈ sobolevFields s :=
    mem_sobolevFields_of_integral_inner_gaugeFixedAdjoint_eq (f := 0) hx hbound hyL
      (fun k ↦ zero_mem _) (fun η hη hc ↦ by
        rw [integral_inner_gaugeFixedAdjoint hx.continuous hy (hη.of_le (mod_cast le_top)) hc]
        simp [hker]) s
  exact ⟨contDiff_infty.2 fun k ↦ contDiff_of_mem_sobolevFields (s := ((k + 2 : ℕ) : ℝ))
    (by push_cast; linarith) (hyS _) hy.continuous, hyS⟩

/-- **The classical and weak `L²` kernels of `L_x` agree.** When `x` is smooth with bounded
derivatives of all orders, sending a classical kernel element to its `L²` class is a real-linear
equivalence between `gaugeFixedKernel x` and `weakGaugeFixedKernel hx.continuous`. -/
def gaugeFixedKernelEquivWeak {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel hx.continuous :=
  LinearEquiv.ofBijective (gaugeFixedKernelToWeak hx.continuous)
    ⟨gaugeFixedKernelToWeak_injective hx.continuous, fun u ↦ by
      obtain ⟨y₀, hy₀s, hy₀c, hae, hLy₀⟩ := exists_contDiff_infty_ae_eq_and_gaugeFixedOperator_eq
        (f := 0) hx hbound (Lp.memLp u.1) (fun _ ↦ zero_mem _) continuous_zero fun η hη hc ↦ by
          simpa using u.2 η hη hc
      have hy₀L : MemLp y₀ 2 volume := memLp_of_mem_sobolevFields (hy₀s 0)
      have hy₀k : y₀ ∈ gaugeFixedKernel x :=
        mem_gaugeFixedKernel.2 ⟨hy₀c.of_le (by simp), hy₀L, hLy₀⟩
      refine ⟨⟨y₀, hy₀k⟩, Subtype.ext (Lp.ext ?_)⟩
      rw [coe_gaugeFixedKernelToWeak]
      exact (mem_gaugeFixedKernel.1 hy₀k).2.1.coeFn_toLp.trans hae.symm⟩

/-- `gaugeFixedKernelEquivWeak` acts as `gaugeFixedKernelToWeak`. -/
@[simp]
theorem gaugeFixedKernelEquivWeak_apply {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (y : gaugeFixedKernel x) :
    gaugeFixedKernelEquivWeak hx hbound y = gaugeFixedKernelToWeak hx.continuous y := (rfl)

/-- When `x` is smooth with bounded derivatives of all orders, testing against `C^k` compactly
supported fields gives the same weak kernel for every `k ≥ 1`. -/
theorem mem_weakGaugeFixedKernel_iff_contDiff {k : ℕ∞} (hk : 1 ≤ k)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i n, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ)} :
    u ∈ weakGaugeFixedKernel hx.continuous ↔ ∀ η : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ k η → HasCompactSupport η → ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  refine ⟨fun hu η hη hc ↦ ?_, fun hu η hη hc ↦ hu η (hη.of_le (mod_cast le_top)) hc⟩
  obtain ⟨y, hy⟩ := (gaugeFixedKernelEquivWeak hx hbound).surjective ⟨u, hu⟩
  have hLp := congrArg Subtype.val hy
  simp only [gaugeFixedKernelEquivWeak_apply, coe_gaugeFixedKernelToWeak] at hLp
  obtain ⟨hyc, hyL, hyk⟩ := mem_gaugeFixedKernel.1 y.2
  have hae : u =ᵐ[volume] (y : ℂ → _) := hLp ▸ hyL.coeFn_toLp
  calc ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫
      = ∫ z, ⟪(y : ℂ → _) z, gaugeFixedAdjoint x η z⟫ :=
        integral_congr_ae (hae.mono fun z hz ↦ by simp only [hz])
    _ = ∫ z, ⟪gaugeFixedOperator x y z, η z⟫ :=
        integral_inner_gaugeFixedAdjoint hx.continuous (hyc.of_le one_le_two)
          (hη.of_le (mod_cast hk)) hc
    _ = 0 := by simp [hyk]

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

/-- **Classical Sobolev solvability of `L_x` at a vortex in `⋂_j A_m^j`.** For `k ≥ 2`, a
continuous solution `x` of the plane vortex equation lying in `framedFieldSpace f m j` for every
`j`, and any continuous `g ∈ H^k`, there is a `C^(k-1)` field `y ∈ H^(k+1)` solving `L_x y = g`
everywhere on `ℂ` and `L²`-orthogonal to `gaugeFixedKernel x`. -/
theorem exists_mem_sobolevFields_add_one_gaugeFixedOperator_eq_of_forall_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m k : ℕ} (hk : 1 < k) {x g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j) (hcont : Continuous x)
    (hsol : ∀ z, equation x z = 0) (hg : g ∈ sobolevFields k) (hgc : Continuous g) :
    ∃ y ∈ sobolevFields (k + 1), ContDiff ℝ (k - 1) y ∧
      (∀ z, gaugeFixedOperator x y z = g z) ∧
      ∀ u ∈ gaugeFixedKernel x, ∫ z, ⟪y z, u z⟫ = 0 :=
  exists_mem_sobolevFields_add_one_gaugeFixedOperator_eq hk
    (contDiff_infty.2 fun j ↦ contDiff_of_mem_framedFieldSpace (s := ((j + 2 : ℕ) : ℝ))
      (by push_cast; linarith) (hx (j + 2)) hcont)
    (fun i n hn ↦ exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace (k := k)
      (s := ((k + 2 : ℕ) : ℝ)) (by push_cast; linarith) (hx (k + 2)) hcont i hn)
    hsol (tendsto_normSq_of_mem_framedFieldSpace (s := 2) one_lt_two (hx 2) hcont) hg hgc

/-- **The classical and weak `L²` kernels agree for smooth fields of `⋂_j A_m^j`.** For a
continuous field `x` lying in `framedFieldSpace f m j` for every natural `j` (for instance, a
Coulomb-slice vortex by `mem_framedFieldSpace_of_equation_eq_zero`), `gaugeFixedKernel x` is
real-linearly isomorphic to `weakGaugeFixedKernel hcont`. -/
def gaugeFixedKernelEquivWeakOfForallMemFramedFieldSpace {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j)
    (hcont : Continuous x) :
    gaugeFixedKernel x ≃ₗ[ℝ] weakGaugeFixedKernel hcont :=
  gaugeFixedKernelEquivWeak
    (contDiff_infty.2 fun k ↦ contDiff_of_mem_framedFieldSpace (s := ((k + 2 : ℕ) : ℝ))
      (by push_cast; linarith) (hx (k + 2)) hcont)
    fun i n ↦ exists_norm_iteratedFDeriv_apply_le_of_mem_framedFieldSpace (k := n)
      (s := ((n + 2 : ℕ) : ℝ)) (by push_cast; linarith) (hx (n + 2)) hcont i le_rfl

/-- `gaugeFixedKernelEquivWeakOfForallMemFramedFieldSpace` acts as `gaugeFixedKernelToWeak`. -/
@[simp]
theorem gaugeFixedKernelEquivWeakOfForallMemFramedFieldSpace_apply {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ∀ j : ℕ, x ∈ framedFieldSpace f m j)
    (hcont : Continuous x) (y : gaugeFixedKernel x) :
    gaugeFixedKernelEquivWeakOfForallMemFramedFieldSpace hx hcont y =
      gaugeFixedKernelToWeak hcont y := (rfl)

end TauCeti.Vortex
