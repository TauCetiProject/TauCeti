/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.VacuumOperator.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.Sobolev.BesselPotential.Multiplier

/-!
# Elliptic regularity of the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴` with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a weak solution of `L_x y = f` if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for
every smooth compactly supported test field `η`; this is the notion of solution produced by the
weak right inverse of `TauCeti.Analysis.PDE.Vortex.RightInverse`. This file shows that weak
solutions gain one derivative, measured on the Sobolev scale `sobolevFields s` of the framed field
space.

The principal part of `L_x` is that of the vacuum operator `L₀` (`vacuumOperator`), and
`L_x - L₀` is multiplication by a matrix whose entries are coordinates of `x - vacuumField`. A weak
solution of `L_x y = f` is therefore a weak solution of `L₀ y = f - (L_x - L₀) y`. Its tempered
distribution solves this equation in the sense of distributions: real smooth compactly supported
test functions determine a tempered distribution (`TemperedDistribution.ext_real`), and on tempered
fields `L₀` is the transpose of `L₀*` on Schwartz fields. Since `L₀ : H^(s+1) → H^s` is bijective
on tempered fields (`memSobolev_temperedVacuumOperator_iff`), the weak solution lies in `H^(s+1)`
as soon as the right-hand side lies in `H^s`.

* `mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq`: at the vacuum,
  a weak `L²` solution of `L₀ y = g` with `g ∈ H^s` lies in `H^(s+1)`, for every real `s`.
* `mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`: at a bounded measurable field
  `x`, a weak `L²` solution of `L_x y = f` with `f ∈ L²` lies in `H¹`. Applied to the weak right
  inverse `Q` of `exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`, it shows that
  `Q f ∈ H¹` at a bounded vortex, and with `f = 0` it shows that the weak `L²` kernel of `L_x`
  lies in `H¹`.
* `mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`: the elliptic
  bootstrap. If `x` is smooth and its coordinates have bounded derivatives through order `k`, a
  weak `L²` solution of `L_x y = f` with `f ∈ H^k` lies in `H^(k+1)`. The multiplication by the
  coefficients of `L_x - L₀` preserves `H^k`
  (`TemperedDistribution.mul_mem_realSobolevFunctions_of_bounded_derivatives`).

These are regularity statements for weak solutions. The Fredholm property of `L_x` between
Sobolev spaces and the dimension of its kernel are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (the Sobolev spaces `H^s`).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv RealInnerProductSpace ContDiff

/-! ### The zeroth-order part of `L_x` -/

/-- The coefficient matrix of the zeroth-order part of the gauge-fixed operator at a field with
value `w`. It is linear in `w`. -/
private def zerothOrderMatrix (w : EuclideanSpace ℝ (Fin 4)) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, -w 3, w 2; 0, 0, w 2, w 3; -w 3, -w 2, -w 1, -w 0; w 2, -w 3, w 0, -w 1]

/-- The zeroth-order part of the gauge-fixed operator at a field with value `w`, applied to a
variation with value `v`. The operator `L_x - L₀` is multiplication by
`zerothOrder (x z - vacuumField z)`. -/
private def zerothOrder (w v : EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 fun i ↦ ∑ j, zerothOrderMatrix w i j * v j

private theorem abs_zerothOrderMatrix_le (w : EuclideanSpace ℝ (Fin 4)) (i j : Fin 4) :
    |zerothOrderMatrix w i j| ≤ ‖w‖ := by
  have h (a : Fin 4) : |w a| ≤ ‖w‖ := by simpa using PiLp.norm_apply_le w a
  fin_cases i <;> fin_cases j <;> simp [zerothOrderMatrix, h]

private theorem continuous_zerothOrderMatrix_apply (i j : Fin 4) :
    Continuous fun w : EuclideanSpace ℝ (Fin 4) ↦ zerothOrderMatrix w i j := by
  have h (a : Fin 4) : Continuous fun w : EuclideanSpace ℝ (Fin 4) ↦ w a := by fun_prop
  fin_cases i <;> fin_cases j <;> first | exact continuous_const | exact h _ | exact (h _).neg

/-- The formal adjoint `L_x*` differs from the vacuum adjoint by the transpose of the zeroth-order
part of `L_x`, pointwise and without any regularity of the test field. -/
private theorem inner_gaugeFixedAdjoint (x η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    ⟪v, gaugeFixedAdjoint x η z⟫ = ⟪v, gaugeFixedAdjoint vacuumField η z⟫ +
      ⟪zerothOrder (x z - vacuumField z) v, η z⟫ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_four, gaugeFixedAdjoint_apply_zero,
    gaugeFixedAdjoint_apply_one, gaugeFixedAdjoint_apply_two, gaugeFixedAdjoint_apply_three,
    zerothOrder, zerothOrderMatrix, vacuumField_apply, PiLp.sub_apply, RCLike.inner_apply,
    conj_trivial]
  simp
  ring

/-! ### The vacuum operator as a transpose -/

/-- The `j`-th component of a real Schwartz field, as a complex Schwartz function. -/
private abbrev cpt (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) (j : Fin 4) : 𝓢(ℂ, ℂ) :=
  η.postcompCLM (ofRealCLM ∘L EuclideanSpace.proj j)

private theorem cpt_vacuumAdjoint (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    cpt (vacuumAdjoint η) 0 = -∂_{(1 : ℂ)} (cpt η 0) - ∂_{I} (cpt η 1) + (1 / 2 : ℂ) • cpt η 3 ∧
    cpt (vacuumAdjoint η) 1 = -∂_{I} (cpt η 0) + ∂_{(1 : ℂ)} (cpt η 1) - (1 / 2 : ℂ) • cpt η 2 ∧
    cpt (vacuumAdjoint η) 2 = -∂_{(1 : ℂ)} (cpt η 2) - ∂_{I} (cpt η 3) + (1 / 2 : ℂ) • cpt η 1 ∧
    cpt (vacuumAdjoint η) 3 = ∂_{I} (cpt η 2) - ∂_{(1 : ℂ)} (cpt η 3) + (1 / 2 : ℂ) • cpt η 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext z
    simp [TauCeti.lineDerivOp_postcompCLM]
    ring

/-- **`L₀` on tempered fields is the transpose of `L₀*` on real Schwartz fields.** For every field
`Y` of complex tempered distributions and every real Schwartz field `η`,
`∑ᵢ (L₀ Y)ᵢ (ηᵢ) = ∑ⱼ Yⱼ ((L₀* η)ⱼ)`. -/
private theorem sum_temperedVacuumOperator_apply (Y : Fin 4 → 𝓢'(ℂ, ℂ))
    (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) :
    ∑ i, temperedVacuumOperator Y i (cpt η i) = ∑ j, Y j (cpt (vacuumAdjoint η) j) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := cpt_vacuumAdjoint η
  simp only [Fin.sum_univ_four, h₀, h₁, h₂, h₃, temperedVacuumOperator_apply_zero,
    temperedVacuumOperator_apply_one, temperedVacuumOperator_apply_two,
    temperedVacuumOperator_apply_three]
  simp [lineDerivOp_apply_apply]
  ring

/-! ### Real `L²` fields as tempered fields -/

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

/-- Square-integrable functions times bounded zeroth-order coefficients are square integrable. -/
private theorem memLp_zerothOrder {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : AEStronglyMeasurable x volume) {C : ℝ} (hC : ∀ z, ‖x z‖ ≤ C)
    (hy : MemLp y 2 volume) :
    MemLp (fun z ↦ zerothOrder (x z - vacuumField z) (y z)) 2 volume := by
  have hw : AEStronglyMeasurable (fun z ↦ x z - vacuumField z) volume :=
    hx.sub (by rw [show vacuumField = _ from funext vacuumField_apply]; fun_prop)
  have hwC (z : ℂ) : ‖x z - vacuumField z‖ ≤ C + ‖vacuumField 0‖ := by
    rw [vacuumField_apply z, ← vacuumField_apply 0]
    exact (norm_sub_le _ _).trans (by gcongr; exact hC z)
  refine memLp_piLp_iff.2 fun i ↦ ?_
  simp only [zerothOrder]
  refine memLp_finsetSum _ fun j _ ↦ ?_
  refine (memLp_piLp_iff.1 hy j).of_le_mul (c := C + ‖vacuumField 0‖)
    (((continuous_zerothOrderMatrix_apply i j).comp_aestronglyMeasurable hw).mul
      (memLp_piLp_iff.1 hy j).aestronglyMeasurable) (ae_of_all _ fun z ↦ ?_)
  rw [norm_mul]
  gcongr
  exact (abs_zerothOrderMatrix_le _ i j).trans (hwC z)

/-- A weak solution of `L_x y = f` is a weak solution of `L₀ y = f - (L_x - L₀) y`. -/
private theorem integral_inner_gaugeFixedAdjoint_vacuumField_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hzo : MemLp (fun z ↦ zerothOrder (x z - vacuumField z) (y z)) 2 volume)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hweak : ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∫ z, ⟪y z, gaugeFixedAdjoint vacuumField η z⟫ =
      ∫ z, ⟪f z - zerothOrder (x z - vacuumField z) (y z), η z⟫ := by
  have hηL : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hc
  have hL : MemLp (gaugeFixedAdjoint vacuumField η) 2 volume :=
    (continuous_gaugeFixedAdjoint
      (by rw [show vacuumField = _ from funext vacuumField_apply]; fun_prop)
      (hη.of_le (by norm_cast))).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hc)
  simp_rw [inner_sub_left]
  rw [integral_sub (hf.integrable_inner hηL) (hzo.integrable_inner hηL), ← hweak]
  simp_rw [inner_gaugeFixedAdjoint x η _ (y _)]
  rw [integral_add (hy.integrable_inner hL) (hzo.integrable_inner hηL)]
  ring

/-- **Elliptic regularity of the gauge-fixed operator.** Let `x` be a bounded measurable field,
and let `y` be a square-integrable weak solution of `L_x y = f` with `f ∈ L²`, in the sense that
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every smooth compactly supported test field `η`. Then `y` lies in
`H¹`. -/
theorem mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : AEStronglyMeasurable x volume) {C : ℝ}
    (hC : ∀ z, ‖x z‖ ≤ C) (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields 1 := by
  have hzo := memLp_zerothOrder hx hC hy
  have hg : (fun z ↦ f z - zerothOrder (x z - vacuumField z) (y z)) ∈ sobolevFields 0 :=
    mem_sobolevFields_zero_iff.2 (hf.sub hzo)
  simpa using mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq hy hg
    fun η hη hc ↦ integral_inner_gaugeFixedAdjoint_vacuumField_eq hy hf hzo hη hc (hweak η hη hc)

/-- The zeroth-order coefficients at a smooth field whose coordinates have bounded derivatives
through order `k` are smooth with bounded derivatives through order `k`. -/
private theorem contDiff_zerothOrderMatrix_and_bounded {k : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun z ↦ zerothOrderMatrix (x z - vacuumField z) i j) ∧
      ∀ n ≤ k, ∃ C, ∀ z,
        ‖iteratedFDeriv ℝ n (fun z ↦ zerothOrderMatrix (x z - vacuumField z) i j) z‖ ≤ C := by
  set P : (ℂ → ℝ) → Prop :=
    fun g ↦ ContDiff ℝ ∞ g ∧ ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n g z‖ ≤ C
  have h0 : P 0 := ⟨contDiff_const, fun n _ ↦ ⟨0, fun z ↦ by simp⟩⟩
  have hneg {g : ℂ → ℝ} (hg : P g) : P (-g) :=
    ⟨hg.1.neg, fun n hn ↦ (hg.2 n hn).imp fun C hC z ↦ by
      rw [iteratedFDeriv_neg_apply, norm_neg]
      exact hC z⟩
  have hw (a : Fin 4) : P fun z ↦ (x z - vacuumField z) a := by
    have hxa : ContDiff ℝ ∞ fun z ↦ x z a := contDiff_euclidean.1 hx a
    have he : (fun z ↦ (x z - vacuumField z) a) = (fun z ↦ x z a) - fun _ ↦ vacuumField 0 a :=
      funext fun z ↦ by simp only [PiLp.sub_apply, Pi.sub_apply, vacuumField_apply]
    rw [he]
    refine ⟨hxa.sub contDiff_const, fun n hn ↦ ?_⟩
    obtain ⟨C, hC⟩ := hbound a n hn
    refine ⟨C + ‖vacuumField 0 a‖, fun z ↦ ?_⟩
    rw [iteratedFDeriv_sub_apply (hxa.contDiffAt.of_le (mod_cast le_top)) contDiffAt_const]
    refine (norm_sub_le _ _).trans (add_le_add (hC z) ?_)
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
  have hA := contDiff_zerothOrderMatrix_and_bounded hx hbound
  have hzo : (fun z ↦ zerothOrder (x z - vacuumField z) (y z)) ∈ sobolevFields k := by
    refine mem_sobolevFields.2 fun i ↦ ?_
    convert Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) ↦
      mul_mem_realSobolevFunctions_of_bounded_derivatives (by norm_num) (by norm_num) k
        (hA i j).1 (hA i j).2 (mem_sobolevFields.1 hy j) using 1
    ext z
    simp [zerothOrder]
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

end TauCeti.Vortex
