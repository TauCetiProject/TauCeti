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
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
import TauCeti.Analysis.PDE.Vortex.Multiplier

/-!
# Elliptic regularity of the gauge-fixed vortex operator

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴` with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a weak solution of `L_x y = f` if `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for
every smooth compactly supported test field `η`; this is the notion of solution produced by the
weak right inverse of `TauCeti.Analysis.PDE.Vortex.RightInverse`. This file shows that weak
solutions gain one derivative, measured on the Sobolev scale `sobolevFields s` of the framed field
space. The same holds for weak solutions of `L_x* η = g`, tested against `L_x`; the weak kernel of
`L_x*` (the case `g = 0`) is the weak cokernel of `L_x`.

The principal part of `L_x` is that of the vacuum operator `L₀` (`vacuumOperator`), and
`L_x - L₀` is multiplication by a matrix whose entries are coordinates of `x - vacuumField`. A weak
solution of `L_x y = f` is therefore a weak solution of `L₀ y = f - (L_x - L₀) y`. Its tempered
distribution solves this equation in the sense of distributions: real smooth compactly supported
test functions determine a tempered distribution (`TemperedDistribution.ext_real`), and on tempered
fields `L₀` is the transpose of `L₀*` on Schwartz fields (`sum_temperedVacuumOperator_apply`).
Since `L₀ : H^(s+1) → H^s` is bijective on tempered fields
(`memSobolev_temperedVacuumOperator_iff`), the weak solution lies in `H^(s+1)` as soon as the
right-hand side lies in `H^s`. For `L_x*` the roles of `L₀` and `L₀*` are exchanged
(`sum_temperedVacuumAdjoint_apply`, `memSobolev_temperedVacuumAdjoint_iff`), and `L_x* - L₀*` is
multiplication by the transposed matrix.

* `mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq`: at the vacuum,
  a weak `L²` solution of `L₀ y = g` with `g ∈ H^s` lies in `H^(s+1)`, for every real `s`.
* `mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`: at an essentially bounded
  measurable field `x`, a weak `L²` solution of `L_x y = f` with `f ∈ L²` lies in `H¹`. Applied to
  the weak right inverse `Q` of `exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`,
  it shows that `Q f ∈ H¹` at a bounded vortex, and with `f = 0` it shows that the weak `L²`
  kernel of `L_x` lies in `H¹`.
* `exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq`: at a bounded `C¹` plane
  vortex with `|α| → 1`, every `f ∈ L²` is `L_x y` weakly for some `y ∈ H¹`, so the `H¹ → L²`
  realization of `L_x` has zero cokernel.
* `mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq`: the elliptic
  bootstrap. If `x` is smooth and its coordinates have bounded derivatives through order `k`, a
  weak `L²` solution of `L_x y = f` with `f ∈ H^k` lies in `H^(k+1)`. The multiplication by the
  coefficients of `L_x - L₀` preserves `H^k` (`mulVec_mem_sobolevFields_natCast`).
* `mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq_add`: the same for weak
  solutions of `L_x y = f + A y`, where `A` is a matrix of smooth coefficients with bounded
  derivatives through order `k`, such as the commutator of `L_x` with a weight.
* `mem_sobolevFields_one_of_mem_framedFieldSpace_of_integral_inner_gaugeFixedAdjoint_eq`: a
  continuous field of `A_m^s`, `s > 1`, is bounded (`exists_norm_le_of_mem_framedFieldSpace`), so
  there weak `L²` solutions of `L_x y = f` with `f ∈ L²`, in particular the weak `L²` kernel of
  `L_x`, lie in `H¹`.
* `mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace`: at a smooth field of `A_m^s`,
  `s > 2`, a weak `L²` solution of `L_x y = f` with `f ∈ H^k`, `k ≤ s`, lies in `H^(k+1)`. Through
  order one the coefficients have bounded derivatives by Sobolev embedding
  (`exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace`); from order two on they
  multiply `H^k` into itself since `H^k(ℂ)` is an algebra
  (`mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`). With `f = 0` the weak `L²` kernel of
  `L_x` lies in `H^(k+1)`
  (`mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace_of_integral_inner_eq_zero`).
* `exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields`: at a
  `C¹` vortex of `A_m^s`, `s > 1`, the weak right inverse `Q` takes values in `H¹`.
* `mem_sobolevFields_add_one_of_integral_inner_gaugeFixedOperator_vacuumField_eq`,
  `mem_sobolevFields_one_of_integral_inner_gaugeFixedOperator_eq` and
  `mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq`: the same three
  statements for weak solutions of `L_x* η = g`, in the sense that `∫ ⟪η, L_x v⟫ = ∫ ⟪g, v⟫` for
  every smooth compactly supported test field `v`. With `g = 0` they show that the weak `L²`
  cokernel of `L_x` lies in `H¹` at an essentially bounded measurable field, and in `H^(k+1)` at a
  smooth field whose coordinates have bounded derivatives through order `k`.
* `mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq_add`: the same for
  weak solutions of `L_x* η = g + A η`, such as the commutator of `L_x*` with a weight.
* `mem_sobolevFields_one_of_mem_framedFieldSpace_of_integral_inner_gaugeFixedOperator_eq`: at a
  continuous field of `A_m^s`, `s > 1`, weak `L²` solutions of `L_x* η = g` with `g ∈ L²`, in
  particular the weak `L²` cokernel of `L_x`, lie in `H¹`.

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

/-- A matrix applied to a vector of `ℝ⁴`, in components: the form of the Sobolev multiplier
lemma `mulVec_mem_sobolevFields_natCast`. -/
private theorem toEuclideanLin_apply_eq_toLp (B : Matrix (Fin 4) (Fin 4) ℝ)
    (v : EuclideanSpace ℝ (Fin 4)) :
    B.toEuclideanLin v = WithLp.toLp 2 fun i ↦ ∑ j, B i j * v j := by
  ext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

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

/-! ### Elliptic regularity

The statements for `L_x` and `L_x*` share their proofs. In the private lemmas below, `T` is the
vacuum operator on tempered fields (`temperedVacuumOperator` or `temperedVacuumAdjoint`), `S` its
transpose on real Schwartz fields, `K x` the classical operator at the field `x` against which
weak solutions are tested (`gaugeFixedAdjoint x` or `gaugeFixedOperator x`), and `A` the
transpose of the matrix of the zeroth-order operator `K x - K vacuumField`. -/

section Common

variable {T : (Fin 4 → 𝓢'(ℂ, ℂ)) → Fin 4 → 𝓢'(ℂ, ℂ)}
  {S : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4)) → 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))}
  {K : (ℂ → EuclideanSpace ℝ (Fin 4)) → (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ →
    EuclideanSpace ℝ (Fin 4)}
  {A : EuclideanSpace ℝ (Fin 4) → Matrix (Fin 4) (Fin 4) ℝ}

/-- Elliptic regularity at the vacuum, for either vacuum operator. -/
private theorem mem_sobolevFields_add_one_of_integral_inner_eq {s : ℝ}
    (hT : ∀ Y η, ∑ i, T Y i (cpt η i) = ∑ j, Y j (cpt (S η) j))
    (hK : ∀ (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) z, K vacuumField η z = S η z)
    (hreg : ∀ Y, (∀ i, MemSobolev s 2 (T Y i)) → ∀ i, MemSobolev (s + 1) 2 (Y i))
    {y g : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hg : g ∈ sobolevFields s)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, K vacuumField η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields (s + 1) := by
  have hyj (j : Fin 4) : MemLp (fun z ↦ y z j) 2 volume := memLp_piLp_iff.1 hy j
  set u : Fin 4 → Lp ℝ 2 (volume : Measure ℂ) := fun j ↦ (hyj j).toLp _
  have hu (j : Fin 4) : u j =ᵐ[volume] fun z ↦ y z j := (hyj j).coeFn_toLp
  choose v hv hvs using fun j ↦ mem_realSobolevFunctions.1 (mem_sobolevFields.1 hg j)
  set Y : Fin 4 → 𝓢'(ℂ, ℂ) := fun j ↦ Lp.toTemperedDistribution (ofRealCLM.compLp (u j))
  set G : Fin 4 → 𝓢'(ℂ, ℂ) := fun j ↦ Lp.toTemperedDistribution (ofRealCLM.compLp (v j))
  -- The tempered field of `y` solves `T Y = G`: test against `φ eᵢ` with `φ` compactly supported.
  have hL : T Y = G := by
    funext i
    refine ext_real fun φ hφ ↦ ?_
    have hη : HasCompactSupport (single i φ) := by
      rw [show ⇑(single i φ) = _ ∘ φ from funext (SchwartzMap.postcompCLM_apply _ φ)]
      exact hφ.comp_left (map_zero _)
    rw [← sum_apply_cpt_single, ← sum_apply_cpt_single, hT, ← integral_inner_eq_sum u hu,
      ← integral_inner_eq_sum v hv]
    congr 1
    rw [← hweak _ ((single i φ).smooth ⊤) hη]
    simp_rw [hK]
  exact mem_sobolevFields.2 fun i ↦ mem_realSobolevFunctions.2
    ⟨u i, hu i, hreg Y (fun i ↦ by rw [hL]; exact hvs i) i⟩

/-- Square-integrable functions times essentially bounded zeroth-order coefficients are square
integrable. -/
private theorem memLp_zerothOrder
    (hA : ∀ i j, ∃ a b, ∀ w, A w i j = gaugeFixedZerothOrderMatrix w a b)
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : AEStronglyMeasurable x volume) {C : ℝ}
    (hC : ∀ᵐ z ∂volume, ‖x z‖ ≤ C) (hy : MemLp y 2 volume) :
    MemLp (fun z ↦ (A (x z - vacuumField z)).toEuclideanLin (y z)) 2 volume := by
  have hw : AEStronglyMeasurable (fun z ↦ x z - vacuumField z) volume :=
    hx.sub (by rw [show vacuumField = _ from funext vacuumField_apply]; fun_prop)
  have hwC (z : ℂ) (hz : ‖x z‖ ≤ C) : ‖x z - vacuumField z‖ ≤ C + ‖vacuumField 0‖ := by
    rw [vacuumField_apply z, ← vacuumField_apply 0]
    exact (norm_sub_le _ _).trans (by gcongr)
  refine memLp_piLp_iff.2 fun i ↦ ?_
  simp only [toEuclideanLin_apply_eq_toLp]
  refine memLp_finsetSum _ fun j _ ↦ ?_
  obtain ⟨a, b, hab⟩ := hA i j
  simp only [hab]
  refine (memLp_piLp_iff.1 hy j).of_le_mul (c := C + ‖vacuumField 0‖)
    (((continuous_gaugeFixedZerothOrderMatrix_apply a b).comp_aestronglyMeasurable hw).mul
      (memLp_piLp_iff.1 hy j).aestronglyMeasurable) (hC.mono fun z hz ↦ ?_)
  rw [norm_mul]
  gcongr
  exact (abs_gaugeFixedZerothOrderMatrix_le _ a b).trans (hwC z hz)

/-- If `∫ ⟪y, K x η⟫ = ∫ ⟪f, η⟫` for a test field `η`, then
`∫ ⟪y, K vacuumField η⟫ = ∫ ⟪f - Z y, η⟫`, where `Z` is the zeroth-order term
`(A (x z - vacuumField z)).toEuclideanLin`: tested against the vacuum operator, `y` has the
zeroth-order term moved to the right-hand side. -/
private theorem integral_inner_vacuumField_eq
    (hK : ∀ (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) z, K vacuumField η z = S η z)
    (hB : ∀ x η z v, ⟪v, K x η z⟫ =
      ⟪v, K vacuumField η z⟫ + ⟪(A (x z - vacuumField z)).toEuclideanLin v, η z⟫)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hzo : MemLp (fun z ↦ (A (x z - vacuumField z)).toEuclideanLin (y z)) 2 volume)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hweak : ∫ z, ⟪y z, K x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∫ z, ⟪y z, K vacuumField η z⟫ =
      ∫ z, ⟪f z - (A (x z - vacuumField z)).toEuclideanLin (y z), η z⟫ := by
  have hηL : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hc
  -- `hK` only applies to Schwartz fields, so `η` is packaged as the Schwartz field
  -- `hc.toSchwartzMap hη`, which `hS` identifies with `η` as a function.
  have hL : MemLp (K vacuumField η) 2 volume := by
    have hS : ⇑(hc.toSchwartzMap hη) = η := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    rw [show K vacuumField η = S (hc.toSchwartzMap hη) from funext fun z ↦ by rw [← hK, hS]]
    exact (S _).memLp 2
  simp_rw [inner_sub_left]
  rw [integral_sub (hf.integrable_inner hηL) (hzo.integrable_inner hηL), ← hweak]
  simp_rw [hB x η _ (y _)]
  rw [integral_add (hy.integrable_inner hL) (hzo.integrable_inner hηL)]
  ring

/-- Elliptic regularity at an essentially bounded measurable field, for either operator. -/
private theorem mem_sobolevFields_one_of_integral_inner_eq
    (hT : ∀ Y η, ∑ i, T Y i (cpt η i) = ∑ j, Y j (cpt (S η) j))
    (hK : ∀ (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) z, K vacuumField η z = S η z)
    (hreg : ∀ s Y, (∀ i, MemSobolev s 2 (T Y i)) → ∀ i, MemSobolev (s + 1) 2 (Y i))
    (hA : ∀ i j, ∃ a b, ∀ w, A w i j = gaugeFixedZerothOrderMatrix w a b)
    (hB : ∀ x η z v, ⟪v, K x η z⟫ =
      ⟪v, K vacuumField η z⟫ + ⟪(A (x z - vacuumField z)).toEuclideanLin v, η z⟫)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : AEStronglyMeasurable x volume) {C : ℝ}
    (hC : ∀ᵐ z ∂volume, ‖x z‖ ≤ C) (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, K x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields 1 := by
  have hzo := memLp_zerothOrder hA hx hC hy
  have hg : (fun z ↦ f z - (A (x z - vacuumField z)).toEuclideanLin (y z)) ∈ sobolevFields 0 :=
    mem_sobolevFields_zero_iff.2 (hf.sub hzo)
  simpa using mem_sobolevFields_add_one_of_integral_inner_eq hT hK (hreg 0) hy hg
    fun η hη hc ↦ integral_inner_vacuumField_eq hK hB hy hf hzo hη hc (hweak η hη hc)

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
    -- A single bound for the derivatives through order `k`.
    obtain ⟨M, hMx⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists (hbound a)
    have hM := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hMx).1
    refine ⟨hxa.sub contDiff_const, M + ‖vacuumField 0 a‖, by positivity, fun n hn z ↦ ?_⟩
    rw [iteratedFDeriv_sub_apply (hxa.contDiffAt.of_le (mod_cast le_top)) contDiffAt_const]
    refine (norm_sub_le _ _).trans (add_le_add (hMx n hn z) ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [iteratedFDeriv_const_of_ne hn]
  fin_cases i <;> fin_cases j <;> first | exact h0 | exact hw _ | exact hneg (hw _)

/-- One step of the elliptic bootstrap: a field `y ∈ L²` with `∫ ⟪y, K x η⟫ = ∫ ⟪f, η⟫` for every
smooth compactly supported test field `η`, where `f ∈ H^s`, lies in `H^(s+1)` as soon as the
zeroth-order part `(A (x z - vacuumField z)).toEuclideanLin (y z)` lies in `H^s`. -/
private theorem mem_sobolevFields_add_one_of_zerothOrder_mem {s : ℝ}
    (hT : ∀ Y η, ∑ i, T Y i (cpt η i) = ∑ j, Y j (cpt (S η) j))
    (hK : ∀ (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) z, K vacuumField η z = S η z)
    (hreg : ∀ s Y, (∀ i, MemSobolev s 2 (T Y i)) → ∀ i, MemSobolev (s + 1) 2 (Y i))
    (hB : ∀ x η z v, ⟪v, K x η z⟫ =
      ⟪v, K vacuumField η z⟫ + ⟪(A (x z - vacuumField z)).toEuclideanLin v, η z⟫)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hzo : (fun z ↦ (A (x z - vacuumField z)).toEuclideanLin (y z)) ∈ sobolevFields s)
    (hy : MemLp y 2 volume) (hf : f ∈ sobolevFields s)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, K x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields (s + 1) :=
  mem_sobolevFields_add_one_of_integral_inner_eq hT hK (hreg s) hy (sub_mem hf hzo)
    fun η hη hc ↦ integral_inner_vacuumField_eq hK hB hy (memLp_of_mem_sobolevFields hf)
      (memLp_of_mem_sobolevFields hzo) hη hc (hweak η hη hc)

/-- One step of the elliptic bootstrap: a field `y ∈ H^k` with `∫ ⟪y, K x η⟫ = ∫ ⟪f, η⟫` for every
smooth compactly supported test field `η`, where `f ∈ H^k`, lies in `H^(k+1)`. -/
private theorem mem_sobolevFields_natCast_add_one_of_mem_sobolevFields {k : ℕ}
    (hT : ∀ Y η, ∑ i, T Y i (cpt η i) = ∑ j, Y j (cpt (S η) j))
    (hK : ∀ (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) z, K vacuumField η z = S η z)
    (hreg : ∀ s Y, (∀ i, MemSobolev s 2 (T Y i)) → ∀ i, MemSobolev (s + 1) 2 (Y i))
    (hA : ∀ i j, ∃ a b, ∀ w, A w i j = gaugeFixedZerothOrderMatrix w a b)
    (hB : ∀ x η z v, ⟪v, K x η z⟫ =
      ⟪v, K vacuumField η z⟫ + ⟪(A (x z - vacuumField z)).toEuclideanLin v, η z⟫)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : y ∈ sobolevFields k) (hf : f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, K x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields (k + 1) := by
  have hM := contDiff_gaugeFixedZerothOrderMatrix_and_bounded hx hbound
  have hzo : (fun z ↦ (A (x z - vacuumField z)).toEuclideanLin (y z)) ∈ sobolevFields k := by
    simp_rw [toEuclideanLin_apply_eq_toLp]
    refine mulVec_mem_sobolevFields_natCast k (A := fun i j z ↦ A (x z - vacuumField z) i j)
      (fun i j ↦ ?_) (fun i j ↦ ?_) hy <;>
    · obtain ⟨a, b, hab⟩ := hA i j
      simp only [hab]
      first | exact (hM a b).1 | exact (hM a b).2
  exact mem_sobolevFields_add_one_of_zerothOrder_mem hT hK hreg hB hzo
    (memLp_of_mem_sobolevFields hy) hf hweak

/-- The elliptic bootstrap at a smooth field, for either operator. -/
private theorem mem_sobolevFields_natCast_add_one_of_integral_inner_eq (k : ℕ)
    (hT : ∀ Y η, ∑ i, T Y i (cpt η i) = ∑ j, Y j (cpt (S η) j))
    (hK : ∀ (η : 𝓢(ℂ, EuclideanSpace ℝ (Fin 4))) z, K vacuumField η z = S η z)
    (hreg : ∀ s Y, (∀ i, MemSobolev s 2 (T Y i)) → ∀ i, MemSobolev (s + 1) 2 (Y i))
    (hA : ∀ i j, ∃ a b, ∀ w, A w i j = gaugeFixedZerothOrderMatrix w a b)
    (hB : ∀ x η z v, ⟪v, K x η z⟫ =
      ⟪v, K vacuumField η z⟫ + ⟪(A (x z - vacuumField z)).toEuclideanLin v, η z⟫)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hy : MemLp y 2 volume) (hf : f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, K x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields (k + 1) := by
  induction k with
  | zero =>
    exact mem_sobolevFields_natCast_add_one_of_mem_sobolevFields hT hK hreg hA hB hx hbound
      (by simpa using hy) hf hweak
  | succ k ih =>
    have hy' : y ∈ sobolevFields (k + 1) :=
      ih (fun i n hn ↦ hbound i n (hn.trans k.le_succ))
        (sobolevFields_mono (by simp) hf)
    exact_mod_cast mem_sobolevFields_natCast_add_one_of_mem_sobolevFields hT hK hreg hA hB hx
      hbound (by exact_mod_cast hy') hf hweak

end Common

/-- The regularity of the tempered vacuum operator, in the form used above. -/
private theorem memSobolev_add_one_of_temperedVacuumOperator (s : ℝ) (Y : Fin 4 → 𝓢'(ℂ, ℂ))
    (hY : ∀ i, MemSobolev s 2 (temperedVacuumOperator Y i)) (i : Fin 4) :
    MemSobolev (s + 1) 2 (Y i) :=
  memSobolev_temperedVacuumOperator_iff.1 (by simpa using hY) i

/-- The regularity of the tempered vacuum adjoint, in the form used above. -/
private theorem memSobolev_add_one_of_temperedVacuumAdjoint (s : ℝ) (Y : Fin 4 → 𝓢'(ℂ, ℂ))
    (hY : ∀ i, MemSobolev s 2 (temperedVacuumAdjoint Y i)) (i : Fin 4) :
    MemSobolev (s + 1) 2 (Y i) :=
  memSobolev_temperedVacuumAdjoint_iff.1 (by simpa using hY) i

/-- The elliptic bootstrap with a zeroth-order term, for either operator: if every weak solution
`y ∈ L²` of `P* y = F` with `F ∈ H^j`, `j ≤ k`, lies in `H^(j+1)`, then so does a weak solution of
`P* y = f + A y` with `f ∈ H^k` and `A` smooth with bounded derivatives through order `k`. -/
private theorem mem_sobolevFields_natCast_add_one_of_integral_inner_eq_add (k : ℕ)
    {P : (ℂ → EuclideanSpace ℝ (Fin 4)) → ℂ → EuclideanSpace ℝ (Fin 4)}
    {y f : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hP : ∀ j ≤ k, ∀ F ∈ sobolevFields j, (∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η →
      HasCompactSupport η → ∫ z, ⟪y z, P η z⟫ = ∫ z, ⟪F z, η z⟫) → y ∈ sobolevFields (j + 1))
    {A : Fin 4 → Fin 4 → ℂ → ℝ} (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hAbound : ∀ i j, ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ M)
    (hy : MemLp y 2 volume) (hf : f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, P η z⟫ =
        ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) :
    y ∈ sobolevFields (k + 1) := by
  -- One step: `y ∈ H^j` puts the right side `f + A y` in `H^j`, hence `y ∈ H^(j+1)`.
  have hstep (j : ℕ) (hj : j ≤ k) (hyj : y ∈ sobolevFields j) : y ∈ sobolevFields (j + 1) :=
    hP j hj _ (add_mem (sobolevFields_mono (by exact_mod_cast hj) hf)
      (mulVec_mem_sobolevFields_natCast j hA (fun i' j' ↦ (hAbound i' j').imp
        fun _ hM ↦ ⟨hM.1, fun n hn ↦ hM.2 n (hn.trans hj)⟩) hyj)) hweak
  have hall (j : ℕ) (hj : j ≤ k) : y ∈ sobolevFields (j + 1) := by
    induction j with
    | zero => simpa using hstep 0 hj (by simpa using hy)
    | succ j ih => exact_mod_cast hstep (j + 1) hj (by exact_mod_cast ih (by omega))
  exact hall k le_rfl

/-! ### Weak solutions of `L_x y = f` -/

/-- **Elliptic regularity at the vacuum.** Let `y` be a square-integrable field which is a weak
solution of `L₀ y = g`, in the sense that `∫ ⟪y, L₀* η⟫ = ∫ ⟪g, η⟫` for every smooth compactly
supported test field `η`, where `g` lies in `L² ∩ H^s`. Then `y` lies in `H^(s+1)`. -/
theorem mem_sobolevFields_add_one_of_integral_inner_gaugeFixedAdjoint_vacuumField_eq {s : ℝ}
    {y g : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 volume) (hg : g ∈ sobolevFields s)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint vacuumField η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields (s + 1) :=
  mem_sobolevFields_add_one_of_integral_inner_eq sum_temperedVacuumOperator_apply
    gaugeFixedAdjoint_vacuumField (memSobolev_add_one_of_temperedVacuumOperator s) hy hg hweak

/-- **Elliptic regularity of the gauge-fixed operator.** Let `x` be an essentially bounded
measurable field, and let `y` be a square-integrable weak solution of `L_x y = f` with `f ∈ L²`,
in the sense that `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every smooth compactly supported test field `η`.
Then `y` lies in `H¹`. -/
theorem mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : AEStronglyMeasurable x volume) {C : ℝ}
    (hC : ∀ᵐ z ∂volume, ‖x z‖ ≤ C) (hy : MemLp y 2 volume) (hf : MemLp f 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields 1 :=
  mem_sobolevFields_one_of_integral_inner_eq (A := gaugeFixedZerothOrderMatrix)
    sum_temperedVacuumOperator_apply gaugeFixedAdjoint_vacuumField
    memSobolev_add_one_of_temperedVacuumOperator (fun i j ↦ ⟨i, j, fun _ ↦ rfl⟩)
    (fun x η z v ↦ by
      rw [inner_gaugeFixedAdjoint_eq_add_inner_gaugeFixedZerothOrder x vacuumField,
        gaugeFixedZerothOrder_eq_toEuclideanLin]) hx hC hy hf hweak

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
  obtain ⟨Q, hQ⟩ :=
    exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution (μ := volume) hx hsol hlim
  have hQf (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
      ∫ z, ⟪Q (hf.toLp f) z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫ := by
    rw [(hQ _).isGaugeFixedWeakSolution.integral_inner_eq hη hηc]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun z hz ↦ by simp only [hz])
  exact ⟨_, mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
    hx.continuous.aestronglyMeasurable (.of_forall hC) (Lp.memLp _) hf
    fun η hη hηc ↦ hQf η (hη.of_le (by norm_cast)) hηc, hQf⟩

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
    y ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_integral_inner_eq k (A := gaugeFixedZerothOrderMatrix)
    sum_temperedVacuumOperator_apply gaugeFixedAdjoint_vacuumField
    memSobolev_add_one_of_temperedVacuumOperator (fun i j ↦ ⟨i, j, fun _ ↦ rfl⟩)
    (fun x η z v ↦ by
      rw [inner_gaugeFixedAdjoint_eq_add_inner_gaugeFixedZerothOrder x vacuumField,
        gaugeFixedZerothOrder_eq_toEuclideanLin]) hx hbound hy hf hweak

/-- **The elliptic bootstrap with a zeroth-order term.** Let `x` be a smooth field whose
coordinates have bounded derivatives through order `k`, and let `A` be a `4 × 4` matrix of smooth
real functions with bounded derivatives through order `k`. A square-integrable weak solution `y`
of `L_x y = f + A y` with `f ∈ H^k`, in the sense that `∫ ⟪y, L_x* η⟫ = ∫ ⟪f + A y, η⟫` for every
smooth compactly supported test field `η`, lies in `H^(k+1)`. -/
theorem mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq_add (k : ℕ)
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {A : Fin 4 → Fin 4 → ℂ → ℝ} (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hAbound : ∀ i j, ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ M)
    (hy : MemLp y 2 volume) (hf : f ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ =
        ∫ z, ⟪f z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * y z j), η z⟫) :
    y ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_integral_inner_eq_add k (fun j hj _ hF hw ↦
    mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq j hx
      (fun i n hn ↦ hbound i n (hn.trans hj)) hy hF hw) hA hAbound hy hf hweak

/-! ### Weak solutions of `L_x* η = g` -/

/-- **Elliptic regularity of the adjoint at the vacuum.** Let `η` be a square-integrable field
which is a weak solution of `L₀* η = g`, in the sense that `∫ ⟪η, L₀ v⟫ = ∫ ⟪g, v⟫` for every
smooth compactly supported test field `v`, where `g` lies in `L² ∩ H^s`. Then `η` lies in
`H^(s+1)`. -/
theorem mem_sobolevFields_add_one_of_integral_inner_gaugeFixedOperator_vacuumField_eq {s : ℝ}
    {η g : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : MemLp η 2 volume) (hg : g ∈ sobolevFields s)
    (hweak : ∀ v : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ v → HasCompactSupport v →
      ∫ z, ⟪η z, gaugeFixedOperator vacuumField v z⟫ = ∫ z, ⟪g z, v z⟫) :
    η ∈ sobolevFields (s + 1) :=
  mem_sobolevFields_add_one_of_integral_inner_eq sum_temperedVacuumAdjoint_apply
    gaugeFixedOperator_vacuumField (memSobolev_add_one_of_temperedVacuumAdjoint s) hη hg hweak

/-- **Elliptic regularity of the adjoint of the gauge-fixed operator.** Let `x` be an essentially
bounded measurable field, and let `η` be a square-integrable weak solution of `L_x* η = g` with
`g ∈ L²`, in the sense that `∫ ⟪η, L_x v⟫ = ∫ ⟪g, v⟫` for every smooth compactly supported test
field `v`. Then `η` lies in `H¹`. -/
theorem mem_sobolevFields_one_of_integral_inner_gaugeFixedOperator_eq
    {x η g : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : AEStronglyMeasurable x volume) {C : ℝ}
    (hC : ∀ᵐ z ∂volume, ‖x z‖ ≤ C) (hη : MemLp η 2 volume) (hg : MemLp g 2 volume)
    (hweak : ∀ v : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ v → HasCompactSupport v →
      ∫ z, ⟪η z, gaugeFixedOperator x v z⟫ = ∫ z, ⟪g z, v z⟫) :
    η ∈ sobolevFields 1 :=
  mem_sobolevFields_one_of_integral_inner_eq sum_temperedVacuumAdjoint_apply
    gaugeFixedOperator_vacuumField memSobolev_add_one_of_temperedVacuumAdjoint
    (fun i j ↦ ⟨j, i, fun _ ↦ rfl⟩)
    (inner_gaugeFixedOperator_eq_add_inner_toEuclideanLin_transpose · vacuumField) hx hC hη hg
    hweak

/-- **The elliptic bootstrap for the adjoint of the gauge-fixed operator.** Let `x` be a smooth
field whose coordinates have bounded derivatives through order `k`, and let `η` be a
square-integrable weak solution of `L_x* η = g` with `g ∈ H^k`, in the sense that
`∫ ⟪η, L_x v⟫ = ∫ ⟪g, v⟫` for every smooth compactly supported test field `v`. Then `η` lies in
`H^(k+1)`. -/
theorem mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq (k : ℕ)
    {x η g : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hη : MemLp η 2 volume) (hg : g ∈ sobolevFields k)
    (hweak : ∀ v : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ v → HasCompactSupport v →
      ∫ z, ⟪η z, gaugeFixedOperator x v z⟫ = ∫ z, ⟪g z, v z⟫) :
    η ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_integral_inner_eq k sum_temperedVacuumAdjoint_apply
    gaugeFixedOperator_vacuumField memSobolev_add_one_of_temperedVacuumAdjoint
    (fun i j ↦ ⟨j, i, fun _ ↦ rfl⟩)
    (inner_gaugeFixedOperator_eq_add_inner_toEuclideanLin_transpose · vacuumField) hx hbound hη hg
    hweak

/-- **The elliptic bootstrap for the adjoint with a zeroth-order term.** Let `x` be a smooth field
whose coordinates have bounded derivatives through order `k`, and let `A` be a `4 × 4` matrix of
smooth real functions with bounded derivatives through order `k`. A square-integrable weak
solution `η` of `L_x* η = g + A η` with `g ∈ H^k`, in the sense that
`∫ ⟪η, L_x v⟫ = ∫ ⟪g + A η, v⟫` for every smooth compactly supported test field `v`, lies in
`H^(k+1)`. -/
theorem mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq_add (k : ℕ)
    {x η g : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    {A : Fin 4 → Fin 4 → ℂ → ℝ} (hA : ∀ i j, ContDiff ℝ ∞ (A i j))
    (hAbound : ∀ i j, ∃ M ≥ 0, ∀ n ≤ k, ∀ z, ‖iteratedFDeriv ℝ n (A i j) z‖ ≤ M)
    (hη : MemLp η 2 volume) (hg : g ∈ sobolevFields k)
    (hweak : ∀ v : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ v → HasCompactSupport v →
      ∫ z, ⟪η z, gaugeFixedOperator x v z⟫ =
        ∫ z, ⟪g z + WithLp.toLp 2 (fun i ↦ ∑ j : Fin 4, A i j z * η z j), v z⟫) :
    η ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_integral_inner_eq_add k (fun j hj _ hF hw ↦
    mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedOperator_eq j hx
      (fun i n hn ↦ hbound i n (hn.trans hj)) hη hF hw) hA hAbound hη hg hweak

/-! ### Fields of `A_m^s` and plane vortices -/

/-- **Weak solutions at a field of `A_m^s` lie in `H¹`.** Let `x` be a continuous field of the
affine space `A_m^s`, `s > 1`, and `g ∈ L²(ℂ; ℝ⁴)`. Every `L²` weak solution of `L_x y = g` lies
in `H¹`; in particular the weak kernel of `L_x` lies in `H¹`. -/
theorem mem_sobolevFields_one_of_mem_framedFieldSpace_of_integral_inner_gaugeFixedAdjoint_eq
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} (hs : 1 < s) {x y g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hcont : Continuous x) (hy : MemLp y 2 volume)
    (hg : MemLp g 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields 1 :=
  let ⟨_, hC⟩ := exists_norm_le_of_mem_framedFieldSpace hs hx hcont
  mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq hcont.aestronglyMeasurable
    (ae_of_all _ hC) hy hg hweak

/-- **Weak solutions of the adjoint at a field of `A_m^s` lie in `H¹`.** Let `x` be a continuous
field of the affine space `A_m^s`, `s > 1`, and `g ∈ L²(ℂ; ℝ⁴)`. Every `L²` weak solution of
`L_x* η = g`, in the sense that `∫ ⟪η, L_x v⟫ = ∫ ⟪g, v⟫` for every smooth compactly supported
test field `v`, lies in `H¹`; in particular the weak `L²` cokernel of `L_x` lies in `H¹`. -/
theorem mem_sobolevFields_one_of_mem_framedFieldSpace_of_integral_inner_gaugeFixedOperator_eq
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} (hs : 1 < s) {x η g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hcont : Continuous x) (hη : MemLp η 2 volume)
    (hg : MemLp g 2 volume)
    (hweak : ∀ v : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ v → HasCompactSupport v →
      ∫ z, ⟪η z, gaugeFixedOperator x v z⟫ = ∫ z, ⟪g z, v z⟫) :
    η ∈ sobolevFields 1 :=
  let ⟨_, hC⟩ := exists_norm_le_of_mem_framedFieldSpace hs hx hcont
  mem_sobolevFields_one_of_integral_inner_gaugeFixedOperator_eq hcont.aestronglyMeasurable
    (ae_of_all _ hC) hη hg hweak

/-- One step of the elliptic bootstrap for `L_x`: a weak `L²` solution of `L_x y = f ∈ H^s` lies in
`H^(s+1)` as soon as the zeroth-order part `(L_x - L₀) y` lies in `H^s`. -/
private theorem mem_sobolevFields_add_one_of_gaugeFixedZerothOrder_mem {s : ℝ}
    {x y f : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hzo : (fun z ↦ gaugeFixedZerothOrder (x z - vacuumField z) (y z)) ∈ sobolevFields s)
    (hy : MemLp y 2 volume) (hf : f ∈ sobolevFields s)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    y ∈ sobolevFields (s + 1) :=
  mem_sobolevFields_add_one_of_zerothOrder_mem (A := gaugeFixedZerothOrderMatrix)
    sum_temperedVacuumOperator_apply gaugeFixedAdjoint_vacuumField
    memSobolev_add_one_of_temperedVacuumOperator
    (fun x η z v ↦ by
      rw [inner_gaugeFixedAdjoint_eq_add_inner_gaugeFixedZerothOrder x vacuumField,
        gaugeFixedZerothOrder_eq_toEuclideanLin])
    (by simpa only [gaugeFixedZerothOrder_eq_toEuclideanLin] using hzo) hy hf hweak

/-- At a field of `A_m^n`, for an integer `n > 1`, the zeroth-order part `(L_x - L₀) y` of the
gauge-fixed operator preserves `H^n`, since `H^n(ℂ)` is then an algebra. -/
private theorem gaugeFixedZerothOrder_mem_sobolevFields_of_mem_framedFieldSpace
    {f : ContDiffBump (0 : ℝ)} {m n : ℕ} (hn : 1 < n) {x y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m n) (hy : y ∈ sobolevFields n) :
    (fun z ↦ gaugeFixedZerothOrder (x z - vacuumField z) (y z)) ∈ sobolevFields n := by
  set P : (ℂ → ℝ) → Prop := fun a ↦ ∀ b, (fun z ↦ a z * y z b) ∈ realSobolevFunctions ℂ n 2
  have h0 : P 0 := fun b ↦ by
    convert zero_mem (realSobolevFunctions ℂ n 2) using 1
    ext
    simp
  have hneg {a : ℂ → ℝ} (ha : P a) : P (-a) := fun b ↦ by
    convert neg_mem (ha b) using 1
    ext
    simp
  have hw (a : Fin 4) : P fun z ↦ (x z - vacuumField z) a := fun b ↦ by
    have hyb := mem_sobolevFields.1 hy b
    convert sub_mem (mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hn hx a hyb)
      (Submodule.smul_mem _ (vacuumField 0 a) hyb) using 1
    ext z
    simp only [PiLp.sub_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, vacuumField_apply]
    ring
  have hentry (i j : Fin 4) :
      P fun z ↦ gaugeFixedZerothOrderMatrix (x z - vacuumField z) i j := by
    fin_cases i <;> fin_cases j <;> first | exact h0 | exact hw _ | exact hneg (hw _)
  refine mem_sobolevFields.2 fun i ↦ ?_
  convert Submodule.sum_mem _ fun j (_ : j ∈ Finset.univ) ↦ hentry i j j using 1
  ext z
  rw [gaugeFixedZerothOrder_apply]
  simp

/-- **Elliptic regularity at a field of `A_m^s`.** Let `x` be a smooth field of `A_m^s` with
`s > 2`, and let `k ≤ s`. A square-integrable weak solution of `L_x y = g` with `g ∈ H^k` lies in
`H^(k+1)`. -/
theorem mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace {f : ContDiffBump (0 : ℝ)}
    {m : ℕ} {s : ℝ} {k : ℕ} (hs : 2 < s) (hks : k ≤ s) {x y g : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hxs : ContDiff ℝ ∞ x) (hy : MemLp y 2 volume)
    (hg : g ∈ sobolevFields k)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪g z, η z⟫) :
    y ∈ sobolevFields (k + 1) := by
  -- Through order one the coefficients of `L_x` have bounded derivatives by Sobolev embedding.
  have hbound (k : ℕ) (hk : k ≤ 1) :
      ∀ i, ∀ n ≤ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C := fun i n hn ↦
    exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace
      (by have : (n : ℝ) ≤ 1 := by exact_mod_cast hn.trans hk
          linarith) hxs.continuous hx i
  induction k with
  | zero =>
    exact mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq 0 hxs
      (hbound 0 (by simp)) hy hg hweak
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact_mod_cast mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq 1
        hxs (hbound 1 le_rfl) hy (by simpa using hg) hweak
    -- From order two on, `H^(k+1)(ℂ)` is an algebra containing the tails of the coefficients.
    have hy' : y ∈ sobolevFields (k + 1) :=
      ih (by push_cast at hks; linarith) (sobolevFields_mono (by simp) hg)
    exact mem_sobolevFields_add_one_of_gaugeFixedZerothOrder_mem
      (gaugeFixedZerothOrder_mem_sobolevFields_of_mem_framedFieldSpace (by omega)
        (framedFieldSpace_mono f m hks hx) (by exact_mod_cast hy')) hy hg hweak

/-- **Regularity of the weak kernel.** Let `x` be a smooth field of `A_m^s` with `s > 2`. Every
square-integrable weak solution of `L_x y = 0` lies in `H^(k+1)` for each `k ≤ s`. -/
theorem mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace_of_integral_inner_eq_zero
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} {k : ℕ} (hs : 2 < s) (hks : k ≤ s)
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : x ∈ framedFieldSpace f m s)
    (hxs : ContDiff ℝ ∞ x) (hy : MemLp y 2 volume)
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = 0) :
    y ∈ sobolevFields (k + 1) :=
  mem_sobolevFields_natCast_add_one_of_mem_framedFieldSpace hs hks hx hxs hy (zero_mem _)
    fun η hη hηc ↦ by simpa using hweak η hη hηc

/-- **The weak right inverse at a plane vortex takes values in `H¹`.** Let `x` be a `C¹` solution
of the plane vortex equation in the affine space `A_m^s`, `s > 1`. Then there is a bounded
operator `Q` on `L²(ℂ; ℝ⁴)` such that, for every `g ∈ L²`, `Q g` is a weak solution of
`L_x y = g`, orthogonal to the weak kernel of `L_x` (`IsMinimalGaugeFixedWeakSolution`), and lies
in `H¹`. -/
theorem exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution_and_mem_sobolevFields
    {f : ContDiffBump (0 : ℝ)} {m : ℕ} {s : ℝ} (hs : 1 < s) {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ framedFieldSpace f m s) (hx₁ : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume : Measure ℂ),
      ∀ g, IsMinimalGaugeFixedWeakSolution volume x g (Q g) ∧
        (Q g : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields 1 := by
  obtain ⟨Q, hQ⟩ := exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution
    (μ := volume) hx₁ hsol (tendsto_normSq_of_mem_framedFieldSpace hs hx hx₁.continuous)
  exact ⟨Q, fun g ↦ ⟨hQ g,
    mem_sobolevFields_one_of_mem_framedFieldSpace_of_integral_inner_gaugeFixedAdjoint_eq hs hx
      hx₁.continuous (Lp.memLp _) (Lp.memLp g) fun η hη hc ↦
        (hQ g).isGaugeFixedWeakSolution.integral_inner_eq (hη.of_le (by simp)) hc⟩⟩

end TauCeti.Vortex
