/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Analysis.Matrix.Grothendieck
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.SimpleFunc.Basic
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Grothendieck's theorem: operators from `L¹` into Hilbert space are absolutely summing

Let `μ` be any measure and `H` an inner product space over `𝕜 = ℝ` or `ℂ`. Every bounded operator
`T : L¹(μ) → H` is absolutely `1`-summing, with `π₁(T) ≤ κ_𝕜 ‖T‖`, where `κ_ℝ = 8` and
`κ_𝕜 = 16` for a general `RCLike` field are the constants of Grothendieck's inequality for
matrices (`Matrix.abs_sum_sum_mul_inner_le_eight_mul` and
`Matrix.norm_sum_sum_mul_inner_le_sixteen_mul`). The constants are not optimal. The space `H`
need not be complete.

The proof first treats finite families in the span of the indicator functions `1_{A j}` of
finitely many disjoint sets of finite measure. This span is a weighted finite `ℓ¹` space:
`‖∑ j, d j • 1_{A j}‖ = ∑ j, μ(A j) * ‖d j‖` (`TauCeti.norm_sum_indicatorConstLp_one`). For
`y i = ∑ j, c i j • 1_{A j}`, let `u i` be unit vectors norming `T (y i)` and
`v j = T 1_{A j} / (μ(A j) ‖T‖)` the normalized columns of `T`. Then
`∑ i, ‖T (y i)‖ = ‖T‖ * ∑ i, ∑ j, c i j * μ(A j) * ⟪u i, v j⟫`. The matrix `c i j * μ(A j)` has
scalar bound the weak `L¹` norm of `y`, since a combination of the `y i` with coefficients of norm
at most one has norm at most that weak norm (`TauCeti.norm_sum_smul_le_weakLpNorm_one`), and
Grothendieck's inequality applies. Every finite family of simple functions lies in such a span,
the sets `A j` being the nonzero fibres of the joint simple function. Both sides of the inequality
are continuous in the family, so density of simple functions in `L¹` gives the general case.

## Main results

* `ContinuousLinearMap.summingENorm_one_le_ofReal_sixteen_mul_norm`: `π₁(T) ≤ 16 ‖T‖` for every
  bounded operator `T : L¹(μ, 𝕜) → H` over an `RCLike` field.
* `ContinuousLinearMap.summingENorm_one_le_ofReal_eight_mul_norm`: `π₁(T) ≤ 8 ‖T‖` over `ℝ`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 8.
* J. Diestel, H. Jarchow and A. Tonge, *Absolutely Summing Operators*, Chapter 3.
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace ContinuousLinearMap

variable {α 𝕜 H : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

variable (𝕜 H) in
/-- Grothendieck's inequality for `ι × κ` matrices over `𝕜` with constant `K` and vectors in `H`:
a matrix with scalar bound `C` has bilinear bound `K * C` on unit vectors of `H`. -/
private def MatrixInequality (ι κ : Type*) [Fintype ι] [Fintype κ] (K : ℝ) : Prop :=
  ∀ (a : Matrix ι κ 𝕜) {C : ℝ} (u : ι → H) (v : κ → H),
    (∀ (s : ι → 𝕜) (t : κ → 𝕜), (∀ i, ‖s i‖ ≤ 1) → (∀ j, ‖t j‖ ≤ 1) →
      ‖∑ i, ∑ j, a i j * s i * t j‖ ≤ C) → (∀ i, ‖u i‖ ≤ 1) → (∀ j, ‖v j‖ ≤ 1) →
    ‖∑ i, ∑ j, a i j * ⟪u i, v j⟫_𝕜‖ ≤ K * C

section Atoms

variable {κ : Type*} [Fintype κ] {A : κ → Set α} (hA : ∀ j, MeasurableSet (A j))
  (hAμ : ∀ j, μ (A j) ≠ ∞)

include hA hAμ in
/-- For `y i = ∑ j, c i j • 1_{A j}` over disjoint sets `A j` of finite measure, the matrix
`c i j * μ(A j)` has scalar bound the weak `L¹` norm of `y`. -/
private theorem norm_sum_sum_mul_measureReal_mul_mul_le {ι : Type*} [Fintype ι]
    (hd : Pairwise (Function.onFun Disjoint A)) (c : ι → κ → 𝕜) {s : ι → 𝕜} {t : κ → 𝕜}
    (hs : ∀ i, ‖s i‖ ≤ 1) (ht : ∀ j, ‖t j‖ ≤ 1) :
    ‖∑ i, ∑ j, c i j * μ.real (A j) * s i * t j‖ ≤ TauCeti.weakLpNorm (𝕜 := 𝕜) 1
      (fun i ↦ ∑ j, c i j • indicatorConstLp 1 (hA j) (hAμ j) (1 : 𝕜)) := by
  refine le_trans ?_ (TauCeti.norm_sum_smul_le_weakLpNorm_one _ hs)
  -- Regroup `∑ i, s i • y i` along the atoms and use the weighted `ℓ¹` norm.
  have hsy : ∑ i, s i • ∑ j, c i j • indicatorConstLp 1 (hA j) (hAμ j) (1 : 𝕜) =
      ∑ j, (∑ i, s i * c i j) • indicatorConstLp 1 (hA j) (hAμ j) (1 : 𝕜) := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hsy]
  simp only [← TauCeti.indicatorConstLp_smul, smul_eq_mul, mul_one]
  rw [TauCeti.norm_sum_indicatorConstLp_one hA hAμ hd, Finset.sum_comm]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  have hj : ∑ i, c i j * μ.real (A j) * s i * t j = μ.real (A j) * (∑ i, s i * c i j) * t j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hj, norm_mul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg measureReal_nonneg]
  exact mul_le_of_le_one_right (by positivity) (ht j)

include hA hAμ in
/-- The finite-atom case of Grothendieck's theorem, for any constant `K` in the matrix
inequality: families in the span of the indicator functions of finitely many disjoint sets of
finite measure satisfy the defining inequality of `1`-summing operators with constant
`K * ‖T‖`. -/
private theorem sum_norm_apply_sum_smul_indicatorConstLp_le {ι : Type*} [Fintype ι] {K : ℝ}
    (hK : MatrixInequality 𝕜 H ι κ K)
    (hd : Pairwise (Function.onFun Disjoint A)) (T : Lp 𝕜 1 μ →L[𝕜] H) (c : ι → κ → 𝕜) :
    ∑ i, ‖T (∑ j, c i j • indicatorConstLp 1 (hA j) (hAμ j) (1 : 𝕜))‖ ≤
      K * ‖T‖ * TauCeti.weakLpNorm (𝕜 := 𝕜) 1
        (fun i ↦ ∑ j, c i j • indicatorConstLp 1 (hA j) (hAμ j) (1 : 𝕜)) := by
  set e : κ → Lp 𝕜 1 μ := fun j ↦ indicatorConstLp 1 (hA j) (hAμ j) (1 : 𝕜)
  set y : ι → Lp 𝕜 1 μ := fun i ↦ ∑ j, c i j • e j with hy_def
  rcases (norm_nonneg T).eq_or_lt with hT | hT
  · simp [norm_eq_zero.1 hT.symm]
  have hne (j : κ) : ‖e j‖ = μ.real (A j) := by
    simp [e, norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top]
  -- The normalized columns `v j` of `T`.
  set v : κ → H := fun j ↦ ((μ.real (A j) * ‖T‖ : ℝ) : 𝕜)⁻¹ • T (e j) with hv_def
  have hTe (j : κ) : T (e j) = ((μ.real (A j) * ‖T‖ : ℝ) : 𝕜) • v j := by
    rcases eq_or_ne (μ.real (A j)) 0 with h | h
    · simp [h, norm_eq_zero.1 ((hne j).trans h)]
    · have hpos : (0 : ℝ) < μ.real (A j) * ‖T‖ := mul_pos (measureReal_nonneg.lt_of_ne' h) hT
      rw [hv_def, smul_inv_smul₀ (RCLike.ofReal_ne_zero.2 hpos.ne')]
  have hv (j : κ) : ‖v j‖ ≤ 1 := by
    rw [hv_def, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    refine inv_mul_le_one_of_le₀ ?_ (by positivity)
    exact (T.le_opNorm _).trans_eq (by rw [hne, mul_comm])
  -- The unit vectors `u i` norming the images `T (y i)`.
  set u : ι → H := fun i ↦ ((‖T (y i)‖ : ℝ) : 𝕜)⁻¹ • T (y i) with hu_def
  have hu (i : ι) : ‖u i‖ ≤ 1 := by
    rw [hu_def, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg _)
  have hTy (i : ι) : ((‖T (y i)‖ : ℝ) : 𝕜) =
      (‖T‖ : 𝕜) * ∑ j, (c i j * μ.real (A j)) * ⟪u i, v j⟫_𝕜 := by
    have hnorm : ((‖T (y i)‖ : ℝ) : 𝕜) = ⟪u i, T (y i)⟫_𝕜 := by
      rw [hu_def, inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, RCLike.conj_ofReal]
      rcases eq_or_ne ‖T (y i)‖ 0 with h | h
      · simp [h]
      · field_simp
    rw [hnorm, hy_def]
    simp only [map_sum, map_smul, hTe, inner_sum, inner_smul_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    ring
  calc
    ∑ i, ‖T (y i)‖ = ‖((∑ i, ‖T (y i)‖ : ℝ) : 𝕜)‖ := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)]
    _ = ‖T‖ * ‖∑ i, ∑ j, (c i j * μ.real (A j)) * ⟪u i, v j⟫_𝕜‖ := by
      rw [RCLike.ofReal_sum]
      simp only [hTy, ← Finset.mul_sum, norm_mul, RCLike.norm_ofReal, abs_norm]
    _ ≤ ‖T‖ * (K * TauCeti.weakLpNorm (𝕜 := 𝕜) 1 y) := by
      gcongr
      exact hK (fun i j ↦ c i j * μ.real (A j)) u v
        (fun s t hs ht ↦ norm_sum_sum_mul_measureReal_mul_mul_le hA hAμ hd c hs ht) hu hv
    _ = K * ‖T‖ * TauCeti.weakLpNorm (𝕜 := 𝕜) 1 y := by ring

end Atoms

/-- The case of families of simple functions, for any constant `K` in the matrix inequality: if
each `x i` is the `i`-th coordinate of an integrable simple function `G`, then the families lie in
the span of the indicator functions of the nonzero fibres of `G`. -/
private theorem sum_norm_apply_le_of_simpleFunc {ι : Type*} [Fintype ι] {K : ℝ}
    (hK : ∀ S : Finset (ι → 𝕜), MatrixInequality 𝕜 H ι S K)
    (T : Lp 𝕜 1 μ →L[𝕜] H) (G : SimpleFunc α (ι → 𝕜)) (hG : Integrable G μ)
    (x : ι → Lp 𝕜 1 μ) (hx : ∀ i, x i =ᵐ[μ] fun a ↦ G a i) :
    ∑ i, ‖T (x i)‖ ≤ K * ‖T‖ * TauCeti.weakLpNorm (𝕜 := 𝕜) 1 x := by
  set S : Finset (ι → 𝕜) := G.range.filter fun w ↦ w ≠ 0
  have hA (w : S) : MeasurableSet (G ⁻¹' {w.1}) := G.measurableSet_fiber _
  have hAμ (w : S) : μ (G ⁻¹' {w.1}) ≠ ∞ :=
    (G.measure_preimage_lt_top_of_integrable hG (Finset.mem_filter.1 w.2).2).ne
  have hd : Pairwise (Function.onFun Disjoint fun w : S ↦ G ⁻¹' {w.1}) := fun w w' hww' ↦
    (Set.disjoint_singleton.2 (Subtype.coe_injective.ne hww')).preimage G
  -- Each `x i` is the combination of the indicator functions of the fibres with coefficients
  -- the `i`-th coordinates of the values.
  have hrepr (i : ι) : x i = ∑ w : S, w.1 i • indicatorConstLp 1 (hA w) (hAμ w) (1 : 𝕜) := by
    rw [TauCeti.eq_sum_indicatorConstLp_fiber (φ := fun w ↦ w i)
      (fun a ha ↦ by simp [S, G.mem_range_self a] at ha; simp [ha]) hAμ (hx i)]
    simp only [← TauCeti.indicatorConstLp_smul, smul_eq_mul, mul_one]
  obtain rfl : x = _ := funext hrepr
  exact sum_norm_apply_sum_smul_indicatorConstLp_le hA hAμ (hK S) hd T fun i w ↦ w.1 i

/-- Grothendieck's theorem for `L¹` follows from any matrix inequality with a constant `K`, by
density of simple functions. -/
private theorem summingENorm_one_le_ofReal_mul_norm {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ (n : ℕ) (S : Finset (Fin n → 𝕜)), MatrixInequality 𝕜 H (Fin n) S K)
    (T : Lp 𝕜 1 μ →L[𝕜] H) :
    T.summingENorm 1 ≤ ENNReal.ofReal (K * ‖T‖) := by
  rw [summingENorm_le_ofReal_iff (mul_nonneg hK0 (norm_nonneg T))]
  intro n
  -- Both sides are continuous in the family, so it suffices to treat families of simple functions.
  refine (dense_pi Set.univ fun i _ ↦
    Lp.simpleFunc.dense (E := 𝕜) (μ := μ) ENNReal.one_ne_top).induction (fun x hx ↦ ?_)
    (isClosed_le ?_ (continuous_const.mul (TauCeti.continuous_weakLpNorm 1)))
  swap
  · exact continuous_norm.comp ((PiLp.continuous_toLp 1 _).comp
      (continuous_pi fun i ↦ T.continuous.comp (continuous_apply i)))
  -- The family `x` is given by the simple functions `g i`, jointly by `SimpleFunc.pi g`.
  set g : Fin n → SimpleFunc α 𝕜 := fun i ↦ Lp.simpleFunc.toSimpleFunc ⟨x i, hx i trivial⟩
  -- `g i` represents `x i`, the underlying `Lp` class of the subtype element `⟨x i, _⟩`.
  have hg (i : Fin n) : x i =ᵐ[μ] g i :=
    (Lp.simpleFunc.toSimpleFunc_eq_toFun ⟨x i, hx i trivial⟩).symm
  have hG : Integrable (SimpleFunc.pi g) μ := by
    rw [SimpleFunc.coe_pi]
    exact integrable_pi_iff.2 fun i ↦ memLp_one_iff_integrable.1 (Lp.simpleFunc.memLp _)
  rw [PiLp.norm_eq_of_L1]
  exact sum_norm_apply_le_of_simpleFunc (hK n) T (SimpleFunc.pi g) hG x fun i ↦ by
    simpa only [SimpleFunc.pi_apply] using hg i

/-- **Grothendieck's theorem.** Every bounded operator `T` from `L¹(μ)` into an inner product space
over an `RCLike` field is absolutely `1`-summing, with `π₁(T) ≤ 16 ‖T‖`. Over `ℝ`,
`ContinuousLinearMap.summingENorm_one_le_ofReal_eight_mul_norm` gives the constant `8`. -/
theorem summingENorm_one_le_ofReal_sixteen_mul_norm (T : Lp 𝕜 1 μ →L[𝕜] H) :
    T.summingENorm 1 ≤ ENNReal.ofReal (16 * ‖T‖) :=
  summingENorm_one_le_ofReal_mul_norm (by norm_num)
    (fun _ _ a _ _ _ ha hu hv ↦ a.norm_sum_sum_mul_inner_le_sixteen_mul ha hu hv) T

/-- **Grothendieck's theorem** over `ℝ`. Every bounded operator `T` from real `L¹(μ)` into a real
inner product space is absolutely `1`-summing, with `π₁(T) ≤ 8 ‖T‖`. -/
theorem summingENorm_one_le_ofReal_eight_mul_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : Lp ℝ 1 μ →L[ℝ] H) :
    T.summingENorm 1 ≤ ENNReal.ofReal (8 * ‖T‖) :=
  summingENorm_one_le_ofReal_mul_norm (by norm_num) (fun _ _ a _ _ _ ha hu hv ↦ by
    simpa only [Real.norm_eq_abs] using a.abs_sum_sum_mul_inner_le_eight_mul
      (fun s t hs ht ↦ by
        simpa only [Real.norm_eq_abs] using ha s t (by simpa using hs) (by simpa using ht))
      hu hv) T

end ContinuousLinearMap
