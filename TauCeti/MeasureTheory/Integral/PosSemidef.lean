/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Integral.Matrix

/-!
# Integrals of positive-semidefinite and ordered matrices

Entrywise integrals of almost everywhere positive-semidefinite, Hermitian, and Loewner-ordered
families of real or complex matrices, together with almost-everywhere finite-sum order properties.

## Main results

* `TauCeti.posSemidef_integral`: the entrywise integral of an a.e. positive-semidefinite family of
  finite matrices over an `RCLike` field with integrable entries is positive semidefinite.
* `TauCeti.isHermitian_integral_of_ae_isHermitian`: entrywise expectation preserves the Hermitian
  property.
* `TauCeti.integral_le_integral_of_ae_le`: entrywise expectation is monotone in the Loewner order.
* `TauCeti.nonneg_of_integral_eq_zero_of_ae_le_smul_one`: an upper scalar bound `L • 1` on a
  zero-mean random matrix forces `0 ≤ L`.
* `TauCeti.ae_isHermitian_finsetSum`, `TauCeti.ae_posSemidef_finsetSum`, and
  `TauCeti.ae_sum_eq_zero_of_ae_posSemidef_of_ae_le_zero`: a.e. properties of finite matrix sums.
-/

public section

namespace TauCeti

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

/-- The **entrywise integral of positive-semidefinite matrices** is positive semidefinite: if
`M x` is positive semidefinite for almost every `x` and every entry of `M` is integrable, then the
matrix of entrywise integrals is positive semidefinite. -/
theorem posSemidef_integral {α ι 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [Finite ι]
    [RCLike 𝕜] {M : α → Matrix ι ι 𝕜} (hM : ∀ᵐ x ∂μ, (M x).PosSemidef)
    (hint : ∀ i j, Integrable (fun x => M x i j) μ) :
    (Matrix.of fun i j => ∫ x, M x i j ∂μ).PosSemidef := by
  have := Fintype.ofFinite ι
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · refine Matrix.IsHermitian.ext fun i j => ?_
    rw [Matrix.of_apply, Matrix.of_apply, RCLike.star_def, ← integral_conj]
    exact integral_congr_ae (hM.mono fun x hx => hx.isHermitian.apply i j)
  · have hquad : star c ⬝ᵥ ((Matrix.of fun i j => ∫ x, M x i j ∂μ) *ᵥ c) =
        ∫ x, star c ⬝ᵥ (M x *ᵥ c) ∂μ := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      rw [integral_finsetSum _ fun i _ =>
        (integrable_finsetSum _ fun j _ => (hint i j).mul_const (c j)).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const (c j)]
      simp only [integral_mul_const]
    rw [hquad]
    exact integral_nonneg_of_ae (hM.mono fun x hx => hx.dotProduct_mulVec_nonneg c)

/-- Entrywise expectation preserves the Hermitian property. -/
theorem isHermitian_integral_of_ae_isHermitian {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [RCLike 𝕜] {F : Ω → Matrix n n 𝕜} (hF : ∀ᵐ ω ∂P, (F ω).IsHermitian) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, of_apply, RCLike.star_def, ← integral_conj]
  refine integral_congr_ae (hF.mono fun ω hω ↦ ?_)
  simpa [conjTranspose_apply, RCLike.star_def] using congrFun (congrFun hω i) j

/-- Entrywise expectation is monotone in the Loewner order. -/
theorem integral_le_integral_of_ae_le {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [RCLike 𝕜] [Finite n] {F G : Ω → Matrix n n 𝕜} (hle : ∀ᵐ ω ∂P, F ω ≤ G ω)
    (hF : ∀ i j, Integrable (fun ω ↦ F ω i j) P)
    (hG : ∀ i j, Integrable (fun ω ↦ G ω i j) P) :
    (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) ≤ (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) := by
  have hsub : (Matrix.of fun i j ↦ ∫ ω, G ω i j ∂P) - (Matrix.of fun i j ↦ ∫ ω, F ω i j ∂P) =
      Matrix.of fun i j ↦ ∫ ω, (G ω - F ω) i j ∂P := by
    ext i j
    simp [integral_sub (hG i j) (hF i j)]
  rw [Matrix.le_iff, hsub]
  exact posSemidef_integral (hle.mono fun _ h ↦ Matrix.le_iff.1 h)
    fun i j ↦ (hG i j).sub (hF i j)

/-- If a zero-mean integrable random matrix on a nonempty index type satisfies `X ≤ L • 1` almost
everywhere, then `0 ≤ L`. -/
theorem nonneg_of_integral_eq_zero_of_ae_le_smul_one {Ω 𝕜 n : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [RCLike 𝕜] [Finite n] [DecidableEq n] [Nonempty n]
    {X : Ω → Matrix n n 𝕜} (hX : ∀ i j, Integrable (fun ω ↦ X ω i j) P)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂P = 0)
    {L : ℝ} (hupper : ∀ᵐ ω ∂P, X ω ≤ L • (1 : Matrix n n 𝕜)) :
    0 ≤ L := by
  have h0 : (0 : Matrix n n 𝕜) = Matrix.of fun i j ↦ ∫ ω, X ω i j ∂P := by
    ext i j; simp [hmean]
  have hL_int : L • (1 : Matrix n n 𝕜) =
      Matrix.of fun i j ↦ ∫ _ω, (L • (1 : Matrix n n 𝕜)) i j ∂P := by
    ext i j; simp
  have hle : (0 : Matrix n n 𝕜) ≤ L • (1 : Matrix n n 𝕜) := by
    rw [h0, hL_int]
    exact integral_le_integral_of_ae_le hupper hX fun _ _ ↦ integrable_const _
  simpa [RCLike.smul_re] using
    (RCLike.nonneg_iff.1 ((Matrix.le_iff.1 hle).diag_nonneg (i := Classical.arbitrary n))).1

/-- A finite sum of a.e. Hermitian random matrices is a.e. Hermitian. -/
theorem ae_isHermitian_finsetSum {Ω ι n R : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [AddCommMonoid R] [StarAddMonoid R] {s : Finset ι} {X : ι → Ω → Matrix n n R}
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian) :
    ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).IsHermitian :=
  (Filter.eventually_all_finset s).2 hherm |>.mono fun _ hω ↦
    (isSelfAdjoint_sum s fun k hk ↦ (hω k hk).isSelfAdjoint).isHermitian

/-- A finite sum of a.e. positive semidefinite random matrices is a.e. positive semidefinite. -/
theorem ae_posSemidef_finsetSum {Ω ι n R : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R] {s : Finset ι}
    {X : ι → Ω → Matrix n n R} (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).PosSemidef) :
    ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).PosSemidef :=
  (Filter.eventually_all_finset s).2 hpsd |>.mono fun _ hω ↦ Matrix.posSemidef_sum s hω

/-- A finite family of a.e. positive semidefinite, a.e. nonpositive random matrices has zero sum
almost everywhere. -/
theorem ae_sum_eq_zero_of_ae_posSemidef_of_ae_le_zero {Ω ι n 𝕜 : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [RCLike 𝕜] {s : Finset ι}
    {Y : ι → Ω → Matrix n n 𝕜} (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) :
    ∀ᵐ ω ∂P, ∑ k ∈ s, Y k ω = 0 :=
  ((ae_ball_iff s.countable_toSet).2 fun k hk ↦ (hpsd k hk).and (hupper k hk)).mono fun _ hω ↦
    Finset.sum_eq_zero fun k hk ↦ le_antisymm (hω k hk).2 (hω k hk).1.nonneg

end TauCeti
