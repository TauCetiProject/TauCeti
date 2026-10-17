/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Fourier.Hardy.Basic
public import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# Toeplitz operators on boundary Hardy space

For an essentially bounded symbol `a` on `UnitAddCircle`, the Toeplitz operator `T_a` is the
compression `P M_a |H²` of the multiplication operator `M_a` on circle `L²` to the boundary Hardy
space `H²`, where `P` is the orthogonal projection onto `H²`. This file bundles the symbol map
`a ↦ T_a` as a bounded complex-linear map `TauCeti.toeplitz` and proves its basic properties:

* `TauCeti.inner_hardyBasis_toeplitz_hardyBasis`: in the Hardy basis `e₀, e₁, …` the matrix
  entry `(i, j)` of `T_a` is the Fourier coefficient `â(i - j)`;
* `TauCeti.adjoint_toeplitz`: the adjoint of `T_a` is the Toeplitz operator of the complex
  conjugate symbol;
* `TauCeti.toeplitz_const`: a constant symbol acts by scalar multiplication;
* `TauCeti.norm_toeplitz_le`: the operator norm of `T_a` is at most `‖a‖∞`;
* `TauCeti.toeplitz_injective`: a symbol is determined by its Toeplitz operator.

The conventions are those of Conway, *A Course in Functional Analysis*, second edition, and of
E. Park, *Toeplitz operators*: normalized Haar measure, the modes `exp (2πint)` and inner products
conjugate linear in the first variable.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Compressing multiplication by `a` to Hardy space does not increase the operator norm. -/
private theorem norm_compress_multiplicationOperator_le
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖hardySubmodule.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
      hardySubmodule.subtypeL‖ ≤ ‖a‖ := by
  calc _ ≤ ‖hardySubmodule.orthogonalProjectionOnto‖ *
        (‖Lp.multiplicationOperator (E := ℂ) a‖ * ‖hardySubmodule.subtypeL‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖a‖ * 1) := by
        gcongr
        · exact hardySubmodule.orthogonalProjectionOnto_norm_le
        · exact Lp.norm_multiplicationOperator_le a
        · exact Submodule.norm_subtypeL_le _
    _ = ‖a‖ := by ring

/-- The Toeplitz operator map, sending an essentially bounded symbol `a` on the unit circle to the
compression `T_a = P M_a |H²` of multiplication by `a` to boundary Hardy space. -/
def toeplitz :
    Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)) →L[ℂ] HardySpace →L[ℂ] HardySpace :=
  LinearMap.mkContinuous
    { toFun a := hardySubmodule.orthogonalProjectionOnto ∘L Lp.multiplicationOperator a ∘L
        hardySubmodule.subtypeL
      map_add' a b := by
        simp only [Lp.multiplicationOperator_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c a := by
        simp only [Lp.multiplicationOperator_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    1 fun a ↦ (one_mul ‖a‖).symm ▸ norm_compress_multiplicationOperator_le a

/-- The Toeplitz operator of `a` compresses the multiplication operator of `a` to Hardy space. -/
theorem toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    toeplitz a = hardySubmodule.orthogonalProjectionOnto ∘L
      Lp.multiplicationOperator a ∘L hardySubmodule.subtypeL :=
  (rfl)

/-- The ambient value of `T_a f` is the Hardy projection of the product `a f`. -/
theorem coe_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (f : HardySpace) :
    (toeplitz a f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      hardySubmodule.starProjection (a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) := by
  rw [toeplitz_apply, Submodule.starProjection_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Lp.multiplicationOperator_apply]

/-- Compressing to Hardy space does not change inner products against Hardy functions. -/
theorem inner_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f g : HardySpace) :
    ⟪f, toeplitz a g⟫_ℂ =
      ⟪(f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))),
        a • (g : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))⟫_ℂ := by
  rw [toeplitz_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, Submodule.subtypeL_apply,
    Lp.multiplicationOperator_apply]

/-- The Hardy coordinates of `T_a f` are the nonnegative Fourier coefficients of `a f`. -/
@[simp]
theorem hardyBasis_repr_toeplitz_apply (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (f : HardySpace) (i : ℕ) :
    hardyBasis.repr (toeplitz a f) i =
      fourierCoeff (a • (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) (i : ℤ) := by
  rw [HilbertBasis.repr_apply_apply, inner_toeplitz_apply, coe_hardyBasis,
    ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

/-- **Matrix formula.** In the Hardy basis `e₀, e₁, …`, the `(i, j)` entry of the Toeplitz
operator `T_a` is the Fourier coefficient `â(i - j)`. -/
theorem inner_hardyBasis_toeplitz_hardyBasis (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))
    (i j : ℕ) :
    ⟪hardyBasis i, toeplitz a (hardyBasis j)⟫_ℂ = fourierCoeff a ((i : ℤ) - j) := by
  rw [← HilbertBasis.repr_apply_apply, hardyBasis_repr_toeplitz_apply, coe_hardyBasis,
    fourierCoeff_smul_fourierBasis]

/-- The adjoint of the Toeplitz operator `T_a` is the Toeplitz operator of the complex conjugate
symbol. -/
@[simp]
theorem adjoint_toeplitz (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ContinuousLinearMap.adjoint (toeplitz a) = toeplitz (star a) := by
  rw [toeplitz_apply, toeplitz_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, Lp.adjoint_multiplicationOperator,
    ContinuousLinearMap.comp_assoc]

/-- A constant symbol acts on Hardy space by scalar multiplication. -/
@[simp]
theorem toeplitz_const (c : ℂ) :
    toeplitz (Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) c) =
      c • ContinuousLinearMap.id ℂ HardySpace := by
  ext f : 2
  rw [coe_toeplitz_apply, ← Lp.multiplicationOperator_apply, Lp.multiplicationOperator_const]
  simp [Submodule.starProjection_eq_self_iff.mpr (hardySubmodule.smul_mem c f.property)]

/-- The operator norm of the Toeplitz operator `T_a` is at most the `L∞` norm of its symbol. -/
theorem norm_toeplitz_le (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    ‖toeplitz a‖ ≤ ‖a‖ :=
  norm_compress_multiplicationOperator_le a

/-- A symbol is determined by its Toeplitz operator: all its Fourier coefficients occur as
matrix entries, and the Fourier modes form a Hilbert basis of circle `L²`. -/
theorem toeplitz_injective : Function.Injective toeplitz := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  -- Every integer is a difference of natural numbers, so all Fourier coefficients of `a` vanish.
  have hcoeff (n : ℤ) : fourierCoeff a n = 0 := by
    have hn : n = (n.toNat : ℤ) - ((-n).toNat : ℤ) := by omega
    rw [hn, ← inner_hardyBasis_toeplitz_hardyBasis, ha, zero_apply, inner_zero_right]
  -- Hence the `L²` function `a e₀` has no Fourier coefficients and vanishes.
  have hzero :
      (a • fourierBasis (T := 1) 0 : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) = 0 := by
    apply (fourierBasis (T := 1)).repr.injective
    ext n
    rw [fourierBasis_repr, fourierCoeff_smul_fourierBasis, sub_zero, hcoeff, map_zero,
      lp.coeFn_zero, Pi.zero_apply]
  -- Since `e₀ = 1`, the symbol `a` itself vanishes almost everywhere.
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := 2) a (fourierBasis (T := 1) 0),
    coeFn_fourierLp (T := 1) 2 0, Lp.coeFn_zero ℂ 2 (AddCircle.haarAddCircle (T := 1)),
    Lp.coeFn_zero ℂ ∞ (AddCircle.haarAddCircle (T := 1))] with x hx h0 hz hz'
  rw [hzero] at hx
  rw [hz', Pi.zero_apply]
  rw [hz, Pi.zero_apply, Pi.smul_apply', coe_fourierBasis, h0, fourier_zero,
    smul_eq_mul, mul_one] at hx
  exact hx.symm

end TauCeti
