/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Laplacian as a contraction of iterated derivatives

On a finite-dimensional real inner product space `E` with standard orthonormal basis `(eᵢ)`, the
contraction of the last two arguments of an `(n + 2)`-multilinear map,

`A ↦ (v ↦ ∑ᵢ A (v, eᵢ, eᵢ))`,

is a continuous linear map `TauCeti.traceLastTwoL` from `(n + 2)`-multilinear to `n`-multilinear
maps. It computes the derivatives of a Laplacian from those of the function: for `f` of class
`C^(m + 2)`,

`D^m (Δ f) x = traceLastTwoL (D^(m + 2) f x)`

(`ContDiff.iteratedFDeriv_laplacian`), and since the Laplacian commutes with derivatives
(`ContDiff.laplacian_iteratedFDeriv`), also `Δ (D^m f) x = traceLastTwoL (D^(m + 2) f x)`
(`ContDiff.laplacian_iteratedFDeriv_eq_traceLastTwoL`). Iterating, the `r`-fold contraction
`TauCeti.iteratedTraceLastTwoL r m` sends `D^(m + 2r) f x` to `D^m (Δ^[r] f) x`
(`ContDiff.iteratedFDeriv_iterate_laplacian`), and `Δ^[r]` loses `2r` derivatives
(`ContDiff.iterate_laplacian`).

Being continuous and linear, the contraction carries bounds, continuity and Hölder estimates of
`D^(m + 2r) f` over to `D^m (Δ^[r] f)`. This is how the time derivatives `∂ₜ^r D^m u = D^m Δ^r u`
of solutions of the heat equation are controlled by their spatial derivatives.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F) in
/-- The contraction `A ↦ (v ↦ ∑ᵢ A (v, eᵢ, eᵢ))` of the last two arguments of an
`(n + 2)`-multilinear map in the standard orthonormal basis `(eᵢ)` of `E`, as a continuous linear
map. It is `traceL` applied after separating the last two arguments. -/
def traceLastTwoL (n : ℕ) : (E [×(n + 2)]→L[ℝ] F) →L[ℝ] (E [×n]→L[ℝ] F) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n ↦ E)
      (E →L[ℝ] E →L[ℝ] F) F traceL).comp
    (((continuousMultilinearCurryRightEquiv' ℝ n E (E →L[ℝ] F)).toContinuousLinearEquiv :
        (E [×(n + 1)]→L[ℝ] E →L[ℝ] F) →L[ℝ] (E [×n]→L[ℝ] E →L[ℝ] E →L[ℝ] F)).comp
      ((continuousMultilinearCurryRightEquiv' ℝ (n + 1) E F).toContinuousLinearEquiv :
        (E [×(n + 2)]→L[ℝ] F) →L[ℝ] (E [×(n + 1)]→L[ℝ] E →L[ℝ] F)))

/-- The contraction of the last two arguments is the sum of the values with the last two
arguments both equal to a vector of the standard orthonormal basis. -/
@[simp]
theorem traceLastTwoL_apply {n : ℕ} (A : E [×(n + 2)]→L[ℝ] F) (v : Fin n → E) :
    traceLastTwoL E F n A v = ∑ i, A (Fin.snoc (Fin.snoc v (stdOrthonormalBasis ℝ E i))
      (stdOrthonormalBasis ℝ E i)) := by
  simp [traceLastTwoL, traceL_apply]

variable (E F) in
/-- The `r`-fold contraction `traceLastTwoL`, from `(m + 2r)`-multilinear maps to `m`-multilinear
maps: it sends `D^(m + 2r) f x` to `D^m (Δ^[r] f) x` (`ContDiff.iteratedFDeriv_iterate_laplacian`).
-/
def iteratedTraceLastTwoL : (r m : ℕ) → (E [×(m + 2 * r)]→L[ℝ] F) →L[ℝ] (E [×m]→L[ℝ] F)
  | 0, _ => ContinuousLinearMap.id ℝ _
  | r + 1, m => (iteratedTraceLastTwoL r m).comp (traceLastTwoL E F (m + 2 * r))

@[simp]
theorem iteratedTraceLastTwoL_zero (m : ℕ) :
    iteratedTraceLastTwoL E F 0 m = ContinuousLinearMap.id ℝ _ :=
  (rfl)

theorem iteratedTraceLastTwoL_succ (r m : ℕ) :
    iteratedTraceLastTwoL E F (r + 1) m =
      (iteratedTraceLastTwoL E F r m).comp (traceLastTwoL E F (m + 2 * r)) :=
  (rfl)

/-- **Derivatives of the Laplacian.** For `f` of class `C^(m + 2)`, the `m`-th derivative of
`Δ f` is the contraction of the last two arguments of the `(m + 2)`-th derivative of `f`. -/
theorem _root_.ContDiff.iteratedFDeriv_laplacian {f : E → F} {m : ℕ} (hf : ContDiff ℝ (m + 2) f)
    (x : E) :
    iteratedFDeriv ℝ m (Δ f) x = traceLastTwoL E F m (iteratedFDeriv ℝ (m + 2) f x) := by
  have hD : ContDiff ℝ m (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := (m + 1 : ℕ)) (by norm_cast)).fderiv_right le_rfl
  have hΔ : Δ f = traceL ∘ fderiv ℝ (fderiv ℝ f) := funext (laplacian_eq_traceL f)
  rw [hΔ, traceL.iteratedFDeriv_comp_left hD.contDiffAt le_rfl]
  ext v
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    traceL_apply, traceLastTwoL_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]

/-- **The Laplacian of a derivative.** For `f` of class `C^(m + 2)`, the Laplacian of `D^m f` is
the contraction of the last two arguments of `D^(m + 2) f`. -/
theorem _root_.ContDiff.laplacian_iteratedFDeriv_eq_traceLastTwoL {f : E → F} {m : ℕ}
    (hf : ContDiff ℝ (m + 2) f) (x : E) :
    Δ (iteratedFDeriv ℝ m f) x = traceLastTwoL E F m (iteratedFDeriv ℝ (m + 2) f x) := by
  rw [hf.laplacian_iteratedFDeriv, hf.iteratedFDeriv_laplacian]

/-- **Derivatives of iterated Laplacians.** For `f` of class `C^(m + 2r)`, the `m`-th derivative
of `Δ^[r] f` is the `r`-fold contraction of the `(m + 2r)`-th derivative of `f`. -/
theorem _root_.ContDiff.iteratedFDeriv_iterate_laplacian {f : E → F} {r m : ℕ}
    (hf : ContDiff ℝ (m + 2 * r) f) (x : E) :
    iteratedFDeriv ℝ m (Δ^[r] f) x =
      iteratedTraceLastTwoL E F r m (iteratedFDeriv ℝ (m + 2 * r) f x) := by
  induction r generalizing f with
  | zero => rfl
  | succ r ih =>
    have hf' : ContDiff ℝ (m + 2 * r + 2) f := by simpa [mul_add, add_assoc] using hf
    rw [Function.iterate_succ_apply,
      ih (hf'.laplacian (by norm_cast)), hf'.iteratedFDeriv_laplacian, iteratedTraceLastTwoL_succ,
      ContinuousLinearMap.comp_apply]
    -- The two sides differ only in the order `m + 2 * (r + 1)` versus `m + 2 * r + 2`, which
    -- agree definitionally (`Nat.mul_succ`, `Nat.add_assoc`); `rfl` unfolds that arithmetic.
    rfl

/-- **Regularity of iterated Laplacians.** The `r`-fold Laplacian loses `2r` derivatives: for `f`
of class `C^n` and `m + 2r ≤ n`, `Δ^[r] f` is of class `C^m`. -/
theorem _root_.ContDiff.iterate_laplacian {n m : WithTop ℕ∞} {f : E → F} {r : ℕ}
    (hf : ContDiff ℝ n f) (hm : m + 2 * r ≤ n) : ContDiff ℝ m (Δ^[r] f) := by
  induction r generalizing m with
  | zero => exact hf.of_le (by simpa using hm)
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    refine (ih (m := m + 2) ?_).laplacian le_rfl
    refine le_trans (le_of_eq ?_) hm
    push_cast
    ring

end TauCeti
