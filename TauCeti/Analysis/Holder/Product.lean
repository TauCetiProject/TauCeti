/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
import TauCeti.Analysis.Holder.Leibniz
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Products in bounded higher-order Hölder spaces

A continuous bilinear map acts pointwise on `CkHolderSpace`. For `α ≤ 1`, the lifted map
`ContinuousLinearMap.compCkHolder₂` is continuous bilinear, with operator norm at most
`(k + 7) * 2^k * ‖B‖`. In particular this supplies bounded multiplication by coefficients,
scalar multiplication, and application of operator-valued coefficient fields in every order.
The constant is not sharp; it is independent of the exponent, spaces and functions.

The norm is the existing sum of the supremum norms of all derivative fields and the Hölder
seminorm of the top field. We use Mathlib's bilinear Leibniz bound for the supremum terms and
`ContinuousLinearMap.holderWith_iteratedFDeriv_of_tsupport_subset_right` for the top seminorm.
Lower derivative fields have Hölder bounds from the mean value inequality.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §4.1.
-/

public section
noncomputable section

open scoped NNReal BoundedContinuousFunction
open TauCeti

namespace ContinuousLinearMap

variable {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ} {α : ℝ≥0}

private theorem norm_iteratedFDeriv_ckHolderBilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) {j : ℕ} (hj : j ≤ k)
    (x : X) :
    ‖iteratedFDeriv ℝ j (fun y ↦ B (f y) (g y)) x‖ ≤ 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  refine (B.norm_iteratedFDeriv_le_of_bilinear f.contDiff g.contDiff x
    (by exact_mod_cast hj)).trans ?_
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖f‖ * ‖g‖ := by
      gcongr with i hi
      · exact f.norm_iteratedFDeriv_apply_le (by have := Finset.mem_range.mp hi; omega) x
      · exact g.norm_iteratedFDeriv_apply_le ((Nat.sub_le j i).trans hj) x
    _ = 2 ^ j * ‖B‖ * ‖f‖ * ‖g‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hsum]
      ring
    _ ≤ _ := by gcongr; norm_num

private theorem holderWith_iteratedFDeriv_ckHolderBilinear (B : E →L[ℝ] F →L[ℝ] G)
    (hα : α ≤ 1) (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    HolderWith (6 * 2 ^ k * ‖B‖₊ * ‖f‖₊ * ‖g‖₊) α
      (iteratedFDeriv ℝ k (fun x ↦ B (f x) (g x))) := by
  have h := B.holderWith_iteratedFDeriv_of_tsupport_subset_right f.contDiff.contDiffOn
    g.contDiff isOpen_univ (Set.subset_univ _)
    (M := ‖f‖₊) (N := ‖g‖₊) (H := 3 * ‖f‖₊) (K := 3 * ‖g‖₊)
    (fun j hj x _ ↦ f.norm_iteratedFDeriv_apply_le hj x)
    (fun j hj x ↦ g.norm_iteratedFDeriv_apply_le hj x)
    (fun j hj ↦ (f.holderWith_iteratedFDeriv_of_le hα hj).holderOnWith Set.univ)
    (fun j hj ↦ g.holderWith_iteratedFDeriv_of_le hα hj)
  convert h using 1; ring

private def ckHolderBilinear (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) : CkHolderSpace k α X G :=
  CkHolderSpace.ofContDiff (fun x ↦ B (f x) (g x))
    (B.isBoundedBilinearMap.contDiff.comp (f.contDiff.prodMk g.contDiff))
    (fun _ hj ↦ ⟨2 ^ k * ‖B‖ * ‖f‖ * ‖g‖,
      norm_iteratedFDeriv_ckHolderBilinear_le B f g hj⟩)
    (holderWith_iteratedFDeriv_ckHolderBilinear B hα f g).memHolder

@[simp]
private theorem coe_ckHolderBilinear (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    ⇑(ckHolderBilinear B hα f g) = fun x ↦ B (f x) (g x) := by
  simp [ckHolderBilinear]

private theorem norm_ckHolderBilinear_le (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    ‖ckHolderBilinear B hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  have hfield (i : Fin (k + 1)) : ‖(ckHolderBilinear B hα f g).iteratedFDeriv i‖ ≤
      2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [← CkHolderSpace.iteratedFDeriv_eq, coe_ckHolderBilinear]
    exact norm_iteratedFDeriv_ckHolderBilinear_le B f g (by omega) x
  have htop : (nnHolderNorm α (iteratedFDeriv ℝ k (ckHolderBilinear B hα f g)) : ℝ) ≤
      6 * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
    rw [coe_ckHolderBilinear]
    exact_mod_cast (holderWith_iteratedFDeriv_ckHolderBilinear B hα f g).nnholderNorm_le
  rw [CkHolderSpace.norm_eq]
  calc
    _ ≤ (∑ _ : Fin (k + 1), 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖) +
        6 * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ :=
      add_le_add (Finset.sum_le_sum fun i _ ↦ hfield i) htop
    _ = _ := by simp; ring

private def ckHolderBilinearLinear (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1) :
    CkHolderSpace k α X E →ₗ[ℝ] CkHolderSpace k α X F →ₗ[ℝ] CkHolderSpace k α X G :=
  LinearMap.mk₂ ℝ (ckHolderBilinear B hα)
    (fun f₁ f₂ g ↦ CkHolderSpace.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpace.ext fun x ↦ by simp)
    (fun f g₁ g₂ ↦ CkHolderSpace.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpace.ext fun x ↦ by simp)

/-- Pointwise application of a continuous bilinear map to bounded `C^{k,α}` functions.
Fixing the first argument gives bounded multiplication by a coefficient field. -/
def compCkHolder₂ (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1) :
    CkHolderSpace k α X E →L[ℝ] CkHolderSpace k α X F →L[ℝ] CkHolderSpace k α X G :=
  (ckHolderBilinearLinear B hα).mkContinuous₂ ((k + 7) * 2 ^ k * ‖B‖)
    (norm_ckHolderBilinear_le B hα)

/-- The lifted bilinear operation is pointwise the original one. -/
@[simp]
theorem compCkHolder₂_apply (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) (x : X) :
    B.compCkHolder₂ hα f g x = B (f x) (g x) := by
  simp [compCkHolder₂, ckHolderBilinearLinear]

/-- The lifted bilinear map has an operator norm bound depending only on the order and `‖B‖`.
This estimate uses the supremum-plus-Hölder sum norm, not an equivalent renorming. -/
theorem norm_compCkHolder₂_le (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1) :
    ‖B.compCkHolder₂ (k := k) (X := X) hα‖ ≤ (k + 7) * 2 ^ k * ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- The order-`k` Hölder product estimate, with an explicit order-dependent constant. -/
theorem norm_compCkHolder₂_apply_le (B : E →L[ℝ] F →L[ℝ] G) (hα : α ≤ 1)
    (f : CkHolderSpace k α X E) (g : CkHolderSpace k α X F) :
    ‖B.compCkHolder₂ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ :=
  (B.compCkHolder₂ hα |>.le_opNorm₂ f g).trans (by
    gcongr
    exact B.norm_compCkHolder₂_le hα)

end ContinuousLinearMap
