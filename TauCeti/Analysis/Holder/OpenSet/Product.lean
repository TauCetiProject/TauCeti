/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
import TauCeti.Analysis.Holder.Leibniz
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Products in the Hölder spaces `C^{k,α}(Ω)` on a convex open set

A continuous bilinear map `B` acts pointwise on the Hölder spaces `C^{k,α}(Ω)` of a convex open
set `Ω`. For `α ≤ 1` the lifted map `ContinuousLinearMap.compCkHolderOn₂` is continuous bilinear,
with operator norm at most `(k + 7) * 2^k * ‖B‖`, the constant of the whole-space estimate
`ContinuousLinearMap.norm_compCkHolder₂_le`. This is the order-`k` Leibniz estimate in the sum
norm `∑_{i ≤ k} sup_Ω ‖D^i f‖ + [D^k f]_{α,Ω}`: for the multiplication of a normed algebra it
says that the norm is submultiplicative up to a constant depending only on `k`, and fixing the
first argument gives bounded multiplication by a coefficient field in `C^{k,α}(Ω)`.

The supremum terms come from Mathlib's bilinear Leibniz bound
`ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`, and the top Hölder seminorm from
`ContinuousLinearMap.holderOnWith_iteratedFDeriv_comp₂`. The latter needs Hölder bounds for the
lower derivatives of both factors, which `CkHolderSpaceOn.holderOnWith_iteratedFDeriv_of_le`
supplies on a convex set. Some geometric condition on `Ω` is needed for `k ≥ 1`: on
`Ω = (-1, 0) ∪ (0, 1)` the function that is `0` on `(-1, 0)` and `1` on `(0, 1)` and the identity
both lie in `C^{1,α}(Ω)`, but the derivative of their product jumps from `0` to `1` across the gap,
so for `α > 0` the product is not in `C^{1,α}(Ω)`.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*, §4.1.
-/

public section
noncomputable section

open scoped NNReal
open TauCeti

namespace ContinuousLinearMap

variable {E F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] {k : ℕ} {α : ℝ≥0}
  {Ω : TopologicalSpace.Opens E}

private theorem norm_iteratedFDeriv_ckHolderOnBilinear_le (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (f : CkHolderSpaceOn k α Ω F₁) (g : CkHolderSpaceOn k α Ω F₂) {j : ℕ} (hj : j ≤ k)
    (x : Ω) :
    ‖iteratedFDeriv ℝ j (fun y ↦ B (f.extend y) (g.extend y)) x‖ ≤
      2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  rw [← iteratedFDerivWithin_of_isOpen j Ω.isOpen x.2]
  refine (B.norm_iteratedFDerivWithin_le_of_bilinear f.contDiffOn_extend g.contDiffOn_extend
    Ω.isOpen.uniqueDiffOn x.2 (by exact_mod_cast hj)).trans ?_
  calc
    _ ≤ ‖B‖ * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖f‖ * ‖g‖ := by
      gcongr with i hi
      · rw [iteratedFDerivWithin_of_isOpen i Ω.isOpen x.2]
        exact f.norm_iteratedFDeriv_extend_le (by have := Finset.mem_range.mp hi; omega) x
      · rw [iteratedFDerivWithin_of_isOpen (j - i) Ω.isOpen x.2]
        exact g.norm_iteratedFDeriv_extend_le ((Nat.sub_le j i).trans hj) x
    _ = 2 ^ j * ‖B‖ * ‖f‖ * ‖g‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hsum]
      ring
    _ ≤ _ := by gcongr; norm_num

private theorem holderOnWith_iteratedFDeriv_ckHolderOnBilinear (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω F₁)
    (g : CkHolderSpaceOn k α Ω F₂) :
    HolderOnWith (6 * 2 ^ k * ‖B‖₊ * ‖f‖₊ * ‖g‖₊) α
      (iteratedFDeriv ℝ k (fun y ↦ B (f.extend y) (g.extend y))) Ω := by
  have h := B.holderOnWith_iteratedFDeriv_comp₂ f.contDiffOn_extend g.contDiffOn_extend
    Ω.isOpen (M := ‖f‖₊) (N := ‖g‖₊) (H := 3 * ‖f‖₊) (K := 3 * ‖g‖₊)
    (fun j hj x hx ↦ f.norm_iteratedFDeriv_extend_le hj ⟨x, hx⟩)
    (fun j hj x hx ↦ g.norm_iteratedFDeriv_extend_le hj ⟨x, hx⟩)
    (fun j hj ↦ f.holderOnWith_iteratedFDeriv_of_le hconv hα f.extend_apply hj)
    (fun j hj ↦ g.holderOnWith_iteratedFDeriv_of_le hconv hα g.extend_apply hj)
  convert h using 1
  ring

private def ckHolderOnBilinear (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hconv : Convex ℝ (Ω : Set E))
    (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω F₁) (g : CkHolderSpaceOn k α Ω F₂) :
    CkHolderSpaceOn k α Ω F₃ :=
  CkHolderSpaceOn.ofContDiffOn (fun y ↦ B (f.extend y) (g.extend y))
    (B.isBoundedBilinearMap.contDiff.comp_contDiffOn
      (f.contDiffOn_extend.prodMk g.contDiffOn_extend))
    (fun _ hj ↦ ⟨2 ^ k * ‖B‖ * ‖f‖ * ‖g‖, norm_iteratedFDeriv_ckHolderOnBilinear_le B f g hj⟩)
    (HolderWith.memHolder fun x y ↦
      holderOnWith_iteratedFDeriv_ckHolderOnBilinear B hconv hα f g x x.2 y y.2)

@[simp]
private theorem coe_ckHolderOnBilinear (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω F₁)
    (g : CkHolderSpaceOn k α Ω F₂) :
    ⇑(ckHolderOnBilinear B hconv hα f g) = fun x ↦ B (f x) (g x) := by
  ext x
  simp [ckHolderOnBilinear]

private theorem norm_ckHolderOnBilinear_le (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω F₁)
    (g : CkHolderSpaceOn k α Ω F₂) :
    ‖ckHolderOnBilinear B hconv hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  refine (CkHolderSpaceOn.norm_le_sum_add_of_norm_iteratedFDeriv_le_of_holderWith
    (M := fun _ ↦ 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖) (fun _ ↦ by positivity) (fun i x ↦ ?_)
    (K := 6 * 2 ^ k * ‖B‖₊ * ‖f‖₊ * ‖g‖₊) (fun x y ↦ ?_)).trans_eq ?_
  · rw [ckHolderOnBilinear, CkHolderSpaceOn.iteratedFDeriv_ofContDiffOn]
    exact norm_iteratedFDeriv_ckHolderOnBilinear_le B f g (Nat.lt_succ_iff.mp i.2) x
  · rw [ckHolderOnBilinear, CkHolderSpaceOn.iteratedFDeriv_ofContDiffOn,
      CkHolderSpaceOn.iteratedFDeriv_ofContDiffOn]
    exact holderOnWith_iteratedFDeriv_ckHolderOnBilinear B hconv hα f g x x.2 y y.2
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

private def ckHolderOnBilinearLinear (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderSpaceOn k α Ω F₁ →ₗ[ℝ] CkHolderSpaceOn k α Ω F₂ →ₗ[ℝ] CkHolderSpaceOn k α Ω F₃ :=
  LinearMap.mk₂ ℝ (ckHolderOnBilinear B hconv hα)
    (fun f₁ f₂ g ↦ CkHolderSpaceOn.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpaceOn.ext fun x ↦ by simp)
    (fun f g₁ g₂ ↦ CkHolderSpaceOn.ext fun x ↦ by simp)
    (fun c f g ↦ CkHolderSpaceOn.ext fun x ↦ by simp)

/-- Pointwise application of a continuous bilinear map to elements of the Hölder spaces
`C^{k,α}(Ω)` of a convex open set, for `α ≤ 1`. Fixing the first argument gives bounded
multiplication by a coefficient field in `C^{k,α}(Ω)`. -/
def compCkHolderOn₂ (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderSpaceOn k α Ω F₁ →L[ℝ] CkHolderSpaceOn k α Ω F₂ →L[ℝ] CkHolderSpaceOn k α Ω F₃ :=
  (ckHolderOnBilinearLinear B hconv hα).mkContinuous₂ ((k + 7) * 2 ^ k * ‖B‖)
    (norm_ckHolderOnBilinear_le B hconv hα)

/-- The lifted bilinear operation on `C^{k,α}(Ω)` is pointwise the original one. -/
@[simp]
theorem compCkHolderOn₂_apply (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hconv : Convex ℝ (Ω : Set E))
    (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω F₁) (g : CkHolderSpaceOn k α Ω F₂) (x : Ω) :
    B.compCkHolderOn₂ hconv hα f g x = B (f x) (g x) := by
  simp [compCkHolderOn₂, ckHolderOnBilinearLinear]

/-- The lifted bilinear map on `C^{k,α}(Ω)` has operator norm at most `(k + 7) * 2^k * ‖B‖`,
for the sum norm of `C^{k,α}(Ω)`. -/
theorem norm_compCkHolderOn₂_le (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (hconv : Convex ℝ (Ω : Set E))
    (hα : α ≤ 1) : ‖B.compCkHolderOn₂ (k := k) hconv hα‖ ≤ (k + 7) * 2 ^ k * ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- The order-`k` product estimate in `C^{k,α}(Ω)` on a convex open set:
`‖B (f, g)‖ ≤ (k + 7) * 2^k * ‖B‖ * ‖f‖ * ‖g‖` in the sum norm. -/
theorem norm_compCkHolderOn₂_apply_le (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hconv : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn k α Ω F₁)
    (g : CkHolderSpaceOn k α Ω F₂) :
    ‖B.compCkHolderOn₂ hconv hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ :=
  (B.compCkHolderOn₂ hconv hα |>.le_opNorm₂ f g).trans (by
    gcongr
    exact B.norm_compCkHolderOn₂_le hconv hα)

end ContinuousLinearMap
