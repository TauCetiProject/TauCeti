/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Open.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.Holder.Leibniz
import TauCeti.Analysis.Holder.Open.Inclusion

/-!
# Bilinear products, scalar multiplication, and algebra multiplication on `C^{k,α}(Ω)`

On a convex open set `Ω` and for `α ≤ 1`, a continuous bilinear map `B : E₁ →L[ℝ] E₂ →L[ℝ] G` acts
pointwise on `CkHolderOnSpace k α Ω` as a continuous bilinear map
`ContinuousLinearMap.compCkHolderOn₂` of operator norm at most `(k + 7) * 2 ^ k * ‖B‖`, adapting
`ContinuousLinearMap.compCkHolder₂` to open domains. Specializing `B` to
`ContinuousLinearMap.lsmul` and `ContinuousLinearMap.mul` yields bounded pointwise scalar
multiplication `TauCeti.CkHolderOnSpace.smulL` and bounded pointwise algebra multiplication
`TauCeti.CkHolderOnSpace.mulL`.

Both hypotheses `Convex ℝ (Ω : Set X)` and `α ≤ 1` enter through the lower-order Hölder estimate
`TauCeti.CkHolderOnSpace.holderOnWith_iteratedFDeriv_extendByZero_of_le`, needed for the cross
terms in the `k`-th order Leibniz rule `ContinuousLinearMap.holderOnWith_iteratedFDeriv_comp₂`.
Neither hypothesis can be omitted in general: on the disconnected open set `(-1, 0) ∪ (0, 1)`, the
locally constant sign function and `x ↦ x` both lie in `C^{1,1}`, whereas their product `x ↦ |x|`
has derivative jumping across `0` and leaves `C^{1,1}`; on `(-1, 1)` with `α = 2`, `x ↦ x` lies in
`C^{1,2}`, whereas its square `x ↦ x ^ 2` has nonconstant derivative `2 x` and leaves `C^{1,2}`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1.
-/

public section

noncomputable section

open scoped NNReal
open TauCeti

namespace ContinuousLinearMap

variable {X E₁ E₂ G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Ω : TopologicalSpace.Opens X}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {k : ℕ} {α : ℝ≥0}

private theorem norm_iteratedFDeriv_ckHolderOnBilinear_le (B : E₁ →L[ℝ] E₂ →L[ℝ] G)
    (f : CkHolderOnSpace k α Ω E₁) (g : CkHolderOnSpace k α Ω E₂) {j : ℕ} (hj : j ≤ k)
    {x : X} (hx : x ∈ Ω) :
    ‖iteratedFDeriv ℝ j (fun y ↦ B (f.extendByZero y) (g.extendByZero y)) x‖ ≤
      2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  have hjk : ((j : ENat) : WithTop ENat) ≤ k := by exact_mod_cast hj
  refine (B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le Ω.isOpen hx
    (f.contDiffOn_extendByZero.of_le hjk) (g.contDiffOn_extendByZero.of_le hjk)
    (fun i hi ↦ f.norm_iteratedFDeriv_extendByZero_le (hi.trans hj) ⟨x, hx⟩)
    (fun i hi ↦ g.norm_iteratedFDeriv_extendByZero_le (hi.trans hj) ⟨x, hx⟩)).trans ?_
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hj
  calc ‖B‖ * 2 ^ j * ‖f‖ * ‖g‖ ≤ ‖B‖ * 2 ^ k * ‖f‖ * ‖g‖ := by gcongr
    _ = 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by ring

private theorem holderOnWith_iteratedFDeriv_ckHolderOnBilinear (B : E₁ →L[ℝ] E₂ →L[ℝ] G)
    (hΩ : Convex ℝ (Ω : Set X)) (hα : α ≤ 1)
    (f : CkHolderOnSpace k α Ω E₁) (g : CkHolderOnSpace k α Ω E₂) :
    HolderOnWith (6 * 2 ^ k * ‖B‖₊ * ‖f‖₊ * ‖g‖₊) α
      (iteratedFDeriv ℝ k (fun y ↦ B (f.extendByZero y) (g.extendByZero y))) (Ω : Set X) := by
  have h := B.holderOnWith_iteratedFDeriv_comp₂ f.contDiffOn_extendByZero g.contDiffOn_extendByZero
    Ω.isOpen
    (M := ‖f‖₊) (N := ‖g‖₊) (H := 3 * ‖f‖₊) (K := 3 * ‖g‖₊)
    (fun _ hj x hx ↦ f.norm_iteratedFDeriv_extendByZero_le hj ⟨x, hx⟩)
    (fun _ hj x hx ↦ g.norm_iteratedFDeriv_extendByZero_le hj ⟨x, hx⟩)
    (fun _ hj ↦ f.holderOnWith_iteratedFDeriv_extendByZero_of_le hΩ hα hj)
    (fun _ hj ↦ g.holderOnWith_iteratedFDeriv_extendByZero_of_le hΩ hα hj)
  exact h.mono_const (le_of_eq (by ring))

private def ckHolderOnBilinear (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) (f : CkHolderOnSpace k α Ω E₁) (g : CkHolderOnSpace k α Ω E₂) :
    CkHolderOnSpace k α Ω G :=
  CkHolderOnSpace.ofContDiffOn (fun y ↦ B (f.extendByZero y) (g.extendByZero y))
    (B.isBoundedBilinearMap.contDiff.comp_contDiffOn
      (f.contDiffOn_extendByZero.prodMk g.contDiffOn_extendByZero))
    (fun _ hj ↦ ⟨2 ^ k * ‖B‖ * ‖f‖ * ‖g‖, fun _ hx ↦
      norm_iteratedFDeriv_ckHolderOnBilinear_le B f g hj hx⟩)
    ⟨_, holderOnWith_iteratedFDeriv_ckHolderOnBilinear B hΩ hα f g⟩

private theorem ckHolderOnBilinear_apply (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) (f : CkHolderOnSpace k α Ω E₁) (g : CkHolderOnSpace k α Ω E₂) (x : Ω) :
    ckHolderOnBilinear B hΩ hα f g x = B (f x) (g x) := by
  rw [ckHolderOnBilinear, CkHolderOnSpace.ofContDiffOn_apply, f.extendByZero_coe,
    g.extendByZero_coe]

private theorem norm_ckHolderOnBilinear_le (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) (f : CkHolderOnSpace k α Ω E₁) (g : CkHolderOnSpace k α Ω E₂) :
    ‖ckHolderOnBilinear B hΩ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ := by
  refine (CkHolderOnSpace.norm_le_of_norm_iteratedFDeriv_le_of_holderOnWith
    (fun x ↦ (CkHolderOnSpace.ofContDiffOn_apply ..).symm) (by positivity)
    (fun _ hj _ hx ↦ norm_iteratedFDeriv_ckHolderOnBilinear_le B f g hj hx)
    (holderOnWith_iteratedFDeriv_ckHolderOnBilinear B hΩ hα f g)).trans_eq ?_
  push_cast
  ring

private def ckHolderOnBilinearLinear (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) :
    CkHolderOnSpace k α Ω E₁ →ₗ[ℝ] CkHolderOnSpace k α Ω E₂ →ₗ[ℝ] CkHolderOnSpace k α Ω G :=
  LinearMap.mk₂ ℝ (ckHolderOnBilinear B hΩ hα)
    (fun f₁ f₂ g ↦ CkHolderOnSpace.ext fun x ↦ by simp [ckHolderOnBilinear_apply])
    (fun c f g ↦ CkHolderOnSpace.ext fun x ↦ by simp [ckHolderOnBilinear_apply])
    (fun f g₁ g₂ ↦ CkHolderOnSpace.ext fun x ↦ by simp [ckHolderOnBilinear_apply])
    (fun c f g ↦ CkHolderOnSpace.ext fun x ↦ by simp [ckHolderOnBilinear_apply])

/-- Pointwise application of a continuous bilinear map to bounded `C^{k,α}` functions on a convex
open set `Ω` when `α ≤ 1`. -/
def compCkHolderOn₂ (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X)) (hα : α ≤ 1) :
    CkHolderOnSpace k α Ω E₁ →L[ℝ] CkHolderOnSpace k α Ω E₂ →L[ℝ] CkHolderOnSpace k α Ω G :=
  (ckHolderOnBilinearLinear B hΩ hα).mkContinuous₂ ((k + 7) * 2 ^ k * ‖B‖)
    (norm_ckHolderOnBilinear_le B hΩ hα)

/-- The lifted bilinear map `compCkHolderOn₂` evaluates pointwise via `B`. -/
@[simp]
theorem compCkHolderOn₂_apply (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) (f : CkHolderOnSpace k α Ω E₁) (g : CkHolderOnSpace k α Ω E₂) (x : Ω) :
    B.compCkHolderOn₂ hΩ hα f g x = B (f x) (g x) :=
  ckHolderOnBilinear_apply B hΩ hα f g x

/-- The lifted bilinear map `compCkHolderOn₂` has operator norm at most `(k + 7) * 2 ^ k * ‖B‖`. -/
theorem norm_compCkHolderOn₂_le (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) :
    ‖B.compCkHolderOn₂ (k := k) hΩ hα‖ ≤ (k + 7) * 2 ^ k * ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- Pointwise `C^{k,α}(Ω)` product estimate for a continuous bilinear map `B`. -/
theorem norm_compCkHolderOn₂_apply_le (B : E₁ →L[ℝ] E₂ →L[ℝ] G) (hΩ : Convex ℝ (Ω : Set X))
    (hα : α ≤ 1) (f : CkHolderOnSpace k α Ω E₁) (g : CkHolderOnSpace k α Ω E₂) :
    ‖B.compCkHolderOn₂ hΩ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖B‖ * ‖f‖ * ‖g‖ :=
  ((B.compCkHolderOn₂ hΩ hα).le_opNorm₂ f g).trans (by
    gcongr
    exact B.norm_compCkHolderOn₂_le hΩ hα)

end ContinuousLinearMap

namespace TauCeti.CkHolderOnSpace

variable {k : ℕ} {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Ω : TopologicalSpace.Opens E}

section SMul

variable {R F : Type*} [NormedRing R] [NormedAlgebra ℝ R]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Module R F] [IsBoundedSMul R F] [IsScalarTower ℝ R F]

/-- Pointwise scalar multiplication of `CkHolderOnSpace k α Ω F` by `CkHolderOnSpace k α Ω R` on a
convex open set `Ω` for `α ≤ 1`, as a continuous bilinear map. -/
def smulL (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderOnSpace k α Ω R →L[ℝ] CkHolderOnSpace k α Ω F →L[ℝ] CkHolderOnSpace k α Ω F :=
  (ContinuousLinearMap.lsmul ℝ R : R →L[ℝ] F →L[ℝ] F).compCkHolderOn₂ hΩ hα

/-- Pointwise scalar multiplication `smulL` evaluates by multiplying values at `x`. -/
@[simp]
theorem smulL_apply (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace k α Ω R) (g : CkHolderOnSpace k α Ω F) (x : Ω) :
    smulL hΩ hα f g x = f x • g x :=
  ContinuousLinearMap.compCkHolderOn₂_apply _ hΩ hα f g x

/-- Pointwise scalar multiplication on `CkHolderOnSpace k α Ω` has operator norm at most
`(k + 7) * 2 ^ k`. -/
theorem norm_smulL_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    ‖smulL (k := k) (R := R) (F := F) hΩ hα‖ ≤ (k + 7) * 2 ^ k := by
  refine (ContinuousLinearMap.norm_compCkHolderOn₂_le _ hΩ hα).trans ?_
  calc ((k : ℝ) + 7) * 2 ^ k * ‖(ContinuousLinearMap.lsmul ℝ R : R →L[ℝ] F →L[ℝ] F)‖
      ≤ ((k : ℝ) + 7) * 2 ^ k * 1 := by
        gcongr
        exact ContinuousLinearMap.opNorm_lsmul_le
    _ = ((k : ℝ) + 7) * 2 ^ k := mul_one _

/-- Norm bound `‖smulL hΩ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖f‖ * ‖g‖` for pointwise scalar
multiplication. -/
theorem norm_smulL_apply_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderOnSpace k α Ω R) (g : CkHolderOnSpace k α Ω F) :
    ‖smulL hΩ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖f‖ * ‖g‖ :=
  ((smulL hΩ hα).le_opNorm₂ f g).trans (by
    gcongr
    exact norm_smulL_le hΩ hα)

end SMul

section Mul

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

/-- Pointwise multiplication on `CkHolderOnSpace k α Ω A` for a non-unital normed `ℝ`-algebra `A`
on a convex open set `Ω` with `α ≤ 1`, as a continuous bilinear map. -/
def mulL (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderOnSpace k α Ω A →L[ℝ] CkHolderOnSpace k α Ω A →L[ℝ] CkHolderOnSpace k α Ω A :=
  (ContinuousLinearMap.mul ℝ A).compCkHolderOn₂ hΩ hα

/-- Pointwise algebra multiplication `mulL` evaluates by multiplying values at `x`. -/
@[simp]
theorem mulL_apply (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f g : CkHolderOnSpace k α Ω A) (x : Ω) :
    mulL hΩ hα f g x = f x * g x :=
  ContinuousLinearMap.compCkHolderOn₂_apply _ hΩ hα f g x

/-- Pointwise algebra multiplication on `CkHolderOnSpace k α Ω A` has operator norm at most
`(k + 7) * 2 ^ k`. -/
theorem norm_mulL_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1) :
    ‖mulL (k := k) (A := A) hΩ hα‖ ≤ (k + 7) * 2 ^ k := by
  refine (ContinuousLinearMap.norm_compCkHolderOn₂_le _ hΩ hα).trans ?_
  calc ((k : ℝ) + 7) * 2 ^ k * ‖ContinuousLinearMap.mul ℝ A‖
      ≤ ((k : ℝ) + 7) * 2 ^ k * 1 := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℝ A
    _ = ((k : ℝ) + 7) * 2 ^ k := mul_one _

/-- Norm bound `‖mulL hΩ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖f‖ * ‖g‖` for pointwise algebra
multiplication. -/
theorem norm_mulL_apply_le (hΩ : Convex ℝ (Ω : Set E)) (hα : α ≤ 1)
    (f g : CkHolderOnSpace k α Ω A) :
    ‖mulL hΩ hα f g‖ ≤ (k + 7) * 2 ^ k * ‖f‖ * ‖g‖ :=
  ((mulL hΩ hα).le_opNorm₂ f g).trans (by
    gcongr
    exact norm_mulL_le hΩ hα)

end Mul

end TauCeti.CkHolderOnSpace
