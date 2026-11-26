/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Topology.MetricSpace.Holder

/-!
# Affine isometries

For a scalar `c` and an affine isometry `e : V ≃ᵃⁱ[𝕜] V₂` between normed spaces, the affine
isometry `TauCeti.dilateConj c e` has the linear part of `e` and translation part `c • e 0`. For
`c ≠ 0` it is the conjugate `y ↦ c • e (c⁻¹ • y)` of `e` by the dilations by `c`.

The derivative of an affine isometry equivalence has norm at most one. Composing a function with
an affine isometry equivalence preserves the norms of its iterated derivatives: on the right in
every order, and on the left in every positive order, since the translation part only shifts
the values. These are the affine forms of Mathlib's
`LinearIsometryEquiv.norm_iteratedFDeriv_comp_right` and
`LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`. Likewise, composing a map with affine
isometries on both sides keeps the Hölder constant of its derivative.

## Main declarations

* `LinearIsometryEquiv.coe_toAffineIsometryEquiv_symm`: the inverse of a linear isometry
  equivalence, seen as an affine isometry equivalence, is its inverse as a linear isometry.
* `TauCeti.dilateConj`: the dilation conjugate of an affine isometry.
* `TauCeti.dilateConj_smul`: `dilateConj c e (c • y) = c • e y`.
* `TauCeti.dilateConj_symm_apply`: the inverse of `dilateConj c e`, written out pointwise.
* `AffineIsometryEquiv.linearIsometryEquiv_symm`: the linear part of the inverse of an affine
  isometry equivalence is the inverse of its linear part.
* `AffineIsometryEquiv.norm_fderiv_le`: the derivative of an affine isometry equivalence has norm
  at most one.
* `AffineIsometryEquiv.image_frontier`: an affine isometry equivalence maps frontiers to frontiers.
* `AffineIsometryEquiv.norm_iteratedFDeriv_comp_left`,
  `AffineIsometryEquiv.norm_iteratedFDeriv_comp_right`: composition with an affine isometry
  equivalence preserves the norms of iterated derivatives.
* `AffineIsometry.holderOnWith_fderiv_comp_comp`, `AffineIsometry.holderWith_fderiv_comp_comp`:
  composing a map with affine isometries on both sides keeps the Hölder constant of its
  derivative, on a set and on the whole space.
-/

public section

noncomputable section

namespace LinearIsometryEquiv

/-- The inverse of a linear isometry equivalence, seen as an affine isometry equivalence, is its
inverse as a linear isometry equivalence. -/
@[simp]
theorem coe_toAffineIsometryEquiv_symm {𝕜 V V₂ : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂]
    (e : V ≃ₗᵢ[𝕜] V₂) : ⇑e.toAffineIsometryEquiv.symm = e.symm := by
  funext x
  rw [AffineIsometryEquiv.symm_apply_eq, coe_toAffineIsometryEquiv, apply_symm_apply]

end LinearIsometryEquiv

namespace AffineIsometryEquiv

/-- The linear part of the inverse of an affine isometry equivalence is the inverse of its linear
part. This holds by definition of `AffineIsometryEquiv.symm`. -/
@[simp]
theorem linearIsometryEquiv_symm {𝕜 V V₂ P P₂ : Type*} [NormedField 𝕜] [SeminormedAddCommGroup V]
    [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P] [SeminormedAddCommGroup V₂]
    [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂) :
    e.symm.linearIsometryEquiv = e.linearIsometryEquiv.symm :=
  rfl

/-- The Fréchet derivative of an affine isometry equivalence has norm at most one. -/
theorem norm_fderiv_le {𝕜 W W₂ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup W₂] [NormedSpace 𝕜 W₂]
    (e : W ≃ᵃⁱ[𝕜] W₂) (x : W) : ‖fderiv 𝕜 e x‖ ≤ 1 := by
  simpa using norm_fderiv_le_of_lipschitz 𝕜 e.lipschitzWith (x₀ := x)

/-- An affine isometry equivalence maps the frontier of a set onto the frontier of its image. -/
theorem image_frontier {𝕜 V V₂ P P₂ : Type*} [NormedField 𝕜] [SeminormedAddCommGroup V]
    [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P] [SeminormedAddCommGroup V₂]
    [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂] (e : P ≃ᵃⁱ[𝕜] P₂)
    (s : Set P) : e '' frontier s = frontier (e '' s) :=
  e.toHomeomorph.image_frontier s

section IteratedFDeriv

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Postcomposition with an affine isometry equivalence preserves the norms of the iterated
derivatives of positive order. In order zero the translation part changes the values. -/
theorem norm_iteratedFDeriv_comp_left (g : F ≃ᵃⁱ[𝕜] G) (f : E → F) (x : E) {i : ℕ}
    (hi : i ≠ 0) : ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  have hg : g ∘ f = fun y ↦ (g.linearIsometryEquiv ∘ f) y + g 0 := by
    funext y
    simpa using g.map_vadd 0 (f y)
  rw [hg, TauCeti.iteratedFDeriv_succ_add_const,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]

/-- Precomposition with an affine isometry equivalence preserves the norms of the iterated
derivatives. -/
theorem norm_iteratedFDeriv_comp_right (g : E ≃ᵃⁱ[𝕜] F) (f : F → G) (x : E) (i : ℕ) :
    ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ = ‖iteratedFDeriv 𝕜 i f (g x)‖ := by
  have hg (y : E) : g y = g.linearIsometryEquiv y + g 0 := by simpa using g.map_vadd 0 y
  have hfg : f ∘ g = (fun z ↦ f (z + g 0)) ∘ g.linearIsometryEquiv := by
    funext y
    simp [hg y]
  rw [hfg, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, iteratedFDeriv_comp_add_right,
    ← hg]

end IteratedFDeriv

end AffineIsometryEquiv

namespace AffineIsometry

section Holder

open scoped NNReal

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Composing a map with affine isometries on both sides keeps the Hölder constant of its
derivative on a set: if `e` maps `s` into `t`, `f` is differentiable at the points of `t` and
`Df` is `α`-Hölder on `t` with constant `K`, then `D(g ∘ f ∘ e)` is `α`-Hölder on `s` with constant
`K`, since `D(g ∘ f ∘ e)(x)` is `Df(e x)` composed on both sides with linear maps of norm at most
one. -/
theorem holderOnWith_fderiv_comp_comp (e : E →ᵃⁱ[𝕜] F) (g : G →ᵃⁱ[𝕜] H) {f : F → G} {s : Set E}
    {t : Set F} (hst : Set.MapsTo e s t) (hf : ∀ y ∈ t, DifferentiableAt 𝕜 f y) {K α : ℝ≥0}
    (hK : HolderOnWith K α (fderiv 𝕜 f) t) :
    HolderOnWith K α (fderiv 𝕜 (g ∘ f ∘ e)) s := by
  set A := e.toContinuousAffineMap
  set B := g.toContinuousAffineMap
  have hd (x : E) (hx : x ∈ s) : fderiv 𝕜 (g ∘ f ∘ e) x =
      B.contLinear.comp ((fderiv 𝕜 f (e x)).comp A.contLinear) :=
    ((B.hasFDerivAt (x := f (e x))).comp x
      ((hf (e x) (hst hx)).hasFDerivAt.comp x (A.hasFDerivAt (x := x)))).fderiv
  have hAn : ‖A.contLinear‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]
    exact (e.linearIsometry.norm_map y).le
  have hBn : ‖B.contLinear‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]
    exact (g.linearIsometry.norm_map y).le
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  rw [hd x hx, hd y hy, dist_eq_norm, ← ContinuousLinearMap.comp_sub,
    ← ContinuousLinearMap.sub_comp]
  calc ‖B.contLinear.comp ((fderiv 𝕜 f (e x) - fderiv 𝕜 f (e y)).comp A.contLinear)‖
      ≤ ‖B.contLinear‖ * (‖fderiv 𝕜 f (e x) - fderiv 𝕜 f (e y)‖ * ‖A.contLinear‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖fderiv 𝕜 f (e x) - fderiv 𝕜 f (e y)‖ * 1) :=
        mul_le_mul hBn (mul_le_mul_of_nonneg_left hAn (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = dist (fderiv 𝕜 f (e x)) (fderiv 𝕜 f (e y)) := by
        rw [one_mul, mul_one, dist_eq_norm]
    _ ≤ K * dist (e x) (e y) ^ (α : ℝ) := hK.dist_le (hst hx) (hst hy)
    _ = K * dist x y ^ (α : ℝ) := by rw [e.dist_map]

/-- Composing a differentiable map with affine isometries on both sides keeps the Hölder constant
of its derivative: if `Df` is `α`-Hölder with constant `K`, so is `D(g ∘ f ∘ e)`. -/
theorem holderWith_fderiv_comp_comp (e : E →ᵃⁱ[𝕜] F) (g : G →ᵃⁱ[𝕜] H) {f : F → G}
    (hf : Differentiable 𝕜 f) {K α : ℝ≥0} (hK : HolderWith K α (fderiv 𝕜 f)) :
    HolderWith K α (fderiv 𝕜 (g ∘ f ∘ e)) :=
  holderOnWith_univ.1 (holderOnWith_fderiv_comp_comp e g (Set.mapsTo_univ _ _) (fun y _ => hf y)
    (holderOnWith_univ.2 hK))

end Holder

end AffineIsometry

namespace TauCeti

variable {𝕜 V V₂ : Type*} [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂]

/-- The affine isometry with the linear part of `e` and translation part `c • e 0`. For `c ≠ 0`
it is the conjugate `y ↦ c • e (c⁻¹ • y)` of `e` by the dilation by `c`; for `c = 0` it is the
linear part of `e`. -/
def dilateConj (c : 𝕜) (e : V ≃ᵃⁱ[𝕜] V₂) : V ≃ᵃⁱ[𝕜] V₂ :=
  e.linearIsometryEquiv.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd 𝕜 V₂ (c • e 0))

/-- The dilation conjugate of `e` sends `c • y` to `c • e y`. -/
@[simp]
theorem dilateConj_smul (c : 𝕜) (e : V ≃ᵃⁱ[𝕜] V₂) (y : V) :
    dilateConj c e (c • y) = c • e y := by
  have he : e y = e.linearIsometryEquiv y + e 0 := by simpa using e.map_vadd 0 y
  simp [dilateConj, he, smul_add, add_comm]

/-- The inverse of the dilation conjugate of `e` by `c ≠ 0` is the dilation conjugate of
`e.symm`, written out pointwise. -/
theorem dilateConj_symm_apply {c : 𝕜} (hc : c ≠ 0) (e : V ≃ᵃⁱ[𝕜] V₂) (z : V₂) :
    (dilateConj c e).symm z = c • e.symm (c⁻¹ • z) := by
  rw [AffineIsometryEquiv.symm_apply_eq, dilateConj_smul, AffineIsometryEquiv.apply_symm_apply,
    smul_inv_smul₀ hc]

end TauCeti
