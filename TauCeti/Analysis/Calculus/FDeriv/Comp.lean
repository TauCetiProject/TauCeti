/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Tactic.Abel
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Derivatives under composition and changes of coordinates

By the chain rule, the differential of `f ∘ φ` at `b` is the differential of `f` at `φ b`
precomposed with that of `φ` at `b`. When the latter is invertible, one vanishes exactly when the
other does, so criticality does not depend on the coordinates. When `φ` is `C¹`, its differential
is locally bounded, so near a point the differential of `f ∘ φ` is at most a fixed multiple of that
of `f`, and estimates bounding a function by its differential survive changes of coordinates.

At a fixed point of a map preserving the germ of `f`, the derivative of `f` is unchanged by
precomposition with the derivative of that map.

For precomposition with an affine change of variables `w ↦ c + a • w`, or with the
multiplication `w ↦ c • w` by a fixed scalar `c` of a division semiring `𝕜'` over which the domain
`E` is a module, the chain rule holds as an identity between values of `fderiv` for every `f`,
differentiable or not: if `f` is not differentiable at the image `c + a • w`, respectively
`c • w`, of the point `w`, both sides are `0`, the value of `fderiv` at points of
nondifferentiability. For the latter, the map `w ↦ c • w` must be continuous and commute with the
scalars `𝕜`; for instance, for `f` on `ℂ`,
`fderiv ℝ (fun w ↦ f (c * w)) w v = fderiv ℝ f (c * w) (c * v)`.

## Main results

* `HasFDerivAt.comp_eq_of_eventuallyEq`: invariance of a germ at a fixed point implies invariance
  of its derivative.
* `HasFDerivAt.injective_of_eventuallyEq_id`: a map with a differentiable local left inverse has
  injective derivative.
* `TauCeti.differentiableAt_iterate`: an iterate is differentiable at a point where the map is
  differentiable along its orbit.
* `TauCeti.fderiv_comp_eq_zero_iff_of_isInvertible`: `b` is a critical point of `f ∘ φ` exactly
  when `φ b` is a critical point of `f`, if the differential of `φ` at `b` is invertible.
* `TauCeti.exists_norm_fderiv_comp_le_mul_norm_fderiv`: near a point where `φ` is `C¹`, the
  differential of `f ∘ φ` is at most a fixed multiple of that of `f`.
* `ContinuousLinearMap.fderiv_comp_right_of_rightInverse`,
  `ContinuousLinearMap.fderiv_comp_left_of_leftInverse`: the chain rule for precomposition with a
  split surjection and postcomposition with a split injection, with no differentiability
  assumption.
* `ContinuousLinearMap.hasFDerivAt_comp_left_iff_of_isEmbedding`,
  `ContinuousLinearMap.comp_comp_eq_of_hasFDerivAt_comp_left`: postcomposition with an embedding
  `Φ` turns the derivatives of `k` into those of `Φ ∘ k`, and every derivative of `Φ ∘ k` arises
  this way when `Φ` is a split injection.
* `TauCeti.fderiv_comp_add_smul`: `fderiv 𝕜` of `w ↦ f (c + a • w)` at `w` is `a` times
  `fderiv 𝕜 f (c + a • w)`, for every `f`.
* `TauCeti.fderiv_comp_smul_apply`: `fderiv 𝕜 (fun w ↦ f (c • w)) x v` equals
  `fderiv 𝕜 f (c • x) (c • v)`, for every `f` and a scalar `c` of a division semiring `𝕜'` over
  which `E` is a module, with each `w ↦ c • w` continuous and commuting with `𝕜`.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- If a map fixes `x` and preserves the germ of `f` there, its derivative preserves the
derivative of `f` by precomposition. -/
theorem _root_.HasFDerivAt.comp_eq_of_eventuallyEq {f : E → F} {f' : E →L[𝕜] F}
    {φ : E → E} {φ' : E →L[𝕜] E} {x : E} (hf : HasFDerivAt f f' x)
    (hφ : HasFDerivAt φ φ' x) (hfix : φ x = x)
    (hinv : f ∘ φ =ᶠ[nhds x] f) : f'.comp φ' = f' := by
  have hfφ : HasFDerivAt f f' (φ x) := by simpa only [hfix] using hf
  exact (hfφ.comp x hφ).unique (hf.congr_of_eventuallyEq hinv)

/-- If `g ∘ f` is the identity near `x` and `g` is differentiable at `f x`, the derivative of `f`
at `x` is injective. -/
theorem _root_.HasFDerivAt.injective_of_eventuallyEq_id {f : E → F} {g : F → E}
    {f' : E →L[𝕜] F} {g' : F →L[𝕜] E} {x : E} (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt g g' (f x)) (hgf : g ∘ f =ᶠ[nhds x] id) : Function.Injective f' := by
  have hcomp := ((hg.comp x hf).congr_of_eventuallyEq hgf.symm).unique (hasFDerivAt_id x)
  exact Function.LeftInverse.injective fun a => by
    simpa using congrArg (fun L : E →L[𝕜] E => L a) hcomp

/-- **Iterates are differentiable along differentiable orbits.** If `f` is differentiable at the
first `n` points `f^[j] x`, `j < n`, of the orbit of `x`, then `f^[n]` is differentiable at `x`.
Unlike `DifferentiableAt.iterate`, the point `x` need not be fixed. -/
theorem differentiableAt_iterate {f : E → E} {x : E} :
    ∀ {n : ℕ}, (∀ j < n, DifferentiableAt 𝕜 f (f^[j] x)) → DifferentiableAt 𝕜 f^[n] x
  | 0, _ => differentiableAt_id
  | n + 1, h => by
    rw [Function.iterate_succ']
    exact (h n (by omega)).comp x (differentiableAt_iterate fun j hj ↦ h j (by omega))

/-- **Criticality does not depend on the coordinates.** If `f` is differentiable at `φ b` and
the differential of `φ` at `b` is invertible, then `b` is a critical
point of `f ∘ φ` exactly when `φ b` is a critical point of `f`. -/
theorem fderiv_comp_eq_zero_iff_of_isInvertible {f : E → G} {φ : F → E} {b : F}
    (hf : DifferentiableAt 𝕜 f (φ b)) (hinv : (fderiv 𝕜 φ b).IsInvertible) :
    fderiv 𝕜 (f ∘ φ) b = 0 ↔ fderiv 𝕜 f (φ b) = 0 := by
  have hφ := differentiableAt_of_isInvertible_fderiv hinv
  obtain ⟨e, he⟩ := hinv
  -- The differential of `f ∘ φ` at `b` is that of `f` at `φ b` precomposed with the equivalence
  -- `e`, so one vanishes exactly when the other does.
  rw [fderiv_comp (x := b) hf hφ, ← he]
  exact ContinuousLinearMap.comp_continuousLinearEquiv_eq_zero_iff _ e

/-- **A change of coordinates distorts the differential by a locally bounded factor.** If `g`
agrees near `x` with `f ∘ φ`, where `φ` is differentiable near `x` with derivative continuous at
`x`, and `f` is differentiable at `φ y` for `y` near `x`, then near `x` the differential of `g` at
`y` has norm at most a fixed multiple of that of `f` at `φ y`. -/
theorem exists_norm_fderiv_comp_le_mul_norm_fderiv {f : E → G} {φ : F → E} {g : F → G} {x : F}
    (hg : g =ᶠ[nhds x] f ∘ φ) (hφ : ∀ᶠ y in nhds x, DifferentiableAt 𝕜 φ y)
    (hφ' : ContinuousAt (fderiv 𝕜 φ) x) (hf : ∀ᶠ y in nhds x, DifferentiableAt 𝕜 f (φ y)) :
    ∃ K > 0, ∀ᶠ y in nhds x, ‖fderiv 𝕜 g y‖ ≤ K * ‖fderiv 𝕜 f (φ y)‖ := by
  refine ⟨‖fderiv 𝕜 φ x‖ + 1, by positivity, ?_⟩
  filter_upwards [hg.eventuallyEq_nhds, hφ, hf,
    hφ'.norm.eventually (eventually_le_nhds (lt_add_one _))] with y hgy hφy hfy hKy
  rw [hgy.fderiv_eq, fderiv_comp y hfy hφy]
  calc ‖fderiv 𝕜 f (φ y) ∘L fderiv 𝕜 φ y‖ ≤ ‖fderiv 𝕜 f (φ y)‖ * ‖fderiv 𝕜 φ y‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖fderiv 𝕜 φ x‖ + 1) * ‖fderiv 𝕜 f (φ y)‖ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hKy (norm_nonneg _)

/-- Precomposing a real-valued function with scalar multiplication scales the norm of its
Fréchet derivative by the absolute value of the scalar. -/
theorem norm_fderiv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (a : ℝ) (x : E) :
    ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ = |a| * ‖fderiv ℝ f (a • x)‖ := by
  rw [_root_.fderiv_comp_smul a, norm_smul, Real.norm_eq_abs]

/-- **The chain rule for an affine change of variables.** `fderiv 𝕜` of `w ↦ f (c + a • w)` at
`w` is `a` times `fderiv 𝕜 f (c + a • w)`. Like `fderiv_comp_smul`, this holds for every `f`: if
`f` is not differentiable at `c + a • w`, both sides are `0`. -/
theorem fderiv_comp_add_smul (f : E → F) (c : E) (a : 𝕜) (w : E) :
    fderiv 𝕜 (fun w ↦ f (c + a • w)) w = a • fderiv 𝕜 f (c + a • w) := by
  rw [_root_.fderiv_comp_smul (f := fun y ↦ f (c + y)), fderiv_comp_add_left]

/-- **The chain rule for precomposition with a scalar multiplication.** Let `𝕜'` be a division
semiring and `E` a `𝕜'`-module such that multiplication `w ↦ c • w` by each fixed scalar `c : 𝕜'`
is continuous and commutes with the action of `𝕜`. Then `fderiv 𝕜 (fun w ↦ f (c • w)) x` sends `v`
to `fderiv 𝕜 f (c • x) (c • v)`. Multiplication by `c` is `𝕜`-linear and, unless `c = 0`,
invertible, so this holds for every `f`, with no norm or additive inverses on `𝕜'`: if `f` is not
differentiable at `c • x`, both sides are `0`, the value of `fderiv` at points of
nondifferentiability. When `𝕜' = 𝕜` and the action is the given normed-space action, this is the
pointwise form of `fderiv_comp_smul`; for `𝕜 = ℝ` and `𝕜' = ℂ` it computes the real `fderiv` of
`w ↦ f (c * w)` on `ℂ`, and for `𝕜' = ℝ≥0` it covers nonnegative dilations. -/
theorem fderiv_comp_smul_apply {𝕜' : Type*} [DivisionSemiring 𝕜'] [Module 𝕜' E]
    [ContinuousConstSMul 𝕜' E] [SMulCommClass 𝕜' 𝕜 E] (f : E → F) (c : 𝕜') (x v : E) :
    fderiv 𝕜 (fun w ↦ f (c • w)) x v = fderiv 𝕜 f (c • x) (c • v) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have h := (ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (Units.mk0 c hc)).comp_right_fderiv
      (f := f) (x := x)
    simpa [Function.comp_def] using DFunLike.congr_fun h v

/-- For a continuous linear map `g` with a continuous linear right inverse `s`, the derivative of
`h ∘ g` at `x` is the derivative of `h` at `g x` composed with `g`, for every `h` (no
differentiability assumption). -/
theorem _root_.ContinuousLinearMap.fderiv_comp_right_of_rightInverse (g : G →L[𝕜] E) (s : E →L[𝕜] G)
    (hgs : Function.RightInverse s g) (h : E → F) (x : G) :
    fderiv 𝕜 (h ∘ g) x = (fderiv 𝕜 h (g x)).comp g := by
  by_cases hd : DifferentiableAt 𝕜 h (g x)
  · rw [fderiv_comp x hd g.differentiableAt, g.fderiv]
  · have hnd : ¬ DifferentiableAt 𝕜 (h ∘ g) x := fun hd' ↦ hd (by
      have hx : (fun u ↦ s u + (x - s (g x))) (g x) = x := by simp
      have hcomp : h = (h ∘ g) ∘ fun u ↦ s u + (x - s (g x)) := by
        funext u
        simp [hgs _]
      have := (hx ▸ hd').comp (g x)
        (by fun_prop : DifferentiableAt 𝕜 (fun u ↦ s u + (x - s (g x))) (g x))
      rwa [← hcomp] at this)
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- For a continuous linear map `Φ` with a continuous linear left inverse `Ψ`, the derivative of
`Φ ∘ k` at `y` is `Φ` composed with the derivative of `k` at `y`, for every `k` (no
differentiability assumption). -/
theorem _root_.ContinuousLinearMap.fderiv_comp_left_of_leftInverse {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Φ : E →L[𝕜] F) (Ψ : F →L[𝕜] E) (hΨΦ : Function.LeftInverse Ψ Φ) (k : X → E) (y : X) :
    fderiv 𝕜 (Φ ∘ k) y = Φ.comp (fderiv 𝕜 k y) := by
  by_cases hd : DifferentiableAt 𝕜 k y
  · rw [fderiv_comp y Φ.differentiableAt hd, Φ.fderiv]
  · have hnd : ¬ DifferentiableAt 𝕜 (Φ ∘ k) y := fun hd' ↦ hd (by
      have : k = Ψ ∘ (Φ ∘ k) := by
        funext u
        simp [hΨΦ _]
      rw [this]
      exact Ψ.differentiableAt.comp y hd')
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- For a continuous linear map `Φ` that is an embedding, `Φ ∘ k` has derivative `Φ ∘ k'` at `y`
exactly when `k` has derivative `k'` at `y`. -/
theorem _root_.ContinuousLinearMap.hasFDerivAt_comp_left_iff_of_isEmbedding {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (Φ : E →L[𝕜] F) (hΦ : Topology.IsEmbedding Φ)
    {k : X → E} {k' : X →L[𝕜] E} {y : X} :
    HasFDerivAt (Φ ∘ k) (Φ.comp k') y ↔ HasFDerivAt k k' y :=
  ⟨fun h ↦ HasFDerivAt.of_comp_of_isEmbedding (hΦ.isInducing.continuousAt_iff.mpr h.continuousAt)
    Φ.hasFDerivAt hΦ h .rfl, fun h ↦ Φ.hasFDerivAt.comp y h⟩

/-- For a continuous linear map `Φ` with a continuous linear left inverse `Ψ`, every derivative
`D` of `Φ ∘ k` takes values in the range of `Φ`: it is `Φ` composed with the derivative `Ψ ∘ D`
of `k`. -/
theorem _root_.ContinuousLinearMap.comp_comp_eq_of_hasFDerivAt_comp_left {X : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (Φ : E →L[𝕜] F) (Ψ : F →L[𝕜] E) (hΨΦ : Function.LeftInverse Ψ Φ) {k : X → E}
    {D : X →L[𝕜] F} {y : X} (hD : HasFDerivAt (Φ ∘ k) D y) : Φ.comp (Ψ.comp D) = D := by
  have hk : Ψ ∘ (Φ ∘ k) = k := funext fun u ↦ hΨΦ (k u)
  have h : HasFDerivAt k (Ψ.comp D) y := by simpa only [hk] using Ψ.hasFDerivAt.comp y hD
  exact (Φ.hasFDerivAt.comp y h).unique hD

end TauCeti

namespace ContinuousLinearMap

open Function
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂]

/-- A critical point of a map yields a critical point of its slice along a level set of a
functional `φ`. Precisely, let `(φ, ρ)` be jointly injective on `F`, let `γ` parametrize a family of
points along which `φ ∘ f` is locally constant, and let `φ ∘ Df` be nonzero at `γ z`. If
`ρ ∘ f ∘ γ` has surjective derivative at `z`, then `Df` is surjective at `γ z`; equivalently, if
`γ z` is critical for `f`, then `z` is critical for the slice `ρ ∘ f ∘ γ`. -/
theorem surjective_fderiv_of_surjective_fderiv_comp {f : E → F} {γ : G₁ → E} {z : G₁} {c : 𝕜}
    (φ : F →L[𝕜] 𝕜) (ρ : F →L[𝕜] G₂) (hφρ : Injective fun w ↦ (φ w, ρ w))
    (hγ : DifferentiableAt 𝕜 γ z) (hf : DifferentiableAt 𝕜 f (γ z))
    (hconst : (fun w ↦ φ (f (γ w))) =ᶠ[𝓝 z] fun _ ↦ c)
    (hne : ∃ v, φ (fderiv 𝕜 f (γ z) v) ≠ 0)
    (hs : Surjective (fderiv 𝕜 (fun w ↦ ρ (f (γ w))) z)) : Surjective (fderiv 𝕜 f (γ z)) := by
  set T : G₁ →L[𝕜] E := fderiv 𝕜 γ z
  set A : E →L[𝕜] F := fderiv 𝕜 f (γ z)
  have hT : HasFDerivAt γ T z := hγ.hasFDerivAt
  have hA : HasFDerivAt f A (γ z) := hf.hasFDerivAt
  have hGd : HasFDerivAt (fun w ↦ ρ (f (γ w))) (ρ.comp (A.comp T)) z :=
    ρ.hasFDerivAt.comp z (hA.comp z hT)
  have hzero : ∀ w : G₁, φ (A (T w)) = 0 := by
    have hd : HasFDerivAt (fun w ↦ φ (f (γ w))) (φ.comp (A.comp T)) z :=
      φ.hasFDerivAt.comp z (hA.comp z hT)
    have hzero' : φ.comp (A.comp T) = 0 :=
      (hd.congr_of_eventuallyEq hconst.symm).unique (hasFDerivAt_const c z)
    intro w
    simpa using congrArg (fun B : G₁ →L[𝕜] 𝕜 ↦ B w) hzero'
  have hker : ∀ y, φ y = 0 → ∃ u, A u = y := by
    intro y hy
    obtain ⟨w, hw⟩ := hs (ρ y)
    rw [hGd.fderiv] at hw
    refine ⟨T w, hφρ ?_⟩
    exact Prod.ext (by simp only [hzero w, hy]) hw
  obtain ⟨v, hv⟩ := hne
  intro w
  obtain ⟨u, hu⟩ := hker (w - (φ w / φ (A v)) • A v) (by simp [div_mul_cancel₀ _ hv])
  refine ⟨u + (φ w / φ (A v)) • v, ?_⟩
  rw [map_add, map_smul, hu]
  abel

end ContinuousLinearMap
