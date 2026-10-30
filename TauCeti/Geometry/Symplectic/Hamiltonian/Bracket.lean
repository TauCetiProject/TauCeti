/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Lie brackets of Hamiltonian vector fields

Let `σ` be a closed two-form on a manifold `M`, with the convention `ι_X σ = df` for a Hamiltonian
vector field `X` of `f`. If `X` and `Y` are differentiable Hamiltonian vector fields of `C²`
functions `f` and `g`, then

`d(σ(X, Y)) = -ι_{[X, Y]} σ`,

so the Lie bracket `[X, Y]` is a Hamiltonian vector field of `-σ(X, Y)`
(`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mvfderiv_eval₂` and
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mlieBracket`). No nondegeneracy is needed.

For a nondegenerate closed form on a finite-dimensional manifold, where the Poisson bracket is
`{f, g} = σ(X_f, X_g) = df(X_g)`, this says

`X_{{f, g}} = -[X_f, X_g]`

(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`): the map
`f ↦ -X_f` takes Poisson brackets to Lie brackets of vector fields. It gives the identity
`{f, {g, k}} = {{f, g}, k} - {{f, k}, g}` and the **Jacobi identity**
`{f, {g, k}} + {g, {k, f}} + {k, {f, g}} = 0` for `C²` functions
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_poissonBracket` and
`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_jacobi`).

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (Lie brackets of symplectic and Hamiltonian vector fields, and the Poisson bracket).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.3 (the Poisson bracket and its Jacobi identity).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {f g : M → ℝ} {X Y : (x : M) → TangentSpace I x} {x : M}

namespace IsHamiltonianVectorField

variable [CompleteSpace E]

/-- For a closed form `σ` and Hamiltonian vector fields `X` of `f` and `Y` of `g`, with `f` and `g`
of class `C²` and `X`, `Y` differentiable at `x`, the differential of `σ(X, Y)` at `x` is
`-ι_{[X, Y]} σ`. -/
theorem mvfderiv_eval₂ (hσ : σ.IsClosed) (hX : σ.IsHamiltonianVectorField f X)
    (hY : σ.IsHamiltonianVectorField g Y) (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x)
    (hX' : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY' : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y ↦ SmoothBundleForm.eval₂ σ y (X y) (Y y)) x v =
      -SmoothBundleForm.eval₂ σ x (mlieBracket I X Y x) v := by
  set W : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E v
  have hWx : W x = v := FiberBundle.extend_apply_self E v
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- Extend `v` to a vector field `W` and evaluate `dσ(X, Y, W) = 0` by the invariant formula.
  -- The terms of `dσ(X, Y, W) = 0` that differentiate `σ` along the fields.
  have hYW : (fun y ↦ σ.1 y ![Y y, W y]) = fun y ↦ mvfderiv I g y (W y) := by
    funext y; rw [← SmoothBundleForm.eval₂_apply, isHamiltonianVectorField_iff.1 hY y]
  have hXW : (fun y ↦ σ.1 y ![X y, W y]) = fun y ↦ mvfderiv I f y (W y) := by
    funext y; rw [← SmoothBundleForm.eval₂_apply, isHamiltonianVectorField_iff.1 hX y]
  have hgX : (fun y ↦ mvfderiv I g y (X y)) = fun y ↦ -SmoothBundleForm.eval₂ σ y (X y) (Y y) := by
    funext y; rw [← isHamiltonianVectorField_iff.1 hY y, SmoothBundleForm.eval₂_swap]
  have hfY : (fun y ↦ mvfderiv I f y (Y y)) = fun y ↦ SmoothBundleForm.eval₂ σ y (X y) (Y y) := by
    funext y; rw [← isHamiltonianVectorField_iff.1 hX y]
  -- The bracket terms of `dσ(X, Y, W) = 0`.
  have hXWY : σ.1 x ![mlieBracket I X W x, Y x] = -mvfderiv I g x (mlieBracket I X W x) := by
    rw [← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_swap,
      isHamiltonianVectorField_iff.1 hY x]
  have hYWX : σ.1 x ![mlieBracket I Y W x, X x] = -mvfderiv I f x (mlieBracket I Y W x) := by
    rw [← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_swap,
      isHamiltonianVectorField_iff.1 hX x]
  have h := SmoothForm.mextDeriv_apply_two (φ := σ) hX' hY' hW
  rw [(SmoothForm.isClosed_def σ).1 hσ, hYW, hXW, hXWY, hYWX,
    mvfderiv_mlieBracket hg h2 hX' hW, mvfderiv_mlieBracket hf h2 hY' hW, hgX, hfY,
    mvfderiv_fun_neg, hWx] at h
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, neg_apply,
    SmoothBundleForm.eval₂_apply] at h ⊢
  linear_combination h

/-- **The Lie bracket of Hamiltonian vector fields is Hamiltonian.** For a closed form `σ` and
differentiable Hamiltonian vector fields `X` of `f` and `Y` of `g`, with `f` and `g` of class `C²`,
the bracket `[X, Y]` is a Hamiltonian vector field of `-σ(X, Y)`. -/
theorem mlieBracket (hσ : σ.IsClosed) (hX : σ.IsHamiltonianVectorField f X)
    (hY : σ.IsHamiltonianVectorField g Y) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hX' : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M)))
    (hY' : MDifferentiable I I.tangent (fun y ↦ (Y y : TangentBundle I M))) :
    σ.IsHamiltonianVectorField (fun y ↦ -SmoothBundleForm.eval₂ σ y (X y) (Y y))
      (mlieBracket I X Y) :=
  isHamiltonianVectorField_iff.2 fun x v ↦ by
    rw [mvfderiv_fun_neg, neg_apply,
      hX.mvfderiv_eval₂ hσ hY (hf x) (hg x) (hX' x) (hY' x), neg_neg]

end IsHamiltonianVectorField

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
include h

/-- For a nondegenerate closed form on a finite-dimensional manifold, the Hamiltonian vector field
of the Poisson bracket of two `C²` functions is `X_{{f, g}} = -[X_f, X_g]`. -/
theorem hamiltonianVectorField_poissonBracket (hσ : σ.IsClosed) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    σ.hamiltonianVectorField (σ.poissonBracket f g) =
      -mlieBracket I (σ.hamiltonianVectorField f) (σ.hamiltonianVectorField g) := by
  refine (h.isHamiltonianVectorField_iff_eq.1 (isHamiltonianVectorField_iff.2 fun x v ↦ ?_)).symm
  have hfg : σ.poissonBracket f g = fun y ↦
      SmoothBundleForm.eval₂ σ y (σ.hamiltonianVectorField f y) (σ.hamiltonianVectorField g y) :=
    funext (σ.poissonBracket_def f g)
  rw [hfg, (h.isHamiltonianVectorField_hamiltonianVectorField f).mvfderiv_eval₂ hσ
    (h.isHamiltonianVectorField_hamiltonianVectorField g) (hf x) (hg x)
    (h.mdifferentiable_hamiltonianVectorField hf x) (h.mdifferentiable_hamiltonianVectorField hg x),
    Pi.neg_apply, SmoothBundleForm.eval₂_neg_left]

/-- For a nondegenerate closed form on a finite-dimensional manifold, the Poisson bracket of `C²`
functions satisfies `{f, {g, k}} = {{f, g}, k} - {{f, k}, g}`. -/
theorem poissonBracket_poissonBracket (hσ : σ.IsClosed) {k : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (hk : ContMDiff I 𝓘(ℝ) 2 k) (x : M) :
    σ.poissonBracket f (σ.poissonBracket g k) x =
      σ.poissonBracket (σ.poissonBracket f g) k x -
        σ.poissonBracket (σ.poissonBracket f k) g x := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- `{f, k}` and `{f, g}` are the derivatives of `f` along `X_k` and `X_g`.
  have hfk : σ.poissonBracket f k = fun y ↦ mvfderiv I f y (σ.hamiltonianVectorField k y) :=
    funext (h.poissonBracket_eq_mvfderiv f k)
  have hfg : σ.poissonBracket f g = fun y ↦ mvfderiv I f y (σ.hamiltonianVectorField g y) :=
    funext (h.poissonBracket_eq_mvfderiv f g)
  rw [h.poissonBracket_eq_mvfderiv, h.hamiltonianVectorField_poissonBracket hσ hg hk, Pi.neg_apply,
    map_neg, mvfderiv_mlieBracket (hf x) (by simp) (h.mdifferentiable_hamiltonianVectorField hg x)
      (h.mdifferentiable_hamiltonianVectorField hk x), h.poissonBracket_eq_mvfderiv,
    h.poissonBracket_eq_mvfderiv, ← hfk, ← hfg]
  ring

/-- **The Jacobi identity for the Poisson bracket.** For a nondegenerate closed form on a
finite-dimensional manifold and `C²` functions `f`, `g`, `k`,
`{f, {g, k}} + {g, {k, f}} + {k, {f, g}} = 0`. -/
theorem poissonBracket_jacobi (hσ : σ.IsClosed) {k : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (hk : ContMDiff I 𝓘(ℝ) 2 k) (x : M) :
    σ.poissonBracket f (σ.poissonBracket g k) x + σ.poissonBracket g (σ.poissonBracket k f) x +
      σ.poissonBracket k (σ.poissonBracket f g) x = 0 := by
  have hkf : σ.poissonBracket k f = -σ.poissonBracket f k :=
    funext fun y ↦ by rw [Pi.neg_apply, neg_poissonBracket]
  rw [h.poissonBracket_poissonBracket hσ hf hg hk, hkf, poissonBracket_neg_right,
    ← neg_poissonBracket, ← neg_poissonBracket σ (σ.poissonBracket f k)]
  ring

end IsNondegenerate

end SmoothTwoForm

end TauCeti
