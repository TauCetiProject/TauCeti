/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Lie brackets of Hamiltonian vector fields

Let `σ` be a closed two-form on a manifold `M`, with the convention `ι_X σ = df` for a Hamiltonian
vector field `X` of `f`. If `X` and `Y` are differentiable Hamiltonian vector fields of `C²`
functions `f` and `g`, then

`d(σ(X, Y)) = -ι_{[X, Y]} σ`,

so the Lie bracket `[X, Y]` is a Hamiltonian vector field of `-σ(X, Y)`, and `-[X, Y]` one of
`σ(X, Y)` (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mvfderiv_eval₂`,
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mlieBracket` and
`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.neg_mlieBracket`). No nondegeneracy is needed, and
the model space may be any Banach space. Two consequences hold in the same generality:

* the **Jacobi identity** `σ([X, Y], Z) + σ([Y, Z], X) + σ([Z, X], Y) = 0` for differentiable
  Hamiltonian vector fields `X`, `Y`, `Z` of `C²` functions
  (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.eval₂_mlieBracket_jacobi`);
* **Poisson's theorem**: if `f` and `g` are stationary along a Hamiltonian vector field `Z`, then
  so is `σ(X, Y)` (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField.mvfderiv_eval₂_apply_eq_zero`).

More generally, the Lie bracket of two symplectic vector fields `X` and `Y`, that is smooth vector
fields with closed contractions `ι_X σ` and `ι_Y σ`, is a Hamiltonian vector field of `σ(Y, X)`
(`TauCeti.SmoothTwoForm.isHamiltonianVectorField_mlieBracket`), although `X` and `Y` themselves
need not be Hamiltonian.

For a nondegenerate closed form on a finite-dimensional manifold, where the Poisson bracket is
`{f, g} = σ(X_f, X_g) = df(X_g)`, this says

`X_{{f, g}} = -[X_f, X_g]`

(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`): the map
`f ↦ -X_f` takes Poisson brackets to Lie brackets of vector fields. It gives the identity
`{f, {g, k}} = {{f, g}, k} - {{f, k}, g}` and the **Jacobi identity**
`{f, {g, k}} + {g, {k, f}} + {k, {f, g}} = 0` for `C²` functions
(`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_poissonBracket` and
`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_jacobi`). The same identity shows that
the Hamiltonian vector fields of two functions commute at every point near which the functions
Poisson-commute
(`TauCeti.SmoothTwoForm.IsNondegenerate.mlieBracket_hamiltonianVectorField_eq_zero`).

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (Lie brackets of symplectic and Hamiltonian vector fields, and the Poisson bracket).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.3 (the Poisson bracket and its Jacobi identity).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold Topology

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
  have hYW : (fun y ↦ σ.val y ![Y y, W y]) = fun y ↦ mvfderiv I g y (W y) := by
    funext y; rw [← SmoothBundleForm.eval₂_apply, isHamiltonianVectorField_iff.1 hY y]
  have hXW : (fun y ↦ σ.val y ![X y, W y]) = fun y ↦ mvfderiv I f y (W y) := by
    funext y; rw [← SmoothBundleForm.eval₂_apply, isHamiltonianVectorField_iff.1 hX y]
  have hgX : (fun y ↦ mvfderiv I g y (X y)) = fun y ↦ -SmoothBundleForm.eval₂ σ y (X y) (Y y) := by
    funext y; rw [← isHamiltonianVectorField_iff.1 hY y, SmoothBundleForm.eval₂_swap]
  have hfY : (fun y ↦ mvfderiv I f y (Y y)) = fun y ↦ SmoothBundleForm.eval₂ σ y (X y) (Y y) := by
    funext y; rw [← isHamiltonianVectorField_iff.1 hX y]
  -- The bracket terms of `dσ(X, Y, W) = 0`.
  have hXWY : σ.val x ![mlieBracket I X W x, Y x] = -mvfderiv I g x (mlieBracket I X W x) := by
    rw [← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_swap,
      isHamiltonianVectorField_iff.1 hY x]
  have hYWX : σ.val x ![mlieBracket I Y W x, X x] = -mvfderiv I f x (mlieBracket I Y W x) := by
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

/-- **The pairing of two Hamiltonian vector fields is Hamiltonian.** For a closed form `σ` and
differentiable Hamiltonian vector fields `X` of `f` and `Y` of `g`, with `f` and `g` of class `C²`,
the function `σ(X, Y)` has the Hamiltonian vector field `-[X, Y]`. -/
theorem neg_mlieBracket (hσ : σ.IsClosed) (hX : σ.IsHamiltonianVectorField f X)
    (hY : σ.IsHamiltonianVectorField g Y) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hX' : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M)))
    (hY' : MDifferentiable I I.tangent (fun y ↦ (Y y : TangentBundle I M))) :
    σ.IsHamiltonianVectorField (fun y ↦ SmoothBundleForm.eval₂ σ y (X y) (Y y))
      (-VectorField.mlieBracket I X Y) :=
  isHamiltonianVectorField_iff.2 fun x v ↦ by
    rw [hX.mvfderiv_eval₂ hσ hY (hf x) (hg x) (hX' x) (hY' x), Pi.neg_apply,
      SmoothBundleForm.eval₂_neg_left]

/-- **The Jacobi identity for Hamiltonian vector fields.** For a closed form `σ` and Hamiltonian
vector fields `X`, `Y`, `Z` of functions `f`, `g`, `k` of class `C²` at `x`, with the three fields
differentiable at `x`, `σ([X, Y], Z) + σ([Y, Z], X) + σ([Z, X], Y) = 0` at `x`. No nondegeneracy is
needed. -/
theorem eval₂_mlieBracket_jacobi (hσ : σ.IsClosed) {k : M → ℝ} {Z : (x : M) → TangentSpace I x}
    (hX : σ.IsHamiltonianVectorField f X) (hY : σ.IsHamiltonianVectorField g Y)
    (hZ : σ.IsHamiltonianVectorField k Z) (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hk : ContMDiffAt I 𝓘(ℝ) 2 k x)
    (hX' : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY' : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hZ' : MDifferentiableAt I I.tangent (fun y ↦ (Z y : TangentBundle I M)) x) :
    SmoothBundleForm.eval₂ σ x (VectorField.mlieBracket I X Y x) (Z x) +
      SmoothBundleForm.eval₂ σ x (VectorField.mlieBracket I Y Z x) (X x) +
        SmoothBundleForm.eval₂ σ x (VectorField.mlieBracket I Z X x) (Y x) = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- `σ(Z, [X, Y]) = dk([X, Y]) = X(σ(Z, Y)) - Y(σ(Z, X))`, and each derivative is a bracket term.
  have hZY : (fun y ↦ mvfderiv I k y (Y y)) = fun y ↦ SmoothBundleForm.eval₂ σ y (Z y) (Y y) :=
    funext fun y ↦ (isHamiltonianVectorField_iff.1 hZ y (Y y)).symm
  have hZX : (fun y ↦ mvfderiv I k y (X y)) = fun y ↦ SmoothBundleForm.eval₂ σ y (Z y) (X y) :=
    funext fun y ↦ (isHamiltonianVectorField_iff.1 hZ y (X y)).symm
  have h := mvfderiv_mlieBracket hk (by simp) hX' hY'
  rw [hZY, hZX, hZ.mvfderiv_eval₂ hσ hY hk hg hZ' hY', hZ.mvfderiv_eval₂ hσ hX hk hf hZ' hX',
    ← isHamiltonianVectorField_iff.1 hZ x, mlieBracket_swap_apply (V := Z) (W := Y)] at h
  rw [SmoothBundleForm.eval₂_swap σ x (VectorField.mlieBracket I X Y x), h,
    SmoothBundleForm.eval₂_neg_left]
  ring

/-- **Poisson's theorem.** Let `σ` be a closed form and `X`, `Y`, `Z` Hamiltonian vector fields of
`f`, `g`, `k`, with `f`, `g`, `k` of class `C²` at `x` and `X`, `Y` differentiable at `x`. If `f`
and `g` are stationary along `Z` near `x`, then so is `σ(X, Y)` at `x`. No nondegeneracy is needed:
for a nondegenerate form this says that the first integrals of `k` are closed under the bracket
`(f, g) ↦ σ(X_f, X_g)`. -/
theorem mvfderiv_eval₂_apply_eq_zero (hσ : σ.IsClosed) {k : M → ℝ}
    {Z : (x : M) → TangentSpace I x} (hX : σ.IsHamiltonianVectorField f X)
    (hY : σ.IsHamiltonianVectorField g Y) (hZ : σ.IsHamiltonianVectorField k Z)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x)
    (hk : ContMDiffAt I 𝓘(ℝ) 2 k x)
    (hX' : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY' : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hfZ : ∀ᶠ y in 𝓝 x, mvfderiv I f y (Z y) = 0) (hgZ : ∀ᶠ y in 𝓝 x, mvfderiv I g y (Z y) = 0) :
    mvfderiv I (fun y ↦ SmoothBundleForm.eval₂ σ y (X y) (Y y)) x (Z x) = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- `dk(Y) = σ(Z, Y) = -dg(Z)` and `dk(X) = -df(Z)` vanish near `x`, so `dk([X, Y]) = 0` at `x`.
  have hkY : (fun y ↦ mvfderiv I k y (Y y)) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := hgZ.mono fun y hy ↦ by
    dsimp only
    rw [← isHamiltonianVectorField_iff.1 hZ y, SmoothBundleForm.eval₂_swap,
      isHamiltonianVectorField_iff.1 hY y, hy, neg_zero]
  have hkX : (fun y ↦ mvfderiv I k y (X y)) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := hfZ.mono fun y hy ↦ by
    dsimp only
    rw [← isHamiltonianVectorField_iff.1 hZ y, SmoothBundleForm.eval₂_swap,
      isHamiltonianVectorField_iff.1 hX y, hy, neg_zero]
  have h := mvfderiv_mlieBracket hk (by simp) hX' hY'
  rw [hkY.mvfderiv_eq, hkX.mvfderiv_eq, mvfderiv_const, zero_apply, zero_apply, sub_self] at h
  rw [hX.mvfderiv_eval₂ hσ hY hf hg hX' hY', SmoothBundleForm.eval₂_swap,
    isHamiltonianVectorField_iff.1 hZ x, h, neg_zero, neg_zero]

end IsHamiltonianVectorField

/-- **The bracket of symplectic vector fields is Hamiltonian.** For a closed two-form `σ` and
smooth vector fields `X`, `Y` with closed contractions, `[X, Y]` is a Hamiltonian vector field of
`σ(Y, X)`: `ι_{[X, Y]} σ = d(σ(Y, X))`. -/
theorem isHamiltonianVectorField_mlieBracket (hσ : σ.IsClosed)
    {X Y : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} (hX : X ∈ σ.symplecticVectorFields)
    (hY : Y ∈ σ.symplecticVectorFields) :
    σ.IsHamiltonianVectorField (fun x ↦ SmoothBundleForm.eval₂ σ x (Y x) (X x))
      (mlieBracket I X Y) := by
  refine isHamiltonianVectorField_iff.2 fun x v ↦ ?_
  -- Extend `v` to a vector field `Z`, differentiable at `x`.
  let Z : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hZ : MDifferentiableAt I I.tangent (fun y ↦ (Z y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E v
  have hZx : Z x = v := FiberBundle.extend_apply_self E v
  have hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x :=
    X.contMDiff.mdifferentiableAt (by simp)
  have hYd : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x :=
    Y.contMDiff.mdifferentiableAt (by simp)
  -- `L_X σ = 0`, evaluated on `(Y, Z)` by the bracket formula.
  have hL := mlieDerivForm_apply_vectorField (V := X) (X := ![Y, Z]) (σ.mdifferentiableAt x)
    (fun i ↦ by fin_cases i <;> assumption)
  have hL0 : mlieDerivForm X σ.val x (fun i ↦ ![⇑Y, Z] i x) = 0 := by
    rw [(mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ).1 hX]
    rfl
  -- `d(ι_Y σ) = 0`, evaluated on `(X, Z)` by the invariant formula.
  have hd := SmoothForm.mextDeriv_apply_one (φ := σ.interiorₗ Y) hXd hZ
  have hd0 : mextDeriv (σ.interiorₗ Y).val x ![X x, Z x] = 0 := by
    rw [coe_interiorₗ, mem_symplecticVectorFields_iff.1 hY]
    rfl
  have hfun : (fun y ↦ σ.val y fun i ↦ ![⇑Y, Z] i y) = fun y ↦ σ.val y ![Y y, Z y] := by
    funext y
    congr 1
    funext i
    fin_cases i <;> rfl
  have hu (w : TangentSpace I x) :
      Function.update (fun i ↦ ![⇑Y, Z] i x) 0 w = ![w, Z x] ∧
        Function.update (fun i ↦ ![⇑Y, Z] i x) 1 w = ![Y x, w] := by
    constructor <;> funext i <;> fin_cases i <;> rfl
  rw [hL0, hfun, Fin.sum_univ_two, (hu _).1, (hu _).2] at hL
  rw [hd0, coe_interiorₗ] at hd
  simp only [RoughForm.interior_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hL hd
  -- Subtracting the two identities leaves `σ([X, Y], Z) = Z(σ(Y, X))`.
  rw [← hZx]
  simp only [SmoothBundleForm.eval₂_apply]
  linarith

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (h : σ.IsNondegenerate)
include h

/-- For a nondegenerate closed form on a finite-dimensional manifold, the Hamiltonian vector field
of the Poisson bracket of two `C²` functions is `X_{{f, g}} = -[X_f, X_g]`. -/
theorem hamiltonianVectorField_poissonBracket (hσ : σ.IsClosed) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    σ.hamiltonianVectorField (σ.poissonBracket f g) =
      -mlieBracket I (σ.hamiltonianVectorField f) (σ.hamiltonianVectorField g) := by
  refine (h.isHamiltonianVectorField_iff_eq.1 ?_).symm
  rw [show σ.poissonBracket f g = _ from funext (σ.poissonBracket_def f g)]
  exact (h.isHamiltonianVectorField_hamiltonianVectorField f).neg_mlieBracket hσ
    (h.isHamiltonianVectorField_hamiltonianVectorField g) hf hg
    (h.mdifferentiable_hamiltonianVectorField hf) (h.mdifferentiable_hamiltonianVectorField hg)

/-- **Locally Poisson-commuting functions have commuting Hamiltonian vector fields.** For a
nondegenerate closed form on a finite-dimensional manifold and `C²` functions `f` and `g` whose
Poisson bracket vanishes near `x`, the Lie bracket `[X_f, X_g]` vanishes at `x`. -/
theorem mlieBracket_hamiltonianVectorField_eq_zero (hσ : σ.IsClosed) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (hfg : σ.poissonBracket f g =ᶠ[𝓝 x] fun _ ↦ 0) :
    mlieBracket I (σ.hamiltonianVectorField f) (σ.hamiltonianVectorField g) x = 0 := by
  have h0 := hamiltonianVectorField_eq_zero_of_eventuallyEq (σ := σ) hfg
  rwa [h.hamiltonianVectorField_poissonBracket hσ hf hg, Pi.neg_apply, neg_eq_zero] at h0

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
