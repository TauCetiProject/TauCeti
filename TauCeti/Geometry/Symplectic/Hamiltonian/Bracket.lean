/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# Lie brackets of Hamiltonian vector fields and the Jacobi identity

Let `σ` be a closed two-form on a manifold `M`. If `X` and `Y` are symplectic vector fields, that
is smooth vector fields with closed contractions `ι_X σ` and `ι_Y σ`, then their Lie bracket is a
Hamiltonian vector field, with Hamiltonian `σ(Y, X)`:

`ι_{[X, Y]} σ = d(σ(Y, X))`

(`TauCeti.SmoothTwoForm.isHamiltonianVectorField_mlieBracket`).

For a closed nondegenerate form on a finite-dimensional manifold, with the conventions
`ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`, this gives for smooth functions

`X_{{f, g}} = -[X_f, X_g]`

(`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`), so `f ↦ -X_f`
turns Poisson brackets into Lie brackets of vector fields. Differentiating `f` along this bracket
gives the Leibniz rule `{f, {g, k}} = {{f, g}, k} + {g, {f, k}}`
(`TauCeti.SmoothTwoForm.IsNondegenerate.leibniz_poissonBracket`), that is, the **Jacobi identity**
for the Poisson bracket (`TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_jacobi`), the
identity which, with antisymmetry, makes the Poisson bracket a Lie bracket.

## Main statements

* `TauCeti.SmoothTwoForm.isHamiltonianVectorField_mlieBracket`: the bracket of two symplectic
  vector fields is Hamiltonian.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`:
  `X_{{f, g}} = -[X_f, X_g]`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.leibniz_poissonBracket` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_jacobi`: the Jacobi identity.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.1 (Lie brackets of symplectic and Hamiltonian vector fields, and the Poisson
  bracket).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18 (Hamiltonian and symplectic vector fields, Poisson brackets).
-/

public section

noncomputable section

open VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- **The bracket of symplectic vector fields is Hamiltonian.** For a closed two-form `σ` and
smooth vector fields `X`, `Y` with closed contractions, `[X, Y]` is a Hamiltonian vector field of
`σ(Y, X)`: `ι_{[X, Y]} σ = d(σ(Y, X))`. -/
theorem isHamiltonianVectorField_mlieBracket (hσ : σ.IsClosed)
    {X Y : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} (hX : X ∈ σ.symplecticVectorFields)
    (hY : Y ∈ σ.symplecticVectorFields) :
    σ.IsHamiltonianVectorField (fun x ↦ SmoothForm.eval₂ σ x (Y x) (X x))
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
  have hL0 : mlieDerivForm X σ.1 x (fun i ↦ ![⇑Y, Z] i x) = 0 := by
    rw [(mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ).1 hX]
    rfl
  -- `d(ι_Y σ) = 0`, evaluated on `(X, Z)` by the invariant formula.
  have hd := SmoothForm.mextDeriv_apply_one (φ := σ.interiorₗ Y) hXd hZ
  have hd0 : mextDeriv (σ.interiorₗ Y).1 x ![X x, Z x] = 0 := by
    rw [coe_interiorₗ, mem_symplecticVectorFields_iff.1 hY]
    rfl
  have hfun : (fun y ↦ σ.1 y fun i ↦ ![⇑Y, Z] i y) = fun y ↦ σ.1 y ![Y y, Z y] := by
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
  simp only [SmoothForm.eval₂_apply]
  linarith

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] (h : σ.IsNondegenerate) {f g k : M → ℝ}
include h

/-- The Hamiltonian vector field of a smooth function, as a smooth vector field. -/
private def hamiltonianSection (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ :=
  ⟨σ.hamiltonianVectorField f, h.contMDiff_hamiltonianVectorField le_rfl (by simpa using hf)⟩

private theorem coe_hamiltonianSection (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ⇑(h.hamiltonianSection hf) = σ.hamiltonianVectorField f :=
  (rfl)

private theorem hamiltonianSection_mem (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    h.hamiltonianSection hf ∈ σ.symplecticVectorFields :=
  mem_symplecticVectorFields_of_isHamiltonianVectorField
    (φ := ⟨RoughForm.ofFunction I f, (isSmoothForm_ofFunction_iff.mpr hf).mem_smoothForms⟩)
    (by simpa only [RoughForm.ofFunction_apply, coe_hamiltonianSection] using
      h.isHamiltonianVectorField_hamiltonianVectorField f)

/-- **The Hamiltonian vector field of a Poisson bracket.** For a closed nondegenerate form on a
finite-dimensional manifold and smooth functions `f`, `g`, `X_{{f, g}} = -[X_f, X_g]`. -/
theorem hamiltonianVectorField_poissonBracket (hσ : σ.IsClosed) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) :
    σ.hamiltonianVectorField (σ.poissonBracket f g) =
      -mlieBracket I (σ.hamiltonianVectorField f) (σ.hamiltonianVectorField g) := by
  have hc := h.isHamiltonianVectorField_iff_eq.1 (isHamiltonianVectorField_mlieBracket hσ
    (h.hamiltonianSection_mem hf) (h.hamiltonianSection_mem hg))
  have hfg : (fun x ↦ SmoothForm.eval₂ σ x (σ.hamiltonianVectorField g x)
      (σ.hamiltonianVectorField f x)) = -σ.poissonBracket f g :=
    funext fun x ↦ by rw [Pi.neg_apply, ← neg_poissonBracket σ f g x, neg_neg, poissonBracket_def]
  funext x
  have hx := congrFun hc x
  rw [coe_hamiltonianSection, coe_hamiltonianSection, hfg, hamiltonianVectorField_neg] at hx
  rw [Pi.neg_apply, hx, neg_neg]

/-- **The Jacobi identity**, in Leibniz form: for a closed nondegenerate form on a
finite-dimensional manifold, `{f, ·}` is a derivation of the Poisson bracket of smooth functions,
`{f, {g, k}} = {{f, g}, k} + {g, {f, k}}`. -/
theorem leibniz_poissonBracket (hσ : σ.IsClosed) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hk : ContMDiff I 𝓘(ℝ) ∞ k) (x : M) :
    σ.poissonBracket f (σ.poissonBracket g k) x =
      σ.poissonBracket (σ.poissonBracket f g) k x +
        σ.poissonBracket g (σ.poissonBracket f k) x := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hXg := ((h.hamiltonianSection hg).contMDiff x).mdifferentiableAt (by simp)
  have hXk := ((h.hamiltonianSection hk).contMDiff x).mdifferentiableAt (by simp)
  rw [coe_hamiltonianSection] at hXg hXk
  have e (l : M → ℝ) : (fun y ↦ mvfderiv I f y (σ.hamiltonianVectorField l y)) =
      σ.poissonBracket f l :=
    funext fun y ↦ (h.poissonBracket_eq_mvfderiv f l y).symm
  -- `{f, {g, k}} = df(X_{{g, k}}) = -df([X_g, X_k])`, a commutator of derivatives of `f`.
  rw [h.poissonBracket_eq_mvfderiv f, h.hamiltonianVectorField_poissonBracket hσ hg hk,
    Pi.neg_apply, map_neg, mvfderiv_mlieBracket (n := ∞) (hf x) (by simp) hXg hXk, e, e,
    ← h.poissonBracket_eq_mvfderiv, ← h.poissonBracket_eq_mvfderiv,
    ← neg_poissonBracket σ g (σ.poissonBracket f k)]
  ring

/-- **The Jacobi identity** for the Poisson bracket of smooth functions with respect to a closed
nondegenerate form on a finite-dimensional manifold:
`{f, {g, k}} + {g, {k, f}} + {k, {f, g}} = 0`. -/
theorem poissonBracket_jacobi (hσ : σ.IsClosed) (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ) ∞ g) (hk : ContMDiff I 𝓘(ℝ) ∞ k) (x : M) :
    σ.poissonBracket f (σ.poissonBracket g k) x + σ.poissonBracket g (σ.poissonBracket k f) x +
      σ.poissonBracket k (σ.poissonBracket f g) x = 0 := by
  have hkf : σ.poissonBracket k f = -σ.poissonBracket f k :=
    funext fun y ↦ (neg_poissonBracket σ k f y).symm
  rw [h.leibniz_poissonBracket hσ hf hg hk, hkf, poissonBracket_neg_right,
    ← neg_poissonBracket σ (σ.poissonBracket f g) k]
  ring

end IsNondegenerate

end SmoothTwoForm

end TauCeti
