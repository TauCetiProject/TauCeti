/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Hamiltonian
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Jacobi bracket of a contact form

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α`, and
write `X_f` for the contact Hamiltonian vector field of a function `f`, so that `α(X_f) = f` and
`ι_(X_f) dα = (R_α f) α - df`. The **Jacobi bracket** of two functions is

`{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)`

(`TauCeti.SmoothForm.jacobiBracket`). It is the bracket of functions induced by the Lie bracket of
contact vector fields: for `C²` functions,

`{f, g}_α = α([X_f, X_g])` and `X_({f, g}_α) = [X_f, X_g]`

(`TauCeti.SmoothForm.IsContactForm.apply_mlieBracket_contactHamiltonianVectorField` and
`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`). The second
identity rests on `d(dα) = 0`: the bracket of two contact Hamiltonian vector fields is again a
contact Hamiltonian vector field
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieBracket`).

Consequently it is a **Jacobi bracket** in the sense of Lichnerowicz:

* it is antisymmetric (`TauCeti.SmoothForm.neg_jacobiBracket`) and bilinear on differentiable
  functions (`TauCeti.SmoothForm.jacobiBracket_add_left`,
  `TauCeti.SmoothForm.jacobiBracket_const_smul_left`);
* it is a first-order differential operator in each argument rather than a derivation, obeying
  the generalized Leibniz rule `{f, g k} = g {f, k} + k {f, g} + g k R_α(f)`, where
  `R_α(f) = -{f, 1}` (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_mul_right`);
* it satisfies the **Jacobi identity** `{f, {g, k}} + {g, {k, f}} + {k, {f, g}} = 0` for `C²`
  functions (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_jacobi`). The proof expands
  `X_({g, k}) = [X_g, X_k]` and uses the Reeb derivative of the bracket,
  `R_α({f, g}) = X_f(R_α g) - X_g(R_α f)`
  (`TauCeti.SmoothForm.IsContactForm.mvfderiv_jacobiBracket_reebVectorField`).

Unlike a Poisson bracket, `{1, g}_α = R_α(g)` need not vanish
(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_const_left`). The bracket can also be computed as
the derivative of `g` along `X_f`, corrected by the Reeb derivative of `f`:
`{f, g}_α = X_f(g) - g R_α(f)` (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_mvfderiv`).

## References

* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced
  Mathematics 109 (2008), Section 2.3.
* André Lichnerowicz, *Les variétés de Jacobi et leurs algèbres de Lie associées*, J. Math. Pures
  Appl. 57 (1978), 453–488.
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g k : M → ℝ} {X Y : (x : M) → TangentSpace I x} {x : M}

/-! ### The bracket -/

/-- The **Jacobi bracket** `{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)` of two functions, where
`X_f` and `X_g` are the contact Hamiltonian vector fields of `f` and `g` and `R_α` is the Reeb
vector field of `α`. For a contact form and `C²` functions it equals `α([X_f, X_g])`
(`TauCeti.SmoothForm.IsContactForm.apply_mlieBracket_contactHamiltonianVectorField`). -/
def jacobiBracket (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) : ℝ :=
  mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, α.contactHamiltonianVectorField g x] +
    f x * mvfderiv I g x (α.reebVectorField x) - g x * mvfderiv I f x (α.reebVectorField x)

/-- The Jacobi bracket unfolds as `dα(X_f, X_g) + f R_α(g) - g R_α(f)`. -/
theorem jacobiBracket_def (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) :
    α.jacobiBracket f g x =
      mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, α.contactHamiltonianVectorField g x] +
        f x * mvfderiv I g x (α.reebVectorField x) - g x * mvfderiv I f x (α.reebVectorField x) :=
  (rfl)

/-- The Jacobi bracket is antisymmetric. -/
theorem neg_jacobiBracket (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) :
    -α.jacobiBracket g f x = α.jacobiBracket f g x := by
  rw [jacobiBracket_def, jacobiBracket_def, mextDeriv_apply_swap α.1 x]
  ring

/-- The Jacobi bracket of a function with itself vanishes. -/
@[simp]
theorem jacobiBracket_self (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    α.jacobiBracket f f x = 0 := by
  have := neg_jacobiBracket α f f x
  linarith

/-- Negating the first argument negates the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_neg_left (x : M) :
    α.jacobiBracket (-f) g x = -α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, mextDeriv_eq_bilinFormAt, contactHamiltonianVectorField_neg,
    map_neg, LinearMap.neg_apply, mvfderiv_neg, Pi.neg_apply, neg_apply]
  ring

/-- Negating the second argument negates the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_neg_right (x : M) :
    α.jacobiBracket f (-g) x = -α.jacobiBracket f g x := by
  rw [← neg_jacobiBracket, jacobiBracket_neg_left, neg_jacobiBracket]

/-- Multiplying the first argument by a real constant scales the Jacobi bracket. -/
theorem jacobiBracket_const_smul_left (c : ℝ) (x : M) :
    α.jacobiBracket (c • f) g x = c • α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, mextDeriv_eq_bilinFormAt, contactHamiltonianVectorField_const_smul,
    map_smul, LinearMap.smul_apply, mvfderiv_const_smul_field, Pi.smul_apply,
    smul_apply, smul_eq_mul]
  ring

/-- Multiplying the second argument by a real constant scales the Jacobi bracket. -/
theorem jacobiBracket_const_smul_right (c : ℝ) (x : M) :
    α.jacobiBracket f (c • g) x = c • α.jacobiBracket f g x := by
  rw [← neg_jacobiBracket, jacobiBracket_const_smul_left, ← neg_jacobiBracket α f g, smul_neg]

/-- The Jacobi bracket is additive in its first argument on functions differentiable at the
point. -/
theorem jacobiBracket_add_left (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.jacobiBracket (f + g) k x = α.jacobiBracket f k x + α.jacobiBracket g k x := by
  simp only [jacobiBracket_def, mextDeriv_eq_bilinFormAt, contactHamiltonianVectorField_add hf hg,
    map_add, LinearMap.add_apply, mvfderiv_add hf hg, Pi.add_apply,
    add_apply]
  ring

/-- The Jacobi bracket is additive in its second argument on functions differentiable at the
point. -/
theorem jacobiBracket_add_right (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.jacobiBracket k (f + g) x = α.jacobiBracket k f x + α.jacobiBracket k g x := by
  rw [← neg_jacobiBracket, jacobiBracket_add_left hf hg, ← neg_jacobiBracket α k f,
    ← neg_jacobiBracket α k g]
  ring

/-! ### Contact Hamiltonian vector fields -/

namespace IsContactHamiltonianVectorField

/-- **Derivative of a contact Hamiltonian along another contact Hamiltonian vector field.** If `X`
and `Y` are contact Hamiltonian vector fields of `f` and `g`, then
`X(g) = f R_α(g) + dα(X, Y)`. -/
theorem mvfderiv_apply_eq (hY : α.IsContactHamiltonianVectorField g Y)
    (hX : α.IsContactHamiltonianVectorField f X) (x : M) :
    mvfderiv I g x (X x) =
      f x * mvfderiv I g x (α.reebVectorField x) + mextDeriv α.1 x ![X x, Y x] := by
  have h := hY.mextDeriv_apply_eq x (X x)
  rw [hX.apply_eq, mextDeriv_apply_swap] at h
  linarith

/-- **The contact form on the bracket of contact Hamiltonian vector fields.** If `X` and `Y` are
contact Hamiltonian vector fields of `f` and `g`, differentiable at `x`, then
`α([X, Y]) = dα(X, Y) + f R_α(g) - g R_α(f)` at `x`. -/
theorem apply_mlieBracket (hX : α.IsContactHamiltonianVectorField f X)
    (hY : α.IsContactHamiltonianVectorField g Y)
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hYd : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x) :
    α.1 x ![mlieBracket I X Y x] = mextDeriv α.1 x ![X x, Y x] +
      f x * mvfderiv I g x (α.reebVectorField x) - g x * mvfderiv I f x (α.reebVectorField x) := by
  -- The invariant formula `dα(X, Y) = X(α(Y)) - Y(α(X)) - α([X, Y])`, with `α(X) = f` and
  -- `α(Y) = g`.
  have h := SmoothForm.mextDeriv_apply_one (φ := α) hXd hYd
  have hfX : (fun y ↦ α.1 y ![X y]) = f := funext hX.apply_eq
  have hgY : (fun y ↦ α.1 y ![Y y]) = g := funext hY.apply_eq
  rw [hfX, hgY, hY.mvfderiv_apply_eq hX, hX.mvfderiv_apply_eq hY,
    mextDeriv_apply_swap α.1 x (Y x)] at h
  linarith

/-- The contraction of `dα` with the bracket of contact Hamiltonian vector fields `X` of `f` and
`Y` of `g`: `ι_([X, Y]) dα = (X(R_α g) - Y(R_α f)) α - dh`, where
`h = dα(X, Y) + f R_α(g) - g R_α(f)`. It is obtained by evaluating `d(dα)(X, Y, W) = 0` with the
invariant formula and substituting the defining equations of `X` and `Y`. -/
private theorem mextDeriv_mlieBracket_apply [CompleteSpace E]
    (hX : α.IsContactHamiltonianVectorField f X)
    (hY : α.IsContactHamiltonianVectorField g Y) (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x)
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hYd : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hRf : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I f y (α.reebVectorField y)) x)
    (hRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x)
    (v : TangentSpace I x) :
    mextDeriv α.1 x ![mlieBracket I X Y x, v] =
      (mvfderiv I (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x (X x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (α.reebVectorField y)) x (Y x)) * α.1 x ![v] -
      mvfderiv I (fun y ↦ mextDeriv α.1 y ![X y, Y y] +
        f y * mvfderiv I g y (α.reebVectorField y) -
        g y * mvfderiv I f y (α.reebVectorField y)) x v := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  -- Extend `v` to a vector field `W`, differentiable at `x`.
  set W : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E v
  have hWx : W x = v := FiberBundle.extend_apply_self E v
  -- Differentiability of the functions whose derivatives appear below.
  have hA : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mextDeriv α.1 y ![X y, Y y]) x := by
    simpa only [mextDerivₗ_apply] using
      (mextDerivₗ I 1 α).mdifferentiableAt_apply_vectorField (V := fun i y ↦ ![X y, Y y] i)
        fun i ↦ by fin_cases i <;> assumption
  have hαW : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ α.1 y ![W y]) x :=
    α.mdifferentiableAt_apply_vectorField (V := fun i y ↦ ![W y] i)
      fun i ↦ by fin_cases i; exact hW
  have hfRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y * mvfderiv I g y (α.reebVectorField y)) x :=
    (hf.mdifferentiableAt two_ne_zero).mul hRg
  have hgRf : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ g y * mvfderiv I f y (α.reebVectorField y)) x :=
    (hg.mdifferentiableAt two_ne_zero).mul hRf
  have hRgαW : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ mvfderiv I g y (α.reebVectorField y) * α.1 y ![W y]) x := hRg.mul hαW
  have hRfαW : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ mvfderiv I f y (α.reebVectorField y) * α.1 y ![W y]) x := hRf.mul hαW
  have hdgW := mdifferentiableAt_mvfderiv_apply hg h2 hW
  have hdfW := mdifferentiableAt_mvfderiv_apply hf h2 hW
  -- `d(dα)(X, Y, W) = 0`, expanded by the invariant formula.
  have hdd := SmoothForm.mextDeriv_apply_two (φ := mextDerivₗ I 1 α) hXd hYd hW
  simp only [mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero] at hdd
  -- The derivatives of `α(W)` along `X` and `Y`, from `L_X α = (R_α f) α` and `L_Y α = (R_α g) α`.
  have hLX := hX.mvfderiv_apply_sub_apply_mlieBracket hXd hW
  have hLY := hY.mvfderiv_apply_sub_apply_mlieBracket hYd hW
  -- The bracket terms `dα([X, W], Y)` and `dα([Y, W], X)`.
  have hXWY := hY.mextDeriv_apply_eq x (mlieBracket I X W x)
  have hYWX := hX.mextDeriv_apply_eq x (mlieBracket I Y W x)
  -- The derivative along `W` of `Y(f)`; that of `X(g)` is `hY.mvfderiv_apply_eq hX`.
  have efY : (fun y ↦ mvfderiv I f y (Y y)) =
      fun y ↦ g y * mvfderiv I f y (α.reebVectorField y) - mextDeriv α.1 y ![X y, Y y] := by
    funext y
    rw [hX.mvfderiv_apply_eq hY y, mextDeriv_apply_swap α.1 y (Y y)]
    ring
  rw [mvfderiv_mlieBracket hg h2 hXd hW, funext fun y ↦ hY.mvfderiv_apply_eq hX y,
    mvfderiv_fun_add hfRg hA] at hXWY
  rw [mvfderiv_mlieBracket hf h2 hYd hW, efY, mvfderiv_fun_sub hgRf hA] at hYWX
  -- The terms differentiating `dα(Y, W)` and `dα(X, W)`.
  rw [mextDeriv_apply_swap α.1 x (mlieBracket I X W x),
    mextDeriv_apply_swap α.1 x (mlieBracket I Y W x),
    funext fun y ↦ hY.mextDeriv_apply_eq y (W y), funext fun y ↦ hX.mextDeriv_apply_eq y (W y),
    mvfderiv_fun_sub hRgαW hdgW, mvfderiv_fun_sub hRfαW hdfW,
    mvfderiv_fun_mul hRg hαW, mvfderiv_fun_mul hRf hαW] at hdd
  have hAfRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mextDeriv α.1 y ![X y, Y y] +
      f y * mvfderiv I g y (α.reebVectorField y)) x := hA.add hfRg
  rw [mvfderiv_fun_sub hAfRg hgRf, mvfderiv_fun_add hA hfRg]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul] at hdd hXWY hYWX ⊢
  rw [← hWx]
  linear_combination hdd - hXWY + hYWX + mvfderiv I g x (α.reebVectorField x) * hLX -
    mvfderiv I f x (α.reebVectorField x) * hLY

end IsContactHamiltonianVectorField

/-! ### Contact forms -/

variable [FiniteDimensional ℝ E]

/-- **The bracket of contact Hamiltonian vector fields is a contact Hamiltonian vector field.**
For a contact form `α` and differentiable contact Hamiltonian vector fields `X` of `f` and `Y` of
`g`, with `f` and `g` of class `C²`, the Lie bracket `[X, Y]` is the contact Hamiltonian vector
field of `α([X, Y])`. -/
theorem IsContactHamiltonianVectorField.mlieBracket (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hY : α.IsContactHamiltonianVectorField g Y)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M)))
    (hYd : MDifferentiable I I.tangent (fun y ↦ (Y y : TangentBundle I M))) :
    α.IsContactHamiltonianVectorField (fun y ↦ α.1 y ![mlieBracket I X Y y])
      (mlieBracket I X Y) := by
  refine isContactHamiltonianVectorField_iff.2 fun x ↦ ⟨rfl, fun v ↦ ?_⟩
  have hfun : (fun y ↦ α.1 y ![VectorField.mlieBracket I X Y y]) =
      fun y ↦ mextDeriv α.1 y ![X y, Y y] +
        f y * mvfderiv I g y (α.reebVectorField y) - g y * mvfderiv I f y (α.reebVectorField y) :=
    funext fun y ↦ hX.apply_mlieBracket hY (hXd y) (hYd y)
  have key := hX.mextDeriv_mlieBracket_apply hY (hf x) (hg x) (hXd x) (hYd x)
    (hα.mdifferentiable_mvfderiv_reebVectorField hf x)
    (hα.mdifferentiable_mvfderiv_reebVectorField hg x)
  -- Evaluating at the Reeb vector field identifies the multiplier with `R_α` of the Hamiltonian.
  have hR := key (α.reebVectorField x)
  rw [hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField, mul_one] at hR
  rw [hfun, key v]
  linear_combination -α.1 x ![v] * hR

namespace IsContactForm

variable (hα : α.IsContactForm)
include hα

/-- The Jacobi bracket is the derivative of `g` along `X_f`, corrected by the Reeb derivative of
`f`: `{f, g}_α = X_f(g) - g R_α(f)`. -/
theorem jacobiBracket_eq_mvfderiv (f g : M → ℝ) (x : M) :
    α.jacobiBracket f g x = mvfderiv I g x (α.contactHamiltonianVectorField f x) -
      g x * mvfderiv I f x (α.reebVectorField x) := by
  rw [jacobiBracket_def,
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g).mvfderiv_apply_eq
      (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f)]
  ring

/-- The Jacobi bracket is minus the derivative of `f` along `X_g`, corrected by the Reeb
derivative of `g`: `{f, g}_α = -X_g(f) + f R_α(g)`. -/
theorem jacobiBracket_eq_neg_mvfderiv (f g : M → ℝ) (x : M) :
    α.jacobiBracket f g x = -mvfderiv I f x (α.contactHamiltonianVectorField g x) +
      f x * mvfderiv I g x (α.reebVectorField x) := by
  rw [← neg_jacobiBracket, hα.jacobiBracket_eq_mvfderiv]
  ring

/-- The Jacobi bracket with a constant `c` on the left is `c` times the Reeb derivative:
`{c, g}_α = c R_α(g)`. In particular `{1, g}_α = R_α(g)`, so the Jacobi bracket is not a Poisson
bracket. -/
theorem jacobiBracket_const_left (c : ℝ) (g : M → ℝ) (x : M) :
    α.jacobiBracket (fun _ ↦ c) g x = c * mvfderiv I g x (α.reebVectorField x) := by
  rw [jacobiBracket_def, hα.contactHamiltonianVectorField_const, Pi.smul_apply,
    mextDeriv_apply_smul_left, hα.mextDeriv_reebVectorField_left, mvfderiv_const]
  simp

/-- The Jacobi bracket with a constant `c` on the right is `-c` times the Reeb derivative:
`{f, c}_α = -c R_α(f)`. -/
theorem jacobiBracket_const_right (f : M → ℝ) (c : ℝ) (x : M) :
    α.jacobiBracket f (fun _ ↦ c) x = -(c * mvfderiv I f x (α.reebVectorField x)) := by
  rw [← neg_jacobiBracket, hα.jacobiBracket_const_left]

/-- **The generalized Leibniz rule** in the second argument, on functions differentiable at the
point: `{f, g k}_α = g {f, k}_α + k {f, g}_α + g k R_α(f)`. Since `R_α(f) = -{f, 1}_α`, this is
the first-order Leibniz rule `{f, g k} = g {f, k} + k {f, g} - g k {f, 1}` of a Jacobi bracket. -/
theorem jacobiBracket_mul_right (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hk : MDifferentiableAt I 𝓘(ℝ) k x) :
    α.jacobiBracket f (g * k) x = g x * α.jacobiBracket f k x + k x * α.jacobiBracket f g x +
      g x * k x * mvfderiv I f x (α.reebVectorField x) := by
  simp only [hα.jacobiBracket_eq_mvfderiv, mvfderiv_mul hg hk, add_apply, smul_apply,
    smul_eq_mul, Pi.mul_apply]
  ring

/-- **The generalized Leibniz rule** in the first argument, on functions differentiable at the
point: `{g k, f}_α = g {k, f}_α + k {g, f}_α - g k R_α(f)`. -/
theorem jacobiBracket_mul_left (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hk : MDifferentiableAt I 𝓘(ℝ) k x) :
    α.jacobiBracket (g * k) f x = g x * α.jacobiBracket k f x + k x * α.jacobiBracket g f x -
      g x * k x * mvfderiv I f x (α.reebVectorField x) := by
  rw [← neg_jacobiBracket, hα.jacobiBracket_mul_right hg hk, ← neg_jacobiBracket α k f,
    ← neg_jacobiBracket α g f]
  ring

/-- **The Jacobi bracket is induced by the Lie bracket of contact vector fields**:
`α([X_f, X_g]) = {f, g}_α` at points where `X_f` and `X_g` are differentiable, for instance
everywhere when `f` and `g` are `C²`
(`TauCeti.SmoothForm.IsContactForm.mdifferentiable_contactHamiltonianVectorField`). -/
theorem apply_mlieBracket_contactHamiltonianVectorField
    (hf : MDifferentiableAt I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) x)
    (hg : MDifferentiableAt I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField g y : TangentBundle I M)) x) :
    α.1 x ![mlieBracket I (α.contactHamiltonianVectorField f)
      (α.contactHamiltonianVectorField g) x] = α.jacobiBracket f g x :=
  (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).apply_mlieBracket
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g) hf hg

/-- **The contact Hamiltonian vector field of a Jacobi bracket** of `C²` functions is the Lie
bracket of their contact Hamiltonian vector fields: `X_({f, g}_α) = [X_f, X_g]`. -/
theorem contactHamiltonianVectorField_jacobiBracket (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    α.contactHamiltonianVectorField (α.jacobiBracket f g) =
      mlieBracket I (α.contactHamiltonianVectorField f) (α.contactHamiltonianVectorField g) := by
  have hXf := hα.mdifferentiable_contactHamiltonianVectorField hf
  have hXg := hα.mdifferentiable_contactHamiltonianVectorField hg
  have h := (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).mlieBracket hα
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g) hf hg hXf hXg
  have hfun : (fun y ↦ α.1 y ![mlieBracket I (α.contactHamiltonianVectorField f)
      (α.contactHamiltonianVectorField g) y]) = α.jacobiBracket f g :=
    funext fun y ↦ hα.apply_mlieBracket_contactHamiltonianVectorField (hXf y) (hXg y)
  rw [hfun] at h
  exact (hα.isContactHamiltonianVectorField_iff_eq.1 h).symm

/-- **The Reeb derivative of a Jacobi bracket.** For `C²` functions `f` and `g`,
`R_α({f, g}_α) = X_f(R_α g) - X_g(R_α f)`. -/
theorem mvfderiv_jacobiBracket_reebVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    mvfderiv I (α.jacobiBracket f g) x (α.reebVectorField x) =
      mvfderiv I (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x
          (α.contactHamiltonianVectorField f x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (α.reebVectorField y)) x
          (α.contactHamiltonianVectorField g x) := by
  have h := (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField
    f).mextDeriv_mlieBracket_apply
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g) (hf x) (hg x)
    (hα.mdifferentiable_contactHamiltonianVectorField hf x)
    (hα.mdifferentiable_contactHamiltonianVectorField hg x)
    (hα.mdifferentiable_mvfderiv_reebVectorField hf x)
    (hα.mdifferentiable_mvfderiv_reebVectorField hg x) (α.reebVectorField x)
  rw [hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField, mul_one] at h
  have hfun : α.jacobiBracket f g = fun y ↦
      mextDeriv α.1 y ![α.contactHamiltonianVectorField f y, α.contactHamiltonianVectorField g y] +
        f y * mvfderiv I g y (α.reebVectorField y) - g y * mvfderiv I f y (α.reebVectorField y) :=
    funext (jacobiBracket_def α f g)
  rw [hfun]
  linarith

/-- **The Jacobi identity for the Jacobi bracket.** For a contact form on a finite-dimensional
manifold and `C²` functions `f`, `g`, `k`,
`{f, {g, k}_α}_α + {g, {k, f}_α}_α + {k, {f, g}_α}_α = 0`. -/
theorem jacobiBracket_jacobi (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hk : ContMDiff I 𝓘(ℝ) 2 k) (x : M) :
    α.jacobiBracket f (α.jacobiBracket g k) x + α.jacobiBracket g (α.jacobiBracket k f) x +
      α.jacobiBracket k (α.jacobiBracket f g) x = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have hXg := hα.mdifferentiable_contactHamiltonianVectorField hg x
  have hXk := hα.mdifferentiable_contactHamiltonianVectorField hk x
  have hdf := (hf x).mdifferentiableAt two_ne_zero
  have hRg := hα.mdifferentiable_mvfderiv_reebVectorField hg x
  have hRk := hα.mdifferentiable_mvfderiv_reebVectorField hk x
  have hfRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y * mvfderiv I g y (α.reebVectorField y)) x :=
    hdf.mul hRg
  have hfRk : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y * mvfderiv I k y (α.reebVectorField y)) x :=
    hdf.mul hRk
  -- `X_k(f) = {k, f} + f R_α(k)` and `X_g(f) = f R_α(g) - {f, g}`, as functions.
  have ekf : (fun y ↦ mvfderiv I f y (α.contactHamiltonianVectorField k y)) =
      fun y ↦ α.jacobiBracket k f y + f y * mvfderiv I k y (α.reebVectorField y) :=
    funext fun y ↦ by rw [hα.jacobiBracket_eq_mvfderiv]; ring
  have egf : (fun y ↦ mvfderiv I f y (α.contactHamiltonianVectorField g y)) =
      fun y ↦ f y * mvfderiv I g y (α.reebVectorField y) - α.jacobiBracket f g y :=
    funext fun y ↦ by rw [hα.jacobiBracket_eq_neg_mvfderiv]; ring
  have hkf : MDifferentiableAt I 𝓘(ℝ) (α.jacobiBracket k f) x := by
    rw [funext (hα.jacobiBracket_eq_mvfderiv k f)]
    exact (mdifferentiableAt_mvfderiv_apply (hf x) h2 hXk).sub hfRk
  have hfg : MDifferentiableAt I 𝓘(ℝ) (α.jacobiBracket f g) x := by
    rw [funext (hα.jacobiBracket_eq_neg_mvfderiv f g)]
    exact (mdifferentiableAt_mvfderiv_apply (hf x) h2 hXg).neg.add hfRg
  -- Expand `{f, {g, k}} = -[X_g, X_k](f) + f R_α({g, k})`.
  have h1 := hα.jacobiBracket_eq_neg_mvfderiv f (α.jacobiBracket g k) x
  rw [hα.contactHamiltonianVectorField_jacobiBracket hg hk,
    mvfderiv_mlieBracket (hf x) h2 hXg hXk, ekf, egf, mvfderiv_fun_add hkf hfRk,
    mvfderiv_fun_sub hfRg hfg, mvfderiv_fun_mul hdf hRk, mvfderiv_fun_mul hdf hRg,
    hα.mvfderiv_jacobiBracket_reebVectorField hg hk] at h1
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul] at h1
  linear_combination h1 + hα.jacobiBracket_eq_mvfderiv g (α.jacobiBracket k f) x +
    hα.jacobiBracket_eq_mvfderiv k (α.jacobiBracket f g) x -
    mvfderiv I g x (α.reebVectorField x) * hα.jacobiBracket_eq_mvfderiv k f x -
    mvfderiv I k x (α.reebVectorField x) * hα.jacobiBracket_eq_neg_mvfderiv f g x

end IsContactForm

end SmoothForm

end TauCeti
