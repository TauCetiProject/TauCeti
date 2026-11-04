/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import TauCeti.Geometry.Contact.Hamiltonian
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Jacobi bracket of a contact form

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α`, and
use the convention `α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df` for the contact Hamiltonian vector
field `X_f` of a function `f`. The **Jacobi bracket** of two functions is

`{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)`

(`TauCeti.SmoothForm.contactBracket`). The defining equation of `X_g` rewrites it as
`{f, g}_α = X_f(g) - g R_α(f)`
(`TauCeti.SmoothForm.IsContactForm.contactBracket_eq_mvfderiv`).

The bracket comes from the Lie bracket of contact vector fields. If `X` and `Y` are contact
Hamiltonian vector fields of `C²` functions `f` and `g`, then `[X, Y]` is the contact Hamiltonian
vector field of `X(g) - g R_α(f)`
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieBracket`). The proof evaluates the
identity `d(dα) = 0` on `X`, `Y` and an extension of a tangent vector, using
`L_X α = (R_α f) α` and `L_Y α = (R_α g) α`. Consequently

`α([X_f, X_g]) = {f, g}_α` and `X_{{f, g}_α} = [X_f, X_g]`

(`TauCeti.SmoothForm.IsContactForm.apply_mlieBracket_contactHamiltonianVectorField` and
`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_contactBracket`). With these sign
conventions `f ↦ X_f` is a Lie algebra map, unlike the symplectic convention
`X_{{f, g}} = -[X_f, X_g]` of
`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`.

On smooth functions the bracket is a Jacobi bracket in the sense of Lichnerowicz:

* it is antisymmetric and real bilinear (`TauCeti.SmoothForm.neg_contactBracket` and the
  `add`, `neg` and `const_smul` lemmas);
* it is a first-order differential operator in each argument rather than a derivation:
  `{f, g k}_α = g {f, k}_α + k {f, g}_α - g k {f, 1}_α`, where `{f, 1}_α = -R_α f`
  (`TauCeti.SmoothForm.IsContactForm.contactBracket_mul_right` and
  `TauCeti.SmoothForm.IsContactForm.contactBracket_one_right`);
* it satisfies the **Jacobi identity**
  `{f, {g, k}_α}_α + {g, {k, f}_α}_α + {k, {f, g}_α}_α = 0` for `C²` functions
  (`TauCeti.SmoothForm.IsContactForm.contactBracket_jacobi`).

The bracket with the constant `1` is the Reeb derivative, `{1, g}_α = R_α g`
(`TauCeti.SmoothForm.IsContactForm.contactBracket_one_left`), so `{f, ·}_α` is a derivation
where `R_α f = 0`. The Reeb derivative of a bracket is `R_α {f, g}_α = X_f(R_α g) - X_g(R_α f)`
(`TauCeti.SmoothForm.IsContactForm.mvfderiv_contactBracket_reebVectorField`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonian vector fields and their Lie algebra).
* A. Lichnerowicz, *Les variétés de Jacobi et leurs algèbres de Lie associées*, J. Math. Pures
  Appl. 57 (1978), 453–488 (Jacobi structures, with contact manifolds as the basic example).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g k : M → ℝ} {X Y : (x : M) → TangentSpace I x}

/-! ### Lie brackets of contact Hamiltonian vector fields -/

namespace IsContactHamiltonianVectorField

/-- For differentiable contact Hamiltonian vector fields `X` of `f` and `Y` of `g`, the value of
`α` on their Lie bracket is `α([X, Y]) = X(g) - g R_α(f)`. -/
theorem apply_mlieBracket (hX : α.IsContactHamiltonianVectorField f X)
    (hY : α.IsContactHamiltonianVectorField g Y) {x : M}
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hYd : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x) :
    α.1 x ![mlieBracket I X Y x] =
      mvfderiv I g x (X x) - g x * mvfderiv I f x (α.reebVectorField x) := by
  -- The invariant formula `dα(X, Y) = X(α Y) - Y(α X) - α([X, Y])`, with `α Y = g`, `α X = f`.
  have h := SmoothForm.mextDeriv_apply_one (φ := α) hXd hYd
  have hfX : (fun y ↦ α.1 y ![X y]) = f := funext hX.apply_eq
  have hgY : (fun y ↦ α.1 y ![Y y]) = g := funext hY.apply_eq
  rw [hfX, hgY] at h
  have hXY := hX.mextDeriv_apply_eq x (Y x)
  rw [hY.apply_eq] at hXY
  linarith

variable [FiniteDimensional ℝ E]

/-- For a contact form `α` and contact Hamiltonian vector fields `X` of `f` and `Y` of `g`, with
`f` and `g` of class `C²` at `x` and `X`, `Y` differentiable at `x`, the contraction of `dα` with
the Lie bracket `[X, Y]` at `x` is `(X(R_α g) - Y(R_α f)) α - d(X(g) - g R_α(f))`. -/
theorem mextDeriv_mlieBracket_apply (hα : α.IsContactForm)
    (hX : α.IsContactHamiltonianVectorField f X) (hY : α.IsContactHamiltonianVectorField g Y)
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hg : ContMDiffAt I 𝓘(ℝ) 2 g x)
    (hXd : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hYd : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (v : TangentSpace I x) :
    mextDeriv α.1 x ![mlieBracket I X Y x, v] =
      (mvfderiv I (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x (X x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (α.reebVectorField y)) x (Y x)) * α.1 x ![v] -
      mvfderiv I (fun y ↦ mvfderiv I g y (X y) - g y * mvfderiv I f y (α.reebVectorField y))
        x v := by
  -- Write `a = R_α f` and `b = R_α g`, and extend `v` to a vector field `W`. The invariant formula
  -- for `d(dα)(X, Y, W) = 0` has six terms. Rewrite the three contractions of `dα` with `X` and
  -- `Y` by the defining equations, the derivatives of `α(W)` along `X` and `Y` by
  -- `L_X α = a α` and `L_Y α = b α`, and the derivatives of `g` and `f` along `[X, W]` and
  -- `[Y, W]` as commutators. What remains is a linear identity among the resulting terms.
  set a : M → ℝ := fun y ↦ mvfderiv I f y (α.reebVectorField y)
  set b : M → ℝ := fun y ↦ mvfderiv I g y (α.reebVectorField y)
  set W : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E v
  have hWx : W x = v := FiberBundle.extend_apply_self E v
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- Differentiability of the functions appearing below.
  have hR : MDifferentiableAt I I.tangent
      (fun y ↦ (α.reebVectorField y : TangentBundle I M)) x :=
    hα.contMDiff_reebVectorField.mdifferentiableAt (by simp)
  have hf1 : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  have hg1 : MDifferentiableAt I 𝓘(ℝ) g x := hg.mdifferentiableAt (by simp)
  have ha : MDifferentiableAt I 𝓘(ℝ) a x := mdifferentiableAt_mvfderiv_apply hf h2 hR
  have hb : MDifferentiableAt I 𝓘(ℝ) b x := mdifferentiableAt_mvfderiv_apply hg h2 hR
  have hαW : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ α.1 y ![W y]) x := by
    convert α.mdifferentiableAt_apply_vectorField (V := ![W]) (x := x)
      (fun i ↦ by fin_cases i; exact hW) using 3 with y
    funext i
    fin_cases i
    rfl
  have hdgW : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I g y (W y)) x :=
    mdifferentiableAt_mvfderiv_apply hg h2 hW
  have hdfW : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I f y (W y)) x :=
    mdifferentiableAt_mvfderiv_apply hf h2 hW
  have hdgX : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I g y (X y)) x :=
    mdifferentiableAt_mvfderiv_apply hg h2 hXd
  have hga : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ g y * a y) x := hg1.mul ha
  have hfb : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y * b y) x := hf1.mul hb
  have haW : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ a y * α.1 y ![W y]) x := ha.mul hαW
  have hbW : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ b y * α.1 y ![W y]) x := hb.mul hαW
  have hgaX : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ g y * a y - mvfderiv I g y (X y)) x :=
    hga.sub hdgX
  -- The contractions of `dα` with `X` and `Y` as functions, from the defining equations.
  have hYW : (fun y ↦ mextDeriv α.1 y ![Y y, W y]) =
      fun y ↦ b y * α.1 y ![W y] - mvfderiv I g y (W y) :=
    funext fun y ↦ hY.mextDeriv_apply_eq y (W y)
  have hXW : (fun y ↦ mextDeriv α.1 y ![X y, W y]) =
      fun y ↦ a y * α.1 y ![W y] - mvfderiv I f y (W y) :=
    funext fun y ↦ hX.mextDeriv_apply_eq y (W y)
  have hXY : (fun y ↦ mextDeriv α.1 y ![X y, Y y]) =
      fun y ↦ mvfderiv I g y (X y) - f y * b y := funext fun y ↦ by
    have h := hY.mextDeriv_apply_eq y (X y)
    rw [hX.apply_eq, mextDeriv_swap] at h
    linarith
  have hfY : (fun y ↦ mvfderiv I f y (Y y)) =
      fun y ↦ g y * a y - mvfderiv I g y (X y) + f y * b y := funext fun y ↦ by
    have h := hX.mextDeriv_apply_eq y (Y y)
    rw [hY.apply_eq, congrFun hXY y] at h
    linarith
  -- The terms of `d(dα)(X, Y, W) = 0` that contain brackets with `W`.
  have h5 : mextDeriv α.1 x ![mlieBracket I X W x, Y x] =
      -(b x * α.1 x ![mlieBracket I X W x] - mvfderiv I g x (mlieBracket I X W x)) := by
    rw [mextDeriv_swap, hY.mextDeriv_apply_eq]
  have h6 : mextDeriv α.1 x ![mlieBracket I Y W x, X x] =
      -(a x * α.1 x ![mlieBracket I Y W x] - mvfderiv I f x (mlieBracket I Y W x)) := by
    rw [mextDeriv_swap, hX.mextDeriv_apply_eq]
  -- `L_X α = (R_α f) α` and `L_Y α = (R_α g) α`, evaluated on `W`.
  have hLX : mvfderiv I (fun y ↦ α.1 y ![W y]) x (X x) - α.1 x ![mlieBracket I X W x] =
      a x * α.1 x ![W x] := by
    rw [← mlieDerivForm_apply_one (α.mdifferentiableAt x) hW, hX.mlieDerivForm_apply_eq hXd,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hLY : mvfderiv I (fun y ↦ α.1 y ![W y]) x (Y x) - α.1 x ![mlieBracket I Y W x] =
      b x * α.1 x ![W x] := by
    rw [← mlieDerivForm_apply_one (α.mdifferentiableAt x) hW, hY.mlieDerivForm_apply_eq hYd,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  -- The derivatives of `g` and `f` along brackets.
  have hdg := mvfderiv_mlieBracket hg h2 hXd hW
  have hdf := mvfderiv_mlieBracket hf h2 hYd hW
  rw [hfY, mvfderiv_fun_add hgaX hfb, mvfderiv_fun_sub hga hdgX, mvfderiv_fun_mul hg1 ha,
    mvfderiv_fun_mul hf1 hb] at hdf
  -- The invariant formula for `d(dα)(X, Y, W) = 0`.
  have h := SmoothForm.mextDeriv_apply_two (φ := mextDerivₗ I 1 α) hXd hYd hW
  simp only [mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv] at h
  rw [hYW, hXW, hXY, h5, h6, mvfderiv_fun_sub hbW hdgW, mvfderiv_fun_sub haW hdfW,
    mvfderiv_fun_sub hdgX hfb,
    mvfderiv_fun_mul hb hαW, mvfderiv_fun_mul ha hαW, mvfderiv_fun_mul hf1 hb] at h
  rw [← hWx, mvfderiv_fun_sub hdgX hga, mvfderiv_fun_mul hg1 ha]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, add_apply,
    sub_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul] at h hdf hdg ⊢
  linear_combination h + b x * hLX - a x * hLY + hdg - hdf

/-- **The Lie bracket of contact Hamiltonian vector fields.** For a contact form `α` on a
finite-dimensional manifold and contact Hamiltonian vector fields `X` of `f` and `Y` of `g`, with
`f` and `g` of class `C²`, the bracket `[X, Y]` is a contact Hamiltonian vector field of
`X(g) - g R_α(f)`. -/
theorem mlieBracket (hα : α.IsContactForm) (hX : α.IsContactHamiltonianVectorField f X)
    (hY : α.IsContactHamiltonianVectorField g Y) (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    α.IsContactHamiltonianVectorField
      (fun y ↦ mvfderiv I g y (X y) - g y * mvfderiv I f y (α.reebVectorField y))
      (mlieBracket I X Y) := by
  -- By uniqueness `X = X_f` and `Y = X_g`, which are differentiable.
  have hXd : MDifferentiable I I.tangent (fun y ↦ (X y : TangentBundle I M)) := by
    rw [hα.isContactHamiltonianVectorField_iff_eq.1 hX]
    exact hα.mdifferentiable_contactHamiltonianVectorField hf
  have hYd : MDifferentiable I I.tangent (fun y ↦ (Y y : TangentBundle I M)) := by
    rw [hα.isContactHamiltonianVectorField_iff_eq.1 hY]
    exact hα.mdifferentiable_contactHamiltonianVectorField hg
  refine isContactHamiltonianVectorField_iff.2 fun x ↦
    ⟨hX.apply_mlieBracket hY (hXd x) (hYd x), fun v ↦ ?_⟩
  have h := hX.mextDeriv_mlieBracket_apply hα hY (hf x) (hg x) (hXd x) (hYd x)
  -- Evaluating at the Reeb vector field identifies the coefficient of `α`.
  have hR := h (α.reebVectorField x)
  rw [hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField] at hR
  rw [h v]
  linear_combination -α.1 x ![v] * hR

end IsContactHamiltonianVectorField

/-! ### The Jacobi bracket -/

/-- The **Jacobi bracket** `{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)` of two functions, for
the contact Hamiltonian vector fields `X_f`, `X_g` and the Reeb vector field `R_α` of `α`. For a
contact form on a finite-dimensional manifold it is `{f, g}_α = X_f(g) - g R_α(f)`
(`TauCeti.SmoothForm.IsContactForm.contactBracket_eq_mvfderiv`). -/
def contactBracket (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) : ℝ :=
  mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, α.contactHamiltonianVectorField g x] +
    f x * mvfderiv I g x (α.reebVectorField x) - g x * mvfderiv I f x (α.reebVectorField x)

/-- The Jacobi bracket unfolds as `dα(X_f, X_g) + f R_α(g) - g R_α(f)`. -/
theorem contactBracket_def (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) :
    α.contactBracket f g x =
      mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, α.contactHamiltonianVectorField g x] +
        f x * mvfderiv I g x (α.reebVectorField x) -
          g x * mvfderiv I f x (α.reebVectorField x) :=
  (rfl)

/-- The Jacobi bracket is antisymmetric. -/
theorem neg_contactBracket (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) :
    -α.contactBracket g f x = α.contactBracket f g x := by
  rw [contactBracket_def, contactBracket_def, mextDeriv_swap α.1 x]
  ring

/-- The Jacobi bracket of a function with itself vanishes. -/
@[simp]
theorem contactBracket_self (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    α.contactBracket f f x = 0 := by
  have h := neg_contactBracket α f f x
  linarith

/-- The Jacobi bracket is additive in its first argument on differentiable functions. -/
theorem contactBracket_add_left {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.contactBracket (f + g) k x = α.contactBracket f k x + α.contactBracket g k x := by
  simp only [contactBracket_def, mextDeriv_eq_bilinFormAt, contactHamiltonianVectorField_add hf hg,
    mvfderiv_add hf hg, map_add, LinearMap.add_apply, Pi.add_apply, add_apply]
  ring

/-- The Jacobi bracket is additive in its second argument on differentiable functions. -/
theorem contactBracket_add_right {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.contactBracket k (f + g) x = α.contactBracket k f x + α.contactBracket k g x := by
  simp only [contactBracket_def, mextDeriv_eq_bilinFormAt, contactHamiltonianVectorField_add hf hg,
    mvfderiv_add hf hg, map_add, Pi.add_apply, add_apply]
  ring

/-- Negating the first argument negates the Jacobi bracket. -/
@[simp]
theorem contactBracket_neg_left (x : M) :
    α.contactBracket (-f) g x = -α.contactBracket f g x := by
  simp only [contactBracket_def, mextDeriv_eq_bilinFormAt, contactHamiltonianVectorField_neg,
    mvfderiv_neg, map_neg, LinearMap.neg_apply, Pi.neg_apply, neg_apply]
  ring

/-- Negating the second argument negates the Jacobi bracket. -/
@[simp]
theorem contactBracket_neg_right (x : M) :
    α.contactBracket f (-g) x = -α.contactBracket f g x := by
  simp only [contactBracket_def, mextDeriv_eq_bilinFormAt, contactHamiltonianVectorField_neg,
    mvfderiv_neg, map_neg, Pi.neg_apply, neg_apply]
  ring

/-- Multiplication of the first argument by a real constant scales the Jacobi bracket. -/
theorem contactBracket_const_smul_left (c : ℝ) (x : M) :
    α.contactBracket (c • f) g x = c • α.contactBracket f g x := by
  simp only [contactBracket_def, mextDeriv_eq_bilinFormAt,
    contactHamiltonianVectorField_const_smul, mvfderiv_const_smul_field, map_smul,
    LinearMap.smul_apply, Pi.smul_apply, smul_apply, smul_eq_mul]
  ring

/-- Multiplication of the second argument by a real constant scales the Jacobi bracket. -/
theorem contactBracket_const_smul_right (c : ℝ) (x : M) :
    α.contactBracket f (c • g) x = c • α.contactBracket f g x := by
  simp only [contactBracket_def, mextDeriv_eq_bilinFormAt,
    contactHamiltonianVectorField_const_smul, mvfderiv_const_smul_field, map_smul,
    Pi.smul_apply, smul_apply, smul_eq_mul]
  ring

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- The Jacobi bracket `{f, g}_α` is the derivative of `g` along the contact Hamiltonian vector
field of `f`, corrected by `-g R_α(f)`. -/
theorem contactBracket_eq_mvfderiv (f g : M → ℝ) (x : M) :
    α.contactBracket f g x = mvfderiv I g x (α.contactHamiltonianVectorField f x) -
      g x * mvfderiv I f x (α.reebVectorField x) := by
  have h := hα.mextDeriv_contactHamiltonianVectorField_left g x
    (α.contactHamiltonianVectorField f x)
  rw [hα.apply_contactHamiltonianVectorField, mextDeriv_swap] at h
  rw [contactBracket_def]
  linarith

/-- The Jacobi bracket `{f, g}_α` is `f R_α(g)` minus the derivative of `f` along the contact
Hamiltonian vector field of `g`. -/
theorem contactBracket_eq_sub_mvfderiv (f g : M → ℝ) (x : M) :
    α.contactBracket f g x = f x * mvfderiv I g x (α.reebVectorField x) -
      mvfderiv I f x (α.contactHamiltonianVectorField g x) := by
  rw [← neg_contactBracket, hα.contactBracket_eq_mvfderiv]
  ring

/-- The Jacobi bracket with a constant `c` on the right is `-c R_α(f)`. In particular
`{f, 1}_α = -R_α(f)`. -/
@[simp]
theorem contactBracket_const_right (f : M → ℝ) (c : ℝ) (x : M) :
    α.contactBracket f (fun _ ↦ c) x = -(c * mvfderiv I f x (α.reebVectorField x)) := by
  rw [hα.contactBracket_eq_mvfderiv, mvfderiv_const, zero_apply, zero_sub]

/-- The Jacobi bracket with a constant `c` on the left is `c R_α(g)`. In particular
`{1, g}_α = R_α(g)`: the bracket with `1` is the derivative along the Reeb vector field. -/
@[simp]
theorem contactBracket_const_left (c : ℝ) (g : M → ℝ) (x : M) :
    α.contactBracket (fun _ ↦ c) g x = c * mvfderiv I g x (α.reebVectorField x) := by
  rw [hα.contactBracket_eq_sub_mvfderiv, mvfderiv_const, zero_apply, sub_zero]

/-- The Jacobi bracket with `1` on the right is `{f, 1}_α = -R_α(f)`. -/
@[simp]
theorem contactBracket_one_right (f : M → ℝ) (x : M) :
    α.contactBracket f 1 x = -mvfderiv I f x (α.reebVectorField x) := by
  rw [Pi.one_def, hα.contactBracket_const_right, one_mul]

/-- The Jacobi bracket with `1` on the left is the Reeb derivative, `{1, g}_α = R_α(g)`. -/
@[simp]
theorem contactBracket_one_left (g : M → ℝ) (x : M) :
    α.contactBracket 1 g x = mvfderiv I g x (α.reebVectorField x) := by
  rw [Pi.one_def, hα.contactBracket_const_left, one_mul]

/-- **The Leibniz rule of the Jacobi bracket.** For `g` and `k` differentiable at `x`,
`{f, g k}_α = g {f, k}_α + k {f, g}_α + g k R_α(f)`. Since `{f, 1}_α = -R_α(f)`, the bracket is a
first-order differential operator in `g` which is a derivation only where `R_α(f) = 0`. -/
theorem contactBracket_mul_right {x : M} (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hk : MDifferentiableAt I 𝓘(ℝ) k x) :
    α.contactBracket f (g * k) x = g x * α.contactBracket f k x + k x * α.contactBracket f g x +
      g x * k x * mvfderiv I f x (α.reebVectorField x) := by
  simp only [hα.contactBracket_eq_mvfderiv, mvfderiv_mul hg hk, Pi.mul_apply, add_apply,
    smul_apply, smul_eq_mul]
  ring

/-- **The Leibniz rule of the Jacobi bracket in its first argument.** For `g` and `k`
differentiable at `x`, `{g k, f}_α = g {k, f}_α + k {g, f}_α - g k R_α(f)`. -/
theorem contactBracket_mul_left {x : M} (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hk : MDifferentiableAt I 𝓘(ℝ) k x) :
    α.contactBracket (g * k) f x = g x * α.contactBracket k f x + k x * α.contactBracket g f x -
      g x * k x * mvfderiv I f x (α.reebVectorField x) := by
  rw [← neg_contactBracket, hα.contactBracket_mul_right hg hk, ← neg_contactBracket α k,
    ← neg_contactBracket α g]
  ring

/-- **The Jacobi bracket comes from the Lie bracket of contact vector fields.** For `C²` functions
`f` and `g`, `α([X_f, X_g]) = {f, g}_α`. -/
theorem apply_mlieBracket_contactHamiltonianVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    α.1 x ![mlieBracket I (α.contactHamiltonianVectorField f)
      (α.contactHamiltonianVectorField g) x] = α.contactBracket f g x := by
  rw [(hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).apply_mlieBracket
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g)
    (hα.mdifferentiable_contactHamiltonianVectorField hf x)
    (hα.mdifferentiable_contactHamiltonianVectorField hg x), hα.contactBracket_eq_mvfderiv]

/-- **Contact Hamiltonian vector fields of Jacobi brackets.** For `C²` functions `f` and `g`,
`X_{{f, g}_α} = [X_f, X_g]`: the map `f ↦ X_f` takes Jacobi brackets to Lie brackets of vector
fields. -/
theorem contactHamiltonianVectorField_contactBracket (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    α.contactHamiltonianVectorField (α.contactBracket f g) =
      mlieBracket I (α.contactHamiltonianVectorField f) (α.contactHamiltonianVectorField g) := by
  have h := (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f).mlieBracket hα
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g) hf hg
  rw [funext (hα.contactBracket_eq_mvfderiv f g)]
  exact (hα.isContactHamiltonianVectorField_iff_eq.1 h).symm

/-- The Reeb derivative of a Jacobi bracket: for `C²` functions `f` and `g`,
`R_α({f, g}_α) = X_f(R_α g) - X_g(R_α f)`. -/
theorem mvfderiv_contactBracket_reebVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    mvfderiv I (α.contactBracket f g) x (α.reebVectorField x) =
      mvfderiv I (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x
          (α.contactHamiltonianVectorField f x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (α.reebVectorField y)) x
          (α.contactHamiltonianVectorField g x) := by
  have h := IsContactHamiltonianVectorField.mextDeriv_mlieBracket_apply hα
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f)
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g) (hf x) (hg x)
    (hα.mdifferentiable_contactHamiltonianVectorField hf x)
    (hα.mdifferentiable_contactHamiltonianVectorField hg x) (α.reebVectorField x)
  rw [hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField, mul_one,
    ← funext (hα.contactBracket_eq_mvfderiv f g)] at h
  linarith

/-- The derivative of a Jacobi bracket: for `f` of class `C²` at `x` and a `C²` function `g`,
`d{f, g}_α = f d(R_α g) + (R_α g) df - d(X_g f)` at `x`. -/
theorem mvfderiv_contactBracket {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    mvfderiv I (α.contactBracket f g) x =
      f x • mvfderiv I (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x +
        mvfderiv I g x (α.reebVectorField x) • mvfderiv I f x -
          mvfderiv I (fun y ↦ mvfderiv I f y (α.contactHamiltonianVectorField g y)) x := by
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hf1 : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by simp)
  have hRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x :=
    mdifferentiableAt_mvfderiv_apply (hg x) h2
      (hα.contMDiff_reebVectorField.mdifferentiableAt (by simp))
  have hfRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y * mvfderiv I g y (α.reebVectorField y)) x :=
    hf1.mul hRg
  have hdfXg : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ mvfderiv I f y (α.contactHamiltonianVectorField g y)) x :=
    mdifferentiableAt_mvfderiv_apply hf h2 (hα.mdifferentiable_contactHamiltonianVectorField hg x)
  rw [funext (hα.contactBracket_eq_sub_mvfderiv f g), mvfderiv_fun_sub hfRg hdfXg,
    mvfderiv_fun_mul hf1 hRg]

/-- For `C²` functions, the Jacobi bracket satisfies
`{f, {g, k}_α}_α = {{f, g}_α, k}_α + {g, {f, k}_α}_α`. -/
theorem contactBracket_contactBracket (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hk : ContMDiff I 𝓘(ℝ) 2 k) (x : M) :
    α.contactBracket f (α.contactBracket g k) x =
      α.contactBracket (α.contactBracket f g) k x +
        α.contactBracket g (α.contactBracket f k) x := by
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hXg := hα.mdifferentiable_contactHamiltonianVectorField hg x
  have hXk := hα.mdifferentiable_contactHamiltonianVectorField hk x
  -- `{f, {g, k}} = f R_α{g, k} - X_{{g, k}} f`, with `X_{{g, k}} = [X_g, X_k]`.
  have e1 := hα.contactBracket_eq_sub_mvfderiv f (α.contactBracket g k) x
  rw [hα.contactHamiltonianVectorField_contactBracket hg hk,
    hα.mvfderiv_contactBracket_reebVectorField hg hk,
    mvfderiv_mlieBracket (hf x) h2 hXg hXk] at e1
  -- `{g, {f, k}} = X_g {f, k} - {f, k} R_α g`, where `{f, k} = f R_α k - X_k f`.
  have e2 := hα.contactBracket_eq_mvfderiv g (α.contactBracket f k) x
  rw [hα.mvfderiv_contactBracket (hf x) hk] at e2
  -- `{{f, g}, k} = -(X_k {f, g} - {f, g} R_α k)`, where `{f, g} = f R_α g - X_g f`.
  have e3 := hα.contactBracket_eq_mvfderiv k (α.contactBracket f g) x
  rw [hα.mvfderiv_contactBracket (hf x) hg] at e3
  have efg := hα.contactBracket_eq_sub_mvfderiv f g x
  have efk := hα.contactBracket_eq_sub_mvfderiv f k x
  rw [← neg_contactBracket α (α.contactBracket f g) k]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul] at e2 e3
  linear_combination e1 - e2 + e3 + mvfderiv I g x (α.reebVectorField x) * efk -
    mvfderiv I k x (α.reebVectorField x) * efg

/-- **The Jacobi identity for the Jacobi bracket of a contact form.** For `C²` functions `f`, `g`
and `k`, `{f, {g, k}_α}_α + {g, {k, f}_α}_α + {k, {f, g}_α}_α = 0`. -/
theorem contactBracket_jacobi (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hk : ContMDiff I 𝓘(ℝ) 2 k) (x : M) :
    α.contactBracket f (α.contactBracket g k) x + α.contactBracket g (α.contactBracket k f) x +
      α.contactBracket k (α.contactBracket f g) x = 0 := by
  have hkf : α.contactBracket k f = -α.contactBracket f k :=
    funext fun y ↦ by rw [Pi.neg_apply, neg_contactBracket]
  rw [hα.contactBracket_contactBracket hf hg hk, hkf, contactBracket_neg_right,
    ← neg_contactBracket α k (α.contactBracket f g)]
  ring

end IsContactForm

end SmoothForm

end TauCeti
