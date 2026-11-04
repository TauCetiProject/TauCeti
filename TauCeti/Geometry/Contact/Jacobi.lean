/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Hamiltonian
import TauCeti.Geometry.Contact.Levi
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Jacobi bracket of a contact form

Let `α` be a one-form on a manifold `M`, with Reeb vector field `R_α` and contact Hamiltonian
vector fields `X_f` (`TauCeti.SmoothForm.contactHamiltonianVectorField`), normalized by
`α(X_f) = f` and `ι_(X_f) dα = (R_α f) α - df`. The **Jacobi bracket** of two functions is

`{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)`

(`TauCeti.SmoothForm.jacobiBracket`). It is antisymmetric
(`TauCeti.SmoothForm.neg_jacobiBracket`). For a contact form on a finite-dimensional manifold,
the contact Hamiltonian equations turn it into

`{f, g}_α = f R_α(g) - df(X_g) = dg(X_f) - g R_α(f)`

(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_mul_sub_mvfderiv`,
`TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_mvfderiv_sub_mul`). In particular
`{1, g}_α = R_α(g)` and `{f, 1}_α = -R_α(f)`, and unlike a Poisson bracket the Jacobi bracket is
not a derivation in each argument: it satisfies the first-order Leibniz rule

`{f, g h}_α = g {f, h}_α + h {f, g}_α - g h {f, 1}_α`

(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_mul_right`).

The bracket comes from the Lie bracket of contact vector fields. For `C²` functions `f` and `g`,
`α([X_f, X_g]) = {f, g}_α`
(`TauCeti.SmoothForm.IsContactForm.apply_mlieBracket_contactHamiltonianVectorField`), and the
Lie bracket `[X_f, X_g]` is itself a contact Hamiltonian vector field, so that

`X_{{f, g}_α} = [X_f, X_g]`

(`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`): the map
`f ↦ X_f` takes Jacobi brackets to Lie brackets of vector fields. The proof evaluates
`d(dα) = 0` on `X_f`, `X_g` and a vector field tangent to `ξ = ker α`. Taking `f = 1` gives
`[R_α, X_g] = X_{R_α g}`
(`TauCeti.SmoothForm.IsContactForm.mlieBracket_reebVectorField_contactHamiltonianVectorField`).
The Reeb derivative of the bracket, which is the multiplier of the contact vector field
`[X_f, X_g]` in `L_{[X_f, X_g]} α = R_α({f, g}_α) α`, is `R_α({f, g}_α) = X_f(R_α g) - X_g(R_α f)`
(`TauCeti.SmoothForm.IsContactForm.mvfderiv_jacobiBracket_reebVectorField`).

These identities give the **Jacobi identity**
`{f, {g, h}_α}_α + {g, {h, f}_α}_α + {h, {f, g}_α}_α = 0` for `C²` functions
(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_jacobi`). Thus on smooth functions `{·, ·}_α` is
a Jacobi bracket: a Lie bracket which is a first-order differential operator in each argument.

## Main declarations

* `TauCeti.SmoothForm.jacobiBracket`: the Jacobi bracket `{f, g}_α`.
* `TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_mul_sub_mvfderiv`,
  `TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_mvfderiv_sub_mul`: the bracket in terms of
  derivatives along contact Hamiltonian vector fields.
* `TauCeti.SmoothForm.IsContactForm.jacobiBracket_mul_right`: the first-order Leibniz rule.
* `TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`:
  `X_{{f, g}_α} = [X_f, X_g]`.
* `TauCeti.SmoothForm.IsContactForm.jacobiBracket_jacobi`: the Jacobi identity.

## References

* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced
  Mathematics 109 (2008), Section 2.3 (contact Hamiltonian vector fields).
* André Lichnerowicz, *Les variétés de Jacobi et leurs algèbres de Lie associées*, J. Math. Pures
  Appl. 57 (1978), 453–488 (Jacobi brackets and the bracket of a contact form).
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g h : M → ℝ}

/-! ### The bracket -/

/-- The **Jacobi bracket** `{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)` of two functions, for
a one-form `α` with Reeb vector field `R_α` and contact Hamiltonian vector fields `X_f`, `X_g`.
For a contact form it is `{f, g}_α = dg(X_f) - g R_α(f)`
(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_mvfderiv_sub_mul`). -/
def jacobiBracket (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) : ℝ :=
  mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, α.contactHamiltonianVectorField g x] +
    f x * mvfderiv I g x (α.reebVectorField x) - g x * mvfderiv I f x (α.reebVectorField x)

/-- The Jacobi bracket unfolds as `dα(X_f, X_g) + f R_α(g) - g R_α(f)`. -/
theorem jacobiBracket_def (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) :
    α.jacobiBracket f g x =
      mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, α.contactHamiltonianVectorField g x] +
        f x * mvfderiv I g x (α.reebVectorField x) -
          g x * mvfderiv I f x (α.reebVectorField x) :=
  (rfl)

/-- The value of `dα` on two tangent vectors, as its bilinear form. -/
private theorem mextDeriv_eq_bilinFormAt (α : SmoothForm I M ℝ 1) (x : M)
    (v w : TangentSpace I x) :
    mextDeriv α.1 x ![v, w] = (mextDerivₗ I 1 α).bilinFormAt x v w := by
  rw [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]

/-- `dα` is alternating. -/
private theorem mextDeriv_swap (α : SmoothForm I M ℝ 1) (x : M) (v w : TangentSpace I x) :
    mextDeriv α.1 x ![v, w] = -mextDeriv α.1 x ![w, v] := by
  have h := SmoothBundleForm.eval₂_swap (mextDerivₗ I 1 α) x v w
  rwa [SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply] at h

/-- The Jacobi bracket is antisymmetric. -/
theorem neg_jacobiBracket (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) :
    -α.jacobiBracket g f x = α.jacobiBracket f g x := by
  rw [jacobiBracket_def, jacobiBracket_def,
    mextDeriv_swap α x (α.contactHamiltonianVectorField g x)]
  ring

/-- The Jacobi bracket of a function with itself vanishes. -/
@[simp]
theorem jacobiBracket_self (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    α.jacobiBracket f f x = 0 := by
  have h := neg_jacobiBracket α f f x
  linarith

/-- The Jacobi bracket is additive in its first argument on differentiable functions. -/
theorem jacobiBracket_add_left {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.jacobiBracket (f + g) h x = α.jacobiBracket f h x + α.jacobiBracket g h x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_add hf hg, mextDeriv_eq_bilinFormAt,
    map_add, LinearMap.add_apply, mvfderiv_add hf hg, add_apply, Pi.add_apply]
  ring

/-- The Jacobi bracket is additive in its second argument on differentiable functions. -/
theorem jacobiBracket_add_right {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.jacobiBracket h (f + g) x = α.jacobiBracket h f x + α.jacobiBracket h g x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_add hf hg, mextDeriv_eq_bilinFormAt,
    map_add, mvfderiv_add hf hg, add_apply, Pi.add_apply]
  ring

/-- Negating the first argument negates the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_neg_left (x : M) : α.jacobiBracket (-f) g x = -α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_neg, mextDeriv_eq_bilinFormAt,
    map_neg, LinearMap.neg_apply, mvfderiv_neg, neg_apply, Pi.neg_apply]
  ring

/-- Negating the second argument negates the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_neg_right (x : M) : α.jacobiBracket f (-g) x = -α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_neg, mextDeriv_eq_bilinFormAt,
    map_neg, mvfderiv_neg, neg_apply, Pi.neg_apply]
  ring

/-- Multiplication of the first argument by a real constant scales the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_const_smul_left (c : ℝ) (x : M) :
    α.jacobiBracket (c • f) g x = c * α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_const_smul, mextDeriv_eq_bilinFormAt,
    map_smul, LinearMap.smul_apply, mvfderiv_const_smul_field, smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Multiplication of the second argument by a real constant scales the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_const_smul_right (c : ℝ) (x : M) :
    α.jacobiBracket f (c • g) x = c * α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_const_smul, mextDeriv_eq_bilinFormAt,
    map_smul, mvfderiv_const_smul_field, smul_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-! ### Contact forms -/

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- For a contact form, `{f, g}_α = f R_α(g) - df(X_g)`. -/
theorem jacobiBracket_eq_mul_sub_mvfderiv (f g : M → ℝ) (x : M) :
    α.jacobiBracket f g x = f x * mvfderiv I g x (α.reebVectorField x) -
      mvfderiv I f x (α.contactHamiltonianVectorField g x) := by
  rw [jacobiBracket_def, hα.mextDeriv_contactHamiltonianVectorField_left,
    hα.apply_contactHamiltonianVectorField]
  ring

/-- For a contact form, `{f, g}_α = dg(X_f) - g R_α(f)`: the derivative of `g` along `X_f`,
corrected by the multiplier `R_α f` of `L_(X_f) α = (R_α f) α`. -/
theorem jacobiBracket_eq_mvfderiv_sub_mul (f g : M → ℝ) (x : M) :
    α.jacobiBracket f g x = mvfderiv I g x (α.contactHamiltonianVectorField f x) -
      g x * mvfderiv I f x (α.reebVectorField x) := by
  rw [← neg_jacobiBracket, hα.jacobiBracket_eq_mul_sub_mvfderiv]
  ring

/-- The Jacobi bracket of a constant `c` with `g` is `c R_α(g)`. -/
@[simp]
theorem jacobiBracket_const_left (c : ℝ) (g : M → ℝ) (x : M) :
    α.jacobiBracket (fun _ ↦ c) g x = c * mvfderiv I g x (α.reebVectorField x) := by
  rw [hα.jacobiBracket_eq_mul_sub_mvfderiv, mvfderiv_const, zero_apply,
    sub_zero]

/-- The Jacobi bracket of `f` with a constant `c` is `-c R_α(f)`. -/
@[simp]
theorem jacobiBracket_const_right (f : M → ℝ) (c : ℝ) (x : M) :
    α.jacobiBracket f (fun _ ↦ c) x = -(c * mvfderiv I f x (α.reebVectorField x)) := by
  rw [hα.jacobiBracket_eq_mvfderiv_sub_mul, mvfderiv_const, zero_apply,
    zero_sub]

/-- **The Jacobi bracket with `1` is the Reeb derivative**: `{1, g}_α = R_α(g)`. -/
@[simp]
theorem jacobiBracket_one_left (g : M → ℝ) (x : M) :
    α.jacobiBracket 1 g x = mvfderiv I g x (α.reebVectorField x) := by
  rw [Pi.one_def, hα.jacobiBracket_const_left, one_mul]

/-- The Jacobi bracket with `1` on the right is `{f, 1}_α = -R_α(f)`. -/
@[simp]
theorem jacobiBracket_one_right (f : M → ℝ) (x : M) :
    α.jacobiBracket f 1 x = -mvfderiv I f x (α.reebVectorField x) := by
  rw [Pi.one_def, hα.jacobiBracket_const_right, one_mul]

/-- **The first-order Leibniz rule** for the Jacobi bracket, for `g` and `h` differentiable at
`x`: `{f, g h}_α = g {f, h}_α + h {f, g}_α + g h R_α(f)`. Since `{f, 1}_α = -R_α(f)`, the last
term is `-g h {f, 1}_α`. -/
theorem jacobiBracket_mul_right {x : M} (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hh : MDifferentiableAt I 𝓘(ℝ) h x) :
    α.jacobiBracket f (g * h) x = g x * α.jacobiBracket f h x + h x * α.jacobiBracket f g x +
      g x * h x * mvfderiv I f x (α.reebVectorField x) := by
  simp only [hα.jacobiBracket_eq_mvfderiv_sub_mul, mvfderiv_mul hg hh,
    add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
  ring

/-- **The first-order Leibniz rule** in the first argument, for `g` and `h` differentiable at
`x`: `{g h, f}_α = g {h, f}_α + h {g, f}_α - g h R_α(f)`. -/
theorem jacobiBracket_mul_left {x : M} (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hh : MDifferentiableAt I 𝓘(ℝ) h x) :
    α.jacobiBracket (g * h) f x = g x * α.jacobiBracket h f x + h x * α.jacobiBracket g f x -
      g x * h x * mvfderiv I f x (α.reebVectorField x) := by
  rw [← neg_jacobiBracket, hα.jacobiBracket_mul_right hg hh, ← neg_jacobiBracket α h f,
    ← neg_jacobiBracket α g f]
  ring

/-- **Regularity of the Jacobi bracket.** For a contact form on a finite-dimensional manifold, the
Jacobi bracket of two `C^(n+1)` functions is `C^n`, for `n ≤ ∞`. -/
theorem contMDiff_jacobiBracket {n : WithTop ℕ∞} (hn : n ≤ ∞) (hf : ContMDiff I 𝓘(ℝ) (n + 1) f)
    (hg : ContMDiff I 𝓘(ℝ) (n + 1) g) : ContMDiff I 𝓘(ℝ) n (α.jacobiBracket f g) := by
  have hfg : α.jacobiBracket f g = fun x ↦ mvfderiv I g x (α.contactHamiltonianVectorField f x) -
      g x * mvfderiv I f x (α.reebVectorField x) :=
    funext (hα.jacobiBracket_eq_mvfderiv_sub_mul f g)
  rw [hfg]
  exact ((hg.contMDiff_mvfderiv_apply le_rfl).comp
    (hα.contMDiff_contactHamiltonianVectorField hn hf)).sub ((hg.of_le le_self_add).smul
      ((hf.contMDiff_mvfderiv_apply le_rfl).comp (hα.contMDiff_reebVectorField.of_le hn)))

/-- The Jacobi bracket of two `C²` functions is differentiable. -/
theorem mdifferentiable_jacobiBracket (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    MDifferentiable I 𝓘(ℝ) (α.jacobiBracket f g) :=
  (hα.contMDiff_jacobiBracket (n := 1) (by simp) (by norm_num [hf])
    (by norm_num [hg])).mdifferentiable one_ne_zero

/-! ### Lie brackets of contact Hamiltonian vector fields -/

/-- **The Jacobi bracket is the contact form evaluated on the Lie bracket**: for a contact form
and `C²` functions `f` and `g`, `α([X_f, X_g]) = {f, g}_α`. -/
theorem apply_mlieBracket_contactHamiltonianVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    α.1 x ![mlieBracket I (α.contactHamiltonianVectorField f)
      (α.contactHamiltonianVectorField g) x] = α.jacobiBracket f g x := by
  -- The invariant formula `dα(X_f, X_g) = X_f(α(X_g)) - X_g(α(X_f)) - α([X_f, X_g])`.
  have h := SmoothForm.mextDeriv_apply_one (φ := α)
    (hα.mdifferentiable_contactHamiltonianVectorField hf x)
    (hα.mdifferentiable_contactHamiltonianVectorField hg x)
  have hαf : (fun y ↦ α.1 y ![α.contactHamiltonianVectorField f y]) = f :=
    funext (hα.apply_contactHamiltonianVectorField f)
  have hαg : (fun y ↦ α.1 y ![α.contactHamiltonianVectorField g y]) = g :=
    funext (hα.apply_contactHamiltonianVectorField g)
  rw [hαf, hαg, hα.mextDeriv_contactHamiltonianVectorField_left,
    hα.apply_contactHamiltonianVectorField] at h
  rw [hα.jacobiBracket_eq_mvfderiv_sub_mul]
  linarith

/-- The key step for `X_{{f, g}_α} = [X_f, X_g]`: on the contact distribution, the contraction of
`dα` with `[X_f, X_g]` is `-d{f, g}_α`. It is `d(dα) = 0` evaluated on `X_f`, `X_g` and a vector
field `W` tangent to `ξ` near `x`, for which `[X_f, W]` and `[X_g, W]` lie in `ξ` at `x`. -/
private theorem mextDeriv_mlieBracket_contactHamiltonianVectorField_of_mem
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g) {x : M} {u : TangentSpace I x}
    (hu : u ∈ α.kerDistribution x) :
    mextDeriv α.1 x ![mlieBracket I (α.contactHamiltonianVectorField f)
      (α.contactHamiltonianVectorField g) x, u] = -mvfderiv I (α.jacobiBracket f g) x u := by
  set X := α.contactHamiltonianVectorField f
  set Y := α.contactHamiltonianVectorField g
  have hX := hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f
  have hY := hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g
  have hXd := hα.mdifferentiable_contactHamiltonianVectorField hf
  have hYd := hα.mdifferentiable_contactHamiltonianVectorField hg
  have hRd : MDifferentiable I I.tangent (fun y ↦ (α.reebVectorField y : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.mdifferentiable (by simp)
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  -- Extend `u` to a `C¹` vector field `W` tangent to `ξ` on an open neighbourhood `U` of `x`.
  have : IsManifold I (1 + 1) M := IsManifold.of_le (n := ∞) (by norm_cast)
  obtain ⟨U, hUo, hxU, W, hWs, hWU, hWx⟩ :=
    (hα.isContMDiffDistribution_kerDistribution (n := 1)).exists_contMDiffOn_apply_eq
      (⟨u, hu⟩ : α.kerDistribution x)
  have hWd : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x :=
    (hWs.contMDiffAt (hUo.mem_nhds hxU)).mdifferentiableAt one_ne_zero
  have hWξ : ∀ᶠ y in 𝓝 x, W y ∈ α.kerDistribution y :=
    Filter.eventually_of_mem (hUo.mem_nhds hxU) hWU
  -- `[X_f, W]` and `[X_g, W]` lie in `ξ` at `x`.
  have hXW := mem_kerDistribution.1 (hX.mlieBracket_mem_kerDistribution (hXd x) hWd hWξ)
  have hYW := mem_kerDistribution.1 (hY.mlieBracket_mem_kerDistribution (hYd x) hWd hWξ)
  -- The functions differentiated in the invariant formula for `d(dα)(X_f, X_g, W)`.
  have hYWfun : (fun y ↦ mextDeriv α.1 y ![Y y, W y]) =ᶠ[𝓝 x]
      fun y ↦ -mvfderiv I g y (W y) := by
    filter_upwards [hWξ] with y hy
    rw [hY.mextDeriv_apply_eq, mem_kerDistribution.1 hy, mul_zero, zero_sub]
  have hXWfun : (fun y ↦ mextDeriv α.1 y ![X y, W y]) =ᶠ[𝓝 x]
      fun y ↦ -mvfderiv I f y (W y) := by
    filter_upwards [hWξ] with y hy
    rw [hX.mextDeriv_apply_eq, mem_kerDistribution.1 hy, mul_zero, zero_sub]
  have hXYfun : (fun y ↦ mextDeriv α.1 y ![X y, Y y]) =
      fun y ↦ mvfderiv I g y (X y) - f y * mvfderiv I g y (α.reebVectorField y) := by
    funext y
    rw [mextDeriv_swap, hY.mextDeriv_apply_eq, hX.apply_eq]
    ring
  have hfg : α.jacobiBracket f g =
      fun y ↦ f y * mvfderiv I g y (α.reebVectorField y) - mvfderiv I f y (Y y) :=
    funext (hα.jacobiBracket_eq_mul_sub_mvfderiv f g)
  -- The bracket terms of the invariant formula.
  have hXWY : mextDeriv α.1 x ![mlieBracket I X W x, Y x] =
      mvfderiv I g x (mlieBracket I X W x) := by
    rw [mextDeriv_swap, hY.mextDeriv_apply_eq, hXW, mul_zero, zero_sub, neg_neg]
  have hYWX : mextDeriv α.1 x ![mlieBracket I Y W x, X x] =
      mvfderiv I f x (mlieBracket I Y W x) := by
    rw [mextDeriv_swap, hX.mextDeriv_apply_eq, hYW, mul_zero, zero_sub, neg_neg]
  -- Differentiability of the functions whose derivatives along `W` are compared.
  have hdgX : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I g y (X y)) x :=
    mdifferentiableAt_mvfderiv_apply (hg x) h2 (hXd x)
  have hdfY : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I f y (Y y)) x :=
    mdifferentiableAt_mvfderiv_apply (hf x) h2 (hYd x)
  have hfRg : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ f y * mvfderiv I g y (α.reebVectorField y)) x :=
    ((hf x).mdifferentiableAt two_ne_zero).mul
      (mdifferentiableAt_mvfderiv_apply (hg x) h2 (hRd x))
  have h := SmoothForm.mextDeriv_apply_two (φ := mextDerivₗ I 1 α) (hXd x) (hYd x) hWd
  rw [(isClosed_def _).1 (isClosed_mextDerivₗ α)] at h
  simp only [mextDerivₗ_apply] at h
  rw [hYWfun.mvfderiv_eq, hXWfun.mvfderiv_eq, hXYfun, hXWY, hYWX,
    mvfderiv_mlieBracket (hg x) h2 (hXd x) hWd, mvfderiv_mlieBracket (hf x) h2 (hYd x) hWd,
    mvfderiv_fun_neg, mvfderiv_fun_neg, mvfderiv_fun_sub hdgX hfRg, hWx] at h
  rw [hfg, mvfderiv_fun_sub hfRg hdfY]
  simp only [sub_apply, neg_apply, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero] at h ⊢
  linear_combination h

/-- **The Lie bracket of contact Hamiltonian vector fields** is a contact Hamiltonian vector
field: for a contact form and `C²` functions `f` and `g`, `[X_f, X_g]` is a contact Hamiltonian
vector field of the Jacobi bracket `{f, g}_α`. -/
theorem isContactHamiltonianVectorField_mlieBracket (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    α.IsContactHamiltonianVectorField (α.jacobiBracket f g)
      (mlieBracket I (α.contactHamiltonianVectorField f) (α.contactHamiltonianVectorField g)) := by
  refine isContactHamiltonianVectorField_iff.2 fun x ↦
    ⟨hα.apply_mlieBracket_contactHamiltonianVectorField hf hg x, fun v ↦ ?_⟩
  set B := mlieBracket I (α.contactHamiltonianVectorField f) (α.contactHamiltonianVectorField g)
  set R := α.reebVectorField x
  -- Split `v` along `T_x M = ξ_x ⊕ ℝ R_α(x)`; `dα(B, R_α) = 0` and the `ξ` part is the key step.
  obtain ⟨c, hc⟩ : ∃ c, c = α.1 x ![v] := ⟨_, rfl⟩
  have hu : v - c • R ∈ α.kerDistribution x := by
    rw [mem_kerDistribution, ← degreeOneEquiv_apply_apply_vec, map_sub, map_smul,
      degreeOneEquiv_apply_apply_vec, degreeOneEquiv_apply_apply_vec, hα.apply_reebVectorField,
      ← hc, smul_eq_mul, mul_one, sub_self]
  have hB : mextDeriv α.1 x ![B x, v] =
      mextDeriv α.1 x ![B x, v - c • R] + c * mextDeriv α.1 x ![B x, R] := by
    rw [mextDeriv_eq_bilinFormAt, mextDeriv_eq_bilinFormAt, mextDeriv_eq_bilinFormAt, map_sub,
      map_smul, smul_eq_mul]
    ring
  have hd : mvfderiv I (α.jacobiBracket f g) x v =
      mvfderiv I (α.jacobiBracket f g) x (v - c • R) +
        c * mvfderiv I (α.jacobiBracket f g) x R := by
    rw [map_sub, map_smul, smul_eq_mul]
    ring
  rw [hB, hd, hα.mextDeriv_mlieBracket_contactHamiltonianVectorField_of_mem hf hg hu,
    hα.mextDeriv_reebVectorField_right, ← hc]
  ring

/-- **Contact Hamiltonian vector fields take Jacobi brackets to Lie brackets**: for a contact form
and `C²` functions `f` and `g`, `X_{{f, g}_α} = [X_f, X_g]`. -/
theorem contactHamiltonianVectorField_jacobiBracket (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    α.contactHamiltonianVectorField (α.jacobiBracket f g) =
      mlieBracket I (α.contactHamiltonianVectorField f) (α.contactHamiltonianVectorField g) :=
  (hα.isContactHamiltonianVectorField_iff_eq.1
    (hα.isContactHamiltonianVectorField_mlieBracket hf hg)).symm

/-- **The Reeb vector field acts on contact Hamiltonian vector fields** by differentiating the
Hamiltonian: for a contact form and a `C²` function `g`, `[R_α, X_g] = X_{R_α g}`. -/
theorem mlieBracket_reebVectorField_contactHamiltonianVectorField (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    mlieBracket I α.reebVectorField (α.contactHamiltonianVectorField g) =
      α.contactHamiltonianVectorField fun y ↦ mvfderiv I g y (α.reebVectorField y) := by
  have h := hα.contactHamiltonianVectorField_jacobiBracket contMDiff_one hg
  rw [hα.contactHamiltonianVectorField_one] at h
  rw [← h]
  congr 1
  exact funext (hα.jacobiBracket_one_left g)

/-- **The multiplier of the Lie bracket of contact Hamiltonian vector fields.** For a contact form
and `C²` functions `f` and `g`, the derivative of `{f, g}_α` along the Reeb vector field is
`R_α({f, g}_α) = X_f(R_α g) - X_g(R_α f)`. Since `[X_f, X_g]` is the contact Hamiltonian
vector field of `{f, g}_α`, this is the multiplier in
`L_{[X_f, X_g]} α = (X_f(R_α g) - X_g(R_α f)) α` wherever `[X_f, X_g]` is differentiable. -/
theorem mvfderiv_jacobiBracket_reebVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (x : M) :
    mvfderiv I (α.jacobiBracket f g) x (α.reebVectorField x) =
      mvfderiv I (fun y ↦ mvfderiv I g y (α.reebVectorField y)) x
          (α.contactHamiltonianVectorField f x) -
        mvfderiv I (fun y ↦ mvfderiv I f y (α.reebVectorField y)) x
          (α.contactHamiltonianVectorField g x) := by
  set R := α.reebVectorField
  set Rf : M → ℝ := fun y ↦ mvfderiv I f y (R y)
  have hRd : MDifferentiable I I.tangent (fun y ↦ (R y : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.mdifferentiable (by simp)
  have hXd := hα.mdifferentiable_contactHamiltonianVectorField hf
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hdgX : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ mvfderiv I g y (α.contactHamiltonianVectorField f y)) x :=
    mdifferentiableAt_mvfderiv_apply (hg x) h2 (hXd x)
  have hgRf : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ g y * Rf y) x :=
    ((hg x).mdifferentiableAt two_ne_zero).mul
      (mdifferentiableAt_mvfderiv_apply (hf x) h2 (hRd x))
  have hfg : α.jacobiBracket f g =
      fun y ↦ mvfderiv I g y (α.contactHamiltonianVectorField f y) - g y * Rf y :=
    funext (hα.jacobiBracket_eq_mvfderiv_sub_mul f g)
  -- `R_α(dg(X_f)) = X_f(R_α g) + dg([R_α, X_f])`, and `[R_α, X_f] = X_{R_α f}`.
  have hRX := mvfderiv_mlieBracket (hg x) h2 (hRd x) (hXd x)
  rw [hα.mlieBracket_reebVectorField_contactHamiltonianVectorField hf] at hRX
  -- `dg(X_{R_α f}) = {R_α f, g}_α + g R_α(R_α f)`, and `{R_α f, g}_α = R_α f R_α g - X_g(R_α f)`.
  have h1 := hα.jacobiBracket_eq_mvfderiv_sub_mul Rf g x
  have h3 := hα.jacobiBracket_eq_mul_sub_mvfderiv Rf g x
  rw [hfg, mvfderiv_fun_sub hdgX hgRf, sub_apply,
    mvfderiv_fun_mul ((hg x).mdifferentiableAt two_ne_zero)
      (mdifferentiableAt_mvfderiv_apply (hf x) h2 (hRd x))]
  simp only [add_apply, smul_apply, smul_eq_mul] at hRX ⊢
  linear_combination -hRX - h1 + h3

/-- The Jacobi identity in the form `{f, {g, h}_α}_α = {h, {g, f}_α}_α - {g, {h, f}_α}_α`, for
`C²` functions. It combines `X_{{g, h}_α} = [X_g, X_h]`, the multiplier formula for
`R_α({g, h}_α)` and the derivative of `df(X_h) = {h, f}_α + f R_α(h)` along `X_g`. -/
private theorem jacobiBracket_jacobiBracket_aux (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (hh : ContMDiff I 𝓘(ℝ) 2 h) (x : M) :
    α.jacobiBracket f (α.jacobiBracket g h) x =
      α.jacobiBracket h (α.jacobiBracket g f) x - α.jacobiBracket g (α.jacobiBracket h f) x := by
  set R := α.reebVectorField
  set Xg := α.contactHamiltonianVectorField g
  set Xh := α.contactHamiltonianVectorField h
  have hRd : MDifferentiable I I.tangent (fun y ↦ (R y : TangentBundle I M)) :=
    hα.contMDiff_reebVectorField.mdifferentiable (by simp)
  have hXg := hα.mdifferentiable_contactHamiltonianVectorField hg
  have hXh := hα.mdifferentiable_contactHamiltonianVectorField hh
  have h2 : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω) := by simp
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have hfd : MDifferentiableAt I 𝓘(ℝ) f x := (hf x).mdifferentiableAt two_ne_zero
  have hRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I g y (R y)) x :=
    mdifferentiableAt_mvfderiv_apply (hg x) h2 (hRd x)
  have hRh : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ mvfderiv I h y (R y)) x :=
    mdifferentiableAt_mvfderiv_apply (hh x) h2 (hRd x)
  -- `{f, {g, h}} = f R({g, h}) - df([X_g, X_h])`.
  have h1 := hα.jacobiBracket_eq_mul_sub_mvfderiv f (α.jacobiBracket g h) x
  rw [hα.contactHamiltonianVectorField_jacobiBracket hg hh,
    mvfderiv_mlieBracket (hf x) h2 (hXg x) (hXh x),
    hα.mvfderiv_jacobiBracket_reebVectorField hg hh] at h1
  -- `df(X_h) = {h, f} + f R(h)` and `df(X_g) = {g, f} + f R(g)`, as functions.
  have hdfXh : (fun y ↦ mvfderiv I f y (Xh y)) =
      fun y ↦ α.jacobiBracket h f y + f y * mvfderiv I h y (R y) := by
    funext y
    rw [hα.jacobiBracket_eq_mvfderiv_sub_mul]
    ring
  have hdfXg : (fun y ↦ mvfderiv I f y (Xg y)) =
      fun y ↦ α.jacobiBracket g f y + f y * mvfderiv I g y (R y) := by
    funext y
    rw [hα.jacobiBracket_eq_mvfderiv_sub_mul]
    ring
  have hfRh : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y * mvfderiv I h y (R y)) x := hfd.mul hRh
  have hfRg : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ f y * mvfderiv I g y (R y)) x := hfd.mul hRg
  rw [hdfXh, hdfXg, mvfderiv_fun_add (hα.mdifferentiable_jacobiBracket hh hf x) hfRh,
    mvfderiv_fun_add (hα.mdifferentiable_jacobiBracket hg hf x) hfRg,
    mvfderiv_fun_mul hfd hRh, mvfderiv_fun_mul hfd hRg] at h1
  -- Derivatives along `X_g` and `X_h` in terms of Jacobi brackets.
  have e1 := hα.jacobiBracket_eq_mvfderiv_sub_mul g (α.jacobiBracket h f) x
  have e2 := hα.jacobiBracket_eq_mvfderiv_sub_mul h (α.jacobiBracket g f) x
  have e3 := hα.jacobiBracket_eq_mvfderiv_sub_mul g f x
  have e4 := hα.jacobiBracket_eq_mvfderiv_sub_mul h f x
  simp only [add_apply, smul_apply, smul_eq_mul] at h1
  linear_combination h1 + e1 - e2 + mvfderiv I h x (R x) * e3 - mvfderiv I g x (R x) * e4

/-- For a contact form on a finite-dimensional manifold, the Jacobi bracket of `C²` functions
satisfies `{f, {g, h}_α}_α = {{f, g}_α, h}_α - {{f, h}_α, g}_α`. -/
theorem jacobiBracket_jacobiBracket (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hh : ContMDiff I 𝓘(ℝ) 2 h) (x : M) :
    α.jacobiBracket f (α.jacobiBracket g h) x =
      α.jacobiBracket (α.jacobiBracket f g) h x - α.jacobiBracket (α.jacobiBracket f h) g x := by
  have hgf : α.jacobiBracket g f = -α.jacobiBracket f g :=
    funext fun y ↦ by rw [Pi.neg_apply, neg_jacobiBracket]
  have hhf : α.jacobiBracket h f = -α.jacobiBracket f h :=
    funext fun y ↦ by rw [Pi.neg_apply, neg_jacobiBracket]
  rw [hα.jacobiBracket_jacobiBracket_aux hf hg hh, hgf, hhf, jacobiBracket_neg_right,
    jacobiBracket_neg_right, ← neg_jacobiBracket α (α.jacobiBracket f g),
    ← neg_jacobiBracket α (α.jacobiBracket f h)]

/-- **The Jacobi identity for the Jacobi bracket.** For a contact form on a finite-dimensional
manifold and `C²` functions `f`, `g`, `h`,
`{f, {g, h}_α}_α + {g, {h, f}_α}_α + {h, {f, g}_α}_α = 0`. -/
theorem jacobiBracket_jacobi (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g)
    (hh : ContMDiff I 𝓘(ℝ) 2 h) (x : M) :
    α.jacobiBracket f (α.jacobiBracket g h) x + α.jacobiBracket g (α.jacobiBracket h f) x +
      α.jacobiBracket h (α.jacobiBracket f g) x = 0 := by
  have hgf : α.jacobiBracket g f = -α.jacobiBracket f g :=
    funext fun y ↦ by rw [Pi.neg_apply, neg_jacobiBracket]
  rw [hα.jacobiBracket_jacobiBracket_aux hf hg hh, hgf, jacobiBracket_neg_right]
  ring

end IsContactForm

end SmoothForm

end TauCeti
