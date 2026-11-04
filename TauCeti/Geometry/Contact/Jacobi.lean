/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Hamiltonian
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Jacobi bracket of a contact form

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α` and
contact Hamiltonian vector fields `X_f` (`TauCeti.SmoothForm.contactHamiltonianVectorField`),
normalized by `α(X_f) = f` and `ι_(X_f) dα = (R_α f) α - df`. The **Jacobi bracket** of two
functions is

`{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)`

(`TauCeti.SmoothForm.jacobiBracket`). It is the analogue for contact forms of the Poisson bracket
of a symplectic form, and it is the bracket induced by contact vector fields:

* `{f, g}_α = α([X_f, X_g])`
  (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_apply_mlieBracket`);
* `X_{{f, g}_α} = [X_f, X_g]`
  (`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`), so that
  `f ↦ X_f` takes Jacobi brackets to Lie brackets of vector fields.

The second identity rests on the fact that the Lie bracket of two contact vector fields is again a
contact vector field: if `X` and `Y` are contact Hamiltonian vector fields of class `C²`, then so is
`[X, Y]`, with Hamiltonian `α([X, Y])`
(`TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_mlieBracket`). Indeed, both
`X` and `Y` preserve the contact distribution `ξ = ker α` infinitesimally, so by the Jacobi
identity for vector fields so does `[X, Y]`
(`TauCeti.SmoothForm.IsContactHamiltonianVectorField.mlieBracket_mlieBracket_mem_kerDistribution`);
hence `L_{[X, Y]} α` vanishes on `ξ` and is a multiple of `α`.

The Jacobi bracket is a **Jacobi structure** on functions of class `C³`:

* it is antisymmetric (`TauCeti.SmoothForm.neg_jacobiBracket`) and bilinear;
* it is a first-order differential operator in each argument, satisfying the generalized Leibniz
  rule `{f, g h}_α = g {f, h}_α + h {f, g}_α + g h R_α(f)`
  (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_mul_right`); unlike a Poisson bracket it is not
  a derivation, since `{f, 1}_α = -R_α(f)` need not vanish
  (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_one_right`);
* it satisfies the **Jacobi identity** `{f, {g, k}_α}_α + {g, {k, f}_α}_α + {k, {f, g}_α}_α = 0`
  (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_jacobi`).

The bracket with the constant `1` recovers the Reeb vector field: `{1, g}_α = R_α(g)`
(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_one_left`). Equivalently,
`{f, g}_α = X_f(g) - g R_α(f)` (`TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_mvfderiv`).

The argument for the Jacobi identity, through the Jacobi identity for Lie brackets of vector
fields, follows `TauCeti.SmoothTwoForm.IsNondegenerate.poissonBracket_jacobi` for the Poisson
bracket of a symplectic form, in `TauCeti.Geometry.Symplectic.Hamiltonian.Bracket`.

## Main definitions

* `TauCeti.SmoothForm.jacobiBracket`: the Jacobi bracket `{f, g}_α`.

## Main results

* `TauCeti.SmoothForm.IsContactForm.isContactHamiltonianVectorField_mlieBracket`: the bracket of
  two contact vector fields is a contact vector field.
* `TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_apply_mlieBracket`:
  `{f, g}_α = α([X_f, X_g])`.
* `TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`:
  `X_{{f, g}_α} = [X_f, X_g]`.
* `TauCeti.SmoothForm.IsContactForm.jacobiBracket_mul_right`: the generalized Leibniz rule.
* `TauCeti.SmoothForm.IsContactForm.jacobiBracket_jacobi`: the Jacobi identity.

## References

* A. Lichnerowicz, *Les variétés de Jacobi et leurs algèbres de Lie associées*, J. Math. Pures
  Appl. 57 (1978), 453–488.
* A. A. Kirillov, *Local Lie algebras*, Russian Math. Surveys 31 (1976), 55–75.
* Hansjörg Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced
  Mathematics 109 (2008), Section 2.3.
-/

public section

noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g h : M → ℝ} {X Y W : (x : M) → TangentSpace I x} {x : M}

/-! ### The definition -/

/-- The **Jacobi bracket** `{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)` of two functions, where
`X_f` and `X_g` are the contact Hamiltonian vector fields of `f` and `g` and `R_α` is the Reeb
vector field of `α`. For a contact form on a finite-dimensional manifold it is
`{f, g}_α = α([X_f, X_g])`
(`TauCeti.SmoothForm.IsContactForm.jacobiBracket_eq_apply_mlieBracket`). -/
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

/-- The exterior derivative of a one-form, evaluated at a point on two tangent vectors, as a
bilinear form. -/
private theorem mextDeriv_apply_eq_bilinFormAt (α : SmoothForm I M ℝ 1) (x : M)
    (u v : TangentSpace I x) :
    mextDeriv α.1 x ![u, v] = (mextDerivₗ I 1 α).bilinFormAt x u v := by
  rw [bilinFormAt_apply, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply]

/-- **The Jacobi bracket is antisymmetric.** -/
theorem neg_jacobiBracket (α : SmoothForm I M ℝ 1) (f g : M → ℝ) (x : M) :
    -α.jacobiBracket g f x = α.jacobiBracket f g x := by
  rw [jacobiBracket_def, jacobiBracket_def, mextDeriv_apply_eq_bilinFormAt,
    mextDeriv_apply_eq_bilinFormAt, ← LinearMap.IsAlt.neg
      (isAlt_bilinFormAt _ x) (α.contactHamiltonianVectorField g x)]
  ring

/-- The Jacobi bracket of a function with itself vanishes. -/
@[simp]
theorem jacobiBracket_self (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    α.jacobiBracket f f x = 0 := by
  rw [jacobiBracket_def, mextDeriv_apply_eq_bilinFormAt,
    LinearMap.IsAlt.self_eq_zero (isAlt_bilinFormAt _ x)]
  ring

/-- Negating the first argument negates the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_neg_left (x : M) :
    α.jacobiBracket (-f) g x = -α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_neg, mvfderiv_neg,
    mextDeriv_apply_eq_bilinFormAt, map_neg, LinearMap.neg_apply, neg_apply, Pi.neg_apply]
  ring

/-- Negating the second argument negates the Jacobi bracket. -/
@[simp]
theorem jacobiBracket_neg_right (x : M) :
    α.jacobiBracket f (-g) x = -α.jacobiBracket f g x := by
  rw [← neg_jacobiBracket, jacobiBracket_neg_left, ← neg_jacobiBracket α f g]

/-- The Jacobi bracket is additive in its first argument on differentiable functions. -/
theorem jacobiBracket_add_left (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.jacobiBracket (f + g) h x = α.jacobiBracket f h x + α.jacobiBracket g h x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_add hf hg, mvfderiv_add hf hg,
    mextDeriv_apply_eq_bilinFormAt, map_add, LinearMap.add_apply, add_apply,
    Pi.add_apply]
  ring

/-- The Jacobi bracket is additive in its second argument on differentiable functions. -/
theorem jacobiBracket_add_right (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.jacobiBracket h (f + g) x = α.jacobiBracket h f x + α.jacobiBracket h g x := by
  rw [← neg_jacobiBracket, jacobiBracket_add_left hf hg, ← neg_jacobiBracket α h f,
    ← neg_jacobiBracket α h g]
  ring

/-- Multiplication of the first argument by a real constant scales the Jacobi bracket. -/
theorem jacobiBracket_const_smul_left (c : ℝ) (x : M) :
    α.jacobiBracket (c • f) g x = c • α.jacobiBracket f g x := by
  simp only [jacobiBracket_def, contactHamiltonianVectorField_const_smul c x,
    mvfderiv_const_smul_field, mextDeriv_apply_eq_bilinFormAt, map_smul, LinearMap.smul_apply,
    smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Multiplication of the second argument by a real constant scales the Jacobi bracket. -/
theorem jacobiBracket_const_smul_right (c : ℝ) (x : M) :
    α.jacobiBracket f (c • g) x = c • α.jacobiBracket f g x := by
  rw [← neg_jacobiBracket, jacobiBracket_const_smul_left, ← neg_jacobiBracket α f g, smul_neg]

/-! ### Brackets of contact vector fields -/

namespace IsContactHamiltonianVectorField

variable [CompleteSpace E]

/-- **The bracket of two contact vector fields preserves the contact distribution**
infinitesimally. Let `X` and `Y` be contact Hamiltonian vector fields and let `W` be a vector field
tangent to `ξ = ker α` near `x`, all three of class `C²` near `x`. Then `[[X, Y], W]` is tangent
to `ξ` at `x`. -/
theorem mlieBracket_mlieBracket_mem_kerDistribution (hX : α.IsContactHamiltonianVectorField f X)
    (hY : α.IsContactHamiltonianVectorField g Y)
    (hX₂ : ∀ᶠ y in 𝓝 x, ContMDiffAt I I.tangent 2 (T% X) y)
    (hY₂ : ∀ᶠ y in 𝓝 x, ContMDiffAt I I.tangent 2 (T% Y) y)
    (hW₂ : ∀ᶠ y in 𝓝 x, ContMDiffAt I I.tangent 2 (T% W) y)
    (hW : ∀ᶠ y in 𝓝 x, W y ∈ α.kerDistribution y) :
    mlieBracket I (mlieBracket I X Y) W x ∈ α.kerDistribution x := by
  have : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  -- By the Jacobi identity `[[X, Y], W] = [X, [Y, W]] - [Y, [X, W]]`, it suffices to treat the two
  -- double brackets on the right, using that `X` and `Y` both preserve `ξ`.
  -- The bracket of `W` with a contact vector field is differentiable at `x` and tangent to `ξ`
  -- near `x`, so its bracket with a second contact vector field is tangent to `ξ` at `x`.
  have key {Z Z' : (y : M) → TangentSpace I y} {k k' : M → ℝ}
      (hZ : α.IsContactHamiltonianVectorField k Z) (hZ' : α.IsContactHamiltonianVectorField k' Z')
      (hZ₂ : ∀ᶠ y in 𝓝 x, ContMDiffAt I I.tangent 2 (T% Z) y)
      (hZ'₂ : ∀ᶠ y in 𝓝 x, ContMDiffAt I I.tangent 2 (T% Z') y) :
      mlieBracket I Z' (mlieBracket I Z W) x ∈ α.kerDistribution x := by
    refine hZ'.mlieBracket_mem_kerDistribution (hZ'₂.self_of_nhds.mdifferentiableAt two_ne_zero)
      ((hZ₂.self_of_nhds.mlieBracket_vectorField (m := 1) (n := 2) hW₂.self_of_nhds
        (by simp [one_add_one_eq_two])).mdifferentiableAt one_ne_zero) ?_
    filter_upwards [hZ₂, hW₂, hW.eventually_nhds] with y hyZ hy₂ hyW
    exact hZ.mlieBracket_mem_kerDistribution (hyZ.mdifferentiableAt two_ne_zero)
      (hy₂.mdifferentiableAt two_ne_zero) hyW
  have hL := leibniz_identity_mlieBracket_apply (hX₂.self_of_nhds.of_le (by simp))
    (hY₂.self_of_nhds.of_le (by simp)) (hW₂.self_of_nhds.of_le (by simp))
  rw [show mlieBracket I (mlieBracket I X Y) W x =
      mlieBracket I X (mlieBracket I Y W) x - mlieBracket I Y (mlieBracket I X W) x by
    rw [hL]; abel]
  exact sub_mem (key hY hX hY₂ hX₂) (key hX hY hX₂ hY₂)

end IsContactHamiltonianVectorField

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- A one-form value vanishing on the contact hyperplane `ξ_y` is its value on the Reeb vector
times `α_y`. -/
private theorem eq_smul_of_forall_mem_kerDistribution {φ : RoughForm I M ℝ 1} {y : M}
    (hφ : ∀ w ∈ α.kerDistribution y, φ y ![w] = 0) :
    φ y = φ y ![α.reebVectorField y] • α.1 y := by
  let ℓ := (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I y) ℝ (0 : Fin 1)).symm (φ y)
  have hℓ (u : TangentSpace I y) : φ y ![u] = ℓ u := by
    rw [ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply, Matrix.vec_single_eq_const]
  ext v
  obtain ⟨u, rfl⟩ : ∃ u, v = ![u] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  -- Split `u` along `T_y M = ξ_y ⊕ ℝ R_α(y)`.
  have hu : u - α.1 y ![u] • α.reebVectorField y ∈ α.kerDistribution y := by
    rw [mem_kerDistribution, ← degreeOneEquiv_apply_apply_vec, map_sub, map_smul,
      degreeOneEquiv_apply_apply_vec, degreeOneEquiv_apply_apply_vec, hα.apply_reebVectorField,
      smul_eq_mul, mul_one, sub_self]
  have h := hφ _ hu
  rw [hℓ, map_sub, map_smul, ← hℓ, ← hℓ, smul_eq_mul, sub_eq_zero] at h
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, h, mul_comm]

/-- A tangent vector in the contact hyperplane `ξ_y` extends to a vector field tangent to `ξ`
everywhere and of class `C²` near `y`. -/
private theorem exists_eventually_contMDiffAt_mem_kerDistribution {y : M}
    {w : TangentSpace I y} (hw : w ∈ α.kerDistribution y) :
    ∃ W : (z : M) → TangentSpace I z, (∀ᶠ z in 𝓝 y, ContMDiffAt I I.tangent 2 (T% W) z) ∧
      (∀ z, W z ∈ α.kerDistribution z) ∧ W y = w := by
  let V : (z : M) → TangentSpace I z := FiberBundle.extend E w
  have hV : ContMDiffAt I I.tangent ∞ (T% V) y := FiberBundle.contMDiffAt_extend I E w
  have hαV : ContMDiffAt I 𝓘(ℝ) ∞ (fun z ↦ degreeOneEquiv α z (V z)) y := by
    have h := ((degreeOneEquiv α).contMDiff y).clm_bundle_apply hV
    rw [contMDiffAt_section] at h
    simpa only [Trivial.eq_trivialization M ℝ, Trivial.trivialization_apply] using h
  -- Project a local extension `V` of `w` to `ξ` along the Reeb vector field.
  refine ⟨fun z ↦ V z - degreeOneEquiv α z (V z) • α.reebVectorField z, ?_, fun z ↦ ?_, ?_⟩
  · have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
    exact (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
      ((hV.sub_section (hαV.smul_section (hα.contMDiff_reebVectorField y))).of_le (by simp))
  · rw [mem_kerDistribution, ← degreeOneEquiv_apply_apply_vec, map_sub, map_smul,
      degreeOneEquiv_apply_apply_vec α z (α.reebVectorField z), hα.apply_reebVectorField,
      smul_eq_mul, mul_one, sub_self]
  · have hVy : V y = w := FiberBundle.extend_apply_self E w
    beta_reduce
    rw [hVy, degreeOneEquiv_apply_apply_vec, mem_kerDistribution.1 hw, zero_smul, sub_zero]

/-- **The bracket of two contact vector fields is a contact vector field.** For a contact form
`α`, if `X` and `Y` are contact Hamiltonian vector fields of class `C²`, then `[X, Y]` is the
contact Hamiltonian vector field of `α([X, Y])`. -/
theorem isContactHamiltonianVectorField_mlieBracket (hX : α.IsContactHamiltonianVectorField f X)
    (hY : α.IsContactHamiltonianVectorField g Y) (hX₂ : ContMDiff I I.tangent 2 (T% X))
    (hY₂ : ContMDiff I I.tangent 2 (T% Y)) :
    α.IsContactHamiltonianVectorField (fun y ↦ α.1 y ![mlieBracket I X Y y])
      (mlieBracket I X Y) := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hZ : MDifferentiable I I.tangent (T% (mlieBracket I X Y)) := fun y ↦
    ((hX₂ y).mlieBracket_vectorField (m := 1) (n := 2) (hY₂ y)
      (by simp [one_add_one_eq_two])).mdifferentiableAt one_ne_zero
  -- `L_{[X, Y]} α` vanishes on `ξ`, so it is a multiple of `α`.
  refine (hα.isContactHamiltonianVectorField_iff_mlieDerivForm hZ).2 ⟨fun _ ↦ rfl,
    fun y ↦ mlieDerivForm (mlieBracket I X Y) α.1 y ![α.reebVectorField y],
    funext fun y ↦ hα.eq_smul_of_forall_mem_kerDistribution fun w hw ↦ ?_⟩
  obtain ⟨W, hW₂, hWξ, rfl⟩ := hα.exists_eventually_contMDiffAt_mem_kerDistribution hw
  -- The bracket formula `L_Z α (W) = Z(α(W)) - α([Z, W])`, where `α(W) = 0`.
  have hαW : (fun z ↦ α.1 z ![W z]) = fun _ ↦ (0 : ℝ) :=
    funext fun z ↦ mem_kerDistribution.1 (hWξ z)
  rw [mlieDerivForm_apply_one (α.mdifferentiableAt y)
      (hW₂.self_of_nhds.mdifferentiableAt two_ne_zero), hαW, mvfderiv_const,
    zero_apply, zero_sub, neg_eq_zero, ← mem_kerDistribution]
  exact hX.mlieBracket_mlieBracket_mem_kerDistribution hY (.of_forall hX₂) (.of_forall hY₂) hW₂
    (.of_forall hWξ)

/-! ### The Jacobi bracket of a contact form -/

/-- The Jacobi bracket is `{f, g}_α = X_f(g) - g R_α(f)`. -/
theorem jacobiBracket_eq_mvfderiv (f g : M → ℝ) (x : M) :
    α.jacobiBracket f g x = mvfderiv I g x (α.contactHamiltonianVectorField f x) -
      g x * mvfderiv I f x (α.reebVectorField x) := by
  rw [← neg_jacobiBracket, jacobiBracket_def, hα.mextDeriv_contactHamiltonianVectorField_left,
    hα.apply_contactHamiltonianVectorField]
  ring

/-- **Regularity of the Jacobi bracket.** For a contact form on a finite-dimensional manifold, the
Jacobi bracket of two `C^(n+1)` functions is of class `C^n`, for `n ≤ ∞`. -/
theorem contMDiff_jacobiBracket {n : WithTop ℕ∞} (hn : n ≤ ∞) (hf : ContMDiff I 𝓘(ℝ) (n + 1) f)
    (hg : ContMDiff I 𝓘(ℝ) (n + 1) g) : ContMDiff I 𝓘(ℝ) n (α.jacobiBracket f g) := by
  have hXg : ContMDiff I 𝓘(ℝ) n fun x ↦ mvfderiv I g x (α.contactHamiltonianVectorField f x) :=
    (hg.contMDiff_mvfderiv_apply le_rfl).comp (hα.contMDiff_contactHamiltonianVectorField hn hf)
  have hRf : ContMDiff I 𝓘(ℝ) n fun x ↦ mvfderiv I f x (α.reebVectorField x) :=
    (hf.contMDiff_mvfderiv_apply le_rfl).comp (hα.contMDiff_reebVectorField.of_le hn)
  rw [show α.jacobiBracket f g = _ from funext (hα.jacobiBracket_eq_mvfderiv f g)]
  exact hXg.sub ((hg.of_le le_self_add).mul hRf)

/-- **The Jacobi bracket with a constant** on the right: `{f, c}_α = -c R_α(f)`. -/
@[simp]
theorem jacobiBracket_const_right (f : M → ℝ) (c : ℝ) (x : M) :
    α.jacobiBracket f (fun _ ↦ c) x = -(c * mvfderiv I f x (α.reebVectorField x)) := by
  rw [hα.jacobiBracket_eq_mvfderiv, mvfderiv_const, zero_apply, zero_sub]

/-- **The Jacobi bracket with a constant** on the left: `{c, g}_α = c R_α(g)`. -/
@[simp]
theorem jacobiBracket_const_left (c : ℝ) (g : M → ℝ) (x : M) :
    α.jacobiBracket (fun _ ↦ c) g x = c * mvfderiv I g x (α.reebVectorField x) := by
  rw [← neg_jacobiBracket, hα.jacobiBracket_const_right, neg_neg]

/-- **The Reeb vector field is the Jacobi bracket with `1`**: `{1, g}_α = R_α(g)`. -/
@[simp]
theorem jacobiBracket_one_left (g : M → ℝ) (x : M) :
    α.jacobiBracket 1 g x = mvfderiv I g x (α.reebVectorField x) := by
  rw [Pi.one_def, hα.jacobiBracket_const_left, one_mul]

/-- The Jacobi bracket with `1` on the right is `{f, 1}_α = -R_α(f)`; in particular the Jacobi
bracket is not a derivation in its second argument. -/
@[simp]
theorem jacobiBracket_one_right (f : M → ℝ) (x : M) :
    α.jacobiBracket f 1 x = -mvfderiv I f x (α.reebVectorField x) := by
  rw [Pi.one_def, hα.jacobiBracket_const_right, one_mul]

/-- **The generalized Leibniz rule** for the Jacobi bracket in its second argument:
`{f, g h}_α = g {f, h}_α + h {f, g}_α + g h R_α(f)`, where `R_α(f) = -{f, 1}_α`. -/
theorem jacobiBracket_mul_right (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hh : MDifferentiableAt I 𝓘(ℝ) h x) :
    α.jacobiBracket f (g * h) x = g x * α.jacobiBracket f h x + h x * α.jacobiBracket f g x +
      g x * h x * mvfderiv I f x (α.reebVectorField x) := by
  simp only [hα.jacobiBracket_eq_mvfderiv, mvfderiv_mul hg hh, add_apply,
    smul_apply, smul_eq_mul, Pi.mul_apply]
  ring

/-- **The generalized Leibniz rule** for the Jacobi bracket in its first argument:
`{g h, f}_α = g {h, f}_α + h {g, f}_α - g h R_α(f)`. -/
theorem jacobiBracket_mul_left (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hh : MDifferentiableAt I 𝓘(ℝ) h x) :
    α.jacobiBracket (g * h) f x = g x * α.jacobiBracket h f x + h x * α.jacobiBracket g f x -
      g x * h x * mvfderiv I f x (α.reebVectorField x) := by
  rw [← neg_jacobiBracket, hα.jacobiBracket_mul_right hg hh, ← neg_jacobiBracket α h f,
    ← neg_jacobiBracket α g f]
  ring

/-- **The Jacobi bracket is induced by the Lie bracket** of contact Hamiltonian vector fields:
`{f, g}_α = α([X_f, X_g])` at every point where `X_f` and `X_g` are differentiable, for instance
when `f` and `g` are of class `C²`. -/
theorem jacobiBracket_eq_apply_mlieBracket
    (hf : MDifferentiableAt I I.tangent (T% (α.contactHamiltonianVectorField f)) x)
    (hg : MDifferentiableAt I I.tangent (T% (α.contactHamiltonianVectorField g)) x) :
    α.jacobiBracket f g x = α.1 x ![mlieBracket I (α.contactHamiltonianVectorField f)
      (α.contactHamiltonianVectorField g) x] := by
  -- Cartan's formula `dα(X_f, X_g) = X_f(α(X_g)) - X_g(α(X_f)) - α([X_f, X_g])`, with
  -- `α(X_f) = f` and `α(X_g) = g`.
  have h := SmoothForm.mextDeriv_apply_one (φ := α) hf hg
  rw [show (fun y ↦ α.1 y ![α.contactHamiltonianVectorField g y]) = g from
      funext (hα.apply_contactHamiltonianVectorField g),
    show (fun y ↦ α.1 y ![α.contactHamiltonianVectorField f y]) = f from
      funext (hα.apply_contactHamiltonianVectorField f)] at h
  have h₀ := jacobiBracket_def α f g x
  have h₁ := hα.jacobiBracket_eq_mvfderiv f g x
  have h₂ := hα.jacobiBracket_eq_mvfderiv g f x
  have h₃ := neg_jacobiBracket α f g x
  linarith

/-- **The contact Hamiltonian vector field of a Jacobi bracket** is the Lie bracket
`X_{{f, g}_α} = [X_f, X_g]`, for functions `f` and `g` of class `C³`. Thus `f ↦ X_f` is a
homomorphism from the Jacobi bracket to the Lie bracket of vector fields. -/
theorem contactHamiltonianVectorField_jacobiBracket (hf : ContMDiff I 𝓘(ℝ) 3 f)
    (hg : ContMDiff I 𝓘(ℝ) 3 g) :
    α.contactHamiltonianVectorField (α.jacobiBracket f g) =
      mlieBracket I (α.contactHamiltonianVectorField f) (α.contactHamiltonianVectorField g) := by
  have hXf : ContMDiff I I.tangent 2 (T% (α.contactHamiltonianVectorField f)) :=
    hα.contMDiff_contactHamiltonianVectorField (by simp) (hf.of_le (by norm_num))
  have hXg : ContMDiff I I.tangent 2 (T% (α.contactHamiltonianVectorField g)) :=
    hα.contMDiff_contactHamiltonianVectorField (by simp) (hg.of_le (by norm_num))
  have h := hα.isContactHamiltonianVectorField_mlieBracket
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField f)
    (hα.isContactHamiltonianVectorField_contactHamiltonianVectorField g) hXf hXg
  rw [show (fun y ↦ α.1 y ![mlieBracket I (α.contactHamiltonianVectorField f)
      (α.contactHamiltonianVectorField g) y]) = α.jacobiBracket f g from
    funext fun y ↦ (hα.jacobiBracket_eq_apply_mlieBracket (hXf.mdifferentiable two_ne_zero y)
      (hXg.mdifferentiable two_ne_zero y)).symm] at h
  exact (hα.isContactHamiltonianVectorField_iff_eq.1 h).symm

/-- **The Jacobi identity for the Jacobi bracket** of a contact form: for functions `f`, `g`, `k`
of class `C³`, `{f, {g, k}_α}_α + {g, {k, f}_α}_α + {k, {f, g}_α}_α = 0`. -/
theorem jacobiBracket_jacobi {k : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) 3 f)
    (hg : ContMDiff I 𝓘(ℝ) 3 g) (hk : ContMDiff I 𝓘(ℝ) 3 k) (x : M) :
    α.jacobiBracket f (α.jacobiBracket g k) x + α.jacobiBracket g (α.jacobiBracket k f) x +
      α.jacobiBracket k (α.jacobiBracket f g) x = 0 := by
  have : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (((2 : ℕ∞) : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  have hX {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 3 u) :
      ContMDiff I I.tangent 2 (T% (α.contactHamiltonianVectorField u)) :=
    hα.contMDiff_contactHamiltonianVectorField (by simp) (hu.of_le (by norm_num))
  -- Each double bracket is `α` applied to the corresponding double Lie bracket.
  have hbr {u v w : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 3 u) (hv : ContMDiff I 𝓘(ℝ) 3 v)
      (hw : ContMDiff I 𝓘(ℝ) 3 w) :
      α.jacobiBracket u (α.jacobiBracket v w) x = degreeOneEquiv α x
        (mlieBracket I (α.contactHamiltonianVectorField u) (mlieBracket I
          (α.contactHamiltonianVectorField v) (α.contactHamiltonianVectorField w)) x) := by
    have hvw : MDifferentiableAt I I.tangent
        (T% (α.contactHamiltonianVectorField (α.jacobiBracket v w))) x := by
      rw [hα.contactHamiltonianVectorField_jacobiBracket hv hw]
      exact ((hX hv x).mlieBracket_vectorField (m := 1) (n := 2) (hX hw x)
        (by simp [one_add_one_eq_two])).mdifferentiableAt one_ne_zero
    rw [hα.jacobiBracket_eq_apply_mlieBracket ((hX hu).mdifferentiable two_ne_zero x) hvw,
      hα.contactHamiltonianVectorField_jacobiBracket hv hw, degreeOneEquiv_apply_apply_vec]
  rw [hbr hf hg hk, hbr hg hk hf, hbr hk hf hg, ← map_add, ← map_add,
    jacobi_identity_mlieBracket_apply ((hX hf).of_le (by simp)).contMDiffAt
      ((hX hg).of_le (by simp)).contMDiffAt ((hX hk).of_le (by simp)).contMDiffAt, map_zero]

end IsContactForm

end SmoothForm

end TauCeti
