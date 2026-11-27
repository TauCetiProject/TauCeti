/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Jacobi
public import TauCeti.Geometry.Contact.Standard
import TauCeti.Geometry.Contact.Standard.Hamiltonian
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Jacobi bracket of the standard contact form

On `ℝ³ = ℝ × ℝ × ℝ` with coordinates `p = (x, y, z)`, let `α = dz - x dy` be the standard contact
form (`TauCeti.standardContactForm`), with Reeb vector field `R_α = ∂_z` and contact Hamiltonian
vector fields `X_f = (x f_z + f_y) ∂_x - f_x ∂_y + (f - x f_x) ∂_z`
(`TauCeti.contactHamiltonianVectorField_standardContactForm`). This file computes its Jacobi bracket
`{f, g}_α = dα(X_f, X_g) + f R_α(g) - g R_α(f)` (`TauCeti.SmoothForm.jacobiBracket`) in
coordinates. Writing `f_x`, `f_y`, `f_z` for the partial derivatives of `f`,

`{f, g}_α = (x f_z + f_y) g_x - f_x g_y + (f - x f_x) g_z - g f_z`

(`TauCeti.jacobiBracket_standardContactForm`), the derivative `X_f(g)` of `g` along `X_f`
corrected by `-g R_α(f)`. As for the contact Hamiltonian vector fields, the formula holds for all
functions, with the Fréchet derivative of a function read as zero where it is not differentiable.

For the coordinate functions it gives

`{x, y}_α = -1`,  `{y, z}_α = y`,  `{z, x}_α = 0`

(`TauCeti.jacobiBracket_standardContactForm_x_y`, `TauCeti.jacobiBracket_standardContactForm_y_z`,
`TauCeti.jacobiBracket_standardContactForm_z_x`). The bracket `{x, y}_α` is entirely the term
`dα(X_x, X_y) = -1`, since `R_α x = R_α y = 0`. By
`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_jacobiBracket`, the Lie bracket of
`X_x = -∂_y` and `X_y = ∂_x + y ∂_z` is therefore the contact Hamiltonian vector field of the
constant `-1`, which is `-R_α = -∂_z`
(`TauCeti.mlieBracket_contactHamiltonianVectorField_standardContactForm_x_y`). This fixes the
sign of the `dα` term in the bracket: with `-dα(X_f, X_g)` in its place, `{x, y}` would be `+1`,
whose contact Hamiltonian vector field `∂_z` is not `[X_x, X_y]`.

The three coordinate brackets are stated as equalities of functions, so they rewrite iterated
brackets of coordinates. For instance the three terms of the Jacobi identity
`{x, {y, z}} + {y, {z, x}} + {z, {x, y}} = 0` become `{x, y} = -1`, `{y, 0} = 0` and
`{z, -1} = R_α z = 1`, the last two by `TauCeti.SmoothForm.IsContactForm.jacobiBracket_const_right`.

## Main results

* `TauCeti.jacobiBracket_standardContactForm`: the Jacobi bracket of `dz - x dy` in coordinates.
* `TauCeti.jacobiBracket_standardContactForm_x_y`, `TauCeti.jacobiBracket_standardContactForm_y_z`,
  `TauCeti.jacobiBracket_standardContactForm_z_x`: the brackets of the coordinate functions.
* `TauCeti.mlieBracket_contactHamiltonianVectorField_standardContactForm_x_y`:
  `[X_x, X_y] = X_(-1) = -∂_z`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3 (contact Hamiltonians and the Jacobi bracket).
-/

public section

noncomputable section

open VectorField
open scoped Manifold

namespace TauCeti

/-- **The Jacobi bracket of `dz - x dy`.** For all functions `f` and `g` on `ℝ³`, the Jacobi bracket
for the standard contact form is
`{f, g}_α = (x f_z + f_y) g_x - f_x g_y + (f - x f_x) g_z - g f_z`, where `f_x = df(∂_x)`,
`f_y = df(∂_y)`, `f_z = df(∂_z)`, and similarly for `g`. -/
theorem jacobiBracket_standardContactForm (f g : ℝ × ℝ × ℝ → ℝ) (p : ℝ × ℝ × ℝ) :
    standardContactForm.jacobiBracket f g p =
      (p.1 * fderiv ℝ f p (0, 0, 1) + fderiv ℝ f p (0, 1, 0)) * fderiv ℝ g p (1, 0, 0) -
          fderiv ℝ f p (1, 0, 0) * fderiv ℝ g p (0, 1, 0) +
        (f p - p.1 * fderiv ℝ f p (1, 0, 0)) * fderiv ℝ g p (0, 0, 1) -
          g p * fderiv ℝ f p (0, 0, 1) := by
  -- `{f, g}_α = X_f(g) - g R_α(f)`, with `X_f(g)` expanded in the coordinates of `X_f`.
  rw [isContactForm_standardContactForm.jacobiBracket_eq_mvfderiv, mvfderiv_eq_fderiv_apply,
    mvfderiv_eq_fderiv_apply, reebVectorField_standardContactForm, standardReebField_apply,
    fderiv_apply_eq_coords g p (standardContactForm.contactHamiltonianVectorField f p),
    contactHamiltonianVectorField_standardContactForm]
  ring

/-- The Jacobi bracket of the coordinates `x` and `y` for `dz - x dy` is `{x, y}_α = -1`. -/
@[simp]
theorem jacobiBracket_standardContactForm_x_y :
    standardContactForm.jacobiBracket (fun q ↦ q.1) (fun q ↦ q.2.1) = fun _ ↦ -1 := by
  funext p
  rw [jacobiBracket_standardContactForm, fderiv_fst, hasFDerivAt_snd.fst.fderiv]
  simp

/-- The Jacobi bracket of the coordinates `y` and `z` for `dz - x dy` is `{y, z}_α = y`. -/
@[simp]
theorem jacobiBracket_standardContactForm_y_z :
    standardContactForm.jacobiBracket (fun q ↦ q.2.1) (fun q ↦ q.2.2) = fun q ↦ q.2.1 := by
  funext p
  rw [jacobiBracket_standardContactForm, hasFDerivAt_snd.fst.fderiv, hasFDerivAt_snd.snd.fderiv]
  simp

/-- The Jacobi bracket of the coordinates `z` and `x` for `dz - x dy` is `{z, x}_α = 0`. -/
@[simp]
theorem jacobiBracket_standardContactForm_z_x :
    standardContactForm.jacobiBracket (fun q ↦ q.2.2) (fun q ↦ q.1) = fun _ ↦ 0 := by
  funext p
  rw [jacobiBracket_standardContactForm, hasFDerivAt_snd.snd.fderiv, fderiv_fst]
  simp

/-- **The Lie bracket of `X_x` and `X_y`.** For `dz - x dy`, the Lie bracket of the contact
Hamiltonian vector fields `X_x = -∂_y` and `X_y = ∂_x + y ∂_z` is minus the Reeb vector field,
`[X_x, X_y] = -∂_z`. This is the contact Hamiltonian vector field `X_(-1) = -R_α` of the constant
`-1 = {x, y}_α`. -/
theorem mlieBracket_contactHamiltonianVectorField_standardContactForm_x_y :
    mlieBracket 𝓘(ℝ, ℝ × ℝ × ℝ) (standardContactForm.contactHamiltonianVectorField fun q ↦ q.1)
        (standardContactForm.contactHamiltonianVectorField fun q ↦ q.2.1) =
      -standardReebField := by
  rw [← isContactForm_standardContactForm.contactHamiltonianVectorField_jacobiBracket
      contDiff_fst.contMDiff contDiff_snd.fst.contMDiff, jacobiBracket_standardContactForm_x_y,
    isContactForm_standardContactForm.contactHamiltonianVectorField_const,
    funext reebVectorField_standardContactForm, neg_one_smul]

end TauCeti
