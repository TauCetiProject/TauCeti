/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.KodairaThurston
public import TauCeti.Geometry.Symplectic.Manifold.Quotient

/-!
# The symplectic form of the Kodaira–Thurston manifold

The Kodaira–Thurston manifold `TauCeti.KodairaThurston` is the orbit space of `ℝ⁴`, with
coordinates `(x, y, z, t)`, under the deck group `Γ = H(ℤ) × ℤ`, acting by
`((a, b, c), n) • (x, y, z, t) = (a + x, b + y, c + z + a y, n + t)`
(`TauCeti.Geometry.Manifold.Instances.KodairaThurston`). This file puts a symplectic form on it.

On the cover, the constant two-form

`ω₀ = dx ∧ dt + dy ∧ dz`, `ω₀(u, w) = u_x w_t - u_t w_x + u_y w_z - u_z w_y`

(`TauCeti.KodairaThurston.Cover.symplecticForm`) is a linear symplectic form. The differential of
an element of `Γ` is the shear `(x, y, z, t) ↦ (x, y, z + a y, t)`, which preserves `ω₀`, since
`dy ∧ (dz + a dy) = dy ∧ dz`. So `Γ` acts by symplectomorphisms of `(ℝ⁴, ω₀)`, and `ω₀` descends
to a two-form `ω` on the Kodaira–Thurston manifold (`TauCeti.KodairaThurston.symplecticForm`). It
is the unique two-form whose pullback to the cover is `ω₀`
(`TauCeti.KodairaThurston.eq_symplecticForm_iff`), and it is symplectic
(`TauCeti.KodairaThurston.isSymplectic_symplecticForm`), by the descent of symplectic forms to
quotients by discrete groups (`TauCeti.SmoothTwoForm.isSymplectic_descend_iff`).

Thus the Kodaira–Thurston manifold is a compact symplectic four-manifold. Thurston observed that
its first Betti number is `3`, so by Hodge theory it admits no Kähler structure; neither the Betti
number nor the Kähler obstruction is proved here.

## Main definitions

* `TauCeti.KodairaThurston.Cover.symplecticForm`: the linear symplectic form `dx ∧ dt + dy ∧ dz`
  of the cover.
* `TauCeti.KodairaThurston.symplecticForm`: the symplectic form of the Kodaira–Thurston manifold.

## Main results

* `TauCeti.KodairaThurston.Cover.mpullback_smul_constSmooth`: the deck group acts by
  symplectomorphisms of the cover.
* `TauCeti.KodairaThurston.mpullback_mk_symplecticForm`,
  `TauCeti.KodairaThurston.eq_symplecticForm_iff`: the symplectic form is the unique two-form
  pulling back to `dx ∧ dt + dy ∧ dz` on the cover.
* `TauCeti.KodairaThurston.eval₂_symplecticForm_mfderiv_mk`: the symplectic form in the
  coordinates of the cover.
* `TauCeti.KodairaThurston.isSymplectic_symplecticForm`: it is a symplectic form.

## References

* W. P. Thurston, *Some simple examples of symplectic manifolds*, Proceedings of the American
  Mathematical Society 55 (1976), 467–468.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace KodairaThurston

namespace Cover

/-- The bilinear form `dx ∧ dt + dy ∧ dz` on the cover. -/
private def bilinForm : LinearMap.BilinForm ℝ Cover :=
  LinearMap.mk₂ ℝ (fun u w ↦ u.x * w.t - u.t * w.x + u.y * w.z - u.z * w.y)
    (fun _ _ _ ↦ by simp only [x_add, y_add, z_add, t_add]; ring)
    (fun _ _ _ ↦ by simp only [x_smul, y_smul, z_smul, t_smul, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [x_add, y_add, z_add, t_add]; ring)
    (fun _ _ _ ↦ by simp only [x_smul, y_smul, z_smul, t_smul, smul_eq_mul]; ring)

private theorem bilinForm_apply (u w : Cover) :
    bilinForm u w = u.x * w.t - u.t * w.x + u.y * w.z - u.z * w.y :=
  (rfl)

private theorem bilinForm_isAlt : bilinForm.IsAlt := fun u ↦ by
  rw [bilinForm_apply]
  ring

/-- The linear symplectic form `ω₀ = dx ∧ dt + dy ∧ dz` on the cover `ℝ⁴` of the Kodaira–Thurston
manifold: `ω₀(u, w) = u_x w_t - u_t w_x + u_y w_z - u_z w_y`. -/
def symplecticForm : SymplecticForm Cover where
  toBilinForm := bilinForm
  isAlt := bilinForm_isAlt
  nondegenerate := by
    refine (bilinForm_isAlt.isRefl).nondegenerate_iff_separatingLeft.mpr fun u hu ↦ ?_
    -- Pairing `u` with the four coordinate vectors recovers its coordinates.
    have hx := hu (mk 0 0 0 1)
    have hy := hu (mk 0 0 1 0)
    have hz := hu (mk 0 1 0 0)
    have ht := hu (mk 1 0 0 0)
    simp only [bilinForm_apply, x_mk, y_mk, z_mk, t_mk] at hx hy hz ht
    ext <;> simp only [x_zero, y_zero, z_zero, t_zero] <;> linarith

/-- The symplectic form of the cover in coordinates. -/
@[simp]
theorem symplecticForm_apply (u w : Cover) :
    symplecticForm u w = u.x * w.t - u.t * w.x + u.y * w.z - u.z * w.y :=
  (rfl)

/-- The shears preserve the symplectic form of the cover. -/
theorem symplecticForm_shear (a : ℝ) (u w : Cover) :
    symplecticForm (shear a u) (shear a w) = symplecticForm u w := by
  simp only [symplecticForm_apply, shear_apply, x_mk, y_mk, z_mk, t_mk]
  ring

/-- The deck group acts by symplectomorphisms of the cover: each element pulls the constant form
`dx ∧ dt + dy ∧ dz` back to itself. -/
theorem mpullback_smul_constSmooth (γ : DeckGroup) :
    SmoothForm.mpullback (γ • ·) (contMDiff_const_smul γ) symplecticForm.constSmooth =
      symplecticForm.constSmooth := by
  refine SmoothBundleForm.ext_eval₂ fun p v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, mfderiv_smul]
  exact (SymplecticForm.constSmooth_apply _ _ _ _).trans
    ((symplecticForm_shear _ v w).trans (SymplecticForm.constSmooth_apply _ _ _ _).symm)

end Cover

open Cover

/-- The symplectic form `ω` of the Kodaira–Thurston manifold, the descent of the constant form
`dx ∧ dt + dy ∧ dz` on its cover `ℝ⁴`: the unique two-form whose pullback to the cover is
`dx ∧ dt + dy ∧ dz` (`TauCeti.KodairaThurston.eq_symplecticForm_iff`). -/
def symplecticForm : SmoothTwoForm 𝓘(ℝ, Cover) KodairaThurston :=
  SmoothForm.descend Cover.symplecticForm.constSmooth mpullback_smul_constSmooth

/-- The symplectic form pulls back to `dx ∧ dt + dy ∧ dz` on the cover. -/
@[simp]
theorem mpullback_mk_symplecticForm :
    SmoothForm.mpullback mk isLocalDiffeomorph_mk.contMDiff symplecticForm =
      Cover.symplecticForm.constSmooth :=
  SmoothForm.mpullback_quotientMk_descend

/-- The symplectic form is the unique two-form on the Kodaira–Thurston manifold whose pullback to
the cover is `dx ∧ dt + dy ∧ dz`. -/
theorem eq_symplecticForm_iff {σ : SmoothTwoForm 𝓘(ℝ, Cover) KodairaThurston} :
    σ = symplecticForm ↔
      SmoothForm.mpullback mk isLocalDiffeomorph_mk.contMDiff σ =
        Cover.symplecticForm.constSmooth :=
  SmoothForm.eq_descend_iff

/-- The symplectic form in the coordinates of the cover: on the images of tangent vectors `u` and
`w` at a point of `ℝ⁴`, it is `u_x w_t - u_t w_x + u_y w_z - u_z w_y`. -/
theorem eval₂_symplecticForm_mfderiv_mk (p u w : Cover) :
    symplecticForm.eval₂ (mk p) (mfderiv 𝓘(ℝ, Cover) 𝓘(ℝ, Cover) mk p u)
        (mfderiv 𝓘(ℝ, Cover) 𝓘(ℝ, Cover) mk p w) =
      u.x * w.t - u.t * w.x + u.y * w.z - u.z * w.y := by
  have h := SmoothForm.eval₂_mpullback mk isLocalDiffeomorph_mk.contMDiff symplecticForm p u w
  rw [mpullback_mk_symplecticForm] at h
  exact h.symm.trans (SymplecticForm.constSmooth_apply _ _ _ _)

/-- **The Kodaira–Thurston manifold is a symplectic manifold**: the descent of
`dx ∧ dt + dy ∧ dz` is closed and nondegenerate. -/
theorem isSymplectic_symplecticForm : symplecticForm.IsSymplectic :=
  SmoothTwoForm.isSymplectic_descend_iff.2 (SymplecticForm.isSymplectic_constSmooth _)

end KodairaThurston

end TauCeti
