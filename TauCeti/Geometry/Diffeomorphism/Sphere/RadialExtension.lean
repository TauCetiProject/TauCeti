/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
public import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Extending a diffeotopy of the unit sphere radially over the ball

Let `Φ` be a `C^k` diffeotopy of the unit sphere `Sⁿ` of a real inner product space `E` of
dimension `n + 1`, with `k ≤ ∞`. Running `Φ` along the radius gives a diffeomorphism of `E`: the
sphere of radius `r` is moved by the time slice of `Φ` at time `τ r`, where `τ` is the collared
smooth transition `TauCeti.collaredSmoothTransitionUnit`, equal to `0` for `r ≤ 1 / 4` and to `1`
for `r ≥ 3 / 4`. In formulas, `TauCeti.Diffeotopy.radialExtension Φ` is

`r • u ↦ r • Φ (τ r, u)` for `r ≥ 0` and `u` on the unit sphere,

the cone over the time slice at time `τ ‖x‖` evaluated at `x` (`TauCeti.sphereCone`). Since `Φ`
starts at the identity, the extension is the identity on the closed ball of radius `1 / 4`, which
is what makes it smooth at the origin; away from the origin it is smooth as a composite of the
polar coordinates with the motion of `Φ`. Its inverse is the radial extension of the inverse
diffeotopy `Φ.symm`. It preserves norms, so it maps every closed ball about the origin onto
itself, and on the unit sphere it is the final diffeomorphism `Φ.final`.

So a diffeomorphism of `Sⁿ` which is diffeotopic to the restriction of a linear isometry extends
to a norm-preserving diffeomorphism of `E`
(`TauCeti.Diffeotopy.exists_diffeomorph_norm_eq_final_mul_unitSphereDiffeomorph`), and hence to a
diffeomorphism of the closed unit ball `Dⁿ⁺¹` as a manifold with boundary
(`TauCeti.Diffeotopy.exists_diffeomorph_closedBall_final_mul_unitSphereDiffeomorph`). This is
Cerf's derivation of `Γ₄ = 0` from his theorem `π₀ Diff⁺(S³) = 0` (`TauCeti.CerfTheorem`): every
diffeomorphism of `S³` is isotopic to an orthogonal one, and the isotopy, run along the radius,
extends it over the four-ball. Deriving `Γ₄ = 0` from `TauCeti.CerfTheorem` this way also needs
the weak Whitney path to the orthogonal map to be replaced by a diffeotopy.

## Main definitions

* `TauCeti.Diffeotopy.radialExtension`: the diffeomorphism `r • u ↦ r • Φ (τ r, u)` of `E`.

## Main results

* `TauCeti.Diffeotopy.radialExtension_smul_coe`: the defining formula on rays.
* `TauCeti.Diffeotopy.norm_radialExtension`: the radial extension preserves norms.
* `TauCeti.Diffeotopy.radialExtension_coe_sphere`: on the unit sphere it is the final
  diffeomorphism of `Φ`.
* `TauCeti.Diffeotopy.radialExtension_of_norm_le`: it is the identity near the origin.
* `TauCeti.Diffeotopy.radialExtension_symm`: its inverse is the radial extension of `Φ.symm`.
* `TauCeti.Diffeotopy.image_radialExtension_closedBall`: it maps each closed ball about the origin
  onto itself.
* `TauCeti.Diffeotopy.exists_diffeomorph_norm_eq_final_mul_unitSphereDiffeomorph`: a diffeomorphism
  of the sphere diffeotopic to a linear isometry extends to a norm-preserving diffeomorphism of `E`.
* `TauCeti.Diffeotopy.exists_diffeomorph_closedBall_final_mul_unitSphereDiffeomorph`: such a
  diffeomorphism is the boundary restriction of a diffeomorphism of the closed unit ball.

## References

* J. Cerf, *Sur les difféomorphismes de la sphère de dimension trois (Γ₄ = 0)*, Lecture Notes in
  Mathematics 53, Springer (1968), Corollaire 1.
-/

public section

noncomputable section

open Metric Module Set
open scoped Manifold ContDiff unitInterval

namespace TauCeti

namespace Diffeotopy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {k : ℕ∞ω}

/-! ### The radial extension of a family of maps of the sphere -/

/-- The radial extension of a time-dependent family `g` of maps of the unit sphere: the cone over
the slice of `g` at time `τ ‖x‖`, evaluated at `x`. -/
private def radialFun (g : I × sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) : E :=
  sphereCone (fun u ↦ (g (collaredSmoothTransitionUnit ‖x‖, u) : E)) x

/-- On the ray through `u`, the radial extension is `r • u ↦ r • g (τ r, u)`. -/
private theorem radialFun_smul_coe (g : I × sphere (0 : E) 1 → sphere (0 : E) 1) {r : ℝ}
    (hr : 0 ≤ r) (u : sphere (0 : E) 1) :
    radialFun g (r • (u : E)) = r • (g (collaredSmoothTransitionUnit r, u) : E) := by
  rw [radialFun, sphereCone_smul_coe hr, norm_smul, norm_eq_of_mem_sphere u, mul_one,
    Real.norm_of_nonneg hr]

/-- The radial extension of a family of maps into the unit sphere preserves norms. -/
private theorem norm_radialFun (g : I × sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) :
    ‖radialFun g x‖ = ‖x‖ :=
  norm_sphereCone (fun _ ↦ norm_eq_of_mem_sphere _) x

/-- If `h` undoes `g` at every time, the radial extension of `h` undoes that of `g`. -/
private theorem radialFun_radialFun {g h : I × sphere (0 : E) 1 → sphere (0 : E) 1}
    (hgh : ∀ t u, h (t, g (t, u)) = u) (x : E) : radialFun h (radialFun g x) = x := by
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, u, rfl⟩
  · simp [radialFun]
  rw [radialFun_smul_coe g hr.le, radialFun_smul_coe h hr.le, hgh]

/-- If `g` starts at the identity, its radial extension is the identity on the closed ball of
radius `1 / 4`. -/
private theorem radialFun_of_norm_le {g : I × sphere (0 : E) 1 → sphere (0 : E) 1}
    (hg : ∀ u, g (0, u) = u) {x : E} (hx : ‖x‖ ≤ 1 / 4) : radialFun g x = x := by
  rw [radialFun, collaredSmoothTransitionUnit_eq_zero_of_le hx]
  simp only [hg]
  rw [sphereCone_subtypeVal, id_eq]

/-- The punctured space `E \ {0}`, as an open subset of `E`. -/
private abbrev puncturedOpens (E : Type*) [NormedAddCommGroup E] : TopologicalSpace.Opens E :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

/-- Away from the origin, the radial extension of a `C^k` family is `C^k`: on the punctured space
it is `x ↦ ‖x‖ • g (τ ‖x‖, x / ‖x‖)`, a composite of `C^k` maps. -/
private theorem contDiffAt_radialFun_of_ne_zero {g : I × sphere (0 : E) 1 → sphere (0 : E) 1}
    (hg : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) (𝓡 n) k g) (hk : k ≤ ∞) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ k (radialFun g) x := by
  have hnorm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) k fun y : puncturedOpens E ↦ ‖(y : E)‖ := fun y ↦
    (contDiffAt_norm ℝ y.property).contMDiffAt.comp y contMDiff_subtypeVal.contMDiffAt
  have hdir := contMDiff_normalize_sphere (E := E) (n := n) (m := k)
  have hmotion : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) k fun y : puncturedOpens E ↦
      ‖(y : E)‖ • (g (collaredSmoothTransitionUnit ‖(y : E)‖,
        ⟨NormedSpace.normalize (y : E), mem_sphere_zero_iff_norm.2
          (NormedSpace.norm_normalize_eq_one_iff.2 y.property)⟩) : E) :=
    hnorm.smul (contMDiff_coe_sphere.comp
      (hg.comp (((contMDiff_collaredSmoothTransitionUnit hk).comp hnorm).prodMk hdir)))
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) k
      (fun y : puncturedOpens E ↦ radialFun g y) ⟨x, hx⟩ := by
    refine (hmotion _).congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
    dsimp only
    rw [radialFun, sphereCone_eq_norm_smul_sphereExtend,
      sphereExtend_of_ne_zero _ (show (y : E) ≠ 0 from y.property)]
  exact contMDiffAt_iff_contDiffAt.1 (contMDiffAt_subtype_iff.1 hcomp)

/-- The radial extension of a `C^k` family starting at the identity is `C^k`, for `k ≤ ∞`. Near
the origin it is the identity. -/
private theorem contDiff_radialFun {g : I × sphere (0 : E) 1 → sphere (0 : E) 1}
    (hg : ContMDiff ((𝓡∂ 1).prod (𝓡 n)) (𝓡 n) k g) (hg₀ : ∀ u, g (0, u) = u) (hk : k ≤ ∞) :
    ContDiff ℝ k (radialFun g) := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · refine contDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
    exact radialFun_of_norm_le hg₀ (mem_ball_zero_iff.1 hy).le
  · exact contDiffAt_radialFun_of_ne_zero hg hk hx

/-! ### The radial extension of a diffeotopy -/

/-- The **radial extension** of a `C^k` diffeotopy `Φ` of the unit sphere, `k ≤ ∞`: the `C^k`
diffeomorphism of `E` which moves the sphere of radius `r` by the time slice of `Φ` at time `τ r`,

`r • u ↦ r • Φ (τ r, u)`,

where `τ = TauCeti.collaredSmoothTransitionUnit` is `0` up to radius `1 / 4` and `1` from radius
`3 / 4` on. It preserves norms, is the identity near the origin, and is `Φ.final` on the unit
sphere. Its inverse is the radial extension of `Φ.symm`. -/
def radialExtension (Φ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1)) (hk : k ≤ ∞) :
    E ≃ₘ^k⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E where
  toFun := radialFun Φ
  invFun := radialFun Φ.symm
  left_inv := radialFun_radialFun Φ.symm_apply_mk_apply
  right_inv := radialFun_radialFun Φ.apply_mk_symm_apply
  contMDiff_toFun := (contDiff_radialFun Φ.contMDiff Φ.apply_zero hk).contMDiff
  contMDiff_invFun := (contDiff_radialFun Φ.symm.contMDiff Φ.symm.apply_zero hk).contMDiff

variable (Φ : Diffeotopy (𝓡 n) k (sphere (0 : E) 1)) (hk : k ≤ ∞)

/-- The radial extension at `x` is the cone over the time slice of `Φ` at time `τ ‖x‖`. -/
theorem radialExtension_apply (x : E) :
    Φ.radialExtension hk x =
      sphereCone (fun u ↦ (Φ (collaredSmoothTransitionUnit ‖x‖, u) : E)) x :=
  (rfl)

/-- On the ray through a unit vector `u`, the radial extension is `r • u ↦ r • Φ (τ r, u)`. -/
theorem radialExtension_smul_coe {r : ℝ} (hr : 0 ≤ r) (u : sphere (0 : E) 1) :
    Φ.radialExtension hk (r • (u : E)) = r • (Φ (collaredSmoothTransitionUnit r, u) : E) :=
  radialFun_smul_coe Φ hr u

/-- The inverse of the radial extension of `Φ` is the radial extension of the inverse
diffeotopy. -/
@[simp]
theorem radialExtension_symm : (Φ.radialExtension hk).symm = Φ.symm.radialExtension hk :=
  _root_.Diffeomorph.ext fun _ ↦ rfl

/-- The radial extension preserves norms. -/
@[simp]
theorem norm_radialExtension (x : E) : ‖Φ.radialExtension hk x‖ = ‖x‖ :=
  norm_radialFun Φ x

/-- The radial extension is the identity on the closed ball of radius `1 / 4`. -/
theorem radialExtension_of_norm_le {x : E} (hx : ‖x‖ ≤ 1 / 4) : Φ.radialExtension hk x = x :=
  radialFun_of_norm_le (g := ⇑Φ) Φ.apply_zero hx

/-- From radius `3 / 4` on, the radial extension is the cone over the final diffeomorphism. -/
theorem radialExtension_smul_coe_of_le {r : ℝ} (hr : 3 / 4 ≤ r) (u : sphere (0 : E) 1) :
    Φ.radialExtension hk (r • (u : E)) = r • (Φ.final u : E) := by
  rw [radialExtension_smul_coe Φ hk (by linarith), collaredSmoothTransitionUnit_eq_one_of_ge hr,
    final_apply]

/-- On the unit sphere, the radial extension of `Φ` is the final diffeomorphism of `Φ`. -/
@[simp]
theorem radialExtension_coe_sphere (u : sphere (0 : E) 1) :
    Φ.radialExtension hk u = Φ.final u := by
  simpa using Φ.radialExtension_smul_coe_of_le hk (by norm_num : (3 / 4 : ℝ) ≤ 1) u

/-- The radial extension maps each closed ball about the origin onto itself. -/
theorem image_radialExtension_closedBall (r : ℝ) :
    Φ.radialExtension hk '' closedBall 0 r = closedBall 0 r := by
  ext y
  simp only [mem_image, mem_closedBall_zero_iff]
  refine ⟨fun ⟨x, hx, hxy⟩ ↦ hxy ▸ (Φ.norm_radialExtension hk x).trans_le hx, fun hy ↦
    ⟨(Φ.radialExtension hk).symm y, ?_, (Φ.radialExtension hk).apply_symm_apply y⟩⟩
  rwa [radialExtension_symm, norm_radialExtension]

/-- **Extension over the ball.** If a diffeomorphism of the unit sphere is a linear isometry
followed by the final diffeomorphism of a `C^k` diffeotopy, `k ≤ ∞`, it extends to a
norm-preserving `C^k` diffeomorphism of `E`; in particular it extends to a diffeomorphism of the
closed unit ball. The extension is the linear isometry followed by the radial extension of the
diffeotopy. -/
theorem exists_diffeomorph_norm_eq_final_mul_unitSphereDiffeomorph (hk : k ≤ ∞)
    (e : E ≃ₗᵢ[ℝ] E) :
    ∃ F : E ≃ₘ^k⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E, (∀ x, ‖F x‖ = ‖x‖) ∧
      ∀ u : sphere (0 : E) 1,
        F u = ((Φ.final * e.unitSphereDiffeomorph k : Diff (𝓡 n) (sphere (0 : E) 1) k) u : E) := by
  let L : E ≃ₘ^k⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E :=
    { toEquiv := e.toLinearEquiv.toEquiv
      contMDiff_toFun := e.contDiff.contMDiff
      contMDiff_invFun := e.symm.contDiff.contMDiff }
  have hL (x : E) : L x = e x := (rfl)
  refine ⟨L.trans (Φ.radialExtension hk), fun x ↦ ?_, fun u ↦ ?_⟩
  · rw [_root_.Diffeomorph.coe_trans, Function.comp_apply, norm_radialExtension, hL,
      e.norm_map]
  · rw [_root_.Diffeomorph.coe_trans, Function.comp_apply, hL, _root_.Diffeomorph.mul_apply,
      ← e.coe_unitSphereDiffeomorph_apply (n := n) (k := n) (m := k) u,
      radialExtension_coe_sphere]

/-- **Extension over the disc.** If a diffeomorphism of the unit sphere `Sⁿ` is a linear isometry
followed by the final diffeomorphism of a `C^k` diffeotopy, `k ≤ ∞`, it is the restriction to the
boundary sphere of a `C^k` diffeomorphism of the closed unit ball `Dⁿ⁺¹`, as a manifold with
boundary. -/
theorem exists_diffeomorph_closedBall_final_mul_unitSphereDiffeomorph (hk : k ≤ ∞)
    (e : E ≃ₗᵢ[ℝ] E) :
    ∃ G : closedBall (0 : E) 1 ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ closedBall (0 : E) 1,
      ∀ u : sphere (0 : E) 1, (G ⟨u, sphere_subset_closedBall u.property⟩ : E) =
        ((Φ.final * e.unitSphereDiffeomorph k : Diff (𝓡 n) (sphere (0 : E) 1) k) u : E) := by
  obtain ⟨F, hF, hFu⟩ := Φ.exists_diffeomorph_norm_eq_final_mul_unitSphereDiffeomorph hk e
  exact ⟨F.restrictUnitClosedBall fun x ↦ by rw [hF], fun u ↦ by
    rw [_root_.Diffeomorph.coe_restrictUnitClosedBall_apply, hFu]⟩

end Diffeotopy

end TauCeti
