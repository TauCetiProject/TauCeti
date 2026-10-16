/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Curvature
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Connected.TotallyDisconnected
-- The derivative bridge reads the inherited global model-space atlas.
import all TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic

/-!
# Vertical fibres under isometries of `SL₂ℝ~`

Every Riemannian isometry carries a vertical fibre onto a vertical fibre. On all fibres
it acts with the same sign: translation in the fibre parameter is either preserved
or reversed everywhere. Thus its two base coordinates are independent of the fibre
parameter, and its fibre coordinate is affine in that parameter with slope `±1`.

The intrinsic vertical direction is supplied by `SL2Tilde.mfderiv_vertical_iff`.
The Sasaki metric fixes the length of its image; connectedness makes the sign global.
Integrating this differential constraint gives the fibre formula. This is the global
fibre-preservation step in identifying the maximal isometry group of this geometry.
The coordinate argument follows the sign-constancy and integration argument in
`TauCeti.Geometry.Manifold.Riemannian.Sol.Height`.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4 (the geometry `SL₂ℝ~` and its isometry group).
-/

public noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)

private def coordinateMap (Φ : Isom J SL2Tilde) : P → P :=
  toProd ∘ Φ ∘ toProd.symm

private theorem contDiff_coordinateMap (Φ : Isom J SL2Tilde) :
    ContDiff ℝ ∞ (coordinateMap Φ) := by
  -- The type synonym has exactly the model-space atlas, and both coordinate
  -- equivalences are identities in that atlas.
  exact Φ.contMDiff.contDiff

private theorem coordinate_derivative (Φ : Isom J SL2Tilde) (p : SL2Tilde)
    (u : TangentSpace J p) :
    fderiv ℝ (coordinateMap Φ) (toProd p) (tangentSpaceCastModel J p u) =
      tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u) := by
  -- The inherited model-space atlas identifies the coordinate derivative and
  -- tangent casts with Mathlib's canonical normed-space derivative bridge.
  change fderiv ℝ (coordinateMap Φ) (toProd p) u =
    mfderiv J J (coordinateMap Φ) (toProd p) u
  rw [mfderiv_eq_fderiv]
  rfl

private theorem vertical_derivative_sign (Φ : Isom J SL2Tilde) (p : P) :
    (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).1 = 0 ∧
      (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.1 = 0 ∧
      ((fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 = 1 ∨
        (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 = -1) := by
  let q := toProd.symm p
  let v := constantField (0, 0, 1) q
  have hv' : tangentSpaceCastModel J q v = (0, 0, 1) := by simp [v]
  have hv : (tangentSpaceCastModel J q v).1 = 0 ∧
      (tangentSpaceCastModel J q v).2.1 = 0 := by simp [hv']
  have h := (mfderiv_vertical_iff Φ q v).mpr hv
  have hi := Φ.inner_mfderiv q v v
  rw [inner_def, inner_def] at hi
  have hs : (tangentSpaceCastModel J (Φ q) (mfderiv J J Φ q v)).2.2 ^ 2 = 1 := by
    simpa [h.1, h.2, hv', pow_two] using hi
  have he := coordinate_derivative Φ q v
  simp only [hv', q, Equiv.apply_symm_apply] at he
  rw [he]
  exact ⟨h.1, h.2, sq_eq_one_iff.mp hs⟩

private theorem vertical_derivative_sign_constant (Φ : Isom J SL2Tilde) (p : P) :
    (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 =
      (fderiv ℝ (coordinateMap Φ) 0 (0, 0, 1)).2.2 := by
  let a : P → ℝ := fun p => (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2
  have ha : Continuous a :=
    (((contDiff_coordinateMap Φ).continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)).snd.snd
  have hfinite : (range a).Finite := by
    apply (toFinite ({1, -1} : Set ℝ)).subset
    rintro _ ⟨q, rfl⟩
    exact (vertical_derivative_sign Φ q).2.2
  exact ((isPreconnected_range ha).isDiscrete_iff_subsingleton.mp hfinite.isDiscrete)
    (mem_range_self p) (mem_range_self 0)

/-- The differential of an isometry multiplies every vertical vector by a single
sign `ε = ±1` independent of the point and the vector. -/
theorem exists_mfderiv_vertical_eq (Φ : Isom J SL2Tilde) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ (p : SL2Tilde) (r : ℝ),
      tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p (constantField (0, 0, r) p)) =
        (0, 0, ε * r) := by
  refine ⟨(fderiv ℝ (coordinateMap Φ) 0 (0, 0, 1)).2.2,
    (vertical_derivative_sign Φ 0).2.2, ?_⟩
  intro p r
  rw [← coordinate_derivative]
  simp only [constantField_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hunit : fderiv ℝ (coordinateMap Φ) (toProd p) (0, 0, 1) =
      (0, 0, (fderiv ℝ (coordinateMap Φ) 0 (0, 0, 1)).2.2) :=
    Prod.ext (vertical_derivative_sign Φ (toProd p)).1
      (Prod.ext (vertical_derivative_sign Φ (toProd p)).2.1
        (vertical_derivative_sign_constant Φ (toProd p)))
  have hr : (0, 0, r) = r • ((0, 0, 1) : P) := by simp
  rw [hr, map_smul, hunit]
  simp [mul_comm]

/-- Every isometry preserves vertical fibres, either preserving their parameter
orientation everywhere or reversing it everywhere. The formula includes the translation
of each fibre and the independence of both base coordinates from the fibre parameter. -/
theorem exists_apply_vertical_eq (Φ : Isom J SL2Tilde) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ (p : SL2Tilde) (t : ℝ),
      Φ (mk p.x p.y (p.z + t)) = mk (Φ p).x (Φ p).y ((Φ p).z + ε * t) := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_vertical_eq Φ
  refine ⟨ε, hε, fun p => ?_⟩
  let c : ℝ → P := fun t => (p.x, p.y, p.z + t)
  have hc (t : ℝ) : HasDerivAt c (0, 0, 1) t := by
    simpa [c] using (hasDerivAt_const t p.x).prodMk
      ((hasDerivAt_const t p.y).prodMk ((hasDerivAt_id t).const_add p.z))
  have hf (t : ℝ) : HasDerivAt (coordinateMap Φ ∘ c) (0, 0, ε) t := by
    have h := hd (toProd.symm (c t)) 1
    rw [← coordinate_derivative] at h
    simp only [constantField_apply, ContinuousLinearEquiv.apply_symm_apply,
      Equiv.apply_symm_apply, mul_one] at h
    simpa only [h] using
      ((contDiff_coordinateMap Φ).differentiable (by simp) (c t)).hasFDerivAt.comp_hasDerivAt
        t (hc t)
  let g : ℝ → P := fun t => ((Φ p).x, (Φ p).y, (Φ p).z + ε * t)
  have hg (t : ℝ) : HasDerivAt g (0, 0, ε) t := by
    simpa [g] using (hasDerivAt_const t (Φ p).x).prodMk
      ((hasDerivAt_const t (Φ p).y).prodMk
        (((hasDerivAt_id t).const_mul ε).const_add (Φ p).z))
  have heq := eq_of_fderiv_eq (fun t => (hf t).differentiableAt)
    (fun t => (hg t).differentiableAt)
    (fun t => (hf t).hasFDerivAt.fderiv.trans (hg t).hasFDerivAt.fderiv.symm)
    0 (by
      simp only [coordinateMap, c, g, Function.comp_apply, add_zero, mul_zero]
      rw [← toProd_mk p.x p.y p.z, mk_x_y_z, Equiv.symm_apply_apply]
      exact Prod.ext (fst_toProd (Φ p))
        (Prod.ext (fst_snd_toProd (Φ p)) (snd_snd_toProd (Φ p))))
  intro t
  apply toProd.injective
  have ht := congrFun heq t
  simp only [coordinateMap, c, g, Function.comp_apply] at ht
  rw [← toProd_mk p.x p.y (p.z + t), Equiv.symm_apply_apply] at ht
  simpa only [toProd_mk] using ht

/-- The image of a whole vertical fibre is the whole fibre through the image of any
one of its points, including for isometries that reverse the fibre orientation. -/
@[simp]
theorem image_vertical_fiber (Φ : Isom J SL2Tilde) (p : SL2Tilde) :
    Φ '' {q : SL2Tilde | q.x = p.x ∧ q.y = p.y} =
      {q : SL2Tilde | q.x = (Φ p).x ∧ q.y = (Φ p).y} := by
  obtain ⟨ε, hε, hΦ⟩ := exists_apply_vertical_eq Φ
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  apply Set.Subset.antisymm
  · rintro _ ⟨q, ⟨hx, hy⟩, rfl⟩
    have hq : mk p.x p.y (p.z + (q.z - p.z)) = q := by
      simpa [hx, hy] using mk_x_y_z q
    have h := hΦ p (q.z - p.z)
    rw [hq] at h
    simp [h]
  · rintro q ⟨hx, hy⟩
    refine ⟨mk p.x p.y (p.z + ε * (q.z - (Φ p).z)), by simp, ?_⟩
    rw [hΦ]
    apply SL2Tilde.ext
    · simpa using hx.symm
    · simpa using hy.symm
    · simp [← mul_assoc, hεsq]

end TauCeti.SL2Tilde
