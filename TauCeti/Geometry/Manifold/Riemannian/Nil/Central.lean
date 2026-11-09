/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Nil.Curvature
-- The private coordinate calculation uses Nil's model-space implementation.
import all TauCeti.Geometry.Manifold.Riemannian.Nil.Basic
import TauCeti.Analysis.Calculus.FDeriv.ConstantDirection
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Central fibres of isometries of Nil

Every Riemannian isometry of Nil carries each entire central fibre onto a central
fibre. Its action along these fibres has one global sign: increasing `z` by `t`
increases the image's `z` coordinate by `ε * t`, where `ε = ±1` is independent of
the point and the fibre. Consequently the horizontal coordinates depend only on
the horizontal coordinates of the input. These are the global constraints needed
to descend an arbitrary Nil isometry to its Euclidean base.

The central Ricci eigenspace determines the central differential up to sign.
Continuity and connectedness make that sign constant; equality of derivatives
then determines the restriction to every central line.

The coordinate calculation follows the height argument in
`TauCeti.Geometry.Manifold.Riemannian.Sol.Height`, using Mathlib's constancy theorem
for continuous maps from connected spaces into discrete subsets.

Reference: P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15
(1983), 401–487, Section 4 (Nil and its isometry group).
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace TauCeti.Nil

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)

private theorem fderiv_coordinates_apply (f : Nil → Nil) (p : Nil)
    (u : TangentSpace J p) :
    fderiv ℝ (toProd ∘ f ∘ toProd.symm) (toProd p) (tangentSpaceCastModel J p u) =
      tangentSpaceCastModel J (f p) (mfderiv J J f p u) := by
  -- Nil has the inherited model-space charts. In those charts both tangent casts
  -- are identities, and the coordinate map is the same function as the original map.
  exact congrArg (fun L => L u) (mfderiv_eq_fderiv
    (𝕜 := ℝ) (f := toProd ∘ f ∘ toProd.symm) (x := toProd p)).symm

private theorem contDiff_coordinates (Φ : Isom J Nil) :
    ContDiff ℝ ∞ (toProd ∘ Φ ∘ toProd.symm) := by
  simpa only [Diffeomorph.coe_trans, coe_toProdDiffeomorph,
    coe_toProdDiffeomorph_symm, RiemannianIsometry.coe_toDiffeomorph,
    Function.comp_assoc] using
    (toProdDiffeomorph.symm.trans (Φ.toDiffeomorph.trans toProdDiffeomorph)).contMDiff.contDiff

private theorem central_derivative (Φ : Isom J Nil) (p : P) :
    let v := fderiv ℝ (toProd ∘ Φ ∘ toProd.symm) p (0, 0, 1)
    v.1 = 0 ∧ v.2.1 = 0 ∧ (v.2.2 = 1 ∨ v.2.2 = -1) := by
  let q := toProd.symm p
  let u := (tangentSpaceCastModel J q).symm (0, 0, 1)
  have hxy := (mfderiv_central_iff Φ q u).2 (by simp [u])
  have hn := Φ.inner_mfderiv q u u
  simp only [inner_def, ← fderiv_coordinates_apply] at hn
  simp only [← fderiv_coordinates_apply] at hxy
  simp only [q, u, ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] at hn hxy
  rcases hxy with ⟨hx, hy⟩
  simp only [hx, hy, mul_zero, sub_zero, zero_add] at hn
  refine ⟨hx, hy, sq_eq_one_iff.mp ?_⟩
  nlinarith [hn]

/-- A Nil isometry sends the unit central tangent vector to itself or its negative,
with the same sign at every point. -/
theorem exists_mfderiv_central_eq (Φ : Isom J Nil) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ p : Nil,
      tangentSpaceCastModel J (Φ p)
        (mfderiv J J Φ p ((tangentSpaceCastModel J p).symm (0, 0, 1))) =
          (0, 0, ε) := by
  let a : P → ℝ := fun p => (fderiv ℝ (toProd ∘ Φ ∘ toProd.symm) p (0, 0, 1)).2.2
  have ha : Continuous a :=
    (((contDiff_coordinates Φ).continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)).snd.snd
  have hmaps : MapsTo a univ ({1, -1} : Set ℝ) := fun p _ => by
    simpa only [mem_insert_iff, mem_singleton_iff] using (central_derivative Φ p).2.2
  have hconst (p : P) : a p = a 0 :=
    isPreconnected_univ.constant_of_mapsTo (by simp : ({1, -1} : Set ℝ).Finite).isDiscrete
      ha.continuousOn hmaps (mem_univ p) (mem_univ 0)
  refine ⟨a 0, (central_derivative Φ 0).2.2, fun p => ?_⟩
  rw [← fderiv_coordinates_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  exact Prod.ext (central_derivative Φ (toProd p)).1
    (Prod.ext (central_derivative Φ (toProd p)).2.1 (hconst (toProd p)))

/-- Every Nil isometry acts affinely along all central fibres, with one common
sign `ε = ±1`. Its horizontal coordinates are constant along each fibre. -/
theorem exists_central_eq (Φ : Isom J Nil) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ (p : Nil) (t : ℝ),
      Φ (mk p.x p.y (p.z + t)) = mk (Φ p).x (Φ p).y ((Φ p).z + ε * t) := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_central_eq Φ
  refine ⟨ε, hε, fun p t => toProd.injective ?_⟩
  have hder (q : P) : fderiv ℝ (toProd ∘ Φ ∘ toProd.symm) q (0, 0, 1) = (0, 0, ε) := by
    have h := hd (toProd.symm q)
    rw [← fderiv_coordinates_apply] at h
    simpa only [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] using h
  have h := apply_add_smul_eq_of_fderiv_apply_eq
    ((contDiff_coordinates Φ).differentiable (by simp)) hder (toProd p) t
  have hq : toProd.symm (toProd p + t • ((0, 0, 1) : P)) = mk p.x p.y (p.z + t) := by
    rw [Equiv.symm_apply_eq, toProd_mk]
    ext <;> simp [fst_toProd, fst_snd_toProd, snd_snd_toProd]
  simp only [Function.comp_apply, hq, Equiv.symm_apply_apply] at h
  rw [h]
  ext <;> simp [fst_toProd, fst_snd_toProd, snd_snd_toProd, mul_comm]

/-- An isometry of Nil carries an entire central fibre onto the central fibre
through the image of any one of its points. -/
@[simp] theorem image_central_fiber (Φ : Isom J Nil) (p : Nil) :
    Φ '' {q : Nil | q.x = p.x ∧ q.y = p.y} =
      {q : Nil | q.x = (Φ p).x ∧ q.y = (Φ p).y} := by
  obtain ⟨ε, hε, hΦ⟩ := exists_central_eq Φ
  ext q
  constructor
  · rintro ⟨r, ⟨hx, hy⟩, rfl⟩
    have h := hΦ p (r.z - p.z)
    simp only [add_sub_cancel, ← hx, ← hy, mk_x_y_z] at h
    rw [h]
    simp
  · rintro ⟨hx, hy⟩
    refine ⟨mk p.x p.y (p.z + ε * (q.z - (Φ p).z)), by simp, ?_⟩
    rw [hΦ]
    apply Nil.ext <;> simp only [x_mk, y_mk, z_mk]
    · exact hx.symm
    · exact hy.symm
    · rcases hε with rfl | rfl <;> ring

end TauCeti.Nil
