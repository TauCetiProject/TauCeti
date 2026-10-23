/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Extending the puncture coordinates to the sphere

The inverses of the standard puncture coordinates extend across zero to the Riemann sphere.
At the finite punctures these maps are `w / 2` and `1 - w / 2`; at infinity the map is `2 / w`,
with zero sent to infinity. These continuous parametrisations express the power-map local
models of a filled cover in the sphere, including their centres.

The inverted coordinate uses `OnePoint.invChart`, so continuity at infinity comes from the
sphere's existing chart rather than a separate limit argument. For the same reason these maps are
holomorphic for the complex structure of the sphere (`Puncture.contMDiff_sphereCoordInv`), which is
what makes the local models of a filled cover holomorphic.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §1.5(c) and Theorem 8.4.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §1.2.7.
-/

public noncomputable section

namespace TauCeti.ThricePuncturedSphere.Puncture

open Set Topology
open scoped ContDiff Manifold OnePoint

/-- The point of the Riemann sphere corresponding to a puncture. -/
def toOnePoint : Puncture → OnePoint ℂ
  | zero => ((0 : ℂ) : OnePoint ℂ)
  | one => ((1 : ℂ) : OnePoint ℂ)
  | inf => ∞

@[simp] theorem toOnePoint_zero : zero.toOnePoint = ((0 : ℂ) : OnePoint ℂ) := (rfl)
@[simp] theorem toOnePoint_one : one.toOnePoint = ((1 : ℂ) : OnePoint ℂ) := (rfl)
@[simp] theorem toOnePoint_inf : inf.toOnePoint = (∞ : OnePoint ℂ) := (rfl)

/-- The inverse standard coordinate at a puncture, extended across zero into the sphere. -/
def sphereCoordInv : Puncture → ℂ → OnePoint ℂ
  | zero, w => ((w / 2 : ℂ) : OnePoint ℂ)
  | one, w => ((1 - w / 2 : ℂ) : OnePoint ℂ)
  | inf, w => OnePoint.invChart.symm (w / 2)

@[simp] theorem sphereCoordInv_zero (w : ℂ) :
    zero.sphereCoordInv w = ((w / 2 : ℂ) : OnePoint ℂ) := (rfl)

@[simp] theorem sphereCoordInv_one (w : ℂ) :
    one.sphereCoordInv w = ((1 - w / 2 : ℂ) : OnePoint ℂ) := (rfl)

@[simp] theorem sphereCoordInv_inf (w : ℂ) :
    inf.sphereCoordInv w = OnePoint.invChart.symm (w / 2) := (rfl)

/-- The extended inverse coordinate takes zero to its puncture. -/
@[simp] theorem sphereCoordInv_apply_zero (q : Puncture) :
    q.sphereCoordInv 0 = q.toOnePoint := by
  cases q <;> simp

/-- Each extended inverse coordinate identifies the plane with an open neighbourhood of its
puncture in the sphere. -/
theorem isOpenEmbedding_sphereCoordInv (q : Puncture) : IsOpenEmbedding q.sphereCoordInv := by
  have hd : IsOpenEmbedding (fun w : ℂ => w / 2) := by
    convert (Homeomorph.mulRight₀ ((2 : ℂ)⁻¹) (by norm_num)).isOpenEmbedding using 1
    ext w
    simp [Homeomorph.coe_mulRight₀, div_eq_mul_inv]
  cases q with
  | zero => exact OnePoint.isOpenEmbedding_coe.comp hd
  | one =>
    exact OnePoint.isOpenEmbedding_coe.comp
      ((Homeomorph.subLeft (1 : ℂ)).isOpenEmbedding.comp hd)
  | inf => exact ((OnePoint.invChart (𝕜 := ℂ)).symm.isOpenEmbedding (by simp)).comp hd

/-- The inverse puncture coordinates are continuous even at the centre. -/
@[continuity, fun_prop] theorem continuous_sphereCoordInv (q : Puncture) :
    Continuous q.sphereCoordInv :=
  q.isOpenEmbedding_sphereCoordInv.continuous

/-- The inverse puncture coordinates are holomorphic maps into the Riemann sphere, even at the
centre: at a finite puncture they are affine, and at infinity the inverse of the inverted chart of
the sphere. -/
theorem contMDiff_sphereCoordInv (q : Puncture) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω q.sphereCoordInv := by
  have hd : ContDiff ℂ ω fun w : ℂ => w / 2 := contDiff_id.div_const 2
  cases q with
  | zero => exact OnePoint.contMDiff_coe.comp hd.contMDiff
  | one => exact OnePoint.contMDiff_coe.comp (contDiff_const.sub hd).contMDiff
  | inf =>
    have h := contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω)
      (IsManifold.subset_maximalAtlas (OnePoint.mem_atlas_iff.2 (Or.inr rfl)))
    rw [OnePoint.invChart_target, contMDiffOn_univ] at h
    exact h.comp hd.contMDiff

/-- Away from the centre, the extended coordinate inverse agrees with the inclusion of the
standard punctured neighbourhood into the sphere. -/
@[simp] theorem sphereCoordInv_coord (q : Puncture) (z : q.neighborhood) :
    q.sphereCoordInv (q.coord z : ℂ) = ThricePuncturedSphere.toOnePoint z := by
  cases q with
  | zero => simp [coe_coord_zero]
  | one => simp [coe_coord_one]
  | inf =>
    rw [coe_coord_inf, sphereCoordInv_inf,
      OnePoint.invChart_symm_of_ne_zero (by
        exact div_ne_zero (div_ne_zero (by norm_num) z.1.ne_zero) (by norm_num))]
    simp [ThricePuncturedSphere.toOnePoint_apply, div_div]

end TauCeti.ThricePuncturedSphere.Puncture
