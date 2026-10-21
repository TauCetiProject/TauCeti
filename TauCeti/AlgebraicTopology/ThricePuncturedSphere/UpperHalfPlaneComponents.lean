/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.LoopAtInfinity
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
public import TauCeti.Topology.Homotopy.Monodromy.PreimageComponents

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import TauCeti.Topology.IsLocalHomeomorph

/-!
# The positive triangles of a cover of the thrice-punctured sphere

Let `p : E → ℂ ∖ {0, 1}` be a covering map whose fibre over the basepoint `1/2` is numbered by
`ν : p ⁻¹' {1/2} ≃ Fin n`. The real line cuts the sphere into two triangles with vertices `0`, `1`
and `∞`, and their preimages triangulate the compactified cover. The triangles over the open upper
half-plane `ℍ = {z | 0 < im z}` are the positive triangles of the dessin: as `ℍ` is simply
connected, each component of `p ⁻¹' ℍ` contains exactly one point over `p₊ = 1/2 + (√35/2)·i`, so
the components are numbered by the sheets. The sheet `i` goes to the component containing the
endpoint of the lift, from the point numbered `i`, of the vertical segment `αPlus` from `1/2` up to
`p₊`; this lift leaves the point numbered `i`, on the edge of the sheet `i`, into the upper side of
that edge.

These are the regions that rotate around the points over `∞`, where the edges of the dessin do not
reach: around such a point the positive triangles follow one another in the order of the cycle of
`σinf`.

## Main declarations

* `TauCeti.ThricePuncturedSphere.upperHalfPlane`: the open upper half-plane of `ℂ ∖ {0, 1}`.
* `TauCeti.ThricePuncturedSphere.isSimplyConnected_upperHalfPlane`: it is simply connected.
* `TauCeti.ThricePuncturedSphere.mem_upperHalfPlane_iff_coord_inf`: in the coordinate `z ↦ 2 / z`
  at `∞`, it is the lower half-plane.
* `IsCoveringMap.finEquivConnectedComponentsUpperHalfPlane`: the sheets are the connected components
  of `p ⁻¹' ℍ`, the sheet `i` going to the component of the end of its lift of `αPlus`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §4.2 (the triangulation of a Belyi surface by the preimages of the two half-planes).
* G. A. Jones and J. Wolfart, *Dessins d'Enfants on Riemann Surfaces*, Springer Monographs in
  Mathematics, Springer, 2016, §2.2 (the positive and negative triangles of a dessin).
-/

public section

noncomputable section

namespace TauCeti

open Set Topology

namespace ThricePuncturedSphere

/-- The open upper half-plane `{z | 0 < im z}` of the thrice-punctured sphere, whose preimages under
a cover are the positive triangles of its dessin. -/
def upperHalfPlane : Set ThricePuncturedSphere :=
  {z | 0 < (z : ℂ).im}

/-- A point lies in the upper half-plane when its imaginary part is positive. -/
@[simp]
theorem mem_upperHalfPlane {z : ThricePuncturedSphere} :
    z ∈ upperHalfPlane ↔ 0 < (z : ℂ).im :=
  Iff.rfl

/-- The upper half-plane is open. -/
theorem isOpen_upperHalfPlane : IsOpen upperHalfPlane :=
  isOpen_lt continuous_const (Complex.continuous_im.comp continuous_subtype_val)

/-- The point `p₊ = 1/2 + (√35/2)·i` lies in the upper half-plane. -/
theorem pPlus_mem_upperHalfPlane : pPlus ∈ upperHalfPlane := by
  simp

/-- In the coordinate `z ↦ 2 / z` of `D∞*`, the upper half-plane is the lower half-plane. -/
theorem mem_upperHalfPlane_iff_coord_inf (z : ThricePuncturedSphere)
    (hz : z ∈ Puncture.inf.neighborhood) :
    z ∈ upperHalfPlane ↔ (Puncture.inf.coord ⟨z, hz⟩ : ℂ).im < 0 := by
  have h : 0 < Complex.normSq (z : ℂ) := Complex.normSq_pos.2 z.ne_zero
  rw [mem_upperHalfPlane, Puncture.coe_coord_inf, Complex.div_im]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, zero_div, zero_sub, neg_lt_zero]
  exact ⟨fun hz ↦ by positivity, fun hz ↦ pos_of_mul_pos_right (div_pos_iff_of_pos_right h |>.1 hz)
    zero_le_two⟩

/-- The upper half-plane is simply connected, being a convex set of `ℂ` avoiding `0` and `1`. -/
theorem isSimplyConnected_upperHalfPlane : IsSimplyConnected upperHalfPlane := by
  have himage : ((↑) : ThricePuncturedSphere → ℂ) '' upperHalfPlane = {w : ℂ | 0 < w.im} := by
    refine (Subtype.image_preimage_coe {w : ℂ | w ≠ 0 ∧ w ≠ 1} {w : ℂ | 0 < w.im}).trans
      (inter_eq_right.2 fun w hw ↦ ⟨?_, ?_⟩) <;>
    · rintro rfl
      simp at hw
  rw [← isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image, himage]
  have := (convex_halfSpace_im_gt (0 : ℝ)).contractibleSpace ⟨Complex.I, by simp⟩
  exact SimplyConnectedSpace.ofContractible _

end ThricePuncturedSphere

open ThricePuncturedSphere

/-! ### The positive triangles are the sheets -/

variable {n : ℕ} {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}
  (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)

include hp in
/-- The preimage of the upper half-plane is locally path connected, as a cover of it. -/
private theorem locallyPathConnectedSpace_preimage_upperHalfPlane :
    LocallyPathConnectedSpace (p ⁻¹' upperHalfPlane) :=
  haveI := isOpen_upperHalfPlane.locallyPathConnectedSpace
  (hp.restrictPreimage upperHalfPlane).isLocalHomeomorph.locallyPathConnectedSpace

/-- **The positive triangles are the sheets.** The connected components of the preimage of the
upper half-plane are numbered by the sheets: since the upper half-plane is simply connected, each
component contains exactly one point of the fibre over `p₊`, and the sheet `i` goes to the
component of the endpoint of the lift of `αPlus` from the point `ν.symm i`. -/
def _root_.IsCoveringMap.finEquivConnectedComponentsUpperHalfPlane :
    Fin n ≃ ConnectedComponents (p ⁻¹' upperHalfPlane) :=
  haveI := locallyPathConnectedSpace_preimage_upperHalfPlane hp
  ((ν.symm.trans (coveringFiberEquiv hp (.mk αPlus))).trans
    (hp.fiberEquivZerothHomotopy isSimplyConnected_upperHalfPlane pPlus_mem_upperHalfPlane)).trans
    connectedComponentsEquivZerothHomotopy.symm

/-- The positive triangle of the sheet `i` is the component of the endpoint of the lift of `αPlus`
from the point numbered `i`. -/
@[simp]
theorem _root_.IsCoveringMap.finEquivConnectedComponentsUpperHalfPlane_apply (i : Fin n) :
    hp.finEquivConnectedComponentsUpperHalfPlane ν i =
      ConnectedComponents.mk ⟨hp.monodromy (.mk αPlus) (ν.symm i), by
        rw [mem_preimage, (hp.monodromy (.mk αPlus) (ν.symm i)).2]
        exact pPlus_mem_upperHalfPlane⟩ := by
  have := locallyPathConnectedSpace_preimage_upperHalfPlane hp
  rw [IsCoveringMap.finEquivConnectedComponentsUpperHalfPlane, Equiv.trans_apply,
    Equiv.trans_apply, Equiv.trans_apply, coveringFiberEquiv_apply,
    hp.fiberEquivZerothHomotopy_apply,
    connectedComponentsEquivZerothHomotopy_symm_apply]
  -- Mathlib states the last value as the quotient class `⟦x⟧`, which is
  -- `ConnectedComponents.mk x` by definition.
  rfl

end TauCeti
