/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.Basic
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift.Basic

/-!
# Fibre orientations induced by a lift of the orthonormal frame bundle

Let `s : TauCeti.OrthonormalFrameLift F E n G ρ` be a lift of the orthonormal frame bundle of a real
vector bundle `E → X` along `ρ : G →* GL(ℝⁿ)`, such as a Spin or `Spinᶜ` structure. A model
orientation `o` of `EuclideanSpace ℝ (Fin n)` is transported by the frame of any point of `s.P x`
to an orientation of the fibre `E x`. When `G` acts by transformations of positive determinant,
for instance through the special orthogonal group, this orientation does not depend on the point
chosen.

## Main definitions

* `TauCeti.OrthonormalFrameLift.fiberOrientation`: the fibre orientation induced by a lift of the
  orthonormal frame bundle and an orientation of `EuclideanSpace ℝ (Fin n)`.

## Main results

* `TauCeti.OrthonormalFrameLift.fiberOrientation_eq_map_frameAt`: when the structure group acts by
  transformations of positive determinant, every frame over a point carries the model orientation
  to the fibre orientation.
* `TauCeti.OrthonormalFrameLift.fiberOrientation_neg`: reversing the model orientation reverses
  every fibre orientation.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1.
-/

public section

noncomputable section

open Bundle MulOpposite

universe w

namespace TauCeti.OrthonormalFrameLift

variable {X : Type*} [TopologicalSpace X] {F : Type*} {E : X → Type w}
  [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] {n : ℕ}
  {G : Type*} [Group G] [TopologicalSpace G] {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

/-- The **orientation of the fibre `E x` induced by a lift** `s` of the orthonormal frame bundle and
a model orientation `o` of `EuclideanSpace ℝ (Fin n)`: the orientation to which the frame of a
chosen point of `s.P x` transports `o`. When `G` acts by transformations of positive determinant,
every frame `s.frameAt p` over `x` transports `o` to it
(`TauCeti.OrthonormalFrameLift.fiberOrientation_eq_map_frameAt`). -/
def fiberOrientation (s : OrthonormalFrameLift F E n G ρ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    Orientation ℝ (E x) (Fin n) :=
  Orientation.map (Fin n) (s.frameAt (Classical.arbitrary (s.P x))).toLinearEquiv o

/-- If `ρ g` has positive determinant, the frames `p` and `p • g` transport a model orientation to
the same orientation of `E x`. -/
private theorem map_frameAt_op_smul (s : OrthonormalFrameLift F E n G ρ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) {x : X} (p : s.P x) {g : G}
    (hg : 0 < (LinearEquiv.det (ρ g) : ℝ)) :
    Orientation.map (Fin n) (s.frameAt (op g • p)).toLinearEquiv o =
      Orientation.map (Fin n) (s.frameAt p).toLinearEquiv o := by
  -- In coordinates, the frame of `p • g` is the frame of `p` after the transformation `R` of `g`.
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let R : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (e.symm.trans (ρ g)).trans e
  have hR : (s.frameAt (op g • p)).toLinearEquiv = R.trans (s.frameAt p).toLinearEquiv := by
    ext v
    simpa [R, e] using s.frameAt_smul p g v.ofLp
  rw [hR, Orientation.map_trans, (o.map_eq_iff_det_pos R (by simp)).2]
  rwa [← LinearEquiv.coe_det, LinearEquiv.det_conj]

/-- If `G` acts by transformations of positive determinant, every frame `s.frameAt p` over `x`
transports `o` to `s.fiberOrientation o x`. -/
theorem fiberOrientation_eq_map_frameAt (s : OrthonormalFrameLift F E n G ρ)
    (hρ : ∀ g, 0 < (LinearEquiv.det (ρ g) : ℝ))
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) {x : X} (p : s.P x) :
    s.fiberOrientation o x = Orientation.map (Fin n) (s.frameAt p).toLinearEquiv o := by
  rw [fiberOrientation]
  -- Compare the chosen frame `p₀` with `p = p₀ • g`.
  generalize Classical.arbitrary (s.P x) = p₀
  obtain ⟨g, hg⟩ : ∃ g, PrincipalBundle.division G p₀ p = g := ⟨_, rfl⟩
  obtain rfl : op g • p₀ = p := hg ▸ PrincipalBundle.smul_division p₀ p
  rw [map_frameAt_op_smul s o p₀ (hρ g)]

/-- Reversing the model orientation reverses the induced orientation of every fibre. -/
@[simp]
theorem fiberOrientation_neg (s : OrthonormalFrameLift F E n G ρ)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    s.fiberOrientation (-o) x = -s.fiberOrientation o x := by
  simp [fiberOrientation, Orientation.map_neg]

end TauCeti.OrthonormalFrameLift
