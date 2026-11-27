/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.Topology.VectorBundle.Orientation.UnitSection
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

/-!
# The `Spinᶜ` structure of an oriented plane field

Let `E → X` be an oriented rank-three vector bundle with fibre inner products, such as the tangent
bundle of an oriented Riemannian three-manifold, and let `σ` be a continuous section of unit
vectors. The planes `ξ = σ^⊥` form an oriented plane field. The positively oriented orthonormal
frames sending the last coordinate vector `e₂` of `ℝ³` to `σ` reduce the structure group of `E` to
the rotations `SO(2)` about `e₂` (`TauCeti.OrthonormalFrameBundle.orientedSectionFrameLift`). The
`Spinᶜ` structure of the plane field, `TauCeti.OrthonormalFrameBundle.planeFieldSpinCStructure`,
is the extension of this reduction along the `Spinᶜ(3)` lift of the rotations about `e₂`
(`TauCeti.axialSpinCLift`), which sends a rotation by the angle `z = exp (i θ)` to
`[exp (θ e₀ e₁ / 2), exp (i θ / 2)]`. Its principal bundle is `P ×_{SO(2)} Spinᶜ(3)` for the
adapted frames `P`, and the frame of `[p, 1]` is the adapted frame `p`
(`TauCeti.OrthonormalFrameBundle.toFrame_planeFieldSpinCStructureInl`): it sends `e₂` to `σ` and is
positively oriented. At the level of structure groups its determinant character is the rotation
angle of the plane field (`TauCeti.det_axialSpinCLift`): the determinant line is associated to the
adapted frames by the rotation angle, as is `ξ` regarded as a complex line through its
orientation; that isomorphism of line bundles is not constructed here. The construction needs
neither a surface fibration nor a symplectic form, only the unit vector field.

For a closed oriented three-manifold `Y`, a nowhere-vanishing vector field exists because the
Euler characteristic of `Y` vanishes, and this structure is the reference `Spinᶜ` structure of `Y`
used to study `S¹ × Y`. On the product, stabilizing `TY` by the trivial line of the circle factor
makes `ℝ ⊕ ξ^⊥ ⊕ ξ` an almost complex bundle, sending the circle direction to `σ`; comparing the
stabilized structure with the canonical `Spinᶜ` structure of that almost complex structure
(`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`) is not done here.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.planeFieldSpinCStructure`: the `Spinᶜ` structure of the oriented
  plane field orthogonal to a continuous unit section of an oriented rank-three bundle.

## Main results

* `TauCeti.OrthonormalFrameBundle.toFrame_planeFieldSpinCStructureInl`,
  `TauCeti.OrthonormalFrameBundle.frameAt_planeFieldSpinCStructureInl_single_two`: the frame of the
  point `[p, 1]` over an adapted frame `p` is `p`, and it sends `e₂` to `σ`.
* `TauCeti.OrthonormalFrameBundle.planeFieldSpinCStructureInl_smul`,
  `TauCeti.OrthonormalFrameBundle.division_planeFieldSpinCStructureInl` and
  `TauCeti.OrthonormalFrameBundle.continuous_planeFieldSpinCStructureInl`: the point map `[p, 1]`
  is equivariant along `TauCeti.axialSpinCLift`, compatible with principal division, and
  continuous.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module MulOpposite

namespace TauCeti

namespace OrthonormalFrameBundle

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {ι : Type*} [Fintype ι]
  [Fact (Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin 3)))]
  (s : VectorBundleOrientation F E ι) (o : Orientation ℝ (EuclideanSpace ℝ (Fin 3)) ι)
  {σ : ∀ x, E x} (hσ : Continuous fun x ↦ (⟨x, σ x⟩ : TotalSpace F E)) (hσ₁ : ∀ x, ‖σ x‖ = 1)
  (hF : finrank ℝ F = 3)

/-- **The adapted frames of an oriented plane field**: the positively oriented frames of an
oriented rank-three bundle sending `e₂` to a continuous unit section `σ`, as a lift of the
orthonormal frame bundle along the inclusion of the rotations `SO(2)` about `e₂` into `O(3)`. This
is the reduction of the structure group to `SO(2)` given by the oriented plane field `σ^⊥`. -/
@[expose] def planeFieldFrameLift :
    OrthonormalFrameLift F E 3
      (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single 2 1))
      ((euclideanLinearEquivHom ℝ (Fin 3)).comp
        (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin 3))
          (EuclideanSpace.single 2 1)).subtype) :=
  orientedSectionFrameLift s o hσ hσ₁ (by simp) (by norm_num) hF

/-- The frame of a point of the adapted frame bundle sends `e₂` to the unit section `σ`. -/
theorem planeFieldFrameLift_frame_single_two {x : X}
    (p : (planeFieldFrameLift s o hσ hσ₁ hF).P x) :
    p.val.frame (EuclideanSpace.single 2 1) = σ x :=
  (mem_orientedSectionFrames_iff.1 p.property).1

/-- The frame of a point of the adapted frame bundle is positively oriented. -/
theorem planeFieldFrameLift_mem_orientedFrames {x : X}
    (p : (planeFieldFrameLift s o hσ hσ₁ hF).P x) :
    (⟨x, p.val.frame⟩ : OrthonormalFrameBundle ℝ F E (EuclideanSpace ℝ (Fin 3))) ∈
      orientedFrames s o :=
  (mem_orientedSectionFrames_iff.1 p.property).2

/-- **The `Spinᶜ` structure of an oriented plane field.** For an oriented rank-three bundle with
fibre inner products and a continuous section `σ` of unit vectors, the extension of the bundle of
positively oriented frames sending `e₂` to `σ`
(`TauCeti.OrthonormalFrameBundle.planeFieldFrameLift`) along the `Spinᶜ(3)` lift
`TauCeti.axialSpinCLift` of the rotations about `e₂`. Its principal bundle is
`P ×_{SO(2)} Spinᶜ(3)` for these frames `P`; its determinant character on `SO(2)` is the rotation
angle of the plane field `σ^⊥` (`TauCeti.det_axialSpinCLift`). -/
@[expose] noncomputable def planeFieldSpinCStructure : SpinCStructure F E 3 :=
  (planeFieldFrameLift s o hσ hσ₁ hF).extendSpinC axialSpinCLift continuous_axialSpinCLift
    toSpecialOrthogonal_comp_axialSpinCLift

/-- The point `[p, 1]` of the principal bundle of the `Spinᶜ` structure of the plane field over
the positively oriented adapted frame `p`. -/
@[expose] noncomputable def planeFieldSpinCStructureInl {x : X}
    (p : (planeFieldFrameLift s o hσ hσ₁ hF).P x) :
    (planeFieldSpinCStructure s o hσ hσ₁ hF).P x :=
  PrincipalBundle.Extend.inl axialSpinCLift continuous_axialSpinCLift p

/-- **The frame of `[p, 1]`** in the `Spinᶜ` structure of the plane field is the adapted frame
`p`. -/
@[simp]
theorem toFrame_planeFieldSpinCStructureInl (x : X)
    (p : (planeFieldFrameLift s o hσ hσ₁ hF).P x) :
    (planeFieldSpinCStructure s o hσ hσ₁ hF).toFrame
        ⟨x, planeFieldSpinCStructureInl s o hσ hσ₁ hF p⟩ =
      ⟨x, p.val.frame⟩ :=
  (planeFieldFrameLift s o hσ hσ₁ hF).toFrame_extendSpinC_inl axialSpinCLift
    continuous_axialSpinCLift toSpecialOrthogonal_comp_axialSpinCLift x p

/-- **The frame of `E x` at `[p, 1]`** in the `Spinᶜ` structure of the plane field is the adapted
frame `p`. -/
@[simp]
theorem frameAt_planeFieldSpinCStructureInl {x : X}
    (p : (planeFieldFrameLift s o hσ hσ₁ hF).P x) :
    (planeFieldSpinCStructure s o hσ hσ₁ hF).frameAt
      (planeFieldSpinCStructureInl s o hσ hσ₁ hF p) = p.val.frame := by
  have h := toFrame_planeFieldSpinCStructureInl s o hσ hσ₁ hF x p
  rw [OrthonormalFrameLift.toFrame_mk] at h
  exact OrthonormalFrameBundle.mk_eq_mk_iff.1 h

/-- The frame of `E x` at `[p, 1]` sends the axis `e₂` to the unit section: the points `[p, 1]`
carry frames adapted to the plane field. -/
theorem frameAt_planeFieldSpinCStructureInl_single_two {x : X}
    (p : (planeFieldFrameLift s o hσ hσ₁ hF).P x) :
    (planeFieldSpinCStructure s o hσ hσ₁ hF).frameAt
      (planeFieldSpinCStructureInl s o hσ hσ₁ hF p) (EuclideanSpace.single 2 1) = σ x := by
  rw [frameAt_planeFieldSpinCStructureInl, planeFieldFrameLift_frame_single_two]

/-- The map `p ↦ [p, 1]` from the total space of the adapted frame bundle to that of the principal
bundle of the `Spinᶜ` structure of the plane field is continuous. -/
theorem continuous_planeFieldSpinCStructureInl :
    Continuous fun p : TotalSpace
        (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single 2 1))
        (planeFieldFrameLift s o hσ hσ₁ hF).P ↦
      TotalSpace.mk' (realCliffordSpinCGroupZero 3) p.proj
        (planeFieldSpinCStructureInl s o hσ hσ₁ hF p.snd) :=
  PrincipalBundle.Extend.continuous_inl (planeFieldFrameLift s o hσ hσ₁ hF).P _
    continuous_axialSpinCLift

/-- `[p • g, 1] = [p, 1] • σ(g)` for a rotation `g` about `e₂`, where `σ` is the lift
`TauCeti.axialSpinCLift`. -/
theorem planeFieldSpinCStructureInl_smul {x : X} (p : (planeFieldFrameLift s o hσ hσ₁ hF).P x)
    (g : specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single 2 1)) :
    planeFieldSpinCStructureInl s o hσ hσ₁ hF (op g • p) =
      op (axialSpinCLift g) • planeFieldSpinCStructureInl s o hσ hσ₁ hF p :=
  PrincipalBundle.Extend.inl_smul _ continuous_axialSpinCLift p g

/-- The principal `Spinᶜ(3)`-division of `[p, 1]` and `[q, 1]` is the image under
`TauCeti.axialSpinCLift` of the principal division of the adapted frames `p` and `q`. -/
@[simp]
theorem division_planeFieldSpinCStructureInl {x : X}
    (p q : (planeFieldFrameLift s o hσ hσ₁ hF).P x) :
    PrincipalBundle.division (realCliffordSpinCGroupZero 3)
        (planeFieldSpinCStructureInl s o hσ hσ₁ hF p)
        (planeFieldSpinCStructureInl s o hσ hσ₁ hF q) =
      axialSpinCLift (PrincipalBundle.division
        (specialOrthogonalStabilizer (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single 2 1)) p q) :=
  PrincipalBundle.Extend.division_inl _ continuous_axialSpinCLift p q

end OrthonormalFrameBundle

end TauCeti
