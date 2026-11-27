/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.AxisRotation
public import TauCeti.Topology.VectorBundle.Orientation.OrientedFrame
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Reduction.Lift
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.UnitSection
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

/-!
# The `Spinᶜ` structure of an oriented plane field

Let `E → X` be an oriented rank-three real vector bundle with fibre inner products, such as the
tangent bundle of an oriented Riemannian three-manifold, and let `R` be a continuous section of unit
vectors. Its orthogonal complement `ξ = R^⊥` is a plane field, oriented so that `(R, f₁, f₂)` is a
positively oriented frame of `E` whenever `(f₁, f₂)` is a positively oriented frame of `ξ`. This
file constructs the canonical `Spinᶜ` structure of `ξ`.

**The reduction.** Write `e₀, e₁, e₂` for the standard basis of `ℝ³`. The positively oriented
orthonormal frames `ℝ³ ≃ E x` sending `e₀` to `R x` are the frames `(R, f₁, f₂)` adapted to the
plane field. An orthogonal transformation carries such a frame to another exactly when it fixes
`e₀` and has determinant one, that is, when it is a rotation about the first axis
(`TauCeti.axisRotationGroup`). These frames are locally trivial with fibre that group
(`TauCeti.OrthonormalFrameBundle.isLocallyTrivialReduction_planeFieldFrames`): the frames adapted
to `R` are locally trivial with fibre the stabilizer `O(2)` of `e₀`
(`TauCeti.OrthonormalFrameBundle.exists_trivialization_sectionFrames`), and the reflection in the
plane orthogonal to `e₁`, which fixes `e₀`
(`TauCeti.reflection_orthogonal_singleton_mem_stabilizer`) and reverses orientation
(`TauCeti.reflection_orthogonal_singleton_notMem_specialOrthogonalGroup`), corrects a local section
into the positively oriented frames
(`TauCeti.OrthonormalFrameBundle.isLocallyTrivialReduction_inter_orientedFrames`). So they reduce
the structure group of the oriented frame bundle from `SO(3)` to `SO(2)`
(`TauCeti.OrthonormalFrameBundle.planeFieldFrameLift`).

**The `Spinᶜ` structure.** The lift `TauCeti.axisSpinCLift : SO(2) → Spinᶜ(3)` of the rotations
of the plane `⟨e₁, e₂⟩`, `exp(iθ) ↦ [exp(θ e₁e₂ / 2), exp(iθ / 2)]`, is a continuous homomorphism
lifting the inclusion `SO(2) ⊆ SO(3)`. The **`Spinᶜ` structure of the plane field**,
`TauCeti.OrthonormalFrameBundle.planeFieldSpinCStructure`, is the extension of the reduction
along this lift: its principal bundle is `P ×_{SO(2)} Spinᶜ(3)` for the adapted frames `P`, and
the frame of the point `[p, 1]` over an adapted frame `p` is `p` itself
(`TauCeti.OrthonormalFrameBundle.toFrame_planeFieldSpinCStructureInl`), so it sends `e₀` to `R`
(`TauCeti.OrthonormalFrameBundle.frameAt_planeFieldSpinCStructureInl_apply_single_zero`). The
determinant character of the lift is the angle of the rotation (`TauCeti.det_axisSpinCLift`), so
the determinant line of this structure is the line bundle associated to the adapted frames by the
rotation of `ξ`, that is `ξ` regarded as a complex line; that identification of line bundles is not
constructed here.

On a closed oriented three-manifold `Y` this is the `Spinᶜ` structure of an oriented plane field,
or of a nowhere vanishing vector field. For the mapping torus of a surface diffeomorphism, with `R`
the suspension flow and `ξ` the vertical tangent planes, its stabilization by the line `ds` is to be
compared on `S¹ × Y` with the canonical `Spinᶜ` structure of the almost complex structure sending
`∂_s` to `R`. That bundle comparison is not constructed here; at the level of structure groups it is
`OrthonormalBasis.spinCUnitary_unitaryTorusHom_mulSingle_one` together with the naturality
`CliffordAlgebra.spinCGroupMap_spinCCircle` of the plane lift.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.planeFieldFrameLift`: the positively oriented frames adapted to a
  unit section of an oriented rank-three bundle, as a lift of the orthonormal frame bundle along
  `SO(2) ⊆ SO(3)`.
* `TauCeti.OrthonormalFrameBundle.planeFieldSpinCStructure`: the `Spinᶜ` structure induced from it
  by the lift `SO(2) → Spinᶜ(3)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.isLocallyTrivialReduction_planeFieldFrames`: the adapted frames
  are a locally trivial reduction to `SO(2)`.
* `TauCeti.OrthonormalFrameBundle.toFrame_planeFieldSpinCStructureInl`,
  `TauCeti.OrthonormalFrameBundle.frameAt_planeFieldSpinCStructureInl_apply_single_zero`: the frame
  of `[p, 1]` is the adapted frame `p`, which sends `e₀` to `R`.
* `TauCeti.OrthonormalFrameBundle.planeFieldSpinCStructureInl_smul`,
  `TauCeti.OrthonormalFrameBundle.division_planeFieldSpinCStructureInl`,
  `TauCeti.OrthonormalFrameBundle.continuous_planeFieldSpinCStructureInl`: the point map
  `p ↦ [p, 1]` is equivariant along the lift, compatible with principal division, and
  continuous.

## References

* P. B. Kronheimer and T. S. Mrowka, *Monopoles and contact structures*, Inventiones
  Mathematicae 130 (1997), 209–255 (the canonical `Spinᶜ` structure of an oriented plane field).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module MulOpposite

namespace TauCeti

/-- The Euclidean space `ℝ³`. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace OrthonormalFrameBundle

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] (s : VectorBundleOrientation F E (Fin 3))
  (o : Orientation ℝ ℝ³ (Fin 3)) {R : ∀ x, E x}

/-- The positively oriented frames adapted to `R` are carried into themselves exactly by the
rotations about the first axis. -/
instance : SMulMemIff axisRotationGroup
    (sectionFrames F R (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∩ orientedFrames s o) := by
  rw [axisRotationGroup_def]
  infer_instance

/-- **The frames adapted to an oriented plane field are a locally trivial reduction to `SO(2)`.**
For a continuous section `R` of unit vectors of an oriented rank-three bundle, the positively
oriented orthonormal frames sending `e₀` to `R` are locally trivial with fibre the rotations
about the first axis, equivariantly. -/
theorem isLocallyTrivialReduction_planeFieldFrames
    (hR : Continuous fun x ↦ (⟨x, R x⟩ : TotalSpace F E)) (hR₁ : ∀ x, ‖R x‖ = 1)
    (hF : finrank ℝ F = 3) :
    IsLocallyTrivialReduction (proj : OrthonormalFrameBundle ℝ F E ℝ³ → X) axisRotationGroup
      (sectionFrames F R (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∩ orientedFrames s o) := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have hS : IsLocallyTrivialReduction (proj : OrthonormalFrameBundle ℝ F E ℝ³ → X)
      (MulAction.stabilizer _ (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
      (sectionFrames F R (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) :=
    isLocallyTrivialReduction_iff.2 fun x ↦ by
      obtain ⟨t, hxt, ht⟩ := exists_trivialization_sectionFrames (v₀ := EuclideanSpace.single 0 1)
        hR hR₁ (by simp) hF x
      exact ⟨t, hxt, fun g p hgp hp ↦ SMulMemIff.smul_eq_mk g p hgp ▸ ht g p hp⟩
  rw [axisRotationGroup_def]
  -- The reflection in the plane orthogonal to `e₁` fixes `e₀` and reverses orientation.
  exact isLocallyTrivialReduction_inter_orientedFrames s o hS
    (reflection_orthogonal_singleton_mem_stabilizer (v := EuclideanSpace.single (1 : Fin 3) 1)
      (by simp))
    (reflection_orthogonal_singleton_notMem_specialOrthogonalGroup (by simp))

variable (hR : Continuous fun x ↦ (⟨x, R x⟩ : TotalSpace F E)) (hR₁ : ∀ x, ‖R x‖ = 1)
  (hF : finrank ℝ F = 3)

/-- **The frames adapted to an oriented plane field**, as a lift of the orthonormal frame bundle
along `SO(2) ⊆ SO(3)`: for a continuous section `R` of unit vectors of an oriented rank-three
bundle, the positively oriented frames sending `e₀` to `R`, with structure group the rotations
about the first axis. This is the reduction of the structure group to `SO(2)` given by the plane
field `R^⊥`. -/
@[expose] def planeFieldFrameLift :
    OrthonormalFrameLift F E 3 axisRotationGroup
      ((euclideanLinearEquivHom ℝ (Fin 3)).comp axisRotationGroup.subtype) :=
  reductionLift (isLocallyTrivialReduction_planeFieldFrames s o hR hR₁ hF)

@[simp]
theorem planeFieldFrameLift_P :
    (planeFieldFrameLift s o hR hR₁ hF).P =
      ReductionFiber
        (sectionFrames F R (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∩ orientedFrames s o) :=
  (rfl)

/-- The frame of a point of the adapted frame bundle is that frame itself. -/
@[simp]
theorem planeFieldFrameLift_toFrame
    (p : TotalSpace axisRotationGroup (ReductionFiber
      (sectionFrames F R (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) ∩ orientedFrames s o))) :
    (planeFieldFrameLift s o hR hR₁ hF).toFrame p = ⟨p.proj, p.snd.val.frame⟩ :=
  (rfl)

/-- An adapted frame sends `e₀` to `R`. -/
@[simp]
theorem planeFieldFrameLift_frame_apply_single_zero {x : X}
    (p : (planeFieldFrameLift s o hR hR₁ hF).P x) :
    p.val.frame (EuclideanSpace.single 0 1) = R x := by
  have h := p.property.1
  rw [mem_sectionFrames_iff] at h
  exact h

/-- An adapted frame is positively oriented: it carries the orientation `o` of `ℝ³` to the
orientation of the fibre. -/
theorem orientation_map_planeFieldFrameLift_frame {x : X}
    (p : (planeFieldFrameLift s o hR hR₁ hF).P x) :
    Orientation.map (Fin 3) p.val.frame.toLinearEquiv o = s x :=
  mem_orientedFrames_iff.1 p.property.2

/-- **The `Spinᶜ` structure of an oriented plane field.** For a continuous section `R` of unit
vectors of an oriented rank-three bundle, the `Spinᶜ` structure induced from the frames adapted to
the plane field `R^⊥` (`TauCeti.OrthonormalFrameBundle.planeFieldFrameLift`) by the lift
`TauCeti.axisSpinCLift : SO(2) → Spinᶜ(3)`. Its principal bundle is `P ×_{SO(2)} Spinᶜ(3)` for the
adapted frames `P`, and the frame of `[p, 1]` is `p`. -/
@[expose] noncomputable def planeFieldSpinCStructure : SpinCStructure F E 3 :=
  (planeFieldFrameLift s o hR hR₁ hF).extendSpinC axisSpinCLift continuous_axisSpinCLift
    toSpecialOrthogonal_comp_axisSpinCLift

/-- The `Spinᶜ` structure of a plane field is the `Spinᶜ` structure induced from the adapted frames
by the lift `TauCeti.axisSpinCLift`. -/
theorem planeFieldSpinCStructure_eq :
    planeFieldSpinCStructure s o hR hR₁ hF =
      (planeFieldFrameLift s o hR hR₁ hF).extendSpinC axisSpinCLift continuous_axisSpinCLift
        toSpecialOrthogonal_comp_axisSpinCLift :=
  (rfl)

/-- The principal bundle of the `Spinᶜ` structure of a plane field is `P ×_{SO(2)} Spinᶜ(3)` for
the adapted frames `P`. -/
@[simp]
theorem planeFieldSpinCStructure_P :
    (planeFieldSpinCStructure s o hR hR₁ hF).P =
      PrincipalBundle.Extend (planeFieldFrameLift s o hR hR₁ hF).P axisSpinCLift
        continuous_axisSpinCLift :=
  (rfl)

/-- The point `[p, 1]` of the principal bundle of the `Spinᶜ` structure of a plane field over the
adapted frame `p`. -/
@[expose] noncomputable def planeFieldSpinCStructureInl {x : X}
    (p : (planeFieldFrameLift s o hR hR₁ hF).P x) :
    (planeFieldSpinCStructure s o hR hR₁ hF).P x :=
  PrincipalBundle.Extend.inl axisSpinCLift continuous_axisSpinCLift p

/-- **The frame of `[p, 1]`** in the `Spinᶜ` structure of a plane field is the adapted frame
`p`. -/
@[simp]
theorem toFrame_planeFieldSpinCStructureInl (x : X)
    (p : (planeFieldFrameLift s o hR hR₁ hF).P x) :
    (planeFieldSpinCStructure s o hR hR₁ hF).toFrame
        ⟨x, planeFieldSpinCStructureInl s o hR hR₁ hF p⟩ =
      ⟨x, p.val.frame⟩ :=
  (planeFieldFrameLift s o hR hR₁ hF).toFrame_extendSpinC_inl axisSpinCLift
    continuous_axisSpinCLift toSpecialOrthogonal_comp_axisSpinCLift x p

/-- **The frame of `E x` at `[p, 1]`** in the `Spinᶜ` structure of a plane field is the adapted
frame `p`. -/
@[simp]
theorem frameAt_planeFieldSpinCStructureInl {x : X}
    (p : (planeFieldFrameLift s o hR hR₁ hF).P x) :
    (planeFieldSpinCStructure s o hR hR₁ hF).frameAt
      (planeFieldSpinCStructureInl s o hR hR₁ hF p) = p.val.frame := by
  have h := toFrame_planeFieldSpinCStructureInl s o hR hR₁ hF x p
  rw [OrthonormalFrameLift.toFrame_mk] at h
  exact OrthonormalFrameBundle.mk_eq_mk_iff.1 h

/-- The frame of `E x` at `[p, 1]` sends `e₀` to `R x`. -/
theorem frameAt_planeFieldSpinCStructureInl_apply_single_zero {x : X}
    (p : (planeFieldFrameLift s o hR hR₁ hF).P x) :
    (planeFieldSpinCStructure s o hR hR₁ hF).frameAt
      (planeFieldSpinCStructureInl s o hR hR₁ hF p) (EuclideanSpace.single 0 1) = R x := by
  simp

/-- The map `p ↦ [p, 1]` from the total space of the adapted frame bundle to that of the principal
bundle of the `Spinᶜ` structure of the plane field is continuous. -/
theorem continuous_planeFieldSpinCStructureInl :
    Continuous fun p : TotalSpace axisRotationGroup (planeFieldFrameLift s o hR hR₁ hF).P ↦
      TotalSpace.mk'
        (spinCGroup (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero) p.proj
        (planeFieldSpinCStructureInl s o hR hR₁ hF p.snd) :=
  PrincipalBundle.Extend.continuous_inl (planeFieldFrameLift s o hR hR₁ hF).P _
    continuous_axisSpinCLift

/-- `[p • g, 1] = [p, 1] • σ(g)` for a rotation `g` about the first axis, where `σ` is the lift
`TauCeti.axisSpinCLift`. -/
theorem planeFieldSpinCStructureInl_smul {x : X} (p : (planeFieldFrameLift s o hR hR₁ hF).P x)
    (g : axisRotationGroup) :
    planeFieldSpinCStructureInl s o hR hR₁ hF (op g • p) =
      op (axisSpinCLift g) • planeFieldSpinCStructureInl s o hR hR₁ hF p :=
  PrincipalBundle.Extend.inl_smul _ continuous_axisSpinCLift p g

/-- The principal `Spinᶜ(3)`-division of `[p, 1]` and `[q, 1]` is the image under
`TauCeti.axisSpinCLift` of the principal division of the adapted frames `p` and `q`. -/
@[simp]
theorem division_planeFieldSpinCStructureInl {x : X}
    (p q : (planeFieldFrameLift s o hR hR₁ hF).P x) :
    PrincipalBundle.division
        (spinCGroup (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero)
        (planeFieldSpinCStructureInl s o hR hR₁ hF p)
        (planeFieldSpinCStructureInl s o hR hR₁ hF q) =
      axisSpinCLift (PrincipalBundle.division axisRotationGroup p q) :=
  PrincipalBundle.Extend.division_inl _ continuous_axisSpinCLift p q

end OrthonormalFrameBundle

end TauCeti
