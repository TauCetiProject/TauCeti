/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitaryLift
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.ComplexStructure
public import TauCeti.Topology.VectorBundle.SpinStructure.Basic

/-!
# The canonical `Spinᶜ` structure of a complex structure on a rank-four bundle

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, such as the tangent bundle of an almost Hermitian four-manifold.
Its unitary frames form a lift of the orthonormal frame bundle along the inclusion of the unitary
group `U(ℝ⁴, J₀)` into `SO(4)` (`TauCeti.OrthonormalFrameBundle.unitaryFrameLift`), where `J₀` is
an orthogonal complex structure on the model `ℝ⁴`. The canonical `Spinᶜ` structure of `J`,
`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`, is the extension of this lift along a
continuous homomorphism `U(ℝ⁴, J₀) → Spinᶜ(4)` lifting the inclusion along the rotation
homomorphism `Spinᶜ(4) → SO(4)`. It is defined relative to the chosen model complex structure `J₀`
and a chosen unitary frame `e` of `J₀`; independence of these choices is not established here.

The homomorphism is `TauCeti.unitarySpinCLift`, built in
`TauCeti.LinearAlgebra.CliffordAlgebra.Spin.UnitaryLift` and shown continuous in
`TauCeti.Topology.Algebra.CliffordAlgebra.Spin.UnitaryLift`. A unitary frame `e` of
`(ℝ⁴, J₀)`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`, maps `U(ℝ⁴, J₀)` homomorphically to `U(2)`
(`OrthonormalBasis.centralizerToUnitaryGroup`), and the lift `U(2) → Spinᶜ` of
`OrthonormalBasis.spinCUnitary` gives a lift `U(ℝ⁴, J₀) → Spinᶜ(Q)` for the form
`Q v = -‖v‖²` of `ℝ⁴` with the Euclidean norm (`OrthonormalBasis.centralizerSpinCLift`). The
standard basis compares `Spinᶜ(Q)` with the coordinate group `Spinᶜ(4)` of the positive-definite
form `realCliffordForm 4 0` (`OrthonormalBasis.realSpinCGroupEquiv`). The rotation of
`unitarySpinCLift g` is `g` (`TauCeti.toSpecialOrthogonal_unitarySpinCLift_apply`), and its
determinant character is the determinant of the unitary matrix of `g`, the complex determinant
(`TauCeti.det_unitarySpinCLift`). So at the level of structure groups the determinant character
of the canonical `Spinᶜ` structure is the complex determinant. Its determinant line is identified
with the anticanonical line `Λ²_ℂ (E, J)` as line bundles in
`TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.Anticanonical`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`: the canonical `Spinᶜ` structure of a
  continuous fibrewise orthogonal complex structure on a rank-four bundle, relative to a chosen
  unitary frame `e` of the model complex structure `J₀`.

## Main results

* `TauCeti.OrthonormalFrameBundle.toFrame_canonicalSpinCStructureInl`,
  `TauCeti.OrthonormalFrameBundle.frameAt_canonicalSpinCStructureInl`: the frame of the point
  `[p, 1]` (`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructureInl`) in the canonical `Spinᶜ`
  structure is the unitary frame `p`.
* `TauCeti.OrthonormalFrameBundle.canonicalSpinCStructureInl_smul`,
  `TauCeti.OrthonormalFrameBundle.division_canonicalSpinCStructureInl` and
  `TauCeti.OrthonormalFrameBundle.continuous_canonicalSpinCStructureInl`: the point map `[p, 1]`
  is equivariant along `TauCeti.unitarySpinCLift`, compatible with principal division, and
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
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
  (hJ₂ : ∀ x v, J x (J x v) = -v)
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (hF : finrank ℝ F = 4) (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The canonical `Spinᶜ` structure of a complex structure.** For a rank-four bundle with a
continuous fibrewise orthogonal complex structure `J`, the `Spinᶜ` structure induced from the
unitary frame bundle `unitaryFrameLift` by the lift `TauCeti.unitarySpinCLift` of
`U(ℝ⁴, J₀) ⊆ SO(4)` to `Spinᶜ(4)`, for a unitary frame `e` of the model complex structure `J₀`. Its
principal bundle is `P ×_σ Spinᶜ(4)` for the unitary frames `P`. The construction depends on the
chosen `J₀` and `e`; its independence of these choices is not proved here. -/
@[expose] noncomputable def canonicalSpinCStructure : SpinCStructure F E 4 :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).extendSpinC (unitarySpinCLift hJ₀ e h₀ h₂)
    (continuous_unitarySpinCLift hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)

/-- The point `[p, 1]` of the principal bundle of the canonical `Spinᶜ` structure over the unitary
frame `p`. -/
@[expose] noncomputable def canonicalSpinCStructureInl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).P x :=
  PrincipalBundle.Extend.inl (unitarySpinCLift hJ₀ e h₀ h₂)
    (continuous_unitarySpinCLift hJ₀ e h₀ h₂) p

/-- **The frame of `[p, 1]`** in the canonical `Spinᶜ` structure is the unitary frame `p`. -/
@[simp]
theorem toFrame_canonicalSpinCStructureInl (x : X) (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).toFrame
        ⟨x, canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p⟩ =
      ⟨x, p.val.frame⟩ :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).toFrame_extendSpinC_inl (unitarySpinCLift hJ₀ e h₀ h₂)
    (continuous_unitarySpinCLift hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂) x p

/-- **The frame of `E x` at `[p, 1]`** in the canonical `Spinᶜ` structure is the unitary frame
`p`. -/
@[simp]
theorem frameAt_canonicalSpinCStructureInl {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).frameAt
      (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) = p.val.frame := by
  have h := toFrame_canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ x p
  rw [OrthonormalFrameLift.toFrame_mk] at h
  exact OrthonormalFrameBundle.mk_eq_mk_iff.1 h

/-- The map `p ↦ [p, 1]` from the total space of the unitary frame bundle to that of the principal
bundle of the canonical `Spinᶜ` structure is continuous. -/
theorem continuous_canonicalSpinCStructureInl :
    Continuous fun p :
        TotalSpace (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P ↦
      TotalSpace.mk'
        (spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero) p.proj
        (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p.snd) :=
  PrincipalBundle.Extend.continuous_inl (unitaryFrameLift hJ hJ₂ hJ₀ hF).P _
    (continuous_unitarySpinCLift hJ₀ e h₀ h₂)

/-- `[p • g, 1] = [p, 1] • σ(g)` for a unitary transformation `g` of `(ℝ⁴, J₀)`, where `σ` is the
lift `TauCeti.unitarySpinCLift`. -/
theorem canonicalSpinCStructureInl_smul {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (g : Subgroup.centralizer {J₀}) :
    canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ (op g • p) =
      op (unitarySpinCLift hJ₀ e h₀ h₂ g) • canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p :=
  PrincipalBundle.Extend.inl_smul _ (continuous_unitarySpinCLift hJ₀ e h₀ h₂) p g

/-- The principal `Spinᶜ(4)`-division of `[p, 1]` and `[q, 1]` is the image under
`TauCeti.unitarySpinCLift` of the principal division of the unitary frames `p` and `q`. -/
@[simp]
theorem division_canonicalSpinCStructureInl {x : X} (p q : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    PrincipalBundle.division
        (spinCGroup (realCliffordForm 4 0) (nondegenerate_realCliffordForm 4 0).ne_zero)
        (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
        (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ q) =
      unitarySpinCLift hJ₀ e h₀ h₂
        (PrincipalBundle.division (Subgroup.centralizer {J₀}) p q) :=
  PrincipalBundle.Extend.division_inl _ (continuous_unitarySpinCLift hJ₀ e h₀ h₂) p q

end OrthonormalFrameBundle

end TauCeti
