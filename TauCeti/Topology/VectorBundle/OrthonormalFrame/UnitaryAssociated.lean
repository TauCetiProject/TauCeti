/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.VectorBundle.Associated.Unitary
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.ComplexStructure
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass

/-!
# The complex vector bundle associated to the unitary frames

Let `E → X` be a rank-four real vector bundle with fibre inner products and a fibrewise orthogonal
complex structure `J`, continuous on the total space, such as the tangent bundle of an almost
Hermitian four-manifold. With `J` as multiplication by `i`, `E` is a complex vector bundle of rank
two, `(E, J)` (`TauCeti.OrthonormalFrameBundle.unitaryComplexStructure`, with fibres
`TauCeti.Bundle.ContinuousComplexStructure.Fiber`). Its unitary frames form a principal bundle `P`
with structure group the unitary group `U(ℝ⁴, J₀)` of a model complex structure `J₀`
(`TauCeti.OrthonormalFrameBundle.unitaryFrameLift`). This file shows that `(E, J)` is the complex
vector bundle associated to `P` by the standard representation of `U(2)`: a unitary frame `e` of
`J₀` identifies `U(ℝ⁴, J₀)` with `U(2)` (`OrthonormalBasis.centralizerToUnitaryGroup`), and

`P ×_{U(2)} ℂ² ≃ (E, J)`,  `[p, z] ↦ p (z₀ e₀ + z₁ e₂)`

as complex vector bundles (`TauCeti.OrthonormalFrameBundle.unitaryAssociatedEquiv`), where
`z₀ e₀ + z₁ e₂` is the vector of `ℝ⁴` with complex coordinates `z` in the frame `e`
(`OrthonormalBasis.complexCoords`). The map is complex linear because unitary frames carry `J₀` to
`J`, it is well defined because `U(ℝ⁴, J₀)` acts on the complex coordinates by its unitary
matrices, and it is continuous on total spaces because the total space of the associated bundle is
a quotient of `P × ℂ²` (`TauCeti.AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk`). Hence the
two bundles have the same first Chern class
(`TauCeti.OrthonormalFrameBundle.firstChernClass_associatedBundle_unitaryFrameModel`).

The model `ℂ²`, on which `U(2)` acts by its unitary matrices, is `TauCeti.UnitaryModel ρ` for
`ρ = OrthonormalBasis.centralizerToUnitaryGroupContinuousMonoidHom`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.unitaryComplexStructure`: `J` as a continuous complex structure
  on `E`.
* `TauCeti.OrthonormalFrameBundle.unitaryFrameModelEquiv`: the complex linear isomorphism
  `ℂ² ≃ (E_x, J_x)` of a unitary frame.
* `TauCeti.OrthonormalFrameBundle.unitaryAssociatedEquiv`: the fibrewise identification of the
  bundle associated to the unitary frames by `ℂ²` with `(E, J)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.unitaryAssociatedEquiv_mk`: it sends `[p, z]` to the vector
  of `E` with complex coordinates `z` in the frame `p`.
* `TauCeti.OrthonormalFrameBundle.continuous_unitaryAssociatedEquiv`: it is continuous on total
  spaces.
* `TauCeti.OrthonormalFrameBundle.firstChernClass_associatedBundle_unitaryFrameModel`: the
  associated bundle and `(E, J)` have the same first Chern class.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (associated bundles) and Chapter IX, §1 (almost complex structures as
  `GL(n; ℂ)`-structures).
-/

public section

noncomputable section

open Bundle Module MulOpposite

namespace TauCeti

namespace OrthonormalFrameBundle

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E))
  (hJ₂ : ∀ x v, J x (J x v) = -v)
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The complex vector bundle `(E, J)`**: a fibrewise orthogonal complex structure `J` on `E`,
continuous on the total space, as a continuous complex structure on `E`. -/
def unitaryComplexStructure [FiniteDimensional ℝ F] : Bundle.ContinuousComplexStructure F E :=
  .ofContinuous (fun x ↦ ((J x : E x ≃L[ℝ] E x) : E x →L[ℝ] E x)) (hJ.congr fun _ ↦ rfl) hJ₂

omit [ContinuousFiberNorm F E] in
@[simp]
theorem unitaryComplexStructure_apply [FiniteDimensional ℝ F] (x : X) (v : E x) :
    unitaryComplexStructure hJ hJ₂ x v = J x v :=
  Bundle.ContinuousComplexStructure.ofContinuous_apply _ _ hJ₂ x v

variable [Fact (finrank ℝ F = 4)]

local instance : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ 3

include h₀ h₂ in
/-- A unitary frame `p` carries multiplication by `i` on the complex coordinates of the frame `e` to
`J`: the vector with complex coordinates `i z` goes to `J` of the vector with coordinates `z`. -/
theorem frame_complexCoords_symm_I_smul {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) (z : Fin 2 → ℂ) :
    p.val.frame ((e.complexCoords 2).symm (Complex.I • z)) =
      J x (p.val.frame ((e.complexCoords 2).symm z)) := by
  have hI : (e.complexCoords 2).symm (Complex.I • z) =
      (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
        ((e.complexCoords 2).symm z) := by
    rw [LinearEquiv.symm_apply_eq, e.complexCoords_two_unitary_apply hJ₀ h₀ h₂,
      LinearEquiv.apply_symm_apply]
  rw [hI]
  exact mk_mem_unitaryFrames_iff.1 p.property _

/-- The model `ℂ²` of the unitary frames: `U(ℝ⁴, J₀)` acts on it by the unitary matrices of its
elements in the complex coordinates of the frame `e` (`OrthonormalBasis.centralizerToUnitaryGroup`).
-/
abbrev unitaryFrameModel : Type :=
  UnitaryModel (e.centralizerToUnitaryGroupContinuousMonoidHom hJ₀ h₀ h₂)

/-- The real linear isomorphism `z ↦ p (z₀ e₀ + z₁ e₂)` of a unitary frame `p`. -/
private def unitaryFrameModelEquivReal {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) :
    unitaryFrameModel hJ₀ e h₀ h₂ ≃L[ℝ] (unitaryComplexStructure hJ hJ₂).Fiber x :=
  ((UnitaryModel.coords.restrictScalars ℝ).trans
    (e.complexCoords 2).symm.toContinuousLinearEquiv).trans
      (p.val.frame.toContinuousLinearEquiv.trans
        ((unitaryComplexStructure hJ hJ₂).fiberEquiv x).symm)

private theorem fiberEquiv_unitaryFrameModelEquivReal {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) (z : unitaryFrameModel hJ₀ e h₀ h₂) :
    (unitaryComplexStructure hJ hJ₂).fiberEquiv x
        (unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p z) =
      p.val.frame ((e.complexCoords 2).symm (UnitaryModel.coords z)) := by
  simp only [unitaryFrameModelEquivReal, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  -- The remaining composite `coords.restrictScalars ℝ ≫ (e.complexCoords 2).symm` applied to `z`
  -- is `(e.complexCoords 2).symm (coords z)` by definition of `ContinuousLinearEquiv.trans`,
  -- `ContinuousLinearEquiv.restrictScalars` and `LinearEquiv.toContinuousLinearEquiv`. It is only
  -- well typed up to unfolding the type synonym `UnitaryModel`, so the coercion lemmas of these
  -- wrappers do not rewrite it.
  rfl

private theorem unitaryFrameModelEquivReal_I_smul {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) (z : unitaryFrameModel hJ₀ e h₀ h₂) :
    unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p (Complex.I • z) =
      Complex.I • unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p z := by
  apply ((unitaryComplexStructure hJ hJ₂).fiberEquiv x).injective
  rw [Bundle.ContinuousComplexStructure.fiberEquiv_I_smul, fiberEquiv_unitaryFrameModelEquivReal,
    fiberEquiv_unitaryFrameModelEquivReal, unitaryComplexStructure_apply, _root_.map_smul,
    frame_complexCoords_symm_I_smul hJ hJ₂ hJ₀ e h₀ h₂]

/-- **The complex coordinates of a unitary frame.** A unitary frame `p` of `J` over `x` identifies
`ℂ²` with the fibre of the complex vector bundle `(E, J)`, `z ↦ p (z₀ e₀ + z₁ e₂)`, where
`z₀ e₀ + z₁ e₂` is the vector of `ℝ⁴` with complex coordinates `z` in the frame `e`
(`TauCeti.OrthonormalFrameBundle.fiberEquiv_unitaryFrameModelEquiv`). It is complex linear because
`p` carries `J₀` to `J`. -/
def unitaryFrameModelEquiv {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) :
    unitaryFrameModel hJ₀ e h₀ h₂ ≃L[ℂ] (unitaryComplexStructure hJ hJ₂).Fiber x where
  toFun := unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p
  map_add' := map_add _
  map_smul' := (unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p).toLinearMap.map_smul_of_map_I_smul
    (unitaryFrameModelEquivReal_I_smul hJ hJ₂ hJ₀ e h₀ h₂ p)
  invFun := (unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p).symm
  left_inv := (unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p).symm_apply_apply
  right_inv := (unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p).apply_symm_apply
  continuous_toFun := (unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p).continuous
  continuous_invFun := (unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p).symm.continuous

/-- The unitary frame `p` sends `z` to the vector `p (z₀ e₀ + z₁ e₂)` of `E`. -/
@[simp]
theorem fiberEquiv_unitaryFrameModelEquiv {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x)
    (z : unitaryFrameModel hJ₀ e h₀ h₂) :
    (unitaryComplexStructure hJ hJ₂).fiberEquiv x (unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ p z) =
      p.val.frame ((e.complexCoords 2).symm (UnitaryModel.coords z)) :=
  fiberEquiv_unitaryFrameModelEquivReal hJ hJ₂ hJ₀ e h₀ h₂ p z

/-- **Equivariance of the complex coordinates.** The frame `p • g` sends `z` where `p` sends
`g • z`, the unitary matrix of `g` applied to `z`. -/
theorem unitaryFrameModelEquiv_smul {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x)
    (g : Subgroup.centralizer {J₀}) (z : unitaryFrameModel hJ₀ e h₀ h₂) :
    unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ (op g • p) z =
      unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ p (g • z) := by
  apply ((unitaryComplexStructure hJ hJ₂).fiberEquiv x).injective
  rw [fiberEquiv_unitaryFrameModelEquiv, fiberEquiv_unitaryFrameModelEquiv,
    UnitaryModel.coords_smul, OrthonormalBasis.centralizerToUnitaryGroupContinuousMonoidHom_apply]
  -- The action of `g` on frames precomposes with `g`, which acts on the complex coordinates of
  -- `e` by its unitary matrix.
  have hg := e.complexCoords_centralizerToUnitaryGroup_apply hJ₀ h₀ h₂ g
    ((e.complexCoords 2).symm (UnitaryModel.coords z))
  rw [LinearEquiv.apply_symm_apply, ← LinearEquiv.eq_symm_apply] at hg
  rw [← hg]
  -- `g` acts on a unitary frame as an orthogonal transformation on the underlying frame
  -- (`ReductionFiber.val_smul`), which precomposes with `g`.
  exact Fiber.frame_smul_apply (op (g : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] _))) p.val _

/-- The unitary frame chosen to read the fibres of the associated bundle. -/
private def refFrame (x : X) : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x :=
  Classical.arbitrary _

/-- **The bundle associated to the unitary frames by `ℂ²` is `(E, J)`**, at a fibre: the complex
linear isomorphism from the fibre of `P ×_{U(2)} ℂ²` over `x` to the fibre of `(E, J)` sending
`[p, z]` to `p (z₀ e₀ + z₁ e₂)` (`TauCeti.OrthonormalFrameBundle.unitaryAssociatedEquiv_mk`). -/
def unitaryAssociatedEquiv (x : X) :
    AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P
        (unitaryFrameModel hJ₀ e h₀ h₂) x ≃L[ℂ]
      (unitaryComplexStructure hJ hJ₂).Fiber x :=
  (AssociatedBundle.mkContinuousLinearEquiv ℂ _ (refFrame hJ hJ₂ hJ₀ x)).symm.trans
    (unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ (refFrame hJ hJ₂ hJ₀ x))

/-- The identification of the associated bundle with `(E, J)` sends `[p, z]` to
`p (z₀ e₀ + z₁ e₂)`. -/
@[simp]
theorem unitaryAssociatedEquiv_mk {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x)
    (z : unitaryFrameModel hJ₀ e h₀ h₂) :
    unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂ x (AssociatedBundle.mk _ p z) =
      unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ p z := by
  rw [unitaryAssociatedEquiv, ContinuousLinearEquiv.trans_apply,
    AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk, ← unitaryFrameModelEquiv_smul,
    PrincipalBundle.smul_division]

/-- The inverse identification of `(E, J)` with the associated bundle sends `p (z₀ e₀ + z₁ e₂)` to
`[p, z]`. -/
@[simp]
theorem unitaryAssociatedEquiv_symm_unitaryFrameModelEquiv {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) (z : unitaryFrameModel hJ₀ e h₀ h₂) :
    (unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂ x).symm
        (unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ p z) =
      AssociatedBundle.mk _ p z :=
  (ContinuousLinearEquiv.symm_apply_eq _).2 (unitaryAssociatedEquiv_mk hJ hJ₂ hJ₀ e h₀ h₂ p z).symm

/-- **The identification of the associated bundle with `(E, J)` is continuous** on total spaces.
-/
theorem continuous_unitaryAssociatedEquiv :
    Continuous fun v : TotalSpace (unitaryFrameModel hJ₀ e h₀ h₂)
        (AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P
          (unitaryFrameModel hJ₀ e h₀ h₂)) ↦
      TotalSpace.mk' (unitaryFrameModel hJ₀ e h₀ h₂) (E := (unitaryComplexStructure hJ hJ₂).Fiber)
        v.proj (unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂ v.proj v.snd) := by
  -- The total space of the associated bundle is the quotient of `P × ℂ²`, on which the map is
  -- `(p, z) ↦ p (z₀ e₀ + z₁ e₂)`, continuous because applying frames to vectors is.
  rw [(AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk _ _ _).isQuotientMap.continuous_iff]
  have hι : Continuous fun z : unitaryFrameModel hJ₀ e h₀ h₂ ↦
      (e.complexCoords 2).symm (UnitaryModel.coords z) :=
    (e.complexCoords 2).symm.toLinearMap.continuous_of_finiteDimensional.comp
      UnitaryModel.coords.continuous
  have h := continuous_totalSpaceMk_frame_apply.comp
    (((unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).continuous_toFrame.comp continuous_fst).prodMk
      (hι.comp continuous_snd))
  refine (((unitaryComplexStructure hJ hJ₂).totalSpaceHomeomorph
    (unitaryFrameModel hJ₀ e h₀ h₂)).symm.continuous.comp h).congr fun ⟨⟨y, p⟩, z⟩ ↦ ?_
  simp only [Function.comp_apply,
    Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply, unitaryAssociatedEquiv_mk]
  -- The frame of the point `⟨y, p⟩` of the unitary frame bundle is `p` itself.
  have hp : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).toFrame ⟨y, p⟩ = ⟨y, p.val.frame⟩ :=
    unitaryFrameLift_toFrame hJ hJ₂ hJ₀ Fact.out ⟨y, p⟩
  rw [hp]
  exact congrArg (TotalSpace.mk y) ((ContinuousLinearEquiv.symm_apply_eq _).2
    (fiberEquiv_unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ p z).symm)

/-- **The first Chern class of the unitary frames' associated bundle.** The bundle associated to
the unitary frames of `J` by `ℂ²` and the complex vector bundle `(E, J)` have the same first Chern
class. The class of `(E, J)` is taken with the model `ℂ² = Fin 2 → ℂ`, which does not depend on the
frame `e`. -/
theorem firstChernClass_associatedBundle_unitaryFrameModel :
    firstChernClass (unitaryFrameModel hJ₀ e h₀ h₂)
        (AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P
          (unitaryFrameModel hJ₀ e h₀ h₂)) =
      firstChernClass (Fin 2 → ℂ) (unitaryComplexStructure hJ hJ₂).Fiber :=
  -- `unitaryFrameModel` is the type synonym `UnitaryModel` of `Fin 2 → ℂ`, with the same normed
  -- space structure, so `(E, J)` is the same complex vector bundle for either model.
  (firstChernClass_eq_of_fiberwise (continuous_unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂)).trans
    (rfl)

end OrthonormalFrameBundle

end TauCeti
