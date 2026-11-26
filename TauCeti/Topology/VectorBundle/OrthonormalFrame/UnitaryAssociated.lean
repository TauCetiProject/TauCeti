/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.Topology.VectorBundle.Associated.Basic
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.ComplexStructure
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
import Mathlib.Topology.Instances.Matrix

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

The model `ℂⁿ` with a group acting through unitary matrices is
`TauCeti.UnitaryModel ρ`, for a continuous homomorphism `ρ : G →ₜ* U(n)`.

## Main definitions

* `TauCeti.UnitaryModel ρ`: the space `ℂⁿ` on which `G` acts by the unitary matrices `ρ g`.
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
open scoped Matrix

namespace TauCeti

/-! ### The model `ℂⁿ` of a unitary representation -/

section UnitaryModel

variable {G : Type*} [Group G] [TopologicalSpace G] {n : ℕ}

/-- The space `ℂⁿ` of complex coordinates, on which a topological group `G` acts through a
continuous homomorphism `ρ : G →ₜ* U(n)` into the unitary matrices, `g • z = ρ g *ᵥ z`
(`TauCeti.UnitaryModel.coords_smul`). It is the model fibre of the complex vector bundles
associated to principal `G`-bundles by `ρ`. -/
@[expose] def UnitaryModel (_ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ) : Type := Fin n → ℂ

namespace UnitaryModel

variable (ρ : G →ₜ* Matrix.unitaryGroup (Fin n) ℂ)

instance instNormedAddCommGroup : NormedAddCommGroup (UnitaryModel ρ) :=
  inferInstanceAs (NormedAddCommGroup (Fin n → ℂ))

instance instNormedSpace : NormedSpace ℂ (UnitaryModel ρ) :=
  inferInstanceAs (NormedSpace ℂ (Fin n → ℂ))

instance instFiniteDimensional : FiniteDimensional ℂ (UnitaryModel ρ) :=
  inferInstanceAs (FiniteDimensional ℂ (Fin n → ℂ))

/-- `G` acts on the model by the unitary matrices `ρ g`. -/
instance instDistribMulAction : DistribMulAction G (UnitaryModel ρ) where
  smul g z := (ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ (show Fin n → ℂ from z)
  one_smul z := by
    change (ρ 1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ (show Fin n → ℂ from z) = z
    rw [map_one, Matrix.UnitaryGroup.one_val, Matrix.one_mulVec]
  mul_smul g h z := by
    change (ρ (g * h) : Matrix (Fin n) (Fin n) ℂ) *ᵥ (show Fin n → ℂ from z) =
      (ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ ((ρ h : Matrix (Fin n) (Fin n) ℂ) *ᵥ
        (show Fin n → ℂ from z))
    rw [map_mul, Matrix.UnitaryGroup.mul_val, Matrix.mulVec_mulVec]
  smul_zero g := Matrix.mulVec_zero _
  smul_add g z w := Matrix.mulVec_add _ (show Fin n → ℂ from z) (show Fin n → ℂ from w)

variable {ρ} in
/-- The model as `ℂⁿ`. -/
def coords : UnitaryModel ρ ≃L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearEquiv.refl ℂ (Fin n → ℂ)

/-- `g` acts on the coordinates by the unitary matrix `ρ g`. -/
@[simp]
theorem coords_smul (g : G) (z : UnitaryModel ρ) :
    coords (g • z) = (ρ g : Matrix (Fin n) (Fin n) ℂ) *ᵥ coords z :=
  (rfl)

instance instSMulCommClass : SMulCommClass G ℂ (UnitaryModel ρ) where
  smul_comm g c z := coords.injective <| by
    rw [coords_smul, map_smul, map_smul, coords_smul, Matrix.mulVec_smul]

instance instContinuousSMul : ContinuousSMul G (UnitaryModel ρ) where
  continuous_smul :=
    (((continuous_subtypeVal.comp ρ.continuous).comp continuous_fst).matrix_mulVec
      continuous_snd).congr fun _ ↦ (rfl)

/-- The model has complex dimension `n`. -/
theorem finrank_eq : finrank ℂ (UnitaryModel ρ) = n :=
  coords.toLinearEquiv.finrank_eq.trans (finrank_fin_fun ℂ)

end UnitaryModel

end UnitaryModel

/-- A real vector space of dimension four has twice the complex dimension of the model `ℂ²`, the
dimension condition under which a continuous complex structure on a real bundle with that model
fibre is a complex vector bundle with model `ℂ²`. -/
instance UnitaryModel.instFactFinrank {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : G →ₜ* Matrix.unitaryGroup (Fin 2) ℂ} {F : Type*} [AddCommGroup F] [Module ℝ F]
    [Fact (finrank ℝ F = 4)] : Fact (finrank ℝ F = 2 * finrank ℂ (UnitaryModel ρ)) :=
  ⟨by rw [UnitaryModel.finrank_eq ρ, (Fact.out : finrank ℝ F = 4)]⟩

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
  let J₀' : AlmostComplexStructure (EuclideanSpace ℝ (Fin 4)) :=
    ⟨(J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)).toLinearMap,
      LinearMap.ext fun v ↦ by simpa using hJ₀ v⟩
  have hI : (e.complexCoords 2).symm (Complex.I • z) =
      (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
        ((e.complexCoords 2).symm z) := by
    have h := OrthonormalBasis.complexCoords_two_almostComplexStructure_apply (J := J₀') h₀ h₂
      ((e.complexCoords 2).symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [LinearEquiv.symm_apply_eq]
    exact h.symm
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
  rfl

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
class. -/
theorem firstChernClass_associatedBundle_unitaryFrameModel :
    firstChernClass (unitaryFrameModel hJ₀ e h₀ h₂)
        (AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P
          (unitaryFrameModel hJ₀ e h₀ h₂)) =
      firstChernClass (unitaryFrameModel hJ₀ e h₀ h₂) (unitaryComplexStructure hJ hJ₂).Fiber :=
  firstChernClass_eq_of_fiberwise (continuous_unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂)

end OrthonormalFrameBundle

end TauCeti
