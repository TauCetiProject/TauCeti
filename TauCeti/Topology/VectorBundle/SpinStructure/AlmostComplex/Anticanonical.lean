/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.Topology.VectorBundle.Complex.Structure
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.Determinant
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.Topology.VectorBundle.Smul

/-!
# The determinant line of the canonical `Spinᶜ` structure is the anticanonical line

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, and let `𝔰` be its canonical `Spinᶜ` structure
(`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`), built from the unitary frames `P` of
`(E, J)` and a unitary frame `e` of the model `(ℝ⁴, J₀)`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`. Its
determinant line is the line `P ×_{det_ℂ} ℂ` associated to the unitary frames by the complex
determinant (`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv`). This file identifies
it with the **anticanonical line** `K⁻¹ = Λ²_ℂ (E, J)`, the determinant line of `E` regarded as a
complex vector bundle `Jc.Fiber` through a continuous complex structure `Jc` agreeing with `J`
(`TauCeti.Bundle.ContinuousComplexStructure`, `TauCeti.DetBundle`). For an almost Hermitian
four-manifold, with `E` its tangent bundle, this is the identification `L_can ≃ K⁻¹` of the
determinant line of the canonical `Spinᶜ` structure.

A unitary frame `p` over `x` gives the basis `(p e₀, p e₂)` of the complex vector space
`(E x, J x)` (`TauCeti.OrthonormalFrameBundle.unitaryFrameBasis`), whose wedge `p e₀ ∧ p e₂`
(`TauCeti.OrthonormalFrameBundle.unitaryFrameWedge`) is a nonzero vector of `Λ²_ℂ (E x, J x)`.
Changing the frame by a unitary transformation `g` of `(ℝ⁴, J₀)` changes this basis by the unitary
matrix of `g` in the model frame `e`
(`OrthonormalBasis.coe_centralizerToUnitaryGroup_apply_eq_inner`), so it multiplies the wedge by
the complex determinant of `g` (`TauCeti.OrthonormalFrameBundle.unitaryFrameWedge_smul`), the
character defining `P ×_{det_ℂ} ℂ`. Hence `[p, w] ↦ w (p e₀ ∧ p e₂)` is a well-defined complex
linear isomorphism `P ×_{det_ℂ} ℂ ≃ Λ²_ℂ (E, J)` on every fibre
(`TauCeti.OrthonormalFrameBundle.unitaryFrameDetEquiv`). It is continuous on total spaces, because
the wedge of continuously varying frames is continuous
(`TauCeti.DetBundle.continuous_totalSpaceMk_ιMulti`). Consequently the first Chern class of the
canonical `Spinᶜ` structure is the first Chern class `c₁(E, J)` of the complex vector bundle
`(E, J)`
(`TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure_eq_firstChernClass`),
the first Chern class of its anticanonical line.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.unitaryFrameBasis`: the complex basis `(p e₀, p e₂)` of
  `(E x, J x)` given by a unitary frame `p`.
* `TauCeti.OrthonormalFrameBundle.unitaryFrameWedge`: its wedge `p e₀ ∧ p e₂` in `Λ²_ℂ (E x, J x)`.
* `TauCeti.OrthonormalFrameBundle.unitaryFrameDetEquiv`: the isomorphism
  `P ×_{det_ℂ} ℂ ≃ Λ²_ℂ (E, J)`, `[p, w] ↦ w (p e₀ ∧ p e₂)`.
* `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle`: the isomorphism of the
  determinant line of the canonical `Spinᶜ` structure with `Λ²_ℂ (E, J)`,
  `[[p, 1], w] ↦ w (p e₀ ∧ p e₂)`.

## Main results

* `TauCeti.OrthonormalFrameBundle.unitaryFrameWedge_smul`: the wedge of `p • g` is `det_ℂ g` times
  the wedge of `p`.
* `TauCeti.OrthonormalFrameBundle.continuous_unitaryFrameWedge`,
  `TauCeti.OrthonormalFrameBundle.continuous_unitaryFrameDetEquiv`,
  `TauCeti.OrthonormalFrameBundle.continuous_canonicalDeterminantLineEquivDetBundle`: continuity on
  total spaces.
* `TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure_eq_firstChernClass`:
  `c₁(𝔰) = c₁(E, J)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D
  (the canonical `Spinᶜ` structure of an almost complex manifold has determinant line `K⁻¹`).
* C. Okonek, A. Teleman, *Seiberg–Witten invariants and the Van de Ven conjecture*, 1995, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.4.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module MulOpposite

namespace TauCeti

namespace OrthonormalFrameBundle

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {J : ∀ x, E x ≃ₗᵢ[ℝ] E x}
  {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  {hJ : Continuous fun v : TotalSpace F E ↦ (⟨v.proj, J v.proj v.snd⟩ : TotalSpace F E)}
  {hJ₂ : ∀ x v, J x (J x v) = -v}
  {hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v}
  {hF : finrank ℝ F = 4} {e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4))}
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)
  {Jc : Bundle.ContinuousComplexStructure F E} (hJc : ∀ x v, Jc x v = J x v)

include hJc in
/-- A unitary frame `p` carries the model complex structure `J₀` to `Jc`. -/
private theorem almostComplexStructureAt_frame_apply {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (v : EuclideanSpace ℝ (Fin 4)) :
    Jc.almostComplexStructureAt x (p.val.frame v) =
      p.val.frame ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) := by
  rw [Bundle.ContinuousComplexStructure.almostComplexStructureAt_apply, hJc]
  exact (mk_mem_unitaryFrames_iff.1 p.property v).symm

include h₀ h₂ hJc in
/-- **The complex frame of a unitary frame.** A unitary frame `p` over `x` with values `p e₀,
p e₁, p e₂, p e₃` on the model frame `e`, `J₀ e₀ = e₁` and `J₀ e₂ = e₃`, gives the basis
`(p e₀, p e₂)` of the complex vector space `(E x, J x)`. -/
def unitaryFrameBasis {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    Basis (Fin 2) ℂ (Jc.Fiber x) :=
  AlmostComplexStructure.basisOfOrthonormalBasisFinFour (J := Jc.almostComplexStructureAt x)
    (e := e.map p.val.frame)
    (by simp [almostComplexStructureAt_frame_apply hJc, h₀])
    (by simp [almostComplexStructureAt_frame_apply hJc, h₂])

include h₀ h₂ hJc in
/-- The vectors of the complex frame of `p` are `p e₀` and `p e₂`. -/
@[simp]
theorem unitaryFrameBasis_apply {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (j : Fin 2) :
    unitaryFrameBasis h₀ h₂ hJc p j = p.val.frame (e ⟨2 * j.val, by omega⟩) := by
  fin_cases j
  · exact (AlmostComplexStructure.basisOfOrthonormalBasisFinFour_zero (V := E x)
      (J := Jc.almostComplexStructureAt x) (e := e.map p.val.frame) _ _).trans (by simp)
  · exact (AlmostComplexStructure.basisOfOrthonormalBasisFinFour_one (V := E x)
      (J := Jc.almostComplexStructureAt x) (e := e.map p.val.frame) _ _).trans (by simp)

include h₀ h₂ hJc in
/-- The `k`-th coordinate of `p v` in the complex frame of `p` is
`⟪e (2k), v⟫ + i ⟪e (2k + 1), v⟫`. -/
@[simp]
theorem unitaryFrameBasis_repr_frame_apply {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (v : EuclideanSpace ℝ (Fin 4)) (k : Fin 2) :
    (unitaryFrameBasis h₀ h₂ hJc p).repr (p.val.frame v) k =
      (inner ℝ (e ⟨2 * k.val, by omega⟩) v : ℂ) +
        Complex.I * inner ℝ (e ⟨2 * k.val + 1, by omega⟩) v := by
  fin_cases k
  · exact (AlmostComplexStructure.basisOfOrthonormalBasisFinFour_repr_apply_zero (V := E x)
      (J := Jc.almostComplexStructureAt x) (e := e.map p.val.frame) _ _ _).trans
      (by simp)
  · exact (AlmostComplexStructure.basisOfOrthonormalBasisFinFour_repr_apply_one (V := E x)
      (J := Jc.almostComplexStructureAt x) (e := e.map p.val.frame) _ _ _).trans
      (by simp)

/-- The frame of `p • g` is the frame of `p` precomposed with `g`. -/
private theorem frame_smul {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (g : Subgroup.centralizer {J₀}) (v : EuclideanSpace ℝ (Fin 4)) :
    (op g • p).val.frame v = p.val.frame (((g : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ]
      EuclideanSpace ℝ (Fin 4))) : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) :=
  Fiber.frame_smul_apply _ _ _

include h₀ h₂ hJc in
/-- **The complex frame changes by the unitary matrix of the rotation.** The matrix of the complex
frame of `p • g` in that of `p` is the unitary matrix of `g` in the model frame `e`. -/
theorem unitaryFrameBasis_toMatrix_unitaryFrameBasis_smul {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (g : Subgroup.centralizer {J₀}) :
    (unitaryFrameBasis h₀ h₂ hJc p).toMatrix (unitaryFrameBasis h₀ h₂ hJc (op g • p)) =
      (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  rw [Basis.toMatrix_apply, unitaryFrameBasis_apply, frame_smul, unitaryFrameBasis_repr_frame_apply,
    OrthonormalBasis.coe_centralizerToUnitaryGroup_apply_eq_inner]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [Fact (finrank ℝ F = 2 * finrank ℂ G)]

omit [TopologicalSpace X] [TopologicalSpace (TotalSpace F E)] in
/-- A complex model fibre of a real bundle of rank four has complex dimension two. -/
private theorem finrank_model_eq_two (hF : finrank ℝ F = 4) : finrank ℂ G = 2 := by
  have := (Fact.out : finrank ℝ F = 2 * finrank ℂ G)
  omega

include h₀ h₂ hJc in
/-- **The wedge of a unitary frame**: `p e₀ ∧ p e₂` in the complex determinant line
`Λ²_ℂ (E x, J x)`, the fibre of `TauCeti.DetBundle ℂ G Jc.Fiber` over `x`. -/
def unitaryFrameWedge {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    DetBundle ℂ G Jc.Fiber x :=
  (DetBundle.linearEquiv ℂ G Jc.Fiber x).symm (exteriorPower.ιMulti ℂ (finrank ℂ G)
    ((unitaryFrameBasis h₀ h₂ hJc p).reindex (finCongr (finrank_model_eq_two hF).symm)))

include h₀ h₂ hJc in
/-- The wedge of a unitary frame `p` is `p e₀ ∧ p e₂`, the wedge of the vectors `p (e (2i))`. -/
theorem unitaryFrameWedge_eq_ιMulti {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    unitaryFrameWedge (G := G) h₀ h₂ hJc p =
      (DetBundle.linearEquiv ℂ G Jc.Fiber x).symm (exteriorPower.ιMulti ℂ (finrank ℂ G)
        fun i ↦ (Jc.fiberEquiv x).symm (p.val.frame (e ⟨2 * i.val, by
          have := (Fact.out : finrank ℝ F = 2 * finrank ℂ G)
          omega⟩))) := by
  rw [unitaryFrameWedge]
  congr 2
  ext i
  rw [Basis.coe_reindex, Function.comp_apply, unitaryFrameBasis_apply,
    Bundle.ContinuousComplexStructure.fiberEquiv_symm_apply]
  -- The two frame indices agree, `finCongr` leaving the value of an index unchanged.
  rfl

include h₀ h₂ hJc in
/-- **The wedge of a unitary frame transforms by the complex determinant**: the wedge of `p • g`
is `det_ℂ g` times the wedge of `p`, `det_ℂ g` the determinant of the unitary matrix of `g` in the
model frame `e`. -/
theorem unitaryFrameWedge_smul {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (g : Subgroup.centralizer {J₀}) :
    unitaryFrameWedge (G := G) h₀ h₂ hJc (op g • p) =
      (Matrix.UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) : ℂ) •
        unitaryFrameWedge (G := G) h₀ h₂ hJc p := by
  set σ := finCongr (finrank_model_eq_two (G := G) hF).symm
  have hdet : ((unitaryFrameBasis h₀ h₂ hJc p).reindex σ).det
      ((unitaryFrameBasis h₀ h₂ hJc (op g • p)).reindex σ) =
        (Matrix.UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) : ℂ) := by
    rw [Basis.det_reindex, Basis.coe_reindex, Function.comp_assoc, σ.symm_comp_self,
      Function.comp_id, Basis.det_apply, unitaryFrameBasis_toMatrix_unitaryFrameBasis_smul,
      Matrix.UnitaryGroup.coe_detCircle]
  have h := congr($(AlternatingMap.eq_basis_det_smulRight
    ((unitaryFrameBasis h₀ h₂ hJc p).reindex σ) (exteriorPower.ιMulti ℂ (finrank ℂ G)))
    ((unitaryFrameBasis h₀ h₂ hJc (op g • p)).reindex σ))
  rw [AlternatingMap.smulRight_apply, hdet] at h
  rw [unitaryFrameWedge, unitaryFrameWedge, h, LinearEquiv.map_smul]

include h₀ h₂ hJc in
/-- The wedge of a unitary frame does not vanish. -/
theorem unitaryFrameWedge_ne_zero {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) :
    unitaryFrameWedge (G := G) h₀ h₂ hJc p ≠ 0 := by
  rw [unitaryFrameWedge, LinearEquiv.map_ne_zero_iff, exteriorPower.ιMulti_ne_zero_iff]
  exact Basis.linearIndependent _

include hJc in
variable (hJ hJ₂ hJ₀ hF e) in
/-- The complex linear map `[p, w] ↦ w (p e₀ ∧ p e₂)` from `P ×_{det_ℂ} ℂ` to `Λ²_ℂ (E x, J x)`,
read through an arbitrary unitary frame `p₀` (`unitaryFrameDetLinearMap_mk`). -/
private def unitaryFrameDetLinearMap (x : X) :
    AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) x
      →ₗ[ℂ] DetBundle ℂ G Jc.Fiber x :=
  let p₀ : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x := Classical.arbitrary _
  (LinearMap.toSpanSingleton ℂ _ (unitaryFrameWedge (G := G) h₀ h₂ hJc p₀)) ∘ₗ
    (SpinCStructure.LiftDeterminantModel.toComplex.toLinearEquiv.toLinearMap ∘ₗ
      (AssociatedBundle.mkContinuousLinearEquiv ℂ (Subgroup.centralizer {J₀}) p₀).symm.toLinearMap)

include hJc in
/-- The comparison read through the frame `q` sends `[p, w]` to `w (p e₀ ∧ p e₂)`. -/
private theorem unitaryFrameDetLinearMap_mk_aux {x : X}
    (q p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) :
    LinearMap.toSpanSingleton ℂ _ (unitaryFrameWedge (G := G) h₀ h₂ hJc q)
        (SpinCStructure.LiftDeterminantModel.toComplex
          ((AssociatedBundle.mkContinuousLinearEquiv ℂ (Subgroup.centralizer {J₀}) q).symm
            (AssociatedBundle.mk _ p w))) =
      SpinCStructure.LiftDeterminantModel.toComplex w • unitaryFrameWedge (G := G) h₀ h₂ hJc p := by
  have hp : op (PrincipalBundle.division (Subgroup.centralizer {J₀}) q p) • q = p :=
    PrincipalBundle.smul_division (G := Subgroup.centralizer {J₀}) q p
  rw [AssociatedBundle.mkContinuousLinearEquiv_symm_apply_mk, LinearMap.toSpanSingleton_apply,
    toComplex_smul_unitarySpinCLiftContinuousMonoidHom, mul_comm, mul_smul,
    ← unitaryFrameWedge_smul, hp]

include hJc in
/-- The comparison sends `[p, w]` to `w (p e₀ ∧ p e₂)`, in every unitary frame `p`. -/
private theorem unitaryFrameDetLinearMap_mk {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) :
    unitaryFrameDetLinearMap (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x (AssociatedBundle.mk _ p w) =
      SpinCStructure.LiftDeterminantModel.toComplex w • unitaryFrameWedge (G := G) h₀ h₂ hJc p :=
  -- By definition, `unitaryFrameDetLinearMap` applies as the left side of
  -- `unitaryFrameDetLinearMap_mk_aux` for the frame `q := Classical.arbitrary _`; unfolding it
  -- with `rw [unitaryFrameDetLinearMap]` instead exceeds the heartbeat limit.
  unitaryFrameDetLinearMap_mk_aux h₀ h₂ hJc _ p w

include hJc in
/-- The anticanonical comparison is injective: the wedge of a unitary frame does not vanish. -/
private theorem injective_unitaryFrameDetLinearMap (x : X) :
    Function.Injective (unitaryFrameDetLinearMap (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  obtain ⟨p, w, rfl⟩ := AssociatedBundle.exists_mk v
  rw [unitaryFrameDetLinearMap_mk, smul_eq_zero, LinearIsometryEquiv.map_eq_zero_iff] at hv
  rw [hv.resolve_right (unitaryFrameWedge_ne_zero h₀ h₂ hJc p), AssociatedBundle.mk_zero]

variable [FiniteDimensional ℂ G] [FiniteDimensional ℝ F]

omit [Fact (finrank ℝ F = 2 * finrank ℂ G)] [FiniteDimensional ℂ G] [FiniteDimensional ℝ F] in
/-- Evaluating unitary frames on a fixed vector is continuous on the total space of the unitary
frame bundle. -/
private theorem continuous_frame_apply (v : EuclideanSpace ℝ (Fin 4)) :
    Continuous fun p : TotalSpace (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P ↦
      TotalSpace.mk' F p.proj (p.snd.val.frame v) :=
  continuous_totalSpaceMk_frame_apply.comp
    ((unitaryFrameLift hJ hJ₂ hJ₀ hF).continuous_toFrame.prodMk continuous_const)


include h₀ h₂ hJc in
/-- **The wedge of unitary frames is continuous** on the total space of the unitary frame
bundle, with values in the total space of `Λ²_ℂ (E, J)`. -/
theorem continuous_unitaryFrameWedge :
    Continuous fun p : TotalSpace (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P ↦
      TotalSpace.mk' ℂ p.proj (unitaryFrameWedge (G := G) h₀ h₂ hJc p.snd) := by
  have := finrank_model_eq_two (G := G) hF
  simp_rw [unitaryFrameWedge_eq_ιMulti]
  refine DetBundle.continuous_totalSpaceMk_ιMulti (FiberBundle.continuous_proj _ _) fun i ↦ ?_
  refine ((Jc.totalSpaceHomeomorph G).symm.continuous.comp
    (continuous_frame_apply (e ⟨2 * i.val, by omega⟩))).congr fun p ↦ ?_
  simp [Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_symm_apply]

variable (hJ hJ₂ hJ₀ hF e)

include hJc in
/-- **The determinant line `P ×_{det_ℂ} ℂ` is the anticanonical line** `Λ²_ℂ (E, J)`, at a
fibre: the complex linear isomorphism sending `[p, w]` to `w (p e₀ ∧ p e₂)` in every unitary frame
`p` (`TauCeti.OrthonormalFrameBundle.unitaryFrameDetEquiv_mk`). -/
def unitaryFrameDetEquiv (x : X) :
    AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) x
      ≃L[ℂ] DetBundle ℂ G Jc.Fiber x :=
  haveI : FiniteDimensional ℂ (DetBundle ℂ G Jc.Fiber x) :=
    Module.finite_of_finrank_eq_succ (DetBundle.finrank_eq_one ℂ G Jc.Fiber x)
  let φ := LinearEquiv.ofBijective
    (unitaryFrameDetLinearMap (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x)
    ⟨injective_unitaryFrameDetLinearMap h₀ h₂ hJc x,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp [SpinCStructure.LiftDeterminantModel.finrank_eq_one])).1
        (injective_unitaryFrameDetLinearMap h₀ h₂ hJc x)⟩
  -- Both fibres carry their module topologies, for which linear maps are continuous.
  { φ with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap φ.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap }

variable {hJ hJ₂ hJ₀ hF e}

/-- The anticanonical comparison sends `[p, w]` to `w (p e₀ ∧ p e₂)`. -/
@[simp]
theorem unitaryFrameDetEquiv_mk {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) :
    unitaryFrameDetEquiv (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x (AssociatedBundle.mk _ p w) =
      SpinCStructure.LiftDeterminantModel.toComplex w • unitaryFrameWedge (G := G) h₀ h₂ hJc p := by
  rw [← unitaryFrameDetLinearMap_mk h₀ h₂ hJc p w]
  -- `unitaryFrameDetEquiv` is `LinearEquiv.ofBijective unitaryFrameDetLinearMap` with continuity
  -- proofs attached, so it applies as `unitaryFrameDetLinearMap` by definition; Mathlib has no
  -- rewrite lemma for the coercion of such a `ContinuousLinearEquiv` structure instance.
  rfl

/-- **The anticanonical comparison is continuous** on total spaces. -/
theorem continuous_unitaryFrameDetEquiv :
    Continuous fun v : TotalSpace
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂))
        (AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P
          (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂))) ↦
      TotalSpace.mk' ℂ v.proj
        (unitaryFrameDetEquiv (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc v.proj v.snd) := by
  refine (AssociatedBundle.isOpenQuotientMap_totalSpaceMk_mk _ _ _).isQuotientMap.continuous_iff.2
    ?_
  refine (Continuous.smul_totalSpace
    (SpinCStructure.LiftDeterminantModel.toComplex.continuous.comp continuous_snd)
    ((continuous_unitaryFrameWedge (G := G) h₀ h₂ hJc).comp continuous_fst)).congr fun q ↦ ?_
  simp [unitaryFrameDetEquiv_mk]

variable (hJ hJ₂ hJ₀ hF e)

/-- **The determinant line of the canonical `Spinᶜ` structure is the anticanonical line**
`Λ²_ℂ (E, J)`, at a fibre: the complex linear isomorphism sending `[[p, 1], w]` to
`w (p e₀ ∧ p e₂)` for every unitary frame `p`
(`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle_mk_inl`). It is continuous
on total spaces
(`TauCeti.OrthonormalFrameBundle.continuous_canonicalDeterminantLineEquivDetBundle`). -/
def canonicalDeterminantLineEquivDetBundle (x : X) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine x ≃L[ℂ]
      DetBundle ℂ G Jc.Fiber x :=
  (canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ x).trans
    (unitaryFrameDetEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x)

variable {hJ hJ₂ hJ₀ hF e}

/-- The identification of the determinant line with `Λ²_ℂ (E, J)` sends `[[p, 1], w]` to
`w (p e₀ ∧ p e₂)`. -/
@[simp]
theorem canonicalDeterminantLineEquivDetBundle_mk_inl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x) (w : SpinCStructure.DeterminantModel 4) :
    canonicalDeterminantLineEquivDetBundle (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc x
        (AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) w) =
      SpinCStructure.DeterminantModel.toComplex w • unitaryFrameWedge (G := G) h₀ h₂ hJc p := by
  simp [canonicalDeterminantLineEquivDetBundle]

/-- **The identification of the determinant line with `Λ²_ℂ (E, J)` is continuous** on total
spaces. -/
theorem continuous_canonicalDeterminantLineEquivDetBundle :
    Continuous fun v : TotalSpace (SpinCStructure.DeterminantModel 4)
        (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine ↦
      TotalSpace.mk' ℂ v.proj
        (canonicalDeterminantLineEquivDetBundle (G := G) hJ hJ₂ hJ₀ hF e h₀ h₂ hJc v.proj v.snd) :=
  ((continuous_unitaryFrameDetEquiv (G := G) h₀ h₂ hJc).comp
    (continuous_canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂)).congr fun _ ↦ (rfl)

include hJc in
/-- **The first Chern class of the canonical `Spinᶜ` structure** of a complex structure `J` is the
first Chern class `c₁(E, J)` of `E` as a complex vector bundle, that of its anticanonical line
`Λ²_ℂ (E, J)`. -/
theorem firstChernClass_canonicalSpinCStructure_eq_firstChernClass :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).firstChernClass =
      TauCeti.firstChernClass G Jc.Fiber := by
  rw [SpinCStructure.firstChernClass_def, firstChernClass_def, lineFirstChernClass_def,
    lineFirstChernClass_def]
  exact complexEulerClass_eq_of_fiberwise (finrank_self ℂ)
    (SpinCStructure.DeterminantModel.finrank_eq_one 4)
    (continuous_canonicalDeterminantLineEquivDetBundle (G := G) h₀ h₂ hJc)

end OrthonormalFrameBundle

end TauCeti
