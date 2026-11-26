/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Determinant
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.UnitaryAssociated
public import TauCeti.Topology.VectorBundle.SpinStructure.AlmostComplex.Basic
public import TauCeti.Topology.VectorBundle.SpinStructure.ExtendDeterminant

/-!
# The determinant line of the canonical `Spinᶜ` structure of a complex structure

Let `E → X` be a rank-four real vector bundle with fibre inner products and a continuous fibrewise
orthogonal complex structure `J`, and let `𝔰` be its canonical `Spinᶜ` structure
(`TauCeti.OrthonormalFrameBundle.canonicalSpinCStructure`), the extension of the unitary frame
bundle `P` along the lift `σ : U(ℝ⁴, J₀) → Spinᶜ(4)` (`TauCeti.unitarySpinCLift`, bundled as the
continuous homomorphism `TauCeti.unitarySpinCLiftContinuousMonoidHom`) for a unitary frame `e` of
the model complex structure `J₀`.

The determinant character of `σ` is the complex determinant (`TauCeti.det_unitarySpinCLift`), so
the determinant line of `𝔰` is the line bundle `P ×_{det_ℂ} ℂ` associated to the unitary frames by
the complex determinant of the unitary matrix in the frame `e`
(`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv`, with the action computed in
`TauCeti.toComplex_smul_unitarySpinCLiftContinuousMonoidHom`), and the first Chern class of `𝔰`
is that of this line bundle
(`TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure`).

**The anticanonical line.** With `J` as multiplication by `i`, `E` is a complex vector bundle of
rank two, `(E, J)` (`TauCeti.OrthonormalFrameBundle.unitaryComplexStructure`), associated to `P` by
`ℂ²` (`TauCeti.OrthonormalFrameBundle.unitaryAssociatedEquiv`). The complex determinant of `ℂ²`
transforms under `U(2)` by the character `det_ℂ`, so it identifies the top complex exterior power
of `P ×_{U(2)} ℂ²` with `P ×_{det_ℂ} ℂ` (`TauCeti.AssociatedBundle.detHomeomorph`). Composing, the
determinant line of the canonical `Spinᶜ` structure is the anticanonical line `Λ²_ℂ (E, J)`, the
dual of the canonical line `K = Λ^(2,0) E*`
(`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle`): in a unitary frame `p`
it sends `[[p, 1], w]` to `w (p e₀ ∧ p e₂)`
(`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle_mk_inl`). Hence the first
Chern class of the canonical `Spinᶜ` structure is the first Chern class of `(E, J)`, the negative
of the canonical class
(`TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure_eq_firstChernClass`). These
statements take the rank as an instance `Fact (finrank ℝ F = 4)`, under which `(E, J)` is a complex
vector bundle with model `ℂ²`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv`: the fibrewise identification of
  the determinant line of the canonical `Spinᶜ` structure with `P ×_{det_ℂ} ℂ`.
* `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle`: the fibrewise
  identification of the determinant line of the canonical `Spinᶜ` structure with `Λ²_ℂ (E, J)`.

## Main results

* `TauCeti.toComplex_smul_unitarySpinCLiftContinuousMonoidHom`: a unitary transformation `g` of
  `(ℝ⁴, J₀)` acts on the model of `P ×_{det_ℂ} ℂ` by the determinant of its unitary matrix in the
  frame `e`.
* `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv_mk_inl` and
  `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv_symm_mk`: the identification sends
  `[[p, 1], w]` to `[p, w]`.
* `TauCeti.OrthonormalFrameBundle.continuous_canonicalDeterminantLineEquiv`: it is continuous on
  total spaces.
* `TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure`: the first Chern class
  of the canonical `Spinᶜ` structure is that of `P ×_{det_ℂ} ℂ`.
* `TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquivDetBundle_mk_inl` and
  `TauCeti.OrthonormalFrameBundle.continuous_canonicalDeterminantLineEquivDetBundle`: the
  identification with `Λ²_ℂ (E, J)` sends `[[p, 1], w]` to `w (p e₀ ∧ p e₂)` and is continuous on
  total spaces.
* `TauCeti.OrthonormalFrameBundle.firstChernClass_canonicalSpinCStructure_eq_firstChernClass`:
  the first Chern class of the canonical `Spinᶜ` structure is the first Chern class of `(E, J)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1` and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832, §5 (the canonical
  `Spinᶜ` structure of a Kähler surface, with determinant line `K⁻¹`).
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module

namespace TauCeti

section

variable {J₀ : unitary (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))}
  (hJ₀ : ∀ v, (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    ((J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) v) = -v)
  (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The determinant character of the canonical lift is the complex determinant**: a unitary
transformation `g` of `(ℝ⁴, J₀)` acts on the model of `P ×_{det_ℂ} ℂ` by the determinant of its
unitary matrix in the frame `e`. -/
theorem toComplex_smul_unitarySpinCLiftContinuousMonoidHom (g : Subgroup.centralizer {J₀})
    (w : SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) :
    SpinCStructure.LiftDeterminantModel.toComplex (g • w) =
      (Matrix.UnitaryGroup.detCircle (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g) : ℂ) *
        SpinCStructure.LiftDeterminantModel.toComplex w := by
  rw [SpinCStructure.LiftDeterminantModel.toComplex_smul, unitarySpinCLiftContinuousMonoidHom_apply,
    det_unitarySpinCLift]

end

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
  (hF : finrank ℝ F = 4) (e : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)))
  (h₀ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 0) = e 1)
  (h₂ : (J₀ : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4)) (e 2) = e 3)

/-- **The determinant line of the canonical `Spinᶜ` structure**, at a fibre: it is identified with
the line `P ×_{det_ℂ} ℂ` associated to the unitary frames `P` by the complex determinant, by
`[[p, 1], w] ↦ [p, w]` (`TauCeti.OrthonormalFrameBundle.canonicalDeterminantLineEquiv_mk_inl`). -/
def canonicalDeterminantLineEquiv (x : X) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine x ≃L[ℂ]
      AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) x :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).determinantLineExtendSpinCEquiv
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)
    x

/-- The identification of determinant lines sends `[[p, 1], w]` to `[p, w]`. -/
@[simp]
theorem canonicalDeterminantLineEquiv_mk_inl {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : SpinCStructure.DeterminantModel 4) :
    canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ x
        (AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p) w) =
      AssociatedBundle.mk _ p (SpinCStructure.LiftDeterminantModel.ofDeterminantModel
        (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂) w) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).determinantLineExtendSpinCEquiv_mk_inl
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)
    p w

/-- The inverse identification of determinant lines sends `[p, w]` to `[[p, 1], w]`. -/
@[simp]
theorem canonicalDeterminantLineEquiv_symm_mk {x : X} (p : (unitaryFrameLift hJ hJ₂ hJ₀ hF).P x)
    (w : SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)) :
    (canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ x).symm (AssociatedBundle.mk _ p w) =
      AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ hF e h₀ h₂ p)
        ((SpinCStructure.LiftDeterminantModel.ofDeterminantModel
          (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)).symm w) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).determinantLineExtendSpinCEquiv_symm_mk
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)
    p w

/-- **The identification of determinant lines is continuous** on total spaces. -/
theorem continuous_canonicalDeterminantLineEquiv :
    Continuous fun v : TotalSpace (SpinCStructure.DeterminantModel 4)
        (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).determinantLine ↦
      TotalSpace.mk'
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂))
        v.proj (canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ hF e h₀ h₂ v.proj v.snd) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).continuous_determinantLineExtendSpinCEquiv
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)

/-- **The first Chern class of the canonical `Spinᶜ` structure** of a complex structure is the
first Chern class of the line bundle `P ×_{det_ℂ} ℂ` associated to the unitary frames by the
complex determinant. -/
theorem firstChernClass_canonicalSpinCStructure :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ hF e h₀ h₂).firstChernClass =
      lineFirstChernClass
        (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂))
        (AssociatedBundle (Subgroup.centralizer {J₀}) (unitaryFrameLift hJ hJ₂ hJ₀ hF).P
          (SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)))
        (SpinCStructure.LiftDeterminantModel.finrank_eq_one _) :=
  (unitaryFrameLift hJ hJ₂ hJ₀ hF).firstChernClass_extendSpinC
    (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    (toSpecialOrthogonal_comp_unitarySpinCLift hJ₀ e h₀ h₂)

/-! ### The anticanonical line -/

section Anticanonical

variable [Fact (finrank ℝ F = 4)]

local instance : FiniteDimensional ℝ F := .of_fact_finrank_eq_succ 3

/-- The model `ℂ²` of the unitary frames has complex dimension two. -/
private theorem finrank_unitaryFrameModel : finrank ℂ (unitaryFrameModel hJ₀ e h₀ h₂) = 2 :=
  UnitaryModel.finrank_eq _

/-- The complex determinant `(z, w) ↦ z₀ w₁ - z₁ w₀` on the model `ℂ²` of the unitary frames, with
values in the model of `P ×_{det_ℂ} ℂ`. -/
private def detForm :
    unitaryFrameModel hJ₀ e h₀ h₂ [⋀^Fin 2]→ₗ[ℂ]
      SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂) :=
  (SpinCStructure.LiftDeterminantModel.toComplex.symm.toLinearEquiv.toLinearMap :
      ℂ →ₗ[ℂ] SpinCStructure.LiftDeterminantModel (unitarySpinCLiftContinuousMonoidHom hJ₀ e h₀ h₂)
    ).compAlternatingMap
    (Matrix.detRowAlternating.compLinearMap UnitaryModel.coords.toLinearEquiv.toLinearMap)

private theorem toComplex_detForm (v : Fin 2 → unitaryFrameModel hJ₀ e h₀ h₂) :
    SpinCStructure.LiftDeterminantModel.toComplex (detForm hJ₀ e h₀ h₂ v) =
      (Matrix.of fun i ↦ UnitaryModel.coords (v i)).det := by
  simp only [detForm, LinearMap.compAlternatingMap_apply, AlternatingMap.compLinearMap_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
  -- `Matrix.det` is `Matrix.detRowAlternating` applied to the rows.
  rfl

/-- The complex determinant is equivariant: a unitary transformation multiplies it by the
determinant of its unitary matrix, as on the model of `P ×_{det_ℂ} ℂ`. -/
private theorem detForm_smul (g : Subgroup.centralizer {J₀})
    (v : Fin 2 → unitaryFrameModel hJ₀ e h₀ h₂) :
    detForm hJ₀ e h₀ h₂ (fun i ↦ g • v i) = g • detForm hJ₀ e h₀ h₂ v := by
  apply SpinCStructure.LiftDeterminantModel.toComplex.injective
  rw [toComplex_smul_unitarySpinCLiftContinuousMonoidHom, toComplex_detForm, toComplex_detForm,
    Matrix.UnitaryGroup.coe_detCircle]
  simp only [UnitaryModel.coords_smul,
    OrthonormalBasis.centralizerToUnitaryGroupContinuousMonoidHom_apply]
  -- The rows `U *ᵥ v i` form the matrix `V Uᵀ`, of determinant `det U det V`.
  have hrows : (Matrix.of fun i ↦ (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g :
      Matrix (Fin 2) (Fin 2) ℂ).mulVec (UnitaryModel.coords (v i))) =
      (Matrix.of fun i ↦ UnitaryModel.coords (v i)) *
        (e.centralizerToUnitaryGroup hJ₀ h₀ h₂ g : Matrix (Fin 2) (Fin 2) ℂ).transpose := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [hrows, Matrix.det_mul, Matrix.det_transpose, mul_comm]

/-- The complex determinant of the standard basis of the model `ℂ²` is `1`. -/
private theorem toComplex_detForm_std :
    SpinCStructure.LiftDeterminantModel.toComplex (detForm hJ₀ e h₀ h₂ fun i ↦
      (UnitaryModel.coords.symm (Pi.single i 1) : unitaryFrameModel hJ₀ e h₀ h₂)) = 1 := by
  rw [toComplex_detForm]
  have h1 : (Matrix.of fun i : Fin 2 ↦ UnitaryModel.coords
      (UnitaryModel.coords.symm (Pi.single i 1) : unitaryFrameModel hJ₀ e h₀ h₂)) = 1 := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h1, Matrix.det_one]

private theorem detForm_ne_zero : detForm hJ₀ e h₀ h₂ ≠ 0 := fun h ↦ by
  simpa [h] using toComplex_detForm_std hJ₀ e h₀ h₂

/-- **The determinant line of the canonical `Spinᶜ` structure is the anticanonical line**, at a
fibre: the determinant line `L` of the canonical `Spinᶜ` structure of `J` is identified with the top
complex exterior power `Λ²_ℂ (E, J)` of the complex vector bundle `(E, J)`, the dual of the
canonical line `K = Λ^(2,0) E*`. It sends `[[p, 1], w]` to `w (p e₀ ∧ p e₂)`, where `p e₀, p e₂`
is the complex basis of `(E, J)` given by the unitary frame `p`. -/
def canonicalDeterminantLineEquivDetBundle (x : X) :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ Fact.out e h₀ h₂).determinantLine x ≃L[ℂ]
      DetBundle ℂ (unitaryFrameModel hJ₀ e h₀ h₂) (unitaryComplexStructure hJ hJ₂).Fiber x :=
  ((canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ Fact.out e h₀ h₂ x).trans
    (AssociatedBundle.detEquiv _ _ (finrank_unitaryFrameModel hJ₀ e h₀ h₂)
      (SpinCStructure.LiftDeterminantModel.finrank_eq_one _) (detForm_ne_zero hJ₀ e h₀ h₂)
      x).symm.toContinuousLinearEquivOfIsModuleTopology).trans
    (DetBundle.congrEquiv (unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂) x)

/-- The identification of the determinant line with the anticanonical line is the composite of
the identification with `P ×_{det_ℂ} ℂ`, the inverse of the determinant of `P ×_{U(2)} ℂ²`, and
the determinant of the identification of `P ×_{U(2)} ℂ²` with `(E, J)`. -/
private theorem canonicalDeterminantLineEquivDetBundle_apply (x : X)
    (v : (canonicalSpinCStructure hJ hJ₂ hJ₀ Fact.out e h₀ h₂).determinantLine x) :
    canonicalDeterminantLineEquivDetBundle hJ hJ₂ hJ₀ e h₀ h₂ x v =
      DetBundle.congrEquiv (unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂) x
        ((AssociatedBundle.detEquiv _ _ (finrank_unitaryFrameModel hJ₀ e h₀ h₂)
          (SpinCStructure.LiftDeterminantModel.finrank_eq_one _) (detForm_ne_zero hJ₀ e h₀ h₂)
          x).symm (canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ Fact.out e h₀ h₂ x v)) := by
  -- Unfold by `delta`: generating the equation lemma of this composite times out.
  delta canonicalDeterminantLineEquivDetBundle
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]

/-- **The determinant line as the anticanonical line in a unitary frame.** The identification sends
`[[p, 1], w]` to `w (p e₀ ∧ p e₂)`, where `p e₀` and `p e₂` are the images under the unitary frame
`p` of the standard basis of `ℂ²`
(`TauCeti.OrthonormalFrameBundle.fiberEquiv_unitaryFrameModelEquiv`), a complex basis of the fibre
of `(E, J)`. -/
@[simp]
theorem canonicalDeterminantLineEquivDetBundle_mk_inl {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) (w : SpinCStructure.DeterminantModel 4) :
    canonicalDeterminantLineEquivDetBundle hJ hJ₂ hJ₀ e h₀ h₂ x
        (AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ Fact.out e h₀ h₂ p) w) =
      SpinCStructure.DeterminantModel.toComplex w •
        exteriorPower.ιMulti ℂ (finrank ℂ (unitaryFrameModel hJ₀ e h₀ h₂)) fun i ↦
          unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ p
            (UnitaryModel.coords.symm (Pi.single (Fin.cast (UnitaryModel.finrank_eq _) i) 1)) := by
  set std : Fin 2 → unitaryFrameModel hJ₀ e h₀ h₂ := fun i ↦
    UnitaryModel.coords.symm (Pi.single i 1)
  -- The class `w` of the determinant model is `w` times the determinant of the standard basis.
  have hw : SpinCStructure.LiftDeterminantModel.ofDeterminantModel _ w =
      SpinCStructure.DeterminantModel.toComplex w • detForm hJ₀ e h₀ h₂ std := by
    apply SpinCStructure.LiftDeterminantModel.toComplex.injective
    rw [SpinCStructure.LiftDeterminantModel.toComplex_ofDeterminantModel,
      LinearIsometryEquiv.map_smul, toComplex_detForm_std, smul_eq_mul, mul_one]
  rw [canonicalDeterminantLineEquivDetBundle_apply, canonicalDeterminantLineEquiv_mk_inl, hw,
    AssociatedBundle.mk_smul_scalar, LinearEquiv.map_smul, ContinuousLinearEquiv.map_smul,
    AssociatedBundle.detEquiv_symm_mk _ _ (detForm_smul hJ₀ e h₀ h₂)]
  congr 1
  -- The fibres of determinant lines are the top exterior powers, on which `congrEquiv` is the
  -- exterior power of the identification `unitaryAssociatedEquiv`.
  refine (DetBundle.congrEquiv_apply _ x _).trans
    ((LinearEquiv.exteriorPower_apply_ιMulti _ _ _).trans ?_)
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_toLinearEquiv, unitaryAssociatedEquiv_mk,
    std]

/-- The inverse identification of the anticanonical line with the determinant line sends
`w (p e₀ ∧ p e₂)` to `[[p, 1], w]`. -/
@[simp]
theorem canonicalDeterminantLineEquivDetBundle_symm_smul_ιMulti {x : X}
    (p : (unitaryFrameLift hJ hJ₂ hJ₀ Fact.out).P x) (w : SpinCStructure.DeterminantModel 4) :
    (canonicalDeterminantLineEquivDetBundle hJ hJ₂ hJ₀ e h₀ h₂ x).symm
        (SpinCStructure.DeterminantModel.toComplex w •
          exteriorPower.ιMulti ℂ (finrank ℂ (unitaryFrameModel hJ₀ e h₀ h₂)) fun i ↦
            unitaryFrameModelEquiv hJ hJ₂ hJ₀ e h₀ h₂ p
              (UnitaryModel.coords.symm (Pi.single (Fin.cast (UnitaryModel.finrank_eq _) i) 1))) =
      AssociatedBundle.mk _ (canonicalSpinCStructureInl hJ hJ₂ hJ₀ Fact.out e h₀ h₂ p) w :=
  (ContinuousLinearEquiv.symm_apply_eq _).2
    (canonicalDeterminantLineEquivDetBundle_mk_inl hJ hJ₂ hJ₀ e h₀ h₂ p w).symm

/-- **The identification of the determinant line with the anticanonical line is continuous** on
total spaces. -/
theorem continuous_canonicalDeterminantLineEquivDetBundle :
    Continuous fun v : TotalSpace (SpinCStructure.DeterminantModel 4)
        (canonicalSpinCStructure hJ hJ₂ hJ₀ Fact.out e h₀ h₂).determinantLine ↦
      TotalSpace.mk' ℂ
        (E := DetBundle ℂ (unitaryFrameModel hJ₀ e h₀ h₂) (unitaryComplexStructure hJ hJ₂).Fiber)
        v.proj (canonicalDeterminantLineEquivDetBundle hJ hJ₂ hJ₀ e h₀ h₂ v.proj v.snd) := by
  refine ((DetBundle.congrHomeomorph _
    (continuous_unitaryAssociatedEquiv hJ hJ₂ hJ₀ e h₀ h₂)).continuous.comp
      ((AssociatedBundle.detHomeomorph _ _ (finrank_unitaryFrameModel hJ₀ e h₀ h₂)
        (SpinCStructure.LiftDeterminantModel.finrank_eq_one _) (detForm_smul hJ₀ e h₀ h₂)
        (detForm_ne_zero hJ₀ e h₀ h₂)).symm.continuous.comp
          (continuous_canonicalDeterminantLineEquiv hJ hJ₂ hJ₀ Fact.out e h₀ h₂))).congr
      fun v ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, AssociatedBundle.detHomeomorph_symm_apply,
    DetBundle.congrHomeomorph_apply, canonicalDeterminantLineEquivDetBundle_apply]

/-- **The first Chern class of the canonical `Spinᶜ` structure is that of `(E, J)`**:
`c₁(L) = c₁(Λ²_ℂ (E, J)) = c₁(E, J)`, minus the canonical class. -/
theorem firstChernClass_canonicalSpinCStructure_eq_firstChernClass :
    (canonicalSpinCStructure hJ hJ₂ hJ₀ Fact.out e h₀ h₂).firstChernClass =
      firstChernClass (unitaryFrameModel hJ₀ e h₀ h₂) (unitaryComplexStructure hJ hJ₂).Fiber := by
  rw [SpinCStructure.firstChernClass_def, firstChernClass_def, lineFirstChernClass_def,
    lineFirstChernClass_def]
  exact complexEulerClass_eq_of_fiberwise (finrank_self ℂ)
    (SpinCStructure.DeterminantModel.finrank_eq_one 4)
    (continuous_canonicalDeterminantLineEquivDetBundle hJ hJ₂ hJ₀ e h₀ h₂)

end Anticanonical

end OrthonormalFrameBundle

end TauCeti
