/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.FirstChernClass
import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# The determinant line of a `Spinᶜ` structure induced by a lift

Let `s` be a lift of the orthonormal frame bundle of `E` along `ρ : G → SO(n)`, and let
`σ : G →ₜ* Spinᶜ(n)` be a continuous lift of `ρ` along the rotation homomorphism. The `Spinᶜ`
structure `s.extendSpinC σ` has principal bundle `P ×_σ Spinᶜ(n)`, so its determinant line
`(P ×_σ Spinᶜ(n)) ×_{det} ℂ` is the line bundle `P ×_{det ∘ σ} ℂ` associated to `P` by the
character `det ∘ σ` of `G`.

The model `ℂ` with `G` acting through `det ∘ σ` is `TauCeti.SpinCStructure.LiftDeterminantModel σ`.
The comparison `[[p, 1], w] ↦ [p, w]` is a fibrewise continuous linear equivalence
(`TauCeti.OrthonormalFrameLift.determinantLineExtendSpinCEquiv`), continuous on total spaces, so
the first Chern class of `s.extendSpinC σ` is that of `P ×_{det ∘ σ} ℂ`
(`TauCeti.OrthonormalFrameLift.firstChernClass_extendSpinC`).

For the unitary frames of a complex structure on a rank-four bundle and the canonical lift
`U(2) → Spinᶜ(4)`, `det ∘ σ` is the complex determinant
(`TauCeti.OrthonormalFrameBundle.toComplex_smul_canonicalDeterminantModel`).

## Main definitions

* `TauCeti.SpinCStructure.LiftDeterminantModel σ`: `ℂ` with `G` acting through `det ∘ σ` and
  `Spinᶜ(n)` through `det`.
* `TauCeti.OrthonormalFrameLift.determinantLineExtendSpinCEquiv`: the fibrewise identification of
  the determinant line of `s.extendSpinC σ` with `P ×_{det ∘ σ} ℂ`.

## Main results

* `TauCeti.OrthonormalFrameLift.determinantLineExtendSpinCEquiv_mk_inl`: the identification sends
  `[[p, 1], w]` to `[p, w]`.
* `TauCeti.OrthonormalFrameLift.continuous_determinantLineExtendSpinCEquiv`: it is continuous on
  total spaces.
* `TauCeti.OrthonormalFrameLift.firstChernClass_extendSpinC`: `c₁(s.extendSpinC σ)` is the first
  Chern class of `P ×_{det ∘ σ} ℂ`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
-/

public section

noncomputable section

open Bundle CliffordAlgebra Module

namespace TauCeti

namespace SpinCStructure

variable {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQn" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

variable {G : Type} [Group G] [TopologicalSpace G]

/-- The determinant model `ℂ` on which a group `G` acts through `det ∘ σ`, for a continuous
homomorphism `σ : G →ₜ* Spinᶜ(n)`, and `Spinᶜ(n)` acts through its determinant character as on
`TauCeti.SpinCStructure.DeterminantModel n`. -/
@[expose] def LiftDeterminantModel (_σ : G →ₜ* spinCGroup (realCliffordForm n 0) hQn) : Type :=
  DeterminantModel n

namespace LiftDeterminantModel

variable (σ : G →ₜ* spinCGroup (realCliffordForm n 0)
    (QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)))

instance instNormedAddCommGroup : NormedAddCommGroup (LiftDeterminantModel σ) :=
  inferInstanceAs (NormedAddCommGroup (DeterminantModel n))

instance instInnerProductSpace : InnerProductSpace ℂ (LiftDeterminantModel σ) :=
  inferInstanceAs (InnerProductSpace ℂ (DeterminantModel n))

instance instFiniteDimensional : FiniteDimensional ℂ (LiftDeterminantModel σ) :=
  inferInstanceAs (FiniteDimensional ℂ (DeterminantModel n))

/-- `Spinᶜ(n)` acts on the model through its determinant character. -/
instance instDistribMulActionSpinC :
    DistribMulAction (spinCGroup (realCliffordForm n 0) hQn) (LiftDeterminantModel σ) :=
  inferInstanceAs
    (DistribMulAction (spinCGroup (realCliffordForm n 0) hQn) (DeterminantModel n))

instance instContinuousSMulSpinC :
    ContinuousSMul (spinCGroup (realCliffordForm n 0) hQn) (LiftDeterminantModel σ) :=
  inferInstanceAs
    (ContinuousSMul (spinCGroup (realCliffordForm n 0) hQn) (DeterminantModel n))

instance instSMulCommClassSpinC :
    SMulCommClass (spinCGroup (realCliffordForm n 0) hQn) ℂ (LiftDeterminantModel σ) :=
  inferInstanceAs
    (SMulCommClass (spinCGroup (realCliffordForm n 0) hQn) ℂ (DeterminantModel n))

/-- `G` acts on the model through `σ`. -/
instance instDistribMulAction : DistribMulAction G (LiftDeterminantModel σ) :=
  DistribMulAction.compHom _ σ.toMonoidHom

instance instSMulCommClass : SMulCommClass G ℂ (LiftDeterminantModel σ) where
  smul_comm g c w := smul_comm (σ g) c (show DeterminantModel n from w)

instance instContinuousSMul : ContinuousSMul G (LiftDeterminantModel σ) :=
  ⟨(continuous_smul (M := spinCGroup (realCliffordForm n 0) hQn)
    (X := LiftDeterminantModel σ)).comp ((σ.continuous.comp continuous_fst).prodMk
      continuous_snd)⟩

/-- `g` acts on the model as `σ g`. -/
theorem smul_def (g : G) (w : LiftDeterminantModel σ) : g • w = σ g • w :=
  (rfl)

variable {σ}

/-- The model as `ℂ`. -/
def toComplex : LiftDeterminantModel σ ≃ₗᵢ[ℂ] ℂ := DeterminantModel.toComplex

/-- `g` acts on the model by multiplication by `det (σ g)`. -/
@[simp]
theorem toComplex_smul (g : G) (w : LiftDeterminantModel σ) :
    toComplex (g • w) = (spinCGroup.det _ hQn (σ g) : ℂ) * toComplex w :=
  DeterminantModel.toComplex_smul (σ g) w

variable (σ) in
/-- The identity of `ℂ`, from the determinant model of `Spinᶜ(n)` to the model of `σ`. -/
def ofDeterminantModel : DeterminantModel n ≃L[ℂ] LiftDeterminantModel σ :=
  ContinuousLinearEquiv.refl ℂ (DeterminantModel n)

@[simp]
theorem toComplex_ofDeterminantModel (w : DeterminantModel n) :
    toComplex (ofDeterminantModel σ w) = DeterminantModel.toComplex w :=
  (rfl)

variable (σ) in
/-- The model has complex dimension one. -/
theorem finrank_eq_one : finrank ℂ (LiftDeterminantModel σ) = 1 :=
  DeterminantModel.finrank_eq_one n

end LiftDeterminantModel

end SpinCStructure

namespace OrthonormalFrameLift

variable {n : ℕ} [NeZero n]

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQn" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)
/-- The group `Spinᶜ(n)`. -/
local notation "SpinCn" => spinCGroup (realCliffordForm n 0) hQn

variable {X : Type} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : X → Type} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {G : Type} [Group G] [TopologicalSpace G]
  {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)} (s : OrthonormalFrameLift F V n G ρ)
  (σ : G →ₜ* spinCGroup (realCliffordForm n 0)
    (QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)))
  (hσρ : ((QuadraticMap.specialOrthogonalGroup (realCliffordForm n 0)).subtype.comp
    (spinCGroup.toSpecialOrthogonal (realCliffordForm n 0) _)).comp σ.toMonoidHom = ρ)

/-- **The determinant line of the `Spinᶜ` structure induced by a lift**, at a fibre: the
determinant line `(P ×_σ Spinᶜ(n)) ×_{det} ℂ` of `s.extendSpinC σ` is identified with the line
`P ×_{det ∘ σ} ℂ` associated to `P` by the character `det ∘ σ` of `G`, by `[[p, 1], w] ↦ [p, w]`
(`TauCeti.OrthonormalFrameLift.determinantLineExtendSpinCEquiv_mk_inl`). -/
def determinantLineExtendSpinCEquiv (x : X) :
    (s.extendSpinC σ.toMonoidHom σ.continuous hσρ).determinantLine x ≃L[ℂ]
      AssociatedBundle G s.P (SpinCStructure.LiftDeterminantModel σ) x :=
  (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinCn
    (P := (s.extendSpinC σ.toMonoidHom σ.continuous hσρ).P)
    (F := SpinCStructure.DeterminantModel n) (PrincipalBundle.Extend.inl σ.toMonoidHom σ.continuous
      (Classical.arbitrary (s.P x)))).symm.trans
    ((SpinCStructure.LiftDeterminantModel.ofDeterminantModel σ).trans
      (AssociatedBundle.mkContinuousLinearEquiv ℂ G (F := SpinCStructure.LiftDeterminantModel σ)
        (Classical.arbitrary (s.P x))))

/-- The comparison of determinant lines is the identification
`PrincipalBundle.Extend.associatedEquiv` of the associated bundles of the extension. -/
private theorem determinantLineExtendSpinCEquiv_apply {x : X}
    (z : (s.extendSpinC σ.toMonoidHom σ.continuous hσρ).determinantLine x) :
    s.determinantLineExtendSpinCEquiv σ hσρ x z =
      PrincipalBundle.Extend.associatedEquiv (P := s.P)
        (F := SpinCStructure.LiftDeterminantModel σ) σ.toMonoidHom σ.continuous
        (SpinCStructure.LiftDeterminantModel.smul_def σ) x z := by
  obtain ⟨w, hw⟩ := (AssociatedBundle.mkContinuousLinearEquiv ℂ SpinCn
    (P := (s.extendSpinC σ.toMonoidHom σ.continuous hσρ).P)
    (F := SpinCStructure.DeterminantModel n) (PrincipalBundle.Extend.inl σ.toMonoidHom
      σ.continuous (Classical.arbitrary (s.P x)))).surjective z
  rw [← hw, determinantLineExtendSpinCEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply,
    AssociatedBundle.mkContinuousLinearEquiv_apply]
  erw [AssociatedBundle.mkContinuousLinearEquiv_apply]
  exact (PrincipalBundle.Extend.associatedEquiv_inl (P := s.P)
    (F := SpinCStructure.LiftDeterminantModel σ) σ.toMonoidHom σ.continuous
    (SpinCStructure.LiftDeterminantModel.smul_def σ) (Classical.arbitrary (s.P x)) w).symm

/-- The identification of determinant lines sends `[[p, 1], w]` to `[p, w]`. -/
theorem determinantLineExtendSpinCEquiv_mk_inl {x : X} (p : s.P x)
    (w : SpinCStructure.DeterminantModel n) :
    s.determinantLineExtendSpinCEquiv σ hσρ x
        (AssociatedBundle.mk SpinCn
          (PrincipalBundle.Extend.inl σ.toMonoidHom σ.continuous p) w) =
      AssociatedBundle.mk G p (SpinCStructure.LiftDeterminantModel.ofDeterminantModel σ w) := by
  rw [determinantLineExtendSpinCEquiv_apply]
  exact PrincipalBundle.Extend.associatedEquiv_inl (P := s.P)
    (F := SpinCStructure.LiftDeterminantModel σ) σ.toMonoidHom σ.continuous
    (SpinCStructure.LiftDeterminantModel.smul_def σ) p w

/-- **The identification of determinant lines is continuous** on total spaces: it is the
homeomorphism `PrincipalBundle.Extend.associatedHomeomorph` of associated bundles of the
extension. -/
theorem continuous_determinantLineExtendSpinCEquiv :
    Continuous fun v : TotalSpace (SpinCStructure.DeterminantModel n)
        (s.extendSpinC σ.toMonoidHom σ.continuous hσρ).determinantLine ↦
      TotalSpace.mk' (SpinCStructure.LiftDeterminantModel σ) v.proj
        (s.determinantLineExtendSpinCEquiv σ hσρ v.proj v.snd) :=
  (PrincipalBundle.Extend.associatedHomeomorph (P := s.P)
    (F := SpinCStructure.LiftDeterminantModel σ) σ.toMonoidHom σ.continuous
    (SpinCStructure.LiftDeterminantModel.smul_def σ)).continuous.congr fun v ↦ by
      rw [PrincipalBundle.Extend.associatedHomeomorph_apply, determinantLineExtendSpinCEquiv_apply]

/-- **The first Chern class of the `Spinᶜ` structure induced by a lift** `s` along `σ` is the
first Chern class of the line bundle `P ×_{det ∘ σ} ℂ` associated to the lift by the character
`det ∘ σ`. -/
theorem firstChernClass_extendSpinC :
    (s.extendSpinC σ.toMonoidHom σ.continuous hσρ).firstChernClass =
      lineFirstChernClass (SpinCStructure.LiftDeterminantModel σ)
        (AssociatedBundle G s.P (SpinCStructure.LiftDeterminantModel σ))
        (SpinCStructure.LiftDeterminantModel.finrank_eq_one σ) := by
  rw [SpinCStructure.firstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def]
  exact complexEulerClass_eq_of_fiberwise (SpinCStructure.LiftDeterminantModel.finrank_eq_one σ)
    (SpinCStructure.DeterminantModel.finrank_eq_one n)
    (φ := s.determinantLineExtendSpinCEquiv σ hσρ)
    (s.continuous_determinantLineExtendSpinCEquiv σ hσρ)

end OrthonormalFrameLift

end TauCeti
