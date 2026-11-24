/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.SpinStructure.FirstChernClass
public import TauCeti.Topology.VectorBundle.SpinStructure.OfSpin
public import TauCeti.Topology.VectorBundle.SpinStructure.Reflection
import TauCeti.Topology.VectorBundle.Orientation.Complex.FiberwiseEquiv

/-!
# Determinant lines under Spin structures and orientation reversal

The first Chern class `c₁(𝔰)` of a `Spinᶜ` structure `𝔰` is that of its determinant line
`L = P ×_{det} ℂ` (`TauCeti.SpinCStructure.firstChernClass`). This file compares determinant lines
in two situations.

* **Spin structures.** The `Spinᶜ` structure `s.toSpinC` induced by a Spin structure `s` has
  determinant line with the nowhere-vanishing continuous section `x ↦ [[p, 1], 1]`
  (`TauCeti.SpinStructure.determinantLineSection`), so `c₁(s.toSpinC) = 0`
  (`TauCeti.SpinStructure.firstChernClass_toSpinC`).
* **Orientation changes.** The `Spinᶜ` structure `𝔰.precompIsometry f`, whose frames are those of
  `𝔰` precomposed with an isometry `f` of `ℝⁿ`, has principal bundle `P ×_σ Spinᶜ(n)` for the
  automorphism `σ : [g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)`. Since `det ∘ σ = det`, the map
  `[p, z] ↦ [[p, 1], z]` is a well-defined continuous fibrewise isomorphism of determinant lines,
  so `c₁(𝔰.precompIsometry f) = c₁(𝔰)` (`TauCeti.SpinCStructure.firstChernClass_precompIsometry`).
  In particular the orientation reversal has the same first Chern class
  (`TauCeti.SpinCStructure.firstChernClass_reverse`).

## Main results

* `TauCeti.SpinStructure.firstChernClass_toSpinC`: `c₁(s.toSpinC) = 0`.
* `TauCeti.SpinCStructure.firstChernClass_precompIsometry`: `c₁(𝔰.precompIsometry f) = c₁(𝔰)`.
* `TauCeti.SpinCStructure.firstChernClass_reverse`: `c₁(𝔰.reverse) = c₁(𝔰)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open Bundle MulOpposite CliffordAlgebra

namespace TauCeti

variable {X : Type} [TopologicalSpace X] {F : Type*} {E : X → Type}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiberBundle F E]
  [VectorBundle ℝ F E] {n : ℕ} [NeZero n]

/-- **The determinant class of a Spin structure vanishes**: the `Spinᶜ` structure induced by a
Spin structure has first Chern class `0`, since its determinant line has the nowhere-vanishing
continuous section `x ↦ [[p, 1], 1]` (`TauCeti.SpinStructure.determinantLineSection`). -/
@[simp]
theorem SpinStructure.firstChernClass_toSpinC (s : SpinStructure F E n) :
    s.toSpinC.firstChernClass = 0 := by
  rw [SpinCStructure.firstChernClass_def, lineFirstChernClass_def]
  exact complexEulerClass_eq_zero_of_forall_ne_zero _ _ _ s.continuous_determinantLineSection
    s.determinantLineSection_ne_zero

namespace SpinCStructure

/-- The proof that the standard form on `ℝⁿ`, `n ≥ 1`, is nonzero, on which `Spinᶜ(n)` depends. -/
local notation "hQ" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm n 0)

variable (f : (realCliffordForm n 0).IsometryEquiv (realCliffordForm n 0))
  (s : SpinCStructure F E n)

/-- The automorphism `σ : [g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)` does not change the action on the
determinant model, since `det ∘ σ = det`. -/
private theorem precompIsometryHom_smul (g : spinCGroup (realCliffordForm n 0) hQ)
    (w : DeterminantModel n) : g • w = precompIsometryHom f g • w :=
  DeterminantModel.toComplex.injective (by
    rw [DeterminantModel.toComplex_smul, DeterminantModel.toComplex_smul,
      QuadraticMap.Isometry.det_spinCGroupMap])

/-- The comparison `[p, z] ↦ [[p, 1], z]` from the determinant line of `s` to that of
`s.precompIsometry f`, at a fibre. -/
private def determinantLinePrecompEquiv (x : X) :
    s.determinantLine x ≃L[ℂ] (s.precompIsometry f).determinantLine x :=
  (AssociatedBundle.mkContinuousLinearEquiv ℂ _ (Classical.arbitrary (s.P x))).symm.trans
    (AssociatedBundle.mkContinuousLinearEquiv ℂ _ (PrincipalBundle.Extend.inl
      (precompIsometryHom f) (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ)
      (Classical.arbitrary (s.P x))))

/-- The comparison of determinant lines is the inverse of the identification
`PrincipalBundle.Extend.associatedEquiv` of associated bundles of an extended principal bundle. -/
private theorem determinantLinePrecompEquiv_apply {x : X} (z : s.determinantLine x) :
    determinantLinePrecompEquiv f s x z = (PrincipalBundle.Extend.associatedEquiv
      (precompIsometryHom f) (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ)
      (precompIsometryHom_smul f) x).symm z := by
  obtain ⟨w, rfl⟩ := (AssociatedBundle.mkContinuousLinearEquiv ℂ _ (F := DeterminantModel n)
    (Classical.arbitrary (s.P x))).surjective z
  rw [determinantLinePrecompEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply, AssociatedBundle.mkContinuousLinearEquiv_apply]
  exact (AssociatedBundle.mkContinuousLinearEquiv_apply _ _).trans
    (PrincipalBundle.Extend.associatedEquiv_symm_mk (precompIsometryHom f)
    (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ) (precompIsometryHom_smul f) (P := s.P)
    (Classical.arbitrary (s.P x)) w).symm

/-- **The first Chern class is unchanged by precomposing with an isometry**: for an isometry `f`
of `ℝⁿ`, `c₁(s.precompIsometry f) = c₁(s)`. The automorphism `[g, z] ↦ [f⁻¹ g, z]` of `Spinᶜ(n)`
through which `s.precompIsometry f` is built preserves the determinant character, so
`[p, z] ↦ [[p, 1], z]` is a continuous fibrewise isomorphism of determinant lines. -/
@[simp]
theorem firstChernClass_precompIsometry :
    (s.precompIsometry f).firstChernClass = s.firstChernClass := by
  rw [firstChernClass_def, firstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def]
  refine (complexEulerClass_eq_of_fiberwise (DeterminantModel.finrank_eq_one n)
    (DeterminantModel.finrank_eq_one n) (φ := determinantLinePrecompEquiv f s) ?_).symm
  refine (PrincipalBundle.Extend.associatedHomeomorph (P := s.P) (precompIsometryHom f)
    (f.symm.toIsometry.continuous_spinCGroupMap hQ hQ)
    (precompIsometryHom_smul f)).symm.continuous.congr fun z ↦ ?_
  rw [PrincipalBundle.Extend.associatedHomeomorph_symm_apply, determinantLinePrecompEquiv_apply]
  rfl

/-- **Orientation reversal does not change the first Chern class**: `c₁(s.reverse) = c₁(s)`. -/
theorem firstChernClass_reverse : s.reverse.firstChernClass = s.firstChernClass :=
  firstChernClass_precompIsometry _ s

end SpinCStructure

end TauCeti
