/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Bundle.QuadraticTwoForm
public import TauCeti.Analysis.PDE.SeibergWitten.ChargeConjugation
public import TauCeti.Topology.VectorBundle.SpinStructure.ChargeConjugation

/-!
# Charge conjugation of the quadratic two-form on the half-spinors of a `Spinᶜ` structure

Let `s` be a `Spinᶜ` structure of rank four on a real vector bundle `E → X`, and let
`j : W ≃ W'` be a conjugate-linear isometric equivalence of model Hermitian Clifford modules
commuting with Clifford multiplication, such as the quaternionic structure of the spinors. Charge
conjugation of spinors `ψ ↦ j ψ` maps the positive half-spinors `W⁺(s)` of `s` to the positive
half-spinors `W'⁺(s.chargeConj)` of its charge conjugate
(`TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv`). This file proves that on every fibre it
reverses the two maps of the Seiberg–Witten curvature equation `F_A⁺ = q(ψ) + η`
(`TauCeti.SpinCStructure.cliffordRestriction`, `TauCeti.SpinCStructure.quadraticTwoForm`):

`C_x(α) (j ψ) = -j (C_x(α) ψ)`,  `q_x(j ψ) = -q_x(ψ)`.

These are the pointwise identities of the model Clifford module
(`TauCeti.SeibergWitten.cliffordRestriction_positiveHalfSpinorsConjEquiv`,
`TauCeti.SeibergWitten.quadraticTwoForm_positiveHalfSpinorsConjEquiv`), read in the frames
`[p, -]` of `W⁺(s)_x` and `[[p, 1], -]` of `W'⁺(s.chargeConj)_x`, which have the same vector frame
of `E x` (`TauCeti.SpinCStructure.vectorFrame_chargeConj_inl`). Since charge conjugation of
connections negates the curvature, `(A, ψ, η) ↦ (conj A, j ψ, -η)` carries the curvature equation
of `s` to that of `s.chargeConj`.

## Main results

* `Orientation.HalfSpinModel.toPositiveHalfSpinors_conjEquiv`: on the model positive half-spinors,
  charge conjugation is the restriction of `j` to the positive half-spinors.
* `Orientation.HalfSpinModel.toPositiveHalfSpinors_symm_positiveHalfSpinorsConjEquiv`: the same
  identity read through the inverse of `toPositiveHalfSpinors`.
* `TauCeti.SpinCStructure.cliffordRestriction_halfSpinorBundleChargeConjEquiv`:
  `C_x(α) (j ψ) = -j (C_x(α) ψ)`.
* `TauCeti.SpinCStructure.quadraticTwoForm_halfSpinorBundleChargeConjEquiv`: `q_x(j ψ) = -q_x(ψ)`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Bundle Module Module.End TauCeti CliffordAlgebra TauCeti.CliffordAlgebra
open TauCeti.PrincipalBundle Orientation.HalfSpinModel
open scoped InnerProductSpace

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-- Charge conjugation of `Spinᶜ(4)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm 4 0) hpos)

/-- Charge conjugation of `Spinᶜ(4)` is continuous. -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm 4 0) hpos

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  {o : Orientation ℝ V (Fin 4)} {hQ : ∀ v, Q v = -‖v‖ ^ 2}
  {b : OrthonormalBasis (Fin 4) ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)}
  {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [FiniteDimensional ℂ W']
  {ρ' : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W'}
  {hρ' : ∀ v, LinearMap.adjoint (ρ' (ι Q v)) = -ρ' (ι Q v)}
  {j : W ≃ₗᵢ⋆[ℂ] W'} {hj : ∀ v w, j (ρ (ι Q v) w) = ρ' (ι Q v) (j w)}

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

namespace Orientation.HalfSpinModel

/-- On the model positive half-spinors, charge conjugation
`Orientation.HalfSpinModel.conjEquiv` is the restriction of `j` to the positive half-spinors of the
model Clifford modules (`CliffordAlgebra.positiveHalfSpinorsConjEquiv`). -/
@[simp]
theorem toPositiveHalfSpinors_conjEquiv (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    toPositiveHalfSpinors o hQ b ρ' hρ' (conjEquiv hρ hρ' j hj (map_one _) ψ) =
      positiveHalfSpinorsConjEquiv o ρ ρ' j hj (toPositiveHalfSpinors o hQ b ρ hρ ψ) :=
  Subtype.ext (by simp)

/-- On the model positive half-spinors, the inverse of `toPositiveHalfSpinors` carries the
restriction of `j` to the positive half-spinors to charge conjugation
`Orientation.HalfSpinModel.conjEquiv`. -/
theorem toPositiveHalfSpinors_symm_positiveHalfSpinorsConjEquiv (φ : positiveHalfSpinors o ρ) :
    (toPositiveHalfSpinors o hQ b ρ' hρ').symm (positiveHalfSpinorsConjEquiv o ρ ρ' j hj φ) =
      conjEquiv hρ hρ' j hj (map_one _) ((toPositiveHalfSpinors o hQ b ρ hρ).symm φ) :=
  (toPositiveHalfSpinors o hQ b ρ' hρ').injective (by simp)

end Orientation.HalfSpinModel

namespace TauCeti.SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Charge conjugation of spinors anticommutes with the Clifford map**:
`C_x(α) (j ψ) = -j (C_x(α) ψ)` on the positive half-spinors, for every two-form `α` of `E x`. -/
theorem cliffordRestriction_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) {x : X}
    (α : ⋀[ℝ]^2 (E x)) (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.chargeConj.cliffordRestriction o hQ b ρ' hρ' x α
        (s.halfSpinorBundleChargeConjEquiv o hQ b hρ hρ' j hj (map_one _) x ψ) =
      -s.halfSpinorBundleChargeConjEquiv o hQ b hρ hρ' j hj (map_one _) x
        (s.cliffordRestriction o hQ b ρ hρ x α ψ) := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  -- `rw` does not unfold `chargeConj`, so the point `[p, 1]` of `s.chargeConj.P x` is explicit.
  rw [halfSpinorBundleChargeConjEquiv_mk, cliffordRestriction_mk,
    halfSpinorBundleChargeConjEquiv_mk, s.chargeConj.cliffordRestriction_mk (Extend.inl χ hχ p),
    vectorFrame_chargeConj_inl, Orientation.HalfSpinModel.toPositiveHalfSpinors_conjEquiv,
    SeibergWitten.cliffordRestriction_positiveHalfSpinorsConjEquiv, map_neg,
    toPositiveHalfSpinors_symm_positiveHalfSpinorsConjEquiv (hρ := hρ),
    AssociatedBundle.mk_neg (P := s.chargeConj.P) (Extend.inl χ hχ p)]

/-- **Charge conjugation of spinors reverses the quadratic two-form**: `q_x(j ψ) = -q_x(ψ)` on the
positive half-spinors. Since charge conjugation of connections negates the curvature, this turns
the curvature equation `F_A⁺ = q(ψ) + η` of `s` into the curvature equation of `s.chargeConj` for
`(conj A, j ψ)` with forcing `-η`. -/
theorem quadraticTwoForm_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) {x : X}
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.chargeConj.quadraticTwoForm o hQ b ρ' hρ' x
        (s.halfSpinorBundleChargeConjEquiv o hQ b hρ hρ' j hj (map_one _) x ψ) =
      -s.quadraticTwoForm o hQ b ρ hρ x ψ := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  -- `rw` does not unfold `chargeConj`, so the point `[p, 1]` of `s.chargeConj.P x` is explicit.
  rw [halfSpinorBundleChargeConjEquiv_mk, quadraticTwoForm_mk,
    s.chargeConj.quadraticTwoForm_mk (Extend.inl χ hχ p), vectorFrame_chargeConj_inl,
    Orientation.HalfSpinModel.toPositiveHalfSpinors_conjEquiv,
    SeibergWitten.quadraticTwoForm_positiveHalfSpinorsConjEquiv, Submodule.coe_neg, map_neg]

end TauCeti.SpinCStructure
