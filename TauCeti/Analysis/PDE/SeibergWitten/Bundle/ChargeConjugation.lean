/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.Bundle.QuadraticTwoForm
public import TauCeti.Analysis.PDE.SeibergWitten.ChargeConjugation
public import TauCeti.Topology.VectorBundle.SpinStructure.HalfSpinorConjugation

/-!
# Charge conjugation reverses the quadratic two-form on the half-spinor bundles

Let `s` be a `Spinᶜ` structure of rank four and `s.chargeConj` its charge conjugate, with positive
half-spinor bundles `W⁺(s)` and `W⁺(s.chargeConj)` built from the same model Hermitian Clifford
module `W`. A conjugate-linear isometric equivalence `j` of `W` commuting with Clifford
multiplication induces the charge conjugation of spinors `ψ ↦ j ψ`, a fibrewise conjugate-linear
isometric equivalence `W⁺(s)_x ≃ W⁺(s.chargeConj)_x`
(`TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv`). Both structures live on the same real
vector bundle `E`, so their Clifford maps `C_x : ⋀² (E x) → End_ℂ (W⁺_x)` and quadratic two-forms
`q_x : W⁺_x → ⋀² (E x)` (`TauCeti.SpinCStructure.cliffordRestriction`,
`TauCeti.SpinCStructure.quadraticTwoForm`) can be compared. This file proves, on every fibre,

`C_x(α) (j ψ) = -j (C_x(α) ψ)`,  `q_x(j ψ) = -q_x(ψ)`

(`TauCeti.SpinCStructure.cliffordRestriction_halfSpinorBundleChargeConjEquiv`,
`TauCeti.SpinCStructure.quadraticTwoForm_halfSpinorBundleChargeConjEquiv`). In a frame `p` of `s`
and the frame `[p, 1]` of `s.chargeConj`, which has the same vector frame
(`TauCeti.SpinCStructure.vectorFrame_chargeConj_inl`), these are the pointwise identities of the
model (`TauCeti.SeibergWitten.cliffordRestriction_positiveHalfSpinorsConjEquiv`,
`TauCeti.SeibergWitten.quadraticTwoForm_positiveHalfSpinorsConjEquiv`).

Since conjugating the connection negates the imaginary curvature form `F_A`, the second identity
is the bundle form of the fact that charge conjugation `(A, ψ, η) ↦ (conj A, j ψ, -η)` carries the
curvature equation `F_A⁺ = q(ψ) + η` of `s` to that of `s.chargeConj`.

## Main results

* `Orientation.HalfSpinModel.toPositiveHalfSpinors_conjEquiv`: on the model positive half-spinors,
  the restriction of `j` is `CliffordAlgebra.positiveHalfSpinorsConjEquiv`.
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
  TauCeti.PrincipalBundle
open scoped InnerProductSpace ComplexConjugate

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-- Charge conjugation of `Spinᶜ(4)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm 4 0) hpos)

/-- Charge conjugation is continuous (`CliffordAlgebra.spinCGroup.continuous_chargeConj`). -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm 4 0) hpos

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  {o : Orientation ℝ V (Fin 4)} {hQ : ∀ v, Q v = -‖v‖ ^ 2}
  {b : OrthonormalBasis (Fin 4) ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)}
  {j : W ≃ₗᵢ⋆[ℂ] W} {hj : ∀ v w, j (ρ (ι Q v) w) = ρ (ι Q v) (j w)} {hε : conj (1 : ℂ) = 1}

/-! ### The model positive half-spinors -/

namespace Orientation.HalfSpinModel

/-- On the model positive half-spinors, the restriction of `j` is its restriction
`CliffordAlgebra.positiveHalfSpinorsConjEquiv` to the positive half-spinors of the model
Clifford module. -/
@[simp]
theorem toPositiveHalfSpinors_conjEquiv (ψ : o.HalfSpinModel hQ b ρ hρ 1) :
    toPositiveHalfSpinors o hQ b ρ hρ (conjEquiv j hj hε ψ) =
      positiveHalfSpinorsConjEquiv o ρ ρ j hj (toPositiveHalfSpinors o hQ b ρ hρ ψ) :=
  Subtype.ext <| by simp

/-- The restriction of `j` to the model positive half-spinors, read through
`CliffordAlgebra.positiveHalfSpinorsConjEquiv`. -/
theorem conjEquiv_toPositiveHalfSpinors_symm (y : positiveHalfSpinors o ρ) :
    conjEquiv j hj hε ((toPositiveHalfSpinors o hQ b ρ hρ).symm y) =
      (toPositiveHalfSpinors o hQ b ρ hρ).symm (positiveHalfSpinorsConjEquiv o ρ ρ j hj y) := by
  rw [LinearIsometryEquiv.eq_symm_apply, toPositiveHalfSpinors_conjEquiv,
    LinearIsometryEquiv.apply_symm_apply]

end Orientation.HalfSpinModel

/-! ### The half-spinor bundles -/

namespace TauCeti.SpinCStructure

open Orientation.HalfSpinModel

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **Charge conjugation anticommutes with the Clifford map** on the positive half-spinor bundles:
`C_x(α) (j ψ) = -j (C_x(α) ψ)` for every two-form `α ∈ ⋀² (E x)`. -/
theorem cliffordRestriction_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) {x : X}
    (α : ⋀[ℝ]^2 (E x)) (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.chargeConj.cliffordRestriction o hQ b ρ hρ x α
        (s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj hε x ψ) =
      -s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj hε x
        (s.cliffordRestriction o hQ b ρ hρ x α ψ) := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  -- The Clifford map of the charge conjugate in its frame `[p, 1]`.
  have h := s.chargeConj.cliffordRestriction_mk (o := o) (hQ := hQ) (hρ := hρ)
    (Extend.inl χ hχ p) α (conjEquiv j hj hε ψ)
  rw [vectorFrame_chargeConj_inl, toPositiveHalfSpinors_conjEquiv,
    SeibergWitten.cliffordRestriction_positiveHalfSpinorsConjEquiv, map_neg] at h
  rw [halfSpinorBundleChargeConjEquiv_mk, cliffordRestriction_mk,
    halfSpinorBundleChargeConjEquiv_mk, conjEquiv_toPositiveHalfSpinors_symm]
  exact h.trans (AssociatedBundle.mk_neg (P := s.chargeConj.P) (Extend.inl χ hχ p) _)

/-- **Charge conjugation reverses the quadratic two-form** on the positive half-spinor bundles:
`q_x(j ψ) = -q_x(ψ)`. With the conjugation of the connection, which negates `F_A`, this carries the
curvature equation `F_A⁺ = q(ψ) + η` of `s` to the curvature equation of `s.chargeConj` with
forcing `-η`. -/
theorem quadraticTwoForm_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) {x : X}
    (ψ : s.halfSpinorBundle o hQ b ρ hρ 1 x) :
    s.chargeConj.quadraticTwoForm o hQ b ρ hρ x
        (s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj hε x ψ) =
      -s.quadraticTwoForm o hQ b ρ hρ x ψ := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  -- The quadratic two-form of the charge conjugate in its frame `[p, 1]`.
  have h := s.chargeConj.quadraticTwoForm_mk (o := o) (hQ := hQ) (hρ := hρ) (x := x)
    (Extend.inl χ hχ p) (conjEquiv j hj hε ψ)
  rw [vectorFrame_chargeConj_inl, toPositiveHalfSpinors_conjEquiv,
    SeibergWitten.quadraticTwoForm_positiveHalfSpinorsConjEquiv, Submodule.coe_neg, map_neg] at h
  rw [halfSpinorBundleChargeConjEquiv_mk, quadraticTwoForm_mk]
  exact h

end TauCeti.SpinCStructure
