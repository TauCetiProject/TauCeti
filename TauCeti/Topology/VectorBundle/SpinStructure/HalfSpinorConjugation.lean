/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Associated.Extension
public import TauCeti.Topology.VectorBundle.SpinStructure.ChargeConjugation
public import TauCeti.Topology.VectorBundle.SpinStructure.Spinor

/-!
# Charge conjugation of the half-spinor bundles

Let `s` be a `Spinᶜ` structure of rank four with principal bundle `P`, and let `s.chargeConj` be
its charge conjugate, the extension of `s` along `χ : [g, z] ↦ [g, z⁻¹]`
(`TauCeti.SpinCStructure.chargeConj`), with principal bundle `P ×_χ Spinᶜ(4)`. The half-spinor
bundles `W^ε = P ×_{Spinᶜ(4)} S^ε` of both structures are built from the same model Hermitian
Clifford module `W` (`TauCeti.SpinCStructure.halfSpinorBundle`). This file constructs the
**charge conjugation of spinors** `ψ ↦ j ψ` from `W^ε(s)` to `W^ε(s.chargeConj)`, the map on
spinors of Taubes's charge conjugation `(A, ψ) ↦ (conj A, j ψ)` of Seiberg–Witten configurations.

**The model.** Let `j : W → W` be a conjugate-linear isometric equivalence commuting with
Clifford multiplication, `j (c(v) w) = c(v) (j w)`, such as the quaternionic structure of the
spinors of `ℝ⁴`. Then `j` commutes with the chirality element, so it preserves its eigenspaces
for real eigenvalues `ε`, and restricts to a conjugate-linear isometric equivalence of the model
half-spinors `S^ε` (`Orientation.HalfSpinModel.conjEquiv`, from
`CliffordAlgebra.eigenspaceChiralityConjEquiv`). Since `j` commutes with the Spin
action and conjugates the central circle, `j (g • ψ) = χ(g) • j ψ`
(`Orientation.HalfSpinModel.conjEquiv_smul`, from
`CliffordAlgebra.map_coe_halfSpinRep_apply`).

**The bundles.** The equivariance makes `[p, ψ] ↦ [[p, 1], j ψ]` well defined: changing `p` to
`p • g` changes `ψ` to `g • ψ` and `[p, 1]` to `[p, 1] • χ(g)`. This is the associated map of the
equivariant model map `j` (`TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant`), a
fibrewise conjugate-linear isometric equivalence
`TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv : W^ε(s)_x ≃ W^ε(s.chargeConj)_x`
(`TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv_mk`), continuous on total spaces
(`TauCeti.SpinCStructure.continuous_halfSpinorBundleChargeConjEquiv`). The frame of `E x` at
`[p, 1]` is the frame at `p` (`TauCeti.SpinCStructure.frameAt_chargeConj_inl`), so the map
commutes with Clifford multiplication by vectors of `E x`
(`TauCeti.SpinCStructure.cliffordMul_halfSpinorBundleChargeConjEquiv`). The consequences for the
quadratic map of the Seiberg–Witten equations are in
`TauCeti.Analysis.PDE.SeibergWitten.Bundle.ChargeConjugation`.

## Main definitions

* `Orientation.HalfSpinModel.conjEquiv`: the restriction of `j` to the model half-spinors.
* `TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv`: charge conjugation of half-spinors,
  `W^ε(s)_x ≃ W^ε(s.chargeConj)_x`, `[p, ψ] ↦ [[p, 1], j ψ]`.

## Main results

* `Orientation.HalfSpinModel.conjEquiv_smul`: `j (g • ψ) = χ(g) • j ψ`.
* `TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv_mk`: the formula in every frame.
* `TauCeti.SpinCStructure.continuous_halfSpinorBundleChargeConjEquiv`: continuity on total
  spaces.
* `TauCeti.SpinCStructure.cliffordMul_halfSpinorBundleChargeConjEquiv`: `c(v) (j ψ) = j (c(v) ψ)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
* C. H. Taubes, *GR = SW: counting curves and connections*, J. Differential Geom. 52 (1999),
  453–609.
-/

public section

noncomputable section

open Bundle MulOpposite Module Module.End CliffordAlgebra TauCeti TauCeti.CliffordAlgebra
  TauCeti.PrincipalBundle
open scoped InnerProductSpace ComplexConjugate

/-- The proof that the standard form on `ℝ⁴` is nonzero, on which `Spinᶜ(4)` depends. -/
local notation "hpos" => QuadraticMap.Nondegenerate.ne_zero (nondegenerate_realCliffordForm 4 0)
local notation "SpinC" => spinCGroup (realCliffordForm 4 0) hpos

/-- Charge conjugation of `Spinᶜ(4)` as a homomorphism. -/
local notation "χ" => MonoidHom.ofClass (spinCGroup.chargeConj (realCliffordForm 4 0) hpos)

/-- Charge conjugation is continuous (`CliffordAlgebra.spinCGroup.continuous_chargeConj`). -/
local notation "hχ" => spinCGroup.continuous_chargeConj (realCliffordForm 4 0) hpos

/-! ### The model half-spinors -/

namespace Orientation.HalfSpinModel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  {o : Orientation ℝ V (Fin 4)} {hQ : ∀ v, Q v = -‖v‖ ^ 2}
  {b : OrthonormalBasis (Fin 4) ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)} {ε : ℂ}
  (j : W ≃ₗᵢ⋆[ℂ] W) (hj : ∀ v w, j (ρ (ι Q v) w) = ρ (ι Q v) (j w)) (hε : conj ε = ε)

/-- **Charge conjugation of the model half-spinors**: a conjugate-linear isometric equivalence `j`
of the model Clifford module commuting with Clifford multiplication restricts to a conjugate-linear
isometric equivalence of the model half-spinors `S^ε`, for a real eigenvalue `ε` of the chirality
element (`CliffordAlgebra.eigenspaceChiralityConjEquiv`). -/
def conjEquiv : o.HalfSpinModel hQ b ρ hρ ε ≃ₗᵢ⋆[ℂ] o.HalfSpinModel hQ b ρ hρ ε :=
  toEigenspace.trans ((eigenspaceChiralityConjEquiv o ρ ρ j hj hε).trans toEigenspace.symm)

/-- The restriction of `j` to the model half-spinors is `j`. -/
@[simp]
theorem coe_toEigenspace_conjEquiv (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    (toEigenspace (conjEquiv j hj hε ψ) : W) = j (toEigenspace ψ) := by
  simp only [conjEquiv, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    coe_eigenspaceChiralityConjEquiv_apply]

/-- The inverse of the restriction of `j` to the model half-spinors is `j⁻¹`. -/
@[simp]
theorem coe_toEigenspace_conjEquiv_symm (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    (toEigenspace ((conjEquiv j hj hε).symm ψ) : W) = j.symm (toEigenspace ψ) := by
  simp only [conjEquiv, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    coe_eigenspaceChiralityConjEquiv_symm_apply]

/-- **Charge conjugation of spinors intertwines `g` with its charge conjugate**:
`j (g • ψ) = χ(g) • j ψ` on the model half-spinors, where `χ [s, z] = [s, z⁻¹]` is charge
conjugation of `Spinᶜ(4)`. At `g = [s, z]` both sides are `z⁻¹ ρ(s) (j ψ)`. -/
theorem conjEquiv_smul (g : SpinC) (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    conjEquiv j hj hε (g • ψ) = spinCGroup.chargeConj _ hpos g • conjEquiv j hj hε ψ := by
  apply toEigenspace.injective
  apply Subtype.ext
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective _ hpos g
  have h := map_coe_halfSpinRep_apply o ρ ε (j := j.toLinearEquiv.toLinearMap) hj
    (b.realSpinGroupEquiv hQ s) (ψ := toEigenspace ψ)
    (ψ' := toEigenspace (conjEquiv j hj hε ψ)) (coe_toEigenspace_conjEquiv j hj hε ψ).symm
  rw [coe_halfSpinRep_apply, coe_halfSpinRep_apply, coe_toEigenspace_conjEquiv] at h
  simp only [coe_toEigenspace_conjEquiv, toEigenspace_smul, spinCGroup.chargeConj_mk,
    realSpinCHalfSpinSmoothHom_mk, spinCHalfSpinRep_apply]
  simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at h
  simp [map_smulₛₗ, h, ← Circle.coe_inv_eq_conj]

/-- **Charge conjugation of spinors commutes with Clifford multiplication**:
`j (c(v) ψ) = c(v) (j ψ)` from `S^ε` to `S^{ε'}`, `ε' = -ε`. -/
theorem conjEquiv_cliffordMul {ε' : ℂ} (hε' : ε' = -ε) (v : V)
    (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    conjEquiv j hj (by rw [hε', map_neg, hε]) (cliffordMul hε' v ψ) =
      cliffordMul hε' v (conjEquiv j hj hε ψ) :=
  toEigenspace.injective <| Subtype.ext <| by simp [hj]

/-- If `j` is a quaternionic structure, `j (j w) = -w`, then so is its restriction to the model
half-spinors. -/
theorem conjEquiv_conjEquiv (hj₂ : ∀ w, j (j w) = -w) (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    conjEquiv j hj hε (conjEquiv j hj hε ψ) = -ψ :=
  toEigenspace.injective <| Subtype.ext <| by simp [hj₂]

end Orientation.HalfSpinModel

/-! ### The half-spinor bundles -/

namespace TauCeti.SpinCStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V}
  {o : Orientation ℝ V (Fin 4)} {hQ : ∀ v, Q v = -‖v‖ ^ 2}
  {b : OrthonormalBasis (Fin 4) ℝ V}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)} {ε : ℂ}
  {j : W ≃ₗᵢ⋆[ℂ] W} {hj : ∀ v w, j (ρ (ι Q v) w) = ρ (ι Q v) (j w)} {hε : conj ε = ε}

omit [Fact (finrank ℝ V = 4)] in
/-- The vector frame `κ : E x ≃ V` at `[p, 1]` in the charge conjugate is the vector frame at
`p` (`TauCeti.SpinCStructure.vectorFrame_extendSpinC_inl`). -/
@[simp]
theorem vectorFrame_chargeConj_inl (s : SpinCStructure F E 4) {x : X} (p : s.P x) :
    s.chargeConj.vectorFrame b (Extend.inl χ hχ p : s.chargeConj.P x) = s.vectorFrame b p :=
  s.vectorFrame_extendSpinC_inl b χ hχ ((MonoidHom.comp_assoc _ _ _).trans
    (congrArg (MonoidHom.comp _) (spinCGroup.toSpecialOrthogonal_comp_chargeConj _ hpos))) p

variable (o hQ b ρ hρ j hj hε) in
/-- **Charge conjugation of the half-spinors** of a `Spinᶜ` structure of rank four: the fibrewise
conjugate-linear isometric equivalence `W^ε(s)_x ≃ W^ε(s.chargeConj)_x`,
`[p, ψ] ↦ [[p, 1], j ψ]` (`TauCeti.SpinCStructure.halfSpinorBundleChargeConjEquiv_mk`), for a
conjugate-linear isometric equivalence `j` of the model Clifford module commuting with Clifford
multiplication and a real eigenvalue `ε` of the chirality element. It is the associated map of the
`χ`-equivariant model map `j` (`TauCeti.PrincipalBundle.Extend.associatedEquivOfEquivariant`). -/
def halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) (x : X) :
    s.halfSpinorBundle o hQ b ρ hρ ε x ≃ₗᵢ⋆[ℂ] s.chargeConj.halfSpinorBundle o hQ b ρ hρ ε x where
  toLinearEquiv := (Extend.associatedEquivOfEquivariant χ hχ
    (Orientation.HalfSpinModel.conjEquiv j hj hε).toContinuousLinearEquiv x).toLinearEquiv
  norm_map' ψ := by
    obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
    refine (congrArg Norm.norm (Extend.associatedEquivOfEquivariant_mk χ hχ _
      (Orientation.HalfSpinModel.conjEquiv_smul j hj hε) p ψ)).trans ?_
    -- Both classes have the norm of their model vectors, which `j` preserves.
    exact (AssociatedBundle.norm_mk _ _).trans
      (((Orientation.HalfSpinModel.conjEquiv j hj hε).norm_map ψ).trans
        (AssociatedBundle.norm_mk p ψ).symm)

/-- **Charge conjugation of the half-spinors in a frame**: `[p, ψ] ↦ [[p, 1], j ψ]` for every point
`p` of the principal bundle over `x`. -/
@[simp]
theorem halfSpinorBundleChargeConjEquiv_mk (s : SpinCStructure F E 4) {x : X} (p : s.P x)
    (ψ : o.HalfSpinModel hQ b ρ hρ ε) :
    s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj hε x (AssociatedBundle.mk SpinC p ψ) =
      AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.inl χ hχ p)
        (Orientation.HalfSpinModel.conjEquiv j hj hε ψ) :=
  -- By definition, `halfSpinorBundleChargeConjEquiv` applies the associated map of `j`.
  Extend.associatedEquivOfEquivariant_mk χ hχ _ (Orientation.HalfSpinModel.conjEquiv_smul j hj hε)
    p ψ

/-- The inverse of charge conjugation of the half-spinors at `[p, 1]`:
`[[p, 1], φ] ↦ [p, j⁻¹ φ]`. -/
@[simp]
theorem halfSpinorBundleChargeConjEquiv_symm_mk_inl (s : SpinCStructure F E 4) {x : X}
    (p : s.P x) (φ : o.HalfSpinModel hQ b ρ hρ ε) :
    (s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj hε x).symm
        (AssociatedBundle.mk (P := Extend s.P χ hχ) SpinC (Extend.inl χ hχ p) φ) =
      AssociatedBundle.mk SpinC p ((Orientation.HalfSpinModel.conjEquiv j hj hε).symm φ) := by
  refine (LinearIsometryEquiv.symm_apply_eq _).2 ?_
  rw [halfSpinorBundleChargeConjEquiv_mk, LinearIsometryEquiv.apply_symm_apply]

/-- **Charge conjugation of the half-spinors is continuous** on total spaces. -/
theorem continuous_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) :
    Continuous fun v : TotalSpace (o.HalfSpinModel hQ b ρ hρ ε) (s.halfSpinorBundle o hQ b ρ hρ ε) ↦
      TotalSpace.mk' (o.HalfSpinModel hQ b ρ hρ ε) v.proj
        (s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj hε v.proj v.snd) :=
  Extend.continuous_associatedEquivOfEquivariant χ hχ _
    (Orientation.HalfSpinModel.conjEquiv_smul j hj hε)

/-- **Charge conjugation of the half-spinors commutes with Clifford multiplication**:
`c(v) (j ψ) = j (c(v) ψ)` for `v ∈ E x`, from `W^ε` to `W^{ε'}`, `ε' = -ε`. -/
theorem cliffordMul_halfSpinorBundleChargeConjEquiv (s : SpinCStructure F E 4) {ε' : ℂ}
    (hε' : ε' = -ε) {x : X} (v : E x) (ψ : s.halfSpinorBundle o hQ b ρ hρ ε x) :
    s.chargeConj.cliffordMul o hQ b ρ hρ hε' x v
        (s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj hε x ψ) =
      s.halfSpinorBundleChargeConjEquiv o hQ b ρ hρ j hj (by rw [hε', map_neg, hε]) x
        (s.cliffordMul o hQ b ρ hρ hε' x v ψ) := by
  obtain ⟨p, ψ, rfl⟩ := AssociatedBundle.exists_mk ψ
  rw [halfSpinorBundleChargeConjEquiv_mk, cliffordMul_mk, halfSpinorBundleChargeConjEquiv_mk,
    Orientation.HalfSpinModel.conjEquiv_cliffordMul, ← vectorFrame_chargeConj_inl]
  -- Clifford multiplication of the charge conjugate in its frame `[p, 1]`.
  exact cliffordMul_mk s.chargeConj hε' (Extend.inl χ hχ p) v _

end TauCeti.SpinCStructure
