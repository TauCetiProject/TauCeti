/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.HalfSpin
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous half-spin representations

The algebraic half-spin representations of `Spinᶜ(4)` act on the actual eigenspaces of the
chirality operator. This file proves that they are continuous for the quotient topology on
`Spinᶜ(4)` and the operator norm topology on endomorphisms. In particular, they give jointly
continuous actions, as needed for associated topological spinor bundles. No choice of a
representative of a quotient class, or matrix coordinates on the half-spinors, is made.

The underlying Spin group has its subtype topology in the real Clifford algebra, whose topology
is the module topology. Clifford multiplication between the two half-spinors is also continuous
in operator norm and jointly continuous in the vector and spinor.

Continuity does not require a compatible Hermitian form on the Clifford module. When such a form
is available, the existing algebraic unitarity theorem applies to the same continuous operators.
These results concern topology, not a smooth manifold structure on the quotient group.

## Main results

* `CliffordAlgebra.continuous_spinCGroupHalfSpinRep`: operator norm continuity on the quotient.
* `CliffordAlgebra.spinCGroupHalfSpinContinuousHom`: the descended representation as a continuous
  monoid homomorphism into continuous complex-linear endomorphisms.
* `CliffordAlgebra.continuous_spinCGroupHalfSpinRep_apply`: joint continuity of the action.
* `CliffordAlgebra.continuous_halfSpinCliffordMul`: operator norm continuity of the odd action.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

omit [FiniteDimensional ℂ W] in
/-- The Spin half-spin representation is continuous at each fixed spinor for the Clifford
subtype topology. -/
@[fun_prop]
theorem continuous_halfSpinRep_apply_const (ψ : eigenspace (ρ (chirality Q o)) ε) :
    Continuous (fun s : spinGroup Q ↦ halfSpinRep o ρ ε s ψ) := by
  have h := IsModuleTopology.continuous_of_linearMap
    (((LinearMap.applyₗ (R := ℂ) (ψ : W)).restrictScalars ℝ).comp ρ.toLinearMap)
  exact continuous_induced_rng.mpr <| by
    simpa only [Function.comp_def, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.applyₗ_apply_apply, AlgHom.toLinearMap_apply, coe_halfSpinRep_apply] using
      h.comp continuous_subtype_val

/-- The Spin half-spin representation varies continuously in operator norm. -/
@[fun_prop]
theorem continuous_halfSpinRep :
    Continuous (fun s : spinGroup Q ↦
      (halfSpinRep o ρ ε s).toContinuousLinearMap) := by
  exact continuous_clm_apply.mpr (continuous_halfSpinRep_apply_const o ρ ε)

omit [FiniteDimensional ℂ W] in
/-- On the product `Spin(4) × U(1)`, the weight-one half-spin action is continuous at each
fixed spinor. -/
@[fun_prop]
theorem continuous_spinCHalfSpinRep_apply_const (ψ : eigenspace (ρ (chirality Q o)) ε) :
    Continuous (fun p : spinGroup Q × Circle ↦ spinCHalfSpinRep o ρ ε p ψ) := by
  have hz : Continuous (fun p : spinGroup Q × Circle ↦ (p.2 : ℂ)) := by fun_prop
  convert hz.smul ((continuous_halfSpinRep_apply_const o ρ ε ψ).comp continuous_fst) using 1
  funext ⟨s, z⟩
  simp

variable (hQ₀ : Q ≠ 0)

omit [FiniteDimensional ℂ W] in
/-- The descended half-spin action is continuous at each fixed spinor for the actual quotient
topology on `Spinᶜ(4)`. -/
@[fun_prop]
theorem continuous_spinCGroupHalfSpinRep_apply_const
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    Continuous (fun x : spinCGroup Q hQ₀ ↦ spinCGroupHalfSpinRep o ρ ε hQ₀ x ψ) := by
  apply (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ₀)).continuous_iff.mpr
  simpa only [Function.comp_def, ← spinCGroup.mk_apply, spinCGroupHalfSpinRep_mk] using
    continuous_spinCHalfSpinRep_apply_const o ρ ε ψ

/-- The descended half-spin representation is continuous in operator norm, not merely in the
pointwise operator topology. -/
@[fun_prop]
theorem continuous_spinCGroupHalfSpinRep :
    Continuous (fun x : spinCGroup Q hQ₀ ↦
      (spinCGroupHalfSpinRep o ρ ε hQ₀ x).toContinuousLinearMap) := by
  exact continuous_clm_apply.mpr (continuous_spinCGroupHalfSpinRep_apply_const o ρ ε hQ₀)

/-- The half-spin representation of `Spinᶜ(4)`, bundled as a continuous monoid homomorphism
into complex-linear continuous endomorphisms. Multiplication in the target is composition. -/
def spinCGroupHalfSpinContinuousHom :
    spinCGroup Q hQ₀ →ₜ* (eigenspace (ρ (chirality Q o)) ε →L[ℂ]
      eigenspace (ρ (chirality Q o)) ε) where
  toFun x := (spinCGroupHalfSpinRep o ρ ε hQ₀ x).toContinuousLinearMap
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  continuous_toFun := continuous_spinCGroupHalfSpinRep o ρ ε hQ₀

/-- The continuous representation has exactly the original algebraic half-spin action. -/
@[simp]
theorem spinCGroupHalfSpinContinuousHom_apply (x : spinCGroup Q hQ₀) :
    spinCGroupHalfSpinContinuousHom o ρ ε hQ₀ x =
      (spinCGroupHalfSpinRep o ρ ε hQ₀ x).toContinuousLinearMap :=
  (rfl)

/-- The descended half-spin action is jointly continuous in the group element and the spinor. -/
@[fun_prop]
theorem continuous_spinCGroupHalfSpinRep_apply :
    Continuous (fun p : spinCGroup Q hQ₀ × eigenspace (ρ (chirality Q o)) ε ↦
      spinCGroupHalfSpinRep o ρ ε hQ₀ p.1 p.2) :=
  ((continuous_spinCGroupHalfSpinRep o ρ ε hQ₀).comp continuous_fst).clm_apply continuous_snd

/-- Clifford multiplication between the two half-spinors is continuous in operator norm as a
function of the real vector. -/
@[fun_prop]
theorem continuous_halfSpinCliffordMul :
    Continuous (fun v : V ↦ (halfSpinCliffordMul o ρ ε v).toContinuousLinearMap) := by
  let : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ
    (Fact.out : finrank ℝ V = 4)
  let : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  apply continuous_clm_apply.mpr
  intro ψ
  apply continuous_induced_rng.mpr
  have h := IsModuleTopology.continuous_of_linearMap
    (((LinearMap.applyₗ (R := ℂ) (ψ : W)).restrictScalars ℝ).comp ρ.toLinearMap)
  simpa only [Function.comp_def, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.applyₗ_apply_apply, AlgHom.toLinearMap_apply,
    LinearMap.coe_toContinuousLinearMap',
    coe_halfSpinCliffordMul_apply_apply] using h.comp (continuous_ι Q)

/-- Clifford multiplication is jointly continuous in the real vector and the half-spinor. -/
@[fun_prop]
theorem continuous_halfSpinCliffordMul_apply :
    Continuous (fun p : V × eigenspace (ρ (chirality Q o)) ε ↦
      halfSpinCliffordMul o ρ ε p.1 p.2) :=
  ((continuous_halfSpinCliffordMul o ρ ε).comp continuous_fst).clm_apply continuous_snd

end CliffordAlgebra
