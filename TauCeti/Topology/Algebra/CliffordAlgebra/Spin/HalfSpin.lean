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
* `CliffordAlgebra.isClosed_stabilizer_spinCGroupHalfSpinRep`: the stabilizer of a fixed spinor
  in `Spinᶜ(4)` is closed, with no topology assumed on `W`.
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

section Normed

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
  apply continuous_induced_rng.mpr
  simpa [Function.comp_def, coe_halfSpinRep_apply] using
    (continuous_algHom_apply ρ (ψ : W)).comp
    (continuous_subtypeVal : Continuous (fun s : spinGroup Q ↦ s.val))

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
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_eq_succ
    (Fact.out : finrank ℝ V = 4)
  have : IsModuleTopology ℝ V := isModuleTopologyOfFiniteDimensional
  apply continuous_clm_apply.mpr
  intro ψ
  apply continuous_induced_rng.mpr
  simpa [Function.comp_def, coe_halfSpinCliffordMul_apply_apply] using
    (continuous_algHom_apply ρ (ψ : W)).comp (continuous_ι Q)

/-- Clifford multiplication is jointly continuous in the real vector and the half-spinor. -/
@[fun_prop]
theorem continuous_halfSpinCliffordMul_apply :
    Continuous (fun p : V × eigenspace (ρ (chirality Q o)) ε ↦
      halfSpinCliffordMul o ρ ε p.1 p.2) :=
  ((continuous_halfSpinCliffordMul o ρ ε).comp continuous_fst).clm_apply continuous_snd

end Normed

section Stabilizer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (finrank ℝ V = 4)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ε : ℂ)

/-- The stabilizer of a fixed half-spinor `ψ` under the `Spinᶜ(Q)` half-spin representation is
closed in `spinCGroup Q hQ₀`, with no topology assumed on the spinor module `W`. -/
theorem isClosed_stabilizer_spinCGroupHalfSpinRep (hQ₀ : Q ≠ 0)
    (ψ : eigenspace (ρ (chirality Q o)) ε) :
    IsClosed {x : spinCGroup Q hQ₀ | spinCGroupHalfSpinRep o ρ ε hQ₀ x ψ = ψ} := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3
  rw [← (QuotientGroup.isQuotientMap_mk (spinCKernel Q hQ₀)).isClosed_preimage]
  let bA := Module.finBasis ℝ (CliffordAlgebra Q)
  let U : Submodule ℂ W := Submodule.span ℂ (Set.range fun i ↦ ρ (bA i) ψ)
  have hmem (a : CliffordAlgebra Q) : ρ a ψ ∈ U := by
    rw [← bA.sum_repr a, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem U fun i _ ↦ ?_
    rw [map_smul, LinearMap.smul_apply]
    exact U.smul_mem (bA.repr a i : ℂ) (Submodule.subset_span ⟨i, rfl⟩)
  have : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let bU := Module.finBasis ℂ U
  let f : CliffordAlgebra Q →ₗ[ℝ] (Fin (finrank ℂ U) → ℂ) :=
    { toFun a := bU.equivFun ⟨ρ a ψ, hmem a⟩
      map_add' a b := by
        rw [← map_add]
        congr 1
        exact Subtype.ext (by simp)
      map_smul' r a := by
        have h : (⟨ρ (r • a) ψ, hmem (r • a)⟩ : U) = (r : ℂ) • ⟨ρ a ψ, hmem a⟩ :=
          Subtype.ext (by simp)
        rw [h, map_smul, RingHom.id_apply]
        ext i
        simp [Complex.real_smul] }
  have hg : Continuous (fun p : spinGroup Q × Circle ↦ (p.2 : ℂ) • f p.1.val) :=
    (continuous_subtypeVal.comp continuous_snd).smul
      ((IsModuleTopology.continuous_of_linearMap f).comp
        (continuous_subtypeVal.comp continuous_fst))
  have hpre : (QuotientGroup.mk : spinGroup Q × Circle → spinCGroup Q hQ₀) ⁻¹'
      {x | spinCGroupHalfSpinRep o ρ ε hQ₀ x ψ = ψ} =
      {p : spinGroup Q × Circle | (p.2 : ℂ) • f p.1.val = f 1} := by
    ext ⟨s, z⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← spinCGroup.mk_apply,
      spinCGroupHalfSpinRep_mk, Subtype.ext_iff, spinCHalfSpinRep_apply, LinearMap.smul_apply,
      Submodule.coe_smul, coe_halfSpinRep_apply]
    have h1 : f 1 = bU.equivFun ⟨ψ, by simpa using hmem 1⟩ := by simp [f]
    have h2 : (z : ℂ) • f s.val = bU.equivFun ⟨(z : ℂ) • ρ s.val ψ, U.smul_mem _ (hmem s.val)⟩ :=
      (bU.equivFun.map_smul (z : ℂ) ⟨ρ s.val ψ, hmem s.val⟩).symm
    rw [h1, h2, bU.equivFun.injective.eq_iff, Subtype.ext_iff]
  rw [hpre]
  exact isClosed_eq hg continuous_const

end Stabilizer

end CliffordAlgebra
