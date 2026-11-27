/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.FundamentalGroupCircle
public import TauCeti.Algebra.Homology.DG.Module.Right.Homology
public import TauCeti.AlgebraicTopology.DGLocalSystem.Homology
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Augmentation
public import TauCeti.Topology.PathSpace.Moore.Between.FundamentalGroup

/-!
# Changing the basepoint conjugates the monodromy

A DG local system at a point `a` of a space `B` is a right DG module `M` over the chain algebra
`C_*(Ω_a B)` of Moore loops, and the fundamental group `π₁(B, a)` acts on its homology `H(M)`
(`TauCeti.IsDGRightModule.cohomologyRepresentation`). Tensoring with the chain bimodule
`C_*(P_{a→b} B)` of Moore paths from `a` to `b` changes its basepoint to `b`. This file computes
the homology of the result as a representation of `π₁(B, b)`.

Fix a Moore path `δ` from `a` to `b`. Tensoring with the `0`-chain of `δ`, `m ↦ m ⊗ [δ]`, is a
homotopy equivalence of chain complexes `M → M ⊗ C_*(P_{a→b} B)`
(`TauCeti.tensorPathChainPoint_tensorPathChainAct`,
`TauCeti.exists_tensorPathChainAct_tensorPathChainPoint`), linear over the ground ring but not
over the loops. So it induces an isomorphism on homology
(`TauCeti.tensorPathChainPointCohomologyEquiv`, built from `LinearMap.homologyEquivOfHomotopy`
through the identification `TauCeti.IsDGRightModule.cohomologyEquivHomology` of `H(M)` with the
homology of the differential):

`H(M) ≅ H(M ⊗ C_*(P_{a→b} B))`.

It intertwines the two actions of the fundamental groups through conjugation by `δ`. For a Moore
loop `λ` at `b`, the loop `δ ⋆ λ ⋆ δ⁻¹` at `a` is
`(MoorePathBetween.loopAppendHomotopyEquiv δ).symm (op λ • δ)`: `λ` acts on `δ` from the right,
and the reversal of `δ` is appended. On homology,

`[m · (δ ⋆ λ ⋆ δ⁻¹)] ↦ [(m ⊗ [δ]) · λ]`

(`TauCeti.tensorPathChainPointCohomologyEquiv_cohomologyRepresentation`). At the chain level,
`m · (δ ⋆ λ ⋆ δ⁻¹) ⊗ [δ] = m ⊗ [δ ⋆ λ ⋆ δ⁻¹ ⋆ δ]` and `(m ⊗ [δ]) · λ = m ⊗ [δ ⋆ λ]`, and the two
paths `δ ⋆ λ ⋆ δ⁻¹ ⋆ δ` and `δ ⋆ λ` are joined by retracting the suffix `δ⁻¹ ⋆ δ`; for a cycle
`m` the two tensors differ by a boundary
(`TauCeti.tensorPathChainPoint_op_smul_eq_op_smul_add_differential`).

So changing the basepoint along `δ` turns a local system with monodromy `ρ` at `a` into one whose
homology has the monodromy `λ ↦ ρ(δ ⋆ λ ⋆ δ⁻¹)` at `b`. When `b = a` and `π₁(B, a)` is
commutative, as for the circle, conjugation is trivial
(`TauCeti.MoorePathBetween.fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul`) and the
change of basepoint along a loop does not change the monodromy on homology
(`TauCeti.tensorPathChainPointCohomologyEquiv_cohomologyRepresentation_of_commute`,
`TauCeti.tensorPathChainPointCohomologyEquiv_cohomologyRepresentation_addCircle`).

## Main definitions

* `TauCeti.tensorPathChainPointCohomologyEquiv`: the isomorphism `H(M) ≅ H(M ⊗ C_*(P_{a→b} B))`
  induced by `m ↦ m ⊗ [δ]`.

## Main results

* `TauCeti.tensorPathChainPoint_op_smul_eq_op_smul_add_differential`: the chain-level comparison of
  the two actions.
* `TauCeti.tensorPathChainPointCohomologyEquiv_cohomologyRepresentation`: the isomorphism carries
  the action of `δ ⋆ λ ⋆ δ⁻¹` to the action of `λ`.
* `TauCeti.tensorPathChainPointCohomologyEquiv_cohomologyRepresentation_of_commute`,
  `TauCeti.tensorPathChainPointCohomologyEquiv_cohomologyRepresentation_addCircle`: along a loop
  whose class is central, in particular on the circle, the isomorphism intertwines the actions of
  the fundamental group.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §6.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.1, Proposition 1.5
  (the change-of-basepoint isomorphism `β_h` of the fundamental group).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite BalancedTensorProduct DGRightModuleCat

universe u v w

section BasepointChange

variable {B : Type u} [TopologicalSpace B] {a b : B}

section Equiv

variable {R : Type w} [CommRing R]
  (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) (δ : MoorePathBetween B a b)

/-- **The two actions on `M ⊗ C_*(P_{a→b} B)` agree up to a boundary.** For a cycle `m` of `M`
and a Moore loop `λ` at `b`, tensoring with `[δ]` carries the action of the loop
`δ ⋆ λ ⋆ δ⁻¹` at `a` on `m` to the action of `λ` on `m ⊗ [δ]`, up to the boundary of the
retracting homotopy `TauCeti.tensorPathChainHomotopy`. -/
theorem tensorPathChainPoint_op_smul_eq_op_smul_add_differential (l : MooreLoopSpace B b)
    {m : M} (hm : M.differential m = 0) :
    tensorPathChainPoint M δ
        (op (cubicalChainPoint (MooreLoopSpace B a) R
          ((MoorePathBetween.loopAppendHomotopyEquiv δ).symm (op l • δ))) • m) =
      op (cubicalChainPoint (MooreLoopSpace B b) R l) • tensorPathChainPoint M δ m +
        (tensorBimoduleObj M (pathChainBimodule B a b R)).differential
          (tensorPathChainHomotopy M δ
            (op (cubicalChainPoint (MooreLoopSpace B b) R l) • tensorPathChainPoint M δ m)) := by
  -- The action of `λ` on `m ⊗ [δ]` is `m ⊗ [δ ⋆ λ]`.
  have hz : op (cubicalChainPoint (MooreLoopSpace B b) R l) • tensorPathChainPoint M δ m =
      tmul R (loopChainAlgebra B a R) m (pathChainPoint R (op l • δ)) := by
    rw [tensorPathChainPoint_apply, smul_tmul_right, pathChainPoint_def, pathChainPoint_def,
      ← cubicalChainModulePoint_def, ← cubicalChainModulePoint_def,
      op_cubicalChainPoint_smul_cubicalChainModulePoint]
  -- It is a cycle, since `m`, `[δ]` and `[λ]` are.
  have hdz : (tensorBimoduleObj M (pathChainBimodule B a b R)).differential
      (op (cubicalChainPoint (MooreLoopSpace B b) R l) • tensorPathChainPoint M δ m) = 0 :=
    IsDGRightModule.map_op_smul_eq_zero_of_map_eq_zero
      (tensorBimoduleObj M (pathChainBimodule B a b R)).isDGRightModule
      (cubicalChainDifferential_cubicalChainPoint l)
      (by rw [differential_tensorPathChainPoint, hm, map_zero])
  have h := tensorPathChainPoint_tensorPathChainAct δ
    (op (cubicalChainPoint (MooreLoopSpace B b) R l) • tensorPathChainPoint M δ m)
  rw [hdz, map_zero, add_zero] at h
  rw [← h, hz, tensorPathChainAct_tmul, pathChainToLoopChain_pathChainPoint]

/-- **Changing the basepoint along a path, on homology**: tensoring with the `0`-chain of a Moore
path `δ` from `a` to `b`, `m ↦ m ⊗ [δ]`, induces an isomorphism
`H(M) ≅ H(M ⊗ C_*(P_{a→b} B))`, linear over the ground ring. Its inverse is induced by
`m ⊗ c ↦ m · ρ(c)`, where `ρ` appends the reversal of `δ`. -/
def tensorPathChainPointCohomologyEquiv :
    M.isDGRightModule.Cohomology ≃ₗ[R]
      (tensorBimoduleObj M (pathChainBimodule B a b R)).isDGRightModule.Cohomology :=
  M.isDGRightModule.cohomologyEquivHomology ≪≫ₗ
    LinearMap.homologyEquivOfHomotopy (tensorPathChainPoint M δ) (tensorPathChainAct M δ)
      M.isDGRightModule.comp_self_eq_zero
      (tensorBimoduleObj M (pathChainBimodule B a b R)).isDGRightModule.comp_self_eq_zero
      (LinearMap.ext fun m ↦ (differential_tensorPathChainPoint δ m).symm)
      (LinearMap.ext fun z ↦ (differential_tensorPathChainAct δ z).symm)
      (by
        obtain ⟨K, hK⟩ := exists_tensorPathChainAct_tensorPathChainPoint M δ
        exact ⟨K, LinearMap.ext fun m ↦ by simp [hK, add_assoc]⟩)
      ⟨tensorPathChainHomotopy M δ, LinearMap.ext fun z ↦ by
        rw [LinearMap.sub_apply, LinearMap.comp_apply, tensorPathChainPoint_tensorPathChainAct]
        simp [add_assoc]⟩ ≪≫ₗ
    (tensorBimoduleObj M (pathChainBimodule B a b R)).isDGRightModule.cohomologyEquivHomology.symm

/-- The isomorphism sends the class of a cycle `m` to the class of `m ⊗ [δ]`. -/
@[simp]
theorem tensorPathChainPointCohomologyEquiv_mk (z : M.isDGRightModule.cycles) :
    tensorPathChainPointCohomologyEquiv M δ (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨tensorPathChainPoint M δ z, by
        rw [IsDGRightModule.mem_cycles, differential_tensorPathChainPoint,
          M.isDGRightModule.mem_cycles.mp z.property, map_zero]⟩ := by
  simp only [tensorPathChainPointCohomologyEquiv, LinearEquiv.trans_apply,
    IsDGRightModule.cohomologyEquivHomology_mk, LinearMap.homologyEquivOfHomotopy_apply,
    LinearMap.homologyMap_mk, IsDGRightModule.cohomologyEquivHomology_symm_mk]

/-- The inverse isomorphism sends the class of a cycle `z` of `M ⊗ C_*(P_{a→b} B)` to the class
of its image under `m ⊗ c ↦ m · ρ(c)`. -/
@[simp]
theorem tensorPathChainPointCohomologyEquiv_symm_mk
    (z : (tensorBimoduleObj M (pathChainBimodule B a b R)).isDGRightModule.cycles) :
    (tensorPathChainPointCohomologyEquiv M δ).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨tensorPathChainAct M δ z, by
        rw [IsDGRightModule.mem_cycles, differential_tensorPathChainAct,
          (tensorBimoduleObj M (pathChainBimodule B a b R)).isDGRightModule.mem_cycles.mp
            z.property, map_zero]⟩ := by
  simp only [tensorPathChainPointCohomologyEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, IsDGRightModule.cohomologyEquivHomology_mk,
    LinearMap.homologyEquivOfHomotopy_symm_apply, LinearMap.homologyMap_mk,
    IsDGRightModule.cohomologyEquivHomology_symm_mk]

end Equiv

section Representation

variable {R : Type u} [CommRing R] (M : DGRightModuleCat.{u, u, v} (loopChain_isDGAlgebra B a R))
  (δ : MoorePathBetween B a b)

/-- **Changing the basepoint conjugates the monodromy.** Along a Moore path `δ` from `a` to `b`,
the isomorphism `H(M) ≅ H(M ⊗ C_*(P_{a→b} B))` induced by `m ↦ m ⊗ [δ]` carries the action of
the loop `δ ⋆ λ ⋆ δ⁻¹` at `a` to the action of the loop `λ` at `b`, for every Moore loop `λ` at
`b`. In the convention of `TauCeti.IsDGRightModule.cohomologyRepresentation`, a loop acts through
the inverse of its class. As the classes of Moore loops exhaust the fundamental group
(`TauCeti.MooreLoopSpace.fundamentalGroupHom_surjective`), this determines the representation
of `π₁(B, b)` on `H(M ⊗ C_*(P_{a→b} B))`. -/
theorem tensorPathChainPointCohomologyEquiv_cohomologyRepresentation (l : MooreLoopSpace B b)
    (x : M.isDGRightModule.Cohomology) :
    tensorPathChainPointCohomologyEquiv M δ
        (M.isDGRightModule.cohomologyRepresentation (MooreLoopSpace.fundamentalGroupHom a
          ((MoorePathBetween.loopAppendHomotopyEquiv δ).symm (op l • δ)))⁻¹ x) =
      (tensorBimoduleObj M (pathChainBimodule B a b R)).isDGRightModule.cohomologyRepresentation
        (MooreLoopSpace.fundamentalGroupHom b l)⁻¹
        (tensorPathChainPointCohomologyEquiv M δ x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    rw [IsDGRightModule.cohomologyRepresentation_fundamentalGroupHom_inv_apply,
      IsDGRightModule.cohomologyRepresentation_fundamentalGroupHom_inv_apply,
      ← Submodule.Quotient.mk_smul, tensorPathChainPointCohomologyEquiv_mk,
      tensorPathChainPointCohomologyEquiv_mk, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq, IsDGRightModule.mem_boundaries]
    refine ⟨tensorPathChainHomotopy M δ
      (op (cubicalChainPoint (MooreLoopSpace B b) R l) • tensorPathChainPoint M δ z), ?_⟩
    -- The cycles of the loop chains act through their underlying chains.
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    exact eq_sub_of_add_eq' (tensorPathChainPoint_op_smul_eq_op_smul_add_differential M δ l
      (M.isDGRightModule.mem_cycles.mp z.property)).symm

/-- **Changing the basepoint along a loop whose class is central does not change the monodromy.**
For a Moore loop `γ` at `a`, read as a Moore path from `a` to itself, and a class `g` of
`π₁(B, a)` commuting with the class of `γ`, the isomorphism `H(M) ≅ H(M ⊗ C_*(P_{a→a} B))`
induced by `m ↦ m ⊗ [γ]` intertwines the actions of `g`. This applies to every `g` when the
fundamental group is commutative, as for the circle. -/
theorem tensorPathChainPointCohomologyEquiv_cohomologyRepresentation_of_commute
    (γ : MoorePathBetween B a a) {g : FundamentalGroup B a}
    (hg : Commute
      (MooreLoopSpace.fundamentalGroupHom a ((MoorePathBetween.loopHomeomorph a).symm γ)) g)
    (x : M.isDGRightModule.Cohomology) :
    tensorPathChainPointCohomologyEquiv M γ (M.isDGRightModule.cohomologyRepresentation g x) =
      (tensorBimoduleObj M (pathChainBimodule B a a R)).isDGRightModule.cohomologyRepresentation g
        (tensorPathChainPointCohomologyEquiv M γ x) := by
  obtain ⟨l, hl⟩ := MooreLoopSpace.fundamentalGroupHom_surjective a g⁻¹
  have hc : MooreLoopSpace.fundamentalGroupHom a
      ((MoorePathBetween.loopAppendHomotopyEquiv γ).symm (op l • γ)) = g⁻¹ := by
    rw [MoorePathBetween.fundamentalGroupHom_loopAppendHomotopyEquiv_symm_op_smul, hl,
      (hg.inv_right).eq, mul_inv_cancel_right]
  have h := tensorPathChainPointCohomologyEquiv_cohomologyRepresentation M γ l x
  rwa [hc, hl, inv_inv] at h

end Representation

section Circle

variable {p : ℝ} [Fact (0 < p)] {x₀ : AddCircle p} {S : Type} [CommRing S]

/-- **On the circle, changing the basepoint along a loop does not change the monodromy**: the
fundamental group of the circle is commutative (it is `ℤ` through the winding number,
`AddCircle.windingNumberIso`), so for every Moore loop `γ` at `x₀` the isomorphism
`H(M) ≅ H(M ⊗ C_*(P_{x₀→x₀} S¹))` induced by `m ↦ m ⊗ [γ]` intertwines the actions of
`π₁(S¹, x₀)`. -/
theorem tensorPathChainPointCohomologyEquiv_cohomologyRepresentation_addCircle
    (M : DGRightModuleCat.{0, 0, v} (loopChain_isDGAlgebra (AddCircle p) x₀ S))
    (γ : MoorePathBetween (AddCircle p) x₀ x₀) (g : FundamentalGroup (AddCircle p) x₀)
    (x : M.isDGRightModule.Cohomology) :
    tensorPathChainPointCohomologyEquiv M γ (M.isDGRightModule.cohomologyRepresentation g x) =
      (tensorBimoduleObj M
        (pathChainBimodule (AddCircle p) x₀ x₀ S)).isDGRightModule.cohomologyRepresentation g
        (tensorPathChainPointCohomologyEquiv M γ x) :=
  tensorPathChainPointCohomologyEquiv_cohomologyRepresentation_of_commute M γ (g := g)
    ((AddCircle.windingNumberIso x₀).injective (by rw [map_mul, map_mul, mul_comm])) x

end Circle

end BasepointChange

end TauCeti
