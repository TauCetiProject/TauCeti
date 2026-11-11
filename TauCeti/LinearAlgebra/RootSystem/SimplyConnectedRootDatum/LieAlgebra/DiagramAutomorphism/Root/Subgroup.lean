/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.ToralClosure
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup

/-!
# Diagram action on every root subgroup

Conjugation by a lattice symmetry intertwining the diagram action sends the divided-power
exponential at a root to that at its diagram image, with parameter multiplied by
`chevalleyDiagramSign`. Unlike at simple roots, this sign need not be one. The formula holds
on any Kostant-stable lattice with nilpotent simple-root actions, over every commutative value
ring. Its matrix form holds in any lattice basis.

Specializing to the integral full-weight diagram symmetry gives
`scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints`, the all-root action on the simply
connected Chevalley point group. No generation hypothesis on the point group is needed.

The Lie-level formula `diagramLieEquiv_chevalleySystem` supplies the signs; the integral
intertwining theorem for nilpotent exponentials carries it to the base-changed lattice.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
-/

public section

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra AddEquiv

noncomputable section

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} (ht : t.Valid) {σ : Equiv.Perm (Fin t.rank)}

section Lattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ _root_.TauCeti.UniversalEnvelopingAlgebra.kostantForm
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

/-- A lattice symmetry intertwining the diagram action conjugates every root subgroup with
exactly the sign of the action on the named Chevalley root vector. -/
theorem baseChangeInvariantRestrictUnit_conj_chevalleyRootSubgroup
    (hσ : σ ∈ t.diagramSymmetry) (θ : V ≃ₗ[ℚ] V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M)
    (hθ : ∀ x v, θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.diagramLieEquiv ht hσ x)) (θ v))
    (α : Fin t.numRoots) (A : CommAlgCat.{v} ℤ) (u : A) :
    baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM *
      chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u) *
      (baseChangeInvariantRestrictUnit (R := A) θ.toAddEquiv M hθM)⁻¹ =
    chevalleyRootSubgroup ρ M hM hnil (t.diagramRootPerm ht hσ α) A
      (Multiplicative.ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u)) := by
  let β := t.diagramRootPerm ht hσ α
  let c : ℤ := t.chevalleyDiagramSign ht hσ α
  have hint (v : V) :
      θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht α)) • v) =
        (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht β))) • θ v := by
    simpa only [c, β, map_zsmul, Module.End.smul_def, LinearMap.smul_apply] using
      (hθ (t.chevalleySystem ht α) v).trans
        (congrArg (fun x => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) (θ v))
          (t.diagramLieEquiv_chevalleySystem ht hσ α))
  have hscaled := dividedPower_zsmul_chevalleySystem_smul_mem ρ M hM hnil c β
  have hn := isNilpotent_apply_ι_chevalleySystem ρ hnil
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  apply LinearMap.ext
  intro z
  simp only [Units.val_mul, mul_apply_eq_comp,
    val_baseChangeInvariantRestrictUnit_apply, chevalleyRootSubgroup_val, toAdd_ofAdd]
  exact (θ.baseChange_invariantRestrict_baseChangeExp M hθM hint
    (dividedPower_chevalleySystem_smul_mem ρ M hM hnil α) (hn α)
    ((hn β).smul c) u z).trans
      (DFunLike.congr_fun (baseChangeExp_zsmul c M
        (dividedPower_chevalleySystem_smul_mem ρ M hM hnil β) hscaled (hn β) u) _)

end Lattice

section Matrix

variable {V : Type} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (t.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ _root_.TauCeti.UniversalEnvelopingAlgebra.kostantForm
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i))))

/-- In any lattice basis, a symmetry intertwining the diagram action conjugates every root
matrix to the matrix at its diagram image, with the signed parameter. -/
theorem kostantNumberedSymmetryMatrix_conj_chevalleyRootSubgroup
    {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
    (hσ : σ ∈ t.diagramSymmetry) (θ : V ≃ₗ[ℚ] V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M)
    (hθ : ∀ x v, θ (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.diagramLieEquiv ht hσ x)) (θ v))
    (α : Fin t.numRoots) (A : Type v) [CommRing A] (u : A) :
    kostantNumberedSymmetryMatrix M b θ hθM A *
      Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
        (chevalleyRootSubgroup ρ M hM hnil α (CommAlgCat.of ℤ A) (Multiplicative.ofAdd u)) *
      (kostantNumberedSymmetryMatrix M b θ hθM A)⁻¹ =
    Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
      (chevalleyRootSubgroup ρ M hM hnil (t.diagramRootPerm ht hσ α) (CommAlgCat.of ℤ A)
        (Multiplicative.ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u))) := by
  have h := congrArg (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom)
    (t.baseChangeInvariantRestrictUnit_conj_chevalleyRootSubgroup ht ρ M hM hnil
      hσ θ hθM hθ α (CommAlgCat.of ℤ A) u)
  simpa only [map_mul, map_inv, kostantNumberedSymmetryMatrix_def,
    MulEquiv.toMonoidHom_eq_coe] using h

end Matrix

/-- The full-weight diagram action sends every root point to the point at its diagram image,
with parameter multiplied by the sign of the action on its Chevalley root vector. -/
@[simp]
theorem scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints
    (hσ : σ ∈ t.diagramSymmetry) (α : Fin t.numRoots) (A : Type v) [CommRing A] (u : A) :
    t.scToralDiagramAutPoints ht hσ A
      (chevalleyToralRootSubgroupPoints (t := t) (ht := ht)
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) α A (Multiplicative.ofAdd u)) =
    chevalleyToralRootSubgroupPoints (t := t) (ht := ht)
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht) (t.diagramRootPerm ht hσ α) A
      (Multiplicative.ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u)) := by
  apply Subtype.ext
  simp only [coe_scToralDiagramAutPoints, coe_chevalleyToralRootSubgroupPoints]
  apply t.kostantNumberedSymmetryMatrix_conj_chevalleyRootSubgroup ht _ _ _ _
    (t.scWeightBasis ht) hσ (t.scModuleDiagramEquiv ht hσ)
    (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) _ α A u
  intro x v
  simpa only [representation_ι_apply] using t.scModuleDiagramEquiv_lie ht hσ x v

end

end TauCeti.DynkinType
