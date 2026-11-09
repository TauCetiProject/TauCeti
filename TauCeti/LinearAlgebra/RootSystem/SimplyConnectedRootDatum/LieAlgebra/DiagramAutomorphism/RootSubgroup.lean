/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.ToralClosure
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup

/-!
# Diagram action on every full-weight root subgroup

Conjugation by the integral full-weight diagram symmetry sends the divided-power exponential
at a root to that at its diagram image, with parameter multiplied by `chevalleyDiagramSign`.
Unlike at simple roots, this sign need not be one. The formula holds over every commutative
value ring, and supplies the all-root action for the simply connected Chevalley point group.
`kostantNumberedSymmetryMatrix_conj_chevalleyRootSubgroup` gives its matrix form: this is the
conjugation appearing in `coe_scToralDiagramAutPoints`, so it computes that point action on
all root matrices, not just the numbered simple-root generators.

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

/-- On the full-weight lattice, the integral diagram symmetry conjugates every root subgroup
with exactly the sign of its action on the named Chevalley root vector. -/
theorem baseChangeInvariantRestrictUnit_conj_chevalleyRootSubgroup
    (hσ : σ ∈ t.diagramSymmetry) (α : Fin t.numRoots) (A : CommAlgCat.{v} ℤ) (u : A) :
    baseChangeInvariantRestrictUnit (R := A) (t.scModuleDiagramEquiv ht hσ).toAddEquiv
        (t.scLattice ht).toAddSubgroup (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) *
      chevalleyRootSubgroup (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
        (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht) α A (Multiplicative.ofAdd u) *
      (baseChangeInvariantRestrictUnit (R := A) (t.scModuleDiagramEquiv ht hσ).toAddEquiv
        (t.scLattice ht).toAddSubgroup
        (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ))⁻¹ =
    chevalleyRootSubgroup (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
      (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht) (t.diagramRootPerm ht hσ α) A
      (Multiplicative.ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u)) := by
  let ρ := representation ℚ (t.lieAlgebra ht) (t.scModule ht)
  let M := (t.scLattice ht).toAddSubgroup
  let β := t.diagramRootPerm ht hσ α
  let c : ℤ := t.chevalleyDiagramSign ht hσ α
  have hint (v : t.scModule ht) :
      t.scModuleDiagramEquiv ht hσ
          (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht α)) • v) =
        (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht β))) •
          t.scModuleDiagramEquiv ht hσ v := by
    simpa only [ρ, c, β, representation_ι_apply, Module.End.smul_def,
      LinearMap.smul_apply, zsmul_lie] using
      (t.scModuleDiagramEquiv_lie ht hσ (t.chevalleySystem ht α) v).trans
        (congrArg (fun x => ⁅x, t.scModuleDiagramEquiv ht hσ v⁆)
          (t.diagramLieEquiv_chevalleySystem ht hσ α))
  have hn := t.isNilpotent_representation_scModule_rootGenerator ht
  have hM := t.kostantForm_apply_mem_scLattice ht
  have hscaled := dividedPower_zsmul_chevalleySystem_smul_mem ρ M hM hn c β
  have hnil := isNilpotent_apply_ι_chevalleySystem ρ hn
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  apply LinearMap.ext
  intro z
  simp only [Units.val_mul, mul_apply_eq_comp,
    val_baseChangeInvariantRestrictUnit_apply, chevalleyRootSubgroup_val, toAdd_ofAdd]
  exact ((t.scModuleDiagramEquiv ht hσ).baseChange_invariantRestrict_baseChangeExp M
    (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) hint
    (dividedPower_chevalleySystem_smul_mem ρ M hM hn α) (hnil α)
    ((hnil β).smul c) u z).trans
      (DFunLike.congr_fun (baseChangeExp_zsmul c M
        (dividedPower_chevalleySystem_smul_mem ρ M hM hn β) hscaled (hnil β) u) _)

/-- In the full-weight basis, the matrix conjugation defining `scToralDiagramAutPoints`
sends every root matrix to the matrix at its diagram image, with the signed parameter. -/
theorem kostantNumberedSymmetryMatrix_conj_chevalleyRootSubgroup
    (hσ : σ ∈ t.diagramSymmetry) (α : Fin t.numRoots) (A : Type v) [CommRing A] (u : A) :
    kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) A *
      Units.map (LinearMap.toMatrixAlgEquiv ((t.scWeightBasis ht).baseChange A)).toMonoidHom
        (chevalleyRootSubgroup (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
          (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht) α (CommAlgCat.of ℤ A)
          (Multiplicative.ofAdd u)) *
      (kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A)⁻¹ =
    Units.map (LinearMap.toMatrixAlgEquiv ((t.scWeightBasis ht).baseChange A)).toMonoidHom
      (chevalleyRootSubgroup (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
        (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht) (t.diagramRootPerm ht hσ α)
        (CommAlgCat.of ℤ A)
        (Multiplicative.ofAdd (((t.chevalleyDiagramSign ht hσ α : ℤ) : A) * u))) := by
  have h := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv ((t.scWeightBasis ht).baseChange A)).toMonoidHom)
    (t.baseChangeInvariantRestrictUnit_conj_chevalleyRootSubgroup ht hσ α (CommAlgCat.of ℤ A) u)
  simpa only [map_mul, map_inv, kostantNumberedSymmetryMatrix_def,
    MulEquiv.toMonoidHom_eq_coe] using h

end

end TauCeti.DynkinType
