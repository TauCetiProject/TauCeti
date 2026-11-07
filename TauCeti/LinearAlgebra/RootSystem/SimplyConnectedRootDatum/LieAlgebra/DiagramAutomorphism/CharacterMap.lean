/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.CharacterMap
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.NumberedSymmetry
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.DiagramAutomorphism

/-!
# Character maps of the full-weight diagram action

For the integral full-weight lattice, conjugation by `scModuleDiagramEquiv` acts on all points
of its Kostant toral closure through `scToralDiagramAutPoints`. Its character pullback on the
represented weight torus is the weight map of the inverse root-datum diagram automorphism.
The action is natural in the value ring, inherits the order of the diagram symmetry, and
renumbers the pinned root subgroups and weight-torus coordinates.
To compute the pullback of its composite with Frobenius, combine
`isCharacterMap_scToralDiagramAutPoints` with `isCharacterMap_kostantToralFrobenius` via
`IsCharacterMap.comp`, obtaining `p ^ k • (diagramAut σ)⁻¹.weightMap`.

The proof specializes the weight-component compatibility of `scModuleDiagramEquiv` and the
generic toral-closure character-map theorem. In particular it does not require the diagram
action to permute the weight basis, nor generation of the point group by root subgroups.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v v'

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} (ht : t.Valid) {σ : Equiv.Perm (Fin t.rank)}

/-- The diagram automorphism on all points of the full-weight Kostant toral closure, given by
conjugation by the scalar extension of `scModuleDiagramEquiv` on the lattice. -/
noncomputable def scToralDiagramAutPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    MulAut (kostantToralPointsSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht) A) :=
  kostantNumberedSymmetryPoints (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
    (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
    A _ (map_kostantToralPointsSubgroup_conj_numberedSymmetryMatrix
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht) (diagramRootGeneratorPerm σ)
      (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
      (t.scModuleDiagramEquiv_representation_rootGenerator ht hσ)
      (diagramRootGeneratorPerm σ).surjective σ
      (fun _ _ hxy => t.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero ht hσ hxy)
      A)

/-- On matrices, the full-weight diagram action is conjugation by its lattice symmetry matrix. -/
@[simp]
theorem coe_scToralDiagramAutPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A]
    (g : kostantToralPointsSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht) A) :
    (t.scToralDiagramAutPoints ht hσ A g :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A * g *
      (kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A)⁻¹ :=
  coe_kostantNumberedSymmetryPoints _ _ _ _ A _ _ g

/-- On matrices, the inverse full-weight diagram action is conjugation by the inverse lattice
symmetry matrix. -/
@[simp]
theorem coe_scToralDiagramAutPoints_symm (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A]
    (g : kostantToralPointsSubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht) A) :
    ((t.scToralDiagramAutPoints ht hσ A).symm g :
        Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      (kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A)⁻¹ * g *
      kostantNumberedSymmetryMatrix (t.scLattice ht).toAddSubgroup (t.scWeightBasis ht)
        (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
        A :=
  coe_kostantNumberedSymmetryPoints_symm _ _ _ _ A _ _ g

/-- The full-weight diagram action is natural in the value ring. In particular it commutes
with Frobenius. -/
theorem map_comp_scToralDiagramAutPoints (hσ : σ ∈ t.diagramSymmetry)
    {A : Type v} {B : Type v'} [CommRing A] [CommRing B] (f : A →+* B) :
    ((kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A).map
      (kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) B) f).comp
      (t.scToralDiagramAutPoints ht hσ A).toMonoidHom =
    (t.scToralDiagramAutPoints ht hσ B).toMonoidHom.comp
      ((kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A).map
      (kostantToralPointsPresentation (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) B) f) :=
  comp_kostantNumberedSymmetryPoints _ _ _ _ _ _ _ _ f _
    (GeneralLinear.IntegralPointsPresentation.coe_map _ _ f)

/-- The order of the full-weight diagram action divides the order of its diagram symmetry. -/
@[simp]
theorem scToralDiagramAutPoints_pow_eq_one (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] {m : ℕ} (hm : σ ^ m = 1) :
    t.scToralDiagramAutPoints ht hσ A ^ m = 1 := by
  -- Package the module composition law to transport the diagram's order relation.
  let θ : t.diagramSymmetry →* (t.scModule ht ≃ₗ[ℚ] t.scModule ht) :=
    { toFun := fun s => t.scModuleDiagramEquiv ht s.property
      map_one' := t.scModuleDiagramEquiv_one ht
      map_mul' := fun s r => t.scModuleDiagramEquiv_mul ht s.property r.property }
  have hm' : (⟨σ, hσ⟩ : t.diagramSymmetry) ^ m = 1 := Subtype.ext hm
  have hθ : (t.scModuleDiagramEquiv ht hσ) ^ m = 1 := by
    -- Unfold only the local hom's application: rewriting the full module term times out.
    change θ ⟨σ, hσ⟩ ^ m = 1
    exact (θ.map_pow ⟨σ, hσ⟩ m).symm.trans ((congrArg θ hm').trans θ.map_one)
  exact kostantNumberedSymmetryPoints_pow_eq_one _ _ _ _ A _ _
    (kostantNumberedSymmetryMatrix_pow_eq_one _ _ _ _ A
      (fun x => by rw [hθ]; rfl))

/-- The identity diagram symmetry acts identically on full-weight toral-closure points. -/
@[simp]
theorem scToralDiagramAutPoints_one (A : Type v) [CommRing A] :
    t.scToralDiagramAutPoints ht t.diagramSymmetry.one_mem A = 1 := by
  simpa using scToralDiagramAutPoints_pow_eq_one ht t.diagramSymmetry.one_mem A
    (m := 1) (pow_one _)

/-- The full-weight diagram action renumbers the pinned root subgroups without changing their
additive parameters. -/
@[simp]
theorem scToralDiagramAutPoints_kostantToralRootSubgroupPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (i : Fin t.rank ⊕ Fin t.rank) (u : Multiplicative A) :
    t.scToralDiagramAutPoints ht hσ A
      (kostantToralRootSubgroupPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) i A u) =
    kostantToralRootSubgroupPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht) (diagramRootGeneratorPerm σ i) A u := by
  apply Subtype.ext
  simp only [coe_scToralDiagramAutPoints, coe_kostantToralRootSubgroupPoints]
  exact kostantNumberedSymmetryMatrix_conj_kostantRootSubgroupMatrix _ _ _ _ _ _ _
    (diagramRootGeneratorPerm σ) _ _
    (t.scModuleDiagramEquiv_representation_rootGenerator ht hσ) A i _

/-- On the full-weight toral closure, the pinned diagram action has character pullback equal
to the weight map of the inverse diagram automorphism of the simply connected root datum. -/
theorem isCharacterMap_scToralDiagramAutPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] :
    IsCharacterMap
      (kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A)
      (t.scToralDiagramAutPoints ht hσ A).toMonoidHom
      (diagramAut ht hσ)⁻¹.toHom.weightMap := by
  have h := isCharacterMap_kostantNumberedSymmetryPoints
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
    (t.kostantForm_apply_mem_scLattice ht)
    (t.isNilpotent_representation_scModule_rootGenerator ht)
    (t.scWeightBasis ht) (t.scWeight ht) (diagramRootGeneratorPerm σ)
    (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
    (t.scModuleDiagramEquiv_representation_rootGenerator ht hσ)
    (diagramRootGeneratorPerm σ).surjective σ
    (fun _ _ hxy => t.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero ht hσ hxy) A
  have hφ : (diagramAut ht hσ)⁻¹.toHom.weightMap = LinearMap.funLeft ℤ ℤ σ := by
    rw [diagramAut_inv_weightMap]
    apply LinearMap.ext
    intro x
    exact LinearEquiv.funCongrLeft_apply ℤ ℤ σ x
  -- Transport only the character-map argument: rewriting the whole specialized point action
  -- with `rw [hφ]` causes an elaboration timeout.
  apply (congrArg (IsCharacterMap _ _) hφ).mpr
  exact h

/-- The full-weight diagram action relabels weight-torus coordinates by the inverse symmetry. -/
@[simp]
theorem scToralDiagramAutPoints_kostantToralWeightTorusPoints (hσ : σ ∈ t.diagramSymmetry)
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) :
    t.scToralDiagramAutPoints ht hσ A
      (kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) A s) =
    kostantToralWeightTorusPoints (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht) A (fun k => s (σ⁻¹ k)) := by
  apply Subtype.ext
  simp only [coe_scToralDiagramAutPoints, coe_kostantToralWeightTorusPoints,
    kostantTorusMatrix_apply]
  apply kostantNumberedSymmetryMatrix_conj_diagGL
  intro i j hij
  have hwt : t.scWeight ht i ∘ σ = t.scWeight ht j :=
    funext (t.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero ht hσ hij)
  have hs : MulEquiv.arrowCongr σ (MulEquiv.refl Aˣ) s = fun k => s (σ⁻¹ k) := by
    funext k
    simp only [MulEquiv.arrowCongr_apply, MulEquiv.refl_apply, Equiv.Perm.inv_def]
  simpa only [hs, hwt] using torusCharacter_mulEquivArrowCongr σ s (t.scWeight ht i)

end TauCeti.DynkinType
