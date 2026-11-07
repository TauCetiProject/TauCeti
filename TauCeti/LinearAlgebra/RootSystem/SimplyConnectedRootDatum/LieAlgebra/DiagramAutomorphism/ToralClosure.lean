/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.NumberedSymmetry
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.NumberedSymmetry
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity

/-!
# Diagram automorphisms of the full-weight toral closure

The integral toral closure in the full-weight representation carries the action of the
Bourbaki-numbered Dynkin diagram. This file descends the existing lattice automorphisms
`TauCeti.DynkinType.scModuleDiagramEquiv` to that group scheme. The construction acts on the
native Kostant toral closure itself; no separate group carrier is introduced.

The root maps at the positive and negative simple roots are permuted without changing their
parameters. The weight torus is relabelled contragrediently. These two equations also determine
the automorphism, and imply the identity, composition and inverse laws. In particular the
construction gives an action of the entire diagram symmetry group, not just a choice of an
individual graph automorphism.

The descent uses preservation of weight components, not a permutation of the weight basis.
Consequently it applies even when a diagram symmetry acts non-monomially on a weight space of
a fundamental representation.

## Main declarations

* `TauCeti.DynkinType.scToralDiagramAut`: the descended diagram automorphism.
* `TauCeti.DynkinType.scToralDiagramAutHom`: the action bundled as a group homomorphism.
* `TauCeti.DynkinType.scToralDiagramAut_pow_eq_one`: every order relation of the node permutation
  holds on the group scheme.
* `TauCeti.DynkinType.scToralDiagramAutPoints`: conjugation on all algebra-valued points,
  with matrix formulas, value-ring naturality, order laws and root-subgroup and weight-torus
  action formulas. These point-level constructions do not require generation by root subgroups.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.15–1.17.

The descent uses `kostantToralNumberedSymmetryIso`; the representation and weight-component
compatibility are supplied by the existing full-weight numbered-symmetry construction.
-/

public section

namespace TauCeti.DynkinType

section Points

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
  -- Compute on matrices so the point-action API does not depend on the character-map layer.
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
end Points

open _root_.CategoryTheory _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable {t : DynkinType} (ht : t.Valid) {σ τ : Equiv.Perm (Fin t.rank)}

/-- The diagram automorphism of the integral toral closure in the full-weight representation.
It descends the lattice automorphism `scModuleDiagramEquiv`, using preservation of weight
components rather than a monomial action on the weight basis. -/
def scToralDiagramAut (hσ : σ ∈ t.diagramSymmetry) :
    Aut (kostantToralGroupScheme (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht)) :=
  kostantToralNumberedSymmetryIso _ _ _ _ _ _ _ _ (diagramRootGeneratorPerm σ)
    (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
    (t.scModuleDiagramEquiv_representation_rootGenerator ht hσ)
    (diagramRootGeneratorPerm σ).surjective σ
    (fun _ _ hxy => t.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero ht hσ hxy)

/-- On the numbered positive and negative simple root maps the diagram automorphism only
renumbers the root, leaving its additive parameter unchanged. -/
@[simp]
theorem kostantRootSubgroupToToral_comp_scToralDiagramAut_hom (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank ⊕ Fin t.rank) :
    kostantRootSubgroupToToral (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) i ≫ (t.scToralDiagramAut ht hσ).asIso.hom =
      kostantRootSubgroupToToral (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) (diagramRootGeneratorPerm σ i) :=
  kostantRootSubgroupToToral_comp_numberedSymmetryIso_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i

/-- The diagram automorphism acts on the full-weight torus by inverse relabelling of its
parameters, the pullback convention for characters. -/
@[simp]
theorem kostantWeightTorusToToral_comp_scToralDiagramAut_hom (hσ : σ ∈ t.diagramSymmetry) :
    kostantWeightTorusToToral (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) ≫ (t.scToralDiagramAut ht hσ).asIso.hom =
      SplitTorus.relabel ℤ σ⁻¹ ≫
        kostantWeightTorusToToral (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) :=
  kostantWeightTorusToToral_comp_numberedSymmetryIso_hom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The identity diagram symmetry induces the identity of the integral toral closure. -/
@[simp]
theorem scToralDiagramAut_one :
    t.scToralDiagramAut ht t.diagramSymmetry.one_mem = 1 := by
  apply Aut.ext
  apply Iso.ext
  apply kostantToralGroupScheme_hom_ext
  · intro i
    cases i <;> simp
  · simp

/-- Diagram automorphisms of the integral toral closure form an action: the lift of `σ * τ`
is the composite of the lifts of `τ` and `σ`. -/
@[simp]
theorem scToralDiagramAut_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry) :
    t.scToralDiagramAut ht (t.diagramSymmetry.mul_mem hσ hτ) =
      t.scToralDiagramAut ht hσ * t.scToralDiagramAut ht hτ := by
  apply Aut.ext
  apply Iso.ext
  apply kostantToralGroupScheme_hom_ext
  · intro i
    simp only [Aut.mul_asIso, Iso.trans_hom, ← Category.assoc,
      kostantRootSubgroupToToral_comp_scToralDiagramAut_hom]
    cases i <;> simp
  · simp only [Aut.mul_asIso, Iso.trans_hom, ← Category.assoc,
      kostantWeightTorusToToral_comp_scToralDiagramAut_hom]
    have h := congrArg (fun f => SplitTorus.relabel ℤ τ⁻¹ ≫ f)
      (t.kostantWeightTorusToToral_comp_scToralDiagramAut_hom ht hσ)
    simpa only [← Category.assoc, SplitTorus.relabel_comp, mul_inv_rev] using h.symm

/-- The action of the diagram symmetry group on the full-weight integral toral closure,
bundled as a group homomorphism. -/
def scToralDiagramAutHom :
    t.diagramSymmetry →*
      Aut (kostantToralGroupScheme (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht)
      (t.scWeightBasis ht) (t.scWeight ht)) where
  toFun g := t.scToralDiagramAut ht g.2
  map_one' := t.scToralDiagramAut_one ht
  map_mul' g₁ g₂ := t.scToralDiagramAut_mul ht g₁.2 g₂.2

/-- Evaluation of the bundled diagram action is the descended diagram automorphism. -/
theorem scToralDiagramAutHom_apply (g : t.diagramSymmetry) :
    t.scToralDiagramAutHom ht g = t.scToralDiagramAut ht g.2 :=
  (rfl)

/-- Inverting a diagram symmetry inverts its descended automorphism. -/
@[simp]
theorem scToralDiagramAut_inv (hσ : σ ∈ t.diagramSymmetry) :
    t.scToralDiagramAut ht (t.diagramSymmetry.inv_mem hσ) = (t.scToralDiagramAut ht hσ)⁻¹ :=
  map_inv (t.scToralDiagramAutHom ht) ⟨σ, hσ⟩

/-- Every order relation of a diagram permutation holds on the integral toral closure. -/
theorem scToralDiagramAut_pow_eq_one (hσ : σ ∈ t.diagramSymmetry) (m : ℕ)
    (hσm : σ ^ m = 1) : (t.scToralDiagramAut ht hσ) ^ m = 1 := by
  have h : (⟨σ, hσ⟩ : t.diagramSymmetry) ^ m = 1 := Subtype.ext (by simpa using hσm)
  calc t.scToralDiagramAut ht hσ ^ m = t.scToralDiagramAutHom ht (⟨σ, hσ⟩ ^ m) :=
        (map_pow (t.scToralDiagramAutHom ht) ⟨σ, hσ⟩ m).symm
    _ = 1 := (congrArg (t.scToralDiagramAutHom ht) h).trans (map_one _)

end

end TauCeti.DynkinType
