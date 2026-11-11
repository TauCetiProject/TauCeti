/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.NumberedSymmetry
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Symmetry
public import TauCeti.LinearAlgebra.RootSystem.GeckConstruction.PinnedSymmetry
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Module

/-!
# Diagram symmetries as numbered symmetries of the full-weight Kostant data

The full-weight module `V_sc(t) = ⨁ᵢ L(ϖᵢ)` of a valid Dynkin type `t`, with its admissible lattice
`TauCeti.DynkinType.scLattice` and the numbered raising and lowering generators `e_{±i}` of the
pinned rational Lie algebra, is an instance of the Kostant data from which root subgroups, the
elementary group and the toral closure are built over every commutative ring. For a symmetry `σ`
of the Bourbaki-numbered Dynkin diagram, the automorphism `θ_σ` of
`TauCeti.DynkinType.scModuleDiagramEquiv` is a symmetry of these numbered data:

* it preserves the lattice;
* it carries the action of `e_{±i}` to that of `e_{±σ i}`, and the action of the Cartan generator
  `hᵢ` to that of `h_{σ i}`;
* hence it maps the weight-`μ` sublattice of `scLattice` onto the weight-`μ ∘ σ⁻¹` sublattice, so
  that in the weight basis `TauCeti.DynkinType.scWeightBasis` its matrix entries join only weights
  related by `σ`.

The weight spaces of the fundamental modules can have dimension greater than one, and `θ_σ` may act
on a `σ`-stable weight space by a non-monomial integral matrix, so it need not permute the weight
basis. The last item is the weight-compatibility condition under which the generic numbered
symmetry construction descends to the toral closure without such a monomiality assumption.

The first two items are exactly the hypotheses of the generic numbered symmetry construction of
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.NumberedSymmetry`. Applied to them,
it produces the automorphism `TauCeti.DynkinType.scElementaryDiagramAut` of the elementary group of
the full-weight lattice over every commutative ring, conjugation by the scalar extension of `θ_σ`,
which renumbers the root subgroups of the simple roots and their negatives without changing their
parameters:

```text
γ_σ (x_{±i}(u)) = x_{±σ i}(u).
```

It commutes with base change of the value ring and with the Frobenius endomorphism.

## Main definitions

* `TauCeti.DynkinType.scElementaryDiagramAut`: the automorphism `γ_σ` of the elementary group of
  the full-weight lattice.

## Main results

* `TauCeti.DynkinType.scModuleDiagramEquiv_representation_rootGenerator` and
  `TauCeti.DynkinType.scModuleDiagramEquiv_representation_h`: `θ_σ` intertwines the numbered root
  and Cartan generators with the generators renumbered by `σ`.
* `TauCeti.DynkinType.map_weightSublattice_scModuleDiagramEquiv`: `θ_σ` maps the weight-`μ`
  sublattice of `scLattice` onto the weight-`μ ∘ σ⁻¹` sublattice.
* `TauCeti.DynkinType.scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero`: the corresponding
  support condition on the matrix of `θ_σ` in the weight basis.
* `TauCeti.DynkinType.scElementaryDiagramAut_kostantRootSubgroupParam`: the pinning equation
  `γ_σ (x_{±i}(u)) = x_{±σ i}(u)`.
* `TauCeti.DynkinType.kostantElementaryMap_scElementaryDiagramAut` and
  `TauCeti.DynkinType.kostantElementaryFrobenius_scElementaryDiagramAut`: compatibility with base
  change and with Frobenius.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 10, Theorem 29.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
-/

public section

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra CategoryTheory

noncomputable section

universe w

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} (ht : t.Valid) {σ : Equiv.Perm (Fin t.rank)}

/-! ### Intertwining the numbered generators -/

/-- `θ_σ` carries the action of a Lie algebra element `x`, read through the enveloping algebra, to
the action of its image `y` under the diagram automorphism. -/
private theorem scModuleDiagramEquiv_representation_ι (hσ : σ ∈ t.diagramSymmetry)
    {x y : t.lieAlgebra ht} (hxy : t.diagramLieEquiv ht hσ x = y) (v : t.scModule ht) :
    t.scModuleDiagramEquiv ht hσ
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v) =
      representation ℚ (t.lieAlgebra ht) (t.scModule ht)
        (_root_.UniversalEnvelopingAlgebra.ι ℚ y) (t.scModuleDiagramEquiv ht hσ v) := by
  -- Rewriting under `representation` on the direct sum is slow, so the image `y` is substituted
  -- and the module arguments of `representation_ι_apply` are given explicitly.
  subst hxy
  simp only [representation_ι_apply ℚ (t.lieAlgebra ht) (t.scModule ht)]
  exact scModuleDiagramEquiv_lie ht hσ x v

/-- **`θ_σ` intertwines each numbered raising or lowering generator with the generator renumbered
by `σ`**, in the form in which the numbered symmetry constructions take this hypothesis. -/
theorem scModuleDiagramEquiv_representation_rootGenerator (hσ : σ ∈ t.diagramSymmetry)
    (i : Fin t.rank ⊕ Fin t.rank) (v : t.scModule ht) :
    t.scModuleDiagramEquiv ht hσ
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator i)) v) =
      representation ℚ (t.lieAlgebra ht) (t.scModule ht)
        (_root_.UniversalEnvelopingAlgebra.ι ℚ
          ((t.lieBasis ht).rootGenerator (diagramRootGeneratorPerm σ i)))
        (t.scModuleDiagramEquiv ht hσ v) :=
  scModuleDiagramEquiv_representation_ι ht hσ (by cases i <;> simp) v

/-- **`θ_σ` intertwines each Cartan generator `hᵢ` with `h_{σ i}`.** -/
theorem scModuleDiagramEquiv_representation_h (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank)
    (v : t.scModule ht) :
    t.scModuleDiagramEquiv ht hσ
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)
          (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).h i)) v) =
      representation ℚ (t.lieAlgebra ht) (t.scModule ht)
        (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).h (σ i)))
        (t.scModuleDiagramEquiv ht hσ v) :=
  scModuleDiagramEquiv_representation_ι ht hσ (diagramLieEquiv_lieBasis_h ht hσ i) v

/-! ### Weight components -/

/-- **`θ_σ` maps the weight-`μ` sublattice of the full-weight lattice onto the weight-`μ ∘ σ⁻¹`
sublattice**, for the weights read on the Cartan generators `hⱼ`. -/
theorem map_weightSublattice_scModuleDiagramEquiv (hσ : σ ∈ t.diagramSymmetry)
    (μ : Fin t.rank → ℤ) :
    (weightSublattice (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
        (t.scLattice ht).toAddSubgroup μ).map
      ((t.scModuleDiagramEquiv ht hσ).toAddEquiv.invariantRestrict (t.scLattice ht).toAddSubgroup
        (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)).toLinearMap =
      weightSublattice (t.lieBasis ht).h (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
        (t.scLattice ht).toAddSubgroup (μ ∘ σ.symm) :=
  map_weightSublattice_invariantRestrict _ _ _ _ _ σ (scModuleDiagramEquiv_representation_h ht hσ) μ

/-- **In the weight basis of the full-weight lattice, `θ_σ` only joins weights related by `σ`**:
if the `x`-th coordinate of the image of the `y`-th basis vector is nonzero, then the weight of the
`x`-th vector at `σ k` is that of the `y`-th vector at `k`. This is the weight-compatibility
condition of the numbered symmetry of the toral closure, with torus permutation `σ`. -/
theorem scWeight_apply_eq_of_repr_scModuleDiagramEquiv_ne_zero (hσ : σ ∈ t.diagramSymmetry)
    {x y : Fin (t.scWeightBasisCard ht)}
    (hxy : (t.scWeightBasis ht).repr
      ((t.scModuleDiagramEquiv ht hσ).toAddEquiv.invariantRestrict (t.scLattice ht).toAddSubgroup
        (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) (t.scWeightBasis ht y)) x ≠ 0)
    (k : Fin t.rank) :
    t.scWeight ht x (σ k) = t.scWeight ht y k :=
  weight_eq_of_repr_invariantRestrict_ne_zero _ _ _ _ _ σ
    (scModuleDiagramEquiv_representation_h ht hσ) _ _ (t.isCartanWeightVector_scWeightBasis ht)
    hxy k

/-! ### The automorphism of the elementary group -/

/-- **The diagram automorphism `γ_σ` of the elementary group of the full-weight lattice** over a
commutative ring `A`: conjugation by the scalar extension of `θ_σ`. It sends the root subgroup of
each numbered raising or lowering generator to the one renumbered by `σ`. -/
def scElementaryDiagramAut (hσ : σ ∈ t.diagramSymmetry) (A : CommAlgCat.{w} ℤ) :
    MulAut (kostantElementarySubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht) A) :=
  kostantElementaryNumberedSymmetryAut (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
    (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
    (t.kostantForm_apply_mem_scLattice ht)
    (t.isNilpotent_representation_scModule_rootGenerator ht) (diagramRootGeneratorPerm σ)
    (t.scModuleDiagramEquiv ht hσ) (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ)
    (scModuleDiagramEquiv_representation_rootGenerator ht hσ)
    (diagramRootGeneratorPerm σ).surjective A

/-- `γ_σ` is conjugation by the scalar extension of `θ_σ` inside the automorphism group of the
scalar-extended lattice. -/
theorem val_scElementaryDiagramAut (hσ : σ ∈ t.diagramSymmetry) (A : CommAlgCat.{w} ℤ)
    (g : kostantElementarySubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht) A) :
    (t.scElementaryDiagramAut ht hσ A g : LinearMap.GeneralLinearGroup A
        (TensorProduct ℤ A (t.scLattice ht).toAddSubgroup)) =
      AddEquiv.baseChangeInvariantRestrictUnit (R := A) (t.scModuleDiagramEquiv ht hσ).toAddEquiv
          (t.scLattice ht).toAddSubgroup
          (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ) * g *
        (AddEquiv.baseChangeInvariantRestrictUnit (R := A)
          (t.scModuleDiagramEquiv ht hσ).toAddEquiv (t.scLattice ht).toAddSubgroup
          (fun _ => t.scModuleDiagramEquiv_mem_scLattice_iff ht hσ))⁻¹ :=
  val_kostantElementaryNumberedSymmetryAut _ _ _ _ _ _ _ _ _ _ _ A g

/-- **The pinning equation of `γ_σ`**: it sends the root subgroup element `x_{±i}(u)` to
`x_{±σ i}(u)`, renumbering the simple root subgroups and their negatives by `σ` without changing
their parameters. -/
@[simp]
theorem scElementaryDiagramAut_kostantRootSubgroupParam (hσ : σ ∈ t.diagramSymmetry)
    (A : CommAlgCat.{w} ℤ) (i : Fin t.rank ⊕ Fin t.rank) (u : Multiplicative A) :
    t.scElementaryDiagramAut ht hσ A
        ⟨kostantRootSubgroupParam (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
            (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
            (t.kostantForm_apply_mem_scLattice ht) i
            (t.isNilpotent_representation_scModule_rootGenerator ht i) A u,
          kostantRootSubgroupParam_mem_kostantElementarySubgroup _ _ _ _ _ _ A i u⟩ =
      ⟨kostantRootSubgroupParam (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht) (diagramRootGeneratorPerm σ i)
          (t.isNilpotent_representation_scModule_rootGenerator ht (diagramRootGeneratorPerm σ i))
          A u,
        kostantRootSubgroupParam_mem_kostantElementarySubgroup _ _ _ _ _ _ A
          (diagramRootGeneratorPerm σ i) u⟩ :=
  kostantElementaryNumberedSymmetryAut_kostantRootSubgroupParam _ _ _ _ _ _ _ _ _ _ _ A i u

/-- `γ_σ` commutes with base change of the value ring. -/
theorem kostantElementaryMap_scElementaryDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    {A B : CommAlgCat.{w} ℤ} (φ : A ⟶ B)
    (g : kostantElementarySubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht) A) :
    kostantElementaryMap (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht) φ
        (t.scElementaryDiagramAut ht hσ A g) =
      t.scElementaryDiagramAut ht hσ B
        (kostantElementaryMap (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht) φ g) :=
  kostantElementaryMap_kostantElementaryNumberedSymmetryAut _ _ _ _ _ _ _ _ _ _ _ φ g

/-- `γ_σ` commutes with the `p ^ n`-power Frobenius endomorphism. -/
theorem kostantElementaryFrobenius_scElementaryDiagramAut (hσ : σ ∈ t.diagramSymmetry)
    (p n : ℕ) (A : CommAlgCat.{w} ℤ) [ExpChar A p]
    (g : kostantElementarySubgroup (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht)
      (t.isNilpotent_representation_scModule_rootGenerator ht) A) :
    kostantElementaryFrobenius (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
        (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht) p n A
        (t.scElementaryDiagramAut ht hσ A g) =
      t.scElementaryDiagramAut ht hσ A
        (kostantElementaryFrobenius (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
          (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht) p n A g) :=
  kostantElementaryFrobenius_kostantElementaryNumberedSymmetryAut _ _ _ _ _ _ _ _ _ _ _ p n A g

end

end TauCeti.DynkinType
