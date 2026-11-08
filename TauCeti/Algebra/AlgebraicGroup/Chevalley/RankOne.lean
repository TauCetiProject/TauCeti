/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coroot
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RootSubgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.Bruhat

/-!
# Rank-one Bruhat collection in Chevalley data

For a Chevalley datum and a numbered simple root, words in the opposite root pair admit
rank-one Bruhat forms over every field. Adjoining the datum's actual character-lattice torus
still gives two forms, with a torus factor on the right. This is the local collection step
used in Bruhat decomposition; it asserts neither separation of the cells nor uniqueness of
coordinates, and is not a decomposition of the whole point group in higher rank.

The proof transports the integral Kostant rank-one relations and uses
`MonoidHom.mem_closure_rankOne_iff`. In particular it does not identify the actual torus with
the image of the full-weight parametrization, an identification that can fail over a field.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–20 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open Multiplicative TensorProduct
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (i : Fin t.rank) (A : Type v) [CommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing
-- Use the integral scalar action carried by the algebra objects in the Kostant formulas.
attribute [local instance high] Algebra.toModule

private theorem negative_simple_weight (j : Fin t.rank) :
    ⁅(t.lieBasis ht).h j, (t.lieBasis ht).rootGenerator (.inr i)⁆ =
      -((t.rootGeneratorWeight ht (.inl i) j : ℚ) •
        (t.lieBasis ht).rootGenerator (.inr i)) := by
  rw [t.lie_lieBasis_h_rootGenerator ht, t.rootGeneratorWeight_inr,
    t.rootGeneratorWeight_inl, Int.cast_neg, neg_smul]

private def matrixMap :
    LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice) →*
      Matrix.GeneralLinearGroup (Fin D.dim) A :=
  Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom

private theorem matrixMap_positive (u : Multiplicative A) :
    D.matrixMap A (kostantRootSubgroupParam (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice (.inl i)
      (D.isNilpotent_representation_rootGenerator (.inl i)) (CommAlgCat.of ℤ A) u) =
      (D.rootSubgroup (t.simpleIndex ht i) A u : Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  rw [coe_rootSubgroup, chevalleyRootSubgroup_simpleIndex]; rfl

private theorem matrixMap_negative (u : Multiplicative A) :
    D.matrixMap A (kostantRootSubgroupParam (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice (.inr i)
      (D.isNilpotent_representation_rootGenerator (.inr i)) (CommAlgCat.of ℤ A) u) =
      (D.rootSubgroup ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) (t.simpleIndex ht i)) A u :
        Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  rw [coe_rootSubgroup, chevalleyRootSubgroup_reflectionPerm_simpleIndex]; rfl

private theorem matrixMap_coroot (s : Aˣ) :
    D.matrixMap A (kostantCoordinateCocharacter D.lattice D.basis D.weight A i s) =
      (D.simpleCorootPoints i A s : Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  rw [kostantCoordinateCocharacter_apply, coe_simpleCorootPoints]
  simp only [matrixMap, MulEquiv.toMonoidHom_eq_coe, basisMatrix_kostantTorusPoints,
    kostantTorusMatrix_apply, torusCharacter_mulSingle]

private theorem matrixMap_weyl :
    D.matrixMap A (kostantWeylGL (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i)) (CommAlgCat.of ℤ A)) =
      (D.weylElement (t.simpleIndex ht i) A 1 :
        Matrix.GeneralLinearGroup (Fin D.dim) A) := by
  rw [kostantWeylGL_eq_kostantRootSubgroupParam_mul]
  simp only [map_mul, D.matrixMap_positive i A, D.matrixMap_negative i A, weylElement_def,
    Subgroup.coe_mul, inv_one, Units.val_one]

/-- A simple coroot rescales its positive simple-root parameter by its square. -/
theorem simpleCorootPoints_conj_rootSubgroup (s : Aˣ) (u : A) :
    D.simpleCorootPoints i A s * D.rootSubgroup (t.simpleIndex ht i) A (ofAdd u) *
        (D.simpleCorootPoints i A s)⁻¹ =
      D.rootSubgroup (t.simpleIndex ht i) A (ofAdd ((s : A) ^ 2 * u)) := by
  apply Subtype.ext
  have h := congrArg (D.matrixMap A)
    (kostantCoordinateCocharacter_conj_kostantRootSubgroupParam
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
      D.representation_mem_lattice D.basis D.weight D.isCartanWeightVector_basis
      (D.isSl2Triple_representation_rootGenerator i)
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (t.lie_lieBasis_h_rootGenerator ht (.inl i)) (CommAlgCat.of ℤ A) s u)
  simpa only [map_mul, map_inv, D.matrixMap_coroot i A, D.matrixMap_positive i A,
    Subgroup.coe_mul, Subgroup.coe_inv] using h

/-- A simple Weyl representative inverts its coroot parameters. -/
theorem weylElement_mul_simpleCorootPoints (s : Aˣ) :
    D.weylElement (t.simpleIndex ht i) A 1 * D.simpleCorootPoints i A s =
      D.simpleCorootPoints i A s⁻¹ * D.weylElement (t.simpleIndex ht i) A 1 := by
  apply mul_inv_eq_iff_eq_mul.mp
  apply Subtype.ext
  have h := congrArg (D.matrixMap A)
    (kostantWeylParam_conj_kostantCoordinateCocharacter
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
      D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i)) D.basis D.weight
      D.isCartanWeightVector_basis (D.isSl2Triple_representation_rootGenerator i)
      (t.lie_lieBasis_h_rootGenerator ht (.inl i)) (negative_simple_weight i)
      (CommAlgCat.of ℤ A) 1 s)
  simpa only [kostantWeylParam_one, map_mul, map_inv, D.matrixMap_coroot i A, D.matrixMap_weyl i A,
    Subgroup.coe_mul, Subgroup.coe_inv] using h

/-- The square of a simple Weyl representative is the coroot value at `-1`. -/
@[simp]
theorem weylElement_mul_self :
    D.weylElement (t.simpleIndex ht i) A 1 * D.weylElement (t.simpleIndex ht i) A 1 =
      D.simpleCorootPoints i A (-1) := by
  apply Subtype.ext
  have h := congrArg (D.matrixMap A)
    (kostantWeylGL_mul_self (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i)) D.basis D.weight
      D.isCartanWeightVector_basis (D.isSl2Triple_representation_rootGenerator i)
      (t.lie_lieBasis_h_rootGenerator ht (.inl i)) (negative_simple_weight i)
      (CommAlgCat.of ℤ A))
  simpa only [map_mul, D.matrixMap_coroot i A, D.matrixMap_weyl i A, Subgroup.coe_mul] using h

/-- The rank-one exchange identity at a unit parameter, valid over any commutative ring. -/
theorem weylElement_mul_rootSubgroup_mul_weylElement (u : Aˣ) :
    let x := D.rootSubgroup (t.simpleIndex ht i) A
    let n := D.weylElement (t.simpleIndex ht i) A 1
    n * x (ofAdd (u : A)) * n =
      x (ofAdd (-((u⁻¹ : Aˣ) : A))) * D.simpleCorootPoints i A (-u⁻¹) * n *
        x (ofAdd (-((u⁻¹ : Aˣ) : A))) := by
  dsimp only
  apply Subtype.ext
  have h := congrArg (D.matrixMap A)
    (kostantWeylGL_mul_kostantRootSubgroupParam_mul_kostantWeylGL
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h D.representation D.lattice
      D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i)) D.basis D.weight
      D.isCartanWeightVector_basis (D.isSl2Triple_representation_rootGenerator i)
      (t.lie_lieBasis_h_rootGenerator ht (.inl i)) (negative_simple_weight i)
      (CommAlgCat.of ℤ A) u)
  simpa only [map_mul, D.matrixMap_positive i A, D.matrixMap_coroot i A, D.matrixMap_weyl i A,
    Subgroup.coe_mul] using h

/-- An opposite simple-root pair generates the same subgroup as its positive root group,
coroot values and simple Weyl representative, over every commutative ring. -/
theorem closure_simpleRootPair_eq :
    Subgroup.closure (Set.range (D.rootSubgroup (t.simpleIndex ht i) A) ∪
      Set.range (D.rootSubgroup ((t.simplyConnectedRootDatum ht).reflectionPerm
        (t.simpleIndex ht i) (t.simpleIndex ht i)) A)) =
    Subgroup.closure (Set.range (D.rootSubgroup (t.simpleIndex ht i) A) ∪
      Set.range (D.simpleCorootPoints i A) ∪ {D.weylElement (t.simpleIndex ht i) A 1}) := by
  apply Subgroup.map_injective (D.points A).subtype_injective
  have h := congrArg (fun S => S.map (D.matrixMap A))
    (closure_kostantRootPair_eq (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice
      (D.isNilpotent_representation_rootGenerator (.inl i))
      (D.isNilpotent_representation_rootGenerator (.inr i)) D.basis D.weight
      D.isCartanWeightVector_basis (D.isSl2Triple_representation_rootGenerator i)
      (t.lie_lieBasis_h_rootGenerator ht (.inl i)) (negative_simple_weight i)
      (CommAlgCat.of ℤ A))
  simpa only [MonoidHom.map_closure, Set.image_union, ← Set.range_comp, Set.image_singleton,
    Function.comp_def, D.matrixMap_positive i A, D.matrixMap_negative i A,
    D.matrixMap_coroot i A, D.matrixMap_weyl i A, Subgroup.coe_subtype] using h

/-- The actual torus normalizes the subgroup generated by an opposite simple-root pair. -/
theorem range_torusPoints_le_normalizer_simpleRootPair :
    (D.torusPoints A).range ≤ Subgroup.normalizer
      (Subgroup.closure (Set.range (D.rootSubgroup (t.simpleIndex ht i) A) ∪
        Set.range (D.rootSubgroup ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) A))) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro _ ⟨s, rfl⟩ _ (⟨u, rfl⟩ | ⟨u, rfl⟩)
  · rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroup]
    exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · rw [← ofAdd_toAdd u, D.torusPoints_conj_rootSubgroup]
    exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)

variable (K : Type v) [Field K]

/-- Over every field, words in an opposite simple-root pair have two rank-one Bruhat forms.
This is an existence and membership criterion, without uniqueness or cell separation. -/
theorem mem_closure_simpleRootPair_iff (g : D.points K) :
    let x := D.rootSubgroup (t.simpleIndex ht i) K
    let y := D.rootSubgroup ((t.simplyConnectedRootDatum ht).reflectionPerm
      (t.simpleIndex ht i) (t.simpleIndex ht i)) K
    let h := D.simpleCorootPoints i K
    let n := D.weylElement (t.simpleIndex ht i) K 1
    g ∈ Subgroup.closure (Set.range x ∪ Set.range y) ↔
      (∃ a s, g = x (ofAdd a) * h s) ∨
        ∃ a s b, g = x (ofAdd a) * h s * n * x (ofAdd b) := by
  dsimp only
  rw [D.closure_simpleRootPair_eq]
  exact MonoidHom.mem_closure_rankOne_iff _ _ _
    (D.simpleCorootPoints_conj_rootSubgroup i K)
    (D.weylElement_mul_simpleCorootPoints i K) (D.weylElement_mul_self i K)
    (D.weylElement_mul_rootSubgroup_mul_weylElement i K) g

/-- Adjoining the actual character-lattice torus to an opposite simple-root pair gives two
rank-one Bruhat forms. The torus factor is on the right, and no surjectivity of the full-weight
parametrization is assumed. This does not assert uniqueness or disjointness of the forms. -/
theorem mem_sup_simpleRootPair_torus_iff (g : D.points K) :
    let x := D.rootSubgroup (t.simpleIndex ht i) K
    let y := D.rootSubgroup ((t.simplyConnectedRootDatum ht).reflectionPerm
      (t.simpleIndex ht i) (t.simpleIndex ht i)) K
    let T := D.torusPoints K
    let n := D.weylElement (t.simpleIndex ht i) K 1
    g ∈ Subgroup.closure (Set.range x ∪ Set.range y) ⊔ T.range ↔
      (∃ a s, g = x (ofAdd a) * T s) ∨
        ∃ a b s, g = x (ofAdd a) * n * x (ofAdd b) * T s := by
  dsimp only
  let x := D.rootSubgroup (t.simpleIndex ht i) K
  let y := D.rootSubgroup ((t.simplyConnectedRootDatum ht).reflectionPerm
    (t.simpleIndex ht i) (t.simpleIndex ht i)) K
  let h := D.simpleCorootPoints i K
  let n := D.weylElement (t.simpleIndex ht i) K 1
  let T := D.torusPoints K
  have htorus (s : Kˣ) : h s = T (D.simpleCorootParameter i K s) := by
    apply Subtype.ext
    simpa only [h, T, coe_torusPoints] using
      D.coe_simpleCorootPoints_eq_kostantTorusMatrix i K s
  have hmove (s : Kˣ) (b : K) : h s * x (ofAdd b) =
      x (ofAdd ((s : K) ^ 2 * b)) * h s :=
    mul_inv_eq_iff_eq_mul.mp (D.simpleCorootPoints_conj_rootSubgroup i K s b)
  constructor
  · intro hg
    have hprod := D.range_torusPoints_le_normalizer_simpleRootPair i K
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hprod] at hg
    obtain ⟨q, hq, _, ⟨s, rfl⟩, rfl⟩ := hg
    have hq' : (∃ a s, q = x (ofAdd a) * h s) ∨
        ∃ a s b, q = x (ofAdd a) * h s * n * x (ofAdd b) :=
      (D.mem_closure_simpleRootPair_iff i K q).mp hq
    rcases hq' with ⟨a, v, rfl⟩ | ⟨a, v, b, rfl⟩
    · exact Or.inl ⟨a, D.simpleCorootParameter i K v * s, by
        rw [(D.torusPoints K).map_mul, ← htorus]; simp only [x, h]; group⟩
    · refine Or.inr ⟨a, ((v⁻¹ : Kˣ) : K) ^ 2 * b,
        D.simpleCorootParameter i K v⁻¹ * s, ?_⟩
      have hn : h v * n = n * h v⁻¹ := by
        simpa only [h, n, inv_inv] using
          (D.weylElement_mul_simpleCorootPoints i K v⁻¹).symm
      calc
        _ = x (ofAdd a) * (h v * n) * x (ofAdd b) * T s := by
          simp only [T]; group
        _ = x (ofAdd a) * n * (h v⁻¹ * x (ofAdd b)) * T s := by rw [hn]; group
        _ = _ := by
          rw [hmove, (D.torusPoints K).map_mul, ← htorus]
          simp only [x, h, n, T]; group
  · have hx (a : K) : x (ofAdd a) ∈
        Subgroup.closure (Set.range x ∪ Set.range y) ⊔ T.range :=
      Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl ⟨_, rfl⟩))
    have hn : n ∈ Subgroup.closure (Set.range x ∪ Set.range y) ⊔ T.range := by
      have hn' : n ∈ Subgroup.closure (Set.range x ∪ Set.range y) := by
        rw [D.closure_simpleRootPair_eq]
        exact Subgroup.subset_closure (Or.inr rfl)
      exact Subgroup.mem_sup_left hn'
    rintro (⟨a, s, rfl⟩ | ⟨a, b, s, rfl⟩)
    · exact Subgroup.mul_mem _ (hx a) (Subgroup.mem_sup_right ⟨s, rfl⟩)
    · exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hx a) hn) (hx b))
        (Subgroup.mem_sup_right ⟨s, rfl⟩)

end

end TauCeti.DynkinType.ChevalleyDatum
