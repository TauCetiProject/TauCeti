/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Blocks
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Weight-block unitriangularity and the Borel--Weyl intersection

The positive and negative point subgroups of a Chevalley datum act on its weight basis by block
upper and block lower unitriangular matrices for the weight-space ranking
`orderedWeightBlock (t.weightDegree ht) D.weight`, over every commutative ring. Over a field `K`,
combining this block unitriangularity with the root action of the Weyl subgroup proves that the
Borel-type subgroup meets the Weyl subgroup in the actual character-lattice torus:

```text
B(K) ∩ N(K) = T(K).
```

First, any `g ∈ B(K) ∩ N(K)` has trivial Weyl projection, because a nontrivial Weyl element
inverts some positive root and would conjugate a nonidentity positive root element to a negative
root element inside `B(K)`. Writing `g = u * t` with `u ∈ U(K)` and `t ∈ T(K)` reduces to showing
that `u ∈ U(K) ∩ N(K)` with trivial Weyl projection is `1`. Extending scalars to the algebraic
closure separates distinct weight blocks via torus characters, so commutation with the represented
weight torus forces `u` to be block diagonal, while `U(K)` is block unitriangular.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.blockUnitriangular_positivePoints` and
  `TauCeti.DynkinType.ChevalleyDatum.blockUnitriangular_toDual_negativePoints`: elements of
  `D.positivePoints A` and `D.negativePoints A` are block upper and block lower unitriangular on
  distinct weight blocks over every commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.weylProjection_eq_one_of_mem_borelSubgroup`: a Weyl lift in
  `D.borelSubgroup K` projects to `1` in the Weyl group.
* `TauCeti.DynkinType.ChevalleyDatum.eq_one_of_mem_positivePoints_of_weylProjection_eq_one`: a
  Weyl lift in `D.positivePoints K` with trivial Weyl projection is `1`.
* `TauCeti.DynkinType.ChevalleyDatum.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints`:
  `D.borelSubgroup K ⊓ D.weylSubgroup K = (D.torusPoints K).range`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 27 and 28.
* R. W. Carter, *Simple Groups of Lie Type*, §8.2.
-/

public section

open Multiplicative TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section BlockUnitriangular

variable (A : Type v) [CommRing A]

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-- Every positive root element acts on the weight basis by a block upper unitriangular matrix for
the decreasing weight-degree block ranking. -/
theorem blockUnitriangular_rootSubgroupPoints_of_mem_posRoots {γ : Fin t.numRoots}
    (hγ : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) (u : Multiplicative A) :
    (((D.rootSubgroupPoints γ A u : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A)).BlockUnitriangular
      (orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.coe_rootSubgroupPoints,
    ← kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator,
    basisMatrix_kostantRootSubgroupParam]
  exact blockUnitriangular_kostantRootSubgroupMatrix
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
    (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
    D.basis D.weight (t.weightDegree ht) γ
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator γ)
    D.isCartanWeightVector_basis (t.lie_lieBasis_h_chevalleySystem ht γ)
    (t.weightDegree_root_pos ht hγ) _

/-- Every negative root element acts on the weight basis by a block lower unitriangular matrix for
the decreasing weight-degree block ranking. -/
theorem blockUnitriangular_toDual_rootSubgroupPoints_of_mem_negRoots {γ : Fin t.numRoots}
    (hγ : γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht)) (u : Multiplicative A) :
    (((D.rootSubgroupPoints γ A u : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A)).BlockUnitriangular
      (OrderDual.toDual ∘ orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.coe_rootSubgroupPoints,
    ← kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator,
    basisMatrix_kostantRootSubgroupParam]
  exact blockUnitriangular_toDual_kostantRootSubgroupMatrix
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
    (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
    D.basis D.weight (t.weightDegree ht) γ
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator γ)
    D.isCartanWeightVector_basis (t.lie_lieBasis_h_chevalleySystem ht γ)
    (t.weightDegree_root_neg ht hγ) _

/-- Every element of `D.positivePoints A` acts by a block upper unitriangular matrix on the
distinct weight blocks of the datum, over any commutative ring `A`. -/
theorem blockUnitriangular_positivePoints {g : D.points A} (hg : g ∈ D.positivePoints A) :
    (((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A)).BlockUnitriangular
      (orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.positivePoints_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, u, rfl⟩ := hx
    exact D.blockUnitriangular_rootSubgroupPoints_of_mem_posRoots A hγ u
  | one => exact Matrix.blockUnitriangular_one
  | mul _ _ _ _ hx hy => exact hx.mul hy
  | inv x _ hx =>
    rw [Subgroup.coe_inv, Matrix.coe_units_inv]
    exact hx.inv

/-- Every element of `D.negativePoints A` acts by a block lower unitriangular matrix on the
distinct weight blocks of the datum, over any commutative ring `A`. -/
theorem blockUnitriangular_toDual_negativePoints {g : D.points A} (hg : g ∈ D.negativePoints A) :
    (((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A)).BlockUnitriangular
      (OrderDual.toDual ∘ orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.negativePoints_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, u, rfl⟩ := hx
    exact D.blockUnitriangular_toDual_rootSubgroupPoints_of_mem_negRoots A hγ u
  | one => exact Matrix.blockUnitriangular_one
  | mul _ _ _ _ hx hy => exact hx.mul hy
  | inv x _ hx =>
    rw [Subgroup.coe_inv, Matrix.coe_units_inv]
    exact hx.inv

end BlockUnitriangular

section Field

variable (K : Type v) [Field K]

/-- A Weyl-subgroup element lying in the Borel-type subgroup has trivial Weyl projection. -/
theorem weylProjection_eq_one_of_mem_borelSubgroup {g : D.weylSubgroup K}
    (hg : (g : D.points K) ∈ D.borelSubgroup K) :
    D.weylProjection K g = 1 := by
  let : (t.simplyConnectedRootDatum ht).IsReduced := t.isReduced_simplyConnectedRootDatum ht
  by_contra hne
  obtain ⟨γ, hγ⟩ := inversions_nonempty_of_ne_one
    (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht) hne
  have hγpos : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [t.posRoots_rationalRootSystem ht]
    exact inversions_subset_posRoots _ _ _ hγ
  have hγneg :
      (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) γ ∈
        negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    simpa only [mem_negRoots, RootPairing.Base.isPos_iff, height_rationalBase] using
      mapsTo_inversions_negRoots _ _ _ hγ
  obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints K g γ
  have hmem : D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) γ) K (ofAdd 1) ∈
      D.borelSubgroup K := by
    have hscale : D.rootSubgroupPoints
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection K g) γ) K (ofAdd 1) =
        MulAut.conj (g : D.points K)
          (D.rootSubgroupPoints γ K (ofAdd ((c⁻¹ : Kˣ) : K))) := by
      simpa only [Units.mul_inv] using (hc ((c⁻¹ : Kˣ) : K)).symm
    rw [hscale, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg
      (D.positivePoints_le_borelSubgroup K
        (D.rootSubgroupPoints_mem_positivePoints K hγpos _)))
      (Subgroup.inv_mem _ hg)
  exact D.rootSubgroupPoints_ofAdd_one_ne_one K _
    ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots K hγneg _).mp hmem)

/-- A Weyl-subgroup element lying in `D.positivePoints K` with trivial Weyl projection is `1`. -/
theorem eq_one_of_mem_positivePoints_of_weylProjection_eq_one {g : D.weylSubgroup K}
    (hgpos : (g : D.points K) ∈ D.positivePoints K) (hproj : D.weylProjection K g = 1) :
    g = 1 := by
  have hblk := D.blockUnitriangular_positivePoints K hgpos
  have hmat : (((g : D.points K) : Matrix.GeneralLinearGroup (Fin D.dim) K) :
      Matrix (Fin D.dim) (Fin D.dim) K) = 1 := by
    ext r c
    by_cases hw : D.weight r = D.weight c
    · exact hblk.apply_of_eq ((orderedWeightBlock_eq_iff (t.weightDegree ht) D.weight).mpr hw)
    · obtain ⟨s, hs⟩ := exists_torusCharacter_ne (K := AlgebraicClosure K) hw
      let φ := algebraMap K (AlgebraicClosure K)
      let gBar := Matrix.GeneralLinearGroup.map φ
        ((g : D.points K) : Matrix.GeneralLinearGroup (Fin D.dim) K)
      have hcomm : gBar * diagGL (fun j => torusCharacter s (D.weight j)) =
          diagGL (fun j => torusCharacter s (D.weight j)) * gBar :=
        mul_inv_eq_iff_eq_mul.mp <| by
          simpa only [gBar, φ, map_one, MulAut.one_apply] using
            (D.weylProjection_eq_iff K g 1).mp hproj s
      have hentry := congrArg
        (fun u : Matrix.GeneralLinearGroup (Fin D.dim) (AlgebraicClosure K) =>
          (u : Matrix (Fin D.dim) (Fin D.dim) (AlgebraicClosure K)) r c) hcomm
      simp only [Units.val_mul, diagGL_coe, Matrix.mul_diagonal, Matrix.diagonal_mul,
        gBar, Matrix.GeneralLinearGroup.map_apply] at hentry
      have hzero : φ (((g : D.points K) : Matrix.GeneralLinearGroup (Fin D.dim) K) r c) *
          ((torusCharacter s (D.weight c) : AlgebraicClosure K) -
            (torusCharacter s (D.weight r) : AlgebraicClosure K)) = 0 := by
        linear_combination hentry
      have hne : (torusCharacter s (D.weight c) : AlgebraicClosure K) -
          (torusCharacter s (D.weight r) : AlgebraicClosure K) ≠ 0 :=
        sub_ne_zero.mpr (Units.val_inj.not.mpr hs.symm)
      have hrc : (((g : D.points K) : Matrix.GeneralLinearGroup (Fin D.dim) K) :
          Matrix (Fin D.dim) (Fin D.dim) K) r c = 0 :=
        (map_eq_zero_iff φ φ.injective).mp ((mul_eq_zero.mp hzero).resolve_right hne)
      rw [hrc, Matrix.one_apply_ne (fun heq => hw (congrArg D.weight heq))]
  exact Subtype.ext (Subtype.ext (Units.ext hmat))

/-- Over a field, the Borel-type subgroup meets the Weyl subgroup in the actual torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints :
    D.borelSubgroup K ⊓ D.weylSubgroup K = (D.torusPoints K).range := by
  apply le_antisymm
  · rintro g ⟨hgB, hgW⟩
    obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff K).mp hgB
    have htW : D.torusPoints K s ∈ D.weylSubgroup K := D.torusPoints_mem_weylSubgroup K s
    have huW : u ∈ D.weylSubgroup K := by
      simpa only [mul_inv_cancel_right] using Subgroup.mul_mem _ hgW (Subgroup.inv_mem _ htW)
    have huproj : D.weylProjection K ⟨u, huW⟩ = 1 := by
      have hmul : (⟨u * D.torusPoints K s, hgW⟩ : D.weylSubgroup K) =
          ⟨u, huW⟩ * ⟨D.torusPoints K s, htW⟩ := rfl
      have h1 := D.weylProjection_eq_one_of_mem_borelSubgroup K (g := ⟨_, hgW⟩) hgB
      rw [hmul, map_mul, D.weylProjection_torusPoints, mul_one] at h1
      exact h1
    have hu1 : u = 1 := congrArg Subtype.val
      (D.eq_one_of_mem_positivePoints_of_weylProjection_eq_one K hu huproj)
    exact ⟨s, by rw [hu1, one_mul]⟩
  · refine le_inf (D.range_torusPoints_le_borelSubgroup K) ?_
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_weylSubgroup K s

/-- Over a field, the Weyl subgroup meets the Borel-type subgroup in the actual torus. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup_eq_range_torusPoints :
    D.weylSubgroup K ⊓ D.borelSubgroup K = (D.torusPoints K).range := by
  rw [inf_comm, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints]

end Field

end TauCeti.DynkinType.ChevalleyDatum
