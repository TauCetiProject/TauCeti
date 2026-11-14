/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.PositiveSubsystem
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Intersection of the Borel and Weyl subgroups of a Chevalley datum

For a Chevalley datum `D` over a field `k`, let `U(k) = D.positivePoints k`,
`B(k) = D.borelSubgroup k = U(k) ⊔ T_D(k)`, and `N(k) = D.weylSubgroup k`. This file proves

```text
U(k) ∩ N(k) = 1   and   B(k) ∩ N(k) = T_D(k).
```

This is the torus-intersection axiom `(BN0)` for the Tits system of a Chevalley datum, proved
uniformly for all isogeny types and over arbitrary fields (including finite fields and fields of
bad characteristic).

The proof of `U(k) ∩ N(k) = 1` has two stages:
1. If `u ∈ U(k) ∩ N(k)` had nontrivial Weyl projection `w ≠ 1`, strong exchange supplies a
   simple root `αⱼ` sent by `w` to a negative root. Conjugating `X_{αⱼ}(k) ≤ U(k)` by
   `u ∈ U(k)` would then place `x_{w(αⱼ)}(1) ≠ 1` inside `U(k) ≤ B(k)`, contradicting the
   disjointness of negative root subgroups from `B(k)`.
2. Thus `u` projects to `1 ∈ W`, so after scalar extension to the infinite algebraic closure `K`
   of `k` its matrix commutes with the represented full-weight torus and therefore preserves
   every weight space. On the other hand, ordering the weight basis by decreasing weight degree
   with both forward and reversed tie-breakers on equal-degree indices places `U(K)` inside two
   upper-unitriangular groups whose intersection on each weight space is the identity.

## Main results

* `ChevalleyDatum.positivePoints_inf_weylSubgroup_eq_bot` and
  `ChevalleyDatum.weylSubgroup_inf_positivePoints_eq_bot`: `U(k) ∩ N(k) = 1`.
* `ChevalleyDatum.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints` and
  `ChevalleyDatum.weylSubgroup_inf_borelSubgroup_eq_range_torusPoints`: `B(k) ∩ N(k) = T_D(k)`.
* `ChevalleyDatum.weylProjection_eq_one_of_mem_borelSubgroup`: every element of `B(k) ∩ N(k)` has
  trivial Weyl projection.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 26 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

-- Match the coefficient structure used by `D.points`, including on an algebraic closure.
attribute [local instance high] Ring.toIntAlgebra
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private structure WeightIdx (d : ℕ) where
  ofFin ::
  toFin : Fin d

private def weightIdxEquiv (d : ℕ) : Fin d ≃ WeightIdx d :=
  ⟨WeightIdx.ofFin, WeightIdx.toFin, fun _ => rfl, fun _ => rfl⟩

private instance instFintypeWeightIdx (d : ℕ) : Fintype (WeightIdx d) :=
  Fintype.ofEquiv (Fin d) (weightIdxEquiv d)

@[instance_reducible]
private noncomputable def weightIdxLinearOrder (e : Equiv.Perm (Fin D.dim)) :
    LinearOrder (WeightIdx D.dim) :=
  LinearOrder.lift'
    (fun x : WeightIdx D.dim =>
      toLex (OrderDual.toDual (t.weightDegree ht (D.weight x.toFin)), e x.toFin))
    (fun x y h => by
      cases x; cases y
      simpa using e.injective (congrArg (fun z => (ofLex z).2) h))

private theorem isUpperUnitriangular_reindex_of_mem_positivePoints
    {A : Type v} [CommRing A] {v : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice)}
    (hv : v ∈ D.positiveSubgroup (CommAlgCat.of ℤ A)) (e : Equiv.Perm (Fin D.dim)) :
    let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder e
    ((Units.map (LinearMap.toMatrixAlgEquiv
      ((D.basis.reindex (weightIdxEquiv D.dim)).baseChange A)).toMulEquiv v :
        Matrix.GeneralLinearGroup (WeightIdx D.dim) A) :
        Matrix (WeightIdx D.dim) (WeightIdx D.dim) A).IsUpperUnitriangular := by
  let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder e
  have hwt (x : WeightIdx D.dim) :
      IsCartanWeightVector (t.lieBasis ht).h D.representation (D.weight x.toFin)
        ((D.basis.reindex (weightIdxEquiv D.dim) x : D.lattice) : _) := by
    simpa [weightIdxEquiv] using D.isCartanWeightVector_basis x.toFin
  have hpos : ∀ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      ∀ {r s : WeightIdx D.dim} {m : ℕ}, 0 < m →
        D.weight r.toFin = D.weight s.toFin + m • (t.simplyConnectedRootDatum ht).root γ →
          r < s := by
    intro γ hγ r s m hm hrs
    have hdeg : t.weightDegree ht (D.weight s.toFin) < t.weightDegree ht (D.weight r.toFin) := by
      rw [hrs, map_add, map_nsmul]
      exact lt_add_of_pos_right _ (nsmul_pos (t.weightDegree_root_pos ht hγ) hm.ne')
    -- `LinearOrder.lift'` has no comparison lemma, so expose its defining lexicographic order.
    change toLex (OrderDual.toDual (t.weightDegree ht (D.weight r.toFin)), e r.toFin) <
      toLex (OrderDual.toDual (t.weightDegree ht (D.weight s.toFin)), e s.toFin)
    exact Prod.Lex.left _ _ hdeg
  have hv' : v ∈ kostantSubsystemSubgroup (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator)
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) (CommAlgCat.of ℤ A) := by
    simpa only [D.positiveSubgroup_eq_closure, kostantSubsystemSubgroup_eq_closure,
      kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator] using hv
  exact UpperUnitriangularGroup.mem_iff.mp <|
    map_kostantSubsystemSubgroup_le_upperUnitriangular
      (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator)
      (D.basis.reindex (weightIdxEquiv D.dim)) (fun x => D.weight x.toFin)
      (t.simplyConnectedRootDatum ht).root
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
      hwt (fun γ _ i => t.lie_lieBasis_h_chevalleySystem ht γ i) hpos A
      ⟨v, hv', rfl⟩

private theorem apply_eq_one_apply_of_mem_positivePoints_of_weightDegree_le
    {A : Type v} [CommRing A] {g : D.points A} (hg : g ∈ D.positivePoints A)
    {r q : Fin D.dim}
    (hdeg : t.weightDegree ht (D.weight r) ≤ t.weightDegree ht (D.weight q)) :
    ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) r q =
      (1 : Matrix (Fin D.dim) (Fin D.dim) A) r q := by
  obtain ⟨v, hv, hgv⟩ := D.mem_positivePoints_iff.mp hg
  have hentry (e : Equiv.Perm (Fin D.dim)) :
      let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder e
      ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) r q =
      ((Units.map (LinearMap.toMatrixAlgEquiv
        ((D.basis.reindex (weightIdxEquiv D.dim)).baseChange A)).toMulEquiv v :
          Matrix.GeneralLinearGroup (WeightIdx D.dim) A) :
          Matrix (WeightIdx D.dim) (WeightIdx D.dim) A) (.ofFin r) (.ofFin q) := by
    let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder e
    rw [← hgv, Module.Basis.baseChange_reindex]
    simp [weightIdxEquiv, LinearMap.toMatrixAlgEquiv_apply, Module.Basis.reindex_apply]
  by_cases hrq : r = q
  · subst q
    let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder (Equiv.refl _)
    have htri := D.isUpperUnitriangular_reindex_of_mem_positivePoints hv (Equiv.refl _)
    rw [hentry (Equiv.refl _), Matrix.one_apply_eq]
    exact htri.apply_diag (.ofFin r)
  · rw [Matrix.one_apply_ne hrq]
    rcases lt_or_eq_of_le hdeg with hlt | heq
    · let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder (Equiv.refl _)
      have htri := D.isUpperUnitriangular_reindex_of_mem_positivePoints hv (Equiv.refl _)
      rw [hentry (Equiv.refl _)]
      apply htri.isUpperTriangular
      -- Expose the lexicographic comparison defining `weightIdxLinearOrder`.
      change toLex (OrderDual.toDual (t.weightDegree ht (D.weight q)), q) <
        toLex (OrderDual.toDual (t.weightDegree ht (D.weight r)), r)
      exact Prod.Lex.left _ _ hlt
    · rcases lt_or_gt_of_ne hrq with hlt | hgt
      · let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder Fin.revPerm
        have htri := D.isUpperUnitriangular_reindex_of_mem_positivePoints hv Fin.revPerm
        rw [hentry Fin.revPerm]
        apply htri.isUpperTriangular
        -- Expose the lexicographic comparison defining `weightIdxLinearOrder`.
        change toLex (OrderDual.toDual (t.weightDegree ht (D.weight q)), Fin.revPerm q) <
          toLex (OrderDual.toDual (t.weightDegree ht (D.weight r)), Fin.revPerm r)
        rw [heq]
        exact Prod.Lex.right _ (Fin.rev_lt_rev.mpr hlt)
      · let _ : LinearOrder (WeightIdx D.dim) := D.weightIdxLinearOrder (Equiv.refl _)
        have htri := D.isUpperUnitriangular_reindex_of_mem_positivePoints hv (Equiv.refl _)
        rw [hentry (Equiv.refl _)]
        apply htri.isUpperTriangular
        -- Expose the lexicographic comparison defining `weightIdxLinearOrder`.
        change toLex (OrderDual.toDual (t.weightDegree ht (D.weight q)), q) <
          toLex (OrderDual.toDual (t.weightDegree ht (D.weight r)), r)
        rw [heq]
        exact Prod.Lex.right _ hgt

private theorem weylProjection_eq_one_of_mem_positivePoints (k : Type v) [Field k]
    {u : D.points k} (huU : u ∈ D.positivePoints k) (huW : u ∈ D.weylSubgroup k) :
    D.weylProjection k ⟨u, huW⟩ = 1 := by
  have := t.isReduced_simplyConnectedRootDatum ht
  by_contra hw
  obtain ⟨j, -, hinv⟩ := exists_mem_support_mem_inversions_of_ne_one
    (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) hw
  rw [mem_inversions] at hinv
  have hj_pos : j ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [t.posRoots_rationalRootSystem ht, mem_posRoots]
    exact hinv.1
  set γ := (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k ⟨u, huW⟩) j
  have hγ_neg : γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [negRoots_eq_compl, t.posRoots_rationalRootSystem ht, Set.mem_compl_iff, mem_posRoots]
    exact hinv.2
  have hmem : D.rootSubgroupPoints γ k (ofAdd 1) ∈
      (D.rootSubgroupPoints j k).range.map (MulAut.conj u).toMonoidHom := by
    rw [D.map_range_rootSubgroupPoints_conj k ⟨u, huW⟩ j]
    exact ⟨ofAdd 1, rfl⟩
  obtain ⟨_, ⟨a, rfl⟩, hconj⟩ := hmem
  have hposU : MulAut.conj u (D.rootSubgroupPoints j k a) ∈ D.positivePoints k := by
    rw [MulAut.conj_apply]
    exact (D.positivePoints k).mul_mem
      ((D.positivePoints k).mul_mem huU (D.rootSubgroupPoints_mem_positivePoints k hj_pos a))
      ((D.positivePoints k).inv_mem huU)
  have hB : D.rootSubgroupPoints γ k (ofAdd 1) ∈ D.borelSubgroup k :=
    D.positivePoints_le_borelSubgroup k (hconj ▸ hposU)
  exact D.rootSubgroupPoints_ofAdd_one_ne_one k γ
    ((D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots k hγ_neg (ofAdd 1)).mp hB)

/-- Inside the points of a Chevalley datum over any field, the positive unipotent subgroup meets
the Weyl subgroup trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot (k : Type v) [Field k] :
    D.positivePoints k ⊓ D.weylSubgroup k = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨huU, huW⟩
  rw [Subgroup.mem_bot]
  have hw1 := D.weylProjection_eq_one_of_mem_positivePoints k huU huW
  let K := AlgebraicClosure k
  let φ : k →+* K := algebraMap k K
  let uK : D.points K := (D.pointsPresentation k).map (D.pointsPresentation K) φ u
  have huK : uK ∈ D.positivePoints K := D.map_positivePoints_le φ ⟨u, huU, rfl⟩
  have hcoe : (uK : Matrix.GeneralLinearGroup (Fin D.dim) K) =
      Matrix.GeneralLinearGroup.map φ (u : Matrix.GeneralLinearGroup (Fin D.dim) k) :=
    GeneralLinear.IntegralPointsPresentation.coe_map
      (D.pointsPresentation k) (D.pointsPresentation K) φ u
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.map_injective φ.injective
  rw [Subgroup.coe_one, map_one, ← hcoe]
  apply Units.ext
  ext r q
  by_cases hwt : D.weight r = D.weight q
  · exact D.apply_eq_one_apply_of_mem_positivePoints_of_weightDegree_le huK
      (le_of_eq (congrArg (t.weightDegree ht) hwt))
  · have hrq : r ≠ q := fun h => hwt (congrArg D.weight h)
    rw [Units.val_one, Matrix.one_apply_ne hrq]
    obtain ⟨s, hchar⟩ := exists_torusCharacter_ne (K := K) hwt
    have hcomm := (D.weylProjection_eq_iff k ⟨u, huW⟩ 1).mp hw1 s
    rw [map_one, MulAut.one_apply, ← hcoe, mul_inv_eq_iff_eq_mul] at hcomm
    have hentry := congrArg (fun M : Matrix.GeneralLinearGroup (Fin D.dim) K =>
      (M : Matrix (Fin D.dim) (Fin D.dim) K) r q) hcomm
    simp only [Units.val_mul, diagGL_coe, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    have hzero : ((torusCharacter s (D.weight q) : K) -
        (torusCharacter s (D.weight r) : K)) *
        ((uK : Matrix.GeneralLinearGroup (Fin D.dim) K) :
          Matrix (Fin D.dim) (Fin D.dim) K) r q = 0 := by
      rw [sub_mul, mul_comm, hentry, mul_comm, sub_self]
    have hsub_ne : (torusCharacter s (D.weight q) : K) -
        (torusCharacter s (D.weight r) : K) ≠ 0 :=
      sub_ne_zero.mpr fun h => hchar (Units.ext h.symm)
    exact (mul_eq_zero.mp hzero).resolve_left hsub_ne

/-- Inside the points of a Chevalley datum over any field, the Weyl subgroup meets the positive
unipotent subgroup trivially. -/
@[simp]
theorem weylSubgroup_inf_positivePoints_eq_bot (k : Type v) [Field k] :
    D.weylSubgroup k ⊓ D.positivePoints k = ⊥ := by
  rw [inf_comm, D.positivePoints_inf_weylSubgroup_eq_bot]

/-- Over any field, the intersection of the positive Borel subgroup and the Weyl subgroup of a
Chevalley datum is the actual weight-lattice torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints (k : Type v) [Field k] :
    D.borelSubgroup k ⊓ D.weylSubgroup k = (D.torusPoints k).range := by
  apply le_antisymm
  · rintro g ⟨hgB, hgW⟩
    obtain ⟨u, huU, s, rfl⟩ := (D.mem_borelSubgroup_iff k).mp hgB
    have huW : u ∈ D.weylSubgroup k := by
      simpa only [mul_inv_cancel_right] using
        (D.weylSubgroup k).mul_mem hgW
          ((D.weylSubgroup k).inv_mem (D.torusPoints_mem_weylSubgroup k s))
    have hu1 : u = 1 := Subgroup.mem_bot.mp <| by
      rw [← D.positivePoints_inf_weylSubgroup_eq_bot k]
      exact ⟨huU, huW⟩
    rw [hu1, one_mul]
    exact ⟨s, rfl⟩
  · refine le_inf (D.range_torusPoints_le_borelSubgroup k) ?_
    rintro _ ⟨s, rfl⟩
    exact D.torusPoints_mem_weylSubgroup k s

/-- Over any field, the intersection of the Weyl subgroup and the positive Borel subgroup of a
Chevalley datum is the actual weight-lattice torus. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup_eq_range_torusPoints (k : Type v) [Field k] :
    D.weylSubgroup k ⊓ D.borelSubgroup k = (D.torusPoints k).range := by
  rw [inf_comm, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints]

/-- Any element of the Weyl subgroup that also belongs to the positive Borel subgroup has trivial
Weyl projection. -/
theorem weylProjection_eq_one_of_mem_borelSubgroup (k : Type v) [Field k]
    {g : D.weylSubgroup k} (hg : (g : D.points k) ∈ D.borelSubgroup k) :
    D.weylProjection k g = 1 := by
  have hmem : (g : D.points k) ∈ (D.torusPoints k).range := by
    rw [← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints k]
    exact ⟨hg, g.property⟩
  obtain ⟨s, hs⟩ := hmem
  have hg' : g = ⟨D.torusPoints k s, D.torusPoints_mem_weylSubgroup k s⟩ := Subtype.ext hs.symm
  rw [hg', D.weylProjection_torusPoints]

end TauCeti.DynkinType.ChevalleyDatum
