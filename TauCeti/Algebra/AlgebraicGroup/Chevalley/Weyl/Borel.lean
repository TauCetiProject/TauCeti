/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Parabolic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.PositiveSubsystem
import TauCeti.GroupTheory.DoubleCoset.Basic
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Borel intersections and simple-reflection double cosets for a Chevalley datum

Over an arbitrary field `k` — including `𝔽₂`, with no assumption on the size of `kˣ` — this file
relates the Weyl subgroup `D.weylSubgroup k` of a Chevalley datum `D` to its positive subgroup
`D.positivePoints k` and Borel-type subgroup `D.borelSubgroup k`:

1. Every element of `D.weylSubgroup k` lying in `D.borelSubgroup k` has trivial Weyl projection,
   because any nontrivial Weyl element sends some positive root to a negative root while every
   nontrivial negative root element lies outside `D.borelSubgroup k`.
2. `D.positivePoints k ⊓ D.weylSubgroup k = ⊥` and consequently
   `D.borelSubgroup k ⊓ D.weylSubgroup k = (D.torusPoints k).range`. Off-diagonal entries between
   distinct weights vanish after passing to the algebraic closure where torus characters separate
   weights; entries within a single weight space agree with the identity matrix because positive
   root operators strictly raise weights under every tie-breaking linear order.
3. Left multiplication of a double coset `B n B` (`n ∈ D.weylSubgroup k`) by the simple-reflection
   cell `B nᵢ(1) B` equals `B (nᵢ(1) n) B` whenever `(D.weylProjection k n)⁻¹` keeps `αᵢ`
   positive, and always lies in `B (nᵢ(1) n) B ∪ B n B`.

These results supply both the intersection `B ∩ N = T` and the double-coset multiplication axiom
for the Tits system of a Chevalley datum, without assuming any braid relations among the pinned
simple Weyl representatives.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 20, 22, 25 and Theorem 4.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

open Multiplicative TensorProduct
open TauCeti.UniversalEnvelopingAlgebra
open scoped Pointwise

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

-- Match scalar-extension tensor products with the integral algebra structure on the value ring.
attribute [local instance high] Algebra.toModule

/-! ### Weight-space entries of positive points -/

/-- Auxiliary index wrapper carrying no built-in order, so weight-decreasing linear orders do not
compete with the standard order on `Fin D.dim`. -/
private structure WtIdx (n : ℕ) where
  idx : Fin n

private def equivWtIdx (n : ℕ) : Fin n ≃ WtIdx n :=
  ⟨WtIdx.mk, WtIdx.idx, fun _ => rfl, fun _ => rfl⟩

private instance (n : ℕ) : Fintype (WtIdx n) :=
  Fintype.ofEquiv (Fin n) (equivWtIdx n)

@[instance_reducible]
private noncomputable def wtIdxLinearOrder {β : Type} [LinearOrder β] (tie : Fin D.dim ≃ β) :
    LinearOrder (WtIdx D.dim) :=
  LinearOrder.lift'
    (fun x => toLex (OrderDual.toDual (t.weightDegree ht (D.weight x.idx)), tie x.idx))
    (fun ⟨_⟩ ⟨_⟩ h => congrArg WtIdx.mk (tie.injective (congrArg (fun z => (ofLex z).2) h)))

/-- Under a weight-decreasing linear order with tie-breaker `tie`, every positive point is upper
unitriangular when reindexed to `WtIdx D.dim`. -/
private theorem isUpperUnitriangular_submatrix_of_mem_positivePoints {A : Type v} [CommRing A]
    {β : Type} [LinearOrder β] (tie : Fin D.dim ≃ β)
    {g : D.points A} (hg : g ∈ D.positivePoints A) :
    letI : LinearOrder (WtIdx D.dim) := D.wtIdxLinearOrder tie
    (((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A).submatrix WtIdx.idx WtIdx.idx).IsUpperUnitriangular := by
  let : LinearOrder (WtIdx D.dim) := D.wtIdxLinearOrder tie
  obtain ⟨u, hu, hu_eq⟩ := D.mem_positivePoints_iff.mp hg
  have hu' : u ∈ kostantSubsystemSubgroup (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator)
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) (CommAlgCat.of ℤ A) := by
    simpa only [SetLike.mem_coe, D.positiveSubgroup_eq_closure, kostantSubsystemSubgroup_eq_closure,
      kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator] using hu
  have hpos : ∀ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
      ∀ {r s : WtIdx D.dim} {m : ℕ}, 0 < m →
        D.weight r.idx = D.weight s.idx + m • (t.simplyConnectedRootDatum ht).root γ → r < s := by
    intro γ hγ r s m hm hrs
    -- Expose the defining lexicographic order of `wtIdxLinearOrder`.
    change toLex (OrderDual.toDual (t.weightDegree ht (D.weight r.idx)), tie r.idx) <
      toLex (OrderDual.toDual (t.weightDegree ht (D.weight s.idx)), tie s.idx)
    apply Prod.Lex.left
    rw [hrs, map_add, map_nsmul]
    exact lt_add_of_pos_right _ (nsmul_pos (t.weightDegree_root_pos ht hγ) hm.ne')
  have hmem := UpperUnitriangularGroup.mem_iff.mp <|
    map_kostantSubsystemSubgroup_le_upperUnitriangular
      (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator)
      (D.basis.reindex (equivWtIdx D.dim)) (fun x => D.weight x.idx)
      (t.simplyConnectedRootDatum ht).root
      (posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
      (fun x => by simpa [equivWtIdx] using D.isCartanWeightVector_basis x.idx)
      (fun γ _ j => t.lie_lieBasis_h_chevalleySystem ht γ j) hpos A ⟨u, hu', rfl⟩
  have hmat :
      ((Units.map (LinearMap.toMatrixAlgEquiv
          ((D.basis.reindex (equivWtIdx D.dim)).baseChange A)).toMulEquiv u :
        Matrix.GeneralLinearGroup (WtIdx D.dim) A) : Matrix (WtIdx D.dim) (WtIdx D.dim) A) =
      (((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A).submatrix WtIdx.idx WtIdx.idx) := by
    rw [← hu_eq]
    ext ⟨r⟩ ⟨s⟩
    simp [equivWtIdx, LinearMap.toMatrixAlgEquiv, LinearMap.toMatrix_apply,
      Module.Basis.baseChange_reindex, Module.Basis.reindex_apply, Module.Basis.repr_reindex]
  rwa [hmat] at hmem

/-- Positive points act as the identity on each individual weight space: if
`D.weight r = D.weight s`, the `(r, s)` entry of `g ∈ D.positivePoints A` agrees with that of
`1`. -/
private theorem coe_apply_of_mem_positivePoints_of_weight_eq {A : Type v} [CommRing A]
    {g : D.points A} (hg : g ∈ D.positivePoints A)
    {r s : Fin D.dim} (hrs : D.weight r = D.weight s) :
    ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) r s =
      (1 : Matrix (Fin D.dim) (Fin D.dim) A) r s := by
  rcases lt_trichotomy r s with hlt | rfl | hgt
  · let : LinearOrder (WtIdx D.dim) := D.wtIdxLinearOrder OrderDual.toDual
    have hu := D.isUpperUnitriangular_submatrix_of_mem_positivePoints OrderDual.toDual hg
    have hdual : (⟨s⟩ : WtIdx D.dim) < ⟨r⟩ := by
      -- Expose the lexicographic comparison on `WtIdx D.dim`.
      change toLex (OrderDual.toDual (t.weightDegree ht (D.weight s)), OrderDual.toDual s) <
        toLex (OrderDual.toDual (t.weightDegree ht (D.weight r)), OrderDual.toDual r)
      rw [hrs]
      exact Prod.Lex.right _ hlt
    rw [Matrix.one_apply_ne hlt.ne]
    exact hu.isUpperTriangular hdual
  · let : LinearOrder (WtIdx D.dim) := D.wtIdxLinearOrder (Equiv.refl _)
    rw [Matrix.one_apply_eq]
    exact (D.isUpperUnitriangular_submatrix_of_mem_positivePoints
      (Equiv.refl _) hg).apply_diag ⟨r⟩
  · let : LinearOrder (WtIdx D.dim) := D.wtIdxLinearOrder (Equiv.refl _)
    have hu := D.isUpperUnitriangular_submatrix_of_mem_positivePoints (Equiv.refl _) hg
    have hrefl : (⟨s⟩ : WtIdx D.dim) < ⟨r⟩ := by
      -- Expose the lexicographic comparison on `WtIdx D.dim`.
      change toLex (OrderDual.toDual (t.weightDegree ht (D.weight s)), s) <
        toLex (OrderDual.toDual (t.weightDegree ht (D.weight r)), r)
      rw [hrs]
      exact Prod.Lex.right _ hgt
    rw [Matrix.one_apply_ne hgt.ne']
    exact hu.isUpperTriangular hrefl

/-! ### Intersection of the Weyl subgroup with the positive and Borel subgroups -/

variable (k : Type v) [Field k]

/-- Any element of `D.weylSubgroup k` that also belongs to `D.borelSubgroup k` has trivial Weyl
projection. -/
theorem weylProjection_eq_one_of_mem_borelSubgroup (n : D.weylSubgroup k)
    (hn : (n : D.points k) ∈ D.borelSubgroup k) :
    D.weylProjection k n = 1 := by
  have := t.isReduced_simplyConnectedRootDatum ht
  by_contra hne
  obtain ⟨γ, hγ⟩ := inversions_nonempty_of_ne_one
    (P := t.simplyConnectedRootDatum ht) (b := t.simplyConnectedBase ht) hne
  have hγ_pos : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [t.posRoots_rationalRootSystem ht]
    exact inversions_subset_posRoots _ _ _ hγ
  have hγ_neg : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n) γ ∈
      negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    rw [negRoots_eq_compl, t.posRoots_rationalRootSystem ht, ← negRoots_eq_compl]
    exact mapsTo_inversions_negRoots _ _ _ hγ
  obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints k n γ
  have hconj_mem :
      MulAut.conj (n : D.points k) (D.rootSubgroupPoints γ k (ofAdd 1)) ∈ D.borelSubgroup k :=
    mul_mem (mul_mem hn (D.positivePoints_le_borelSubgroup k
      (D.rootSubgroupPoints_mem_positivePoints k hγ_pos _))) (inv_mem hn)
  rw [hc 1, mul_one, D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots k hγ_neg,
    ← mul_one (c : k), ← hc 1, MulAut.conj_apply, conj_eq_one_iff] at hconj_mem
  exact D.rootSubgroupPoints_ofAdd_one_ne_one k γ hconj_mem

/-- Over every field, the positive point subgroup meets the Weyl subgroup trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot :
    D.positivePoints k ⊓ D.weylSubgroup k = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hpos, hw⟩ : g ∈ D.positivePoints k ∧ g ∈ D.weylSubgroup k := hg
  have hproj : D.weylProjection k ⟨g, hw⟩ = 1 :=
    D.weylProjection_eq_one_of_mem_borelSubgroup k ⟨g, hw⟩
      (D.positivePoints_le_borelSubgroup k hpos)
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro r s
  simp only [Subgroup.coe_one, Units.val_one]
  by_cases hwt : D.weight r = D.weight s
  · exact D.coe_apply_of_mem_positivePoints_of_weight_eq hpos hwt
  · have hrs : r ≠ s := fun h => hwt (congrArg D.weight h)
    rw [Matrix.one_apply_ne hrs]
    obtain ⟨x, hx⟩ := exists_torusCharacter_ne (K := AlgebraicClosure k) hwt
    have hcomm := (D.weylProjection_eq_iff k ⟨g, hw⟩ 1).mp hproj x
    rw [map_one, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at hcomm
    have hdiag : Commute
        (Matrix.diagonal fun j => (torusCharacter x (D.weight j) : AlgebraicClosure k))
        ((Matrix.GeneralLinearGroup.map (algebraMap k (AlgebraicClosure k))
          (g : Matrix.GeneralLinearGroup (Fin D.dim) k) :
            Matrix.GeneralLinearGroup (Fin D.dim) (AlgebraicClosure k)) :
          Matrix (Fin D.dim) (Fin D.dim) (AlgebraicClosure k)) := by
      simpa only [Commute, SemiconjBy, Units.val_mul, diagGL_coe] using
        congrArg Units.val hcomm.symm
    have hzero := apply_eq_zero_of_commute_diagonal hdiag (Units.ext_iff.not.mp hx)
    exact (algebraMap k (AlgebraicClosure k)).injective
      (by simpa [RingHom.mapMatrix_apply] using hzero)

/-- Over every field, the intersection of the Borel-type subgroup with the Weyl subgroup is
precisely the actual torus image. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints :
    D.borelSubgroup k ⊓ D.weylSubgroup k = (D.torusPoints k).range := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hb, hw⟩ : g ∈ D.borelSubgroup k ∧ g ∈ D.weylSubgroup k := hg
    obtain ⟨u, hu, s, rfl⟩ := (D.mem_borelSubgroup_iff k).mp hb
    have hu_weyl : u ∈ D.weylSubgroup k := by
      have hts := D.torusPoints_mem_weylSubgroup k s
      simpa only [mul_inv_cancel_right] using (D.weylSubgroup k).mul_mem hw
        ((D.weylSubgroup k).inv_mem hts)
    have hu_one : u = 1 := Subgroup.mem_bot.mp <| by
      rw [← D.positivePoints_inf_weylSubgroup_eq_bot k]
      exact ⟨hu, hu_weyl⟩
    rw [hu_one, one_mul]
    exact ⟨s, rfl⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨D.range_torusPoints_le_borelSubgroup k ⟨s, rfl⟩, D.torusPoints_mem_weylSubgroup k s⟩

/-! ### Simple-reflection multiplication of Borel double cosets -/

private theorem weylElement_conj_mem_borelSubgroup_of_mem_diff_singleton (i : Fin t.rank)
    {v : D.points k}
    (hv : v ∈ (⨆ γ ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \ {t.simpleIndex ht i},
      (D.rootSubgroupPoints γ k).range : Subgroup (D.points k))) :
    D.weylElement (t.simpleIndex ht i) k 1 * v *
      (D.weylElement (t.simpleIndex ht i) k 1)⁻¹ ∈ D.borelSubgroup k := by
  have hle : (⨆ γ ∈
        posRoots (t.rationalRootSystem ht) (t.rationalBase ht) \ {t.simpleIndex ht i},
      (D.rootSubgroupPoints γ k).range : Subgroup (D.points k)) ≤ D.positivePoints k :=
    iSup₂_le fun γ hγ => by
      rintro _ ⟨w, rfl⟩
      exact D.rootSubgroupPoints_mem_positivePoints k hγ.1 w
  exact D.positivePoints_le_borelSubgroup k <| hle <|
    (Subgroup.mem_normalizer_iff.mp
      (D.weylElement_mem_normalizer_positivePoints_diff_singleton k i 1) v).mp hv

/-- **Length-increasing simple-reflection cell multiplication.** If `(D.weylProjection k n)⁻¹`
sends the simple root `αᵢ` to a positive root, then multiplying `B n B` on the left by
`B nᵢ(1) B` yields the single double coset `B (nᵢ(1) n) B`. -/
theorem doubleCoset_weylElement_mul_eq_of_mem_posRoots (i : Fin t.rank) (n : D.weylSubgroup k)
    (hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n)⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1)
        (D.borelSubgroup k) (D.borelSubgroup k) *
      DoubleCoset.doubleCoset (n : D.points k)
        (D.borelSubgroup k) (D.borelSubgroup k) =
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1 * (n : D.points k))
      (D.borelSubgroup k) (D.borelSubgroup k) := by
  let B := D.borelSubgroup k
  let ni := D.weylElement (t.simpleIndex ht i) k 1
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
    obtain ⟨b₁, hb₁, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
    obtain ⟨b', hb', b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    obtain ⟨u, hu, s, hbb⟩ := (D.mem_borelSubgroup_iff k).mp (B.mul_mem hb hb')
    obtain ⟨v, hv, a, rfl⟩ :=
      (D.mem_positivePoints_iff_exists_mul_rootSubgroupPoints k i u).mp hu
    have hv_conj : ni * v * ni⁻¹ ∈ B :=
      D.weylElement_conj_mem_borelSubgroup_of_mem_diff_singleton k i hv
    have ht_conj : (n : D.points k)⁻¹ * D.torusPoints k s * (n : D.points k) ∈ B := by
      have hn_inv : (n : D.points k)⁻¹ ∈ Subgroup.normalizer (D.torusPoints k).range :=
        D.weylSubgroup_le_normalizer_range_torusPoints k (inv_mem n.property)
      exact D.range_torusPoints_le_borelSubgroup k
        (by simpa using (Subgroup.mem_normalizer_iff.mp hn_inv _).mp ⟨s, rfl⟩)
    obtain ⟨c, hc⟩ := D.exists_unit_conj_rootSubgroupPoints k n⁻¹ (t.simpleIndex ht i)
    have hx_conj : (n : D.points k)⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k a *
        (n : D.points k) ∈ B := by
      have hceq : (n : D.points k)⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k a *
          (n : D.points k) =
          D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).weylGroupToPerm
            (D.weylProjection k n)⁻¹ (t.simpleIndex ht i)) k (ofAdd ((c : k) * toAdd a)) := by
        simpa [MulAut.conj_apply] using hc (toAdd a)
      rw [hceq]
      exact D.positivePoints_le_borelSubgroup k (D.rootSubgroupPoints_mem_positivePoints k hpos _)
    refine DoubleCoset.mem_doubleCoset.mpr
      ⟨b₁ * (ni * v * ni⁻¹), B.mul_mem hb₁ hv_conj,
        ((n : D.points k)⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) k a * (n : D.points k)) *
          ((n : D.points k)⁻¹ * D.torusPoints k s * (n : D.points k)) * b₂,
        B.mul_mem (B.mul_mem hx_conj ht_conj) hb₂, ?_⟩
    dsimp only [ni]
    calc
      (b₁ * D.weylElement (t.simpleIndex ht i) k 1 * b) * (b' * (n : D.points k) * b₂) =
          b₁ * D.weylElement (t.simpleIndex ht i) k 1 * (b * b') * (n : D.points k) * b₂ := by
        group
      _ = _ := by rw [← hbb]; group
  · exact DoubleCoset.doubleCoset_mul_subset_mul_doubleCoset B B B B.one_mem ni (n : D.points k)

private theorem weylElement_mul_rootSubgroup_mul_weylElement_mem (i : Fin t.rank)
    (a : Multiplicative k) :
    D.weylElement (t.simpleIndex ht i) k 1 *
        D.rootSubgroupPoints (t.simpleIndex ht i) k a *
        D.weylElement (t.simpleIndex ht i) k 1 ∈
      (D.borelSubgroup k : Set (D.points k)) ∪
        DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1)
          (D.borelSubgroup k) (D.borelSubgroup k) := by
  let B := D.borelSubgroup k
  have hpos_i : t.simpleIndex ht i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
    simpleIndex_mem_posRoots i
  have hcoroot_mem (u : kˣ) : D.simpleCorootPoints i k u ∈ B := by
    rw [D.simpleCorootPoints_eq_torusPoints]
    exact D.range_torusPoints_le_borelSubgroup k ⟨_, rfl⟩
  by_cases ha : toAdd a = 0
  · left
    have ha1 : a = 1 := toAdd.injective ha
    rw [ha1, map_one, mul_one, D.weylElement_mul_self i k]
    exact hcoroot_mem (-1)
  · right
    let ua : kˣ := Units.mk0 (toAdd a) ha
    have hua : D.rootSubgroupPoints (t.simpleIndex ht i) k a =
        D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (ua : k)) := by
      simp [ua]
    rw [hua, D.weylElement_mul_rootSubgroup_mul_weylElement i k ua]
    have hx_mem : D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((ua⁻¹ : kˣ) : k))) ∈ B :=
      D.positivePoints_le_borelSubgroup k (D.rootSubgroupPoints_mem_positivePoints k hpos_i _)
    exact DoubleCoset.mem_doubleCoset.mpr
      ⟨D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((ua⁻¹ : kˣ) : k))) *
          D.simpleCorootPoints i k (-ua⁻¹),
        B.mul_mem hx_mem (hcoroot_mem (-ua⁻¹)),
        D.rootSubgroupPoints (t.simpleIndex ht i) k (ofAdd (-((ua⁻¹ : kˣ) : k))),
        hx_mem, by group⟩

/-- The square of a simple-reflection Borel double coset lies in `B ∪ B nᵢ(1) B`. -/
theorem doubleCoset_weylElement_mul_self_subset (i : Fin t.rank) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1)
        (D.borelSubgroup k) (D.borelSubgroup k) *
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1)
        (D.borelSubgroup k) (D.borelSubgroup k) ⊆
    (D.borelSubgroup k : Set (D.points k)) ∪
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1)
        (D.borelSubgroup k) (D.borelSubgroup k) := by
  let B := D.borelSubgroup k
  let ni := D.weylElement (t.simpleIndex ht i) k 1
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨b₁, hb₁, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx
  obtain ⟨b', hb', b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
  obtain ⟨u, hu, s, hbb⟩ := (D.mem_borelSubgroup_iff k).mp (B.mul_mem hb hb')
  obtain ⟨v, hv, a, rfl⟩ :=
    (D.mem_positivePoints_iff_exists_mul_rootSubgroupPoints k i u).mp hu
  have hv_conj : ni * v * ni⁻¹ ∈ B :=
    D.weylElement_conj_mem_borelSubgroup_of_mem_diff_singleton k i hv
  have ht_conj : ni⁻¹ * D.torusPoints k s * ni ∈ B := by
    have hni_inv : ni⁻¹ ∈ Subgroup.normalizer (D.torusPoints k).range :=
      inv_mem (D.weylElement_mem_normalizer_range_torusPoints i k)
    exact D.range_torusPoints_le_borelSubgroup k
      (by simpa using (Subgroup.mem_normalizer_iff.mp hni_inv _).mp ⟨s, rfl⟩)
  have hmid : (b₁ * ni * b) * (b' * ni * b₂) =
      (b₁ * (ni * v * ni⁻¹)) * (ni * D.rootSubgroupPoints (t.simpleIndex ht i) k a * ni) *
        ((ni⁻¹ * D.torusPoints k s * ni) * b₂) := by
    calc
      (b₁ * ni * b) * (b' * ni * b₂) =
          b₁ * ni * (b * b') * ni * b₂ := by group
      _ = b₁ * ni * (v * D.rootSubgroupPoints (t.simpleIndex ht i) k a * D.torusPoints k s) *
          ni * b₂ := by rw [← hbb]
      _ = _ := by group
  rw [hmid]
  rcases D.weylElement_mul_rootSubgroup_mul_weylElement_mem k i a with hB | hni
  · exact Or.inl (B.mul_mem (B.mul_mem (B.mul_mem hb₁ hv_conj) hB) (B.mul_mem ht_conj hb₂))
  · obtain ⟨c₁, hc₁, c₂, hc₂, hc⟩ := DoubleCoset.mem_doubleCoset.mp hni
    dsimp only [ni] at hv_conj ht_conj ⊢
    rw [hc]
    exact Or.inr <| DoubleCoset.mem_doubleCoset.mpr
      ⟨(b₁ * (D.weylElement (t.simpleIndex ht i) k 1 * v *
          (D.weylElement (t.simpleIndex ht i) k 1)⁻¹)) * c₁,
        B.mul_mem (B.mul_mem hb₁ hv_conj) hc₁,
        c₂ * (((D.weylElement (t.simpleIndex ht i) k 1)⁻¹ * D.torusPoints k s *
          D.weylElement (t.simpleIndex ht i) k 1) * b₂),
        B.mul_mem hc₂ (B.mul_mem ht_conj hb₂), by group⟩

private theorem doubleCoset_weylElement_inv_mul_eq (i : Fin t.rank) (g : D.points k) :
    DoubleCoset.doubleCoset ((D.weylElement (t.simpleIndex ht i) k 1)⁻¹ * g)
        (D.borelSubgroup k) (D.borelSubgroup k) =
      DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1 * g)
        (D.borelSubgroup k) (D.borelSubgroup k) := by
  apply DoubleCoset.doubleCoset_eq_of_mem
  refine DoubleCoset.mem_doubleCoset.mpr
    ⟨(D.simpleCorootPoints i k (-1))⁻¹, ?_, 1, (D.borelSubgroup k).one_mem, ?_⟩
  · rw [D.simpleCorootPoints_eq_torusPoints]
    exact inv_mem (D.range_torusPoints_le_borelSubgroup k ⟨_, rfl⟩)
  · rw [← D.weylElement_mul_self i k]
    group

/-- **Simple-reflection double-coset multiplication.** Over every field `k`, multiplying any cell
`B n B` (`n ∈ D.weylSubgroup k`) on the left by `B nᵢ(1) B` lands in
`B (nᵢ(1) n) B ∪ B n B`. -/
theorem doubleCoset_weylElement_mul_subset (i : Fin t.rank) (n : D.weylSubgroup k) :
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1)
        (D.borelSubgroup k) (D.borelSubgroup k) *
      DoubleCoset.doubleCoset (n : D.points k)
        (D.borelSubgroup k) (D.borelSubgroup k) ⊆
    DoubleCoset.doubleCoset (D.weylElement (t.simpleIndex ht i) k 1 * (n : D.points k))
        (D.borelSubgroup k) (D.borelSubgroup k) ∪
      DoubleCoset.doubleCoset (n : D.points k)
        (D.borelSubgroup k) (D.borelSubgroup k) := by
  let B := D.borelSubgroup k
  let ni : D.weylSubgroup k := ⟨D.weylElement (t.simpleIndex ht i) k 1,
    D.weylElement_mem_weylSubgroup k i⟩
  by_cases hpos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n)⁻¹
      (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)
  · rw [D.doubleCoset_weylElement_mul_eq_of_mem_posRoots k i n hpos]
    exact Set.subset_union_left
  · have hneg := (not_mem_posRoots_iff_mem_negRoots _ _ _).mp hpos
    let m : D.weylSubgroup k := ni⁻¹ * n
    have hm_pos : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k m)⁻¹
        (t.simpleIndex ht i) ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      have hperm : (t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k m)⁻¹
          (t.simpleIndex ht i) =
          (t.rationalRootSystem ht).reflectionPerm
            ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n)⁻¹
              (t.simpleIndex ht i))
            ((t.simplyConnectedRootDatum ht).weylGroupToPerm (D.weylProjection k n)⁻¹
              (t.simpleIndex ht i)) := by
        simp only [m, map_mul, map_inv, mul_inv_rev, inv_inv, ni, D.weylProjection_weylElement,
          Equiv.Perm.mul_apply, RootPairing.weylGroupToPerm_ofIdx_apply,
          t.reflectionPerm_rationalRootSystem ht]
        exact (t.simplyConnectedRootDatum ht).weylGroupToPerm_neg
          (D.weylProjection k n)⁻¹ (t.simpleIndex ht i)
      rw [hperm]
      exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots _ _ _).mpr hneg
    have hBn : DoubleCoset.doubleCoset (n : D.points k) B B =
        DoubleCoset.doubleCoset (ni : D.points k) B B *
          DoubleCoset.doubleCoset (m : D.points k) B B := by
      have heq := D.doubleCoset_weylElement_mul_eq_of_mem_posRoots k i m hm_pos
      have hnim : (ni : D.points k) * (m : D.points k) = (n : D.points k) := by simp [m]
      simpa only [ni, hnim] using heq.symm
    have hBm_absorb : (B : Set (D.points k)) * DoubleCoset.doubleCoset (m : D.points k) B B =
        DoubleCoset.doubleCoset (m : D.points k) B B :=
      Set.Subset.antisymm
        (by rintro _ ⟨b, hb, y, hy, rfl⟩; exact (DoubleCoset.mul_mem_doubleCoset_iff hb).mpr hy)
        (fun z hz => Set.mem_mul.mpr ⟨1, B.one_mem, z, hz, one_mul z⟩)
    calc
      DoubleCoset.doubleCoset (ni : D.points k) B B * DoubleCoset.doubleCoset (n : D.points k) B B
          = (DoubleCoset.doubleCoset (ni : D.points k) B B *
              DoubleCoset.doubleCoset (ni : D.points k) B B) *
              DoubleCoset.doubleCoset (m : D.points k) B B := by rw [hBn, mul_assoc]
      _ ⊆ ((B : Set (D.points k)) ∪ DoubleCoset.doubleCoset (ni : D.points k) B B) *
            DoubleCoset.doubleCoset (m : D.points k) B B :=
          Set.mul_subset_mul_right (D.doubleCoset_weylElement_mul_self_subset k i)
      _ = DoubleCoset.doubleCoset ((ni : D.points k) * (n : D.points k)) B B ∪
            DoubleCoset.doubleCoset (n : D.points k) B B := by
          rw [Set.union_mul, hBm_absorb, ← hBn, ← D.doubleCoset_weylElement_inv_mul_eq k i]
          rfl

end TauCeti.DynkinType.ChevalleyDatum
