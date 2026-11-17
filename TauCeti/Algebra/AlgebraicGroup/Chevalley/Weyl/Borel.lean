/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Blocks
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.LinearAlgebra.Matrix.Diagonal
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Intersection of the Borel and Weyl subgroups of a Chevalley datum

For a Chevalley datum `D` over a field `k`, let `U(k) = D.positivePoints k`,
`B(k) = D.borelSubgroup k = U(k) ⊔ T_D(k)`, and `N(k) = D.weylSubgroup k`. Over any commutative
ring `A`, `N(A)` normalizes `T_D(A)` and therefore conjugates torus points inside `B(A)`. Over any
field `k`, this file proves

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
   every weight space, while
   `ChevalleyDatum.coe_apply_eq_one_apply_of_mem_positivePoints_of_weight_eq` shows that its
   restriction to each weight space is already the identity.

## Main results

* `ChevalleyDatum.weylSubgroup_conj_torusPoints_mem_borelSubgroup`: over any commutative ring `A`,
  conjugating a point of `T_D(A)` by `w ∈ N(A)` stays inside `B(A)`.
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

open Multiplicative TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

-- Match the coefficient structure used by `D.points`, including on an algebraic closure.
attribute [local instance high] Ring.toIntAlgebra
attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Conjugating any point of the actual weight-lattice torus by an element of `D.weylSubgroup A`
stays inside `D.borelSubgroup A`. -/
theorem weylSubgroup_conj_torusPoints_mem_borelSubgroup
    (A : Type v) [CommRing A] (w : D.weylSubgroup A) (s : Fin t.rank → Aˣ) :
    (w : D.points A) * D.torusPoints A s * (w : D.points A)⁻¹ ∈ D.borelSubgroup A :=
  D.range_torusPoints_le_borelSubgroup A <|
    (Subgroup.mem_normalizer_iff.mp
      (D.weylSubgroup_le_normalizer_range_torusPoints A w.property)
      (D.torusPoints A s)).mp ⟨s, rfl⟩

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
    rw [← compl_posRoots, t.posRoots_rationalRootSystem ht, Set.mem_compl_iff, mem_posRoots]
    exact hinv.2
  obtain ⟨_, ⟨a, rfl⟩, hconj⟩ : D.rootSubgroupPoints γ k (ofAdd 1) ∈
      (D.rootSubgroupPoints j k).range.map (MulAut.conj u).toMonoidHom := by
    rw [D.map_range_rootSubgroupPoints_conj k ⟨u, huW⟩ j]
    exact ⟨ofAdd 1, rfl⟩
  have hposU : MulAut.conj u (D.rootSubgroupPoints j k a) ∈ D.positivePoints k := by
    rw [MulAut.conj_apply]
    exact mul_mem (mul_mem huU (D.rootSubgroupPoints_mem_positivePoints k hj_pos a)) (inv_mem huU)
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
  · exact D.coe_apply_eq_one_apply_of_mem_positivePoints_of_weight_eq K huK hwt
  · have hrq : r ≠ q := fun h => hwt (congrArg D.weight h)
    rw [Units.val_one, Matrix.one_apply_ne hrq]
    obtain ⟨s, hchar⟩ := exists_torusCharacter_ne (K := K) hwt
    have hcomm := (D.weylProjection_eq_iff k ⟨u, huW⟩ 1).mp hw1 s
    rw [map_one, MulAut.one_apply, ← hcoe, mul_inv_eq_iff_eq_mul] at hcomm
    have hcommM : Commute (Matrix.diagonal fun j => (torusCharacter s (D.weight j) : K))
        ((uK : Matrix.GeneralLinearGroup (Fin D.dim) K) : Matrix (Fin D.dim) (Fin D.dim) K) := by
      simpa only [Commute, SemiconjBy, Units.val_mul, diagGL_coe] using
        (congrArg Units.val hcomm).symm
    exact apply_eq_zero_of_commute_diagonal hcommM fun h => hchar (Units.ext h)

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
