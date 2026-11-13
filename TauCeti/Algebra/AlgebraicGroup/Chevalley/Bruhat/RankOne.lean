/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected

/-!
# Uniqueness in a simple Bruhat cell

For a Chevalley datum, a positive simple root subgroup `X`, its pinned Weyl representative
`n`, and the positive Borel-type subgroup `B`, multiplication `X × B → X n⁻¹ B` is injective.
Consequently the existing rank-one collection theorem has a unique open-cell factorization,
with a root-group element and a Borel element, whenever
a word in the opposite simple-root pair and the actual torus does not belong to `B`.
The inverse representative is used so that the relevant conjugation is by `n`, exactly as
in the pinned opposite-root equation.

These results concern root-group elements for an arbitrary datum: injectivity of every root
parameter over an arbitrary ring is not assumed. For the simply connected datum, injectivity
of the root map gives uniqueness of the additive parameter as well. They are local normal-form
results, not a Bruhat decomposition of the entire point group.

The central inputs are the native opposite-intersection theorem in `Chevalley.Borel`, the
rank-one collection theorem `ChevalleyDatum.mem_sup_simpleRootPair_torus_iff`, and the
simply connected integral root-map injectivity theorem.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorems 4 and 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §8.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (i : Fin t.rank) (A : Type v) [CommRing A]

/-- The simple Bruhat cell has unique root-group and right Borel factors. The Weyl
representative is inverted; the root factor is an element, not a chosen additive parameter. -/
theorem simpleRoot_bruhat_injective :
    Function.Injective (fun p : (D.rootSubgroupPoints (t.simpleIndex ht i) A).range ×
        D.borelSubgroup A =>
      (p.1 : D.points A) * (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ * p.2) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ h
  let n := D.weylElement (t.simpleIndex ht i) A 1
  dsimp only at h
  have he : n * ((x : D.points A)⁻¹ * y) * n⁻¹ =
      (b : D.points A) * (c : D.points A)⁻¹ := by
    calc
      _ = ((x : D.points A) * n⁻¹)⁻¹ * ((y : D.points A) * n⁻¹ * c) *
          (c : D.points A)⁻¹ := by group
      _ = ((x : D.points A) * n⁻¹)⁻¹ * ((x : D.points A) * n⁻¹ * b) *
          (c : D.points A)⁻¹ := by rw [← h]
      _ = _ := by group
  obtain ⟨u, hu⟩ := (D.rootSubgroupPoints (t.simpleIndex ht i) A).range.mul_mem
    ((D.rootSubgroupPoints (t.simpleIndex ht i) A).range.inv_mem x.property) y.property
  have hm : n * D.rootSubgroupPoints (t.simpleIndex ht i) A u * n⁻¹ ∈
      D.borelSubgroup A := by
    rw [hu, he]
    exact (D.borelSubgroup A).mul_mem b.property ((D.borelSubgroup A).inv_mem c.property)
  have hz := (D.weylElement_conj_rootSubgroupPoints_simpleIndex_mem_borelSubgroup_iff
    A i u).mp hm
  have hxy : x = y := Subtype.ext (inv_mul_eq_one.mp (hu.symm.trans hz))
  subst y
  have hbc : b = c := Subtype.ext (mul_left_cancel h)
  exact Prod.ext rfl hbc

/-- A word in an opposite simple-root pair and the actual torus that lies outside the
positive Borel has exactly one open-cell root-group/Borel factorization. The Borel factor
uses the actual character-lattice torus, including for adjoint data. -/
theorem existsUnique_simpleRoot_bruhat_of_notMem_borelSubgroup
    (K : Type v) [Field K] (g : D.points K)
    (hg : g ∈ Subgroup.closure
      (Set.range (D.rootSubgroupPoints (t.simpleIndex ht i) K) ∪
        Set.range (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) K)) ⊔ (D.torusPoints K).range)
    (hB : g ∉ D.borelSubgroup K) :
    ∃! p : (D.rootSubgroupPoints (t.simpleIndex ht i) K).range × D.borelSubgroup K,
      (p.1 : D.points K) * (D.weylElement (t.simpleIndex ht i) K 1)⁻¹ * p.2 = g := by
  apply (D.simpleRoot_bruhat_injective i K).existsUnique_iff_exists.mpr
  have hx (a : K) : D.rootSubgroupPoints (t.simpleIndex ht i) K
      (Multiplicative.ofAdd a) ∈ D.borelSubgroup K :=
    D.positivePoints_le_borelSubgroup K (D.rootSubgroupPoints_mem_positivePoints K
      (support_subset_posRoots _ _ (t.simpleIndex_mem_support i)) _)
  have hT (s : Fin t.rank → Kˣ) : D.torusPoints K s ∈ D.borelSubgroup K :=
    D.range_torusPoints_le_borelSubgroup K ⟨s, rfl⟩
  rcases (D.mem_sup_simpleRootPair_torus_iff i K g).mp hg with
    ⟨a, s, he⟩ | ⟨a, b, s, he⟩
  · exact (hB (he ▸ (D.borelSubgroup K).mul_mem (hx a) (hT s))).elim
  · let n := D.weylElement (t.simpleIndex ht i) K 1
    have hnn : n * n ∈ D.borelSubgroup K := by
      rw [D.weylElement_mul_self]
      rw [D.simpleCorootPoints_eq_torusPoints]
      exact hT _
    let c : D.borelSubgroup K := ⟨n * n *
      D.rootSubgroupPoints (t.simpleIndex ht i) K (Multiplicative.ofAdd b) * D.torusPoints K s,
      (D.borelSubgroup K).mul_mem ((D.borelSubgroup K).mul_mem hnn (hx b)) (hT s)⟩
    refine ⟨(⟨_, ⟨Multiplicative.ofAdd a, rfl⟩⟩, c), ?_⟩
    dsimp only [c]
    rw [he]
    dsimp only [n]
    group

end TauCeti.DynkinType.ChevalleyDatum

namespace TauCeti.DynkinType

variable (t : DynkinType) (ht : t.Valid) (i : Fin t.rank)
variable (A : Type v) [CommRing A]

/-- For the simply connected datum, the simple Bruhat normal form has a unique additive
root parameter and a unique right Borel factor, over every commutative ring. -/
theorem scChevalleyDatum_simpleRoot_bruhat_injective :
    Function.Injective (fun p : A × (t.scChevalleyDatum ht).borelSubgroup A =>
      (t.scChevalleyDatum ht).rootSubgroupPoints (t.simpleIndex ht i) A
          (Multiplicative.ofAdd p.1) *
        ((t.scChevalleyDatum ht).weylElement (t.simpleIndex ht i) A 1)⁻¹ * p.2) := by
  intro p q h
  have he := (t.scChevalleyDatum ht).simpleRoot_bruhat_injective i A
    (a₁ := (⟨_, ⟨Multiplicative.ofAdd p.1, rfl⟩⟩, p.2))
    (a₂ := (⟨_, ⟨Multiplicative.ofAdd q.1, rfl⟩⟩, q.2)) h
  have hpq := congrArg (fun z => (z.1 : (t.scChevalleyDatum ht).points A)) he
  have ha := t.scChevalleyDatum_rootSubgroupPoints_injective ht (t.simpleIndex ht i) A hpq
  exact Prod.ext (congrArg Multiplicative.toAdd ha) (congrArg (fun z => z.2) he)

end TauCeti.DynkinType
