/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Uniqueness in a simple Bruhat cell

For any Chevalley datum `D`, a positive simple root subgroup `X`, its pinned Weyl representative
`n`, and the positive Borel-type subgroup `B`, multiplication `X × B → X n B` is injective
over every commutative ring. Integral root-subgroup injectivity
(`ChevalleyDatum.rootSubgroupPoints_injective`) gives uniqueness of the additive root parameter as
well, and over a field the rank-one collection theorem yields a unique open-cell factorization
whenever a word in the opposite simple-root pair and the actual torus does not belong to `B`.

These are local rank-one normal-form results, not a Bruhat decomposition of the entire point group.
The central inputs are the opposite-intersection theorem in `Chevalley.Borel`, the rank-one
collection theorem `ChevalleyDatum.mem_sup_simpleRootPair_torus_iff`, and integral root-subgroup
injectivity in `Chevalley.Root.Injective`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Theorems 4 and 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §8.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (i : Fin t.rank) (A : Type v) [CommRing A]

/-- Over every commutative ring, a positive simple-root group meets the Borel conjugated
by the pinned simple Weyl representative trivially. -/
theorem disjoint_range_rootSubgroupPoints_map_conj_weylElement_borelSubgroup :
    Disjoint (D.rootSubgroupPoints (t.simpleIndex ht i) A).range
      ((D.borelSubgroup A).map
        (MulAut.conj (D.weylElement (t.simpleIndex ht i) A 1)).toMonoidHom) := by
  apply Subgroup.disjoint_def.mpr
  rintro _ ⟨u, rfl⟩ hb
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hb
  let n := D.weylElement (t.simpleIndex ht i) A 1
  have hnn : n * n ∈ D.borelSubgroup A := by
    rw [D.weylElement_mul_self, D.simpleCorootPoints_eq_torusPoints]
    exact D.torusPoints_mem_borelSubgroup A _
  rw [D.rootSubgroupPoints_eq_one_iff]
  apply (D.weylElement_conj_rootSubgroupPoints_simpleIndex_mem_borelSubgroup_iff A i u).mp
  have he : n * D.rootSubgroupPoints (t.simpleIndex ht i) A u * n⁻¹ =
      (n * n) * (n⁻¹ * D.rootSubgroupPoints (t.simpleIndex ht i) A u * n) *
        (n * n)⁻¹ := by group
  rw [he]
  exact (D.borelSubgroup A).mul_mem ((D.borelSubgroup A).mul_mem hnn hb)
    ((D.borelSubgroup A).inv_mem hnn)

/-- Over every commutative ring, the simple Bruhat cell has unique root-group and right
Borel factors. The root factor is an element, not a chosen additive parameter. -/
theorem range_rootSubgroupPoints_mul_weylElement_mul_borelSubgroup_injective :
    Function.Injective (fun p : (D.rootSubgroupPoints (t.simpleIndex ht i) A).range ×
        D.borelSubgroup A =>
      (p.fst : D.points A) * D.weylElement (t.simpleIndex ht i) A 1 * p.snd) :=
  Subgroup.mul_mul_injective_of_disjoint _ _
    (D.disjoint_range_rootSubgroupPoints_map_conj_weylElement_borelSubgroup i A)

/-- Over a field, a word in an opposite simple-root pair and the actual torus that lies
outside the positive Borel has exactly one open-cell root-group/Borel factorization. The Borel
factor uses the actual character-lattice torus, including for adjoint data. -/
theorem existsUnique_mul_weylElement_mul_eq_of_mem_sup_simpleRootPair_torus_of_notMem_borelSubgroup
    (K : Type v) [Field K] (g : D.points K)
    (hg : g ∈ Subgroup.closure
      (Set.range (D.rootSubgroupPoints (t.simpleIndex ht i) K) ∪
        Set.range (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) K)) ⊔ (D.torusPoints K).range)
    (hB : g ∉ D.borelSubgroup K) :
    ∃! p : (D.rootSubgroupPoints (t.simpleIndex ht i) K).range × D.borelSubgroup K,
      (p.fst : D.points K) * D.weylElement (t.simpleIndex ht i) K 1 * p.snd = g := by
  have hinj := D.range_rootSubgroupPoints_mul_weylElement_mul_borelSubgroup_injective i K
  apply hinj.existsUnique_iff_exists.mpr
  have hx (a : K) : D.rootSubgroupPoints (t.simpleIndex ht i) K
      (Multiplicative.ofAdd a) ∈ D.borelSubgroup K :=
    D.rootSubgroupPoints_mem_borelSubgroup_of_mem_posRoots K (simpleIndex_mem_posRoots i) _
  have hT (s : Fin t.rank → Kˣ) : D.torusPoints K s ∈ D.borelSubgroup K :=
    D.torusPoints_mem_borelSubgroup K s
  rcases (D.mem_sup_simpleRootPair_torus_iff i K g).mp hg with
    ⟨a, s, he⟩ | ⟨a, b, s, he⟩
  · exact (hB (he ▸ (D.borelSubgroup K).mul_mem (hx a) (hT s))).elim
  · refine ⟨(⟨_, ⟨Multiplicative.ofAdd a, rfl⟩⟩,
      ⟨_, (D.borelSubgroup K).mul_mem (hx b) (hT s)⟩), ?_⟩
    dsimp only
    rw [he]
    group

/-- For any Chevalley datum, the simple Bruhat normal form has a unique additive root parameter
and a unique right Borel factor, over every commutative ring. -/
theorem rootSubgroupPoints_ofAdd_mul_weylElement_mul_borelSubgroup_injective :
    Function.Injective (fun p : A × D.borelSubgroup A =>
      D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd p.fst) *
        D.weylElement (t.simpleIndex ht i) A 1 * p.snd) := by
  intro p q h
  have he := D.range_rootSubgroupPoints_mul_weylElement_mul_borelSubgroup_injective i A
    (a₁ := (⟨_, ⟨Multiplicative.ofAdd p.fst, rfl⟩⟩, p.snd))
    (a₂ := (⟨_, ⟨Multiplicative.ofAdd q.fst, rfl⟩⟩, q.snd)) h
  have hpq := congrArg (fun z => (z.fst : D.points A)) he
  have ha := D.rootSubgroupPoints_injective (t.simpleIndex ht i) A hpq
  exact Prod.ext (congrArg Multiplicative.toAdd ha) (congrArg (fun z => z.snd) he)

/-- Over a field, an opposite-simple-root-pair/torus word of any Chevalley datum outside the Borel
has a unique additive root parameter and right Borel factor in its simple Bruhat form. -/
theorem existsUnique_rootSubgroupPoints_ofAdd_mul_weylElement_mul_eq
    (K : Type v) [Field K] (g : D.points K)
    (hg : g ∈ Subgroup.closure
      (Set.range (D.rootSubgroupPoints (t.simpleIndex ht i) K) ∪
        Set.range (D.rootSubgroupPoints
          ((t.simplyConnectedRootDatum ht).reflectionPerm
            (t.simpleIndex ht i) (t.simpleIndex ht i)) K)) ⊔
        (D.torusPoints K).range)
    (hB : g ∉ D.borelSubgroup K) :
    ∃! p : K × D.borelSubgroup K,
      D.rootSubgroupPoints (t.simpleIndex ht i) K (Multiplicative.ofAdd p.fst) *
        D.weylElement (t.simpleIndex ht i) K 1 * p.snd = g := by
  apply (D.rootSubgroupPoints_ofAdd_mul_weylElement_mul_borelSubgroup_injective
    i K).existsUnique_iff_exists.mpr
  obtain ⟨⟨⟨_, u, rfl⟩, b⟩, he⟩ := (
    D.existsUnique_mul_weylElement_mul_eq_of_mem_sup_simpleRootPair_torus_of_notMem_borelSubgroup
      i K g hg hB).exists
  exact ⟨(Multiplicative.toAdd u, b), he⟩

end TauCeti.DynkinType.ChevalleyDatum
