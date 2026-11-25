/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Positive
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Word

/-!
# Word factorization of the Weyl subgroup and its intersection with the Borel subgroup

For a Chevalley datum `D` over any commutative ring `A`, the pinned simple Weyl representatives
satisfy `nᵢ(1)² = αᵢ∨(-1) ∈ T_D(A)` and normalize the actual torus `T_D(A)`. Consequently every
element of `D.weylSubgroup A` decomposes as a positive word in the pinned simple Weyl
representatives followed by an actual torus point.

Over every nontrivial commutative ring `A`, combining this word decomposition with the Weyl-word
separation criterion `simplyConnectedWeylWordProd_eq_one_of_mem_borelSubgroup` shows that any Weyl
word in `D.weylSubgroup A` lying in `D.borelSubgroup A` spells `1` in the Weyl group, hence lies in
`T_D(A)` by `weylWord_mem_range_torusPoints_of_simplyConnectedWeylWordProd_eq_one`; so such a
word lies in `D.borelSubgroup A` exactly when it spells `1`
(`ChevalleyDatum.weylWord_mem_borelSubgroup_iff`). Together
with `positivePoints_inf_range_torusPoints_eq_bot`, this yields the exact
intersections `D.positivePoints A ⊓ D.weylSubgroup A = ⊥` and
`D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range` over every commutative ring `A`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 22 and 27, and Chapter 5,
  Theorem 7.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

open Multiplicative
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section CommRing

variable (A : Type v) [CommRing A]

/-- Every element of `D.weylSubgroup A` is a positive word in the pinned simple Weyl
representatives followed by a point of the actual torus, over every commutative ring. -/
theorem mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints {g : D.points A} :
    g ∈ D.weylSubgroup A ↔
      ∃ (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ),
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
          D.torusPoints A s = g := by
  let r : Fin t.rank → D.points A := fun i => D.weylElement (t.simpleIndex ht i) A 1
  have htorus_mul (s₀ : Fin t.rank → Aˣ) (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ) :
      ∃ s' : Fin t.rank → Aˣ,
        D.torusPoints A s₀ * ((l.map r).prod * D.torusPoints A s) =
          (l.map r).prod * D.torusPoints A s' := by
    have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints A
      (inv_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l))
    obtain ⟨s₁, hs₁⟩ := (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints A s₀)).mp
      ⟨s₀, rfl⟩
    refine ⟨s₁ * s, ?_⟩
    have hcomm : D.torusPoints A s₀ * (l.map r).prod = (l.map r).prod * D.torusPoints A s₁ := by
      rw [hs₁]
      dsimp only [r]
      group
    rw [← mul_assoc, hcomm, mul_assoc, (D.torusPoints A).map_mul]
  constructor
  · intro hg
    rw [D.weylSubgroup_def] at hg
    induction hg using Subgroup.closure_induction_left with
    | one =>
      exact ⟨[], 1, by simp⟩
    | mul_left x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · obtain ⟨s', hs'⟩ := htorus_mul s₀ l s
        exact ⟨l, s', hs'.symm⟩
      · exact ⟨i :: l, s, by simp [mul_assoc]⟩
    | inv_mul_cancel x hx y _ ih =>
      obtain ⟨l, s, rfl⟩ := ih
      rcases hx with ⟨s₀, rfl⟩ | ⟨i, rfl⟩
      · rw [← map_inv]
        obtain ⟨s', hs'⟩ := htorus_mul s₀⁻¹ l s
        exact ⟨l, s', hs'.symm⟩
      · have hri_inv : (r i)⁻¹ =
            r i * D.torusPoints A (D.simpleCorootParameter i A (-1))⁻¹ := by
          apply inv_eq_of_mul_eq_one_right
          rw [← mul_assoc, D.weylElement_mul_self i A, D.simpleCorootPoints_eq_torusPoints,
            ← (D.torusPoints A).map_mul, mul_inv_cancel, map_one]
        rw [hri_inv, mul_assoc]
        obtain ⟨s', hs'⟩ := htorus_mul (D.simpleCorootParameter i A (-1))⁻¹ l s
        refine ⟨i :: l, s', ?_⟩
        dsimp only [r] at hs' ⊢
        simp only [List.map_cons, List.prod_cons, mul_assoc]
        rw [← hs']
  · rintro ⟨l, s, rfl⟩
    exact mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup A l)
      (D.torusPoints_mem_weylSubgroup A s)

/-- **A Weyl word lies in the positive Borel subgroup if and only if it spells `1`.** Over any
nontrivial commutative ring `A`, a product of pinned simple Weyl representatives belongs to
`D.borelSubgroup A` precisely when its image in the Weyl group is the identity. -/
theorem weylWord_mem_borelSubgroup_iff [Nontrivial A] (l : List (Fin t.rank)) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ D.borelSubgroup A ↔
      t.simplyConnectedWeylWordProd ht l = 1 :=
  ⟨D.simplyConnectedWeylWordProd_eq_one_of_mem_borelSubgroup A l, fun hl =>
    D.range_torusPoints_le_borelSubgroup A
      (D.weylWord_mem_range_torusPoints_of_simplyConnectedWeylWordProd_eq_one A l hl)⟩

/-- Over every commutative ring, the positive point subgroup intersects the Weyl subgroup
trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot :
    D.positivePoints A ⊓ D.weylSubgroup A = ⊥ := by
  refine eq_bot_iff.mpr ?_
  intro u ⟨huP, huW⟩
  rw [Subgroup.mem_bot]
  rcases subsingleton_or_nontrivial A with _ | _
  · exact Subtype.ext (Units.ext (Matrix.ext fun _ _ => Subsingleton.elim _ _))
  · obtain ⟨l, s, hls⟩ := (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints A).mp huW
    have hlB : (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈
        D.borelSubgroup A := by
      rw [eq_mul_inv_of_mul_eq hls]
      exact mul_mem (D.positivePoints_le_borelSubgroup A huP)
        (inv_mem (D.range_torusPoints_le_borelSubgroup A ⟨s, rfl⟩))
    have hl := D.simplyConnectedWeylWordProd_eq_one_of_mem_borelSubgroup A l hlB
    have huT : u ∈ (D.torusPoints A).range := by
      rw [← hls]
      exact mul_mem
        (D.weylWord_mem_range_torusPoints_of_simplyConnectedWeylWordProd_eq_one A l hl) ⟨s, rfl⟩
    have hmem : u ∈ D.positivePoints A ⊓ (D.torusPoints A).range := ⟨huP, huT⟩
    rwa [D.positivePoints_inf_range_torusPoints_eq_bot A, Subgroup.mem_bot] at hmem

/-- Over every commutative ring, the intersection of the Borel-type subgroup and the Weyl subgroup
of a Chevalley datum is precisely the image of its actual torus. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup_eq_range_torusPoints :
    D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgB, hgW⟩ := hg
    obtain ⟨u, huP, s, rfl⟩ := (D.mem_borelSubgroup_iff A).mp hgB
    have huW : u ∈ D.weylSubgroup A := by
      have hts : D.torusPoints A s ∈ D.weylSubgroup A := D.torusPoints_mem_weylSubgroup A s
      simpa only [mul_inv_cancel_right] using mul_mem hgW (inv_mem hts)
    have hu1 : u = 1 := by
      have hmem : u ∈ D.positivePoints A ⊓ D.weylSubgroup A :=
        Subgroup.mem_inf.mpr ⟨huP, huW⟩
      rwa [D.positivePoints_inf_weylSubgroup_eq_bot A, Subgroup.mem_bot] at hmem
    rw [hu1, one_mul]
    exact ⟨s, rfl⟩
  · exact le_inf (D.range_torusPoints_le_borelSubgroup A) (D.range_torusPoints_le_weylSubgroup A)

/-- Read inside `D.weylSubgroup A`, the Borel subgroup cuts out the actual weight-lattice torus,
over every commutative ring. -/
@[simp]
theorem borelSubgroup_subgroupOf_weylSubgroup :
    (D.borelSubgroup A).subgroupOf (D.weylSubgroup A) =
      ((D.torusPoints A).range).subgroupOf (D.weylSubgroup A) := by
  rw [Subgroup.subgroupOf_inj, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints,
    inf_eq_left.mpr (D.range_torusPoints_le_weylSubgroup A)]

/-- `B ∩ N` is normal in `N`: it is the actual torus, which `N` normalizes. This is the normality
axiom of a Tits system with these subgroups. -/
instance normal_borelSubgroup_subgroupOf_weylSubgroup :
    ((D.borelSubgroup A).subgroupOf (D.weylSubgroup A)).Normal := by
  rw [D.borelSubgroup_subgroupOf_weylSubgroup A]
  infer_instance

/-- Over every commutative ring, an element of `D.weylSubgroup A` belongs to `D.borelSubgroup A`
if and only if it lies in the image of the actual torus. -/
theorem mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup
    {n : D.points A} (hn : n ∈ D.weylSubgroup A) :
    n ∈ D.borelSubgroup A ↔ n ∈ (D.torusPoints A).range := by
  rw [← D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints A, Subgroup.mem_inf]
  exact (and_iff_left hn).symm

/-- Inside the points of a Chevalley datum over every commutative ring, the Weyl subgroup meets the
positive unipotent subgroup trivially. -/
@[simp]
theorem weylSubgroup_inf_positivePoints_eq_bot :
    D.weylSubgroup A ⊓ D.positivePoints A = ⊥ := by
  rw [inf_comm, D.positivePoints_inf_weylSubgroup_eq_bot]

/-- Over every commutative ring, the intersection of the Weyl subgroup and the positive Borel
subgroup of a Chevalley datum is the actual weight-lattice torus. -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup_eq_range_torusPoints :
    D.weylSubgroup A ⊓ D.borelSubgroup A = (D.torusPoints A).range := by
  rw [inf_comm, D.borelSubgroup_inf_weylSubgroup_eq_range_torusPoints]

end CommRing

section Field

variable (K : Type v) [Field K]

/-- Any element of the Weyl subgroup that also belongs to the positive Borel subgroup has trivial
Weyl projection. -/
theorem weylProjection_eq_one_of_mem_borelSubgroup {g : D.weylSubgroup K}
    (hg : (g : D.points K) ∈ D.borelSubgroup K) :
    D.weylProjection K g = 1 := by
  obtain ⟨s, hs⟩ := (D.mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup K
    g.property).mp hg
  have hg' : g = ⟨D.torusPoints K s, D.torusPoints_mem_weylSubgroup K s⟩ := Subtype.ext hs.symm
  rw [hg', D.weylProjection_torusPoints]

end Field

end TauCeti.DynkinType.ChevalleyDatum
