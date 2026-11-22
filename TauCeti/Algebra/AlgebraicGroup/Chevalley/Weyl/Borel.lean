/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Word
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Lift
import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Positive

/-!
# Intersection of the Weyl subgroup with the Borel subgroup

For a Chevalley datum `D` over any nontrivial commutative ring `A`, combining the Weyl-word
factorization (`ChevalleyDatum.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints`), the
big-cell Weyl-word separation criterion
(`ChevalleyDatum.geckWeylWordProd_eq_one_of_mem_borelSubgroup`), and the Coxeter quotient lift
(`ChevalleyDatum.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one`) shows that a word in
the pinned simple Weyl representatives lies in `D.borelSubgroup A` if and only if it spells `1` in
the Weyl group (`ChevalleyDatum.weylWord_mem_borelSubgroup_iff`).

Consequently `D.weylSubgroup A ⊓ D.borelSubgroup A = (D.torusPoints A).range`
(`ChevalleyDatum.weylSubgroup_inf_borelSubgroup`) and `D.borelSubgroup A ⊓ D.weylSubgroup A =
(D.torusPoints A).range` (`ChevalleyDatum.borelSubgroup_inf_weylSubgroup`) hold over every
commutative ring `A` (including nonreduced rings, finite fields, bad characteristic, and the zero
ring), making `B(A) ∩ N(A)` normal in `N(A)`
(`ChevalleyDatum.normal_borelSubgroup_subgroupOf_weylSubgroup`) and yielding
`D.positivePoints A ⊓ D.weylSubgroup A = ⊥`
(`ChevalleyDatum.positivePoints_inf_weylSubgroup_eq_bot`).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 22 and 27, and Chapter 5,
  Theorem 7.
* R. W. Carter, *Simple Groups of Lie Type*, §§7.2 and 8.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

section CommRing

variable (A : Type v) [CommRing A]

/-- **A Weyl word lies in the positive Borel subgroup if and only if it spells `1`.** Over any
nontrivial commutative ring `A`, a product of pinned simple Weyl representatives belongs to
`D.borelSubgroup A` precisely when its image in the Weyl group is the identity. -/
theorem weylWord_mem_borelSubgroup_iff [Nontrivial A] (l : List (Fin t.rank)) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ D.borelSubgroup A ↔
      t.geckWeylWordProd ht l = 1 :=
  ⟨D.geckWeylWordProd_eq_one_of_mem_borelSubgroup A l, fun hl =>
    D.range_torusPoints_le_borelSubgroup A
      (D.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one A hl)⟩

/-- **The Weyl subgroup meets the Borel subgroup in the actual torus**, over every commutative
ring `A` (including nonreduced rings, finite fields, bad characteristic, and the zero ring). -/
@[simp]
theorem weylSubgroup_inf_borelSubgroup :
    D.weylSubgroup A ⊓ D.borelSubgroup A = (D.torusPoints A).range := by
  refine le_antisymm ?_ (le_inf
    (by rintro _ ⟨s, rfl⟩; exact D.torusPoints_mem_weylSubgroup A s)
    (D.range_torusPoints_le_borelSubgroup A))
  rintro g ⟨hgW, hgB⟩
  by_cases hA : Nontrivial A
  · obtain ⟨l, s, rfl⟩ := (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints A).mp hgW
    have hwordB : (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈
        D.borelSubgroup A := by
      have hsB : (D.torusPoints A s)⁻¹ ∈ D.borelSubgroup A :=
        (D.borelSubgroup A).inv_mem (D.range_torusPoints_le_borelSubgroup A ⟨s, rfl⟩)
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using (D.borelSubgroup A).mul_mem hgB hsB
    have hl : t.geckWeylWordProd ht l = 1 := (D.weylWord_mem_borelSubgroup_iff A l).mp hwordB
    exact (D.torusPoints A).range.mul_mem
      (D.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one A hl) ⟨s, rfl⟩
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact Subsingleton.elim _ _

/-- Symmetric form of `weylSubgroup_inf_borelSubgroup`: `B(A) ∩ N(A) = T(A)` over every
commutative ring `A`. -/
@[simp]
theorem borelSubgroup_inf_weylSubgroup :
    D.borelSubgroup A ⊓ D.weylSubgroup A = (D.torusPoints A).range := by
  rw [inf_comm, D.weylSubgroup_inf_borelSubgroup A]

/-- `B ∩ N` is normal in `N`: it is the actual torus, which `N` normalizes. This is the normality
axiom of a Tits system with these subgroups. -/
instance normal_borelSubgroup_subgroupOf_weylSubgroup :
    ((D.borelSubgroup A).subgroupOf (D.weylSubgroup A)).Normal := by
  rw [← Subgroup.inf_subgroupOf_left, inf_comm,
    D.borelSubgroup_inf_weylSubgroup A]
  infer_instance

/-- Over every commutative ring `A`, an element of `D.weylSubgroup A` belongs to
`D.borelSubgroup A` if and only if it lies in the image of the actual torus. -/
theorem mem_borelSubgroup_iff_mem_range_torusPoints_of_mem_weylSubgroup
    {n : D.points A} (hn : n ∈ D.weylSubgroup A) :
    n ∈ D.borelSubgroup A ↔ n ∈ (D.torusPoints A).range := by
  rw [← D.borelSubgroup_inf_weylSubgroup A, Subgroup.mem_inf]
  exact (and_iff_left hn).symm

/-- Conjugating any point of the actual weight-lattice torus by an element of `D.weylSubgroup A`
stays inside `D.borelSubgroup A`. -/
theorem weylSubgroup_conj_torusPoints_mem_borelSubgroup (w : D.weylSubgroup A)
    (s : Fin t.rank → Aˣ) :
    (w : D.points A) * D.torusPoints A s * (w : D.points A)⁻¹ ∈ D.borelSubgroup A :=
  D.range_torusPoints_le_borelSubgroup A <|
    (Subgroup.mem_normalizer_iff.mp
      (D.weylSubgroup_le_normalizer_range_torusPoints A w.property)
      (D.torusPoints A s)).mp ⟨s, rfl⟩

/-- Over every commutative ring, the positive point subgroup intersects the Weyl subgroup
trivially. -/
@[simp]
theorem positivePoints_inf_weylSubgroup_eq_bot :
    D.positivePoints A ⊓ D.weylSubgroup A = ⊥ :=
  eq_bot_mono
    (le_inf inf_le_left
      ((inf_le_inf_right _ (D.positivePoints_le_borelSubgroup A)).trans_eq
        (D.borelSubgroup_inf_weylSubgroup A)))
    (D.positivePoints_inf_range_torusPoints_eq_bot A)

/-- Inside the points of a Chevalley datum over every commutative ring, the Weyl subgroup meets
the positive unipotent subgroup trivially. -/
@[simp]
theorem weylSubgroup_inf_positivePoints_eq_bot :
    D.weylSubgroup A ⊓ D.positivePoints A = ⊥ := by
  rw [inf_comm, D.positivePoints_inf_weylSubgroup_eq_bot]

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
