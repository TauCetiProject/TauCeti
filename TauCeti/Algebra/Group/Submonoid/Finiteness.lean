/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import TauCeti.Algebra.Group.Submonoid.GroupCompletion
public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.LinearAlgebra.Basis.Order

/-!
# Finiteness of preimages and saturations of additive submonoids

This file establishes two forms of Gordan's lemma for finitely generated additive submonoids:

* **Preimages under homomorphisms**: the preimage of a finitely generated additive submonoid under a
  homomorphism from a finitely generated commutative monoid is finitely generated, provided the
  target is cancellative (`AddSubmonoid.FG.comap`). For instance, since the nonnegative integer
  vectors form a finitely generated submonoid of `ℤⁿ`, finitely many integral linear inequalities
  on a finitely generated abelian group cut out a finitely generated additive submonoid. The proof
  uses Mathlib's `AddSubmonoid.fg_iff_exists_fin_addMonoidHom` to parametrize both monoids by finite
  products of naturals, and `AddSubmonoid.fg_eqLocusM` to impose equality of their images (the
  slack-variable form of Gordan's lemma).
* **Bounded shifts and saturations**: for a finitely generated submonoid `S` of a free abelian
  group `L`, Euclidean division of natural generator coefficients bounds representatives of
  `S.nsmulSaturation` modulo `S` inside a finite coordinate box over the basis support of the
  generators, yielding a finite set `F ⊆ S.nsmulSaturation` with `S.nsmulSaturation = F + S`
  (`AddSubmonoid.FG.exists_finset_subset_nsmulSaturation_add`). Consequently `S.nsmulSaturation` is
  finitely generated (`AddSubmonoid.FG.nsmulSaturation`), and for any finitely generated submonoid
  `S` of an arbitrary torsion-free abelian group `G`, its saturation inside
  `AddSubgroup.closure (S : Set G)` is finitely generated
  (`AddSubmonoid.FG.nsmulSaturation_inf_closure`).

## Main results

* `AddSubmonoid.FG.comap`: preimages of finitely generated additive submonoids are finitely
  generated when the source monoid is finitely generated and the target is cancellative.
* `Submonoid.exists_finset_inclusion_mul` and `AddSubmonoid.exists_finset_inclusion_add`:
  restricting an ambient finite translate covering of `T` over `S ≤ T` to the subtype `T`.
* `AddSubmonoid.FG.exists_finset_subset_nsmulSaturation_add` and
  `AddSubmonoid.FG.exists_finset_subset_nsmulSaturation_inf_closure_add`: bounded-shift covering of
  saturations over `S`.
* `AddSubmonoid.FG.nsmulSaturation` and `AddSubmonoid.FG.nsmulSaturation_inf_closure`: Gordan's
  finiteness theorem for saturations.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 2, affine monoids and
  Gordan's lemma.
* W. Fulton, *Introduction to Toric Varieties*, §1.2, Proposition 1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2, Proposition 1.2.17.
-/

public section

/-- The preimage of a finitely generated additive submonoid of a cancellative commutative monoid
under a homomorphism from a finitely generated commutative monoid is finitely generated. -/
theorem AddSubmonoid.FG.comap {M G : Type*} [AddCommMonoid M] [AddCommMonoid G]
    [IsCancelAdd G] [AddMonoid.FG M] {P : AddSubmonoid G} (hP : P.FG) (f : M →+ G) :
    (P.comap f).FG := by
  obtain ⟨n, q, hq⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp
    (AddMonoid.FG.fg_top (M := M))
  obtain ⟨k, g, rfl⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp hP
  -- Pair a parameter of `M` with a slack vector parametrizing `P`, and keep the pairs whose
  -- images under `f` and `g` agree.
  let π := q.comp (AddMonoidHom.fst _ (Fin k → ℕ))
  convert (AddSubmonoid.fg_eqLocusM (f.comp π) (g.comp (.snd ..))).map π
  ext x
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := AddMonoidHom.mrange_eq_top.mp hq x
    exact ⟨(a, b), hb.symm, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha.symm⟩

namespace Submonoid

/-- Given submonoids `S ≤ T` of `M`, an ambient covering of `T` by finitely many left translates
of `S` restricts to a finite covering of the subtype `T` along `Submonoid.inclusion hST`. -/
@[to_additive
/-- Given additive submonoids `S ≤ T` of `M`, an ambient covering of `T` by finitely many shifts
of `S` restricts to a finite covering of the subtype `T` along `AddSubmonoid.inclusion hST`. -/]
theorem exists_finset_inclusion_mul {M : Type*} [MulOneClass M] {S T : Submonoid M}
    (hST : S ≤ T) (hF : ∃ F : Finset M, (F : Set M) ⊆ T ∧ ∀ x ∈ T, ∃ z ∈ F, ∃ s ∈ S, x = z * s) :
    ∃ F : Finset T, ∀ x : T, ∃ z ∈ F, ∃ s : S, x = z * Submonoid.inclusion hST s := by
  classical
  obtain ⟨F, hF_sub, hF_mul⟩ := hF
  refine ⟨F.subtype (· ∈ T), fun x => ?_⟩
  obtain ⟨z, hz, s, hs, hxz⟩ := hF_mul x.1 x.2
  exact ⟨⟨z, hF_sub hz⟩, Finset.mem_subtype.mpr hz, ⟨s, hs⟩, Subtype.ext hxz⟩

end Submonoid

namespace AddSubmonoid

section AmbientLattice

variable {L : Type*} [AddCommGroup L] [Module.Free ℤ L]

/-- **Bounded shifts for submonoid saturation.** If `S` is a finitely generated submonoid of a
free abelian group `L`, there is a finite subset `F ⊆ S.nsmulSaturation` such that every element of
`S.nsmulSaturation` is of the form `z + s` with `z ∈ F` and `s ∈ S`. -/
theorem FG.exists_finset_subset_nsmulSaturation_add {S : AddSubmonoid L} (hS : S.FG) :
    ∃ F : Finset L, (F : Set L) ⊆ S.nsmulSaturation ∧
      ∀ x ∈ S.nsmulSaturation, ∃ z ∈ F, ∃ s ∈ S, x = z + s := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  obtain ⟨m, g, hg⟩ := fg_iff_exists_fin_addMonoidHom.mp hS
  let a : Fin m → L := fun j => g (Pi.single j 1)
  have hg_eq (k : Fin m → ℕ) : g k = ∑ j, k j • a j := by
    have hk_sum : k = ∑ j, k j • Pi.single j 1 := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hk_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => map_nsmul g (k j) (Pi.single j 1)
  let J : Finset ι := Finset.univ.biUnion fun j => (b.repr (a j)).support
  let B : ι → ℤ := fun i => ∑ j, |b.repr (a j) i|
  have hB (i : ι) (hi : i ∉ J) : B i = 0 := by
    simp only [J, Finset.mem_biUnion, Finset.mem_univ, true_and, Finsupp.mem_support_iff,
      not_exists, not_not] at hi
    simp [B, hi]
  let box : Finset (J → ℤ) := Fintype.piFinset fun i => Finset.Icc (-B i.1) (B i.1)
  have hfin : {z : L | z ∈ S.nsmulSaturation ∧ ∀ i, |b.repr z i| ≤ B i}.Finite := by
    refine box.finite_toSet.of_injOn (f := fun z (i : J) => b.repr z i.1)
      (fun z hz => Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr (abs_le.mp (hz.2 i.1)))
      fun z₁ hz₁ z₂ hz₂ heq => b.repr.injective <| Finsupp.ext fun i => ?_
    by_cases hi : i ∈ J
    · exact congrFun heq ⟨i, hi⟩
    · exact (abs_nonpos_iff.mp ((hz₁.2 i).trans_eq (hB i hi))).trans
        (abs_nonpos_iff.mp ((hz₂.2 i).trans_eq (hB i hi))).symm
  refine ⟨hfin.toFinset, fun z hz => ((Set.Finite.mem_toFinset hfin).mp hz).1, fun x hx => ?_⟩
  obtain ⟨n, hn, hnx⟩ := mem_nsmulSaturation.mp hx
  rw [← hg, AddMonoidHom.mem_mrange] at hnx
  obtain ⟨k, hk⟩ := hnx
  let q : Fin m → ℕ := fun j => k j / n
  let r : Fin m → ℕ := fun j => k j % n
  let s : L := g q
  let z : L := x - s
  have hqr : n • q + r = k := by
    ext j
    simp [q, r, Nat.div_add_mod]
  have hnz : n • z = g r := by
    have hmap := congrArg g hqr
    simp only [map_add, map_nsmul, hk] at hmap
    simp [z, s, smul_sub, ← hmap]
  have hz_sat : z ∈ S.nsmulSaturation :=
    mem_nsmulSaturation.mpr ⟨n, hn, hnz ▸ hg ▸ ⟨r, rfl⟩⟩
  have hz_bound : ∀ i, |b.repr z i| ≤ B i :=
    b.abs_repr_le_of_nsmul_eq_sum hn (fun j _ => (Nat.mod_lt _ hn).le) (hnz.trans (hg_eq r))
  exact ⟨z, (Set.Finite.mem_toFinset hfin).mpr ⟨hz_sat, hz_bound⟩,
    s, hg ▸ ⟨q, rfl⟩, (sub_add_cancel x s).symm⟩

/-- **Gordan's lemma for submonoid saturation.** In a free abelian group `L`, the saturation of any
finitely generated additive submonoid `S` is finitely generated. -/
theorem FG.nsmulSaturation {S : AddSubmonoid L} (hS : S.FG) : S.nsmulSaturation.FG := by
  classical
  obtain ⟨F, hF_sub, hF_add⟩ := hS.exists_finset_subset_nsmulSaturation_add
  obtain ⟨T, hT⟩ := isAddFG_iff.mp hS
  refine isAddFG_iff.mpr ⟨F ∪ T, le_antisymm ?_ (fun x hx => ?_)⟩
  · rw [closure_le, Finset.coe_union]
    exact Set.union_subset hF_sub (hT ▸ subset_closure |>.trans S.le_nsmulSaturation)
  · obtain ⟨z, hz, s, hs, rfl⟩ := hF_add x hx
    refine add_mem (subset_closure (Finset.mem_coe.mpr (Finset.mem_union_left _ hz))) ?_
    exact closure_mono (Finset.subset_union_right (s₁ := F)) (hT ▸ hs)

end AmbientLattice

section GeneratedGroup

variable {G : Type*} [AddCommGroup G] [HasUniqueDiv G]

/-- In any torsion-free abelian group `G`, the saturation of a finitely generated submonoid `S`
inside `AddSubgroup.closure (S : Set G)` is covered by finitely many shifts of `S`. -/
theorem FG.exists_finset_subset_nsmulSaturation_inf_closure_add {S : AddSubmonoid G} (hS : S.FG) :
    ∃ F : Finset G,
      (F : Set G) ⊆ S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid ∧
        ∀ x ∈ S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid,
          ∃ z ∈ F, ∃ s ∈ S, x = z + s := by
  classical
  have := hS.moduleFinite_addSubgroupClosure
  have : Module.Free ℤ (AddSubgroup.closure (S : Set G)) := Module.free_of_finite_type_torsion_free'
  obtain ⟨F₀, hF₀_sub, hF₀_add⟩ :=
    hS.comap_subtype_closure.exists_finset_subset_nsmulSaturation_add
  refine ⟨F₀.image Subtype.val, ?_, fun x hx => ?_⟩
  · rw [Finset.coe_image]
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hF₀_sub hz
    rw [nsmulSaturation_comap] at hz'
    exact ⟨hz', z.2⟩
  · obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    have hx0 : (⟨x, hx2⟩ : AddSubgroup.closure (S : Set G)) ∈
        (S.comap (AddSubgroup.closure (S : Set G)).subtype).nsmulSaturation := by
      rw [nsmulSaturation_comap]
      exact hx1
    obtain ⟨z, hz, s, hs, heq⟩ := hF₀_add ⟨x, hx2⟩ hx0
    exact ⟨z.1, Finset.mem_image_of_mem Subtype.val hz, s.1, hs, congrArg Subtype.val heq⟩

/-- In any torsion-free abelian group `G`, the saturation of the pullback of a finitely generated
submonoid `S` to `AddSubgroup.closure (S : Set G)` is finitely generated. -/
theorem FG.nsmulSaturation_comap_subtype_closure {S : AddSubmonoid G} (hS : S.FG) :
    (S.comap (AddSubgroup.closure (S : Set G)).subtype).nsmulSaturation.FG := by
  have := hS.moduleFinite_addSubgroupClosure
  have : Module.Free ℤ (AddSubgroup.closure (S : Set G)) := Module.free_of_finite_type_torsion_free'
  exact hS.comap_subtype_closure.nsmulSaturation

/-- In any torsion-free abelian group `G`, the saturation of a finitely generated submonoid `S`
inside `AddSubgroup.closure (S : Set G)` is finitely generated. -/
theorem FG.nsmulSaturation_inf_closure {S : AddSubmonoid G} (hS : S.FG) :
    (S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid).FG :=
  (isAddFG_congr S.nsmulSaturationInfClosureEquiv).mpr hS.nsmulSaturation_comap_subtype_closure

end GeneratedGroup

end AddSubmonoid
