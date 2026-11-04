/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.RingTheory.Finiteness.Cardinality
public import TauCeti.Algebra.Group.Submonoid.GroupCompletion
public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Finiteness of preimages and saturations of additive submonoids

This file establishes two forms of Gordan's lemma for finitely generated additive submonoids:

* **Preimages under homomorphisms**: the preimage of a finitely generated additive submonoid under a
  homomorphism from a finitely generated commutative monoid is finitely generated, provided the
  target is cancellative (`AddSubmonoid.FG.comap`). Together with
  `AddSubmonoid.fg_iff_exists_fin_addMonoidHom` and `AddSubmonoid.fg_eqLocusM`, this gives the
  slack-variable form of Gordan's lemma.
* **Bounded shifts and saturations**: for a finitely generated submonoid `S` of a finitely generated
  torsion-free abelian group `L`, Euclidean division of natural generator coefficients bounds
  representatives of `S.nsmulSaturation` modulo `S` inside a finite coordinate box, yielding a
  finite set `F ⊆ S.nsmulSaturation` with `S.nsmulSaturation = F + S`
  (`AddSubmonoid.FG.exists_finset_subset_nsmulSaturation_add`). Consequently `S.nsmulSaturation` is
  finitely generated (`AddSubmonoid.FG.nsmulSaturation`), and for any finitely generated submonoid
  `S` of an arbitrary torsion-free abelian group `G`, its saturation inside
  `AddSubgroup.closure (S : Set G)` is finitely generated
  (`AddSubmonoid.FG.nsmulSaturation_inf_closure`).

## Main results

* `AddSubmonoid.FG.comap`: preimages of finitely generated additive submonoids are finitely
  generated when the source monoid is finitely generated and the target is cancellative.
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

namespace TauCeti

/-- The preimage of a finitely generated additive submonoid of a cancellative commutative monoid
is finitely generated when the source monoid is finitely generated. -/
theorem _root_.AddSubmonoid.FG.comap {M G : Type*} [AddCommMonoid M] [AddCommMonoid G]
    [IsCancelAdd G] [AddMonoid.FG M] {P : AddSubmonoid G} (hP : P.FG) (f : M →+ G) :
    (P.comap f).FG := by
  obtain ⟨n, q, hq⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp
    (AddMonoid.FG.fg_top (M := M))
  obtain ⟨k, g, hg⟩ := AddSubmonoid.fg_iff_exists_fin_addMonoidHom.mp hP
  have hqsurj := AddMonoidHom.mrange_eq_top.mp hq
  let π := q.comp (AddMonoidHom.fst (Fin n → ℕ) (Fin k → ℕ))
  let γ := g.comp (AddMonoidHom.snd (Fin n → ℕ) (Fin k → ℕ))
  have hfg := (AddSubmonoid.fg_eqLocusM (f.comp π) γ).map π
  have heq : ((f.comp π).eqLocusM γ).map π = P.comap f := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [AddSubmonoid.mem_comap, ← hg, AddMonoidHom.mem_mrange]
      exact ⟨a.2, (AddMonoidHom.mem_eqLocusM.mp ha).symm⟩
    · intro hx
      obtain ⟨a, rfl⟩ := hqsurj x
      rw [AddSubmonoid.mem_comap, ← hg, AddMonoidHom.mem_mrange] at hx
      obtain ⟨b, hb⟩ := hx
      exact ⟨(a, b), AddMonoidHom.mem_eqLocusM.mpr hb.symm, rfl⟩
  exact heq ▸ hfg

end TauCeti

namespace AddSubmonoid

section AmbientLattice

variable {L : Type*} [AddCommGroup L]

private theorem abs_repr_le_of_nsmul_eq_sum {ι : Type*} (b : Module.Basis ι ℤ L)
    {m n : ℕ} (hn : 0 < n) (a : Fin m → L) (r : Fin m → ℕ) (hr : ∀ j, r j < n) {z : L}
    (hz : n • z = ∑ j, r j • a j) (i : ι) :
    |b.repr z i| ≤ ∑ j, |b.repr (a j) i| := by
  have h1 : (n : ℤ) * |b.repr z i| = |b.repr (n • z) i| := by
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, abs_mul,
      abs_of_pos (by exact_mod_cast hn : (0 : ℤ) < n)]
  have h2 : |b.repr (n • z) i| ≤ (n : ℤ) * ∑ j, |b.repr (a j) i| := by
    rw [hz, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (r j))]
    exact mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr (hr j).le) (abs_nonneg _)
  exact le_of_mul_le_mul_left (h1.trans_le h2) (by exact_mod_cast hn : (0 : ℤ) < n)

variable [Module.Finite ℤ L] [HasUniqueDiv L]

/-- **Bounded shifts for submonoid saturation.** If `S` is a finitely generated submonoid of a
finitely generated torsion-free abelian group `L`, there is a finite subset `F ⊆ S.nsmulSaturation`
such that every element of `S.nsmulSaturation` is of the form `z + s` with `z ∈ F` and `s ∈ S`. -/
theorem FG.exists_finset_subset_nsmulSaturation_add {S : AddSubmonoid L} (hS : S.FG) :
    ∃ F : Finset L, (F : Set L) ⊆ S.nsmulSaturation ∧
      ∀ x ∈ S.nsmulSaturation, ∃ z ∈ F, ∃ s ∈ S, x = z + s := by
  classical
  have : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
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
  let B : ι → ℤ := fun i => ∑ j, |b.repr (a j) i|
  let box : Finset (ι → ℤ) := Fintype.piFinset fun i => Finset.Icc (-B i) (B i)
  let e : L ↪ (ι → ℤ) :=
    ⟨fun z i => b.repr z i, fun z₁ z₂ h => b.repr.injective (Finsupp.ext (congrFun h))⟩
  have hfin : {z : L | z ∈ S.nsmulSaturation ∧ ∀ i, |b.repr z i| ≤ B i}.Finite := by
    refine (box.finite_toSet.preimage_embedding e).subset fun z hz => ?_
    rw [Set.mem_preimage, Finset.mem_coe, Fintype.mem_piFinset]
    exact fun i => Finset.mem_Icc.mpr (abs_le.mp (hz.2 i))
  refine ⟨hfin.toFinset, fun z hz => ((Set.Finite.mem_toFinset hfin).mp hz).1, fun x hx => ?_⟩
  obtain ⟨n, hn, hnx⟩ := mem_nsmulSaturation.mp hx
  rw [← hg, AddMonoidHom.mem_mrange] at hnx
  obtain ⟨k, hk⟩ := hnx
  let q : Fin m → ℕ := fun j => k j / n
  let r : Fin m → ℕ := fun j => k j % n
  let s : L := g q
  let z : L := x - s
  have hnz : n • z = g r := by
    dsimp only [z, s]
    rw [smul_sub, ← hk, hg_eq k, hg_eq q, hg_eq r, Finset.smul_sum, sub_eq_iff_eq_add,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← add_smul, add_comm, Nat.div_add_mod]
  have hz_sat : z ∈ S.nsmulSaturation :=
    mem_nsmulSaturation.mpr ⟨n, hn, hnz ▸ hg ▸ ⟨r, rfl⟩⟩
  have hz_bound : ∀ i, |b.repr z i| ≤ B i :=
    abs_repr_le_of_nsmul_eq_sum b hn a r (fun j => Nat.mod_lt _ hn) (hnz.trans (hg_eq r))
  exact ⟨z, (Set.Finite.mem_toFinset hfin).mpr ⟨hz_sat, hz_bound⟩,
    s, hg ▸ ⟨q, rfl⟩, (sub_add_cancel x s).symm⟩

/-- **Gordan's lemma for submonoid saturation.** In a finitely generated torsion-free abelian
group `L`, the saturation of any finitely generated additive submonoid `S` is finitely generated. -/
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
  have : Module.Finite ℤ (AddSubgroup.closure (S : Set G)) :=
    Module.Finite.iff_addGroup_fg.mpr hS.addSubgroup_closure
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
  have : Module.Finite ℤ (AddSubgroup.closure (S : Set G)) :=
    Module.Finite.iff_addGroup_fg.mpr hS.addSubgroup_closure
  exact hS.comap_subtype_closure.nsmulSaturation

/-- In any torsion-free abelian group `G`, the saturation of a finitely generated submonoid `S`
inside `AddSubgroup.closure (S : Set G)` is finitely generated. -/
theorem FG.nsmulSaturation_inf_closure {S : AddSubmonoid G} (hS : S.FG) :
    (S.nsmulSaturation ⊓ (AddSubgroup.closure (S : Set G)).toAddSubmonoid).FG :=
  (isAddFG_congr S.nsmulSaturationInfClosureEquiv).mpr hS.nsmulSaturation_comap_subtype_closure

end GeneratedGroup

end AddSubmonoid
