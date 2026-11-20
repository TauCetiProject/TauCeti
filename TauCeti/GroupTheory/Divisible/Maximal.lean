/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Projection

/-!
# The maximal divisible subgroup of an abelian group

`TauCeti.Divisible.maxDivisible A` is the sum of all divisible subgroups of `A`. It is itself
divisible, is preserved by homomorphisms, and has a reduced quotient (one with no nonzero
divisible subgroup). It admits an internal complement by injectivity of divisible groups.

The maximal divisible subgroup is contained in the intersection of the images of multiplication
by positive integers. If these images stabilize along multiples of a fixed positive integer,
the stabilized image equals both the intersection and the maximal divisible subgroup. This is
the group-theoretic step in Weibel, *The K-book*, Proposition VI.7.3.
-/

public section

namespace AddSubgroup

variable {A B : Type*} [AddCommGroup A] [AddGroup B]

/-- A sum of divisible subgroups is divisible, even when the summands are not directed. -/
@[instance_reducible]
noncomputable def divisibleBySSup (S : Set (AddSubgroup A))
    (hS : ∀ D ∈ S, Nonempty (DivisibleBy D ℕ)) : DivisibleBy (sSup S : AddSubgroup A) ℕ :=
  divisibleByOfSMulRightSurj _ ℕ fun {n} hn x ↦ by
    -- The image of multiplication by `n` on the sum contains each summand.
    have h : sSup S ≤ (sSup S).map (nsmulAddMonoidHom n) := by
      refine sSup_le fun D hD a ha ↦ ?_
      let := (hS D hD).some
      obtain ⟨y, hy⟩ := DivisibleBy.surjective_smul D ℕ hn ⟨a, ha⟩
      exact ⟨y, le_sSup hD y.property, congrArg Subtype.val hy⟩
    obtain ⟨y, hy, hxy⟩ := h x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

/-- Images of divisible subgroups under additive homomorphisms are divisible. -/
noncomputable instance instDivisibleByMap {G H : Type*} [AddGroup G] [AddGroup H]
    (D : AddSubgroup G) [DivisibleBy D ℕ] (f : G →+ H) : DivisibleBy (D.map f) ℕ :=
  (f.addSubgroupMap_surjective D).divisibleBy _ fun x n ↦ map_nsmul (f.addSubgroupMap D) n x

/-- The preimage of a divisible subgroup in the range is divisible if the kernel is divisible. -/
@[instance_reducible]
noncomputable def divisibleByComap (D : AddSubgroup B) [DivisibleBy D ℕ] (f : A →+ B)
    [DivisibleBy f.ker ℕ] (hD : D ≤ f.range) : DivisibleBy (D.comap f) ℕ :=
  divisibleByOfSMulRightSurj _ ℕ fun {n} hn x ↦ by
    obtain ⟨b, hb⟩ := DivisibleBy.surjective_smul D ℕ hn ⟨f x, x.property⟩
    obtain ⟨y, hy⟩ := hD b.property
    have hy' : y ∈ D.comap f := by
      rw [AddSubgroup.mem_comap, hy]
      exact b.property
    have hk : (x : A) - n • y ∈ f.ker := by
      have h : n • (b : B) = f x := congrArg Subtype.val hb
      simp [hy, h]
    obtain ⟨k, hk'⟩ := DivisibleBy.surjective_smul f.ker ℕ hn ⟨_, hk⟩
    refine ⟨⟨y + k, add_mem hy' ?_⟩, Subtype.ext ?_⟩
    · simp [AddSubgroup.mem_comap, AddMonoidHom.mem_ker.mp k.property]
    · have h : n • (k : A) = (x : A) - n • y := congrArg Subtype.val hk'
      simp [h]

/-- A divisible subgroup of an abelian group admits an internal complement. -/
theorem exists_isCompl_of_divisibleBy (D : AddSubgroup A) [DivisibleBy D ℕ] :
    ∃ E : AddSubgroup A, IsCompl D E := by
  let := AddGroup.divisibleByIntOfDivisibleByNat D
  obtain ⟨r, hr⟩ := (Module.Baer.of_divisible D).extension_property_addMonoidHom
    D.subtype Subtype.val_injective (AddMonoidHom.id D)
  refine ⟨r.ker, AddSubgroup.toIntSubmodule.isCompl_iff.mpr ?_⟩
  rw [← r.coe_toIntLinearMap_ker]
  exact LinearMap.isCompl_of_proj (p := D.toIntSubmodule) (f := r.toIntLinearMap)
    fun x ↦ DFunLike.congr_fun hr x

/-- A divisible subgroup and its quotient give an abstract product decomposition. -/
theorem nonempty_addEquiv_prod_quotient_of_divisibleBy (D : AddSubgroup A) [DivisibleBy D ℕ] :
    Nonempty (A ≃+ D × (A ⧸ D)) := by
  obtain ⟨E, hE⟩ := D.exists_isCompl_of_divisibleBy
  have h := AddSubgroup.toIntSubmodule.isCompl_iff.mp hE
  let e := (D.toIntSubmodule.prodEquivOfIsCompl E.toIntSubmodule h).symm
  let q := (D.toIntSubmodule.quotientEquivOfIsCompl E.toIntSubmodule h).symm
  exact ⟨e.toAddEquiv.trans ((AddEquiv.refl D).prodCongr q.toAddEquiv)⟩

end AddSubgroup

namespace TauCeti.Divisible

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The sum of all divisible additive subgroups of an abelian group. -/
def maxDivisible (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  sSup {D : AddSubgroup A | Nonempty (DivisibleBy D ℕ)}

/-- The maximal divisible subgroup is the supremum in the lattice of additive subgroups. -/
theorem maxDivisible_def (A : Type*) [AddCommGroup A] :
    maxDivisible A = sSup {D : AddSubgroup A | Nonempty (DivisibleBy D ℕ)} := (rfl)

/-- The sum of divisible subgroups is itself divisible. -/
noncomputable instance instDivisibleByMaxDivisible : DivisibleBy (maxDivisible A) ℕ := by
  rw [maxDivisible_def]
  exact AddSubgroup.divisibleBySSup _ fun _ hD ↦ hD

/-- Every divisible subgroup is contained in the maximal divisible subgroup. -/
theorem le_maxDivisible (D : AddSubgroup A) [DivisibleBy D ℕ] : D ≤ maxDivisible A := by
  rw [maxDivisible_def]
  exact le_sSup (show Nonempty (DivisibleBy D ℕ) from ⟨inferInstance⟩)

/-- Membership in the maximal divisible subgroup is witnessed by any divisible subgroup. -/
theorem mem_maxDivisible_iff {x : A} :
    x ∈ maxDivisible A ↔ ∃ D : AddSubgroup A, Nonempty (DivisibleBy D ℕ) ∧ x ∈ D := by
  refine ⟨fun hx ↦ ⟨_, ⟨inferInstance⟩, hx⟩, ?_⟩
  rintro ⟨D, ⟨hD⟩, hx⟩
  let := hD
  exact le_maxDivisible D hx

/-- An abelian group is divisible exactly when its maximal divisible subgroup is the whole group. -/
theorem maxDivisible_eq_top_iff :
    maxDivisible A = ⊤ ↔ Nonempty (DivisibleBy A ℕ) := by
  constructor
  · intro h
    let : DivisibleBy (⊤ : AddSubgroup A) ℕ := h ▸ instDivisibleByMaxDivisible
    let e : (⊤ : AddSubgroup A) ≃+ A := AddSubgroup.topEquiv
    exact ⟨e.surjective.divisibleBy e fun x n ↦ map_nsmul e n x⟩
  · rintro ⟨h⟩
    let := h
    let e : A ≃+ (⊤ : AddSubgroup A) := AddSubgroup.topEquiv.symm
    let := e.surjective.divisibleBy e fun x n ↦ map_nsmul e n x
    exact top_le_iff.mp (le_maxDivisible ⊤)

/-- Every additive homomorphism preserves membership in the maximal divisible subgroup. -/
theorem map_maxDivisible_le (f : A →+ B) : (maxDivisible A).map f ≤ maxDivisible B :=
  le_maxDivisible _

/-- Quotienting by the maximal divisible subgroup leaves no nonzero divisible subgroup. -/
@[simp]
theorem maxDivisible_quotient : maxDivisible (A ⧸ maxDivisible A) = ⊥ := by
  let q := QuotientAddGroup.mk' (maxDivisible A)
  let : DivisibleBy q.ker ℕ := by
    rw [QuotientAddGroup.ker_mk']
    infer_instance
  let D := maxDivisible (A ⧸ maxDivisible A)
  have hq := QuotientAddGroup.mk'_surjective (maxDivisible A)
  let := D.divisibleByComap q (by rw [QuotientAddGroup.range_mk']; exact le_top)
  have h := AddSubgroup.map_mono (f := q) (le_maxDivisible (D.comap q))
  exact le_bot_iff.mp (by simpa [q, AddSubgroup.map_comap_eq_self_of_surjective hq] using h)

/-- The maximal divisible subgroup of a binary product is the product of the two subgroups. -/
@[simp]
theorem maxDivisible_prod : maxDivisible (A × B) = (maxDivisible A).prod (maxDivisible B) := by
  apply le_antisymm
  · intro x hx
    exact ⟨map_maxDivisible_le (AddMonoidHom.fst A B) ⟨x, hx, rfl⟩,
      map_maxDivisible_le (AddMonoidHom.snd A B) ⟨x, hx, rfl⟩⟩
  · let e := (AddSubgroup.prodEquiv (maxDivisible A) (maxDivisible B)).symm
    let := e.surjective.divisibleBy e fun x n ↦ map_nsmul e n x
    exact le_maxDivisible _

/-- The maximal divisible subgroup lies in the image of multiplication by any nonzero natural. -/
theorem maxDivisible_le_range_nsmul {n : ℕ} (hn : n ≠ 0) :
    maxDivisible A ≤ (nsmulAddMonoidHom n : A →+ A).range := by
  intro x hx
  obtain ⟨y, hy⟩ := DivisibleBy.surjective_smul (maxDivisible A) ℕ hn ⟨x, hx⟩
  exact ⟨y, congrArg Subtype.val hy⟩

/-- The maximal divisible subgroup is contained in the intersection of all positive
multiplication images. -/
theorem maxDivisible_le_iInf_range_nsmul :
    maxDivisible A ≤ ⨅ n : {n : ℕ // n ≠ 0}, (nsmulAddMonoidHom n.val : A →+ A).range :=
  le_iInf fun n ↦ maxDivisible_le_range_nsmul n.property

/-- A finite abelian group has no nonzero divisible subgroup. -/
@[simp]
theorem maxDivisible_eq_bot_of_finite [Finite A] : maxDivisible A = ⊥ := by
  let := Fintype.ofFinite A
  have h : (nsmulAddMonoidHom (Fintype.card A) : A →+ A) = 0 := by
    ext x
    simp
  exact le_bot_iff.mp (by simpa [h] using
    (maxDivisible_le_range_nsmul (A := A) (Fintype.card_ne_zero (α := A))))

/-- If multiplication images agree with `wA` along nonzero multiples of `w`, then `wA`
is the maximal divisible subgroup. -/
theorem range_nsmul_eq_maxDivisible {w : ℕ} (hw : w ≠ 0)
    (h : ∀ n : ℕ, n ≠ 0 → (nsmulAddMonoidHom (n * w) : A →+ A).range =
      (nsmulAddMonoidHom w : A →+ A).range) :
    (nsmulAddMonoidHom w : A →+ A).range = maxDivisible A := by
  let D := (nsmulAddMonoidHom w : A →+ A).range
  let : DivisibleBy D ℕ := divisibleByOfSMulRightSurj _ ℕ fun {n} hn x ↦ by
    have hx : (x : A) ∈ (nsmulAddMonoidHom w : A →+ A).range := x.property
    rw [← h n hn] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨⟨w • y, ⟨y, rfl⟩⟩, Subtype.ext ?_⟩
    simpa only [nsmulAddMonoidHom_apply, mul_nsmul', AddSubgroup.coe_nsmul] using hy
  exact le_antisymm (le_maxDivisible D) (maxDivisible_le_range_nsmul hw)

/-- If multiplication images agree with `wA` along nonzero multiples of `w`, then `wA`
is the intersection of all positive multiplication images. -/
theorem range_nsmul_eq_iInf_range_nsmul {w : ℕ} (hw : w ≠ 0)
    (h : ∀ n : ℕ, n ≠ 0 → (nsmulAddMonoidHom (n * w) : A →+ A).range =
      (nsmulAddMonoidHom w : A →+ A).range) :
    (nsmulAddMonoidHom w : A →+ A).range =
      ⨅ n : {n : ℕ // n ≠ 0}, (nsmulAddMonoidHom n.val : A →+ A).range :=
  le_antisymm ((range_nsmul_eq_maxDivisible hw h).le.trans maxDivisible_le_iInf_range_nsmul)
    (iInf_le _ (⟨w, hw⟩ : {n : ℕ // n ≠ 0}))

/-- If the reduced quotient is cyclic, the group splits abstractly as its maximal divisible
subgroup times `ZMod` of the quotient's cardinality (`ZMod 0` for an infinite cyclic quotient). -/
theorem nonempty_addEquiv_prod_zmod [h : IsAddCyclic (A ⧸ maxDivisible A)] :
    Nonempty (A ≃+ maxDivisible A × ZMod (Nat.card (A ⧸ maxDivisible A))) :=
  (maxDivisible A).nonempty_addEquiv_prod_quotient_of_divisibleBy.map fun e ↦
    e.trans ((AddEquiv.refl _).prodCongr (zmodAddCyclicAddEquiv h).symm)

end TauCeti.Divisible
