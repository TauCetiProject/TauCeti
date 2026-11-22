/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Divisible
public import Mathlib.GroupTheory.Exponent

import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Projection

/-!
# The maximal divisible subgroup of an abelian group

A subgroup `D` of an additive group is *divisible* (`AddSubgroup.IsDivisible`) when every element
of `D` is an `n`-fold multiple of an element of `D`, for every `n ≠ 0`. In an abelian group `A`
the divisible subgroups are closed under arbitrary suprema, so their supremum
`TauCeti.AddCommGroup.maxDivisible A`, often written `Div(A)`, is the largest divisible subgroup.
The quotient `A ⧸ Div(A)` is *reduced*: it has no nonzero divisible subgroup. Since divisible
abelian groups are injective `ℤ`-modules, every divisible subgroup is a direct summand, so
`A ≃+ Div(A) × (A ⧸ Div(A))` noncanonically.

The maximal divisible subgroup is the part of an abelian group that is invisible to finite
coefficients and to completions: it lies in `⋂_{m ≥ 1} m A`. The file isolates the criterion
used to identify it in computations of algebraic K-groups: if `w ≠ 0` and `w A ≤ (w k) A` for every
`k ≠ 0`, then `w A = Div(A) = ⋂_{m ≥ 1} m A`, and if moreover `A ⧸ w A` is cyclic of order `w`
then `A ≃+ Div(A) × ℤ/w`.

## Main definitions

* `AddSubgroup.IsDivisible`: a subgroup in which multiplication by every `n ≠ 0` is surjective.
* `TauCeti.AddCommGroup.maxDivisible`: the supremum of the divisible subgroups.

## Main results

* `AddSubgroup.IsDivisible.sSup`: a supremum of divisible subgroups is divisible.
* `AddSubgroup.IsDivisible.exists_isCompl`: a divisible subgroup has a complement.
* `TauCeti.AddCommGroup.isGreatest_maxDivisible`: `Div(A)` is the greatest divisible subgroup.
* `TauCeti.AddCommGroup.maxDivisible_quotient_eq_bot`: the quotient `A ⧸ Div(A)` is reduced.
* `TauCeti.AddCommGroup.maxDivisible_prod`, `TauCeti.AddCommGroup.maxDivisible_pi`: compatibility
  with products.
* `TauCeti.AddCommGroup.map_maxDivisible_le`: functoriality under additive homomorphisms.
* `TauCeti.AddCommGroup.maxDivisible_eq_bot_of_exponentExists`: a group of bounded exponent, in
  particular a finite group, is reduced.
* `TauCeti.AddCommGroup.maxDivisible_le_iInf_range_nsmul`: `Div(A) ≤ ⋂_{m ≥ 1} m A`.
* `TauCeti.AddCommGroup.range_nsmul_eq_maxDivisible`,
  `TauCeti.AddCommGroup.maxDivisible_eq_iInf_range_nsmul`: the stabilization criterion.
* `TauCeti.AddCommGroup.nonempty_addEquiv_maxDivisible_prod_zmod`: the splitting
  `A ≃+ Div(A) × ℤ/w` under the stabilization criterion with cyclic quotient.

## References

* C. Weibel, *The K-book: an introduction to algebraic K-theory*, proof of Lemma VI.1.6 and
  Proposition VI.7.3.
* L. Fuchs, *Infinite abelian groups*, Vol. I, §§20–21.
-/

public section

open Function

namespace AddSubgroup

section AddGroup

variable {A B : Type*} [AddGroup A] [AddGroup B]

/-- An additive subgroup `D` is **divisible** if every element of `D` is an `n`-fold multiple of
an element of `D` for every `n ≠ 0`. -/
def IsDivisible (D : AddSubgroup A) : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ x ∈ D, ∃ y ∈ D, n • y = x

theorem isDivisible_def {D : AddSubgroup A} :
    D.IsDivisible ↔ ∀ n : ℕ, n ≠ 0 → ∀ x ∈ D, ∃ y ∈ D, n • y = x :=
  Iff.rfl

/-- A subgroup is divisible exactly when multiplication by every `n ≠ 0` is surjective on it. -/
theorem isDivisible_iff_surjective_nsmul {D : AddSubgroup A} :
    D.IsDivisible ↔ ∀ n : ℕ, n ≠ 0 → Surjective fun y : D ↦ n • y := by
  refine ⟨fun hD n hn x ↦ ?_, fun hD n hn x hx ↦ ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hD n hn x x.property
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  · obtain ⟨y, hy⟩ := hD n hn ⟨x, hx⟩
    exact ⟨y, y.property, congrArg Subtype.val hy⟩

/-- A subgroup is divisible exactly when it carries a Mathlib `DivisibleBy _ ℕ` structure. -/
theorem isDivisible_iff_nonempty_divisibleBy {D : AddSubgroup A} :
    D.IsDivisible ↔ Nonempty (DivisibleBy D ℕ) := by
  rw [isDivisible_iff_surjective_nsmul]
  exact ⟨fun h ↦ ⟨divisibleByOfSMulRightSurj D ℕ fun hn ↦ h _ hn⟩,
    fun ⟨_⟩ _ hn ↦ DivisibleBy.surjective_smul D ℕ hn⟩

/-- The whole group is divisible exactly when multiplication by every `n ≠ 0` is surjective. -/
theorem isDivisible_top_iff :
    (⊤ : AddSubgroup A).IsDivisible ↔ ∀ n : ℕ, n ≠ 0 → Surjective fun x : A ↦ n • x :=
  ⟨fun h n hn x ↦ (h n hn x trivial).imp fun _ hy ↦ hy.2,
    fun h n hn x _ ↦ (h n hn x).imp fun _ hy ↦ ⟨trivial, hy⟩⟩

@[simp]
theorem isDivisible_bot : (⊥ : AddSubgroup A).IsDivisible := fun _ _ x hx ↦
  ⟨0, zero_mem _, by rw [(mem_bot).1 hx, smul_zero]⟩

namespace IsDivisible

/-- The image of a divisible subgroup under an additive homomorphism is divisible. -/
theorem map {D : AddSubgroup A} (hD : D.IsDivisible) (f : A →+ B) : (D.map f).IsDivisible := by
  rintro n hn _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hD n hn x hx
  exact ⟨f y, mem_map_of_mem f hy, (map_nsmul f n y).symm⟩

end IsDivisible

end AddGroup

section AddCommGroup

variable {A : Type*} [AddCommGroup A]

namespace IsDivisible

/-- A supremum of divisible subgroups of an abelian group is divisible. -/
theorem sSup {S : Set (AddSubgroup A)} (hS : ∀ D ∈ S, D.IsDivisible) :
    (SupSet.sSup S).IsDivisible := by
  let K : AddSubgroup A :=
    { carrier := {x | ∀ n : ℕ, n ≠ 0 → ∃ y ∈ SupSet.sSup S, n • y = x}
      zero_mem' := fun _ _ ↦ ⟨0, zero_mem _, smul_zero _⟩
      add_mem' := fun ha hb n hn ↦ by
        obtain ⟨y, hy, rfl⟩ := ha n hn
        obtain ⟨z, hz, rfl⟩ := hb n hn
        exact ⟨y + z, add_mem hy hz, smul_add _ _ _⟩
      neg_mem' := fun ha n hn ↦ by
        obtain ⟨y, hy, rfl⟩ := ha n hn
        exact ⟨-y, neg_mem hy, smul_neg _ _⟩ }
  have hle : SupSet.sSup S ≤ K := sSup_le fun D hDS x hx n hn ↦ by
    obtain ⟨y, hy, rfl⟩ := hS D hDS n hn x hx
    exact ⟨y, le_sSup hDS hy, rfl⟩
  exact fun n hn x hx ↦ hle hx n hn

/-- The sum of two divisible subgroups of an abelian group is divisible. -/
theorem sup {D E : AddSubgroup A} (hD : D.IsDivisible) (hE : E.IsDivisible) :
    (D ⊔ E).IsDivisible := by
  rw [← sSup_pair]
  refine IsDivisible.sSup ?_
  rintro F (rfl | rfl)
  exacts [hD, hE]

/-- A divisible subgroup of an abelian group admits a retraction: divisible abelian groups are
injective `ℤ`-modules. -/
theorem exists_retraction {D : AddSubgroup A} (hD : D.IsDivisible) :
    ∃ r : A →+ D, ∀ x : D, r x = x := by
  obtain ⟨_⟩ := isDivisible_iff_nonempty_divisibleBy.1 hD
  let : DivisibleBy D ℤ := AddGroup.divisibleByIntOfDivisibleByNat D
  obtain ⟨r, hr⟩ := (Module.Baer.of_divisible D).extension_property_addMonoidHom D.subtype
    Subtype.val_injective (AddMonoidHom.id D)
  exact ⟨r, fun x ↦ DFunLike.congr_fun hr x⟩

/-- A divisible subgroup of an abelian group is a direct summand: it has a complement. The
complement is not canonical. -/
theorem exists_isCompl {D : AddSubgroup A} (hD : D.IsDivisible) :
    ∃ C : AddSubgroup A, IsCompl D C := by
  obtain ⟨r, hr⟩ := hD.exists_retraction
  exact ⟨r.ker, toIntSubmodule.isCompl_iff.2 <|
    LinearMap.isCompl_of_proj (p := D.toIntSubmodule) (f := r.toIntLinearMap) hr⟩

/-- An abelian group splits, noncanonically, as the product of a divisible subgroup and the
quotient by it. -/
theorem nonempty_addEquiv_prod_quotient {D : AddSubgroup A} (hD : D.IsDivisible) :
    Nonempty (A ≃+ D × (A ⧸ D)) := by
  obtain ⟨r, hr⟩ := hD.exists_retraction
  have hr' : ∀ x ∈ D, (r x : A) = x := fun x hx ↦ congrArg Subtype.val (hr ⟨x, hx⟩)
  refine ⟨AddEquiv.ofBijective (r.prod (QuotientAddGroup.mk' D)) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [AddMonoidHom.prod_apply, QuotientAddGroup.mk'_apply, Prod.mk_eq_zero,
      QuotientAddGroup.eq_zero_iff] at hx
    rw [← hr' x hx.2, hx.1, ZeroMemClass.coe_zero]
  · rintro ⟨d, y⟩
    induction y using QuotientAddGroup.induction_on with | H a => ?_
    refine ⟨d + (a - r a), Prod.ext ?_ ?_⟩
    · simp [hr]
    · simp only [AddMonoidHom.prod_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
        neg_add_rev]
      have : -(a - r a) + -(d : A) + a = (r a : A) - d := by abel
      rw [this]
      exact sub_mem (r a).property d.property

end IsDivisible

end AddCommGroup

end AddSubgroup

namespace TauCeti.AddCommGroup

open AddSubgroup

variable (A : Type*) [AddCommGroup A]

/-- The **maximal divisible subgroup** `Div(A)` of an abelian group `A`: the supremum of its
divisible subgroups. By `isGreatest_maxDivisible` it is the greatest divisible subgroup. -/
def maxDivisible : AddSubgroup A :=
  sSup {D : AddSubgroup A | D.IsDivisible}

theorem maxDivisible_def : maxDivisible A = sSup {D : AddSubgroup A | D.IsDivisible} :=
  (rfl)

/-- The maximal divisible subgroup is divisible. -/
theorem isDivisible_maxDivisible : (maxDivisible A).IsDivisible :=
  IsDivisible.sSup (S := {D : AddSubgroup A | D.IsDivisible}) fun _ hD ↦ hD

variable {A}

/-- Every divisible subgroup lies in the maximal divisible subgroup. -/
theorem _root_.AddSubgroup.IsDivisible.le_maxDivisible {D : AddSubgroup A} (hD : D.IsDivisible) :
    D ≤ maxDivisible A :=
  le_sSup hD

variable (A) in
/-- The maximal divisible subgroup is the greatest divisible subgroup. -/
theorem isGreatest_maxDivisible :
    IsGreatest {D : AddSubgroup A | D.IsDivisible} (maxDivisible A) :=
  ⟨isDivisible_maxDivisible A, fun _ hD ↦ hD.le_maxDivisible⟩

/-- An element lies in the maximal divisible subgroup exactly when it lies in some divisible
subgroup. -/
theorem mem_maxDivisible_iff {x : A} :
    x ∈ maxDivisible A ↔ ∃ D : AddSubgroup A, D.IsDivisible ∧ x ∈ D :=
  ⟨fun hx ↦ ⟨_, isDivisible_maxDivisible A, hx⟩, fun ⟨_, hD, hx⟩ ↦ hD.le_maxDivisible hx⟩

/-- Elements of the maximal divisible subgroup are `n`-fold multiples of elements of it, for every
`n ≠ 0`. -/
theorem exists_mem_maxDivisible_nsmul_eq {x : A} (hx : x ∈ maxDivisible A) {n : ℕ} (hn : n ≠ 0) :
    ∃ y ∈ maxDivisible A, n • y = x :=
  isDivisible_maxDivisible A n hn x hx

/-- The maximal divisible subgroup is the whole group exactly when the group is divisible. -/
theorem maxDivisible_eq_top_iff :
    maxDivisible A = ⊤ ↔ ∀ n : ℕ, n ≠ 0 → Surjective fun x : A ↦ n • x := by
  rw [← isDivisible_top_iff]
  exact ⟨fun h ↦ h ▸ isDivisible_maxDivisible A, fun h ↦ eq_top_iff.2 h.le_maxDivisible⟩

/-- A divisible abelian group is its own maximal divisible subgroup. -/
@[simp]
theorem maxDivisible_eq_top [DivisibleBy A ℕ] : maxDivisible A = ⊤ :=
  maxDivisible_eq_top_iff.2 fun _ hn ↦ DivisibleBy.surjective_smul A ℕ hn

section Functoriality

variable {B : Type*} [AddCommGroup B]

/-- An additive homomorphism carries the maximal divisible subgroup into the maximal divisible
subgroup. -/
theorem map_maxDivisible_le (f : A →+ B) : (maxDivisible A).map f ≤ maxDivisible B :=
  ((isDivisible_maxDivisible A).map f).le_maxDivisible

/-- An additive homomorphism carries the maximal divisible subgroup into the maximal divisible
subgroup, stated with preimages. -/
theorem maxDivisible_le_comap (f : A →+ B) : maxDivisible A ≤ (maxDivisible B).comap f :=
  map_le_iff_le_comap.1 (map_maxDivisible_le f)

/-- An additive homomorphism carries elements of the maximal divisible subgroup to elements of the
maximal divisible subgroup. -/
theorem map_mem_maxDivisible (f : A →+ B) {x : A} (hx : x ∈ maxDivisible A) :
    f x ∈ maxDivisible B :=
  maxDivisible_le_comap f hx

/-- An additive equivalence identifies the maximal divisible subgroups. -/
@[simp]
theorem map_maxDivisible_addEquiv (e : A ≃+ B) :
    (maxDivisible A).map (e : A →+ B) = maxDivisible B := by
  refine le_antisymm (map_maxDivisible_le _) fun x hx ↦ ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  exact map_mem_maxDivisible (e.symm : B →+ A) hx

end Functoriality

section Quotient

/-- The quotient by the maximal divisible subgroup is **reduced**: it has no nonzero divisible
subgroup. -/
@[simp]
theorem maxDivisible_quotient_eq_bot : maxDivisible (A ⧸ maxDivisible A) = ⊥ := by
  set π := QuotientAddGroup.mk' (maxDivisible A)
  -- The preimage of the maximal divisible subgroup of the quotient is divisible.
  have hP : ((maxDivisible (A ⧸ maxDivisible A)).comap π).IsDivisible := by
    intro n hn x hx
    obtain ⟨y', hy', hyx⟩ := exists_mem_maxDivisible_nsmul_eq hx hn
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (maxDivisible A) y'
    have hd : x - n • y ∈ maxDivisible A := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul]
      exact sub_eq_zero.2 hyx.symm
    obtain ⟨z, hz, hzd⟩ := exists_mem_maxDivisible_nsmul_eq hd hn
    refine ⟨y + z, add_mem hy' ((maxDivisible_le_comap π) hz), ?_⟩
    rw [smul_add, hzd, add_sub_cancel]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (maxDivisible A) x
  exact (QuotientAddGroup.eq_zero_iff a).2 (hP.le_maxDivisible hx)

/-- An abelian group splits, noncanonically, as the product of its maximal divisible subgroup and
the reduced quotient. -/
theorem nonempty_addEquiv_maxDivisible_prod_quotient :
    Nonempty (A ≃+ maxDivisible A × (A ⧸ maxDivisible A)) :=
  (isDivisible_maxDivisible A).nonempty_addEquiv_prod_quotient

/-- The maximal divisible subgroup has a (noncanonical) complement. -/
theorem exists_isCompl_maxDivisible : ∃ C : AddSubgroup A, IsCompl (maxDivisible A) C :=
  (isDivisible_maxDivisible A).exists_isCompl

end Quotient

section Products

variable {B : Type*} [AddCommGroup B]

/-- The maximal divisible subgroup of a product is the product of the maximal divisible
subgroups. -/
theorem maxDivisible_prod :
    maxDivisible (A × B) = (maxDivisible A).prod (maxDivisible B) := by
  refine le_antisymm (fun x hx ↦ ⟨map_mem_maxDivisible (AddMonoidHom.fst A B) hx,
    map_mem_maxDivisible (AddMonoidHom.snd A B) hx⟩) ?_
  refine IsDivisible.le_maxDivisible fun n hn x hx ↦ ?_
  obtain ⟨a, ha, ha'⟩ := exists_mem_maxDivisible_nsmul_eq hx.1 hn
  obtain ⟨b, hb, hb'⟩ := exists_mem_maxDivisible_nsmul_eq hx.2 hn
  exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext ha' hb'⟩

/-- The maximal divisible subgroup of an arbitrary product is the product of the maximal
divisible subgroups. -/
theorem maxDivisible_pi {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)] :
    maxDivisible (∀ i, A i) = AddSubgroup.pi Set.univ fun i ↦ maxDivisible (A i) := by
  refine le_antisymm (fun x hx i _ ↦ map_mem_maxDivisible (Pi.evalAddMonoidHom A i) hx) ?_
  refine IsDivisible.le_maxDivisible fun n hn x hx ↦ ?_
  choose y hy hyx using fun i ↦ exists_mem_maxDivisible_nsmul_eq (hx i trivial) hn
  exact ⟨y, fun i _ ↦ hy i, funext hyx⟩

end Products

section Exponent

/-- An abelian group of bounded exponent has no nonzero divisible subgroup. -/
theorem maxDivisible_eq_bot_of_exponentExists (h : AddMonoid.ExponentExists A) :
    maxDivisible A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, -, rfl⟩ := exists_mem_maxDivisible_nsmul_eq hx
    (AddMonoid.exponent_ne_zero.2 h)
  exact (mem_bot).2 (AddMonoid.exponent_nsmul_eq_zero y)

/-- A finite abelian group has no nonzero divisible subgroup. -/
@[simp]
theorem maxDivisible_eq_bot_of_finite [Finite A] : maxDivisible A = ⊥ :=
  maxDivisible_eq_bot_of_exponentExists AddMonoid.ExponentExists.of_finite

end Exponent

section Multiples

/-- The maximal divisible subgroup is contained in every subgroup `n A` with `n ≠ 0`. -/
theorem maxDivisible_le_range_nsmul {n : ℕ} (hn : n ≠ 0) :
    maxDivisible A ≤ (nsmulAddMonoidHom (α := A) n).range := fun _ hx ↦
  (exists_mem_maxDivisible_nsmul_eq hx hn).imp fun _ hy ↦ hy.2

/-- The maximal divisible subgroup is contained in `⋂_{m ≥ 1} m A`. -/
theorem maxDivisible_le_iInf_range_nsmul :
    maxDivisible A ≤ ⨅ n : {n : ℕ // 0 < n}, (nsmulAddMonoidHom (α := A) n.val).range :=
  le_iInf fun n ↦ maxDivisible_le_range_nsmul n.property.ne'

/-- **Stabilization criterion.** If `w A ≤ (w k) A` for every `k ≠ 0`, then `w A` is
divisible. -/
theorem isDivisible_range_nsmul {w : ℕ}
    (h : ∀ k : ℕ, k ≠ 0 →
      (nsmulAddMonoidHom (α := A) w).range ≤ (nsmulAddMonoidHom (α := A) (w * k)).range) :
    (nsmulAddMonoidHom (α := A) w).range.IsDivisible := by
  intro n hn x hx
  obtain ⟨b, rfl⟩ := h n hn hx
  refine ⟨w • b, ⟨b, rfl⟩, ?_⟩
  rw [nsmulAddMonoidHom_apply, smul_smul, mul_comm]

/-- **Stabilization criterion.** If `w ≠ 0` and `w A ≤ (w k) A` for every `k ≠ 0`, then `w A` is
the maximal divisible subgroup. -/
theorem range_nsmul_eq_maxDivisible {w : ℕ} (hw : w ≠ 0)
    (h : ∀ k : ℕ, k ≠ 0 →
      (nsmulAddMonoidHom (α := A) w).range ≤ (nsmulAddMonoidHom (α := A) (w * k)).range) :
    (nsmulAddMonoidHom (α := A) w).range = maxDivisible A :=
  le_antisymm (isDivisible_range_nsmul h).le_maxDivisible (maxDivisible_le_range_nsmul hw)

/-- **Stabilization criterion.** If `w ≠ 0` and `w A ≤ (w k) A` for every `k ≠ 0`, then the
maximal divisible subgroup is `⋂_{m ≥ 1} m A`. -/
theorem maxDivisible_eq_iInf_range_nsmul {w : ℕ} (hw : w ≠ 0)
    (h : ∀ k : ℕ, k ≠ 0 →
      (nsmulAddMonoidHom (α := A) w).range ≤ (nsmulAddMonoidHom (α := A) (w * k)).range) :
    maxDivisible A = ⨅ n : {n : ℕ // 0 < n}, (nsmulAddMonoidHom (α := A) n.val).range := by
  refine le_antisymm maxDivisible_le_iInf_range_nsmul ?_
  rw [← range_nsmul_eq_maxDivisible hw h]
  exact iInf_le_of_le ⟨w, Nat.pos_of_ne_zero hw⟩ le_rfl

/-- **Splitting off a cyclic quotient.** If `w ≠ 0`, `w A ≤ (w k) A` for every `k ≠ 0`, and
`A ⧸ w A` is cyclic of order `w`, then `A ≃+ Div(A) × ℤ/w`, noncanonically. -/
theorem nonempty_addEquiv_maxDivisible_prod_zmod {w : ℕ} (hw : w ≠ 0)
    (h : ∀ k : ℕ, k ≠ 0 →
      (nsmulAddMonoidHom (α := A) w).range ≤ (nsmulAddMonoidHom (α := A) (w * k)).range)
    (e : A ⧸ (nsmulAddMonoidHom (α := A) w).range ≃+ ZMod w) :
    Nonempty (A ≃+ maxDivisible A × ZMod w) := by
  obtain ⟨f⟩ := nonempty_addEquiv_maxDivisible_prod_quotient (A := A)
  have hq : A ⧸ maxDivisible A ≃+ ZMod w :=
    (QuotientAddGroup.quotientAddEquivOfEq (range_nsmul_eq_maxDivisible hw h).symm).trans e
  exact ⟨f.trans (AddEquiv.prodCongr (AddEquiv.refl _) hq)⟩

end Multiples

section Examples

/-- The integers are reduced: `Div(ℤ) = 0`. -/
@[simp]
theorem maxDivisible_int : maxDivisible ℤ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, -, hy⟩ := exists_mem_maxDivisible_nsmul_eq hx (Nat.add_one_ne_zero x.natAbs)
  rw [nsmul_eq_mul] at hy
  rw [mem_bot, ← hy]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  · exfalso
    have h1 : 1 ≤ y.natAbs := Int.natAbs_pos.2 hy0
    have h2 := congrArg Int.natAbs hy
    rw [Int.natAbs_mul, Int.natAbs_natCast] at h2
    nlinarith [Nat.mul_le_mul_left (x.natAbs + 1) h1]

end Examples

end TauCeti.AddCommGroup
