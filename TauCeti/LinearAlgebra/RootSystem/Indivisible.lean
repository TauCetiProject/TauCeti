/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Indivisible roots of a root pairing

In a crystallographic (possibly non-reduced) root pairing `P`, two linearly dependent roots can
differ only by a factor `±1`, `±2`, or `±1/2`. The roots that are not twice another root — the
*indivisible* roots — form a reduced crystallographic root pairing `P.indivisible` on the same
weight and coweight spaces, with the same Weyl group (`P.indivisibleWeylGroupEquiv`).

Because proportional roots induce the same linear reflection (`P.reflection_eq_of_root_eq_smul`),
every reflection of `P` already belongs to `P.indivisible`, and passing to `P.indivisible` reduces
questions about the Weyl group of a possibly non-reduced root pairing (such as non-reduced systems
of type `BCₙ`) to the reduced case.

This file also constructs a base `P.baseOfRegularCoweight v hv` attached to a regular coweight `v`
of any finite reduced crystallographic root pairing over a linearly ordered commutative ring,
without assuming `[Field R]` or `[P.IsRootSystem]`, using the canonical positive-definite
root/coroot forms to identify the additively indecomposable roots and coroots. Combining the two
yields `RootPairing.weylGroup.eq_one_of_forall_root'_pos`: in any finite crystallographic (possibly
non-reduced, possibly non-spanning) root pairing over a linearly ordered commutative ring, a
Weyl-group element preserving the positive roots for a regular coweight is trivial.

## Main definitions

* `RootPairing.IsIndivisible`: a root index is indivisible if its root is not twice another root.
* `RootPairing.indivisible`: the sub-pairing of indivisible roots.
* `RootPairing.autToIndivisible`: restriction of automorphisms of `P` to `P.indivisible`.
* `RootPairing.indivisibleWeylGroupEquiv`: the canonical isomorphism
  `P.indivisible.weylGroup ≃* P.weylGroup`.
* `RootPairing.baseOfRegularCoweight`: the base cut out by a regular coweight over a linearly
  ordered commutative ring.

## Main results

* `RootPairing.reflection_eq_of_root_eq_smul`, `RootPairing.reflectionPerm_eq_of_root_eq_smul`,
  `RootPairing.weylGroup.ofIdx_eq_of_root_eq_smul`: proportional roots have the same reflection.
* `RootPairing.root_eq_or_eq_neg_or_two_smul_of_not_linearIndependent`: two linearly dependent
  roots of a crystallographic root pairing are equal up to sign or a factor of `2`.
* `RootPairing.instIndivisibleIsReduced`: `P.indivisible` is reduced.
* `RootPairing.isPos_baseOfRegularCoweight_iff`: positivity with respect to
  `P.baseOfRegularCoweight v hv` is positivity of evaluation at `v`.
* `RootPairing.weylGroup.eq_one_of_forall_root'_pos`: a Weyl-group element keeping every
  `v`-positive root `v`-positive is the identity.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Chapter VI, §1, no. 4–5.
-/

public section

open Function Module Set Submodule

namespace RootPairing

section Proportional

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- If `P.root j = t • P.root i`, then `2 • P.coroot j = P.pairing i j • P.coroot i`. -/
private theorem two_smul_coroot_of_root_eq_smul {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : 2 • P.coroot j = P.pairing i j • P.coroot i := by
  have hperm : P.reflectionPerm i j = P.reflectionPerm j j :=
    P.root.injective <| by
      rw [root_reflectionPerm, root_reflectionPerm, reflection_apply_self, h, map_smul,
        reflection_apply_self, smul_neg]
  have h1 := congrArg P.coroot hperm
  rw [coroot_reflectionPerm, coroot_reflectionPerm, coreflection_apply_coroot,
    coreflection_apply_self] at h1
  rw [two_nsmul]
  exact eq_of_sub_eq_zero (by rw [add_sub_assoc, add_comm (P.coroot j), h1, neg_add_cancel])

/-- If `P.root j = t • P.root i`, then `t • P.coroot j = P.coroot i`, without finiteness of
`ι`. -/
private theorem smul_coroot_of_root_eq_smul [HasUniqueDiv N] {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : t • P.coroot j = P.coroot i := by
  have hcor : 2 • P.coroot j = P.pairing i j • P.coroot i := P.two_smul_coroot_of_root_eq_smul h
  have hpair : t * P.pairing i j = 2 := by
    have h1 := congrArg (P.coroot' j) h.symm
    simpa [root_coroot'_eq_pairing] using h1
  refine nsmul_right_injective two_ne_zero ?_
  calc
    2 • (t • P.coroot j) = t • (2 • P.coroot j) := (smul_comm t 2 _).symm
    _ = t • (P.pairing i j • P.coroot i) := by rw [hcor]
    _ = (t * P.pairing i j) • P.coroot i := (mul_smul _ _ _).symm
    _ = (2 : R) • P.coroot i := by rw [hpair]
    _ = 2 • P.coroot i := by rw [two_smul, two_nsmul]

/-- Proportional roots of a root pairing induce the same linear reflection. -/
theorem reflection_eq_of_root_eq_smul [HasUniqueDiv N] {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : P.reflection j = P.reflection i := by
  have hc : t • P.coroot j = P.coroot i := P.smul_coroot_of_root_eq_smul h
  ext x
  simp only [reflection_apply, coroot', h, ← hc, map_smul, LinearMap.smul_apply, smul_eq_mul,
    smul_smul, mul_comm]

/-- Proportional roots of a root pairing induce the same coreflection. -/
theorem coreflection_eq_of_root_eq_smul [HasUniqueDiv N] {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : P.coreflection j = P.coreflection i := by
  have hc : t • P.coroot j = P.coroot i := P.smul_coroot_of_root_eq_smul h
  ext y
  simp only [coreflection_apply, root', h, ← hc, map_smul, LinearMap.smul_apply, smul_eq_mul,
    smul_smul, mul_comm]

/-- Proportional roots of a root pairing induce the same reflection permutation. -/
theorem reflectionPerm_eq_of_root_eq_smul [HasUniqueDiv N] {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : P.reflectionPerm j = P.reflectionPerm i :=
  _root_.Equiv.ext fun k ↦ P.root.injective <| by
    simp only [root_reflectionPerm, P.reflection_eq_of_root_eq_smul h]

/-- Proportional roots of a root pairing induce the same root-pairing reflection. -/
theorem equiv_reflection_eq_of_root_eq_smul [HasUniqueDiv N] {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : Equiv.reflection P j = Equiv.reflection P i :=
  Equiv.weightHom_injective P <| by
    simpa only [Equiv.weightHom_apply, Equiv.reflection_weightEquiv] using
      P.reflection_eq_of_root_eq_smul h

/-- Proportional roots of a root pairing induce the same reflection in the Weyl group. -/
theorem weylGroup.ofIdx_eq_of_root_eq_smul [HasUniqueDiv N] {i j : ι} {t : R}
    (h : P.root j = t • P.root i) : weylGroup.ofIdx P j = weylGroup.ofIdx P i :=
  Subtype.ext (P.equiv_reflection_eq_of_root_eq_smul h)

/-- Two roots with the same linear reflection are linearly dependent when `2 ≠ 0`. -/
theorem not_linearIndependent_of_reflection_eq [NeZero (2 : R)] {i j : ι}
    (h : P.reflection j = P.reflection i) : ¬ LinearIndependent R ![P.root i, P.root j] := by
  intro hli
  have h1 : P.reflection j (P.root i) = P.reflection i (P.root i) := congrArg (· (P.root i)) h
  rw [reflection_apply_root, reflection_apply_self] at h1
  have hrel : (2 : R) • P.root i + (-P.pairing i j) • P.root j = 0 := by
    rw [two_smul, neg_smul, ← sub_eq_add_neg, add_sub_assoc]
    rw [eq_neg_iff_add_eq_zero] at h1
    simpa [add_comm] using h1
  exact NeZero.ne (2 : R) (LinearIndependent.pair_iff.mp hli 2 (-P.pairing i j) hrel).1

/-- Two roots with the same reflection in the Weyl group are linearly dependent when `2 ≠ 0`. -/
theorem not_linearIndependent_of_ofIdx_eq [NeZero (2 : R)] {i j : ι}
    (h : weylGroup.ofIdx P j = weylGroup.ofIdx P i) :
    ¬ LinearIndependent R ![P.root i, P.root j] :=
  P.not_linearIndependent_of_reflection_eq <| by
    simpa only [weylGroup.coe_ofIdx, Equiv.weightHom_apply, Equiv.reflection_weightEquiv] using
      congrArg (fun w : P.weylGroup ↦ Equiv.weightHom P (w : P.Aut)) h

/-- In a crystallographic root pairing over a characteristic-zero domain, two linearly dependent
roots are equal up to sign or a factor of `2`. -/
theorem root_eq_or_eq_neg_or_two_smul_of_not_linearIndependent
    [IsDomain R] [CharZero R] [P.IsCrystallographic] {i j : ι}
    (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.root j = P.root i ∨ P.root j = -P.root i ∨
      P.root j = (2 : R) • P.root i ∨ P.root j = -((2 : R) • P.root i) ∨
      P.root i = (2 : R) • P.root j ∨ P.root i = -((2 : R) • P.root j) := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have hij : P.pairing j i • P.root i = (2 : R) • P.root j :=
    P.pairing_smul_root_eq_of_not_linearIndependent h
  have hji : P.pairing i j • P.root j = (2 : R) • P.root i :=
    P.pairing_smul_root_eq_of_not_linearIndependent
      (by rwa [LinearIndependent.pair_symm_iff] at h)
  set a := P.pairingIn ℤ i j
  set b := P.pairingIn ℤ j i
  have ha : P.pairing i j = (a : R) := by simpa [a] using (P.algebraMap_pairingIn ℤ i j).symm
  have hb : P.pairing j i = (b : R) := by simpa [b] using (P.algebraMap_pairingIn ℤ j i).symm
  have h4 : a * b = 4 := Int.cast_injective (α := R) <| by
    have h4R : P.pairing i j * P.pairing j i = (4 : R) := smul_left_injective R (P.ne_zero i) <| by
      dsimp only
      rw [mul_smul, hij, smul_comm, hji, smul_smul]; norm_num
    rw [Int.cast_mul, ← ha, ← hb, h4R]; norm_num
  have hcases : (a = 2 ∧ b = 2) ∨ (a = -2 ∧ b = -2) ∨ (a = 1 ∧ b = 4) ∨
      (a = -1 ∧ b = -4) ∨ (a = 4 ∧ b = 1) ∨ (a = -4 ∧ b = -1) := by
    have ha_le : a.natAbs ≤ 4 :=
      Nat.le_of_dvd (by decide) ⟨b.natAbs, by
        simpa [Int.natAbs_mul] using (congrArg Int.natAbs h4).symm⟩
    have ha_lo : -4 ≤ a := by omega
    have ha_hi : a ≤ 4 := by omega
    interval_cases a <;> omega
  rcases hcases with
    ⟨_, hb'⟩ | ⟨_, hb'⟩ | ⟨ha', _⟩ | ⟨ha', _⟩ | ⟨_, hb'⟩ | ⟨_, hb'⟩
  · exact Or.inl <| smul_right_injective M (two_ne_zero (α := R))
      (by simpa [hb, hb'] using hij.symm)
  · exact Or.inr <| Or.inl <| smul_right_injective M (two_ne_zero (α := R)) <| by
      simpa [hb, hb', smul_neg, ← neg_smul] using hij.symm
  · exact Or.inr <| Or.inr <| Or.inl (by simpa [ha, ha'] using hji)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [ha, ha', neg_eq_iff_eq_neg] using hji)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (by simpa [hb, hb'] using hij)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      (by simpa [hb, hb', neg_eq_iff_eq_neg] using hij)

end Proportional

/-! ### The sub-pairing of indivisible roots -/

section Indivisible

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- A root index `i` is indivisible if `P.root i` is not twice another root of `P`. -/
def IsIndivisible (i : ι) : Prop :=
  ∀ j : ι, P.root i ≠ (2 : R) • P.root j

/-- Reflections preserve indivisibility of root indices. -/
theorem isIndivisible_reflectionPerm_iff (i j : ι) :
    P.IsIndivisible (P.reflectionPerm i j) ↔ P.IsIndivisible j := by
  refine ⟨fun h k hk ↦ h (P.reflectionPerm i k) ?_,
    fun h k hk ↦ h (P.reflectionPerm i k) ?_⟩
  · rw [root_reflectionPerm, root_reflectionPerm, hk, map_smul]
  · have h' := congrArg (P.reflection i) hk
    simpa only [← root_reflectionPerm, P.reflectionPerm_involutive i j, map_smul] using h'

/-- The sub-pairing consisting of the indivisible roots of `P`, on the same weight and coweight
spaces. -/
def indivisible : RootPairing {i : ι // P.IsIndivisible i} R M N where
  toLinearMap := P.toLinearMap
  isPerfPair_toLinearMap := P.isPerfPair_toLinearMap
  root := ⟨fun i ↦ P.root i.1, fun _ _ h ↦ Subtype.ext (P.root.injective h)⟩
  coroot := ⟨fun i ↦ P.coroot i.1, fun _ _ h ↦ Subtype.ext (P.coroot.injective h)⟩
  root_coroot_two i := P.root_coroot_two i.1
  reflectionPerm i :=
    (P.reflectionPerm i.1).subtypeEquiv fun j ↦ (P.isIndivisible_reflectionPerm_iff i.1 j).symm
  reflectionPerm_root i j := P.reflectionPerm_root i.1 j.1
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i.1 j.1

@[simp]
lemma indivisible_toLinearMap : P.indivisible.toLinearMap = P.toLinearMap :=
  (rfl)

@[simp]
lemma indivisible_root (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.root i = P.root i.1 :=
  (rfl)

@[simp]
lemma indivisible_coroot (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.coroot i = P.coroot i.1 :=
  (rfl)

@[simp]
lemma indivisible_root' (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.root' i = P.root' i.1 :=
  (rfl)

@[simp]
lemma indivisible_coroot' (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.coroot' i = P.coroot' i.1 :=
  (rfl)

@[simp]
lemma indivisible_pairing (i j : {i : ι // P.IsIndivisible i}) :
    P.indivisible.pairing i j = P.pairing i.1 j.1 :=
  (rfl)

@[simp]
lemma indivisible_reflection (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.reflection i = P.reflection i.1 :=
  (rfl)

@[simp]
lemma indivisible_coreflection (i : {i : ι // P.IsIndivisible i}) :
    P.indivisible.coreflection i = P.coreflection i.1 :=
  (rfl)

@[simp]
lemma indivisible_reflectionPerm_coe (i j : {i : ι // P.IsIndivisible i}) :
    (P.indivisible.reflectionPerm i j : ι) = P.reflectionPerm i.1 j.1 :=
  (rfl)

instance instIndivisibleIsValuedIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    P.indivisible.IsValuedIn S where
  exists_value i j := IsValuedIn.exists_value (P := P) (S := S) i.1 j.1

/-- The indivisible sub-pairing of a crystallographic root pairing is reduced. -/
instance instIndivisibleIsReduced [IsDomain R] [CharZero R] [P.IsCrystallographic] :
    P.indivisible.IsReduced where
  eq_or_eq_neg i j h := by
    rcases P.root_eq_or_eq_neg_or_two_smul_of_not_linearIndependent h with
      h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr (neg_eq_iff_eq_neg.mp h1.symm)
    · exact (j.2 i.1 h1).elim
    · refine (j.2 (P.reflectionPerm i.1 i.1) ?_).elim
      simpa only [root_reflectionPerm, reflection_apply_self, smul_neg] using h1
    · exact (i.2 j.1 h1).elim
    · refine (i.2 (P.reflectionPerm j.1 j.1) ?_).elim
      simpa only [root_reflectionPerm, reflection_apply_self, smul_neg] using h1

/-- Every root of a crystallographic root pairing is either indivisible or twice an indivisible
root. -/
theorem exists_isIndivisible_of_index [CharZero R] [P.IsCrystallographic] (i : ι) :
    P.IsIndivisible i ∨ ∃ j : ι, P.IsIndivisible j ∧ P.root i = (2 : R) • P.root j := by
  by_cases hi : P.IsIndivisible i
  · exact Or.inl hi
  · simp only [IsIndivisible, not_forall, not_ne_iff] at hi
    obtain ⟨j, hj⟩ := hi
    refine Or.inr ⟨j, fun k hk ↦ ?_, hj⟩
    have h4 : (4 : R) * P.pairing k i = 2 := by
      have hik : P.root i = (4 : R) • P.root k := by rw [hj, hk, smul_smul]; norm_num
      simpa [root_coroot'_eq_pairing] using (congrArg (P.coroot' i) hik).symm
    have hZ : (4 : ℤ) * P.pairingIn ℤ k i = 2 := Int.cast_injective (α := R) <| by
      have hp : (P.pairingIn ℤ k i : R) = P.pairing k i := by
        simpa using P.algebraMap_pairingIn ℤ k i
      rw [Int.cast_mul, hp]
      simpa using h4
    omega

/-- Every automorphism of `P` preserves indivisibility of root indices. -/
theorem isIndivisible_indexEquiv_iff (e : P.Aut) (i : ι) :
    P.IsIndivisible (e.indexEquiv i) ↔ P.IsIndivisible i := by
  refine ⟨fun h k hk ↦ h (e.indexEquiv k) ?_, fun h k hk ↦ h (e.indexEquiv.symm k) ?_⟩
  · rw [← Hom.root_weightMap_apply P P i e.toHom, ← Hom.root_weightMap_apply P P k e.toHom,
      hk, map_smul]
  · apply e.bijective_weightMap.1
    rw [map_smul, Hom.root_weightMap_apply, Hom.root_weightMap_apply,
      _root_.Equiv.apply_symm_apply, hk]

/-- Restriction of automorphisms of `P` to the indivisible sub-pairing `P.indivisible`. -/
def autToIndivisible : P.Aut →* P.indivisible.Aut where
  toFun e :=
    { weightMap := e.weightMap
      coweightMap := e.coweightMap
      indexEquiv := e.indexEquiv.subtypeEquiv fun i ↦ (P.isIndivisible_indexEquiv_iff e i).symm
      weight_coweight_transpose := e.weight_coweight_transpose
      root_weightMap := by
        ext i
        exact Hom.root_weightMap_apply P P i.1 e.toHom
      coroot_coweightMap := by
        ext i
        exact Hom.coroot_coweightMap_apply P P i.1 e.toHom
      bijective_weightMap := e.bijective_weightMap
      bijective_coweightMap := e.bijective_coweightMap }
  map_one' := by
    ext x <;> rfl
  map_mul' e₁ e₂ := by
    ext x <;> rfl

@[simp]
lemma autToIndivisible_weightMap (e : P.Aut) :
    (P.autToIndivisible e).weightMap = e.weightMap :=
  (rfl)

@[simp]
lemma autToIndivisible_indexEquiv_coe (e : P.Aut) (i : {i : ι // P.IsIndivisible i}) :
    ((P.autToIndivisible e).indexEquiv i : ι) = e.indexEquiv i.1 :=
  (rfl)

@[simp]
lemma autToIndivisible_smul (e : P.Aut) (x : M) :
    P.autToIndivisible e • x = e • x :=
  (rfl)

@[simp]
lemma autToIndivisible_reflection (i : {i : ι // P.IsIndivisible i}) :
    P.autToIndivisible (Equiv.reflection P i.1) = Equiv.reflection P.indivisible i :=
  Equiv.weightHom_injective P.indivisible (by ext x; rfl)

/-- Restriction of automorphisms to `P.indivisible` is injective, as both act faithfully on the
common weight space `M`. -/
theorem autToIndivisible_injective : Function.Injective P.autToIndivisible := fun e₁ e₂ h ↦
  Equiv.weightHom_injective P <| LinearEquiv.ext fun x ↦ by
    simpa only [Equiv.weightHom_apply, Equiv.weightEquiv_apply, ← P.autToIndivisible_weightMap]
      using congrArg (fun e : P.indivisible.Aut ↦ e.weightMap x) h

private noncomputable def weylGroupToIndivisible
    [CharZero R] [P.IsCrystallographic] :
    P.weylGroup →* P.indivisible.weylGroup :=
  (P.autToIndivisible.domRestrict P.weylGroup).codRestrict P.indivisible.weylGroup <| by
    rintro ⟨g, hg⟩
    induction hg using weylGroup.induction with
    | mem i =>
      rcases P.exists_isIndivisible_of_index i with hi | ⟨j, hj, hij⟩
      · simpa only [MonoidHom.domRestrict_apply,
          autToIndivisible_reflection P (⟨i, hi⟩ : {k // P.IsIndivisible k})] using
          P.indivisible.reflection_mem_weylGroup ⟨i, hi⟩
      · have h2 : (2 : R) * P.pairing j i = 2 := by
          simpa [root_coroot'_eq_pairing] using (congrArg (P.coroot' i) hij).symm
        have hpZ : P.pairingIn ℤ j i = 1 := by
          have hp : (P.pairingIn ℤ j i : R) = P.pairing j i := by
            simpa using P.algebraMap_pairingIn ℤ j i
          have : (2 : ℤ) * P.pairingIn ℤ j i = 2 := Int.cast_injective (α := R) <| by
            rw [Int.cast_mul, hp]; simpa using h2
          omega
        have hp : P.pairing j i = 1 := by
          rw [← P.algebraMap_pairingIn ℤ j i, hpZ]; simp
        have hcor : (2 : R) • P.coroot i = P.coroot j := by
          have h := P.two_smul_coroot_of_root_eq_smul hij
          simpa [hp, two_nsmul, two_smul] using h
        have hrefl : Equiv.reflection P i = Equiv.reflection P j :=
          Equiv.weightHom_injective P <| LinearEquiv.ext fun x ↦ by
            simp only [Equiv.weightHom_apply, Equiv.reflection_weightEquiv, reflection_apply,
              coroot', hij, ← hcor, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul,
              mul_comm]
        rw [MonoidHom.domRestrict_apply]
        dsimp only
        rw [hrefl, P.autToIndivisible_reflection (⟨j, hj⟩ : {k // P.IsIndivisible k})]
        exact P.indivisible.reflection_mem_weylGroup ⟨j, hj⟩
    | one =>
      simpa only [MonoidHom.domRestrict_apply, map_one] using P.indivisible.weylGroup.one_mem
    | mul x y _ _ hx hy =>
      simpa only [MonoidHom.domRestrict_apply, map_mul] using P.indivisible.weylGroup.mul_mem hx hy

/-- **The Weyl group of a crystallographic root pairing is canonically isomorphic to the Weyl group
of its indivisible sub-pairing.** -/
noncomputable def indivisibleWeylGroupEquiv [CharZero R] [P.IsCrystallographic] :
    P.indivisible.weylGroup ≃* P.weylGroup :=
  (MulEquiv.ofBijective P.weylGroupToIndivisible
    ⟨fun _ _ h ↦ Subtype.ext (P.autToIndivisible_injective (congrArg Subtype.val h)), by
      rintro ⟨w, hw⟩
      induction hw using weylGroup.induction with
      | mem i =>
        refine ⟨weylGroup.ofIdx P i.1, Subtype.ext ?_⟩
        exact P.autToIndivisible_reflection i
      | one => exact ⟨1, map_one _⟩
      | mul x y _ _ hx hy =>
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        exact ⟨x' * y', by rw [map_mul, hx', hy']; rfl⟩⟩).symm

@[simp]
theorem indivisibleWeylGroupEquiv_symm_ofIdx [CharZero R] [P.IsCrystallographic]
    (i : {i : ι // P.IsIndivisible i}) :
    P.indivisibleWeylGroupEquiv.symm (weylGroup.ofIdx P i.1) =
      weylGroup.ofIdx P.indivisible i :=
  Subtype.ext (P.autToIndivisible_reflection i)

@[simp]
theorem indivisibleWeylGroupEquiv_ofIdx [CharZero R] [P.IsCrystallographic]
    (i : {i : ι // P.IsIndivisible i}) :
    P.indivisibleWeylGroupEquiv (weylGroup.ofIdx P.indivisible i) =
      weylGroup.ofIdx P i.1 := by
  rw [← P.indivisibleWeylGroupEquiv_symm_ofIdx i, MulEquiv.apply_symm_apply]

@[simp]
theorem indivisibleWeylGroupEquiv_smul [CharZero R] [P.IsCrystallographic]
    (w : P.indivisible.weylGroup) (x : M) :
    P.indivisibleWeylGroupEquiv w • x = w • x := by
  have h : P.autToIndivisible (P.indivisibleWeylGroupEquiv w : P.Aut) = (w : P.indivisible.Aut) :=
    congrArg Subtype.val (P.indivisibleWeylGroupEquiv.symm_apply_apply w)
  rw [Subgroup.smul_def, Subgroup.smul_def, ← P.autToIndivisible_smul, h]

/-- The permutation action of `P.indivisible.weylGroup` on indivisible root indices agrees with the
permutation action of `P.weylGroup` via `P.indivisibleWeylGroupEquiv`. -/
theorem indivisible_weylGroupToPerm_coe [CharZero R] [P.IsCrystallographic]
    (w : P.indivisible.weylGroup) (i : {i : ι // P.IsIndivisible i}) :
    (P.indivisible.weylGroupToPerm w i : ι) =
      P.weylGroupToPerm (P.indivisibleWeylGroupEquiv w) i.1 := by
  apply P.root.injective
  rw [← P.weylGroup_apply_root, P.indivisibleWeylGroupEquiv_smul,
    ← P.indivisible_root, ← P.indivisible.weylGroup_apply_root, indivisible_root]

end Indivisible

/-! ### Bases from regular coweights without `[Field R]` or `[P.IsRootSystem]` -/

section BaseOfRegularCoweight

variable {ι R M N : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (P : RootPairing ι R M N)

/-- If a coroot is the sum of two coroots, then the corresponding root is a strictly positive
linear combination of the two corresponding roots. -/
private theorem pos_smul_root_eq_add_of_coroot_eq_add [Finite ι] {i j k : ι}
    (h : P.coroot i = P.coroot j + P.coroot k) :
    ∃ a b c : R, 0 < b ∧ 0 < c ∧ a • P.root i = b • P.root j + c • P.root k := by
  have : Fintype ι := Fintype.ofFinite ι
  let l (r : ι) : R := P.RootForm (P.root r) (P.root r)
  have hl (r : ι) : 0 < l r := by
    have hr : P.rootSpanMem R r ≠ 0 := fun h0 ↦ P.ne_zero r (congrArg Subtype.val h0)
    simpa only [l, ← P.algebraMap_posRootForm_posForm R (P.rootSpanMem R r) (P.rootSpanMem R r),
      Algebra.algebraMap_self_apply] using P.posRootForm_posForm_pos_of_ne_zero R hr
  refine ⟨l j * l k, l i * l k, l i * l j, mul_pos (hl i) (hl k), mul_pos (hl i) (hl j), ?_⟩
  let w : P.rootSpan R := (l j * l k) • P.rootSpanMem R i -
    (l i * l k) • P.rootSpanMem R j - (l i * l j) • P.rootSpanMem R k
  have hpol : P.Polarization (2 • (w : M)) = 0 := by
    have hsmul (r : ι) : P.Polarization (2 • P.root r) = l r • P.coroot r := by
      rw [map_nsmul, ← P.rootForm_self_smul_coroot]
    have hcor : (l i * l j * l k) • P.coroot i =
        (l i * l j * l k) • P.coroot j + (l i * l j * l k) • P.coroot k := by
      rw [h, smul_add]
    simp only [w, Submodule.coe_sub, SetLike.val_smul, rootSpanMem, smul_sub,
      smul_comm (2 : ℕ), map_sub, map_smul, hsmul, smul_smul]
    rw [show l j * l k * l i = l i * l j * l k by ring,
      show l i * l k * l j = l i * l j * l k by ring, hcor]
    abel
  have hzero : (P.posRootForm R).posForm (2 • w) (2 • w) = 0 := by
    have hR : P.RootForm (↑(2 • w) : M) (↑(2 • w) : M) = 0 := by
      rw [← P.toLinearMap_apply_apply_Polarization, AddSubmonoidClass.coe_nsmul, hpol, map_zero]
    simpa only [← P.algebraMap_posRootForm_posForm R (2 • w) (2 • w),
      Algebra.algebraMap_self_apply] using hR
  have hw2 : 2 • w = 0 := by
    by_contra hne
    exact (P.posRootForm_posForm_pos_of_ne_zero R hne).ne' hzero
  have hw0 : (w : M) = 0 := by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have : HasUniqueDiv M := .of_isTorsionFree R M
    exact nsmul_right_injective two_ne_zero (by simpa using congrArg Subtype.val hw2)
  exact sub_eq_zero.mp (by simpa [w, sub_sub] using hw0)

/-- Additively indecomposable roots for `f` are additively indecomposable coroots for any dual
functional `g` with the same positive roots. -/
private theorem baseOf_root_subset_baseOf_coroot [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    (f : Dual R M) (g : Dual R N) (hf : ∀ i, f (P.root i) ≠ 0)
    (hfg : ∀ i, 0 < f (P.root i) ↔ 0 < g (P.coroot i)) :
    IsAddIndecomposable.baseOf P.root (f : M →+ R) ⊆
      IsAddIndecomposable.baseOf P.coroot (g : N →+ R) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let s := IsAddIndecomposable.baseOf P.root (f : M →+ R)
  refine fun i hi ↦ ⟨(hfg i).mp hi.1, fun j hj k hk hjk ↦ ?_⟩
  obtain ⟨u, v, w, hv, hw, huv⟩ := P.pos_smul_root_eq_add_of_coroot_eq_add hjk
  have hmem {r : ι} (hr : 0 < g (P.coroot r)) :
      ∃ c : P.root '' s → ℕ, ∑ x, c x • (x : M) = P.root r := by
    rw [← Submodule.mem_span_iff_of_fintype, ← mem_toAddSubmonoid,
      span_nat_eq_addSubmonoidClosure, AddSubmonoid.closure_image_isAddIndecomposable_baseOf,
      AddSubmonoid.mem_closure_image_pos_iff P.root (f : M →+ R) _ (P.ne_zero _)]
    exact (hfg r).mpr hr
  obtain ⟨a, ha⟩ := hmem hj
  obtain ⟨b, hb⟩ := hmem hk
  let ri : P.root '' s := ⟨P.root i, mem_image_of_mem _ hi⟩
  have hcoef : (fun x ↦ v * (a x : R) + w * (b x : R)) = Pi.single ri u := by
    have hli : LinearIndependent R (fun x : P.root '' s ↦ (x : M)) := by
      rw [linearIndependent_subtype_iff, ← linearIndepOn_iff_image P.root.injective.injOn]
      exact P.linearIndepOn_root_baseOf' f hf
    refine linearIndependent_iff_injective_fintypeLinearCombination.mp hli ?_
    simp only [Fintype.linearCombination_apply, add_smul, Finset.sum_add_distrib, mul_smul,
      ← Finset.smul_sum, Nat.cast_smul_eq_nsmul, ha, hb, ← huv, Pi.single_apply, ite_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ri]
  have ha0 (x : P.root '' s) (hx : x ≠ ri) : a x = 0 := by
    have hx' : v * (a x : R) + w * (b x : R) = 0 := by simpa [hx] using congrFun hcoef x
    have h1 : 0 ≤ v * (a x : R) := mul_nonneg hv.le (Nat.cast_nonneg _)
    have h2 : 0 ≤ w * (b x : R) := mul_nonneg hw.le (Nat.cast_nonneg _)
    have h0 : v * (a x : R) = 0 := le_antisymm (by linarith) h1
    exact Nat.cast_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hv.ne')
  have hj_eq : P.root j = (a ri : R) • P.root i := by
    rw [← ha, Finset.sum_eq_single ri (fun x _ hx ↦ by simp [ha0 x hx]) (by simp),
      Nat.cast_smul_eq_nsmul]
  have hdep : ¬ LinearIndependent R ![P.root i, P.root j] := fun hli ↦
    neg_ne_zero.mpr one_ne_zero (LinearIndependent.pair_iff.mp hli (a ri : R) (-1)
      (by rw [neg_smul, one_smul, ← hj_eq, add_neg_cancel])).2
  rcases IsReduced.eq_or_eq_neg (P := P) i j hdep with hEq | hNeg
  · exact Or.inr (by simpa [P.root.injective hEq] using hjk.symm)
  · exfalso
    have hpos_i : 0 < f (P.root i) := hi.1
    have hpos_j : 0 < f (P.root j) := (hfg j).mpr hj
    have hneg : f (P.root i) = -f (P.root j) := by rw [hNeg, map_neg]
    linarith

/-- Every coroot lies in `±AddSubmonoid.closure` of the coroots indexed by the indecomposable
roots for a regular coweight `v`. -/
private theorem coroot_mem_or_neg_mem_baseOf_regularCoweight
    [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    (v : N) (hv : ∀ i, P.root' i v ≠ 0) (i : ι) :
    P.coroot i ∈ AddSubmonoid.closure
        (P.coroot '' IsAddIndecomposable.baseOf P.root (P.toLinearMap.flip v : M →+ R)) ∨
      -P.coroot i ∈ AddSubmonoid.closure
        (P.coroot '' IsAddIndecomposable.baseOf P.root (P.toLinearMap.flip v : M →+ R)) := by
  have : Fintype ι := Fintype.ofFinite ι
  let := P.indexNeg
  let f : Dual R M := P.toLinearMap.flip v
  let g : Dual R N := P.CorootForm v
  have hf (r : ι) : f (P.root r) = P.root' r v := rfl
  have hfg (r : ι) : 0 < f (P.root r) ↔ 0 < g (P.coroot r) := by
    have hlen : 0 < P.CorootForm (P.coroot r) (P.coroot r) := by
      have hr : P.flip.rootSpanMem R r ≠ 0 :=
        fun h0 ↦ P.flip.ne_zero r (congrArg Subtype.val h0)
      have hpos := P.flip.posRootForm_posForm_pos_of_ne_zero R hr
      have heq := P.flip.algebraMap_posRootForm_posForm R (P.flip.rootSpanMem R r)
        (P.flip.rootSpanMem R r)
      rw [Algebra.algebraMap_self_apply] at heq
      rwa [heq] at hpos
    have hrel : P.CorootForm (P.coroot r) (P.coroot r) * f (P.root r) =
        2 * g (P.coroot r) := by
      have h1 := congrArg (P.toLinearMap.flip v) (P.corootForm_self_smul_root r)
      have hsymm : P.CorootForm (P.coroot r) v = g (P.coroot r) :=
        P.flip.rootForm_symmetric.eq (P.coroot r) v
      simpa only [f, LinearMap.flip_apply, map_smul, map_nsmul, P.toLinearMap_apply_CoPolarization,
        smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, hsymm] using h1
    constructor <;> intro hpos <;> nlinarith
  have hg (r : ι) : g (P.coroot r) ≠ 0 := fun h0 ↦ by
    rcases (hv r).lt_or_gt with hlt | hgt
    · have : 0 < f (P.root (P.reflectionPerm r r)) := by simpa [hf] using hlt
      have hpos := (hfg (P.reflectionPerm r r)).mp this
      have : g (P.coroot (P.reflectionPerm r r)) = -g (P.coroot r) := by simp
      linarith
    · linarith [(hfg r).mp hgt]
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have hbase_eq : IsAddIndecomposable.baseOf P.root (f : M →+ R) =
      IsAddIndecomposable.baseOf P.coroot (g : N →+ R) :=
    subset_antisymm (P.baseOf_root_subset_baseOf_coroot f g hv hfg)
      (P.flip.baseOf_root_subset_baseOf_coroot g f hg fun r ↦ (hfg r).symm)
  simpa [hbase_eq, f] using
    IsAddIndecomposable.mem_or_neg_mem_closure_baseOf P.coroot (g : N →+ R) i (hg i) (by simp)

/-- The base of a finite reduced crystallographic root pairing over a linearly ordered commutative
ring cut out by a regular coweight `v : N`. -/
noncomputable def baseOfRegularCoweight [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    (v : N) (hv : ∀ i, P.root' i v ≠ 0) : P.Base where
  support :=
    (IsAddIndecomposable.baseOf P.root (P.toLinearMap.flip v : M →+ R)).toFinite.toFinset
  linearIndepOn_root := by
    simpa using P.linearIndepOn_root_baseOf' (P.toLinearMap.flip v) hv
  linearIndepOn_coroot := by
    have : Fintype ι := Fintype.ofFinite ι
    simpa using P.linearIndepOn_coroot_iff.mpr
      (P.linearIndepOn_root_baseOf' (P.toLinearMap.flip v) hv)
  root_mem_or_neg_mem i := by
    let := P.indexNeg
    simpa using IsAddIndecomposable.mem_or_neg_mem_closure_baseOf P.root
      (P.toLinearMap.flip v : M →+ R) i (hv i) (by simp)
  coroot_mem_or_neg_mem i := by
    simpa using P.coroot_mem_or_neg_mem_baseOf_regularCoweight v hv i

/-- Every simple root of `P.baseOfRegularCoweight v hv` is positive at `v`. -/
theorem root'_pos_of_mem_support_baseOfRegularCoweight
    [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    (v : N) (hv : ∀ i, P.root' i v ≠ 0) {i : ι}
    (hi : i ∈ (P.baseOfRegularCoweight v hv).support) : 0 < P.root' i v := by
  have hi' : i ∈ IsAddIndecomposable.baseOf P.root (P.toLinearMap.flip v : M →+ R) := by
    simpa [baseOfRegularCoweight] using hi
  exact IsAddIndecomposable.baseOf_subset_pos P.root (P.toLinearMap.flip v : M →+ R) hi'

/-- A root is positive for `P.baseOfRegularCoweight v hv` if and only if it is positive at `v`. -/
theorem isPos_baseOfRegularCoweight_iff
    [Finite ι] [P.IsCrystallographic] [P.IsReduced]
    (v : N) (hv : ∀ i, P.root' i v ≠ 0) (i : ι) :
    (P.baseOfRegularCoweight v hv).IsPos i ↔ 0 < P.root' i v := by
  have hsup : ∀ j ∈ (P.baseOfRegularCoweight v hv).support, 0 < P.root' j v :=
    fun _ hj ↦ P.root'_pos_of_mem_support_baseOfRegularCoweight v hv hj
  exact ⟨fun h ↦ root'_pos_of_isPos hsup h,
    fun h ↦ by_contra fun hn ↦ (root'_neg_of_not_isPos hsup hn).not_gt h⟩

variable {P} in
/-- **A Weyl-group element preserving the positive roots for a regular coweight is trivial.**
Applies to any finite crystallographic (possibly non-reduced, possibly non-spanning) root pairing
over a linearly ordered commutative ring. -/
theorem weylGroup.eq_one_of_forall_root'_pos
    [Finite ι] [P.IsCrystallographic] {v : N} (hv : ∀ i, P.root' i v ≠ 0) {w : P.weylGroup}
    (hw : ∀ i, 0 < P.root' i v → 0 < P.root' (P.weylGroupToPerm w i) v) : w = 1 := by
  have hv' : ∀ i : {i : ι // P.IsIndivisible i}, P.indivisible.root' i v ≠ 0 := fun i ↦ by
    rw [P.indivisible_root']; exact hv i.1
  let b := P.indivisible.baseOfRegularCoweight v hv'
  have hmaps : MapsTo (P.indivisible.weylGroupToPerm (P.indivisibleWeylGroupEquiv.symm w))
      (TauCeti.posRoots P.indivisible b) (TauCeti.posRoots P.indivisible b) := by
    intro i hi
    rw [TauCeti.mem_posRoots] at hi ⊢
    dsimp only [b] at hi ⊢
    rw [isPos_baseOfRegularCoweight_iff] at hi ⊢
    rw [indivisible_root', indivisible_weylGroupToPerm_coe, MulEquiv.apply_symm_apply]
    rw [indivisible_root'] at hi
    exact hw i.1 hi
  have h1 : P.indivisibleWeylGroupEquiv.symm w = 1 :=
    TauCeti.eq_one_of_mapsTo_posRoots (P := P.indivisible) (b := b) hmaps
  exact P.indivisibleWeylGroupEquiv.symm.injective (h1.trans (map_one _).symm)

end BaseOfRegularCoweight

end RootPairing
