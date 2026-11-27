/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Reduced
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ReflectionPerm
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Indivisible subsystem of a root pairing

For any root pairing `P : RootPairing ι R M N`, a root index `i` is **indivisible**
(`RootPairing.IsIndivisible`) if `P.root i` is not `(2 : R) • P.root j` for any `j : ι`.
Reflections preserve indivisibility (`RootPairing.IsIndivisible.reflectionPerm`), so restricting `P`
to `{i | P.IsIndivisible i}` (`RootPairing.restrict`, `RootPairing.indivisible`) yields a
well-defined sub-pairing over any commutative ring `R`.

When `R` has characteristic zero and `P` is crystallographic:
* no root is `4 • P.root i` (`RootPairing.root_ne_four_smul`), so every root is either
  indivisible or twice an indivisible root (`RootPairing.isIndivisible_or_exists_eq_two_smul`);
* `s_{2α} = s_α` on both weight and coweight spaces (`RootPairing.reflection_eq_of_root_eq_smul`,
  `RootPairing.coreflection_eq_of_root_eq_smul`) whenever `ι` is finite and `N` has unique
  division;
* when `ι` is also finite and `R` is a characteristic-zero domain, `P.indivisible` is reduced
  (`RootPairing.isReduced_indivisible`), `P` and `P.indivisible` have the same reflections and
  coreflections and canonically isomorphic Weyl groups (`RootPairing.weylGroupEquivIndivisible`),
  and if `P` is a root system and `2` is a unit in `R` (in particular, over any
  characteristic-zero field), `P.indivisible` is also a root system
  (`RootPairing.isRootSystem_indivisible`).

## Main definitions

* `RootPairing.IsIndivisible`: predicate that `P.root i` is not twice any root of `P`.
* `RootPairing.restrict`: restriction of a root pairing to a reflection-stable subset of indices.
* `RootPairing.indivisible`: the indivisible subsystem of `P`.
* `RootPairing.weylGroupEquivIndivisible`: the isomorphism `P.weylGroup ≃* P.indivisible.weylGroup`
  intertwining their actions on `M`.

## Main results

* `RootPairing.IsIndivisible.reflectionPerm`: reflections preserve indivisibility.
* `RootPairing.isIndivisible_or_exists_eq_two_smul`: every root of a crystallographic pairing
  over a characteristic-zero ring is indivisible or twice an indivisible root.
* `RootPairing.isReduced_indivisible`: `P.indivisible` is reduced.
* `RootPairing.range_reflection_indivisible` and `RootPairing.range_coreflection_indivisible`:
  `P.indivisible` and `P` have the same reflections and coreflections.
* `RootPairing.isRootSystem_indivisible`: over a characteristic-zero field, `P.indivisible` is a
  root system when `P` is.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing

section Restrict

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- Restrict a root pairing `P` to a subset `s : Set ι` of indices preserved by the reflections
among elements of `s`. -/
def restrict (P : RootPairing ι R M N) (s : Set ι)
    (hs : ∀ i ∈ s, ∀ j ∈ s, P.reflectionPerm i j ∈ s) :
    RootPairing s R M N where
  toLinearMap := P.toLinearMap
  root := (Function.Embedding.subtype _).trans P.root
  coroot := (Function.Embedding.subtype _).trans P.coroot
  root_coroot_two i := P.root_coroot_two i.val
  reflectionPerm i :=
    { toFun := fun j ↦ ⟨P.reflectionPerm i.val j.val, hs i.val i.property j.val j.property⟩
      invFun := fun j ↦ ⟨P.reflectionPerm i.val j.val, hs i.val i.property j.val j.property⟩
      left_inv := fun j ↦ Subtype.ext (P.reflectionPerm_self i.val j.val)
      right_inv := fun j ↦ Subtype.ext (P.reflectionPerm_self i.val j.val) }
  reflectionPerm_root i j := P.reflectionPerm_root i.val j.val
  reflectionPerm_coroot i j := P.reflectionPerm_coroot i.val j.val

section RestrictSimp

variable (P : RootPairing ι R M N) (s : Set ι)
  (hs : ∀ i ∈ s, ∀ j ∈ s, P.reflectionPerm i j ∈ s)

@[simp]
theorem restrict_toLinearMap : (P.restrict s hs).toLinearMap = P.toLinearMap := by rfl

@[simp]
theorem restrict_root (i : s) : (P.restrict s hs).root i = P.root i := by rfl

@[simp]
theorem restrict_coroot (i : s) : (P.restrict s hs).coroot i = P.coroot i := by rfl

@[simp]
theorem restrict_root' (i : s) : (P.restrict s hs).root' i = P.root' i := by rfl

@[simp]
theorem restrict_coroot' (i : s) : (P.restrict s hs).coroot' i = P.coroot' i := by rfl

@[simp]
theorem restrict_pairing (i j : s) : (P.restrict s hs).pairing i j = P.pairing i j := by rfl

@[simp]
theorem restrict_reflection (i : s) : (P.restrict s hs).reflection i = P.reflection i := by
  ext x
  simp [reflection_apply]

@[simp]
theorem restrict_coreflection (i : s) :
    (P.restrict s hs).coreflection i = P.coreflection i := by
  ext x
  simp [coreflection_apply]

@[simp]
theorem restrict_reflectionPerm_coe (i j : s) :
    ((P.restrict s hs).reflectionPerm i j : ι) = P.reflectionPerm i j := by rfl

instance restrict_isValuedIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    (P.restrict s hs).IsValuedIn S where
  exists_value i j := by simpa using P.exists_value i.val j.val

end RestrictSimp

end Restrict

section Indivisible

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A root index `i` of a root pairing `P` is **indivisible** if `P.root i` is not equal to
`(2 : R) • P.root j` for any root index `j`. -/
def IsIndivisible (P : RootPairing ι R M N) (i : ι) : Prop :=
  ∀ j : ι, (2 : R) • P.root j ≠ P.root i

/-- An index `i` is indivisible iff `P.root i` is not `(2 : R) • P.root j` for any `j`. -/
theorem isIndivisible_iff (P : RootPairing ι R M N) (i : ι) :
    P.IsIndivisible i ↔ ∀ j : ι, (2 : R) • P.root j ≠ P.root i :=
  Iff.rfl

/-- Reflections preserve indivisibility of root indices. -/
theorem IsIndivisible.reflectionPerm {P : RootPairing ι R M N} {i j : ι}
    (hj : P.IsIndivisible j) : P.IsIndivisible (P.reflectionPerm i j) := by
  intro k hk
  refine hj (P.reflectionPerm i k) ?_
  calc
    (2 : R) • P.root (P.reflectionPerm i k)
        = (2 : R) • P.reflection i (P.root k) := by rw [root_reflectionPerm]
    _ = P.reflection i ((2 : R) • P.root k) := (map_smul (P.reflection i) _ _).symm
    _ = P.reflection i (P.root (P.reflectionPerm i j)) := by rw [hk]
    _ = P.root j := by rw [root_reflectionPerm, reflection_same]

/-- The **indivisible subsystem** of a root pairing `P`, obtained by restricting to the
indivisible root indices `{i | P.IsIndivisible i}`. -/
def indivisible (P : RootPairing ι R M N) :
    RootPairing {i : ι | P.IsIndivisible i} R M N :=
  P.restrict {i : ι | P.IsIndivisible i} fun _ _ _ hj ↦ hj.reflectionPerm

section IndivisibleSimp

variable (P : RootPairing ι R M N)

@[simp]
theorem indivisible_toLinearMap : P.indivisible.toLinearMap = P.toLinearMap := by
  rw [indivisible, restrict_toLinearMap]

@[simp]
theorem indivisible_root (i : {i : ι | P.IsIndivisible i}) :
    P.indivisible.root i = P.root i := by
  rw [indivisible, restrict_root]

@[simp]
theorem indivisible_coroot (i : {i : ι | P.IsIndivisible i}) :
    P.indivisible.coroot i = P.coroot i := by
  rw [indivisible, restrict_coroot]

@[simp]
theorem indivisible_root' (i : {i : ι | P.IsIndivisible i}) :
    P.indivisible.root' i = P.root' i := by
  rw [indivisible, restrict_root']

@[simp]
theorem indivisible_coroot' (i : {i : ι | P.IsIndivisible i}) :
    P.indivisible.coroot' i = P.coroot' i := by
  rw [indivisible, restrict_coroot']

@[simp]
theorem indivisible_pairing (i j : {i : ι | P.IsIndivisible i}) :
    P.indivisible.pairing i j = P.pairing i j := by
  rw [indivisible, restrict_pairing]

@[simp]
theorem indivisible_reflection (i : {i : ι | P.IsIndivisible i}) :
    P.indivisible.reflection i = P.reflection i := by
  rw [indivisible, restrict_reflection]

@[simp]
theorem indivisible_coreflection (i : {i : ι | P.IsIndivisible i}) :
    P.indivisible.coreflection i = P.coreflection i := by
  rw [indivisible, restrict_coreflection]

@[simp]
theorem indivisible_reflectionPerm_coe (i j : {i : ι | P.IsIndivisible i}) :
    (P.indivisible.reflectionPerm i j : ι) = P.reflectionPerm i j := by
  rw [indivisible, restrict_reflectionPerm_coe]

instance indivisible_isValuedIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] :
    P.indivisible.IsValuedIn S :=
  inferInstanceAs ((P.restrict _ _).IsValuedIn S)

end IndivisibleSimp

section SmulReflection

variable (P : RootPairing ι R M N) [Finite ι] [HasUniqueDiv N]

/-- If `P.root j = t • P.root i`, then the reflections at `j` and `i` coincide. -/
theorem reflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.reflection j = P.reflection i := by
  have hc : t • P.coroot j = P.coroot i := P.smul_coroot_eq_of_root_eq_smul i j t h
  ext x
  simp only [reflection_apply, coroot', ← hc, map_smul, LinearMap.smul_apply, smul_eq_mul, h]
  rw [smul_smul, mul_comm, ← smul_smul]

/-- If `P.root j = t • P.root i`, then the coreflections at `j` and `i` coincide. -/
theorem coreflection_eq_of_root_eq_smul {i j : ι} {t : R} (h : P.root j = t • P.root i) :
    P.coreflection j = P.coreflection i := by
  have hc : t • P.coroot j = P.coroot i := P.smul_coroot_eq_of_root_eq_smul i j t h
  ext y
  simp only [coreflection_apply, root', h, map_smul, LinearMap.smul_apply, smul_eq_mul, ← hc]
  rw [smul_smul, mul_comm, ← smul_smul]

end SmulReflection

section Crystallographic

variable (P : RootPairing ι R M N) [CharZero R] [P.IsCrystallographic]

/-- In a crystallographic root pairing over a characteristic-zero ring, no root is four times
another root. -/
theorem root_ne_four_smul (i j : ι) : P.root j ≠ (4 : R) • P.root i := by
  intro hj
  have hp : algebraMap ℤ R (4 * P.pairingIn ℤ i j) = algebraMap ℤ R 2 := by
    rw [map_mul, map_ofNat, algebraMap_pairingIn, pairing, root']
    calc
      (4 : R) * P.toLinearMap (P.root i) (P.coroot j)
          = P.toLinearMap ((4 : R) • P.root i) (P.coroot j) := by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      _ = P.toLinearMap (P.root j) (P.coroot j) := by rw [← hj]
      _ = 2 := P.root_coroot_two j
      _ = algebraMap ℤ R 2 := by norm_num
  have hint : 4 * P.pairingIn ℤ i j = 2 := Int.cast_injective hp
  omega

/-- Every root index of a crystallographic root pairing over a characteristic-zero ring is either
indivisible or has root equal to twice the root of an indivisible index. -/
theorem isIndivisible_or_exists_eq_two_smul (i : ι) :
    P.IsIndivisible i ∨ ∃ j : ι, P.IsIndivisible j ∧ P.root i = (2 : R) • P.root j := by
  by_cases hi : P.IsIndivisible i
  · exact Or.inl hi
  · simp only [IsIndivisible, not_forall, not_not] at hi
    obtain ⟨j, hj⟩ := hi
    refine Or.inr ⟨j, fun k hk ↦ ?_, hj.symm⟩
    exact P.root_ne_four_smul k i (by rw [← hj, ← hk, smul_smul]; norm_num)

/-- The indivisible roots span `M` whenever `P` is a crystallographic root system over a
characteristic-zero ring. -/
theorem span_root_indivisible_eq_top [P.IsRootSystem] :
    Submodule.span R (Set.range P.indivisible.root) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← IsRootSystem.span_root_eq_top (P := P), Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rcases P.isIndivisible_or_exists_eq_two_smul i with hi | ⟨j, hj, hij⟩
  · exact Submodule.subset_span ⟨⟨i, hi⟩, P.indivisible_root ⟨i, hi⟩⟩
  · rw [hij]
    exact Submodule.smul_mem _ 2 (Submodule.subset_span ⟨⟨j, hj⟩, P.indivisible_root ⟨j, hj⟩⟩)

section Finite

variable [Finite ι] [IsDomain R]

private theorem pairingIn_pairingIn_mem_of_coxeterWeightIn_eq_four {i j : ι}
    (hcw : P.coxeterWeightIn ℤ i j = 4) :
    (P.pairingIn ℤ i j, P.pairingIn ℤ j i) ∈
      ({(4, 1), (1, 4), (-4, -1), (-1, -4), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) := by
  have hset := P.pairingIn_pairingIn_mem_set_of_isCrystallographic i j
  rw [coxeterWeightIn] at hcw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hset ⊢
  aesop

/-- The indivisible subsystem of a finite crystallographic root pairing over a
characteristic-zero domain is reduced. -/
instance isReduced_indivisible : P.indivisible.IsReduced := by
  let _ : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  let _ : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  refine ⟨fun i j hdep ↦ ?_⟩
  have hdep' : ¬ LinearIndependent R ![P.root i.val, P.root j.val] := by
    simpa [indivisible_root] using hdep
  have hcw : P.coxeterWeightIn ℤ i.val j.val = 4 :=
    (P.coxeterWeightIn_eq_four_iff_not_linearIndependent ℤ).mpr hdep'
  have hmem := P.pairingIn_pairingIn_mem_of_coxeterWeightIn_eq_four hcw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with hij | hij | hij | hij | hij | hij
  · exact absurd ((P.pairingIn_one_four_iff ℤ j.val i.val).mp hij.symm).symm (i.property j.val)
  · exact absurd ((P.pairingIn_one_four_iff ℤ i.val j.val).mp hij).symm (j.property i.val)
  · have hneg := (P.pairingIn_neg_one_neg_four_iff ℤ j.val i.val).mp hij.symm
    refine absurd ?_ (i.property (P.reflectionPerm j.val j.val))
    rw [root_reflectionPerm, reflection_apply_self, smul_neg, ← neg_smul, ← hneg]
  · have hneg := (P.pairingIn_neg_one_neg_four_iff ℤ i.val j.val).mp hij
    refine absurd ?_ (j.property (P.reflectionPerm i.val i.val))
    rw [root_reflectionPerm, reflection_apply_self, smul_neg, ← neg_smul, ← hneg]
  · exact Or.inl (by simp [(P.pairingIn_two_two_iff ℤ i.val j.val).mp hij])
  · exact Or.inr (by simp [(P.pairingIn_neg_two_neg_two_iff ℤ i.val j.val).mp hij])

/-- The reflections of `P.indivisible` coincide with those of `P`. -/
@[simp]
theorem range_reflection_indivisible :
    Set.range P.indivisible.reflection = Set.range P.reflection := by
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv N := .of_isTorsionFree R N
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, (P.indivisible_reflection i).symm⟩
  · rintro ⟨i, rfl⟩
    rcases P.isIndivisible_or_exists_eq_two_smul i with hi | ⟨j, hj, hij⟩
    · exact ⟨⟨i, hi⟩, P.indivisible_reflection ⟨i, hi⟩⟩
    · exact ⟨⟨j, hj⟩, (P.indivisible_reflection ⟨j, hj⟩).trans
        (P.reflection_eq_of_root_eq_smul hij).symm⟩

/-- The coreflections of `P.indivisible` coincide with those of `P`. -/
@[simp]
theorem range_coreflection_indivisible :
    Set.range P.indivisible.coreflection = Set.range P.coreflection := by
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv N := .of_isTorsionFree R N
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, (P.indivisible_coreflection i).symm⟩
  · rintro ⟨i, rfl⟩
    rcases P.isIndivisible_or_exists_eq_two_smul i with hi | ⟨j, hj, hij⟩
    · exact ⟨⟨i, hi⟩, P.indivisible_coreflection ⟨i, hi⟩⟩
    · exact ⟨⟨j, hj⟩, (P.indivisible_coreflection ⟨j, hj⟩).trans
        (P.coreflection_eq_of_root_eq_smul hij).symm⟩

/-- Canonical isomorphism `P.weylGroup ≃* P.indivisible.weylGroup`, identifying the Weyl groups
via their common action on the weight space `M`. -/
noncomputable def weylGroupEquivIndivisible : P.weylGroup ≃* P.indivisible.weylGroup :=
  weylGroupEquivOfRangeReflectionEq P P.indivisible P.range_reflection_indivisible.symm

/-- `weylGroupEquivIndivisible` intertwines the Weyl-group actions on `M`. -/
@[simp]
theorem weylGroupEquivIndivisible_smul (w : P.weylGroup) (x : M) :
    P.weylGroupEquivIndivisible w • x = w • x :=
  weylGroupEquivOfRangeReflectionEq_smul P P.indivisible P.range_reflection_indivisible.symm w x

section IsRootSystem

variable [P.IsRootSystem]

/-- The indivisible coroots span `N` whenever `P` is a finite crystallographic root system over a
characteristic-zero domain in which `2` is a unit. -/
theorem span_coroot_indivisible_eq_top (h2 : IsUnit (2 : R)) :
    Submodule.span R (Set.range P.indivisible.coroot) = ⊤ := by
  have : Module.IsReflexive R N := .of_isPerfPair P.flip.toLinearMap
  have : HasUniqueDiv N := .of_isTorsionFree R N
  obtain ⟨u, hu⟩ := h2
  refine eq_top_iff.mpr ?_
  rw [← IsRootSystem.span_coroot_eq_top (P := P), Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rcases P.isIndivisible_or_exists_eq_two_smul i with hi | ⟨j, hj, hij⟩
  · exact Submodule.subset_span ⟨⟨i, hi⟩, P.indivisible_coroot ⟨i, hi⟩⟩
  · have hc : (u : R) • P.coroot i = P.coroot j := by
      rw [hu]
      exact P.smul_coroot_eq_of_root_eq_smul j i 2 hij
    have hinv : P.coroot i = (↑u⁻¹ : R) • P.coroot j := by
      rw [← hc, smul_smul, Units.inv_mul, one_smul]
    rw [hinv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, P.indivisible_coroot ⟨j, hj⟩⟩)

/-- When `2` is a unit, the indivisible subsystem of a finite crystallographic root system over a
characteristic-zero domain is a root system. -/
theorem isRootSystem_indivisible_of_isUnit_two (h2 : IsUnit (2 : R)) :
    P.indivisible.IsRootSystem where
  span_root_eq_top := P.span_root_indivisible_eq_top
  span_coroot_eq_top := P.span_coroot_indivisible_eq_top h2

end IsRootSystem

end Finite

end Crystallographic

/-- Over a characteristic-zero field, the indivisible subsystem of a finite crystallographic root
system is a root system. -/
instance isRootSystem_indivisible {K : Type*} [Field K] [CharZero K]
    [Module K M] [Module K N] (P : RootPairing ι K M N) [Finite ι]
    [P.IsCrystallographic] [P.IsRootSystem] :
    P.indivisible.IsRootSystem :=
  P.isRootSystem_indivisible_of_isUnit_two (Ne.isUnit two_ne_zero)

end Indivisible

end RootPairing
