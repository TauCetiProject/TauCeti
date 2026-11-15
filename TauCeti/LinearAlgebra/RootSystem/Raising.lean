/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Raising a root by simple roots

Let `b` be a base of a finite crystallographic root pairing and order the roots by `α ≤ γ` when
`γ - α` lies in the positive root cone `Q⁺`. This file proves that the order on the positive roots
moves in steps of one simple root: below a strictly larger root `γ`, a positive root `α` can be
raised to a root `α + αₖ` that still lies below `γ`. It also introduces simple raising steps, the
reflections in simple roots which raise the height by exactly one.

## Main definitions

* `RootPairing.Base.IsSimpleRaise`: the root `j` is the reflection of the root `i` in a simple root,
  and is higher by exactly one.

## Main results

* `RootPairing.exists_pos_and_pairingIn_lt_of_root_sub_root_eq_sum`: if a difference of two distinct
  roots is a natural combination of roots, some root occurring in it has a strictly larger Cartan
  integer with the larger root.
* `RootPairing.Base.exists_root_eq_add_root_and_sub_mem_posRootCone`: the raising step.
* `RootPairing.Base.isSimpleRaise_iff`: a simple raising step is a reflection in a simple root with
  Cartan integer `-1`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, no. 3.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N}

/-- **A root occurring in the difference of two roots pairs more with the larger root.** If a
difference `αⱼ - αᵢ` of two distinct roots is a natural combination of roots, some root occurring
in it with a positive coefficient has a strictly larger Cartan integer with `αⱼ` than with `αᵢ`. -/
theorem exists_pos_and_pairingIn_lt_of_root_sub_root_eq_sum [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] {κ : Type*} {s : Finset κ} {f : κ → ι} {c : κ → ℕ} {i j : ι}
    (hij : i ≠ j) (h : P.root j - P.root i = ∑ k ∈ s, c k • P.root (f k)) :
    ∃ k ∈ s, 0 < c k ∧ P.pairingIn ℤ i (f k) < P.pairingIn ℤ j (f k) := by
  have := Fintype.ofFinite ι
  by_contra! hle
  set B := P.posRootForm ℤ
  -- The form on the root lattice, on the pairs of a lattice vector and a root.
  have hform (x : ι) (k : ι) : 2 * B.posForm (P.rootSpanMem ℤ x) (P.rootSpanMem ℤ k) =
      P.pairingIn ℤ x k * B.rootLength k := by
    apply FaithfulSMul.algebraMap_injective ℤ R
    simp only [map_mul, map_ofNat, RootPositiveForm.algebraMap_posForm, algebraMap_pairingIn,
      RootPositiveForm.algebraMap_rootLength]
    exact B.two_mul_apply_root_root x k
  set v : P.rootSpan ℤ := P.rootSpanMem ℤ j - P.rootSpanMem ℤ i with hv
  have hv₀ : v ≠ 0 := fun h₀ ↦ hij (P.root.injective
    (sub_eq_zero.mp (congrArg Subtype.val h₀)).symm)
  have hsum : v = ∑ k ∈ s, c k • P.rootSpanMem ℤ (f k) := Subtype.ext <| by simpa [hv] using h
  have hexp : 2 * B.posForm v v =
      ∑ k ∈ s, (c k : ℤ) * ((P.pairingIn ℤ j (f k) - P.pairingIn ℤ i (f k)) *
        B.rootLength (f k)) := by
    calc 2 * B.posForm v v = 2 * B.posForm v (∑ k ∈ s, c k • P.rootSpanMem ℤ (f k)) := by
          rw [← hsum]
      _ = _ := by
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [map_nsmul, nsmul_eq_mul, sub_mul, ← hform, ← hform, hv]
          simp only [map_sub, LinearMap.sub_apply]
          ring
  have hpos := P.posRootForm_posForm_pos_of_ne_zero ℤ hv₀
  refine absurd hexp (ne_of_gt (lt_of_le_of_lt (Finset.sum_nonpos fun k hk ↦ ?_)
    (mul_pos two_pos hpos)))
  rcases (c k).eq_zero_or_pos with hk₀ | hk₀
  · simp [hk₀]
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hle k hk hk₀)) (B.rootLength_pos _).le)

namespace Base

variable [CharZero R] (b : P.Base)

/-- Removing a simple root which occurs in a natural combination of the simple roots stays in the
positive root cone. -/
theorem sum_nsmul_root_sub_root_mem_posRootCone {c : ι → ℕ} {k : ι}
    (hk : k ∈ b.support) (hck : 0 < c k) :
    ∑ l ∈ b.support, c l • P.root l - P.root k ∈ TauCeti.posRootCone P b := by
  classical
  have hsimple (l : ι) (hl : l ∈ b.support) : P.root l ∈ TauCeti.posRootCone P b :=
    TauCeti.root_mem_posRootCone_of_mem_posRoots P b
      ((TauCeti.mem_posRoots P b l).mpr (b.isPos_of_mem_support hl))
  have heq : ∑ l ∈ b.support, c l • P.root l - P.root k = (c k - 1) • P.root k +
      ∑ l ∈ b.support.erase k, c l • P.root l := by
    rw [← Finset.add_sum_erase _ _ hk]
    nth_rw 1 [show c k = (c k - 1) + 1 by omega]
    rw [add_smul, one_smul]
    abel
  rw [heq]
  exact add_mem (nsmul_mem (hsimple k hk) _)
    (sum_mem fun l hl ↦ nsmul_mem (hsimple l (Finset.mem_of_mem_erase hl)) _)

section Raising

variable [Finite ι] [IsDomain R] [P.IsCrystallographic]

/-- **A positive root can be raised by a simple root towards any larger root**: if `αᵢ` is positive
and `αⱼ - αᵢ` is a nonzero element of the positive root cone, there is a simple root `αₖ` such that
`αᵢ + αₖ` is a root and `αⱼ - (αᵢ + αₖ)` still lies in the positive root cone. Positivity of `αᵢ`
is needed: in `A₁`, `α - (-α)` is in the cone, but `-α + α` is not a root. -/
theorem exists_root_eq_add_root_and_sub_mem_posRootCone {i j : ι} (hi : b.IsPos i) (hij : i ≠ j)
    (h : P.root j - P.root i ∈ TauCeti.posRootCone P b) :
    ∃ k ∈ b.support, ∃ m, P.root m = P.root i + P.root k ∧
      P.root j - P.root m ∈ TauCeti.posRootCone P b := by
  classical
  have hi' := TauCeti.root_mem_posRootCone_of_mem_posRoots P b ((TauCeti.mem_posRoots P b i).mpr hi)
  induction hn : (b.height j).toNat using Nat.strong_induction_on generalizing j with
  | _ n ih =>
  obtain ⟨c, hc⟩ := (TauCeti.mem_posRootCone P b).mp h
  obtain ⟨k, hk, hck, hlt⟩ := exists_pos_and_pairingIn_lt_of_root_sub_root_eq_sum hij hc
  have hsub : P.root j - P.root i - P.root k ∈ TauCeti.posRootCone P b :=
    hc ▸ b.sum_nsmul_root_sub_root_mem_posRootCone hk hck
  by_cases hik : P.pairingIn ℤ i k < 0
  · -- `αₖ` pairs negatively with `αᵢ`, so it can be added to `αᵢ` directly
    have hne : P.root i ≠ -P.root k := fun heq ↦ by
      have hik' : i = P.reflectionPerm k k := P.root.injective (by simp [heq])
      exact TauCeti.reflectionPerm_self_notMem_posRoots P b
        ((TauCeti.mem_posRoots P b k).mpr (b.isPos_of_mem_support hk))
        ((TauCeti.mem_posRoots P b _).mpr (hik' ▸ hi))
    obtain ⟨m, hm⟩ := P.root_add_root_mem_of_pairingIn_neg hik hne
    exact ⟨k, hk, m, hm, by rwa [hm, ← sub_sub]⟩
  -- otherwise `αₖ` pairs positively with `αⱼ`, which can be lowered by `αₖ` and stays above `αᵢ`
  have hjk : 0 < P.pairingIn ℤ j k := by omega
  have hjne : j ≠ k := by
    rintro rfl
    refine P.ne_zero i (TauCeti.eq_zero_of_add_eq_zero_of_mem_posRootCone P b hi' hsub ?_)
    abel
  obtain ⟨j', hj'⟩ := P.root_sub_root_mem_of_pairingIn_pos hjk hjne
  by_cases hij' : i = j'
  · subst hij'
    refine ⟨k, hk, j, by rw [hj']; abel, by simp⟩
  have hj'i : P.root j' - P.root i ∈ TauCeti.posRootCone P b := by
    rw [hj']
    convert hsub using 1
    abel
  have hjpos : b.IsPos j := by
    refine (TauCeti.mem_posRoots P b j).mp
      ((TauCeti.mem_posRoots_iff_root_mem_posRootCone P b).mpr ?_)
    simpa using add_mem h hi'
  have hheight : b.height j' = b.height j - 1 := by
    rw [b.height_sub hj', height_one_of_mem_support hk]
  have hlt' : (b.height j').toNat < n := by
    have := b.isPos_iff.mp hjpos
    omega
  obtain ⟨l, hl, m, hm, hmj⟩ := ih _ hlt' hij' hj'i rfl
  refine ⟨l, hl, m, hm, ?_⟩
  have heq : P.root j - P.root m = P.root j' - P.root m + P.root k := by
    rw [hj']
    abel
  rw [heq]
  exact add_mem hmj (TauCeti.root_mem_posRootCone_of_mem_posRoots P b
    ((TauCeti.mem_posRoots P b k).mpr (b.isPos_of_mem_support hk)))

end Raising

/-- `b.IsSimpleRaise i j` says that the root `j` is the reflection of the root `i` in a simple root
and is higher than `i` by exactly one. -/
def IsSimpleRaise (i j : ι) : Prop :=
  ∃ k ∈ b.support, P.reflectionPerm k i = j ∧ b.height j = b.height i + 1

theorem isSimpleRaise_def {i j : ι} : b.IsSimpleRaise i j ↔
    ∃ k ∈ b.support, P.reflectionPerm k i = j ∧ b.height j = b.height i + 1 :=
  Iff.rfl

variable {b} in
/-- A simple raising step adds one to the height. -/
theorem IsSimpleRaise.height_eq {i j : ι} (h : b.IsSimpleRaise i j) :
    b.height j = b.height i + 1 := by
  obtain ⟨_, _, _, h⟩ := h
  exact h

variable {b} in
/-- A simple raising step from a positive root reaches a positive root. -/
theorem IsSimpleRaise.isPos {i j : ι} (h : b.IsSimpleRaise i j) (hi : b.IsPos i) : b.IsPos j := by
  have := b.isPos_iff.mp hi
  exact b.isPos_iff.mpr (by rw [h.height_eq]; omega)

variable [P.IsCrystallographic]

/-- A simple raising step is a reflection in a simple root with Cartan integer `-1`. -/
theorem isSimpleRaise_iff {i j : ι} :
    b.IsSimpleRaise i j ↔ ∃ k ∈ b.support, P.reflectionPerm k i = j ∧ P.pairingIn ℤ i k = -1 := by
  refine exists_congr fun k ↦ and_congr_right fun hk ↦ and_congr_right fun hj ↦ ?_
  rw [← hj, b.height_reflectionPerm_of_mem_support hk]
  omega

variable {b} in
/-- A simple raising step adds the simple root it reflects in. -/
theorem IsSimpleRaise.exists_root_eq_add {i j : ι} (h : b.IsSimpleRaise i j) :
    ∃ k ∈ b.support, P.root j = P.root i + P.root k := by
  obtain ⟨k, hk, rfl, hp⟩ := b.isSimpleRaise_iff.mp h
  refine ⟨k, hk, ?_⟩
  have := P.reflection_apply_root' ℤ (i := k) (j := i)
  rw [hp] at this
  simpa [sub_eq_add_neg] using this

end Base

end RootPairing
