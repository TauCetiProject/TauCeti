/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
import TauCeti.LinearAlgebra.RootSystem.Lowering
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit.Basic

/-!
# Raising a root by simple roots

Let `b` be a base of a finite crystallographic root pairing and order the roots by `α ≤ γ` when
`γ - α` lies in the positive root cone `Q⁺`. This file proves that the order on the positive roots
moves in steps of one simple root: below a strictly larger root `γ`, a positive root `α` can be
raised to a root `α + αₖ` that still lies below `γ`.

For a reduced irreducible root system this characterizes the highest root `θ` by a root-string test:
a positive root to which no simple root can be added is `θ`. So `θ` is greatest and not merely
maximal, which also reads as a statement about coefficients in the simple roots: those of `θ`
dominate those of every root, and `θ` is the unique maximum of every strictly positive weighting of
the coefficients.

When the Cartan matrix is simply laced the test can be run by reflections alone: all roots have the
same length, so `α + αₖ` is the reflection of `α` in `αₖ`, and every maximal sequence of simple
reflections raising the height by one ends at `θ`. Without the hypothesis, in `B₂` the positive root
`e₁` lies below the root `e₁ + e₂` but its simple reflections do not raise its height by one.

## Main definitions

* `RootPairing.Base.IsSimpleRaise`: the root `j` is the reflection of the root `i` in a simple root,
  and is higher by exactly one.

## Main results

* `RootPairing.exists_pos_and_pairingIn_lt_of_root_sub_root_eq_sum`: if a difference of two distinct
  roots is a natural combination of roots, some root occurring in it has a strictly larger Cartan
  integer with the larger root.
* `RootPairing.Base.exists_root_eq_add_root_and_sub_mem_posRootCone`: the raising step.
* `RootPairing.Base.eq_highestRoot_of_forall_root_add_notMem`: a positive root to which no simple
  root can be added is the highest root.
* `RootPairing.Base.toWeightBasisInt_repr_le_highestRoot` and
  `RootPairing.Base.sum_mul_toWeightBasisInt_repr_lt_highestRoot`: the highest root in the integral
  coordinates given by the simple roots.
* `RootPairing.InvariantForm.apply_root_root_eq_of_isSimplyLaced`: in a simply laced irreducible
  root system all roots have the same length.
* `RootPairing.Base.exists_isSimpleRaise`: in that case every positive root other than `θ` admits
  a simple reflection raising its height by one.
* `RootPairing.Base.getLast_eq_highestRoot_of_isChain`: every maximal sequence of such steps ends
  at `θ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1, nos. 3 and 8.
* J. S. Milne, *Algebraic Groups*, Cambridge University Press, 2017, Appendix C, C.24.
-/

public section

open Set

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

section HighestRoot

variable [Finite ι] [Nonempty ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]
  [P.IsIrreducible]

/-- **A positive root to which no simple root can be added is the highest root**: the highest root
is greatest among the roots, and not merely maximal. -/
theorem eq_highestRoot_of_forall_root_add_notMem {i : ι} (hi : b.IsPos i)
    (h : ∀ k ∈ b.support, P.root i + P.root k ∉ range P.root) : i = b.highestRoot := by
  by_contra hne
  obtain ⟨k, hk, m, hm, -⟩ := b.exists_root_eq_add_root_and_sub_mem_posRootCone hi hne
    (b.root_highestRoot_sub_mem_posRootCone i)
  exact h k hk ⟨m, hm⟩

/-- A positive root is the highest root exactly when no simple root can be added to it. -/
theorem eq_highestRoot_iff_forall_root_add_notMem {i : ι} (hi : b.IsPos i) :
    i = b.highestRoot ↔ ∀ k ∈ b.support, P.root i + P.root k ∉ range P.root :=
  ⟨fun h _ hk ↦ h ▸ b.root_highestRoot_add_root_notMem hk,
    b.eq_highestRoot_of_forall_root_add_notMem hi⟩

/-- **The coefficients of the highest root dominate those of every root**, in the integral basis of
the root lattice given by the simple roots. -/
theorem toWeightBasisInt_repr_le_highestRoot (j : ι) (k : b.support) :
    b.toWeightBasisInt.repr (P.rootSpanMem ℤ j) k ≤
      b.toWeightBasisInt.repr (P.rootSpanMem ℤ b.highestRoot) k := by
  classical
  obtain ⟨c, hc⟩ := (TauCeti.mem_posRootCone P b).mp (b.root_highestRoot_sub_mem_posRootCone j)
  have hx : P.rootSpanMem ℤ b.highestRoot - P.rootSpanMem ℤ j =
      ∑ l : b.support, c l • b.toWeightBasisInt l := Subtype.ext <| by
    simpa [← Finset.sum_coe_sort b.support] using hc
  have := congrArg (fun x ↦ b.toWeightBasisInt.repr x k) hx
  simp only [map_sub, Finsupp.sub_apply, map_sum, map_nsmul, Module.Basis.repr_self,
    Finsupp.finsetSum_apply, Finsupp.smul_apply] at this
  rw [← sub_nonneg, this]
  refine Finset.sum_nonneg fun _ _ ↦ nsmul_nonneg ?_ _
  rw [Finsupp.single_apply]
  split_ifs <;> simp

/-- **The highest root is the unique maximum of every strictly positive weighting** of the integral
coefficients in the simple roots. -/
theorem sum_mul_toWeightBasisInt_repr_lt_highestRoot {w : b.support → ℤ} (hw : ∀ k, 0 < w k) {j : ι}
    (hj : j ≠ b.highestRoot) :
    ∑ k, w k * b.toWeightBasisInt.repr (P.rootSpanMem ℤ j) k <
      ∑ k, w k * b.toWeightBasisInt.repr (P.rootSpanMem ℤ b.highestRoot) k := by
  have hle := b.toWeightBasisInt_repr_le_highestRoot j
  obtain ⟨k, hk⟩ : ∃ k, b.toWeightBasisInt.repr (P.rootSpanMem ℤ j) k ≠
      b.toWeightBasisInt.repr (P.rootSpanMem ℤ b.highestRoot) k := by
    by_contra! hall
    exact hj (P.root.injective (congrArg Subtype.val (b.toWeightBasisInt.ext_elem hall)))
  exact Finset.sum_lt_sum (fun l _ ↦ mul_le_mul_of_nonneg_left (hle l) (hw l).le)
    ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hle k) hk) (hw k)⟩

end HighestRoot

end Base

/-- **In a simply laced irreducible root system all roots have the same length** for every invariant
form. Irreducibility is needed: a system of type `A₁ × A₁` has invariant forms giving its two
components different lengths. -/
theorem InvariantForm.apply_root_root_eq_of_isSimplyLaced [CharZero R] [IsDomain R] [Finite ι]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible] (B : P.InvariantForm) (b : P.Base)
    (hsl : b.cartanMatrix.IsSimplyLaced) (i j : ι) :
    B.form (P.root i) (P.root i) = B.form (P.root j) (P.root j) := by
  have hsimple (l m : b.support) : B.form (P.root l) (P.root l) = B.form (P.root m) (P.root m) := by
    refine b.induction_on_cartanMatrix
      (fun k : b.support ↦ B.form (P.root l) (P.root l) = B.form (P.root k) (P.root k)) rfl ?_
    intro u v (huv : B.form (P.root l) (P.root l) = _) hne
    rcases eq_or_ne u v with rfl | hne'
    · exact huv
    have hvu : b.cartanMatrix v u = -1 := (hsl hne'.symm).resolve_left hne
    have huv' : b.cartanMatrix u v = -1 :=
      (hsl hne').resolve_left (b.cartanMatrix_apply_eq_zero_iff_symm.not.mp hne)
    have hp (x y : b.support) (hxy : b.cartanMatrix x y = -1) : P.pairing x y = -1 := by
      have : P.pairingIn ℤ x y = -1 := by
        simpa [Base.cartanMatrix, Base.cartanMatrixIn_def] using hxy
      rw [← P.algebraMap_pairingIn ℤ, this]
      simp
    have := B.pairing_mul_eq_pairing_mul_swap (u : ι) v
    rw [hp v u hvu, hp u v huv'] at this
    rw [huv]
    linear_combination -this
  have : Nonempty ι := ⟨i⟩
  obtain ⟨l⟩ : Nonempty b.support := b.support_nonempty.to_subtype
  have hall (x : ι) : B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l) := by
    refine b.induction_simple_reflect x
      (p := fun x ↦ B.form (P.root x) (P.root x) = B.form (P.root l) (P.root l))
      (fun k hk ↦ hsimple ⟨k, hk⟩ l) fun k r hk _ ↦ ?_
    rw [← hk, root_reflectionPerm, B.apply_reflection_reflection]
  rw [hall i, hall j]

namespace Base

variable [CharZero R] (b : P.Base)

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

/-- The highest root admits no simple raising step. -/
theorem not_isSimpleRaise_highestRoot [Finite ι] [Nonempty ι] (j : ι) :
    ¬ b.IsSimpleRaise b.highestRoot j := fun h ↦ by
  have := b.height_le_height_highestRoot j
  rw [h.height_eq] at this
  omega

variable [P.IsCrystallographic]

/-- A simple raising step is a reflection in a simple root with Cartan integer `-1`. -/
theorem isSimpleRaise_iff {i j : ι} :
    b.IsSimpleRaise i j ↔ ∃ k ∈ b.support, P.reflectionPerm k i = j ∧ P.pairingIn ℤ i k = -1 := by
  refine exists_congr fun k ↦ and_congr_right fun hk ↦ and_congr_right fun hj ↦ ?_
  rw [← hj, TauCeti.height_reflectionPerm_of_mem_support P b hk]
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

section SimplyLaced

variable [Finite ι] [IsDomain R] [P.IsReduced] [P.IsIrreducible]

/-- **In a simply laced irreducible root system, two roots whose sum is a root have Cartan integer
`-1`.** -/
theorem pairingIn_eq_neg_one_of_isSimplyLaced (hsl : b.cartanMatrix.IsSimplyLaced) {i k m : ι}
    (hm : P.root m = P.root i + P.root k) : P.pairingIn ℤ i k = -1 := by
  have := Fintype.ofFinite ι
  let B := P.toInvariantForm
  have hlen (x y : ι) := B.apply_root_root_eq_of_isSimplyLaced b hsl x y
  have hsymm := B.symm.eq (P.root k) (P.root i)
  have htwo := B.two_mul_apply_root_root i k
  have hexp : B.form (P.root m) (P.root m) = B.form (P.root i) (P.root i) +
      2 * B.form (P.root i) (P.root k) + B.form (P.root k) (P.root k) := by
    rw [hm]
    simp only [map_add, LinearMap.add_apply]
    simp only [RingHom.id_apply] at hsymm
    rw [hsymm]
    ring
  rw [htwo, hlen m k, hlen i k] at hexp
  have hz : (P.pairing i k + 1) * B.form (P.root k) (P.root k) = 0 := by
    linear_combination -hexp
  have hp : P.pairing i k = -1 := by
    have := (mul_eq_zero.mp hz).resolve_right (B.ne_zero k)
    linear_combination this
  apply FaithfulSMul.algebraMap_injective ℤ R
  rw [algebraMap_pairingIn, hp, map_neg, map_one]

variable [Nonempty ι]

/-- **In a simply laced irreducible root system, every positive root other than the highest root
admits a simple reflection raising its height by exactly one.** -/
theorem exists_isSimpleRaise (hsl : b.cartanMatrix.IsSimplyLaced) {i : ι} (hi : b.IsPos i)
    (hne : i ≠ b.highestRoot) : ∃ j, b.IsSimpleRaise i j := by
  by_contra! h
  refine hne (b.eq_highestRoot_of_forall_root_add_notMem hi fun k hk ⟨m, hm⟩ ↦ ?_)
  exact h _ (b.isSimpleRaise_iff.mpr
    ⟨k, hk, rfl, b.pairingIn_eq_neg_one_of_isSimplyLaced hsl hm⟩)

/-- **In a simply laced irreducible root system, the highest root is the only positive root without
a simple raising step.** -/
theorem eq_highestRoot_iff_forall_not_isSimpleRaise (hsl : b.cartanMatrix.IsSimplyLaced) {i : ι}
    (hi : b.IsPos i) : i = b.highestRoot ↔ ∀ j, ¬ b.IsSimpleRaise i j :=
  ⟨fun h ↦ h ▸ b.not_isSimpleRaise_highestRoot, fun h ↦ by
    by_contra hne
    obtain ⟨j, hj⟩ := b.exists_isSimpleRaise hsl hi hne
    exact h j hj⟩

/-- **In a simply laced irreducible root system, simple raising steps lead every positive root to
the highest root.** -/
theorem reflTransGen_isSimpleRaise_highestRoot (hsl : b.cartanMatrix.IsSimplyLaced) {i : ι}
    (hi : b.IsPos i) : Relation.ReflTransGen b.IsSimpleRaise i b.highestRoot := by
  induction hn : (b.height b.highestRoot - b.height i).toNat using Nat.strong_induction_on
    generalizing i with
  | _ n ih =>
  rcases eq_or_ne i b.highestRoot with rfl | hne
  · exact .refl
  obtain ⟨j, hj⟩ := b.exists_isSimpleRaise hsl hi hne
  have hle := b.height_le_height_highestRoot j
  have hlt : (b.height b.highestRoot - b.height j).toNat < n := by
    rw [hj.height_eq] at hle ⊢
    omega
  exact .head hj (ih _ hlt (hj.isPos hi) rfl)

/-- **In a simply laced irreducible root system, every maximal sequence of simple raising steps
ends at the highest root.** Such a sequence starts at a positive root and has no further step from
its last root. -/
theorem getLast_eq_highestRoot_of_isChain (hsl : b.cartanMatrix.IsSimplyLaced) {l : List ι}
    (hl : l ≠ []) (hchain : l.IsChain b.IsSimpleRaise) (hhead : b.IsPos (l.head hl))
    (hmax : ∀ j, ¬ b.IsSimpleRaise (l.getLast hl) j) : l.getLast hl = b.highestRoot := by
  refine (b.eq_highestRoot_iff_forall_not_isSimpleRaise hsl ?_).mpr hmax
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    cases l with
    | nil => simpa using hhead
    | cons c l =>
      rw [List.isChain_cons_cons] at hchain
      simpa using ih (by simp) hchain.2 (hchain.1.isPos (by simpa using hhead))
        (by simpa using hmax)

end SimplyLaced

end Base

end RootPairing
