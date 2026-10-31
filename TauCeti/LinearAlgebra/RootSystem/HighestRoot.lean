/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.RootPositive
public import TauCeti.LinearAlgebra.RootSystem.Positive
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import TauCeti.LinearAlgebra.RootSystem.Lowering
import TauCeti.LinearAlgebra.RootSystem.Weyl.Orbit

/-!
# The highest root of an irreducible root system

Let `b` be a base of a finite, reduced, irreducible, crystallographic root system `P`. Order the
weights by `μ ≤ λ` when `λ - μ` lies in the positive root cone `Q⁺` of nonnegative integer
combinations of the simple roots. This file proves that the roots have a greatest element `θ` for
this order, the **highest root**, and records its standard properties:

* every coefficient of `θ` in the simple roots is positive;
* `θ` is dominant: it pairs nonnegatively with every simple coroot;
* `θ` is long: no root is longer than `θ` for any root-positive form.

The highest root is the extra datum an affine root system adds to a finite one: the affine
function `1 - θ` is the last wall of the fundamental alcove and the coefficients of `θ` are the
marks of the affine Dynkin diagram.

The definition `RootPairing.Base.highestRoot` picks a root of maximal height, which makes sense
for any finite root pairing with a base; the theorems identify it as the greatest root once the
root system is reduced and irreducible, and in particular show it does not depend on the choice.

## Main definitions

* `RootPairing.Base.highestRoot`: a root of maximal height relative to `b`; for a reduced
  irreducible root system, the highest root.

## Main results

* `RootPairing.Base.root_highestRoot_sub_mem_posRootCone`: **every root lies below the highest
  root**, `θ - α ∈ Q⁺`.
* `RootPairing.Base.forall_root_sub_mem_posRootCone_iff`: the highest root is the only root
  lying above every root.
* `RootPairing.Base.height_lt_height_highestRoot`: every other root has strictly smaller height.
* `RootPairing.Base.exists_root_highestRoot_eq_sum_nat`: the coefficients of the highest root in
  the simple roots are all positive.
* `RootPairing.Base.pairingIn_highestRoot_nonneg`: the highest root is dominant.
* `RootPairing.Base.rootLength_le_rootLength_highestRoot`: the highest root is long.
* `RootPairing.Base.pairingIn_highestRoot_right_nonneg`: a positive root pairs nonnegatively with
  the coroot `θ^∨`.
* `RootPairing.Base.pairingIn_highestRoot_right_mem`: a root other than `±θ` pairs with `θ^∨` to
  `-1`, `0` or `1`.
* `RootPairing.root'_le_root'_highestRoot`: at a point of the coweight space where every simple
  root is nonnegative, the highest root takes the largest value of all roots.

Two general facts about a positive root `α` to which no simple root can be added lie behind
these: such a root is dominant
(`RootPairing.Base.pairingIn_nonneg_of_forall_root_add_root_notMem`), and in an irreducible system
all its coefficients are positive
(`RootPairing.Base.exists_root_eq_sum_nat_of_forall_root_add_root_notMem`). Both rest on
`RootPairing.pairingIn_eq_sum_of_root_eq_sum`, which reads the Cartan integers of an integral
combination of roots off those of its summands.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §10.4:
  Lemma A (the maximal root) and the lemma there that the maximal root is long. The proof of
  length maximality below replaces Humphreys' Weyl conjugation to a dominant root by the choice of
  a longest root of greatest height.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §1.8.
-/

public section

open Set

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [CharZero R] (b : P.Base)

section HighestRoot

variable [Finite ι] [Nonempty ι]

/-- A root of maximal height relative to the base `b`. When the root system is reduced and
irreducible this is the **highest root**: the unique root `θ` with `θ - α` a nonnegative integer
combination of the simple roots for every root `α`
(`RootPairing.Base.forall_root_sub_mem_posRootCone_iff`). -/
noncomputable def highestRoot : ι :=
  (Finite.exists_max b.height).choose

/-- No root is higher than `RootPairing.Base.highestRoot`. -/
theorem height_le_height_highestRoot (j : ι) : b.height j ≤ b.height b.highestRoot :=
  (Finite.exists_max b.height).choose_spec j

/-- `RootPairing.Base.highestRoot` is a positive root. -/
theorem isPos_highestRoot : b.IsPos b.highestRoot := by
  let := P.indexNeg
  have h := b.height_le_height_highestRoot (-b.highestRoot)
  rw [height_reflectionPerm_self] at h
  exact b.isPos_iff'.mpr (by omega)

/-- A positive root is not the negative of the highest root. -/
private theorem root_ne_neg_root_highestRoot {j : ι} (hj : b.IsPos j) :
    P.root j ≠ -P.root b.highestRoot := fun h ↦ by
  have hj' : j = P.reflectionPerm b.highestRoot b.highestRoot :=
    P.root.injective (by rw [h, root_reflectionPerm, reflection_apply_self])
  have h := (TauCeti.isPos_reflectionPerm_self_iff_mem_negRoots P b b.highestRoot).mp (hj' ▸ hj)
  exact (TauCeti.mem_negRoots P b _).mp h b.isPos_highestRoot

/-- No simple root can be added to `RootPairing.Base.highestRoot`: the sum would be a higher
root. -/
theorem root_highestRoot_add_root_notMem {k : ι} (hk : k ∈ b.support) :
    P.root b.highestRoot + P.root k ∉ range P.root := by
  rintro ⟨m, hm⟩
  have h := b.height_le_height_highestRoot m
  rw [b.height_add hm, height_one_of_mem_support hk] at h
  omega

end HighestRoot

variable [P.IsCrystallographic] [Finite ι] [IsDomain R]

/-- **A positive root to which no simple root can be added is dominant**: it pairs nonnegatively
with every simple coroot. -/
theorem pairingIn_nonneg_of_forall_root_add_root_notMem {i : ι} (hi : b.IsPos i)
    (h : ∀ k ∈ b.support, P.root i + P.root k ∉ range P.root) {k : ι} (hk : k ∈ b.support) :
    0 ≤ P.pairingIn ℤ i k := by
  -- a negative pairing with `αₖ^∨` would make `α + αₖ` a root, unless `α = -αₖ` is negative
  by_contra! hneg
  refine h k hk (P.root_add_root_mem_of_pairingIn_neg hneg fun heq ↦ ?_)
  have hik : i = P.reflectionPerm k k := P.root.injective (by simp [heq])
  exact TauCeti.reflectionPerm_self_notMem_posRoots P b
    ((TauCeti.mem_posRoots P b k).mpr (b.isPos_of_mem_support hk))
    ((TauCeti.mem_posRoots P b _).mpr (hik ▸ hi))

/-- **In an irreducible root system, a positive root to which no simple root can be added has
every coefficient positive**: it is a combination of the simple roots with positive natural
coefficients. -/
theorem exists_root_eq_sum_nat_of_forall_root_add_root_notMem [P.IsReduced] [P.IsIrreducible]
    {i : ι} (hi : b.IsPos i) (h : ∀ k ∈ b.support, P.root i + P.root k ∉ range P.root) :
    ∃ f : ι → ℕ, (∀ k ∈ b.support, 0 < f k) ∧ P.root i = ∑ k ∈ b.support, f k • P.root k := by
  classical
  obtain ⟨f, -, hf⟩ :=
    TauCeti.exists_root_eq_sum_nat_of_mem_posRoots P b ((TauCeti.mem_posRoots P b _).mpr hi)
  refine ⟨f, fun k hk ↦ ?_, hf⟩
  obtain ⟨k₀, hk₀, hpos⟩ : ∃ k₀ ∈ b.support, 0 < f k₀ := by
    by_contra! H
    exact P.ne_zero i <| hf.trans <| Finset.sum_eq_zero fun k hk ↦ by
      rw [Nat.le_zero.mp (H k hk), zero_smul]
  have hfz : P.root i = ∑ k ∈ b.support, (f k : ℤ) • P.root k := by simpa using hf
  -- Positivity spreads along the edges of the Dynkin diagram, which is connected: if the
  -- coefficient of `αₘ` vanished while that of a neighbour `αₗ` did not, the root would pair
  -- negatively with `αₘ^∨`, against `pairingIn_nonneg_of_forall_root_add_root_notMem`.
  refine b.induction_on_cartanMatrix (fun k : b.support ↦ 0 < f k) (i := ⟨k₀, hk₀⟩)
    (j := ⟨k, hk⟩) hpos ?_
  rintro ⟨l, hl⟩ ⟨m, hm⟩ (hfl : 0 < f l) hlm
  by_contra! hfm
  replace hfm : f m = 0 := by simpa using hfm
  have hlm' : l ≠ m := by rintro rfl; omega
  -- `αₗ` and `αₘ` are joined in the Dynkin diagram, so their Cartan integer is negative.
  have hneg : P.pairingIn ℤ l m < 0 := by
    have hne : P.pairingIn ℤ l m ≠ 0 := by
      simpa [cartanMatrix, cartanMatrixIn_def] using
        (b.cartanMatrix_apply_eq_zero_iff_symm (i := ⟨m, hm⟩) (j := ⟨l, hl⟩)).not.mp hlm
    exact lt_of_le_of_ne (b.pairingIn_le_zero_of_ne hlm' hl hm) hne
  have hsum : P.pairingIn ℤ i m < 0 := by
    rw [pairingIn_eq_sum_of_root_eq_sum hfz, ← Finset.add_sum_erase _ _ hl]
    refine add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg (by exact_mod_cast hfl) hneg)
      (Finset.sum_nonpos fun k hk ↦ ?_)
    obtain ⟨-, hk⟩ := Finset.mem_erase.mp hk
    rcases eq_or_ne k m with rfl | hkm
    · simp [hfm]
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (b.pairingIn_le_zero_of_ne hkm hk hm)
  exact (pairingIn_nonneg_of_forall_root_add_root_notMem b hi h hm).not_gt hsum

variable [Nonempty ι]

/-- **The highest root is dominant**: it pairs nonnegatively with every simple coroot. -/
theorem pairingIn_highestRoot_nonneg {k : ι} (hk : k ∈ b.support) :
    0 ≤ P.pairingIn ℤ b.highestRoot k :=
  b.pairingIn_nonneg_of_forall_root_add_root_notMem b.isPos_highestRoot
    (fun _ ↦ b.root_highestRoot_add_root_notMem) hk

/-- **A positive root pairs nonnegatively with the coroot of the highest root**,
`0 ≤ ⟨α, θ^∨⟩`: if the pairing were negative, `α + θ` would be a root higher than `θ`. -/
theorem pairingIn_highestRoot_right_nonneg {j : ι} (hj : b.IsPos j) :
    0 ≤ P.pairingIn ℤ j b.highestRoot := by
  by_contra! hneg
  obtain ⟨k, hk⟩ := P.root_add_root_mem_of_pairingIn_neg hneg (b.root_ne_neg_root_highestRoot hj)
  have h := b.height_le_height_highestRoot k
  rw [b.height_add hk] at h
  rw [isPos_iff] at hj
  omega

variable [P.IsReduced] [P.IsIrreducible]

/-- **The coefficients of the highest root in the simple roots are all positive.** -/
theorem exists_root_highestRoot_eq_sum_nat :
    ∃ f : ι → ℕ, (∀ k ∈ b.support, 0 < f k) ∧
      P.root b.highestRoot = ∑ k ∈ b.support, f k • P.root k :=
  b.exists_root_eq_sum_nat_of_forall_root_add_root_notMem b.isPos_highestRoot
    fun _ ↦ b.root_highestRoot_add_root_notMem

/-- The step of `RootPairing.Base.root_highestRoot_sub_mem_posRootCone` for a positive root to
which no simple root can be added. -/
private lemma root_highestRoot_sub_mem_posRootCone_of_forall_root_add_root_notMem {j : ι}
    (hj : b.IsPos j) (h : ∀ k ∈ b.support, P.root j + P.root k ∉ range P.root) :
    P.root b.highestRoot - P.root j ∈ TauCeti.posRootCone P b := by
  -- The coefficients of `αⱼ` are all positive and `θ` is dominant and not orthogonal to every
  -- simple root, so `αⱼ` and `θ` pair positively, and `θ - αⱼ` is a root of nonnegative height.
  classical
  set θ := b.highestRoot
  rcases eq_or_ne θ j with rfl | hθj
  · simp
  obtain ⟨d, hd, hdj⟩ := b.exists_root_eq_sum_nat_of_forall_root_add_root_notMem hj h
  obtain ⟨k₀, hk₀, hpos⟩ := b.isPos_highestRoot.exists_mem_support_pos_pairingIn
  -- the simple roots pair nonnegatively with `θ^∨`, and `αₖ₀` strictly so
  have hnonneg : ∀ k ∈ b.support, 0 ≤ P.pairingIn ℤ k θ := fun k hk ↦ by
    simpa using (P.pairingIn_lt_zero_iff ℤ (i := k) (j := θ)).not.mpr
      (b.pairingIn_highestRoot_nonneg hk).not_gt
  have hjθ : 0 < P.pairingIn ℤ j θ := by
    rw [pairingIn_eq_sum_of_root_eq_sum (f := fun k ↦ (d k : ℤ)) (by simpa using hdj),
      ← Finset.add_sum_erase _ _ hk₀]
    exact add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hd k₀ hk₀) hpos)
      (Finset.sum_nonneg fun k hk ↦
        mul_nonneg (by positivity) (hnonneg k (Finset.mem_of_mem_erase hk)))
  obtain ⟨m, hm⟩ := P.root_sub_root_mem_of_pairingIn_pos
    ((P.zero_lt_pairingIn_iff' ℤ).mp hjθ) hθj
  rw [← hm]
  refine TauCeti.root_mem_posRootCone_of_mem_posRoots P b
    ((TauCeti.mem_posRoots P b _).mpr (b.isPos_iff'.mpr ?_))
  rw [b.height_sub hm]
  linarith [b.height_le_height_highestRoot j, b.height_le_height_highestRoot m]

/-- **Every root lies below the highest root**: for every root `α`, `θ - α` is a nonnegative
integer combination of the simple roots. -/
theorem root_highestRoot_sub_mem_posRootCone (j : ι) :
    P.root b.highestRoot - P.root j ∈ TauCeti.posRootCone P b := by
  set θ := b.highestRoot
  have hθ := (TauCeti.mem_posRoots P b _).mpr b.isPos_highestRoot
  rcases IsPos.or_neg b j with hj | hj
  swap
  · -- a negative root: `θ - α = θ + (-α)` is a sum of two positive roots
    let := P.indexNeg
    rw [sub_eq_add_neg, show -P.root j = P.root (-j) by simp]
    exact add_mem (TauCeti.root_mem_posRootCone_of_mem_posRoots P b hθ)
      (TauCeti.root_mem_posRootCone_of_mem_posRoots P b ((TauCeti.mem_posRoots P b _).mpr hj))
  -- a positive root: climb by simple roots, by induction on the height gap to `θ`
  suffices H : ∀ n : ℕ, ∀ j, b.IsPos j → b.height θ - b.height j = n →
      P.root θ - P.root j ∈ TauCeti.posRootCone P b from
    H _ j hj (Int.toNat_of_nonneg (sub_nonneg.mpr (b.height_le_height_highestRoot j))).symm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hj hn
  by_cases hadd : ∃ k ∈ b.support, P.root j + P.root k ∈ range P.root
  swap
  · exact b.root_highestRoot_sub_mem_posRootCone_of_forall_root_add_root_notMem hj
      fun k hk hmem ↦ hadd ⟨k, hk, hmem⟩
  obtain ⟨k, hk, m, hm⟩ := hadd
  have hmj : b.height m = b.height j + 1 := by
    rw [b.height_add hm, height_one_of_mem_support hk]
  have hgap : b.height θ - b.height m = ((b.height θ - b.height m).toNat : ℤ) :=
    (Int.toNat_of_nonneg (sub_nonneg.mpr (b.height_le_height_highestRoot m))).symm
  have hmθ := ih _ (by omega) m
    (hj.add (b.isPos_of_mem_support hk) hm) hgap
  have : P.root θ - P.root j = (P.root θ - P.root m) + P.root k := by rw [hm]; abel
  rw [this]
  exact add_mem hmθ (TauCeti.root_mem_posRootCone_of_mem_posRoots P b
    ((TauCeti.mem_posRoots P b k).mpr (b.isPos_of_mem_support hk)))

/-- **The highest root is the only root lying above every root.** -/
theorem forall_root_sub_mem_posRootCone_iff {i : ι} :
    (∀ j, P.root i - P.root j ∈ TauCeti.posRootCone P b) ↔ i = b.highestRoot := by
  refine ⟨fun hi ↦ P.root.injective ?_, fun h ↦ h ▸ b.root_highestRoot_sub_mem_posRootCone⟩
  refine sub_eq_zero.mp (TauCeti.eq_zero_of_add_eq_zero_of_mem_posRootCone P b
    (hi b.highestRoot) (b.root_highestRoot_sub_mem_posRootCone i) ?_)
  abel

/-- **Every root other than the highest root has strictly smaller height.** -/
theorem height_lt_height_highestRoot {j : ι} (hj : j ≠ b.highestRoot) :
    b.height j < b.height b.highestRoot := by
  refine (b.height_le_height_highestRoot j).lt_of_ne fun h ↦ hj (P.root.injective ?_)
  refine (sub_eq_zero.mp (TauCeti.eq_zero_of_mem_posRootCone_of_heightLinearMap_eq_zero P b
    (b.root_highestRoot_sub_mem_posRootCone j) ?_)).symm
  simp [h]

variable {b} in
/-- **The highest root takes the largest value of all roots** at a point where every simple root
is nonnegative, since `θ - α` is a nonnegative combination of the simple roots for every root
`α`. -/
theorem _root_.RootPairing.root'_le_root'_highestRoot [Preorder R] [IsOrderedAddMonoid R]
    {x : N} (hx : ∀ i ∈ b.support, 0 ≤ P.root' i x) (j : ι) :
    P.root' j x ≤ P.root' b.highestRoot x := by
  have h := RootPairing.toLinearMap_apply_nonneg_of_mem_posRootCone hx
    (b.root_highestRoot_sub_mem_posRootCone j)
  rwa [map_sub, LinearMap.sub_apply, sub_nonneg] at h

/-- **The highest root is long**: for every root-positive form, no root is longer than the
highest root. -/
theorem rootLength_le_rootLength_highestRoot {S : Type*} [CommRing S] [LinearOrder S]
    [IsStrictOrderedRing S] [Algebra S R] [FaithfulSMul S R] [Module S M] [IsScalarTower S R M]
    [P.IsValuedIn S] (B : P.RootPositiveForm S) (j : ι) :
    B.rootLength j ≤ B.rootLength b.highestRoot := by
  -- A longest root `β` of greatest height among the longest roots is dominant, since reflecting
  -- it in a simple root it pairs negatively with would give a root of the same length and greater
  -- height. Writing `θ - β = ∑ cₖ αₖ` with `cₖ ≥ 0`, the difference `2 (|θ|² - |β|²)` is
  -- `∑ cₖ (⟨θ, αₖ^∨⟩ + ⟨β, αₖ^∨⟩) |αₖ|²`, which is nonnegative because both roots are dominant.
  set θ := b.highestRoot
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max B.rootLength
  set T := {i | ∀ j, B.rootLength j ≤ B.rootLength i}
  obtain ⟨β, hβT, hβ⟩ := Set.exists_max_image T b.height T.toFinite ⟨i₀, hi₀⟩
  refine (hβT j).trans ?_
  have hdom : ∀ k ∈ b.support, 0 ≤ P.pairingIn ℤ β k := fun k hk ↦ by
    by_contra! hneg
    have := hβ (P.reflectionPerm k β) fun j ↦ by simpa using hβT j
    rw [TauCeti.height_reflectionPerm_of_mem_support P b hk] at this
    omega
  obtain ⟨c, hc⟩ := (TauCeti.mem_posRootCone P b).mp (b.root_highestRoot_sub_mem_posRootCone β)
  have hp (i k : ι) : ((P.pairingIn ℤ i k : ℤ) : R) = P.pairing i k := by
    rw [← P.algebraMap_pairingIn ℤ]; simp
  have key : 2 * B.rootLength θ - 2 * B.rootLength β = ∑ k ∈ b.support,
      ((c k : S) * ((P.pairingIn ℤ θ k + P.pairingIn ℤ β k : ℤ) : S)) * B.rootLength k := by
    apply FaithfulSMul.algebraMap_injective S R
    have hsymm := B.symm.eq (P.root θ) (P.root β)
    simp only [map_sub, map_mul, map_sum, map_add, map_natCast, map_intCast, map_ofNat,
      B.algebraMap_rootLength, Int.cast_add, hp]
    simp only [mul_assoc, add_mul, ← B.two_mul_apply_root_root]
    calc 2 * B.form (P.root θ) (P.root θ) - 2 * B.form (P.root β) (P.root β)
        = 2 * B.form (P.root θ) (P.root θ - P.root β)
          + 2 * B.form (P.root β) (P.root θ - P.root β) := by
          simp only [map_sub]; rw [RingHom.id_apply] at hsymm; rw [hsymm]; ring
      _ = _ := by
          rw [hc]
          simp only [map_sum, map_nsmul, nsmul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          ring
  have hnonneg : 0 ≤ 2 * B.rootLength θ - 2 * B.rootLength β := by
    rw [key]
    refine Finset.sum_nonneg fun k hk ↦ mul_nonneg (mul_nonneg (by positivity) ?_)
      (B.rootLength_pos k).le
    exact_mod_cast add_nonneg (b.pairingIn_highestRoot_nonneg hk) (hdom k hk)
  linarith

/-- **A root other than `±θ` pairs with the coroot of the highest root to `-1`, `0` or `1`**,
because the highest root is long. -/
theorem pairingIn_highestRoot_right_mem {j : ι} (h : P.root j ≠ P.root b.highestRoot)
    (h' : P.root j ≠ -P.root b.highestRoot) :
    P.pairingIn ℤ j b.highestRoot ∈ ({-1, 0, 1} : Set ℤ) := by
  have := Fintype.ofFinite ι
  by_contra hmem
  exact ((P.posRootForm ℤ).rootLength_lt_of_pairingIn_notMem h h' hmem).not_ge
    (b.rootLength_le_rootLength_highestRoot (P.posRootForm ℤ) j)

/-- **A positive root other than `θ` pairs with the coroot of the highest root to `0` or `1`.** -/
theorem pairingIn_highestRoot_right_eq_zero_or_eq_one {j : ι} (hj : b.IsPos j)
    (hne : j ≠ b.highestRoot) :
    P.pairingIn ℤ j b.highestRoot = 0 ∨ P.pairingIn ℤ j b.highestRoot = 1 := by
  have h0 := b.pairingIn_highestRoot_right_nonneg hj
  have h1 := b.pairingIn_highestRoot_right_mem (P.root.injective.ne hne)
    (b.root_ne_neg_root_highestRoot hj)
  simp only [mem_insert_iff, mem_singleton_iff] at h1
  omega

end RootPairing.Base
