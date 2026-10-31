/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot

/-!
# The fundamental alcove of a base

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P` over a
linearly ordered coefficient ring, with simple roots `αᵢ` and highest root `θ`. The roots are
functionals `α(x) = ⟨α, x⟩` on the coweight space `N`, and the affine root hyperplanes
`H_{α,k} = {x | α(x) = k}`, for `α` a root and `k` an integer, cut `N` into the *alcoves*. The
**fundamental alcove** is

`A = {x ∈ N | αᵢ(x) > 0 for every simple root αᵢ, and θ(x) < 1}`,

the part of the open dominant chamber below the affine wall `θ = 1`. Its walls are the zero sets
of the affine functions `αᵢ` and `1 - θ`; classically the reflections in these walls generate the
affine Weyl group, and the affine Cartan matrix `RootPairing.Base.affineCartanMatrix` records how
the walls meet.

The main theorem identifies `A` with the set of points where every positive root takes a value
strictly between `0` and `1`. One inclusion is the definition, as the simple roots and `θ` are
positive. For the other, a positive root `α` is a nonnegative combination of the simple roots, so
`α(x) > 0` on `A` (`RootPairing.root'_pos_of_isPos`), and `θ - α` lies in the positive root cone
`Q⁺` (`RootPairing.Base.root_highestRoot_sub_mem_posRootCone`), so `α(x) ≤ θ(x) < 1`
(`RootPairing.root'_le_root'_highestRoot`). Consequently every root, positive or negative, takes
values in an open interval between consecutive integers on `A`, and this interval depends only on
the sign of the root. So `A` meets none of the hyperplanes `H_{α,k}`, and a point lies in `A`
exactly when it lies on the same side as `A` of every one of them: `A` is one of the alcoves, a
cell of the affine root-hyperplane arrangement.

The alcove is convex, as an intersection of open half-spaces. Over a linearly ordered field it is
nonempty: the simple roots take arbitrary prescribed values at some point of `N`
(`RootPairing.Base.exists_forall_root'_eq`), and the point at which each of them takes the value
`1 / (n + 1)`, where `n` is the sum of the coefficients of `θ`, lies in `A`.

The alcove lives on the coweight space because the roots act on it, as in the classical setting
where `N = Hom(ℤΦ, ℝ)` contains the coroot lattice. Over the same space the dominant chamber is the
open dominant chamber of the flipped pairing `P.flip`, which contains `A`.

## Main definitions

* `RootPairing.fundamentalAlcove`: the open fundamental alcove of a base.

## Main results

* `RootPairing.fundamentalAlcove_subset_openDominantChamber`: the fundamental alcove lies in the
  open dominant chamber of `P.flip`.
* `RootPairing.mem_fundamentalAlcove_iff_forall_isPos`: **the fundamental alcove is the set of
  points where every positive root takes a value in the open interval `(0, 1)`.**
* `RootPairing.exists_intCast_lt_root'_lt`: on the fundamental alcove each root takes its values in
  a fixed open interval `(n, n + 1)` with `n` an integer.
* `RootPairing.root'_ne_intCast_of_mem_fundamentalAlcove`: the fundamental alcove meets no affine
  root hyperplane.
* `RootPairing.mem_fundamentalAlcove_iff_of_mem`: **the fundamental alcove is a cell of the affine
  root-hyperplane arrangement**: a point lies in it exactly when it lies on no affine root
  hyperplane and on the same side as a given point of the alcove of each of them.
* `RootPairing.convex_fundamentalAlcove`: the fundamental alcove is convex.
* `RootPairing.fundamentalAlcove_nonempty`: over a linearly ordered field the fundamental alcove
  is nonempty.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §1–§3 (alcoves of an affine
  hyperplane arrangement) and Ch. VI, §2.2 (the fundamental alcove of an irreducible root system).
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29, Chapter 4, §4.3 (alcoves).
-/

public section

namespace RootPairing

open Set TauCeti

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (b : P.Base)

section Definition

variable [CharZero R] [Finite ι] [Nonempty ι] [Preorder R]

/-- The **open fundamental alcove** of a base `b`: the points of the coweight space at which every
simple root is positive and the highest root `θ = b.highestRoot` is less than `1`.

When `P` is reduced and irreducible, so that `θ` is the highest root rather than merely a root of
maximal height, it is a cell of the affine root-hyperplane arrangement
(`RootPairing.mem_fundamentalAlcove_iff_of_mem`). -/
def fundamentalAlcove : Set N :=
  {x | (∀ i ∈ b.support, 0 < P.root' i x) ∧ P.root' b.highestRoot x < 1}

/-- Membership in the fundamental alcove. -/
@[simp]
lemma mem_fundamentalAlcove {x : N} :
    x ∈ fundamentalAlcove P b ↔
      (∀ i ∈ b.support, 0 < P.root' i x) ∧ P.root' b.highestRoot x < 1 :=
  Iff.rfl

/-- The fundamental alcove lies in the open dominant chamber of the flipped pairing, the points of
the coweight space at which every simple root is positive. -/
lemma fundamentalAlcove_subset_openDominantChamber :
    fundamentalAlcove P b ⊆ openDominantChamber P.flip b.flip := fun x hx ↦
  (mem_openDominantChamber P.flip b.flip x).mpr fun i hi ↦ by simpa using hx.1 i (by simpa using hi)

end Definition

/-! ### The fundamental alcove as a cell of the affine root-hyperplane arrangement -/

section Alcove

variable [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [Nonempty ι] {P b} {x y : N}

/-- The fundamental alcove is convex: it is an intersection of open half-spaces. -/
theorem convex_fundamentalAlcove : Convex R (fundamentalAlcove P b) := by
  have h : fundamentalAlcove P b =
      (⋂ i ∈ b.support, {x | 0 < P.root' i x}) ∩ {x | P.root' b.highestRoot x < 1} := by
    ext x
    simp [mem_fundamentalAlcove]
  rw [h]
  exact (convex_iInter₂ fun i _ ↦ convex_halfSpace_gt (P.root' i).isLinear 0).inter
    (convex_halfSpace_lt (P.root' _).isLinear 1)

variable [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- Every root is less than `1` on the fundamental alcove. -/
theorem root'_lt_one_of_mem_fundamentalAlcove (hx : x ∈ fundamentalAlcove P b) (j : ι) :
    P.root' j x < 1 :=
  (root'_le_root'_highestRoot (fun i hi ↦ (hx.1 i hi).le) j).trans_lt hx.2

/-- Every root is greater than `-1` on the fundamental alcove. -/
theorem neg_one_lt_root'_of_mem_fundamentalAlcove (hx : x ∈ fundamentalAlcove P b) (j : ι) :
    -1 < P.root' j x := by
  let := P.indexNeg
  have h := root'_lt_one_of_mem_fundamentalAlcove hx (-j)
  simp only [root', root_neg_index, map_neg, LinearMap.neg_apply] at h
  linarith

/-- **The fundamental alcove is the set of points where every positive root takes a value in the
open interval `(0, 1)`.** -/
theorem mem_fundamentalAlcove_iff_forall_isPos :
    x ∈ fundamentalAlcove P b ↔ ∀ j, b.IsPos j → 0 < P.root' j x ∧ P.root' j x < 1 :=
  ⟨fun hx _ hj ↦ ⟨root'_pos_of_isPos hx.1 hj,
      root'_lt_one_of_mem_fundamentalAlcove hx _⟩,
    fun h ↦ ⟨fun i hi ↦ (h i (b.isPos_of_mem_support hi)).1, (h _ b.isPos_highestRoot).2⟩⟩

/-- **On the fundamental alcove every root stays between two consecutive integers**: for each
root there is an integer `n`, namely `0` for a positive root and `-1` for a negative one, such
that the root takes its values in the open interval `(n, n + 1)` on the whole alcove. -/
theorem exists_intCast_lt_root'_lt (j : ι) :
    ∃ n : ℤ, ∀ x ∈ fundamentalAlcove P b, (n : R) < P.root' j x ∧ P.root' j x < n + 1 := by
  by_cases hj : b.IsPos j
  · exact ⟨0, fun x hx ↦ by simpa using ⟨root'_pos_of_isPos hx.1 hj,
      root'_lt_one_of_mem_fundamentalAlcove hx j⟩⟩
  · exact ⟨-1, fun x hx ↦ by simpa using ⟨neg_one_lt_root'_of_mem_fundamentalAlcove hx j,
      root'_neg_of_not_isPos hx.1 hj⟩⟩

/-- **The fundamental alcove meets no affine root hyperplane**: no root takes an integer value on
it. -/
theorem root'_ne_intCast_of_mem_fundamentalAlcove (hx : x ∈ fundamentalAlcove P b) (j : ι)
    (k : ℤ) : P.root' j x ≠ k := by
  obtain ⟨n, hn⟩ := exists_intCast_lt_root'_lt (P := P) (b := b) j
  obtain ⟨h₁, h₂⟩ := hn x hx
  rintro h
  rw [h] at h₁ h₂
  have h₁' : n < k := by exact_mod_cast h₁
  have h₂' : k < n + 1 := by exact_mod_cast h₂
  omega

/-- **The fundamental alcove is a cell of the affine root-hyperplane arrangement.** Given a point
`x` of the alcove, a point `y` lies in the alcove exactly when, for every root `α` and every
integer `k`, it does not lie on the hyperplane `α = k` and lies on the same side of it as `x`. -/
theorem mem_fundamentalAlcove_iff_of_mem (hx : x ∈ fundamentalAlcove P b) :
    y ∈ fundamentalAlcove P b ↔
      ∀ j (k : ℤ), ((k : R) < P.root' j y ↔ (k : R) < P.root' j x) ∧ P.root' j y ≠ k := by
  refine ⟨fun hy j k ↦ ⟨?_, root'_ne_intCast_of_mem_fundamentalAlcove hy j k⟩, fun h ↦ ?_⟩
  · -- both values lie in the same interval `(n, n + 1)`, where `k < v` means `k ≤ n`
    obtain ⟨n, hn⟩ := exists_intCast_lt_root'_lt (P := P) (b := b) j
    have key : ∀ v : R, (n : R) < v → v < n + 1 → ((k : R) < v ↔ k ≤ n) := fun v h₁ h₂ ↦
      ⟨fun h ↦ Int.lt_add_one_iff.mp (by exact_mod_cast h.trans h₂),
        fun h ↦ lt_of_le_of_lt (by exact_mod_cast h) h₁⟩
    rw [key _ (hn x hx).1 (hn x hx).2, key _ (hn y hy).1 (hn y hy).2]
  · refine ⟨fun i hi ↦ ?_, ?_⟩
    · simpa using (h i 0).1.mpr (by simpa using hx.1 i hi)
    · obtain ⟨h₁, h₂⟩ := h b.highestRoot 1
      push_cast at h₁ h₂
      exact lt_of_le_of_ne (not_lt.mp fun h' ↦ hx.2.not_gt (h₁.mp h')) h₂

end Alcove

end CommRing

/-! ### Nonemptiness -/

section Field

variable {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- Over a linearly ordered field the fundamental alcove is nonempty: if `θ = ∑ nᵢ αᵢ`, it contains
the point at which every simple root takes the value `1 / (∑ nᵢ + 1)`. -/
theorem fundamentalAlcove_nonempty [Finite ι] [Nonempty ι] :
    (fundamentalAlcove P b).Nonempty := by
  obtain ⟨f, -, hf⟩ := exists_root_eq_sum_nat_of_mem_posRoots P b
    ((mem_posRoots P b _).mpr b.isPos_highestRoot)
  set n : R := ∑ k ∈ b.support, (f k : R)
  have hn : 0 ≤ n := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  obtain ⟨x, hx⟩ := b.exists_forall_root'_eq fun _ ↦ (n + 1)⁻¹
  refine ⟨x, fun i hi ↦ by rw [hx i hi]; positivity, ?_⟩
  have hθ : P.root' b.highestRoot x = n * (n + 1)⁻¹ := by
    simp only [root', hf, map_sum, map_nsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      nsmul_eq_mul, n, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k hk ↦ by rw [← hx k hk]
  rw [hθ, mul_inv_lt_iff₀ (by positivity)]
  linarith

end Field

end RootPairing
