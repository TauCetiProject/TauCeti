/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.LinearAlgebra.RootSystem.AffineCartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Chamber

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
`1 / (ht(θ) + 1)` lies in `A`.

The alcove lives on the coweight space because the roots act on it, as in the classical setting
where `N = Hom(ℤΦ, ℝ)` contains the coroot lattice. Over the same space the dominant chamber is the
open dominant chamber of the flipped pairing `P.flip`, which contains `A`.

## Main definitions

* `RootPairing.fundamentalAlcove`: the open fundamental alcove of a base.
* `RootPairing.closedFundamentalAlcove`: the closed fundamental alcove, cut out by the
  non-strict inequalities.
* `RootPairing.Base.affineSimpleRoot`: the affine simple roots `a₀ = 1 - θ` and `aᵢ = αᵢ`,
  indexed by the nodes of the affine Dynkin diagram, whose zero sets are the walls of the
  fundamental alcove.

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
* `RootPairing.mem_fundamentalAlcove_iff_mem_closedFundamentalAlcove`: the fundamental alcove is
  the part of the closed fundamental alcove lying on no affine root hyperplane.
* `RootPairing.convex_fundamentalAlcove`: the fundamental alcove is convex.
* `RootPairing.mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos`: the fundamental alcove is
  the set of points at which every affine simple root is positive.
* `RootPairing.Base.sum_affineMarks_mul_affineSimpleRoot`: the null-root relation `∑ₖ mₖ aₖ = 1`,
  where the marks `mₖ` are the coefficients of `θ` and `m₀ = 1`.
* `RootPairing.Base.exists_affineSimpleRoot_eq_of_height_eq_one`: an affine root `α + n` of height
  `ht(α) + n (ht(θ) + 1) = 1` is an affine simple root.
* `RootPairing.exists_mem_fundamentalAlcove_root'_eq_height_div`: over a linearly ordered field
  the fundamental alcove contains a point at which every root `α` takes the value
  `ht(α) / (ht(θ) + 1)`.
* `RootPairing.fundamentalAlcove_nonempty`: so the fundamental alcove is nonempty.

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

/-- The **closed fundamental alcove** of a base `b`: the points of the coweight space at which every
simple root is nonnegative and the highest root `θ = b.highestRoot` is at most `1`. For a real root
system it is the closure of `RootPairing.fundamentalAlcove`. Over an archimedean ring the affine
Weyl group carries every point into it
(`RootPairing.exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove`). -/
def closedFundamentalAlcove : Set N :=
  {x | (∀ i ∈ b.support, 0 ≤ P.root' i x) ∧ P.root' b.highestRoot x ≤ 1}

/-- Membership in the closed fundamental alcove. -/
@[simp]
lemma mem_closedFundamentalAlcove {x : N} :
    x ∈ closedFundamentalAlcove P b ↔
      (∀ i ∈ b.support, 0 ≤ P.root' i x) ∧ P.root' b.highestRoot x ≤ 1 :=
  Iff.rfl

/-- The fundamental alcove lies in the closed fundamental alcove. -/
lemma fundamentalAlcove_subset_closedFundamentalAlcove :
    fundamentalAlcove P b ⊆ closedFundamentalAlcove P b := fun _ hx ↦
  ⟨fun i hi ↦ (hx.1 i hi).le, hx.2.le⟩

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

/-- **The fundamental alcove is the part of the closed fundamental alcove lying on no affine root
hyperplane.** -/
theorem mem_fundamentalAlcove_iff_mem_closedFundamentalAlcove :
    x ∈ fundamentalAlcove P b ↔
      x ∈ closedFundamentalAlcove P b ∧ ∀ j (k : ℤ), P.root' j x ≠ k := by
  refine ⟨fun hx ↦ ⟨fundamentalAlcove_subset_closedFundamentalAlcove P b hx,
    root'_ne_intCast_of_mem_fundamentalAlcove hx⟩, fun ⟨hx, h⟩ ↦ ⟨fun i hi ↦ ?_, ?_⟩⟩
  · exact (hx.1 i hi).lt_of_ne' (by simpa using h i 0)
  · exact hx.2.lt_of_ne (by simpa using h b.highestRoot 1)

end Alcove

end CommRing

/-! ### The affine simple roots -/

section AffineSimpleRoot

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base) [CharZero R] [Finite ι] [Nonempty ι]

namespace Base

/-- The **affine simple roots** of a base `b`: the affine functions `a₀ = 1 - θ` at the affine node
`none`, and `aᵢ = αᵢ` at the node of a simple root `αᵢ`, where `θ = b.highestRoot`. Their zero sets
are the walls of the fundamental alcove
(`RootPairing.mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos`). -/
noncomputable def affineSimpleRoot : Option b.support → N → R
  | none, x => 1 - P.root' b.highestRoot x
  | some i, x => P.root' i x

@[simp]
lemma affineSimpleRoot_none (x : N) :
    b.affineSimpleRoot none x = 1 - P.root' b.highestRoot x :=
  (rfl)

@[simp]
lemma affineSimpleRoot_some (i : b.support) (x : N) : b.affineSimpleRoot (some i) x = P.root' i x :=
  (rfl)

/-- An affine simple root is the root functional of `RootPairing.Base.affineSimpleRootIndex` plus
its value at `0`. -/
lemma affineSimpleRoot_eq_root'_add (k : Option b.support) (x : N) :
    b.affineSimpleRoot k x = P.root' (b.affineSimpleRootIndex k) x + b.affineSimpleRoot k 0 := by
  rcases k with _ | i <;> simp [root'_reflectionPerm_self, sub_eq_neg_add]

/-- Distinct nodes have distinct affine simple roots. -/
lemma affineSimpleRoot_injective : Function.Injective b.affineSimpleRoot := by
  rintro (_ | i) (_ | j) h <;> have h0 := congrFun h 0
  · rfl
  · simp at h0
  · simp at h0
  · have : P.root i = P.root j :=
      P.toPerfPair.injective <| LinearMap.ext fun x ↦ by simpa using congrFun h x
    exact congrArg some (Subtype.ext (P.root.injective this))

/-- **The null-root relation**: `∑ₖ mₖ aₖ = 1`, where the marks `mₖ` are the coefficients of the
highest root `θ = ∑ mᵢ αᵢ` and `m₀ = 1`. -/
theorem sum_affineMarks_mul_affineSimpleRoot (x : N) :
    ∑ k, (b.affineMarks k : R) * b.affineSimpleRoot k x = 1 := by
  have h : P.root' b.highestRoot x =
      ∑ i : b.support, (b.affineMarks (some i) : R) * P.root' i x := by
    rw [root', b.root_highestRoot_eq_sum_affineMarks]
    simp [zsmul_eq_mul]
  rw [Fintype.sum_option]
  simp only [affineMarks_none, Int.cast_one, one_mul, affineSimpleRoot_none,
    affineSimpleRoot_some, h]
  ring

/-- **An affine root `α + n` of height `ht(α) + n (ht(θ) + 1) = 1` is an affine simple root**: it
is `αᵢ` (with `n = 0`) or `1 - θ` (with `n = 1`). -/
lemma exists_affineSimpleRoot_eq_of_height_eq_one [IsDomain R] [P.IsCrystallographic]
    [P.IsReduced] [P.IsIrreducible] {j : ι} {n : ℤ}
    (h : b.height j + n * (b.height b.highestRoot + 1) = 1) :
    ∃ l, ∀ x, b.affineSimpleRoot l x = P.root' j x + n := by
  have hθ : 0 < b.height b.highestRoot := b.isPos_highestRoot
  have hlo := b.neg_height_highestRoot_le_height j
  have hhi := b.height_le_height_highestRoot j
  obtain rfl | rfl | hn : n = 0 ∨ n = 1 ∨ (2 ≤ n ∨ n ≤ -1) := by omega
  · -- `n = 0`: `α` has height `1`, so it is a simple root.
    have hj : j ∈ b.support := (b.height_eq_one_iff).mp (by simpa using h)
    exact ⟨some ⟨j, hj⟩, fun x ↦ by simp⟩
  · -- `n = 1`: `α` has height `-ht(θ)`, so it is `-θ`.
    obtain rfl : j = P.reflectionPerm b.highestRoot b.highestRoot := by
      by_contra hne
      have := b.neg_height_highestRoot_lt_height hne
      omega
    exact ⟨none, fun x ↦ by simp [root'_reflectionPerm_self, sub_eq_neg_add]⟩
  · exact absurd h (by rcases hn with hn | hn <;> nlinarith)

end Base

/-- **The fundamental alcove is the set of points at which every affine simple root is
positive.** -/
theorem mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos [PartialOrder R]
    [IsOrderedAddMonoid R] {x : N} :
    x ∈ fundamentalAlcove P b ↔ ∀ k, 0 < b.affineSimpleRoot k x := by
  simp only [mem_fundamentalAlcove, Option.forall, Base.affineSimpleRoot_none, sub_pos,
    Base.affineSimpleRoot_some, Subtype.forall]
  tauto

end AffineSimpleRoot

/-! ### Nonemptiness -/

section Field

variable {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- The point `x₀` at which every simple root takes the value `1 / h`, with `h = ht(θ) + 1`, lies in
the fundamental alcove, and every root `α` takes the value `ht(α) / h` there. -/
lemma exists_mem_fundamentalAlcove_root'_eq_height_div [Finite ι] [Nonempty ι] :
    ∃ x₀ ∈ fundamentalAlcove P b,
      ∀ j, P.root' j x₀ = b.height j / ((b.height b.highestRoot : R) + 1) := by
  have hD : (0 : R) < b.height b.highestRoot + 1 := by
    have : (0 : R) < b.height b.highestRoot := by exact_mod_cast b.isPos_highestRoot
    linarith
  obtain ⟨x₀, hx₀⟩ := b.exists_forall_root'_eq fun _ ↦ ((b.height b.highestRoot : R) + 1)⁻¹
  have hx₀' (j : ι) : P.root' j x₀ = b.height j / ((b.height b.highestRoot : R) + 1) := by
    simpa [zsmul_eq_mul, div_eq_mul_inv] using TauCeti.apply_root_eq_height_zsmul P b
      (P.toLinearMap.flip x₀).toAddMonoidHom (fun j hj ↦ hx₀ j hj) j
  refine ⟨x₀, (mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos b).mpr ?_, hx₀'⟩
  rintro (_ | i)
  · rw [Base.affineSimpleRoot_none, hx₀', sub_pos, div_lt_one hD]
    linarith
  · rw [Base.affineSimpleRoot_some, hx₀', Base.height_one_of_mem_support i.2]
    simpa using hD

/-- Over a linearly ordered field the fundamental alcove is nonempty: it contains the point at which
every simple root takes the value `1 / (ht(θ) + 1)`. -/
theorem fundamentalAlcove_nonempty [Finite ι] [Nonempty ι] :
    (fundamentalAlcove P b).Nonempty :=
  let ⟨x₀, hx₀, _⟩ := exists_mem_fundamentalAlcove_root'_eq_height_div b
  ⟨x₀, hx₀⟩

end Field

end RootPairing
