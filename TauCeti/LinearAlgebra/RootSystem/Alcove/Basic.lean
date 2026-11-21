/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.LinearAlgebra.RootSystem.AffineCartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Chamber
public import TauCeti.LinearAlgebra.RootSystem.CoweightLattice.Basis

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
* `RootPairing.Base.closedAlcoveFace` and `RootPairing.Base.openAlcoveFace`: the closed face and
  open face of the fundamental alcove associated with a set `J` of affine nodes.

## Main results

* `RootPairing.fundamentalAlcove_subset_openDominantChamber`: the fundamental alcove lies in the
  open dominant chamber of `P.flip`.
* `RootPairing.mem_fundamentalAlcove_iff_forall_isPos` and
  `RootPairing.mem_closedFundamentalAlcove_iff_forall_isPos`: **the open and closed fundamental
  alcoves are the sets of points where every positive root takes a value in `(0, 1)` and `[0, 1]`,
  respectively.**
* `RootPairing.exists_intCast_lt_root'_lt`: on the fundamental alcove each root takes its values in
  a fixed open interval `(n, n + 1)` with `n` an integer.
* `RootPairing.root'_ne_intCast_of_mem_fundamentalAlcove`: the fundamental alcove meets no affine
  root hyperplane.
* `RootPairing.mem_fundamentalAlcove_iff_of_mem`: **the fundamental alcove is a cell of the affine
  root-hyperplane arrangement**: a point lies in it exactly when it lies on no affine root
  hyperplane and on the same side as a given point of the alcove of each of them.
* `RootPairing.mem_fundamentalAlcove_iff_mem_closedFundamentalAlcove`: the fundamental alcove is
  the part of the closed fundamental alcove lying on no affine root hyperplane.
* `RootPairing.convex_fundamentalAlcove`, `RootPairing.convex_closedFundamentalAlcove`, and
  `RootPairing.lineMap_mem_fundamentalAlcove`: convexity of both alcoves, and that the half-open
  segment `(x, x₀]` from a point of `Ā` to a point of `A` lies in `A`.
* `RootPairing.mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos`: the fundamental alcove is
  the set of points at which every affine simple root is positive.
* `RootPairing.mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg`: the closed
  fundamental alcove is the set of points at which every affine simple root is nonnegative.
* `RootPairing.Base.sum_affineMarks_mul_affineSimpleRoot`: the null-root relation `∑ₖ mₖ aₖ = 1`,
  where the marks `mₖ` are the coefficients of `θ` and `m₀ = 1`.
* `RootPairing.Base.exists_affineSimpleRoot_eq_of_height_eq_one`: an affine root `α + n` of height
  `ht(α) + n (ht(θ) + 1) = 1` is an affine simple root.
* `RootPairing.Base.affineSimpleRoot_fundamentalCoweightBasis_of_mem_specialNodes` and
  `RootPairing.Base.exists_mem_coweightLattice_affineSimpleRoot_eq`: at a special node `k` the
  closed fundamental alcove has a vertex in the coweight lattice, the origin for `k = 0` and the
  fundamental coweight `ϖⱼ` for `k = j`.
* `RootPairing.exists_mem_fundamentalAlcove_root'_eq_height_div` and
  `RootPairing.fundamentalAlcove_nonempty`: over a linearly ordered field the fundamental alcove is
  nonempty, containing the point where every root `α` takes the value `ht(α) / (ht(θ) + 1)`.
* `RootPairing.Base.exists_forall_affineSimpleRoot_eq`: over a field any tuple `a` satisfying
  `∑ k, mₖ aₖ = 1` is realized by `b.affineSimpleRoot · x` at some point `x : N`.
* `RootPairing.Base.iUnion_openAlcoveFace`, `RootPairing.Base.pairwise_disjoint_openAlcoveFace`,
  `RootPairing.Base.openAlcoveFace_nonempty_iff`, `RootPairing.Base.closedAlcoveFace_nonempty_iff`,
  `RootPairing.Base.closedAlcoveFace_compl_singleton_none`,
  `RootPairing.Base.closedAlcoveFace_compl_singleton_some_of_mem_specialNodes`, and
  `RootPairing.Base.closedAlcoveFace_compl_singleton_some`: the partition of `Ā` into pairwise
  disjoint open faces, nonemptiness for proper node sets `J ≠ univ`, and the vertex faces opposite
  the affine wall `θ = 1` and every simple wall `αⱼ = 0`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §1–§3 (alcoves of an affine
  hyperplane arrangement) and Ch. VI, §2.2 (the fundamental alcove of an irreducible root system).
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29, Chapter 4, §4.3 (alcoves).
-/

public section

namespace RootPairing

open Set Function TauCeti

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (b : P.Base)

section Definition

variable [CharZero R] [Finite ι] [Nonempty ι] [Preorder R]

/-- The **open fundamental alcove** of a base `b`: the points of the coweight space at which every
simple root is positive and the highest root `θ = b.highestRoot` is less than `1`.

For a finite, reduced, irreducible, crystallographic root pairing over a linearly ordered ring,
`RootPairing.mem_fundamentalAlcove_iff_of_mem` characterizes it as the cell of a given point of
the alcove in the affine root-hyperplane arrangement. -/
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
system it is the closure of `RootPairing.fundamentalAlcove`. For a finite, reduced, irreducible,
crystallographic root pairing over an archimedean linearly ordered ring, the affine Weyl group
carries every point into it
(`RootPairing.exists_mem_affineWeylGroup_apply_mem_closedFundamentalAlcove`). -/
def closedFundamentalAlcove : Set N :=
  {x | (∀ i ∈ b.support, 0 ≤ P.root' i x) ∧ P.root' b.highestRoot x ≤ 1}

/-- Membership in the closed fundamental alcove. -/
@[simp]
lemma mem_closedFundamentalAlcove {x : N} :
    x ∈ closedFundamentalAlcove P b ↔
      (∀ i ∈ b.support, 0 ≤ P.root' i x) ∧ P.root' b.highestRoot x ≤ 1 :=
  Iff.rfl

/-- The open fundamental alcove as an intersection of open half-spaces. -/
lemma fundamentalAlcove_eq_biInter_inter :
    fundamentalAlcove P b =
      (⋂ i ∈ b.support, P.root' i ⁻¹' Ioi 0) ∩ P.root' b.highestRoot ⁻¹' Iio 1 := by
  ext x
  simp [mem_fundamentalAlcove]

/-- The closed fundamental alcove as an intersection of closed half-spaces. -/
lemma closedFundamentalAlcove_eq_biInter_inter :
    closedFundamentalAlcove P b =
      (⋂ i ∈ b.support, P.root' i ⁻¹' Ici 0) ∩ P.root' b.highestRoot ⁻¹' Iic 1 := by
  ext x
  simp [mem_closedFundamentalAlcove]

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
  rw [fundamentalAlcove_eq_biInter_inter]
  exact (convex_iInter₂ fun i _ ↦ convex_halfSpace_gt (P.root' i).isLinear 0).inter
    (convex_halfSpace_lt (P.root' _).isLinear 1)

/-- The closed fundamental alcove is convex: it is an intersection of closed half-spaces. -/
theorem convex_closedFundamentalAlcove : Convex R (closedFundamentalAlcove P b) := by
  rw [closedFundamentalAlcove_eq_biInter_inter]
  exact (convex_iInter₂ fun i _ ↦ convex_halfSpace_ge (P.root' i).isLinear 0).inter
    (convex_halfSpace_le (P.root' _).isLinear 1)

/-- The half-open segment `(x, x₀]` from a point `x` of the closed fundamental alcove to a point
`x₀` of the open fundamental alcove lies inside the open fundamental alcove. -/
theorem lineMap_mem_fundamentalAlcove {x x₀ : N} (hx : x ∈ closedFundamentalAlcove P b)
    (hx₀ : x₀ ∈ fundamentalAlcove P b) {t : R} (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    AffineMap.lineMap x x₀ t ∈ fundamentalAlcove P b := by
  obtain ⟨hx₁, hx₂⟩ := (mem_closedFundamentalAlcove P b).mp hx
  obtain ⟨hx₀₁, hx₀₂⟩ := (mem_fundamentalAlcove P b).mp hx₀
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  rw [AffineMap.lineMap_apply_module, mem_fundamentalAlcove]
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg h1t (hx₁ i hi)) (mul_pos ht₀ (hx₀₁ i hi))
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc (1 - t) * P.root' b.highestRoot x + t * P.root' b.highestRoot x₀
        < (1 - t) * 1 + t * 1 :=
          add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx₂ h1t)
            (mul_lt_mul_of_pos_left hx₀₂ ht₀)
      _ = 1 := by ring

/-- The origin lies in the closed fundamental alcove (and when `P` is a root system, it is the
vertex of the alcove opposite the wall `θ = 1`). -/
theorem zero_mem_closedFundamentalAlcove : (0 : N) ∈ closedFundamentalAlcove P b :=
  ⟨fun _ _ ↦ by simp, by simp⟩

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

/-- Every root is at most `1` on the closed fundamental alcove. -/
theorem root'_le_one_of_mem_closedFundamentalAlcove (hx : x ∈ closedFundamentalAlcove P b)
    (j : ι) : P.root' j x ≤ 1 :=
  (root'_le_root'_highestRoot ((mem_closedFundamentalAlcove P b).mp hx).1 j).trans
    ((mem_closedFundamentalAlcove P b).mp hx).2

/-- Every root is at least `-1` on the closed fundamental alcove. -/
theorem neg_one_le_root'_of_mem_closedFundamentalAlcove (hx : x ∈ closedFundamentalAlcove P b)
    (j : ι) : -1 ≤ P.root' j x := by
  let := P.indexNeg
  have h := root'_le_one_of_mem_closedFundamentalAlcove hx (-j)
  simp only [root', root_neg_index, map_neg, LinearMap.neg_apply] at h
  linarith

/-- **The fundamental alcove is the set of points where every positive root takes a value in the
open interval `(0, 1)`.** -/
theorem mem_fundamentalAlcove_iff_forall_isPos :
    x ∈ fundamentalAlcove P b ↔ ∀ j, b.IsPos j → 0 < P.root' j x ∧ P.root' j x < 1 :=
  ⟨fun hx _ hj ↦ ⟨root'_pos_of_isPos hx.1 hj,
      root'_lt_one_of_mem_fundamentalAlcove hx _⟩,
    fun h ↦ ⟨fun i hi ↦ (h i (b.isPos_of_mem_support hi)).1, (h _ b.isPos_highestRoot).2⟩⟩

/-- **The closed fundamental alcove is the set of points where every positive root takes a value in
`[0, 1]`.** -/
theorem mem_closedFundamentalAlcove_iff_forall_isPos :
    x ∈ closedFundamentalAlcove P b ↔ ∀ j, b.IsPos j → 0 ≤ P.root' j x ∧ P.root' j x ≤ 1 :=
  ⟨fun hx _ hj ↦ ⟨root'_nonneg_of_isPos ((mem_closedFundamentalAlcove P b).mp hx).1 hj,
      root'_le_one_of_mem_closedFundamentalAlcove hx _⟩,
    fun h ↦ (mem_closedFundamentalAlcove P b).mpr
      ⟨fun i hi ↦ (h i (b.isPos_of_mem_support hi)).1, (h _ b.isPos_highestRoot).2⟩⟩

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

/-- **The closed fundamental alcove is the set of points at which every affine simple root is
nonnegative.** -/
theorem mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg [PartialOrder R]
    [IsOrderedAddMonoid R] {x : N} :
    x ∈ closedFundamentalAlcove P b ↔ ∀ k, 0 ≤ b.affineSimpleRoot k x := by
  simp only [mem_closedFundamentalAlcove, Option.forall, Base.affineSimpleRoot_none, sub_nonneg,
    Base.affineSimpleRoot_some, Subtype.forall]
  tauto

/-! ### The special vertices -/

variable [P.IsRootSystem]

/-- The highest root evaluated on a fundamental coweight `ϖⱼ` is the mark `mⱼ`. -/
@[simp]
theorem Base.root'_highestRoot_fundamentalCoweightBasis (j : b.support) :
    P.root' b.highestRoot (b.fundamentalCoweightBasis j) = b.affineMarks (some j) := by
  classical
  rw [root', b.root_highestRoot_eq_sum_affineMarks]
  simp [zsmul_eq_mul]

/-- **At a special node `j`, the fundamental coweight `ϖⱼ` is the vertex of the closed fundamental
alcove opposite the wall `αⱼ = 0`**: the affine simple root `aₖ` takes the value `1` at `ϖⱼ` for
`k = j` and vanishes for every other `k`, since `θ(ϖⱼ) = mⱼ = 1`. -/
theorem Base.affineSimpleRoot_fundamentalCoweightBasis_of_mem_specialNodes
    [DecidableEq ι] {j : b.support} (hj : some j ∈ b.specialNodes) (k : Option b.support) :
    b.affineSimpleRoot k (b.fundamentalCoweightBasis j) = if k = some j then 1 else 0 := by
  rcases k with _ | i
  · simp [b.mem_specialNodes.mp hj]
  · simp

/-- **At a special node `k` the closed fundamental alcove has a vertex in the coweight lattice**:
a point at which `aₖ = 1` and every other affine simple root vanishes. For `k = 0` it is the
origin, and for a simple root `αⱼ` it is the fundamental coweight `ϖⱼ`
(`RootPairing.Base.affineSimpleRoot_fundamentalCoweightBasis_of_mem_specialNodes`). -/
theorem Base.exists_mem_coweightLattice_affineSimpleRoot_eq {k : Option b.support}
    (hk : k ∈ b.specialNodes) :
    ∃ x ∈ P.coweightLattice,
      b.affineSimpleRoot k x = 1 ∧ ∀ l ≠ k, b.affineSimpleRoot l x = 0 := by
  classical
  rcases k with _ | j
  · refine ⟨0, zero_mem _, by simp, ?_⟩
    rintro (_ | i) hi
    · exact absurd rfl hi
    · simp
  · refine ⟨b.fundamentalCoweightBasis j, b.fundamentalCoweightBasis_mem_coweightLattice j,
      by simp [b.affineSimpleRoot_fundamentalCoweightBasis_of_mem_specialNodes hk], fun l hl ↦ ?_⟩
    simp [b.affineSimpleRoot_fundamentalCoweightBasis_of_mem_specialNodes hk, hl]

end AffineSimpleRoot

/-! ### Faces of the fundamental alcove -/

section CommRingFaces

variable {ι R M N : Type*} [CommRing R] [PartialOrder R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] (b : P.Base)

namespace Base

/-- The **closed face** of the fundamental alcove cut out by a set `J` of affine nodes: the points
of `closedFundamentalAlcove P b` lying on every wall `aₖ = 0` with `k ∈ J`. -/
def closedAlcoveFace (J : Set (Option b.support)) : Set N :=
  {x ∈ closedFundamentalAlcove P b | ∀ k ∈ J, b.affineSimpleRoot k x = 0}

/-- The **open face** (or wall-incidence stratum) of the fundamental alcove indexed by `J`: the
points where the affine simple roots in `J` vanish and all remaining affine simple roots are
strictly positive. -/
def openAlcoveFace (J : Set (Option b.support)) : Set N :=
  {x | (∀ k ∈ J, b.affineSimpleRoot k x = 0) ∧ ∀ k ∉ J, 0 < b.affineSimpleRoot k x}

@[simp]
lemma mem_closedAlcoveFace {J : Set (Option b.support)} {x : N} :
    x ∈ b.closedAlcoveFace J ↔
      x ∈ closedFundamentalAlcove P b ∧ ∀ k ∈ J, b.affineSimpleRoot k x = 0 :=
  Iff.rfl

@[simp]
lemma mem_openAlcoveFace {J : Set (Option b.support)} {x : N} :
    x ∈ b.openAlcoveFace J ↔
      (∀ k ∈ J, b.affineSimpleRoot k x = 0) ∧ ∀ k ∉ J, 0 < b.affineSimpleRoot k x :=
  Iff.rfl

lemma closedAlcoveFace_subset_closedFundamentalAlcove (J : Set (Option b.support)) :
    b.closedAlcoveFace J ⊆ closedFundamentalAlcove P b :=
  fun _ hx ↦ hx.1

@[simp]
lemma closedAlcoveFace_empty : b.closedAlcoveFace ∅ = closedFundamentalAlcove P b := by
  ext x
  simp

lemma closedAlcoveFace_antitone : Antitone b.closedAlcoveFace :=
  fun _ _ hJ _ hx ↦ ⟨hx.1, fun k hk ↦ hx.2 k (hJ hk)⟩

/-- Intersecting two closed faces takes the union of their wall sets. -/
theorem closedAlcoveFace_union (J₁ J₂ : Set (Option b.support)) :
    b.closedAlcoveFace (J₁ ∪ J₂) = b.closedAlcoveFace J₁ ∩ b.closedAlcoveFace J₂ := by
  ext x
  exact ⟨fun ⟨hx, h⟩ ↦
      ⟨⟨hx, fun k hk ↦ h k (.inl hk)⟩, ⟨hx, fun k hk ↦ h k (.inr hk)⟩⟩,
    fun ⟨⟨hx, h₁⟩, _, h₂⟩ ↦ ⟨hx, fun k hk ↦ hk.elim (h₁ k) (h₂ k)⟩⟩

/-- Intersecting a nonempty family of closed faces takes the union of their wall sets. -/
theorem closedAlcoveFace_iUnion {α : Sort*} [Nonempty α] (J : α → Set (Option b.support)) :
    b.closedAlcoveFace (⋃ a, J a) = ⋂ a, b.closedAlcoveFace (J a) := by
  ext x
  simp only [mem_closedAlcoveFace, mem_iUnion, mem_iInter, forall_exists_index]
  exact ⟨fun ⟨hx, h⟩ a ↦ ⟨hx, fun k hk ↦ h k a hk⟩,
    fun h ↦ ⟨(h (Classical.arbitrary α)).1, fun k a hk ↦ (h a).2 k hk⟩⟩

/-- All walls of the fundamental alcove cannot meet simultaneously, by the null-root relation
`∑ₖ mₖ aₖ = 1`. -/
@[simp]
theorem closedAlcoveFace_univ : b.closedAlcoveFace univ = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x ⟨_, h0⟩ ↦ zero_ne_one (α := R) ?_
  simpa [h0 _ (mem_univ _)] using b.sum_affineMarks_mul_affineSimpleRoot x

/-- The origin lies in the open face `b.openAlcoveFace {none}ᶜ` where every simple root vanishes
and `θ < 1`. -/
theorem zero_mem_openAlcoveFace_compl_singleton_none [ZeroLEOneClass R] :
    (0 : N) ∈ b.openAlcoveFace {none}ᶜ := by
  refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
  · rcases k with _ | i
    · exact absurd rfl hk
    · simp
  · obtain rfl : k = none := notMem_compl_iff.mp hk
    simp

/-- On `b.closedAlcoveFace {k}ᶜ`, where every affine simple root other than `aₖ` vanishes, the
null-root relation reduces to `mₖ * aₖ(x) = 1`. -/
private lemma affineMarks_mul_affineSimpleRoot_eq_one {k : Option b.support} {x : N}
    (hx : x ∈ b.closedAlcoveFace {k}ᶜ) :
    (b.affineMarks k : R) * b.affineSimpleRoot k x = 1 := by
  classical
  have hnull := b.sum_affineMarks_mul_affineSimpleRoot x
  rwa [Finset.sum_eq_single k (fun l _ hlk ↦ by rw [hx.2 l hlk, mul_zero]) (by simp)] at hnull

/-- For a root system, the vertex face `b.closedAlcoveFace {k}ᶜ` opposite the wall `k` contains at
most one point. -/
theorem subsingleton_closedAlcoveFace_compl_singleton [P.IsRootSystem]
    (k : Option b.support) : (b.closedAlcoveFace {k}ᶜ).Subsingleton := by
  intro x hx y hy
  have heq (l : Option b.support) : b.affineSimpleRoot l x = b.affineSimpleRoot l y := by
    rcases eq_or_ne l k with rfl | hlk
    · calc b.affineSimpleRoot l x
          = ((b.affineMarks l : R) * b.affineSimpleRoot l y) * b.affineSimpleRoot l x := by
            rw [b.affineMarks_mul_affineSimpleRoot_eq_one hy, one_mul]
        _ = b.affineSimpleRoot l y * ((b.affineMarks l : R) * b.affineSimpleRoot l x) := by ring
        _ = b.affineSimpleRoot l y := by
            rw [b.affineMarks_mul_affineSimpleRoot_eq_one hx, mul_one]
    · rw [hx.2 l hlk, hy.2 l hlk]
  exact b.fundamentalCoweightBasis.ext_elem fun i ↦ by simpa using heq (some i)

/-- For a root system, the vertex of the closed fundamental alcove opposite the affine wall `θ = 1`
is `{0}`. -/
@[simp]
theorem closedAlcoveFace_compl_singleton_none [ZeroLEOneClass R] [P.IsRootSystem] :
    b.closedAlcoveFace {none}ᶜ = {0} := by
  have h0 : (0 : N) ∈ b.closedAlcoveFace {none}ᶜ := by
    refine ⟨⟨fun _ _ ↦ by simp, by simp⟩, ?_⟩
    rintro (_ | i) hi
    · exact absurd rfl hi
    · simp
  exact Subset.antisymm (fun _ hx ↦ mem_singleton_iff.mpr
    (b.subsingleton_closedAlcoveFace_compl_singleton none hx h0)) (singleton_subset_iff.mpr h0)

/-- For a root system, a point `x : N` with `0 ≤ P.root' j x` and `b.affineSimpleRoot l x = 0` for
all `l ≠ some j` is the unique point of the closed vertex face `b.closedAlcoveFace {some j}ᶜ`. -/
private lemma closedAlcoveFace_compl_singleton_some_eq_singleton [P.IsRootSystem]
    {j : b.support} {x : N} (hj : 0 ≤ P.root' j x)
    (h0 : ∀ l ≠ some j, b.affineSimpleRoot l x = 0) :
    b.closedAlcoveFace {some j}ᶜ = {x} := by
  have hmem : x ∈ b.closedAlcoveFace {some j}ᶜ := by
    refine ⟨⟨fun i hi ↦ ?_, ?_⟩, fun l hl ↦ h0 l (mem_compl_singleton_iff.mp hl)⟩
    · by_cases hij : (⟨i, hi⟩ : b.support) = j
      · rcases hij with rfl
        exact hj
      · have hzero : b.affineSimpleRoot (some ⟨i, hi⟩) x = 0 := h0 _ (by simp [hij])
        rw [affineSimpleRoot_some] at hzero
        exact hzero.ge
    · have hnone : b.affineSimpleRoot none x = 0 := h0 none (by simp)
      rw [affineSimpleRoot_none, sub_eq_zero] at hnone
      exact hnone.ge
  exact Subset.antisymm (fun _ hy ↦ mem_singleton_iff.mpr
    (b.subsingleton_closedAlcoveFace_compl_singleton (some j) hy hmem))
    (singleton_subset_iff.mpr hmem)

/-- For a root system, at a special simple node `j`, the vertex of the closed fundamental alcove
opposite the wall `αⱼ = 0` is `{b.fundamentalCoweightBasis j}`. -/
theorem closedAlcoveFace_compl_singleton_some_of_mem_specialNodes [ZeroLEOneClass R]
    [P.IsRootSystem] {j : b.support} (hj : some j ∈ b.specialNodes) :
    b.closedAlcoveFace {some j}ᶜ = {b.fundamentalCoweightBasis j} := by
  classical
  have hj_pos : 0 ≤ P.root' j (b.fundamentalCoweightBasis j) := by simp [zero_le_one]
  have h0 : ∀ l ≠ some j, b.affineSimpleRoot l (b.fundamentalCoweightBasis j) = 0 :=
    fun l hl ↦ by simp [b.affineSimpleRoot_fundamentalCoweightBasis_of_mem_specialNodes hj, hl]
  exact b.closedAlcoveFace_compl_singleton_some_eq_singleton hj_pos h0

section OrderedAdd

variable [IsOrderedAddMonoid R]

@[simp]
lemma openAlcoveFace_empty : b.openAlcoveFace ∅ = fundamentalAlcove P b := by
  ext x
  rw [mem_fundamentalAlcove_iff_forall_affineSimpleRoot_pos b]
  simp

lemma openAlcoveFace_subset_closedAlcoveFace (J : Set (Option b.support)) :
    b.openAlcoveFace J ⊆ b.closedAlcoveFace J := by
  rintro x ⟨h0, hpos⟩
  refine ⟨(mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg b).mpr
    fun k ↦ ?_, h0⟩
  by_cases hk : k ∈ J
  · exact (h0 k hk).ge
  · exact (hpos k hk).le

lemma openAlcoveFace_subset_closedFundamentalAlcove (J : Set (Option b.support)) :
    b.openAlcoveFace J ⊆ closedFundamentalAlcove P b :=
  (b.openAlcoveFace_subset_closedAlcoveFace J).trans
    (b.closedAlcoveFace_subset_closedFundamentalAlcove J)

@[simp]
theorem openAlcoveFace_univ : b.openAlcoveFace univ = ∅ :=
  eq_empty_of_subset (b.openAlcoveFace_subset_closedAlcoveFace univ) b.closedAlcoveFace_univ

/-- On `{k}ᶜ`, where every affine simple root other than `aₖ` vanishes, the open and closed faces
coincide. -/
theorem openAlcoveFace_compl_singleton_eq_closedAlcoveFace (k : Option b.support) :
    b.openAlcoveFace {k}ᶜ = b.closedAlcoveFace {k}ᶜ := by
  refine Subset.antisymm (b.openAlcoveFace_subset_closedAlcoveFace _) fun x hx ↦ ⟨hx.2, ?_⟩
  intro l hl
  obtain rfl : l = k := notMem_compl_iff.mp hl
  refine ((mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg b).mp hx.1 l).lt_of_ne'
    fun h0 ↦ ?_
  have hxuniv : x ∈ b.closedAlcoveFace univ :=
    ⟨hx.1, fun m _ ↦ (eq_or_ne m l).elim (fun h ↦ h ▸ h0) (hx.2 m)⟩
  simp at hxuniv

/-- A point of the closed fundamental alcove lies in the open face `b.openAlcoveFace J` precisely
when `J` is the set of walls passing through it. -/
theorem mem_openAlcoveFace_iff_eq_setOf_eq_zero {J : Set (Option b.support)} {x : N}
    (hx : x ∈ closedFundamentalAlcove P b) :
    x ∈ b.openAlcoveFace J ↔ J = {k | b.affineSimpleRoot k x = 0} := by
  have hnn := (mem_closedFundamentalAlcove_iff_forall_affineSimpleRoot_nonneg b).mp hx
  refine ⟨fun ⟨h0, hpos⟩ ↦ Set.ext fun k ↦
      ⟨fun hk ↦ h0 k hk, fun hk ↦ by_contra fun hnot ↦ (hpos k hnot).ne' hk⟩,
    fun hJ ↦ ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩⟩
  · rw [hJ] at hk
    exact hk
  · rw [hJ] at hk
    exact (hnn k).lt_of_ne' (by simpa using hk)

/-- **The open faces partition the closed fundamental alcove.** -/
theorem iUnion_openAlcoveFace :
    ⋃ J : Set (Option b.support), b.openAlcoveFace J = closedFundamentalAlcove P b := by
  refine Subset.antisymm
    (iUnion_subset fun J ↦ b.openAlcoveFace_subset_closedFundamentalAlcove J) fun x hx ↦ ?_
  exact mem_iUnion.mpr ⟨{k | b.affineSimpleRoot k x = 0},
    (b.mem_openAlcoveFace_iff_eq_setOf_eq_zero hx).mpr rfl⟩

/-- Open faces associated with distinct sets of affine nodes are disjoint. -/
theorem pairwise_disjoint_openAlcoveFace : Pairwise (Disjoint on b.openAlcoveFace) := by
  intro J₁ J₂ hne
  refine disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ?_
  have hx := b.openAlcoveFace_subset_closedFundamentalAlcove J₁ hx₁
  rw [(b.mem_openAlcoveFace_iff_eq_setOf_eq_zero hx).mp hx₁,
    (b.mem_openAlcoveFace_iff_eq_setOf_eq_zero hx).mp hx₂]

end OrderedAdd

end Base

end CommRingFaces

/-! ### Nonemptiness and vertices over a linearly ordered field -/

section Field

variable {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base)

/-- On `b.closedAlcoveFace {k}ᶜ`, where every affine simple root other than `aₖ` vanishes, the
remaining affine simple root `aₖ` takes the value `1 / mₖ`. -/
theorem Base.affineSimpleRoot_eq_inv_affineMarks_of_mem_closedAlcoveFace_compl_singleton
    [PartialOrder R] [CharZero R] [Finite ι] [Nonempty ι]
    {k : Option b.support} {x : N} (hx : x ∈ b.closedAlcoveFace {k}ᶜ) :
    b.affineSimpleRoot k x = (b.affineMarks k : R)⁻¹ :=
  eq_inv_of_mul_eq_one_right (b.affineMarks_mul_affineSimpleRoot_eq_one hx)

/-- Over a field, any tuple `a : Option b.support → R` satisfying the null-root relation
`∑ k, mₖ aₖ = 1` is realized as `b.affineSimpleRoot · x` at some point `x : N`. -/
theorem Base.exists_forall_affineSimpleRoot_eq [CharZero R] [Finite ι] [Nonempty ι]
    {a : Option b.support → R} (ha : ∑ k, (b.affineMarks k : R) * a k = 1) :
    ∃ x : N, ∀ k, b.affineSimpleRoot k x = a k := by
  classical
  obtain ⟨x, hx⟩ := b.exists_forall_root'_eq fun i ↦
    if h : i ∈ b.support then a (some ⟨i, h⟩) else 0
  refine ⟨x, ?_⟩
  have hsome (i : b.support) : b.affineSimpleRoot (some i) x = a (some i) := by
    simpa [i.property] using hx i i.property
  have hnull := b.sum_affineMarks_mul_affineSimpleRoot x
  rw [Fintype.sum_option] at hnull ha
  simp only [Base.affineMarks_none, Int.cast_one, one_mul, hsome] at hnull ha
  have hnone : b.affineSimpleRoot none x = a none :=
    add_right_cancel (hnull.trans ha.symm)
  rintro (_ | i)
  · exact hnone
  · exact hsome i

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
  · rw [Base.affineSimpleRoot_some, hx₀', Base.height_one_of_mem_support i.property]
    simpa using hD

/-- Over a linearly ordered field the fundamental alcove is nonempty: it contains the point at which
every simple root takes the value `1 / (ht(θ) + 1)`. -/
theorem fundamentalAlcove_nonempty [Finite ι] [Nonempty ι] :
    (fundamentalAlcove P b).Nonempty :=
  let ⟨x₀, hx₀, _⟩ := exists_mem_fundamentalAlcove_root'_eq_height_div b
  ⟨x₀, hx₀⟩

section IrreducibleFaces

variable [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- **An open face `b.openAlcoveFace J` is nonempty if and only if `J` is a proper subset of the
affine nodes (`J ≠ univ`).** -/
theorem Base.openAlcoveFace_nonempty_iff {J : Set (Option b.support)} :
    (b.openAlcoveFace J).Nonempty ↔ J ≠ univ := by
  classical
  refine ⟨fun ⟨x, hx⟩ hJ ↦ by simp [hJ] at hx, fun hJ ↦ ?_⟩
  -- Let `c = ∑_{k ∉ J} mₖ > 0`; choose `x` with `aₖ(x) = 0` on `J` and `aₖ(x) = c⁻¹` off `J`.
  obtain ⟨k₀, hk₀⟩ := (ne_univ_iff_exists_notMem J).mp hJ
  let c : R := ∑ k : Option b.support, if k ∈ J then 0 else (b.affineMarks k : R)
  have hc : 0 < c := Finset.sum_pos'
    (fun k _ ↦ by split_ifs <;> positivity [b.affineMarks_pos k])
    ⟨k₀, Finset.mem_univ k₀, by simpa [hk₀] using b.affineMarks_pos k₀⟩
  let a : Option b.support → R := fun k ↦ if k ∈ J then 0 else c⁻¹
  have ha : ∑ k, (b.affineMarks k : R) * a k = 1 := by
    calc ∑ k, (b.affineMarks k : R) * a k
        = c * c⁻¹ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          dsimp [a]
          split_ifs <;> simp
      _ = 1 := mul_inv_cancel₀ hc.ne'
  obtain ⟨x, hx⟩ := b.exists_forall_affineSimpleRoot_eq ha
  exact ⟨x, fun k hk ↦ by simp [hx k, a, hk],
    fun k hk ↦ by simpa [hx k, a, hk] using inv_pos.mpr hc⟩

/-- **A closed face `b.closedAlcoveFace J` is nonempty if and only if `J ≠ univ`.** -/
theorem Base.closedAlcoveFace_nonempty_iff {J : Set (Option b.support)} :
    (b.closedAlcoveFace J).Nonempty ↔ J ≠ univ :=
  ⟨fun ⟨x, hx⟩ hJ ↦ by simp [hJ] at hx, fun hJ ↦
    (b.openAlcoveFace_nonempty_iff.mpr hJ).mono (b.openAlcoveFace_subset_closedAlcoveFace J)⟩

/-- For a reduced irreducible crystallographic root system over a linearly ordered field, the vertex
of the closed fundamental alcove opposite the simple wall `αⱼ = 0` is `mⱼ⁻¹ • ϖⱼ`, where
`mⱼ = b.affineMarks (some j)` and `ϖⱼ = b.fundamentalCoweightBasis j`. -/
@[simp]
theorem Base.closedAlcoveFace_compl_singleton_some [P.IsRootSystem] (j : b.support) :
    b.closedAlcoveFace {some j}ᶜ =
      {(b.affineMarks (some j) : R)⁻¹ • b.fundamentalCoweightBasis j} := by
  classical
  have hm : (0 : R) < b.affineMarks (some j) := Int.cast_pos.mpr (b.affineMarks_pos (some j))
  let v : N := (b.affineMarks (some j) : R)⁻¹ • b.fundamentalCoweightBasis j
  have hcoord (k : Option b.support) :
      b.affineSimpleRoot k v = if k = some j then (b.affineMarks (some j) : R)⁻¹ else 0 := by
    rcases k with _ | i
    · simp [v, inv_mul_cancel₀ hm.ne']
    · by_cases hij : i = j <;> simp [v, hij]
  have hj_pos : 0 ≤ P.root' j v := by
    have := hcoord (some j)
    simp only [Base.affineSimpleRoot_some, ↓reduceIte] at this
    rw [this]
    exact inv_nonneg.mpr hm.le
  exact b.closedAlcoveFace_compl_singleton_some_eq_singleton hj_pos
    fun l hl ↦ by rw [hcoord l, ite_eq_right hl]

end IrreducibleFaces

end Field

end RootPairing
