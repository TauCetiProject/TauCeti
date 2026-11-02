/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineCartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Alcove

/-!
# The affine simple roots

Let `b` be a base of a finite root pairing `P`, with simple roots `αᵢ`, highest root `θ` and
fundamental alcove

`A = {x | αᵢ(x) > 0 for every simple root αᵢ, and θ(x) < 1}`.

The **affine simple roots** (`RootPairing.Base.affineSimpleRoot'`) are the affine functions on the
coweight space indexed by the nodes of the affine Dynkin diagram: `αᵢ` at a simple node `i`, and
`α₀ = 1 - θ` at the affine node. For a reduced irreducible crystallographic pairing over a linearly
ordered field their zero sets are the walls of `A`: the alcove is the set of points at which all of
them are positive (`RootPairing.Base.mem_fundamentalAlcove_iff_forall_affineSimpleRoot'_pos`), and
with the marks `mₖ` of the affine Cartan matrix they satisfy the null-root relation
`∑ₖ mₖ αₖ = 1` (`RootPairing.Base.sum_affineMarks_mul_affineSimpleRoot'`).

Every affine root `αⱼ - c`, with `c` an integer, that is positive on `A` is a nonnegative integer
combination `∑ₗ nₗ αₗ` of the affine simple roots: `αⱼ - c` is `αⱼ` for a positive root `αⱼ` and
`c = 0`, and otherwise `c ≤ -1` and `αⱼ - c = (αⱼ + θ) + α₀ + (-c - 1)`, where
`αⱼ + θ = θ - (-αⱼ)` is a nonnegative combination of the simple roots and `1 = α₀ + θ`.

## Main definitions

* `RootPairing.Base.affineSimpleRoot'`: the affine simple roots, as functions on the coweight
  space.

## Main results

* `RootPairing.Base.mem_fundamentalAlcove_iff_forall_affineSimpleRoot'_pos`: the fundamental
  alcove is the set of points at which every affine simple root is positive.
* `RootPairing.Base.sum_affineMarks_mul_affineSimpleRoot'`: the null-root relation
  `∑ₖ mₖ αₖ = 1`.
* `RootPairing.Base.affineSimpleRoot'_injective`: distinct nodes have distinct affine simple
  roots.
* `RootPairing.Base.exists_forall_affineSimpleRoot'_eq`: some point of the coweight space has all
  affine simple roots equal to `1 / ∑ₖ mₖ`.
* `RootPairing.Base.exists_root'_sub_eq_sum_nat_mul_affineSimpleRoot'`: an affine root positive on
  the fundamental alcove is a nonnegative integer combination of the affine simple roots.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §2 (the fundamental alcove
  and its walls) and §4.3 (the marks).
-/

public section

open Set

namespace RootPairing

/-! ### The affine simple roots -/

namespace Base

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [CharZero R] [Finite ι] [Nonempty ι] (b : P.Base)

/-- The **affine simple roots** of a base, as affine functions on the coweight space, indexed by
the nodes of the affine Dynkin diagram: the simple root `αᵢ` at a simple node `i`, and
`α₀ = 1 - θ` at the affine node, where `θ` is the highest root. For a reduced irreducible root
pairing their zero sets are the walls of the fundamental alcove. -/
noncomputable def affineSimpleRoot' : Option b.support → N → R
  | none, x => 1 - P.root' b.highestRoot x
  | some i, x => P.root' i x

@[simp]
theorem affineSimpleRoot'_none (x : N) :
    b.affineSimpleRoot' none x = 1 - P.root' b.highestRoot x :=
  (rfl)

@[simp]
theorem affineSimpleRoot'_some (i : b.support) (x : N) :
    b.affineSimpleRoot' (some i) x = P.root' i x :=
  (rfl)

/-- The difference of the values of an affine simple root at two points is the value at their
difference of the root functional of `RootPairing.Base.affineSimpleRootIndex`: its linear part is
`αᵢ` at a simple node and `-θ` at the affine node. -/
theorem affineSimpleRoot'_sub_affineSimpleRoot' (k : Option b.support) (x y : N) :
    b.affineSimpleRoot' k x - b.affineSimpleRoot' k y =
      P.root' (b.affineSimpleRootIndex k) (x - y) := by
  rcases k with _ | i <;> simp

/-- Every affine simple root is an affine root `αⱼ - c`, with `c` an integer. -/
theorem exists_affineSimpleRoot'_eq (k : Option b.support) :
    ∃ (j : ι) (c : ℤ), ∀ x, b.affineSimpleRoot' k x = P.root' j x - c := by
  rcases k with _ | i
  · exact ⟨P.reflectionPerm b.highestRoot b.highestRoot, -1, fun x ↦ by simp; ring⟩
  · exact ⟨i, 0, fun x ↦ by simp⟩

/-- **The null-root relation**: the affine simple roots, weighted by the marks of the affine Cartan
matrix, sum to the constant function `1`, since `θ = ∑ᵢ mᵢ αᵢ` and `α₀ = 1 - θ`. -/
theorem sum_affineMarks_mul_affineSimpleRoot' (x : N) :
    ∑ k, (b.affineMarks k : R) * b.affineSimpleRoot' k x = 1 := by
  have hθ : P.root' b.highestRoot x =
      ∑ i : b.support, (b.affineMarks (some i) : R) * P.root' i x := by
    rw [root', b.root_highestRoot_eq_sum_affineMarks, map_sum, LinearMap.sum_apply]
    simp [zsmul_eq_mul]
  rw [Fintype.sum_option, affineMarks_none, affineSimpleRoot'_none, hθ]
  simp only [affineSimpleRoot'_some, Int.cast_one]
  ring

/-- **Distinct nodes have distinct affine simple roots.** The affine simple root of the affine
node is the only one taking the value `1` at `0`, and distinct simple roots give distinct
functionals on the coweight space, since the root pairing is perfect. -/
theorem affineSimpleRoot'_injective : Function.Injective b.affineSimpleRoot' := by
  rintro (_ | i) (_ | j) h
  · rfl
  · simpa using congrFun h 0
  · simpa using congrFun h 0
  · have h' : P.root' i = P.root' j := LinearMap.ext (congrFun h)
    exact congrArg some (Subtype.ext (P.root.injective
      ((LinearMap.IsPerfPair.bijective_left P.toLinearMap).1 h')))

/-- **The fundamental alcove is the set of points at which every affine simple root is
positive.** -/
theorem mem_fundamentalAlcove_iff_forall_affineSimpleRoot'_pos [LinearOrder R]
    [IsStrictOrderedRing R] {x : N} :
    x ∈ fundamentalAlcove P b ↔ ∀ k, 0 < b.affineSimpleRoot' k x := by
  rw [mem_fundamentalAlcove]
  refine ⟨fun hx k ↦ ?_, fun h ↦ ⟨fun i hi ↦ h (some ⟨i, hi⟩), by simpa using h none⟩⟩
  rcases k with _ | i
  · simpa using hx.2
  · exact hx.1 i i.2

end CommRing

section Field

variable {ι R M N : Type*} [Field R] [CharZero R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] {P : RootPairing ι R M N} [Finite ι] [Nonempty ι] (b : P.Base)

/-- The sum of the marks is nonzero in a field of characteristic zero. -/
private lemma sum_affineMarks_cast_ne_zero : ∑ k, (b.affineMarks k : R) ≠ 0 := by
  rw [← Int.cast_sum]
  exact_mod_cast b.sum_affineMarks_pos.ne'

/-- There is a point of the coweight space at which every affine simple root takes the value
`1 / h`, where `h = ∑ₖ mₖ` is the sum of the marks. -/
theorem exists_forall_affineSimpleRoot'_eq :
    ∃ x : N, ∀ k, b.affineSimpleRoot' k x = (∑ k, (b.affineMarks k : R))⁻¹ := by
  have hh := b.sum_affineMarks_cast_ne_zero
  obtain ⟨x, hx⟩ := b.exists_forall_root'_eq fun _ ↦ (∑ k, (b.affineMarks k : R))⁻¹
  have hsome (i : b.support) :
      b.affineSimpleRoot' (some i) x = (∑ k, (b.affineMarks k : R))⁻¹ := hx i i.2
  refine ⟨x, fun k ↦ ?_⟩
  rcases k with _ | i
  · have hsplit : ∑ k, (b.affineMarks k : R) =
        1 + ∑ i : b.support, (b.affineMarks (some i) : R) := by
      rw [Fintype.sum_option, affineMarks_none, Int.cast_one]
    have hrel := b.sum_affineMarks_mul_affineSimpleRoot' x
    rw [Fintype.sum_option, affineMarks_none, Int.cast_one, one_mul] at hrel
    simp only [hsome, ← Finset.sum_mul] at hrel
    rw [hsplit] at hrel hh ⊢
    rw [eq_sub_of_add_eq hrel]
    field_simp
    ring
  · exact hsome i

end Field

/-! ### Affine roots positive on the alcove are nonnegative combinations of the walls -/

section OrderedField

variable {ι R M N : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M] [AddCommGroup N] [Module R N] {P : RootPairing ι R M N} [Finite ι] [Nonempty ι]
  (b : P.Base)

/-- The nonnegative integer combinations of the affine simple roots, as functions on the coweight
space. -/
private noncomputable def wallCone : AddSubmonoid (N → R) :=
  AddSubmonoid.closure (range b.affineSimpleRoot')

private lemma affineSimpleRoot'_mem_wallCone (k : Option b.support) :
    b.affineSimpleRoot' k ∈ wallCone b :=
  AddSubmonoid.subset_closure ⟨k, rfl⟩

/-- A nonnegative combination of the simple roots is a nonnegative combination of the affine
simple roots. -/
private lemma toLinearMap_mem_wallCone {m : M} (hm : m ∈ TauCeti.posRootCone P b) :
    ⇑(P.toLinearMap m) ∈ wallCone b := by
  obtain ⟨f, rfl⟩ := (TauCeti.mem_posRootCone P b).mp hm
  rw [map_sum, LinearMap.coe_sum]
  refine sum_mem fun i hi ↦ ?_
  rw [map_nsmul, LinearMap.coe_smul]
  exact nsmul_mem (affineSimpleRoot'_mem_wallCone b (some ⟨i, hi⟩)) _

variable [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-- An affine root positive at a point of the fundamental alcove lies in the cone. -/
private lemma mem_wallCone {x₀ : N} (hx₀ : x₀ ∈ fundamentalAlcove P b) {j : ι} {c : ℤ}
    (hc : (c : R) < P.root' j x₀) : (fun x ↦ P.root' j x - c) ∈ wallCone b := by
  have hθ : ⇑(P.root' b.highestRoot) ∈ wallCone b :=
    toLinearMap_mem_wallCone b (TauCeti.root_mem_posRootCone_of_mem_posRoots P b
      ((TauCeti.mem_posRoots P b _).mpr b.isPos_highestRoot))
  have hone : (fun _ ↦ (1 : R)) ∈ wallCone b := by
    have : (fun _ : N ↦ (1 : R)) = b.affineSimpleRoot' none + ⇑(P.root' b.highestRoot) := by
      ext x
      simp
    rw [this]
    exact add_mem (affineSimpleRoot'_mem_wallCone b none) hθ
  have hc1 : c < 1 := by
    exact_mod_cast hc.trans (root'_lt_one_of_mem_fundamentalAlcove hx₀ j)
  rcases (show c = 0 ∨ c ≤ -1 by omega) with rfl | hc0
  · -- `αⱼ` is positive on the alcove, so it is a positive root
    have hj : b.IsPos j := by
      by_contra hj
      exact (root'_neg_of_not_isPos ((mem_fundamentalAlcove P b).mp hx₀).1 hj).not_gt
        (by simpa using hc)
    have : (fun x ↦ P.root' j x - ((0 : ℤ) : R)) = ⇑(P.toLinearMap (P.root j)) := by
      ext x
      simp
    rw [this]
    exact toLinearMap_mem_wallCone b
      (TauCeti.root_mem_posRootCone_of_mem_posRoots P b ((TauCeti.mem_posRoots P b _).mpr hj))
  · -- `αⱼ - c = (θ - (-αⱼ)) + α₀ + (-c - 1)`
    have hsum := toLinearMap_mem_wallCone b
      (b.root_highestRoot_sub_mem_posRootCone (P.reflectionPerm j j))
    have : (fun x ↦ P.root' j x - c) =
        ⇑(P.toLinearMap (P.root b.highestRoot - P.root (P.reflectionPerm j j))) +
          b.affineSimpleRoot' none + (-c - 1).toNat • fun _ ↦ (1 : R) := by
      ext x
      have hcast : (((-c).toNat - 1 : ℕ) : R) = -c - 1 := by
        exact_mod_cast (show (((-c).toNat - 1 : ℕ) : ℤ) = -c - 1 by omega)
      simp [hcast]
      ring
    rw [this]
    exact add_mem (add_mem hsum (affineSimpleRoot'_mem_wallCone b none)) (nsmul_mem hone _)

/-- **An affine root positive on the fundamental alcove is a nonnegative integer combination of the
affine simple roots**: if `αⱼ - c`, with `c` an integer, is positive at a point of the
fundamental alcove, then `αⱼ - c = ∑ₖ nₖ αₖ` with natural numbers `nₖ`. -/
theorem exists_root'_sub_eq_sum_nat_mul_affineSimpleRoot' {x₀ : N}
    (hx₀ : x₀ ∈ fundamentalAlcove P b) {j : ι} {c : ℤ} (hc : (c : R) < P.root' j x₀) :
    ∃ n : Option b.support → ℕ,
      ∀ x, P.root' j x - c = ∑ k, (n k : R) * b.affineSimpleRoot' k x := by
  have h := mem_wallCone b hx₀ hc
  rw [wallCone, ← Submodule.span_nat_eq_addSubmonoidClosure, Submodule.mem_toAddSubmonoid,
    Submodule.mem_span_range_iff_exists_fun] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun x ↦ ?_⟩
  rw [← congrFun hn x, Finset.sum_apply]
  simp [nsmul_eq_mul]

end OrderedField

end Base

end RootPairing
