/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Unit
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Multiplication

/-!
# `A∞` deformations of a zigzag algebra supported on closed walks

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as a cohomologically graded algebra: vertex idempotents in degree `0`, arrows in
degree `1` and volume classes in degree `2`. This is the regrading of an arrow to bidegree
`(1, -1)`, read in the cohomological component.

A **loop operation** is attached to `n ≥ 1` darts `w 0, …, w (n - 1)` of `G`. It is the
`n`-linear map

```text
m_w(x₀, …, x_{n-1}) = a_{w 0}(x₀) ⋯ a_{w (n - 1)}(x_{n-1}) · x_v,
```

where `a_d` is the coordinate of the arrow of `d` in the vertex-arrow-volume basis and `x_v` is the
volume class at the head `v` of `w 0`. On arrows it is nonzero only on the word `w` itself. When
the darts form a closed walk, read in Tau Ceti's later-factor-first order (`w (n - 1)` is traversed
first, and `(w i).fst = (w (i + 1)).snd` cyclically), the operation is a Hochschild cocycle
(`TauCeti.zigzagLoopOperation_cocycle`). Its coboundary telescopes, because the arrow coordinate of
a product only sees the idempotents at the two ends of the arrow
(`TauCeti.zigzagBasis_coord_dart_mul`). Moreover `m_w ∘ m_w` vanishes, since `m_w` takes values in
the volume classes, which have no arrow coordinates.

Consequently, for `n ≥ 3`, every finite linear combination `μ` of loop operations of closed walks of
length `n` gives an `A∞` algebra `TauCeti.zigzagLoopAInfinityAlgebra` on `Z`. Its operations are
`m₁ = 0`, `m₂` the product, `mₙ = μ`, and `m r = 0` otherwise. It is minimal and strictly unital
with unit `1`, so it is a strictly unital minimal `A∞` deformation of the strict zigzag algebra. Its
operation `m r` has cohomological degree `2 - r`, and degree `r - 2` for the Adams grading, which is
the negative of path length. For walks of length one or two the coefficients are not used: there
are no closed walks of length one in a simple graph, and the loop operation of a closed walk of
length two, a backtrack, would change the product rather than add a higher operation.

Such deformations include the quartic operation of Liu--Wang's Example 4.7 for affine `D₄`; see
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.AffineD.Four`. Longer closed walks give
higher operations: for instance, closed walks of lengths `6`, `8` and `12` match the path degrees
of the nonzero cyclic classes of the preprojective algebras of the affine `E₆`, `E₇` and `E₈`
graphs.

Some of the quartic deformations are trivial modulo `A∞` isomorphism
(`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Backtrack`) and, when `2` is invertible,
some are not (`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.NonFormal`).

## Main definitions

* `TauCeti.zigzagLoopOperation`: the loop operation of `n` darts.
* `TauCeti.zigzagLoopAInfinityAlgebra`: the `A∞` algebra with `m₂` the product and `mₙ` a
  linear combination of loop operations of closed walks of length `n`.
* `TauCeti.zigzagStrictAInfinityAlgebra`: the strict zigzag algebra, the loop deformation with
  zero coefficients.

## Main results

* `TauCeti.zigzagLoopOperation_ofArrow`: a loop operation is nonzero on arrows only on its own
  word, where it is the volume class at the base of the walk.
* `TauCeti.zigzagLoopOperation_cocycle`: the loop operation of a closed walk is a Hochschild
  cocycle.
* `TauCeti.zigzagLoopAInfinityAlgebra_m_two_apply`,
  `TauCeti.zigzagLoopAInfinityAlgebra_m_eq_linearCombination` and
  `TauCeti.zigzagLoopAInfinityAlgebra_m_eq_zero`: the operations.
* `TauCeti.zigzagLoopAInfinityAlgebra_m_mem`: the higher operation takes values in the volume
  classes.
* `TauCeti.zigzagLoopAInfinityAlgebra_grading_eq`: the grading depends neither on the
  coefficients nor on the length of the walks.
* `TauCeti.zigzagStrictAInfinityAlgebra_m_two_apply` and
  `TauCeti.zigzagStrictAInfinityAlgebra_m_eq_zero`: the strict zigzag algebra has no operation
  besides the product `m₂`.
* `TauCeti.isMinimal_zigzagLoopAInfinityAlgebra` and
  `TauCeti.strictUnit_one_zigzagLoopAInfinityAlgebra`: the algebra is minimal and strictly unital.
* `TauCeti.isHomogeneous_zigzagLoopAInfinityAlgebra_m_adams`: the Adams degree of `m r` is
  `r - 2`.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Section 4, for minimal `A∞` deformations of zigzag algebras and Example 4.7.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the Stasheff
  identities.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity _root_.MultilinearMap

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (hns : ∀ i : V, ∃ j, G.Adj i j)

/-! ### Loop operations -/

variable {n : ℕ} [NeZero n]

/-- The **loop operation** of `n` darts `w`: the product of the `w i`-arrow coordinates of the
`n` inputs, times the volume class at the head of `w 0`. -/
noncomputable def zigzagLoopOperation (w : Fin n → G.Dart) :
    MultilinearMap k (fun _ : Fin n ↦ nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G) :=
  ((MultilinearMap.mkPiAlgebra k (Fin n) k).compLinearMap
    fun i ↦ (zigzagBasis k G hns).coord (.inr (.inl (w i)))).smulRight
      (zigzagVolume k G (w 0).snd)

/-- A loop operation is the product of the arrow coordinates of its inputs, times the volume class
at the head of `w 0`. -/
@[simp]
theorem zigzagLoopOperation_apply (w : Fin n → G.Dart)
    (x : Fin n → nonisolatedZigzagQuotient k G) :
    zigzagLoopOperation k G hns w x =
      (∏ i, (zigzagBasis k G hns).coord (.inr (.inl (w i))) (x i)) •
        zigzagVolume k G (w 0).snd := by
  simp [zigzagLoopOperation]

open scoped Classical in
/-- **A loop operation on arrows**: on the arrows of `n` darts `d`, the loop operation of `w` is
the volume class at the head of `w 0` when `d = w`, and zero otherwise. -/
theorem zigzagLoopOperation_ofArrow (w d : Fin n → G.Dart) :
    zigzagLoopOperation k G hns w (fun i ↦ zigzagMk k G (ofArrow (arrow G (d i).adj))) =
      if d = w then zigzagVolume k G (w 0).snd else 0 := by
  classical
  have harrow (i : Fin n) : zigzagMk k G (ofArrow (arrow G (d i).adj)) =
      zigzagBasis k G hns (.inr (.inl (d i))) := by simp
  simp only [zigzagLoopOperation_apply, harrow, zigzagBasis_coord_apply, Sum.inr.injEq,
    Sum.inl.injEq, Finset.prod_boole, Finset.mem_univ, true_implies]
  split_ifs with h h' h' <;> simp_all [funext_iff]

/-! ### The cocycle identity -/

/-- The darts of `w`, extended periodically to all natural numbers. -/
private def walkNat (w : Fin n → G.Dart) (i : ℕ) : G.Dart :=
  w ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩

omit [Finite V] in
private theorem walkNat_coe (w : Fin n → G.Dart) (i : Fin n) : walkNat G w i = w i := by
  simp [walkNat, Nat.mod_eq_of_lt i.isLt]

omit [Finite V] in
private theorem walkNat_zero (w : Fin n → G.Dart) : walkNat G w 0 = w 0 := by
  simp [walkNat]

omit [Finite V] in
private theorem walkNat_self (w : Fin n → G.Dart) : walkNat G w n = w 0 := by
  simp [walkNat]

omit [Finite V] in
private theorem walkNat_fst {w : Fin n → G.Dart} (hw : ∀ i, (w i).fst = (w (i + 1)).snd)
    (i : ℕ) : (walkNat G w i).fst = (walkNat G w (i + 1)).snd := by
  have h : (⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) + 1 =
      ⟨(i + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
    ext
    simp only [Fin.val_add, Fin.val_one', Nat.mod_add_mod, Nat.add_mod_mod]
  rw [walkNat, walkNat, hw, h]

private theorem evalNat_zigzagLoopOperation (w : Fin n → G.Dart)
    (y : ℕ → nonisolatedZigzagQuotient k G) :
    evalNat (zigzagLoopOperation k G hns w) y =
      (∏ i ∈ Finset.range n, (zigzagBasis k G hns).coord (.inr (.inl (walkNat G w i))) (y i)) •
        zigzagVolume k G (w 0).snd := by
  rw [evalNat_def, zigzagLoopOperation_apply, Finset.prod_range]
  simp only [walkNat_coe]

/-- **The loop operation of a closed walk is a Hochschild cocycle.** For a closed walk `w` of
length `n` and inputs `x 0, …, x n`, with `L = m_w`,

```text
∑_{p < n} (-1)^p L(x₀, …, x_p x_{p+1}, …, x_n) + (-1)^n L(x₀, …, x_{n-1}) x_n - x₀ L(x₁, …, x_n)
```

vanishes. The `p`-th term is the sum of the terms in which the vertex idempotent at the `p`-th or
`(p + 1)`-st vertex of the walk is inserted, so the alternating sum telescopes. -/
theorem zigzagLoopOperation_cocycle {w : Fin n → G.Dart}
    (hw : ∀ i, (w i).fst = (w (i + 1)).snd) (x : ℕ → nonisolatedZigzagQuotient k G) :
    ∑ p ∈ Finset.range n, negOnePowCast k (p : ℤ) •
        evalNat (zigzagLoopOperation k G hns w) (replaceBlock x p 2 (x p * x (p + 1))) +
      negOnePowCast k (n : ℤ) • (evalNat (zigzagLoopOperation k G hns w) x * x n) -
        x 0 * evalNat (zigzagLoopOperation k G hns w) (fun j ↦ x (1 + j)) = 0 := by
  have hmerge : ∀ p ∈ Finset.range n,
      negOnePowCast k (p : ℤ) •
        evalNat (zigzagLoopOperation k G hns w) (replaceBlock x p 2 (x p * x (p + 1))) =
      (negOnePowCast k (p : ℤ) *
        ((∏ i ∈ Finset.range p, (zigzagBasis k G hns).coord (.inr (.inl (walkNat G w i))) (x i)) *
          ((zigzagBasis k G hns).coord (.inl (walkNat G w p).snd) (x p) *
              (zigzagBasis k G hns).coord (.inr (.inl (walkNat G w p))) (x (p + 1)) +
            (zigzagBasis k G hns).coord (.inr (.inl (walkNat G w p))) (x p) *
              (zigzagBasis k G hns).coord (.inl (walkNat G w (p + 1)).snd) (x (p + 1))) *
          ∏ i ∈ Finset.Ico (p + 1) n,
            (zigzagBasis k G hns).coord (.inr (.inl (walkNat G w i))) (x (i + 1)))) •
        zigzagVolume k G (w 0).snd := by
    intro p hp
    have hp := Finset.mem_range.1 hp
    rw [evalNat_zigzagLoopOperation, ← Finset.prod_range_mul_prod_Ico _ hp.le,
      Finset.prod_eq_prod_Ico_succ_bot hp, ← mul_assoc, replaceBlock_self,
      zigzagBasis_coord_dart_mul, walkNat_fst G hw, smul_smul]
    refine congrArg₂ _ (congrArg₂ _ rfl (congrArg₂ _ (congrArg₂ _
      (Finset.prod_congr rfl fun i hi ↦ ?_) rfl) (Finset.prod_congr rfl fun i hi ↦ ?_))) rfl
    · rw [replaceBlock_of_lt _ _ _ _ (Finset.mem_range.1 hi)]
    · rw [Finset.mem_Ico] at hi
      rw [replaceBlock_of_gt _ _ _ _ (by omega), show i + 2 - 1 = i + 1 by omega]
  have h₀ : x 0 * zigzagVolume k G (w 0).snd =
      (zigzagBasis k G hns).coord (.inl (walkNat G w 0).snd) (x 0) •
        zigzagVolume k G (w 0).snd := by
    rw [mul_zigzagVolume hns, walkNat_zero]
  have hn : zigzagVolume k G (w 0).snd * x n =
      (zigzagBasis k G hns).coord (.inl (walkNat G w n).snd) (x n) •
        zigzagVolume k G (w 0).snd := by
    rw [zigzagVolume_mul hns, walkNat_self]
  have hshift : ∏ i ∈ Finset.range n,
      (zigzagBasis k G hns).coord (.inr (.inl (walkNat G w i))) (x (1 + i)) =
      ∏ i ∈ Finset.range n,
        (zigzagBasis k G hns).coord (.inr (.inl (walkNat G w i))) (x (i + 1)) :=
    Finset.prod_congr rfl fun i _ ↦ by rw [add_comm]
  rw [Finset.sum_congr rfl hmerge, ← Finset.sum_smul, sum_range_negOnePowCast_telescope,
    evalNat_zigzagLoopOperation, evalNat_zigzagLoopOperation, smul_mul_assoc, hn,
    mul_smul_comm, h₀, hshift]
  module

/-! ### The operations of the deformation -/

/-- The operations of the deformation attached to `c`: the product in arity two, the linear
combination of loop operations with coefficients `c` in arity `n` when `3 ≤ n`, and zero
otherwise. -/
private noncomputable def loopOps (c : (Fin n → G.Dart) →₀ k) (m : ℕ) :
    MultilinearMap k (fun _ : Fin m ↦ nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G) :=
  if h₂ : m = 2 then
    ((MultilinearMap.ofSubsingletonₗ k k (nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G) (0 : Fin 1) ∘ₗ
        LinearMap.mul k (nonisolatedZigzagQuotient k G)).uncurryLeft).domDomCongr
      (finCongr h₂.symm)
  else if h : m = n ∧ 3 ≤ n then
    (Finsupp.linearCombination k (zigzagLoopOperation k G hns) c).domDomCongr (finCongr h.1.symm)
  else 0

variable {k G hns}

variable (c : (Fin n → G.Dart) →₀ k)

private theorem loopOps_two_apply (x : Fin 2 → nonisolatedZigzagQuotient k G) :
    loopOps k G hns c 2 x = x 0 * x 1 := by
  simp [loopOps, LinearMap.uncurryLeft_apply, Fin.tail]

private theorem loopOps_self (hn : 3 ≤ n) :
    loopOps k G hns c n = Finsupp.linearCombination k (zigzagLoopOperation k G hns) c := by
  rw [loopOps]
  split_ifs with h₂ h
  · omega
  · ext
    simp
  · exact absurd ⟨rfl, hn⟩ h

private theorem loopOps_apply_self (hn : 3 ≤ n) (x : Fin n → nonisolatedZigzagQuotient k G) :
    loopOps k G hns c n x = ∑ w ∈ c.support,
      (c w * ∏ i, (zigzagBasis k G hns).coord (.inr (.inl (w i))) (x i)) •
        zigzagVolume k G (w 0).snd := by
  simp [loopOps_self c hn, Finsupp.linearCombination_apply, Finsupp.sum, smul_smul]

private theorem loopOps_eq_zero {m : ℕ} (h₂ : m ≠ 2) (h : m = n → n < 3) :
    loopOps k G hns c m = 0 := by
  rw [loopOps]
  split_ifs with h₂' h'
  · exact absurd h₂' h₂
  · have := h h'.1
    omega
  · rfl

private theorem loopOps_zero : loopOps k G hns c 0 = 0 :=
  loopOps_eq_zero c (by decide) fun h ↦ by have := NeZero.ne n; omega

/-- The higher operation takes values in the span of the volume classes, which have no arrow
coordinates. -/
private theorem coord_dart_loopOps {m : ℕ} (h₂ : m ≠ 2) (d : G.Dart)
    (x : Fin m → nonisolatedZigzagQuotient k G) :
    (zigzagBasis k G hns).coord (.inr (.inl d)) (loopOps k G hns c m x) = 0 := by
  by_cases h : m = n ∧ 3 ≤ n
  · obtain ⟨rfl, hn⟩ := h
    simp only [loopOps_apply_self c hn, _root_.map_sum, map_smul,
      zigzagBasis_coord_dart_zigzagVolume, smul_zero, Finset.sum_const_zero]
  · rw [loopOps_eq_zero c h₂ fun h' ↦ by omega, _root_.zero_apply, _root_.map_zero]

/-- The higher operation vanishes as soon as one input has no arrow coordinates. -/
private theorem loopOps_eq_zero_of_coord {m : ℕ} (h₂ : m ≠ 2)
    (x : Fin m → nonisolatedZigzagQuotient k G) (j : Fin m)
    (hj : ∀ d : G.Dart, (zigzagBasis k G hns).coord (.inr (.inl d)) (x j) = 0) :
    loopOps k G hns c m x = 0 := by
  by_cases h : m = n ∧ 3 ≤ n
  · obtain ⟨rfl, hn⟩ := h
    rw [loopOps_apply_self c hn]
    refine Finset.sum_eq_zero fun w _ ↦ ?_
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (hj (w j)), mul_zero, zero_smul]
  · rw [loopOps_eq_zero c h₂ fun h' ↦ by omega, _root_.zero_apply]

/-! ### Degrees -/

/-- The path-length grading of the zigzag quotient, as an internal integer grading. -/
private noncomputable def loopGrading : InternalGrading k (nonisolatedZigzagQuotient k G) :=
  ⟨zigzagIntegerGrade k G, isInternal_zigzagIntegerGrade k G⟩

private theorem isHomogeneous_loopOps (m : ℕ) :
    MultilinearMap.IsHomogeneous (loopOps k G hns c m) (fun _ ↦ zigzagIntegerGrade k G)
      (zigzagIntegerGrade k G) (2 - m) := by
  classical
  rw [MultilinearMap.isHomogeneous_def]
  intro e x hx
  by_cases h₂ : m = 2
  · subst h₂
    rw [loopOps_two_apply, Fin.sum_univ_two]
    simpa using mul_mem_zigzagIntegerGrade k G (hx 0) (hx 1)
  by_cases he : ∀ i, e i = 1
  · by_cases h : m = n ∧ 3 ≤ n
    · obtain ⟨rfl, hn⟩ := h
      rw [loopOps_apply_self c hn]
      refine Submodule.sum_mem _ fun w _ ↦ Submodule.smul_mem _ _ ?_
      convert zigzagVolume_mem_zigzagIntegerGrade_two k G (w 0).snd using 2
      simp [he]
    · rw [loopOps_eq_zero c h₂ fun h' ↦ by omega, _root_.zero_apply]
      exact Submodule.zero_mem _
  · obtain ⟨j, hj⟩ := not_forall.mp he
    rw [loopOps_eq_zero_of_coord c h₂ x j fun d ↦
      zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade k G hns d hj (hx j)]
    exact Submodule.zero_mem _

/-! ### The Stasheff identities -/

/-- A composite whose inner operation is the higher operation vanishes unless the outer one is the
product, since the higher operation takes values in the volume classes. -/
private theorem stasheffTerm_loopOps_self {p t : ℕ} (h : p + 1 + t ≠ 2) (e : ℕ → ℤ)
    (x : ℕ → nonisolatedZigzagQuotient k G) :
    stasheffTerm (loopOps k G hns c) e x p n t = 0 := by
  rcases eq_or_ne n 2 with hn | hn
  · exact stasheffTerm_eq_zero_of_outer_eq_zero _ _ _ (loopOps_eq_zero c h fun h' ↦ by omega)
  rw [stasheffTerm_def, evalNat_def,
    loopOps_eq_zero_of_coord c h _ ⟨p, Nat.lt_add_right t (Nat.lt_succ_self p)⟩ fun d ↦ ?_,
    smul_zero]
  simp only [replaceBlock_self, evalNat_def]
  exact coord_dart_loopOps c hn d _

/-- **The arity-`n + 1` Stasheff sum**: only the composites of the product with the higher
operation remain, with their Stasheff signs. -/
private theorem stasheffSum_loopOps_succ (hn : 3 ≤ n) (e : ℕ → ℤ)
    (x : ℕ → nonisolatedZigzagQuotient k G) :
    stasheffSum (loopOps k G hns c) e x (n + 1) =
      ∑ p ∈ Finset.range n, negOnePowCast k (p : ℤ) •
          evalNat (loopOps k G hns c n) (replaceBlock x p 2 (x p * x (p + 1))) +
        negOnePowCast k (n : ℤ) • (evalNat (loopOps k G hns c n) x * x n) +
        negOnePowCast k (1 + (2 - n) * e 0) •
          (x 0 * evalNat (loopOps k G hns c n) fun j ↦ x (1 + j)) := by
  have hinner : ∀ p ∈ Finset.range (n + 1 + 1),
      ∑ s ∈ Finset.Icc 1 (n + 1 - p), stasheffTerm (loopOps k G hns c) e x p s (n + 1 - p - s) =
        stasheffTerm (loopOps k G hns c) e x p 2 (n + 1 - p - 2) +
          stasheffTerm (loopOps k G hns c) e x p n (n + 1 - p - n) := by
    intro p hp
    rw [Finset.mem_range] at hp
    refine Finset.sum_eq_add 2 n (by omega) (fun s _ hs ↦ ?_) (fun h ↦ ?_) (fun h ↦ ?_)
    · exact stasheffTerm_eq_zero_of_inner_eq_zero _ _ _
        (loopOps_eq_zero c hs.1 fun h ↦ absurd h hs.2)
    · rw [Finset.mem_Icc] at h
      exact stasheffTerm_eq_zero_of_outer_eq_zero _ _ _
        (loopOps_eq_zero c (by omega) fun h' ↦ by omega)
    · rw [Finset.mem_Icc] at h
      exact stasheffTerm_loopOps_self c (by omega) e x
  have hA : ∑ p ∈ Finset.range (n + 1 + 1),
      stasheffTerm (loopOps k G hns c) e x p 2 (n + 1 - p - 2) =
        ∑ p ∈ Finset.range n, negOnePowCast k (p : ℤ) •
          evalNat (loopOps k G hns c n) (replaceBlock x p 2 (x p * x (p + 1))) := by
    have hz : ∀ p, n ≤ p → stasheffTerm (loopOps k G hns c) e x p 2 (n + 1 - p - 2) = 0 :=
      fun p hp ↦ stasheffTerm_eq_zero_of_outer_eq_zero _ _ _
        (loopOps_eq_zero c (by omega) fun h ↦ by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hz n le_rfl, hz (n + 1) (by omega),
      add_zero, add_zero]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.mem_range] at hp
    rw [stasheffTerm_of_even _ _ _ even_two, show p + 1 + (n + 1 - p - 2) = n by omega,
      evalNat_two, loopOps_two_apply]
    simp only [add_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hB : ∑ p ∈ Finset.range (n + 1 + 1),
      stasheffTerm (loopOps k G hns c) e x p n (n + 1 - p - n) =
        negOnePowCast k (n : ℤ) • (evalNat (loopOps k G hns c n) x * x n) +
          negOnePowCast k (1 + (2 - n) * e 0) •
            (x 0 * evalNat (loopOps k G hns c n) fun j ↦ x (1 + j)) := by
    rw [Finset.sum_eq_add 0 1 (by omega)
      (fun p _ hp ↦ stasheffTerm_loopOps_self c (by omega) e x) (by simp) (by simp),
      show n + 1 - 0 - n = 1 by omega, show n + 1 - 1 - n = 0 by omega, stasheffTerm_def,
      stasheffTerm_def]
    simp only [Nat.cast_zero, Nat.cast_one, Finset.range_zero, Finset.sum_empty,
      Finset.sum_range_one, mul_zero, add_zero, zero_add, mul_one, Nat.reduceAdd, evalNat_two,
      loopOps_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      replaceBlock_self, replaceBlock_of_gt _ _ _ _ zero_lt_one,
      replaceBlock_of_lt _ _ _ _ zero_lt_one, add_tsub_cancel_left]
  rw [stasheffSum_def, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, hA, hB, add_assoc]

/-- The arity-three identity is associativity, since `m₁` vanishes. -/
private theorem stasheffSum_loopOps_three (e : ℕ → ℤ) (x : ℕ → nonisolatedZigzagQuotient k G) :
    stasheffSum (loopOps k G hns c) e x 3 = 0 := by
  have h₁ : loopOps k G hns c 1 = 0 := loopOps_eq_zero c (by decide) fun h ↦ by omega
  rw [stasheffSum_three, h₁]
  simp only [_root_.zero_apply, loopOps_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [(loopOps k G hns c 3).map_coord_zero 0 rfl, (loopOps k G hns c 3).map_coord_zero 1 rfl,
    (loopOps k G hns c 3).map_coord_zero 2 rfl]
  simp [mul_assoc]

/-- **The coboundary of the higher operation vanishes**: the arity-`n + 1` Stasheff identity, with
only the product and the higher operation present. -/
private theorem stasheffSum_loopOps_succ_eq_zero
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) (hn : 3 ≤ n) (e : ℕ → ℤ)
    (x : ℕ → nonisolatedZigzagQuotient k G) (hx : x 0 ∈ zigzagIntegerGrade k G (e 0)) :
    stasheffSum (loopOps k G hns c) e x (n + 1) = 0 := by
  -- the Koszul sign `(-1) ^ ((2 - n) e₀)` is harmless: `x₀` multiplies a volume class
  have hsign : negOnePowCast k (1 + (2 - n) * e 0) •
      (x 0 * evalNat (loopOps k G hns c n) fun j ↦ x (1 + j)) =
      -(x 0 * evalNat (loopOps k G hns c n) fun j ↦ x (1 + j)) := by
    by_cases he : e 0 = 0
    · rw [he, mul_zero, add_zero, negOnePowCast_one, neg_one_smul]
    · have hzero : x 0 * evalNat (loopOps k G hns c n) (fun j ↦ x (1 + j)) = 0 := by
        rw [evalNat_def, loopOps_apply_self c hn, Finset.mul_sum]
        refine Finset.sum_eq_zero fun w _ ↦ ?_
        rw [mul_smul_comm, mul_zigzagVolume hns,
          zigzagBasis_coord_vertex_eq_zero_of_mem_zigzagIntegerGrade k G hns _ he hx,
          zero_smul, smul_zero]
      rw [hzero, smul_zero, neg_zero]
  rw [stasheffSum_loopOps_succ c hn, hsign, loopOps_self c hn, ← sub_eq_add_neg]
  have hsum (y : ℕ → nonisolatedZigzagQuotient k G) :
      evalNat (Finsupp.linearCombination k (zigzagLoopOperation k G hns) c) y =
        ∑ w ∈ c.support, c w • evalNat (zigzagLoopOperation k G hns w) y := by
    simp [evalNat_def, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [hsum, Finset.smul_sum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun w hw ↦ ?_
  have h := zigzagLoopOperation_cocycle k G hns (hc w hw) x
  simp only [smul_comm (negOnePowCast k _) (c w)]
  rw [← Finset.smul_sum, ← smul_add, ← smul_sub, h, smul_zero]

private theorem stasheffSum_loopOps (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (r : ℕ) (e : ℕ → ℤ) (x : ℕ → nonisolatedZigzagQuotient k G)
    (hx : ∀ i < r, x i ∈ zigzagIntegerGrade k G (e i)) :
    stasheffSum (loopOps k G hns c) e x r = 0 := by
  by_cases h₃ : r = 3
  · subst h₃
    exact stasheffSum_loopOps_three c e x
  by_cases hr : r = n + 1 ∧ 3 ≤ n
  · obtain ⟨rfl, hn⟩ := hr
    exact stasheffSum_loopOps_succ_eq_zero c hc hn e x (hx 0 (by omega))
  -- every other term has an inner or an outer operation which vanishes, or is `mₙ ∘ mₙ`
  rw [stasheffSum_def]
  refine Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun s hs ↦ ?_
  rw [Finset.mem_range] at hp
  rw [Finset.mem_Icc] at hs
  by_cases hsn : s = n ∧ 3 ≤ n
  · obtain ⟨rfl, hn⟩ := hsn
    exact stasheffTerm_loopOps_self c (by omega) e x
  by_cases hs₂ : s = 2
  · subst hs₂
    exact stasheffTerm_eq_zero_of_outer_eq_zero _ _ _
      (loopOps_eq_zero c (by omega) fun h ↦ by omega)
  · exact stasheffTerm_eq_zero_of_inner_eq_zero _ _ _
      (loopOps_eq_zero c hs₂ fun h ↦ by omega)

/-! ### The `A∞` algebra -/

variable (hns) in
/-- **The loop deformation of a zigzag algebra.** For coefficients `c` supported on closed walks
of length `n ≥ 3`, read in product order, this is the `A∞` algebra on the zigzag quotient of `G`.
It has the path-length grading, `m₂` the product, `mₙ` the linear combination of the loop
operations `TauCeti.zigzagLoopOperation` with coefficients `c`, and every other operation zero.
For `n ≤ 2` the coefficients are not used, and this is the strict zigzag algebra. -/
noncomputable def zigzagLoopAInfinityAlgebra
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    AInfinityAlgebra k (nonisolatedZigzagQuotient k G) :=
  AInfinityAlgebra.ofStasheff loopGrading (loopOps k G hns c) (loopOps_zero c)
    (fun m _ ↦ isHomogeneous_loopOps c m)
    (AInfinity.suspensionTaylor _ _) (AInfinity.isSuspension_suspensionTaylor _ _)
    (fun r _ e x hx ↦ stasheffSum_loopOps c hc r e x hx)

variable (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)

private theorem zigzagLoopAInfinityAlgebra_m :
    (zigzagLoopAInfinityAlgebra hns c hc).m = loopOps k G hns c := by
  unfold zigzagLoopAInfinityAlgebra
  exact AInfinityAlgebra.ofStasheff_m _ _ _ _ _ _ _

/-- The loop deformation is graded by path length. -/
@[simp]
theorem zigzagLoopAInfinityAlgebra_grading_piece :
    (zigzagLoopAInfinityAlgebra hns c hc).grading.piece = zigzagIntegerGrade k G := by
  unfold zigzagLoopAInfinityAlgebra
  exact congrArg InternalGrading.piece (AInfinityAlgebra.ofStasheff_grading _ _ _ _ _ _ _)

/-- The grading of a loop deformation depends neither on its coefficients nor on the length of
its walks. -/
theorem zigzagLoopAInfinityAlgebra_grading_eq {n' : ℕ} [NeZero n']
    (c' : (Fin n' → G.Dart) →₀ k)
    (hc' : ∀ w ∈ c'.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    (zigzagLoopAInfinityAlgebra hns c hc).grading =
      (zigzagLoopAInfinityAlgebra hns c' hc').grading :=
  InternalGrading.ext fun p ↦ by simp

/-- The binary operation of the loop deformation is the product of the zigzag algebra. -/
@[simp]
theorem zigzagLoopAInfinityAlgebra_m_two_apply (x : Fin 2 → nonisolatedZigzagQuotient k G) :
    (zigzagLoopAInfinityAlgebra hns c hc).m 2 x = x 0 * x 1 := by
  rw [zigzagLoopAInfinityAlgebra_m, loopOps_two_apply]

/-- For `n ≥ 3`, the operation of arity `n` of the loop deformation is the linear combination of
loop operations with coefficients `c`. -/
theorem zigzagLoopAInfinityAlgebra_m_eq_linearCombination (hn : 3 ≤ n) :
    (zigzagLoopAInfinityAlgebra hns c hc).m n =
      Finsupp.linearCombination k (zigzagLoopOperation k G hns) c := by
  rw [zigzagLoopAInfinityAlgebra_m, loopOps_self c hn]

/-- The operation of arity `n ≥ 3` of the loop deformation takes values of degree two, in the
volume classes. -/
theorem zigzagLoopAInfinityAlgebra_m_mem (hn : 3 ≤ n) (y : Fin n → nonisolatedZigzagQuotient k G) :
    (zigzagLoopAInfinityAlgebra hns c hc).m n y ∈ zigzagIntegerGrade k G 2 := by
  rw [zigzagLoopAInfinityAlgebra_m, loopOps_apply_self c hn]
  exact Submodule.sum_mem _ fun w _ ↦
    Submodule.smul_mem _ _ (zigzagVolume_mem_zigzagIntegerGrade_two k G _)

/-- Every operation of the loop deformation other than `m₂` and `mₙ` vanishes. -/
theorem zigzagLoopAInfinityAlgebra_m_eq_zero {m : ℕ} (h₂ : m ≠ 2) (hn : m ≠ n) :
    (zigzagLoopAInfinityAlgebra hns c hc).m m = 0 := by
  rw [zigzagLoopAInfinityAlgebra_m, loopOps_eq_zero c h₂ fun h ↦ absurd h hn]

/-- **The higher operation on arrows**: for `n ≥ 3`, on the arrows of `n` darts `d`, the
operation of arity `n` of the loop deformation is the coefficient `c d` times the volume class at
the head of `d 0`. -/
theorem zigzagLoopAInfinityAlgebra_m_ofArrow (hn : 3 ≤ n) (d : Fin n → G.Dart) :
    (zigzagLoopAInfinityAlgebra hns c hc).m n
        (fun i ↦ zigzagMk k G (ofArrow (arrow G (d i).adj))) =
      c d • zigzagVolume k G (d 0).snd := by
  classical
  rw [zigzagLoopAInfinityAlgebra_m_eq_linearCombination c hc hn,
    Finsupp.linearCombination_apply, Finsupp.sum, _root_.sum_apply]
  simp only [_root_.smul_apply, zigzagLoopOperation_ofArrow, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.mp h, zero_smul]

/-- The loop deformation is minimal: its unary operation vanishes. -/
theorem isMinimal_zigzagLoopAInfinityAlgebra :
    (zigzagLoopAInfinityAlgebra hns c hc).IsMinimal := by
  rw [AInfinityAlgebra.isMinimal_iff_m_one_eq_zero]
  intro x
  rw [zigzagLoopAInfinityAlgebra_m, loopOps_eq_zero c (by decide) fun h ↦ by omega,
    _root_.zero_apply]

/-- **The loop deformation is strictly unital**, with the unit of the zigzag algebra as strict
unit: the higher operation vanishes when an input is `1`, which has no arrow coordinates. -/
theorem strictUnit_one_zigzagLoopAInfinityAlgebra :
    (zigzagLoopAInfinityAlgebra hns c hc).StrictUnit 1 := by
  have hone : (1 : nonisolatedZigzagQuotient k G) ∈ zigzagIntegerGrade k G ((0 : ℕ) : ℤ) := by
    let _ := zigzagGradedAlgebra k G
    rw [zigzagIntegerGrade_ofNat]
    exact SetLike.GradedOne.one_mem
  refine ⟨by simpa using hone, fun x ↦ by simp, fun x ↦ by simp, fun m h₂ x ⟨i, hi⟩ ↦ ?_⟩
  rw [zigzagLoopAInfinityAlgebra_m]
  refine loopOps_eq_zero_of_coord c h₂ x i fun d ↦ ?_
  rw [hi]
  exact zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade k G hns d (by decide) hone

/-- **The Adams degree of the loop deformation**: for the Adams grading, the negative of path
length, in which an arrow has degree `-1`, the operation `m r` is homogeneous of degree `r - 2`.
Together with its cohomological degree `2 - r`, this is the bidegree `(2 - r, r - 2)` of `m r` when
each arrow has bidegree `(1, -1)`. -/
theorem isHomogeneous_zigzagLoopAInfinityAlgebra_m_adams (r : ℕ) :
    MultilinearMap.IsHomogeneous ((zigzagLoopAInfinityAlgebra hns c hc).m r)
      (fun _ q ↦ zigzagIntegerGrade k G (-q)) (fun q ↦ zigzagIntegerGrade k G (-q))
      ((r : ℤ) - 2) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro e x hx
  have h := (isHomogeneous_loopOps (hns := hns) c r).map_mem (fun i ↦ -e i) x hx
  rw [← zigzagLoopAInfinityAlgebra_m c hc] at h
  rw [Finset.sum_neg_distrib] at h
  convert h using 2
  ring

/-! ### The strict zigzag algebra -/

variable (k hns) in
/-- **The strict zigzag algebra** as an `A∞` algebra: the loop deformation with zero coefficients,
graded by path length, with `m₂` the product and every other operation zero. -/
noncomputable def zigzagStrictAInfinityAlgebra :
    AInfinityAlgebra k (nonisolatedZigzagQuotient k G) :=
  zigzagLoopAInfinityAlgebra hns (0 : (Fin 4 → G.Dart) →₀ k) (by simp)

/-- The strict zigzag algebra is the loop deformation with zero coefficients. -/
theorem zigzagStrictAInfinityAlgebra_def :
    zigzagStrictAInfinityAlgebra k hns =
      zigzagLoopAInfinityAlgebra hns (0 : (Fin 4 → G.Dart) →₀ k) (by simp) := by
  rw [zigzagStrictAInfinityAlgebra]

/-- The strict zigzag algebra is graded by path length. -/
@[simp]
theorem zigzagStrictAInfinityAlgebra_grading_piece :
    (zigzagStrictAInfinityAlgebra k hns).grading.piece = zigzagIntegerGrade k G :=
  zigzagLoopAInfinityAlgebra_grading_piece _ _

/-- A loop deformation has the grading of the strict zigzag algebra. -/
theorem zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading :
    (zigzagLoopAInfinityAlgebra hns c hc).grading = (zigzagStrictAInfinityAlgebra k hns).grading :=
  zigzagLoopAInfinityAlgebra_grading_eq _ _ _ _

/-- The binary operation of the strict zigzag algebra is the product. -/
@[simp]
theorem zigzagStrictAInfinityAlgebra_m_two_apply (x : Fin 2 → nonisolatedZigzagQuotient k G) :
    (zigzagStrictAInfinityAlgebra k hns).m 2 x = x 0 * x 1 :=
  zigzagLoopAInfinityAlgebra_m_two_apply _ _ x

/-- A loop deformation has the binary operation of the strict zigzag algebra. -/
theorem zigzagLoopAInfinityAlgebra_m_two_eq_zigzagStrictAInfinityAlgebra_m_two :
    (zigzagLoopAInfinityAlgebra hns c hc).m 2 = (zigzagStrictAInfinityAlgebra k hns).m 2 :=
  MultilinearMap.ext fun x ↦ by
    rw [zigzagLoopAInfinityAlgebra_m_two_apply, zigzagStrictAInfinityAlgebra_m_two_apply]

/-- The strict zigzag algebra has no operation besides the product. -/
theorem zigzagStrictAInfinityAlgebra_m_eq_zero {m : ℕ} (hm : m ≠ 2) :
    (zigzagStrictAInfinityAlgebra k hns).m m = 0 := by
  rw [zigzagStrictAInfinityAlgebra_def]
  rcases eq_or_ne m 4 with rfl | h₄
  · rw [zigzagLoopAInfinityAlgebra_m_eq_linearCombination _ _ (by norm_num), _root_.map_zero]
  · exact zigzagLoopAInfinityAlgebra_m_eq_zero _ _ hm h₄

/-- The strict zigzag algebra is minimal. -/
theorem isMinimal_zigzagStrictAInfinityAlgebra :
    (zigzagStrictAInfinityAlgebra k hns).IsMinimal :=
  isMinimal_zigzagLoopAInfinityAlgebra _ _

end TauCeti
