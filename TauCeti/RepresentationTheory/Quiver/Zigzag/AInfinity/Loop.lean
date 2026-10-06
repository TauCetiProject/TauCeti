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
# Quartic `A∞` deformations of a zigzag algebra supported on closed walks

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as a cohomologically graded algebra: vertex idempotents in degree `0`, arrows in
degree `1` and volume classes in degree `2`. This is the regrading of an arrow to bidegree
`(1, -1)`, read in the cohomological component.

A **loop operation** is attached to four darts `w 0, w 1, w 2, w 3` of `G`. It is the
`4`-linear map

```text
m_w(x₀, x₁, x₂, x₃) = a_{w 0}(x₀) a_{w 1}(x₁) a_{w 2}(x₂) a_{w 3}(x₃) · x_v,
```

where `a_d` is the coordinate of the arrow of `d` in the vertex-arrow-volume basis and `x_v` is the
volume class at the head `v` of `w 0`. On arrows it is nonzero only on the word `w` itself. When
the darts form a closed walk, read in Tau Ceti's later-factor-first order (`w 3` is traversed
first, and `(w i).fst = (w (i + 1)).snd` cyclically), the operation is a Hochschild cocycle. Its
coboundary telescopes, because the arrow coordinate of a product only sees the idempotents at the
two ends of the arrow (`TauCeti.zigzagBasis_coord_dart_mul`). Moreover `m_w ∘ m_w` vanishes, since
`m_w` takes values in the volume classes, which have no arrow coordinates.

Consequently every finite linear combination `μ` of loop operations of closed walks gives an `A∞`
algebra `TauCeti.zigzagLoopAInfinityAlgebra` on `Z`. Its operations are `m₁ = 0`, `m₂` the
product, `m₄ = μ`, and `m n = 0` otherwise. It is minimal and strictly unital with unit `1`, so it
is a strictly unital minimal `A∞` deformation of the strict zigzag algebra. Its operation `m n`
has cohomological degree `2 - n`, and degree `n - 2` for the Adams grading, which is the negative
of path length. Such deformations include the operation of Liu--Wang's Example 4.7 for affine
`D₄`; see `TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.AffineD4`.

Nontriviality of such a deformation modulo `A∞` isomorphism is not addressed here.

## Main definitions

* `TauCeti.zigzagLoopOperation`: the quartic operation of four darts.
* `TauCeti.zigzagLoopAInfinityAlgebra`: the `A∞` algebra with `m₂` the product and `m₄` a
  linear combination of loop operations of closed walks.

## Main results

* `TauCeti.zigzagLoopOperation_ofArrow`: a loop operation is nonzero on arrows only on its own
  word, where it is the volume class at the base of the walk.
* `TauCeti.zigzagLoopAInfinityAlgebra_m_two_apply`, `TauCeti.zigzagLoopAInfinityAlgebra_m_four`
  and `TauCeti.zigzagLoopAInfinityAlgebra_m_eq_zero`: the operations.
* `TauCeti.isMinimal_zigzagLoopAInfinityAlgebra` and
  `TauCeti.strictUnit_one_zigzagLoopAInfinityAlgebra`: the algebra is minimal and strictly unital.
* `TauCeti.isHomogeneous_zigzagLoopAInfinityAlgebra_m_adams`: the Adams degree of `m n` is
  `n - 2`.

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

/-- The **loop operation** of four darts `w`: the product of the `w i`-arrow coordinates of the
four inputs, times the volume class at the head of `w 0`. -/
noncomputable def zigzagLoopOperation (w : Fin 4 → G.Dart) :
    MultilinearMap k (fun _ : Fin 4 ↦ nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G) :=
  ((MultilinearMap.mkPiAlgebra k (Fin 4) k).compLinearMap
    fun i ↦ (zigzagBasis k G hns).coord (.inr (.inl (w i)))).smulRight
      (zigzagVolume k G (w 0).snd)

/-- A loop operation is the product of the arrow coordinates of its inputs, times the volume class
at the head of `w 0`. -/
@[simp]
theorem zigzagLoopOperation_apply (w : Fin 4 → G.Dart)
    (x : Fin 4 → nonisolatedZigzagQuotient k G) :
    zigzagLoopOperation k G hns w x =
      (∏ i, (zigzagBasis k G hns).coord (.inr (.inl (w i))) (x i)) •
        zigzagVolume k G (w 0).snd := by
  simp [zigzagLoopOperation]

open scoped Classical in
/-- **A loop operation on arrows**: on the arrows of four darts `d`, the loop operation of `w` is
the volume class at the head of `w 0` when `d = w`, and zero otherwise. -/
theorem zigzagLoopOperation_ofArrow (w d : Fin 4 → G.Dart) :
    zigzagLoopOperation k G hns w (fun i ↦ zigzagMk k G (ofArrow (arrow G (d i).adj))) =
      if d = w then zigzagVolume k G (w 0).snd else 0 := by
  classical
  have harrow (i : Fin 4) : zigzagMk k G (ofArrow (arrow G (d i).adj)) =
      zigzagBasis k G hns (.inr (.inl (d i))) := by simp
  simp only [zigzagLoopOperation_apply, harrow, zigzagBasis_coord_apply, Sum.inr.injEq,
    Sum.inl.injEq, Finset.prod_boole, Finset.mem_univ, true_implies]
  split_ifs with h h' h' <;> simp_all [funext_iff]

/-! ### The operations of the deformation -/

/-- The operations of the deformation attached to `c`: the product in arity two, the linear
combination of loop operations with coefficients `c` in arity four, and zero otherwise. -/
private noncomputable def loopOps (c : (Fin 4 → G.Dart) →₀ k) :
    ∀ n : ℕ, MultilinearMap k (fun _ : Fin n ↦ nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G)
  | 0 => 0
  | 1 => 0
  | 2 => (MultilinearMap.ofSubsingletonₗ k k (nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G) (0 : Fin 1) ∘ₗ
        LinearMap.mul k (nonisolatedZigzagQuotient k G)).uncurryLeft
  | 3 => 0
  | 4 => Finsupp.linearCombination k (zigzagLoopOperation k G hns) c
  | _ + 5 => 0

variable {k G hns}

variable (c : (Fin 4 → G.Dart) →₀ k)

private theorem loopOps_two_apply (x : Fin 2 → nonisolatedZigzagQuotient k G) :
    loopOps k G hns c 2 x = x 0 * x 1 := by
  simp [loopOps, LinearMap.uncurryLeft_apply, Fin.tail]

private theorem loopOps_four_apply (x : Fin 4 → nonisolatedZigzagQuotient k G) :
    loopOps k G hns c 4 x = ∑ w ∈ c.support,
      (c w * ∏ i, (zigzagBasis k G hns).coord (.inr (.inl (w i))) (x i)) •
        zigzagVolume k G (w 0).snd := by
  simp [loopOps, Finsupp.linearCombination_apply, Finsupp.sum, smul_smul]

private theorem loopOps_zero : loopOps k G hns c 0 = 0 := (rfl)

private theorem loopOps_eq_zero {n : ℕ} (h₂ : n ≠ 2) (h₄ : n ≠ 4) : loopOps k G hns c n = 0 := by
  match n, h₂, h₄ with
  | 0, _, _ | 1, _, _ | 3, _, _ | _ + 5, _, _ => rfl

/-- The quartic operation takes values in the span of the volume classes, which have no arrow
coordinates. -/
private theorem coord_dart_loopOps_four (d : G.Dart) (x : Fin 4 → nonisolatedZigzagQuotient k G) :
    (zigzagBasis k G hns).coord (.inr (.inl d)) (loopOps k G hns c 4 x) = 0 := by
  simp only [loopOps_four_apply, _root_.map_sum, map_smul, zigzagBasis_coord_dart_zigzagVolume,
    smul_zero, Finset.sum_const_zero]

/-- The quartic operation vanishes as soon as one input has no arrow coordinates. -/
private theorem loopOps_four_eq_zero_of_coord (x : Fin 4 → nonisolatedZigzagQuotient k G)
    (j : Fin 4) (hj : ∀ d : G.Dart, (zigzagBasis k G hns).coord (.inr (.inl d)) (x j) = 0) :
    loopOps k G hns c 4 x = 0 := by
  rw [loopOps_four_apply]
  refine Finset.sum_eq_zero fun w _ ↦ ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (hj (w j)), mul_zero, zero_smul]

/-! ### Degrees -/

/-- The path-length grading of the zigzag quotient, as an internal integer grading. -/
private noncomputable def loopGrading : InternalGrading k (nonisolatedZigzagQuotient k G) :=
  ⟨zigzagIntegerGrade k G, isInternal_zigzagIntegerGrade k G⟩

private theorem isHomogeneous_loopOps (n : ℕ) :
    MultilinearMap.IsHomogeneous (loopOps k G hns c n) (fun _ ↦ zigzagIntegerGrade k G)
      (zigzagIntegerGrade k G) (2 - n) := by
  classical
  rw [MultilinearMap.isHomogeneous_def]
  intro e x hx
  rcases (by omega : n = 2 ∨ n = 4 ∨ (n ≠ 2 ∧ n ≠ 4)) with rfl | rfl | ⟨h₂, h₄⟩
  · rw [loopOps_two_apply, Fin.sum_univ_two]
    simpa using mul_mem_zigzagIntegerGrade k G (hx 0) (hx 1)
  · by_cases he : ∀ i, e i = 1
    · rw [loopOps_four_apply, Fin.sum_univ_four, he 0, he 1, he 2, he 3]
      refine Submodule.sum_mem _ fun w _ ↦ Submodule.smul_mem _ _ ?_
      have hv : zigzagVolume k G (w 0).snd ∈ zigzagIntegerGrade k G (2 : ℕ) := by
        rw [zigzagIntegerGrade_ofNat, zigzagGrade_two_eq_span_range_zigzagVolume]
        exact Submodule.subset_span ⟨_, rfl⟩
      convert hv using 2
      norm_num
    · obtain ⟨j, hj⟩ := not_forall.mp he
      rw [loopOps_four_eq_zero_of_coord c x j fun d ↦
        zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade k G hns d hj (hx j)]
      exact Submodule.zero_mem _
  · rw [loopOps_eq_zero c h₂ h₄, _root_.zero_apply]
    exact Submodule.zero_mem _

/-! ### The Stasheff identities -/

/-- The composite `m₄ ∘ m₄` vanishes, since `m₄` takes values in the volume classes. -/
private theorem stasheffTerm_four_four {p t : ℕ} (hpt : p + 1 + t = 4) (e : ℕ → ℤ)
    (x : ℕ → nonisolatedZigzagQuotient k G) :
    stasheffTerm (loopOps k G hns c) e x p 4 t = 0 := by
  rw [stasheffTerm_def]
  generalize hq : p + 1 + t = q
  obtain rfl : q = 4 := hq ▸ hpt
  rw [evalNat_def, loopOps_four_eq_zero_of_coord c _ ⟨p, by omega⟩ fun d ↦ ?_, smul_zero]
  simp only [replaceBlock_self, evalNat_def]
  exact coord_dart_loopOps_four c d _

/-- **The coboundary of the quartic operation vanishes**: the arity-five Stasheff identity, with
only the product and the quartic operation present. It telescopes walk by walk, by the product
rule `TauCeti.zigzagBasis_coord_dart_mul` for arrow coordinates. -/
private theorem loopOps_four_cocycle (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (x₀ x₁ x₂ x₃ x₄ : nonisolatedZigzagQuotient k G) :
    loopOps k G hns c 4 ![x₀ * x₁, x₂, x₃, x₄] - loopOps k G hns c 4 ![x₀, x₁ * x₂, x₃, x₄] +
        loopOps k G hns c 4 ![x₀, x₁, x₂ * x₃, x₄] -
          loopOps k G hns c 4 ![x₀, x₁, x₂, x₃ * x₄] +
        loopOps k G hns c 4 ![x₀, x₁, x₂, x₃] * x₄ -
          x₀ * loopOps k G hns c 4 ![x₁, x₂, x₃, x₄] = 0 := by
  simp only [loopOps_four_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, zigzagVolume_mul hns, mul_zigzagVolume hns, smul_smul,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun w hw ↦ ?_
  have h₀ := hc w hw 0
  have h₁ := hc w hw 1
  have h₂ := hc w hw 2
  have h₃ := hc w hw 3
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zigzagBasis_coord_dart_mul]
  simp only [zero_add, Fin.isValue, Fin.reduceAdd] at h₀ h₁ h₂ h₃
  rw [h₀, h₁, h₂, h₃]
  module

private theorem stasheffSum_loopOps (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)
    (n : ℕ) (e : ℕ → ℤ) (x : ℕ → nonisolatedZigzagQuotient k G) :
    stasheffSum (loopOps k G hns c) e x n = 0 := by
  rcases (by omega : n = 3 ∨ n = 5 ∨ (n ≠ 3 ∧ n ≠ 5)) with rfl | rfl | ⟨h₃, h₅⟩
  · -- arity three: associativity
    rw [stasheffSum_three_eq_zero_iff_of_m_three_eq_zero _ _ _ rfl]
    simp [loopOps_two_apply, mul_assoc]
  · -- arity five: the cocycle condition; every other term has an inner operation of odd arity
    have hodd {p s t : ℕ} (hs : s = 1 ∨ s = 3 ∨ s = 5) :
        stasheffTerm (loopOps k G hns c) e x p s t = 0 :=
      stasheffTerm_eq_zero_of_inner_eq_zero _ _ _ (loopOps_eq_zero c (by omega) (by omega))
    have hIcc (f : ℕ → nonisolatedZigzagQuotient k G) (m : ℕ) :
        ∑ s ∈ Finset.Icc 1 (m + 1), f s = ∑ s ∈ Finset.Icc 1 m, f s + f (m + 1) :=
      Finset.sum_Icc_succ_top (by omega) f
    simp only [stasheffSum_def, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      Nat.reduceAdd, Nat.reduceSub, hIcc, Finset.Icc_self, Finset.sum_singleton,
      Order.lt_one_iff, Finset.Icc_eq_empty_of_lt, zero_add, Nat.sub_self]
    simp only [hodd (s := 1) (by omega), hodd (s := 3) (by omega), hodd (s := 5) (by omega),
      stasheffTerm_of_even _ _ _ (by decide : Even 2),
      stasheffTerm_of_even _ _ _ (by decide : Even 4),
      add_zero, zero_add]
    have h₂ : negOnePowCast k (2 : ℤ) = 1 := negOnePowCast_two_mul 1
    have h₃ : negOnePowCast k (3 : ℤ) = -1 := negOnePowCast_odd (by decide)
    simp (disch := omega) only [Nat.reduceAdd, evalNat_two, evalNat_four, loopOps_two_apply,
      replaceBlock_self, replaceBlock_of_lt, replaceBlock_of_gt, Nat.reduceSub,
      Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, negOnePowCast_zero, negOnePowCast_one, h₂, h₃, one_smul, neg_smul]
    refine Eq.trans ?_ (loopOps_four_cocycle (hns := hns) c hc (x 0) (x 1) (x 2) (x 3) (x 4))
    abel
  · rw [stasheffSum_def]
    refine Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun s hs ↦ ?_
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Icc] at hs
    by_cases h44 : s = 4 ∧ p + 1 + (n - p - s) = 4
    · obtain ⟨rfl, h⟩ := h44
      exact stasheffTerm_four_four c h e x
    · rcases (by omega : (s ≠ 2 ∧ s ≠ 4) ∨
          (p + 1 + (n - p - s) ≠ 2 ∧ p + 1 + (n - p - s) ≠ 4)) with h | h
      · exact stasheffTerm_eq_zero_of_inner_eq_zero _ _ _ (loopOps_eq_zero c h.1 h.2)
      · exact stasheffTerm_eq_zero_of_outer_eq_zero _ _ _ (loopOps_eq_zero c h.1 h.2)

/-! ### The `A∞` algebra -/

variable (hns) in
/-- **The quartic loop deformation of a zigzag algebra.** For coefficients `c` supported on closed
walks of length four, read in product order, this is the `A∞` algebra on the zigzag quotient of
`G`. It has the path-length grading, `m₂` the product, `m₄` the linear combination of the loop
operations `TauCeti.zigzagLoopOperation` with coefficients `c`, and every other operation zero. -/
noncomputable def zigzagLoopAInfinityAlgebra
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    AInfinityAlgebra k (nonisolatedZigzagQuotient k G) :=
  AInfinityAlgebra.ofStasheff loopGrading (loopOps k G hns c) (loopOps_zero c)
    (fun n _ ↦ isHomogeneous_loopOps c n)
    (AInfinity.suspensionTaylor _ _) (AInfinity.isSuspension_suspensionTaylor _ _)
    (fun n _ e x _ ↦ stasheffSum_loopOps c hc n e x)

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

/-- The binary operation of the loop deformation is the product of the zigzag algebra. -/
@[simp]
theorem zigzagLoopAInfinityAlgebra_m_two_apply (x : Fin 2 → nonisolatedZigzagQuotient k G) :
    (zigzagLoopAInfinityAlgebra hns c hc).m 2 x = x 0 * x 1 := by
  rw [zigzagLoopAInfinityAlgebra_m, loopOps_two_apply]

/-- The quartic operation of the loop deformation is the linear combination of loop operations
with coefficients `c`. -/
theorem zigzagLoopAInfinityAlgebra_m_four :
    (zigzagLoopAInfinityAlgebra hns c hc).m 4 =
      Finsupp.linearCombination k (zigzagLoopOperation k G hns) c := by
  rw [zigzagLoopAInfinityAlgebra_m, loopOps]

/-- Every operation of the loop deformation other than `m₂` and `m₄` vanishes. -/
theorem zigzagLoopAInfinityAlgebra_m_eq_zero {n : ℕ} (h₂ : n ≠ 2) (h₄ : n ≠ 4) :
    (zigzagLoopAInfinityAlgebra hns c hc).m n = 0 := by
  rw [zigzagLoopAInfinityAlgebra_m, loopOps_eq_zero c h₂ h₄]

/-- **The quartic operation on arrows**: on the arrows of four darts `d`, the quartic operation of
the loop deformation is the coefficient `c d` times the volume class at the head of `d 0`. -/
theorem zigzagLoopAInfinityAlgebra_m_four_ofArrow (d : Fin 4 → G.Dart) :
    (zigzagLoopAInfinityAlgebra hns c hc).m 4
        (fun i ↦ zigzagMk k G (ofArrow (arrow G (d i).adj))) =
      c d • zigzagVolume k G (d 0).snd := by
  classical
  rw [zigzagLoopAInfinityAlgebra_m_four, Finsupp.linearCombination_apply, Finsupp.sum,
    _root_.sum_apply]
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
  rw [zigzagLoopAInfinityAlgebra_m_eq_zero c hc (by decide) (by decide), _root_.zero_apply]

/-- **The loop deformation is strictly unital**, with the unit of the zigzag algebra as strict
unit: the quartic operation vanishes when an input is `1`, which has no arrow coordinates. -/
theorem strictUnit_one_zigzagLoopAInfinityAlgebra :
    (zigzagLoopAInfinityAlgebra hns c hc).StrictUnit 1 := by
  have hone : (1 : nonisolatedZigzagQuotient k G) ∈ zigzagIntegerGrade k G ((0 : ℕ) : ℤ) := by
    let _ := zigzagGradedAlgebra k G
    rw [zigzagIntegerGrade_ofNat]
    exact SetLike.GradedOne.one_mem
  refine ⟨by simpa using hone, fun x ↦ by simp, fun x ↦ by simp, fun n h₂ x ⟨i, hi⟩ ↦ ?_⟩
  by_cases h₄ : n = 4
  · subst h₄
    rw [zigzagLoopAInfinityAlgebra_m]
    refine loopOps_four_eq_zero_of_coord c x i fun d ↦ ?_
    rw [hi]
    exact zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade k G hns d (by decide) hone
  · rw [zigzagLoopAInfinityAlgebra_m_eq_zero c hc h₂ h₄, _root_.zero_apply]

/-- **The Adams degree of the loop deformation**: for the Adams grading, the negative of path
length, in which an arrow has degree `-1`, the operation `m n` is homogeneous of degree `n - 2`.
Together with its cohomological degree `2 - n`, this is the bidegree `(2 - n, n - 2)` of `m n` when
each arrow has bidegree `(1, -1)`. -/
theorem isHomogeneous_zigzagLoopAInfinityAlgebra_m_adams (n : ℕ) :
    MultilinearMap.IsHomogeneous ((zigzagLoopAInfinityAlgebra hns c hc).m n)
      (fun _ q ↦ zigzagIntegerGrade k G (-q)) (fun q ↦ zigzagIntegerGrade k G (-q))
      ((n : ℤ) - 2) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro e x hx
  have h := (isHomogeneous_loopOps (hns := hns) c n).map_mem (fun i ↦ -e i) x hx
  rw [← zigzagLoopAInfinityAlgebra_m c hc] at h
  rw [Finset.sum_neg_distrib] at h
  convert h using 2
  ring

end TauCeti
