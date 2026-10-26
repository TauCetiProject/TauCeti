/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Formal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Component
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Loop

/-!
# Gauge-trivial quartic loop deformations of a zigzag algebra

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). For two darts `d` and `e` with `d.fst = e.snd`, the
**backtrack operation**

```text
ψ_{d,e}(x₀, x₁, x₂) = a_d(x₀) a_e(x₁) a_{e.symm}(x₂) · d,
```

with `a_d` the coordinate of the arrow of `d` in the vertex-arrow-volume basis, is a ternary
operation of degree `-2`. On arrows it is nonzero only on the word `d, e, e.symm`, which it sends to
`d`: the backtrack along `e` is removed. Its Hochschild coboundary

```text
x₀ ψ(x₁, x₂, x₃) - ψ(x₀ x₁, x₂, x₃) + ψ(x₀, x₁ x₂, x₃) - ψ(x₀, x₁, x₂ x₃) + ψ(x₀, x₁, x₂) x₃
```

is the sum of the loop operations `TauCeti.zigzagLoopOperation` of the closed walk
`d.symm, d, e, e.symm` and of its rotation `d, e, e.symm, d.symm`
(`TauCeti.zigzagBacktrackOperation_coboundary`). The proof is the telescoping of arrow coordinates
used for the cocycle property of loop operations.

Let `P` be a finite set of such pairs, with weights `a`, and suppose that no first dart of a pair is
reverse to the first dart of another, so that the products of two values of the weighted
backtrack cochain `ψ = ∑ a_p ψ_p` vanish. Then the loop deformation
`TauCeti.zigzagLoopAInfinityAlgebra` whose coefficients are the weighted backtrack walks and their
rotations is **gauge trivial**. The maps `f₁ = id`, `f₃ = ψ` and `fₙ = 0` otherwise are the
components of an `A∞` morphism to the strict zigzag algebra (`TauCeti.zigzagBacktrackAInfinityHom`).
Its morphism equations are `f₁ m₄ = δψ` in arity four, `m₂(f₃, f₃) = 0` in arity six, and trivial
otherwise, since `ψ` vanishes on the volume classes in which `m₄` takes its values. The linear part
is the identity, so the morphism is an `A∞` isomorphism and the deformation is formal.

The signs are those of Tau Ceti's Keller/Getzler--Jones conventions, in which the arity-four
morphism equation carries no relative sign between the two outer terms of `δψ`. Liu--Wang's quartic
operation for affine `D₄`, with equal values on the four rotations of its walk, is an instance;
see `TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.AffineD4`.

## Main definitions

* `TauCeti.zigzagBacktrackOperation`: the backtrack operation of two darts.
* `TauCeti.zigzagBacktrackWalk`: the closed walk `d.symm, d, e, e.symm`.
* `TauCeti.zigzagBacktrackCochain`: a weighted sum of backtrack operations.
* `TauCeti.zigzagBacktrackCoefficients`: the coefficients of the corresponding loop deformation.
* `TauCeti.zigzagBacktrackTaylor`: the suspension of the backtrack cochain.
* `TauCeti.zigzagBacktrackAInfinityHom`: the `A∞` isomorphism to the strict zigzag algebra.

## Main results

* `TauCeti.zigzagBacktrackOperation_coboundary` and `TauCeti.zigzagBacktrackCochain_coboundary`:
  the quartic operation is the Hochschild coboundary of the backtrack cochain.
* `TauCeti.taylor_zigzagBacktrackAInfinityHom`,
  `TauCeti.component_three_zigzagBacktrackAInfinityHom` and
  `TauCeti.component_zigzagBacktrackAInfinityHom_of_ne`: the Taylor map of the backtrack
  isomorphism, its arity-three component, the backtrack cochain, and the vanishing of its
  components outside arities one and three.
* `TauCeti.isIso_zigzagBacktrackAInfinityHom` and
  `TauCeti.isFormal_zigzagLoopAInfinityAlgebra_zigzagBacktrackCoefficients`: the loop deformation
  with backtrack coefficients is `A∞` isomorphic to the strict zigzag algebra, hence formal.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.4, for `A∞` morphisms.
* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  Section 4 and Example 4.7.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (hns : ∀ i : V, ∃ j, G.Adj i j)

/-! ### Backtrack operations -/

/-- The **backtrack operation** of two darts `d` and `e`: the product of the `d`-, `e`- and
`e.symm`-arrow coordinates of its three inputs, times the arrow of `d`. -/
noncomputable def zigzagBacktrackOperation (d e : G.Dart) :
    MultilinearMap k (fun _ : Fin 3 ↦ nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G) :=
  ((MultilinearMap.mkPiAlgebra k (Fin 3) k).compLinearMap
    fun i ↦ (zigzagBasis k G hns).coord (.inr (.inl (![d, e, e.symm] i)))).smulRight
      (zigzagBasis k G hns (.inr (.inl d)))

/-- A backtrack operation is the product of three arrow coordinates times an arrow. -/
@[simp]
theorem zigzagBacktrackOperation_apply (d e : G.Dart) (x : Fin 3 → nonisolatedZigzagQuotient k G) :
    zigzagBacktrackOperation k G hns d e x =
      ((zigzagBasis k G hns).coord (.inr (.inl d)) (x 0) *
          (zigzagBasis k G hns).coord (.inr (.inl e)) (x 1) *
            (zigzagBasis k G hns).coord (.inr (.inl e.symm)) (x 2)) •
        zigzagMk k G (ofArrow (arrow G d.adj)) := by
  simp [zigzagBacktrackOperation, Fin.prod_univ_three, mul_assoc]

/-- The closed walk `d.symm, d, e, e.symm` in product order: read from the last entry it goes
back and forth along `e` and then along `d`, so it is closed when `d.fst = e.snd`. -/
def zigzagBacktrackWalk (d e : G.Dart) : Fin 4 → G.Dart :=
  ![d.symm, d, e, e.symm]

omit [Finite V] in
/-- The backtrack walk lists `d.symm`, `d`, `e` and `e.symm`. -/
theorem zigzagBacktrackWalk_def (d e : G.Dart) :
    zigzagBacktrackWalk G d e = ![d.symm, d, e, e.symm] := by
  rw [zigzagBacktrackWalk]

variable {G}

omit [Finite V] in
/-- Every rotation of the backtrack walk of `d` and `e` is closed, read in product order, when `d`
starts where `e` ends. -/
theorem zigzagBacktrackWalk_fst_eq_snd {d e : G.Dart} (h : d.fst = e.snd) (j i : Fin 4) :
    (zigzagBacktrackWalk G d e (i + j)).fst = (zigzagBacktrackWalk G d e (i + 1 + j)).snd := by
  fin_cases i <;> fin_cases j <;> simp [zigzagBacktrackWalk, h]

/-- **The core coboundary identity.** When `d.fst = e.snd`, the Hochschild coboundary of the
backtrack operation of `d` and `e` is the sum of the loop operations of the backtrack walk and of
its rotation by one step. -/
theorem zigzagBacktrackOperation_coboundary {d e : G.Dart} (h : d.fst = e.snd)
    (x₀ x₁ x₂ x₃ : nonisolatedZigzagQuotient k G) :
    x₀ * zigzagBacktrackOperation k G hns d e ![x₁, x₂, x₃] -
          zigzagBacktrackOperation k G hns d e ![x₀ * x₁, x₂, x₃] +
        zigzagBacktrackOperation k G hns d e ![x₀, x₁ * x₂, x₃] -
          zigzagBacktrackOperation k G hns d e ![x₀, x₁, x₂ * x₃] +
        zigzagBacktrackOperation k G hns d e ![x₀, x₁, x₂] * x₃ =
      zigzagLoopOperation k G hns (zigzagBacktrackWalk G d e) ![x₀, x₁, x₂, x₃] +
        zigzagLoopOperation k G hns (fun i ↦ zigzagBacktrackWalk G d e (i + 1))
          ![x₀, x₁, x₂, x₃] := by
  simp only [zigzagBacktrackOperation_apply, zigzagLoopOperation_apply, Fin.prod_univ_four,
    mul_smul_comm, smul_mul_assoc, mul_zigzagMk_ofArrow hns, zigzagMk_ofArrow_mul hns,
    zigzagBasis_coord_dart_mul hns, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    zigzagBacktrackWalk, Fin.reduceAdd, zero_add, zigzagBasis_apply, zigzagBasisFun_inr_inl,
    zigzagBasisFun_inr_inr, SimpleGraph.Dart.symm_toProd, Prod.fst_swap, Prod.snd_swap]
  simp only [h]
  module

/-! ### Weighted families of backtrack operations -/

section Family

variable {k} (P : Finset (G.Dart × G.Dart)) (a : G.Dart × G.Dart → k)

/-- The **backtrack cochain** of a finite set `P` of pairs of darts with weights `a`: the sum of the
backtrack operations of the pairs in `P`, weighted by `a`. -/
noncomputable def zigzagBacktrackCochain :
    MultilinearMap k (fun _ : Fin 3 ↦ nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G) :=
  ∑ p ∈ P, a p • zigzagBacktrackOperation k G hns p.1 p.2

/-- The backtrack cochain is a weighted sum of products of three arrow coordinates times arrows. -/
@[simp]
theorem zigzagBacktrackCochain_apply (x : Fin 3 → nonisolatedZigzagQuotient k G) :
    zigzagBacktrackCochain hns P a x =
      ∑ p ∈ P, (a p * ((zigzagBasis k G hns).coord (.inr (.inl p.1)) (x 0) *
          (zigzagBasis k G hns).coord (.inr (.inl p.2)) (x 1) *
            (zigzagBasis k G hns).coord (.inr (.inl p.2.symm)) (x 2))) •
        zigzagMk k G (ofArrow (arrow G p.1.adj)) := by
  simp [zigzagBacktrackCochain, zigzagBacktrackOperation_apply, smul_smul]

/-- The coefficients of the loop operations of the backtrack walks of the pairs in `P` and of their
rotations by one step, weighted by `a`. -/
noncomputable def zigzagBacktrackCoefficients : (Fin 4 → G.Dart) →₀ k :=
  ∑ p ∈ P, (Finsupp.single (zigzagBacktrackWalk G p.1 p.2) (a p) +
    Finsupp.single (fun i ↦ zigzagBacktrackWalk G p.1 p.2 (i + 1)) (a p))

omit [Finite V] in
/-- The backtrack coefficients are the sum, over the pairs in `P`, of the single coefficients of the
backtrack walk and of its rotation by one step. -/
theorem zigzagBacktrackCoefficients_def :
    zigzagBacktrackCoefficients P a =
      ∑ p ∈ P, (Finsupp.single (zigzagBacktrackWalk G p.1 p.2) (a p) +
        Finsupp.single (fun i ↦ zigzagBacktrackWalk G p.1 p.2 (i + 1)) (a p)) := by
  rw [zigzagBacktrackCoefficients]

variable {P}

omit [Finite V] in
/-- The backtrack coefficients are supported on closed walks, read in product order. -/
theorem fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients
    (hP : ∀ p ∈ P, p.1.fst = p.2.snd) :
    ∀ w ∈ (zigzagBacktrackCoefficients P a).support, ∀ i, (w i).fst = (w (i + 1)).snd := by
  classical
  intro w hw i
  rw [Finsupp.mem_support_iff, zigzagBacktrackCoefficients, Finsupp.finsetSum_apply] at hw
  obtain ⟨p, hp, hpw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply] at hpw
  by_cases h₁ : zigzagBacktrackWalk G p.1 p.2 = w
  · subst h₁
    simpa using zigzagBacktrackWalk_fst_eq_snd (hP p hp) 0 i
  by_cases h₂ : (fun i ↦ zigzagBacktrackWalk G p.1 p.2 (i + 1)) = w
  · subst h₂
    exact zigzagBacktrackWalk_fst_eq_snd (hP p hp) 1 i
  simp [h₁, h₂] at hpw

/-- The quartic operation of the loop deformation with backtrack coefficients is the weighted sum
of the loop operations of the backtrack walks and of their rotations. -/
theorem zigzagLoopAInfinityAlgebra_zigzagBacktrackCoefficients_m_four
    (hc : ∀ w ∈ (zigzagBacktrackCoefficients P a).support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a) hc).m 4 =
      ∑ p ∈ P, a p • (zigzagLoopOperation k G hns (zigzagBacktrackWalk G p.1 p.2) +
        zigzagLoopOperation k G hns (fun i ↦ zigzagBacktrackWalk G p.1 p.2 (i + 1))) := by
  rw [zigzagLoopAInfinityAlgebra_m_four, zigzagBacktrackCoefficients, map_sum]
  simp [smul_add]

/-- **The coboundary of the backtrack cochain** is the quartic operation of the loop deformation
with backtrack coefficients. -/
theorem zigzagBacktrackCochain_coboundary (hP : ∀ p ∈ P, p.1.fst = p.2.snd)
    (x₀ x₁ x₂ x₃ : nonisolatedZigzagQuotient k G) :
    x₀ * zigzagBacktrackCochain hns P a ![x₁, x₂, x₃] -
          zigzagBacktrackCochain hns P a ![x₀ * x₁, x₂, x₃] +
        zigzagBacktrackCochain hns P a ![x₀, x₁ * x₂, x₃] -
          zigzagBacktrackCochain hns P a ![x₀, x₁, x₂ * x₃] +
        zigzagBacktrackCochain hns P a ![x₀, x₁, x₂] * x₃ =
      (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
        (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).m 4 ![x₀, x₁, x₂, x₃] := by
  rw [zigzagLoopAInfinityAlgebra_zigzagBacktrackCoefficients_m_four]
  simp only [zigzagBacktrackCochain, _root_.sum_apply, _root_.smul_apply, _root_.add_apply,
    Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [← zigzagBacktrackOperation_coboundary k hns (hP p hp)]
  simp only [smul_sub, smul_add]

/-- The backtrack cochain vanishes as soon as one input is homogeneous of degree other than one: it
only reads arrow coordinates. -/
theorem zigzagBacktrackCochain_eq_zero_of_mem (x : Fin 3 → nonisolatedZigzagQuotient k G)
    (j : Fin 3) {m : ℤ} (hm : m ≠ 1) (hx : x j ∈ zigzagIntegerGrade k G m) :
    zigzagBacktrackCochain hns P a x = 0 := by
  rw [zigzagBacktrackCochain_apply]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  have h (d : G.Dart) := zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade k G hns d hm hx
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h <;> simp [h]

/-- The backtrack cochain has degree `-2` for the path-length grading. -/
theorem isHomogeneous_zigzagBacktrackCochain :
    MultilinearMap.IsHomogeneous (zigzagBacktrackCochain hns P a)
      (fun _ ↦ zigzagIntegerGrade k G) (zigzagIntegerGrade k G) (-2) := by
  classical
  rw [MultilinearMap.isHomogeneous_def]
  intro e x hx
  by_cases he : ∀ i, e i = 1
  · rw [Fin.sum_univ_three, he 0, he 1, he 2, zigzagBacktrackCochain_apply]
    refine Submodule.sum_mem _ fun p _ ↦ Submodule.smul_mem _ _ ?_
    convert zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G p.1 using 2
    norm_num
  · obtain ⟨j, hj⟩ := not_forall.mp he
    rw [zigzagBacktrackCochain_eq_zero_of_mem hns a x j hj (hx j)]
    exact Submodule.zero_mem _

/-- Products of values of the backtrack cochain vanish when no pair in `P` has a first dart reverse
to the first dart of another. -/
theorem zigzagBacktrackCochain_mul_zigzagBacktrackCochain_eq_zero
    (hP' : ∀ p ∈ P, ∀ q ∈ P, q.1 ≠ p.1.symm) (x y : Fin 3 → nonisolatedZigzagQuotient k G) :
    zigzagBacktrackCochain hns P a x * zigzagBacktrackCochain hns P a y = 0 := by
  rw [zigzagBacktrackCochain_apply, zigzagBacktrackCochain_apply, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun q hq ↦ ?_
  rw [smul_mul_smul_comm, zigzagMk_ofArrow_mul_ofArrow_of_ne k G (hP' p hp q hq), smul_zero]

section Twist

variable {𝒢 : InternalGrading k (nonisolatedZigzagQuotient k G)}
  (h𝒢 : 𝒢.piece = zigzagIntegerGrade k G)
include h𝒢

/-- The degree-one Koszul twist negates the values of the backtrack cochain, which are arrows. -/
private theorem koszulTwist_one_zigzagBacktrackCochain (x : Fin 3 → nonisolatedZigzagQuotient k G) :
    𝒢.koszulTwist 1 (zigzagBacktrackCochain hns P a x) = -zigzagBacktrackCochain hns P a x := by
  simp only [zigzagBacktrackCochain_apply, map_sum, map_smul, koszulTwist_one_zigzagMk_ofArrow h𝒢,
    smul_neg, Finset.sum_neg_distrib]

/-- Twisting the first input of the backtrack cochain negates it. -/
private theorem zigzagBacktrackCochain_koszulTwist_one_zero
    (x y z : nonisolatedZigzagQuotient k G) :
    zigzagBacktrackCochain hns P a ![𝒢.koszulTwist 1 x, y, z] =
      -zigzagBacktrackCochain hns P a ![x, y, z] := by
  simp [zigzagBasis_coord_dart_koszulTwist_one h𝒢]

/-- Twisting the second input of the backtrack cochain negates it. -/
private theorem zigzagBacktrackCochain_koszulTwist_one_one
    (x y z : nonisolatedZigzagQuotient k G) :
    zigzagBacktrackCochain hns P a ![x, 𝒢.koszulTwist 1 y, z] =
      -zigzagBacktrackCochain hns P a ![x, y, z] := by
  simp [zigzagBasis_coord_dart_koszulTwist_one h𝒢]

/-- Twisting the third input of the backtrack cochain negates it. -/
private theorem zigzagBacktrackCochain_koszulTwist_one_two
    (x y z : nonisolatedZigzagQuotient k G) :
    zigzagBacktrackCochain hns P a ![x, y, 𝒢.koszulTwist 1 z] =
      -zigzagBacktrackCochain hns P a ![x, y, z] := by
  simp [zigzagBasis_coord_dart_koszulTwist_one h𝒢]

/-- **The coboundary identity with suspension signs**: the form of
`TauCeti.zigzagBacktrackCochain_coboundary` met in the arity-four component equation, where the
Koszul twists of the suspension appear. -/
private theorem zigzagBacktrackCochain_coboundary_koszulTwist (hP : ∀ p ∈ P, p.1.fst = p.2.snd)
    (hmul : ∀ x y, 𝒢.koszulTwist 1 (x * y) = 𝒢.koszulTwist 1 x * 𝒢.koszulTwist 1 y)
    (x₀ x₁ x₂ x₃ : nonisolatedZigzagQuotient k G) :
    𝒢.koszulTwist 1 x₀ * zigzagBacktrackCochain hns P a ![x₁, 𝒢.koszulTwist 1 x₂, x₃] +
        𝒢.koszulTwist 1 (zigzagBacktrackCochain hns P a ![x₀, 𝒢.koszulTwist 1 x₁, x₂]) * x₃ =
      (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
          (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).m 4
          ![𝒢.koszulTwist 1 x₀, x₁, 𝒢.koszulTwist 1 x₂, x₃] +
        (zigzagBacktrackCochain hns P a ![𝒢.koszulTwist 1 x₀ * x₁, 𝒢.koszulTwist 1 x₂, x₃] +
          zigzagBacktrackCochain hns P a
            ![-𝒢.koszulTwist 1 x₀, 𝒢.koszulTwist 1 (𝒢.koszulTwist 1 x₁ * x₂), x₃] +
          zigzagBacktrackCochain hns P a
            ![-𝒢.koszulTwist 1 x₀, 𝒢.koszulTwist 1 (-𝒢.koszulTwist 1 x₁),
              𝒢.koszulTwist 1 x₂ * x₃]) := by
  -- Negating the first or the second input negates the cochain, by multilinearity.
  have hneg₀ (u v w : nonisolatedZigzagQuotient k G) :
      zigzagBacktrackCochain hns P a ![-u, v, w] = -zigzagBacktrackCochain hns P a ![u, v, w] := by
    have h := (zigzagBacktrackCochain hns P a).map_update_neg (Fin.cons u ![v, w]) 0 u
    rwa [Fin.update_cons_zero, Fin.update_cons_zero] at h
  have hneg₁ (u v w : nonisolatedZigzagQuotient k G) :
      zigzagBacktrackCochain hns P a ![u, -v, w] = -zigzagBacktrackCochain hns P a ![u, v, w] := by
    have h := (zigzagBacktrackCochain hns P a).map_update_neg (Fin.cons u (Fin.cons v ![w]))
      (Fin.succ 0) v
    rwa [← Fin.cons_update, ← Fin.cons_update, Fin.update_cons_zero, Fin.update_cons_zero] at h
  -- Normalize the twists and negations on both sides, then compare with the coboundary identity.
  have hid := zigzagBacktrackCochain_coboundary hns a hP (𝒢.koszulTwist 1 x₀) x₁
    (𝒢.koszulTwist 1 x₂) x₃
  simp only [zigzagBacktrackCochain_koszulTwist_one_zero hns a h𝒢,
    zigzagBacktrackCochain_koszulTwist_one_one hns a h𝒢,
    zigzagBacktrackCochain_koszulTwist_one_two hns a h𝒢,
    koszulTwist_one_zigzagBacktrackCochain hns a h𝒢, hmul, map_neg,
    InternalGrading.koszulTwist_koszulTwist, hneg₀, hneg₁, neg_neg] at hid ⊢
  rw [← hid]
  abel

end Twist

end Family

/-! ### The `A∞` isomorphism -/

section AInfinity

variable {k} {P : Finset (G.Dart × G.Dart)} (a : G.Dart × G.Dart → k)

variable (P) in
/-- The family of operations of the backtrack Taylor map: the backtrack cochain in arity three. -/
private noncomputable def backtrackOps :
    ∀ n : ℕ, MultilinearMap k (fun _ : Fin n ↦ nonisolatedZigzagQuotient k G)
      (nonisolatedZigzagQuotient k G)
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => zigzagBacktrackCochain hns P a
  | _ + 4 => 0

private theorem backtrackOps_three : backtrackOps hns P a 3 = zigzagBacktrackCochain hns P a := by
  rw [backtrackOps]

private theorem backtrackOps_eq_zero {n : ℕ} (h : n ≠ 3) : backtrackOps hns P a n = 0 := by
  match n, h with
  | 0, _ | 1, _ | 2, _ | _ + 4, _ => rfl

variable (P) in
/-- The **backtrack Taylor map**: the suspension of the backtrack cochain, concentrated on words of
length three. Together with the projection onto single letters it is the Taylor map of the
backtrack isomorphism. -/
noncomputable def zigzagBacktrackTaylor : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
    nonisolatedZigzagQuotient k G :=
  suspensionTaylor (zigzagStrictAInfinityAlgebra k hns).grading (backtrackOps hns P a)

/-- The backtrack Taylor map vanishes on a word with a letter of degree two. -/
private theorem zigzagBacktrackTaylor_of_tprod_eq_zero_of_mem {m : ℕ} (hm : 0 < m)
    (w : Fin m → nonisolatedZigzagQuotient k G) (j : Fin m)
    (hj : w j ∈ zigzagIntegerGrade k G 2) :
    zigzagBacktrackTaylor hns P a (of k _ ⟨m, hm⟩ (PiTensorProduct.tprod k w)) = 0 := by
  rw [zigzagBacktrackTaylor, suspensionTaylor_of_tprod]
  by_cases h3 : m = 3
  · subst h3
    rw [backtrackOps_three]
    refine zigzagBacktrackCochain_eq_zero_of_mem hns a _ j (m := 2) (by norm_num) ?_
    have h := (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist_mem_piece (x := w j) (e := 2)
      (by simpa using hj)
      ((3 : ℕ) - 1 - j)
    simpa using h
  · rw [backtrackOps_eq_zero hns a h3, _root_.zero_apply]

/-- The backtrack Taylor map vanishes on words whose length is not three. -/
@[simp]
theorem zigzagBacktrackTaylor_of_tprod_of_ne {m : ℕ} (hm : 0 < m) (hm3 : m ≠ 3)
    (w : Fin m → nonisolatedZigzagQuotient k G) :
    zigzagBacktrackTaylor hns P a (of k _ ⟨m, hm⟩ (PiTensorProduct.tprod k w)) = 0 := by
  rw [zigzagBacktrackTaylor, suspensionTaylor_of_tprod, backtrackOps_eq_zero hns a hm3,
    _root_.zero_apply]

/-- On a word of length three the backtrack Taylor map is the backtrack cochain, with the
suspension sign carried by the degree-one Koszul twist of the middle letter. -/
private theorem zigzagBacktrackTaylor_of_tprod_three_koszulTwist
    (w : Fin 3 → nonisolatedZigzagQuotient k G) :
    zigzagBacktrackTaylor hns P a (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k w)) =
      zigzagBacktrackCochain hns P a
        ![w 0, (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 (w 1), w 2] := by
  rw [zigzagBacktrackTaylor, suspensionTaylor_of_tprod, backtrackOps_three]
  congr 1
  funext i
  -- the outer letters carry the twists of even degree `2` and `0`, which are the identity
  fin_cases i
  · exact LinearMap.congr_fun (InternalGrading.koszulTwist_two _) _
  · rfl
  · exact LinearMap.congr_fun (InternalGrading.koszulTwist_zero _) _

/-- On a word of length three the backtrack Taylor map is the negative of the backtrack cochain:
the suspension sign of an arity-three operation of even degree is that of its middle letter, which
the backtrack cochain only reads through an arrow coordinate. -/
@[simp]
theorem zigzagBacktrackTaylor_of_tprod_three (w : Fin 3 → nonisolatedZigzagQuotient k G) :
    zigzagBacktrackTaylor hns P a (of k _ (3 : ℕ+) (PiTensorProduct.tprod k w)) =
      -zigzagBacktrackCochain hns P a w := by
  -- `(3 : ℕ+)` is definitionally `⟨3, _⟩`; rewriting with `PNat.mk_ofNat` is not possible here
  -- because the type `Fin ↑3` of the word `w` depends on this literal
  change zigzagBacktrackTaylor hns P a (of k _ ⟨3, by norm_num⟩ (PiTensorProduct.tprod k w)) = _
  rw [zigzagBacktrackTaylor_of_tprod_three_koszulTwist,
    zigzagBacktrackCochain_koszulTwist_one_one hns a zigzagStrictAInfinityAlgebra_grading_piece]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- The backtrack Taylor map vanishes on blocks of length other than three. -/
private theorem zigzagBacktrackTaylor_subword_of_ne {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s b : ℕ) (hb : b ≠ 3) :
    zigzagBacktrackTaylor hns P a (subword k x s b) = 0 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · rw [subword_length_zero, map_zero]
  by_cases h : s + b ≤ n
  · rw [subword_eq_of_tprod k x hb0 h, zigzagBacktrackTaylor_of_tprod_of_ne hns a hb0 hb]
  · rw [subword_eq_zero_of_lt_add k x (by omega), map_zero]

/-- The backtrack Taylor map on a block of length three. -/
private theorem zigzagBacktrackTaylor_subword_three {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s : ℕ) (h : s + 3 ≤ n) :
    zigzagBacktrackTaylor hns P a (subword k x s 3) =
      zigzagBacktrackCochain hns P a ![x ⟨s, by omega⟩,
        (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 (x ⟨s + 1, by omega⟩),
        x ⟨s + 2, by omega⟩] := by
  rw [subword_eq_of_tprod k x (by norm_num) h, zigzagBacktrackTaylor_of_tprod_three_koszulTwist]
  -- the two sides list the same letters, indexed by `Fin` literals
  rfl

/-- The backtrack Taylor map vanishes on spliced words whose length is not three. -/
private theorem zigzagBacktrackTaylor_splice_of_ne {n : ℕ}
    (z : Fin n → nonisolatedZigzagQuotient k G) (p d : ℕ) (e : nonisolatedZigzagQuotient k G)
    (h : n + 1 - d ≠ 3) : zigzagBacktrackTaylor hns P a (splice k z 0 n p d e) = 0 := by
  by_cases hfit : 0 < d ∧ p + d ≤ n
  · rw [splice_eq_of_tprod k z e hfit.1 hfit.2 (by omega),
      zigzagBacktrackTaylor_of_tprod_of_ne hns a _ h]
  · rw [splice_eq_zero_of_not_fits k z e hfit, map_zero]

/-- The backtrack Taylor map vanishes on spliced words whose new letter has degree two. -/
private theorem zigzagBacktrackTaylor_splice_of_mem {n : ℕ}
    (z : Fin n → nonisolatedZigzagQuotient k G) (p d : ℕ) {e : nonisolatedZigzagQuotient k G}
    (he : e ∈ zigzagIntegerGrade k G 2) :
    zigzagBacktrackTaylor hns P a (splice k z 0 n p d e) = 0 := by
  by_cases hfit : 0 < d ∧ p + d ≤ n
  · rw [splice_eq_of_tprod k z e hfit.1 hfit.2 (by omega)]
    exact zigzagBacktrackTaylor_of_tprod_eq_zero_of_mem hns a _ _ ⟨p, by omega⟩ (by simpa using he)
  · rw [splice_eq_zero_of_not_fits k z e hfit, map_zero]

/-- The backtrack Taylor map on the spliced word collapsing the first two letters of a word of
length four. -/
private theorem zigzagBacktrackTaylor_splice_four_zero (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    zigzagBacktrackTaylor hns P a (splice k z 0 4 0 2 e) =
      zigzagBacktrackCochain hns P a ![e,
        (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 (z 2), z 3] := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num),
    zigzagBacktrackTaylor_of_tprod_three_koszulTwist]
  -- the two sides list the same letters, indexed by `Fin` literals
  rfl

/-- The backtrack Taylor map on the spliced word collapsing the middle two letters of a word of
length four. -/
private theorem zigzagBacktrackTaylor_splice_four_one (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    zigzagBacktrackTaylor hns P a (splice k z 0 4 1 2 e) =
      zigzagBacktrackCochain hns P a ![z 0,
        (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 e, z 3] := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num),
    zigzagBacktrackTaylor_of_tprod_three_koszulTwist]
  -- the two sides list the same letters, indexed by `Fin` literals
  rfl

/-- The backtrack Taylor map on the spliced word collapsing the last two letters of a word of
length four. -/
private theorem zigzagBacktrackTaylor_splice_four_two (z : Fin 4 → nonisolatedZigzagQuotient k G)
    (e : nonisolatedZigzagQuotient k G) :
    zigzagBacktrackTaylor hns P a (splice k z 0 4 2 2 e) =
      zigzagBacktrackCochain hns P a ![z 0,
        (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 (z 1), e] := by
  rw [splice_eq_of_tprod k z e (by norm_num) (by norm_num) (by norm_num),
    zigzagBacktrackTaylor_of_tprod_three_koszulTwist]
  -- the two sides list the same letters, indexed by `Fin` literals
  rfl

variable {c : (Fin 4 → G.Dart) →₀ k} (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd)

/-- The Taylor map of a loop deformation vanishes on blocks of length other than two and four. -/
private theorem taylor_zigzagLoopAInfinityAlgebra_subword_of_ne {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s b : ℕ) (h₂ : b ≠ 2) (h₄ : b ≠ 4) :
    (zigzagLoopAInfinityAlgebra hns c hc).taylor (subword k x s b) = 0 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · rw [subword_length_zero, map_zero]
  by_cases h : s + b ≤ n
  · rw [subword_eq_of_tprod k x hb0 h, AInfinityAlgebra.taylor_of_tprod,
      zigzagLoopAInfinityAlgebra_m_eq_zero _ _ h₂ h₄, _root_.zero_apply]
  · rw [subword_eq_zero_of_lt_add k x (by omega), map_zero]

/-- The Taylor map of a loop deformation on a block of length two. -/
private theorem taylor_zigzagLoopAInfinityAlgebra_subword_two {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s : ℕ) (h : s + 2 ≤ n) :
    (zigzagLoopAInfinityAlgebra hns c hc).taylor (subword k x s 2) =
      (zigzagLoopAInfinityAlgebra hns c hc).grading.koszulTwist 1 (x ⟨s, by omega⟩) *
        x ⟨s + 1, by omega⟩ := by
  rw [subword_eq_of_tprod k x (by norm_num) h, AInfinityAlgebra.taylor_of_tprod,
    zigzagLoopAInfinityAlgebra_m_two_apply]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
    sub_zero]
  norm_num

/-- The Taylor map of a loop deformation takes values of degree two on blocks of length four. -/
private theorem taylor_zigzagLoopAInfinityAlgebra_subword_four_mem {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s : ℕ) :
    (zigzagLoopAInfinityAlgebra hns c hc).taylor (subword k x s 4) ∈ zigzagIntegerGrade k G 2 := by
  by_cases h : s + 4 ≤ n
  · rw [subword_eq_of_tprod k x (by norm_num) h, AInfinityAlgebra.taylor_of_tprod]
    exact zigzagLoopAInfinityAlgebra_m_four_mem _ hc _
  · rw [subword_eq_zero_of_lt_add k x (by omega), map_zero]
    exact zero_mem _

/-- The Taylor map `letter + φ` on a block of length other than one and three. -/
private theorem letter_add_zigzagBacktrackTaylor_subword_of_ne {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s b : ℕ) (h₁ : b ≠ 1) (h₃ : b ≠ 3) :
    (letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x s b) = 0 := by
  rw [LinearMap.add_apply, letter_subword_of_ne_one k _ x s h₁,
    zigzagBacktrackTaylor_subword_of_ne hns a x s b h₃, add_zero]

/-- The Taylor map `letter + φ` on a block of length one. -/
private theorem letter_add_zigzagBacktrackTaylor_subword_one {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s : ℕ) (h : s < n) :
    (letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x s 1) = x ⟨s, h⟩ := by
  rw [LinearMap.add_apply, zigzagBacktrackTaylor_subword_of_ne hns a x s 1 (by norm_num),
    subword_one k _ x h, letter_ofLetter, add_zero]

/-- The Taylor map `letter + φ` on a block of length three. -/
private theorem letter_add_zigzagBacktrackTaylor_subword_three {n : ℕ}
    (x : Fin n → nonisolatedZigzagQuotient k G) (s : ℕ) (h : s + 3 ≤ n) :
    (letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x s 3) =
      zigzagBacktrackCochain hns P a ![x ⟨s, by omega⟩,
        (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 (x ⟨s + 1, by omega⟩),
        x ⟨s + 2, by omega⟩] := by
  rw [LinearMap.add_apply, letter_subword_of_ne_one k _ x s (by norm_num), zero_add,
    zigzagBacktrackTaylor_subword_three hns a x s h]

variable (hP : ∀ p ∈ P, p.1.fst = p.2.snd) (hP' : ∀ p ∈ P, ∀ q ∈ P, q.1 ≠ p.1.symm)

include hP' in
/-- In the component equation, the cuts of a word into two blocks contribute only for the words of
length two and four. -/
private theorem backtrack_cut_eq_zero {n : ℕ} (x : Fin n → nonisolatedZigzagQuotient k G) (d : ℕ)
    (hd : ¬((n = 2 ∧ d = 1) ∨ (n = 4 ∧ (d = 1 ∨ d = 3)))) :
    (zigzagStrictAInfinityAlgebra k hns).m 2
      ![(zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1
          ((letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x 0 d)),
        (letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x d (n - d))] = 0 := by
  rw [zigzagStrictAInfinityAlgebra_m_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases h₁ : d = 1 ∨ d = 3
  · by_cases h₂ : n - d = 1 ∨ n - d = 3
    · obtain ⟨rfl, rfl⟩ : d = 3 ∧ n = 6 := by omega
      rw [letter_add_zigzagBacktrackTaylor_subword_three hns a x 0 (by norm_num),
        letter_add_zigzagBacktrackTaylor_subword_three hns a x 3 (by norm_num),
        koszulTwist_one_zigzagBacktrackCochain hns a zigzagStrictAInfinityAlgebra_grading_piece,
        neg_mul, zigzagBacktrackCochain_mul_zigzagBacktrackCochain_eq_zero hns a hP', neg_zero]
    · rw [letter_add_zigzagBacktrackTaylor_subword_of_ne hns a x d (n - d) (by omega) (by omega),
        mul_zero]
  · rw [letter_add_zigzagBacktrackTaylor_subword_of_ne hns a x 0 d (by omega) (by omega), map_zero,
      zero_mul]

/-- In the component equation, the collapsed blocks contribute to the backtrack Taylor map only for
words of length four. -/
private theorem backtrack_collapse_eq_zero {n : ℕ} (x : Fin n → nonisolatedZigzagQuotient k G)
    (p d : ℕ) (hd : ¬(n = 4 ∧ d = 2)) :
    zigzagBacktrackTaylor hns P a
      (splice k (((zigzagLoopAInfinityAlgebra hns c hc).grading.shift 1).twistedTuple 1 x 0 p)
        0 n p d ((zigzagLoopAInfinityAlgebra hns c hc).taylor (subword k x p d))) = 0 := by
  by_cases h₂ : d = 2
  · subst h₂
    have h : n + 1 - 2 ≠ 3 := by omega
    exact zigzagBacktrackTaylor_splice_of_ne hns a _ _ _ _ h
  by_cases h₄ : d = 4
  · subst h₄
    exact zigzagBacktrackTaylor_splice_of_mem hns a _ _ _
      (taylor_zigzagLoopAInfinityAlgebra_subword_four_mem hns _ x p)
  rw [taylor_zigzagLoopAInfinityAlgebra_subword_of_ne hns _ x p d h₂ h₄, splice_zero, map_zero]

include hP hP' in
/-- The component equation on words of length four, where the backtrack cochain kills the quartic
operation. -/
private theorem backtrack_component_four (x : Fin 4 → nonisolatedZigzagQuotient k G) :
    ∑ d ∈ Finset.range 4,
        (zigzagStrictAInfinityAlgebra k hns).m 2
          ![(zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1
              ((letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x 0 d)),
            (letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x d (4 - d))] =
      (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
          (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).taylor
          (of k _ ⟨4, by norm_num⟩ (PiTensorProduct.tprod k x)) +
        ∑ p ∈ Finset.range 4, ∑ d ∈ Finset.range 5, zigzagBacktrackTaylor hns P a
          (splice k (((zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
              (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).grading.shift
                1).twistedTuple 1 x 0 p) 0 4 p d
            ((zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
              (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).taylor
                (subword k x p d))) := by
  -- Only the collapses of two letters and the cuts after the first and the third letter remain.
  have hcut (d : ℕ) (hd : d = 0 ∨ d = 2) := backtrack_cut_eq_zero hns a hP' x d (by omega)
  rw [Finset.sum_congr rfl fun p _ ↦ Finset.sum_eq_single 2
    (fun d _ hd ↦ backtrack_collapse_eq_zero hns a _ x p d (by omega)) (by simp)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hcut 0 (by simp),
    hcut 2 (by simp), add_zero]
  simp (disch := norm_num) only [Nat.reduceSub, zero_add,
    splice_eq_zero_of_block_lt_add, map_zero, add_zero, zigzagBacktrackTaylor_splice_four_zero,
    zigzagBacktrackTaylor_splice_four_one, zigzagBacktrackTaylor_splice_four_two,
    taylor_zigzagLoopAInfinityAlgebra_subword_two, InternalGrading.twistedTuple_apply_of_mem_Ico,
    InternalGrading.twistedTuple_apply_of_not_mem_Ico, InternalGrading.koszulTwist_one_shift_one,
    letter_add_zigzagBacktrackTaylor_subword_one, letter_add_zigzagBacktrackTaylor_subword_three]
  -- All Koszul twists are those of one grading, in which the arity-four suspension twists the
  -- first and third letters; the remaining identity is the coboundary identity with signs.
  set 𝒢 := (zigzagStrictAInfinityAlgebra k hns).grading with h𝒢
  have hG : (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
      (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).grading = 𝒢 :=
    zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading _ _
  have h₃ (y : nonisolatedZigzagQuotient k G) : 𝒢.koszulTwist 3 y = 𝒢.koszulTwist 1 y := by
    simpa using (LinearMap.congr_fun (𝒢.koszulTwist_comp 1 2) y).symm
  have hmul (y z : nonisolatedZigzagQuotient k G) :
      𝒢.koszulTwist 1 (y * z) = 𝒢.koszulTwist 1 y * 𝒢.koszulTwist 1 z := by
    have h := (zigzagStrictAInfinityAlgebra k hns).koszulTwist_m_two 1 y z
    rw [zigzagStrictAInfinityAlgebra_m_two_apply, zigzagStrictAInfinityAlgebra_m_two_apply] at h
    simpa using h
  have hx : (fun i : Fin 4 ↦ 𝒢.koszulTwist
      (((⟨4, by norm_num⟩ : {n : ℕ // 0 < n}) : ℕ) - 1 - (i : ℕ)) (x i)) =
      ![𝒢.koszulTwist 1 (x 0), x 1, 𝒢.koszulTwist 1 (x 2), x 3] := by
    funext i
    fin_cases i
    · simpa using h₃ (x 0)
    · simp
    · simp
    · simp
  rw [AInfinityAlgebra.taylor_of_tprod, hG, hx, zigzagStrictAInfinityAlgebra_m_two_apply,
    zigzagStrictAInfinityAlgebra_m_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk, Nat.reduceAdd,
    Fin.isValue, LinearMap.neg_apply]
  exact zigzagBacktrackCochain_coboundary_koszulTwist hns a
    zigzagStrictAInfinityAlgebra_grading_piece hP hmul (x 0) (x 1) (x 2) (x 3)

include hP hP' in
/-- The component equation on words of length two, where it is the agreement of the products. -/
private theorem backtrack_component_two (x : Fin 2 → nonisolatedZigzagQuotient k G) :
    ∑ d ∈ Finset.range 2,
        (zigzagStrictAInfinityAlgebra k hns).m 2
          ![(zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1
              ((letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x 0 d)),
            (letter k _ + zigzagBacktrackTaylor hns P a : _ →ₗ[k] _) (subword k x d (2 - d))] =
      (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
          (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).taylor
          (of k _ ⟨2, by norm_num⟩ (PiTensorProduct.tprod k x)) +
        ∑ p ∈ Finset.range 2, ∑ d ∈ Finset.range 3, zigzagBacktrackTaylor hns P a
          (splice k (((zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
              (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).grading.shift
                1).twistedTuple 1 x 0 p) 0 2 p d
            ((zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
              (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).taylor
                (subword k x p d))) := by
  -- Only the cut after the first letter remains; both sides are then the twisted product.
  rw [Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
      backtrack_collapse_eq_zero hns a _ x p d (by omega), add_zero,
    Finset.sum_range_succ, Finset.sum_range_one, backtrack_cut_eq_zero hns a hP' x 0 (by omega),
    AInfinityAlgebra.taylor_of_tprod,
    zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading]
  simp (disch := norm_num) only [Nat.reduceSub, letter_add_zigzagBacktrackTaylor_subword_one,
    zigzagLoopAInfinityAlgebra_m_two_apply, zigzagStrictAInfinityAlgebra_m_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

include hP hP' in
/-- **The component equation of the backtrack isomorphism**: the Taylor map `letter + φ`, for `φ`
the backtrack Taylor map, intertwines the loop deformation with backtrack coefficients and the
strict zigzag algebra. -/
private theorem taylor_comp_coalgHom_zigzagBacktrackTaylor :
    (zigzagStrictAInfinityAlgebra k hns).taylor ∘ₗ
        coalgHom k (letter k _ + zigzagBacktrackTaylor hns P a) =
      (letter k _ + zigzagBacktrackTaylor hns P a) ∘ₗ
        (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
          (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).barDifferential := by
  rw [LinearMap.add_comp, AInfinityAlgebra.letter_comp_barDifferential]
  refine linearMap_ext k _ fun ⟨n, hn⟩ x ↦ ?_
  rw [LinearMap.comp_apply,
    (isMinimal_zigzagStrictAInfinityAlgebra (hns := hns)).taylor_coalgHom_of_tprod
      (fun m hm ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)),
    LinearMap.add_apply, LinearMap.comp_apply, AInfinityAlgebra.barDifferential_def,
    gradedCoderiv_of_tprod, map_sum]
  simp only [map_sum]
  rcases (by omega : n = 2 ∨ n = 4 ∨ (n ≠ 2 ∧ n ≠ 4)) with rfl | rfl | ⟨h₂, h₄⟩
  · exact backtrack_component_two hns a hP hP' x
  · exact backtrack_component_four hns a hP hP' x
  · rw [Finset.sum_eq_zero fun d _ ↦ backtrack_cut_eq_zero hns a hP' (n := n) x d (by omega),
      Finset.sum_eq_zero fun p _ ↦ Finset.sum_eq_zero fun d _ ↦
        backtrack_collapse_eq_zero hns a _ (n := n) x p d (by omega), add_zero,
      AInfinityAlgebra.taylor_of_tprod, zigzagLoopAInfinityAlgebra_m_eq_zero _ _ h₂ h₄,
      _root_.zero_apply]

/-- The backtrack Taylor map has degree zero for the suspended path-length grading. -/
theorem isHomogeneous_zigzagBacktrackTaylor :
    LinearMap.IsHomogeneous (zigzagBacktrackTaylor hns P a)
      (gradedPiece ((zigzagStrictAInfinityAlgebra k hns).grading.shift 1))
      ((zigzagStrictAInfinityAlgebra k hns).grading.shift 1).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro D z hz
  refine gradedPiece_induction
    (motive := fun w ↦ zigzagBacktrackTaylor hns P a w ∈
      ((zigzagStrictAInfinityAlgebra k hns).grading.shift 1).piece (D + 0)) hz ?_ ?_ ?_ ?_
  · intro m hm 𝒟 y hy hD
    by_cases h₃ : m = 3
    · subst h₃
      rw [zigzagBacktrackTaylor_of_tprod_three_koszulTwist, InternalGrading.shift_piece,
        zigzagStrictAInfinityAlgebra_grading_piece]
      have hy' (i : Fin 3) : y i ∈ zigzagIntegerGrade k G (𝒟 i + 1) := by
        simpa using hy i
      have hmem := (isHomogeneous_zigzagBacktrackCochain hns (P := P) a).map_mem (fun i ↦ 𝒟 i + 1)
        ![y 0, (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 (y 1), y 2] fun i ↦ by
          fin_cases i
          · exact hy' 0
          · have h := (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist_mem_piece (x := y 1)
              (e := 𝒟 1 + 1)
                (by simpa using hy' 1) 1
            simpa using h
          · exact hy' 2
      convert hmem using 2
      rw [← hD, Fin.sum_univ_three, Fin.sum_univ_three]
      ring
    · rw [zigzagBacktrackTaylor_of_tprod_of_ne hns a hm h₃]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact add_mem hu hv
  · intro r u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ r hu

/-- **The backtrack isomorphism**: the `A∞` morphism from the loop deformation with backtrack
coefficients to the strict zigzag algebra whose Taylor map is the projection onto single letters
plus the backtrack Taylor map. In unsuspended terms its components are `f₁ = id`, `f₃` the
backtrack cochain, and `fₙ = 0` otherwise. -/
noncomputable def zigzagBacktrackAInfinityHom :
    AInfinityHom (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
        (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP))
      (zigzagStrictAInfinityAlgebra k hns) :=
  AInfinityHom.ofTaylor (letter k _ + zigzagBacktrackTaylor hns P a)
    (by
      rw [zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading
        (zigzagBacktrackCoefficients P a)
        (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)]
      exact (isHomogeneous_letter _).add (isHomogeneous_zigzagBacktrackTaylor hns a))
    (taylor_comp_coalgHom_zigzagBacktrackTaylor hns a hP hP')

/-- The Taylor map of the backtrack isomorphism. -/
@[simp]
theorem taylor_zigzagBacktrackAInfinityHom :
    (zigzagBacktrackAInfinityHom hns a hP hP').taylor =
      letter k _ + zigzagBacktrackTaylor hns P a :=
  AInfinityHom.taylor_ofTaylor _ _ _

/-- The linear part of the backtrack isomorphism is the identity. -/
@[simp]
theorem linearPart_zigzagBacktrackAInfinityHom :
    (zigzagBacktrackAInfinityHom hns a hP hP').linearPart = LinearMap.id := by
  refine LinearMap.ext fun y ↦ ?_
  rw [AInfinityHom.linearPart_apply, taylor_zigzagBacktrackAInfinityHom, LinearMap.add_apply,
    letter_ofLetter, ofLetter_eq_of_tprod,
    zigzagBacktrackTaylor_of_tprod_of_ne hns a _ (by norm_num), add_zero, LinearMap.id_apply]

/-- The arity-three component of the backtrack isomorphism is the backtrack cochain. -/
@[simp]
theorem component_three_zigzagBacktrackAInfinityHom :
    (zigzagBacktrackAInfinityHom hns a hP hP').component 3 = zigzagBacktrackCochain hns P a := by
  ext x
  have hx : (fun i : Fin 3 ↦
      (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist ((3 : ℕ) - 1 - i) (x i)) =
      ![x 0, (zigzagStrictAInfinityAlgebra k hns).grading.koszulTwist 1 (x 1), x 2] := by
    funext i
    fin_cases i <;> simp
  rw [AInfinityHom.component_apply _ 3 (by norm_num), taylor_zigzagBacktrackAInfinityHom,
    LinearMap.add_apply, letter_of_of_ne_one k _ (by decide), zero_add,
    zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading, hx]
  -- The suspension sign twists the middle letter, which negates the backtrack cochain.
  simp only [PNat.mk_ofNat, zigzagBacktrackTaylor_of_tprod_three, neg_neg,
    zigzagBacktrackCochain_koszulTwist_one_one hns a zigzagStrictAInfinityAlgebra_grading_piece]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The components of the backtrack isomorphism vanish outside arities one and three. -/
@[simp]
theorem component_zigzagBacktrackAInfinityHom_of_ne {n : ℕ} (h₁ : n ≠ 1) (h₃ : n ≠ 3) :
    (zigzagBacktrackAInfinityHom hns a hP hP').component n = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact AInfinityHom.component_zero _
  ext x
  rw [AInfinityHom.component_apply _ n hn, taylor_zigzagBacktrackAInfinityHom,
    LinearMap.add_apply, letter_of_of_ne_one k _ (Subtype.coe_ne_coe.mp h₁), zero_add,
    zigzagBacktrackTaylor_of_tprod_of_ne hns a hn h₃, _root_.zero_apply]

/-- **The backtrack isomorphism is an `A∞` isomorphism.** -/
theorem isIso_zigzagBacktrackAInfinityHom : (zigzagBacktrackAInfinityHom hns a hP hP').IsIso :=
  AInfinityHom.isIso_of_linearPart_bijective _ (by
    rw [linearPart_zigzagBacktrackAInfinityHom]
    exact Function.bijective_id)

include hP' in
/-- **The loop deformation with backtrack coefficients is formal**: it is `A∞` isomorphic to the
strict zigzag algebra, which has no operation besides the product. -/
theorem isFormal_zigzagLoopAInfinityAlgebra_zigzagBacktrackCoefficients :
    (zigzagLoopAInfinityAlgebra hns (zigzagBacktrackCoefficients P a)
      (fst_eq_snd_of_mem_support_zigzagBacktrackCoefficients a hP)).IsFormal :=
  (AInfinityAlgebra.IsMinimal.isFormal isMinimal_zigzagStrictAInfinityAlgebra
    fun _ hn ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)).of_isQuasiIso
      (isIso_zigzagBacktrackAInfinityHom hns a hP hP').isQuasiIso

end AInfinity

end TauCeti
