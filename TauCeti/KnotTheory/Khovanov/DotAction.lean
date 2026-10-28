/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Split

/-!
# Dots on circle tensors

A dot on a selected circle acts by multiplication by `X = ε` on that factor and by the
identity on all other factors. On enhanced-state labels it replaces `1` by `X` and kills
`X`. This action squares to zero, has quantum degree `−2`, and is self-adjoint for the
perfect Frobenius pairing. Dots pass through both merges and splits along the corresponding
circle. These are the statewise identities used by the marked-component action and reduction
of the Khovanov complex.

All circle sets are retained: in particular the formulas also apply to unaffected and
crossing-free circles. No ordering of the circles is chosen.

## References

* M. Khovanov, *Patterns in knot cohomology I*, §3 (the marked-component action).
* M. Khovanov, *A categorification of the Jones polynomial*, §2 (the Frobenius algebra).
-/

public section

open PiTensorProduct DualNumber TrivSqZeroExt Finset

namespace TauCeti.Khovanov

section Semiring

variable (R : Type*) [CommSemiring R]
variable {ι : Type*} [DecidableEq ι]

/-- Multiply by `X` on the selected circle and act identically on every other factor. -/
noncomputable def circleDot (p : ι) : CircleTensor R ι →ₗ[R] CircleTensor R ι :=
  LinearMap.mulLeft R (singleAlgHom (R := R) (A := fun _ : ι ↦ R[ε]) p ε)

variable {R}

/-- The dot is multiplication by the inclusion of `ε` in its selected tensor factor. -/
theorem circleDot_apply (p : ι) (x : CircleTensor R ι) :
    circleDot R p x = singleAlgHom (A := fun _ : ι ↦ R[ε]) p ε * x := (rfl)

/-- On pure tensors a dot multiplies the selected factor by `ε`. -/
@[simp]
theorem circleDot_tprod (p : ι) (x : ι → R[ε]) :
    circleDot R p (tprod R x) = tprod R (Function.update x p (ε * x p)) := by
  rw [circleDot_apply, singleAlgHom_apply, tprod_mul_tprod]
  congr 1
  funext i
  by_cases hi : i = p
  · subst i
    simp
  · simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hi, Function.update_of_ne hi]

/-- A dot kills an `X` label and changes a `1` label to `X`, leaving all other labels intact. -/
@[simp↓]
theorem circleDot_circleBasis [Finite ι] (p : ι) (l : ι → Bool) :
    circleDot R p (circleBasis R ι l) =
      if l p then 0 else circleBasis R ι (Function.update l p true) := by
  rw [circleBasis_apply, circleDot_tprod]
  cases hp : l p
  · simp only [Bool.false_eq_true, ↓reduceIte, circleBasis_apply]
    congr 1
    funext i
    by_cases hi : i = p
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  · simp only [↓reduceIte]
    exact MultilinearMap.map_coord_zero _ p (by simp)

/-- Two dots on the same circle act by zero. -/
@[simp]
theorem circleDot_circleDot (p : ι) (x : CircleTensor R ι) :
    circleDot R p (circleDot R p x) = 0 := by
  rw [circleDot_apply, circleDot_apply, ← mul_assoc, ← map_mul, eps_mul_eps, map_zero, zero_mul]

/-- Dots on any two circles commute. -/
theorem circleDot_comm (p q : ι) (x : CircleTensor R ι) :
    circleDot R p (circleDot R q x) = circleDot R q (circleDot R p x) := by
  simp only [circleDot_apply]
  exact _root_.mul_left_comm _ _ x

variable {σ τ : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq τ]

/-- A merge transports a dot to the image of its selected circle. This includes births on
the other circles, since the correspondence need not be surjective. -/
@[simp]
theorem fiberwiseMul_circleDot (f : σ → τ) (p : σ) (x : CircleTensor R σ) :
    fiberwiseMul (A := fun _ ↦ R[ε]) f (circleDot R p x) =
      circleDot R (f p) (fiberwiseMul (A := fun _ ↦ R[ε]) f x) := by
  simp only [circleDot_apply, map_mul, fiberwiseMul_singleAlgHom]

omit [Fintype σ] in
/-- Relabelling the circles transports the selected dot without any sign. -/
@[simp]
theorem reindex_circleDot [Finite σ] (e : σ ≃ τ) (p : σ) (x : CircleTensor R σ) :
    reindex R (fun _ ↦ R[ε]) e (circleDot R p x) =
      circleDot R (e p) (reindex R (fun _ ↦ R[ε]) e x) := by
  let := Fintype.ofFinite σ
  simpa only [← AlgHom.toLinearMap_apply, toLinearMap_fiberwiseMul_equiv,
    LinearEquiv.coe_coe] using fiberwiseMul_circleDot e p x

end Semiring

section Pairing

variable {R : Type*} [CommSemiring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A dot is self-adjoint for the perfect Frobenius pairing of circle tensors. -/
theorem circleDuality_circleDot (p : ι) (x y : CircleTensor R ι) :
    circleDuality R ι (circleDot R p x) y = circleDuality R ι x (circleDot R p y) := by
  have h : (circleDuality R ι).toLinearMap.comp (circleDot R p) =
      (circleDuality R ι).toLinearMap.compl₂ (circleDot R p) := by
    apply (circleBasis R ι).ext
    intro l
    apply (circleBasis R ι).ext
    intro k
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.compl₂_apply,
      circleDot_circleBasis]
    -- Self-adjointness reduces to complementary labels away from the selected circle.
    cases hl : l p <;> cases hk : k p <;>
      simp_all only [Bool.false_eq_true, ↓reduceIte, map_zero, LinearMap.zero_apply,
        circleDuality_apply_circleBasis, Module.Basis.repr_self, Finsupp.single_apply]
    · have heq : (Function.update l p true = fun i ↦ !k i) ↔
          (l = fun i ↦ !(Function.update k p true i)) := by
        constructor <;> intro h <;> funext i <;> by_cases hi : i = p
        · subst i
          simp [hl]
        · simpa [Function.update_of_ne hi] using congrFun h i
        · subst i
          simp [hk]
        · simpa [Function.update_of_ne hi] using congrFun h i
      exact if_congr heq rfl rfl
    · have hn : Function.update l p true ≠ fun i ↦ !k i := by
        intro h
        have := congrFun h p
        simp [hk] at this
      exact ite_eq_right hn
    · have hn : l ≠ fun i ↦ !(Function.update k p true i) := by
        intro h
        have := congrFun h p
        simp [hl] at this
      exact (ite_eq_right hn).symm
  exact congrArg (fun f ↦ f x y) h

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]

/-- A split transports a dot to either corresponding output circle. The same formula covers
unaffected circles and deaths on other factors. -/
theorem fiberwiseSplit_circleDot (f : σ → τ) (p : σ) (x : CircleTensor R τ) :
    fiberwiseSplit f (circleDot R (f p) x) = circleDot R p (fiberwiseSplit f x) := by
  apply (circleDuality R σ).injective
  apply LinearMap.ext
  intro y
  rw [circleDuality_circleDot p, circleDuality_fiberwiseSplit,
    circleDuality_fiberwiseSplit, fiberwiseMul_circleDot, circleDuality_circleDot]

end Pairing

section Coordinates

variable {R : Type*} [CommSemiring R]
variable {ι : Type*} [Finite ι] [DecidableEq ι]

/-- The coefficient of a dotted tensor at `l` is zero when its selected label is `1`.
When that label is `X`, it is the input coefficient with that label replaced by `1`. -/
@[simp↓]
theorem circleBasis_repr_circleDot (p : ι) (x : CircleTensor R ι) (l : ι → Bool) :
    (circleBasis R ι).repr (circleDot R p x) l =
      if l p then (circleBasis R ι).repr x (Function.update l p false) else 0 := by
  let := Fintype.ofFinite ι
  have h := circleDuality_circleDot p x (circleBasis R ι fun i ↦ !l i)
  rw [circleDuality_apply_circleBasis, circleDot_circleBasis] at h
  simp only [Bool.not_not] at h
  have hn : (fun i ↦ !(Function.update (fun j ↦ !l j) p true i)) =
      Function.update l p false := by
    funext i
    by_cases hi : i = p
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  cases hp : l p <;>
    simpa only [hp, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      map_zero, circleDuality_apply_circleBasis, hn] using h

end Coordinates

section Grading

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem labelingQuantumDegree_update_true {l : ι → Bool} {p : ι}
    (hp : l p = false) :
    labelingQuantumDegree ι (Function.update l p true) = labelingQuantumDegree ι l - 2 := by
  simp only [labelingQuantumDegree_def]
  rw [← Finset.add_sum_erase _ _ (mem_univ p),
    ← Finset.add_sum_erase _ _ (mem_univ p)]
  simp only [Function.update_self, hp, Bool.cond_true, Bool.cond_false]
  have h : ∑ i ∈ univ.erase p, (bif Function.update l p true i then (-1 : ℤ) else 1) =
      ∑ i ∈ univ.erase p, (bif l i then (-1 : ℤ) else 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (mem_erase.mp hi).1]
  rw [h]
  omega

/-- Multiplication by `X` on one circle lowers quantum degree by two. -/
theorem isHomogeneous_circleDot (p : ι) :
    TauCeti.LinearMap.IsHomogeneous (circleDot R p)
      (circleQuantumGrading R ι).piece (circleQuantumGrading R ι).piece (-2) := by
  classical
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro q x hx
  rw [mem_circleQuantumGrading_piece_iff] at hx
  rw [← (circleBasis R ι).sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun l _ ↦ ?_
  rw [map_smul]
  by_cases hl : (circleBasis R ι).repr x l = 0
  · simp [hl]
  refine Submodule.smul_mem _ _ ?_
  rw [circleDot_circleBasis]
  cases hp : l p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hx l hl, ← sub_eq_add_neg, ← labelingQuantumDegree_update_true hp]
    exact circleBasis_mem_circleQuantumGrading_piece _
  · simp

end Grading

end TauCeti.Khovanov
