/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Basic

/-!
# Parameter-power quotients of weak completions

The map from a finitely generated algebra to its Monsky–Washnitzer weak completion
induces an isomorphism modulo every power of the parameter. The key point is that
removing a finite head of a degree-growth expansion leaves another degree-growth
expansion. Thus the remainder is divisible by the parameter power in the weak
completion itself, not only in the ambient adic completion.

No noetherianity, completeness or regularity of the parameter is needed.

## References

* M. van der Put, *The cohomology of Monsky and Washnitzer*, §2, (2.1)–(2.2).
* P. Monsky and G. Washnitzer, *Formal cohomology. I*, §2.
-/

public section

namespace TauCeti.Dagger

open Finset MvPolynomial

variable {O S : Type*} [CommRing O] [CommRing S] [Algebra O S] (π : O)

variable [Algebra.FiniteType O S]

namespace weakCompletion

/-- Reduction of a weakly completed element modulo a power of the parameter. -/
noncomputable def eval (n : ℕ) : weakCompletion π S →ₐ[O]
    S ⧸ Ideal.span {algebraMap O S π} ^ n :=
  ((AdicCompletion.evalₐ _ n).restrictScalars O).comp (weakCompletion π S).val

/-- Reduction is the ambient adic-completion projection. -/
theorem eval_eq (n : ℕ) (z : weakCompletion π S) :
    eval π n z = AdicCompletion.evalₐ _ n (z : piAdicCompletion π S) :=
  (rfl)

@[simp]
theorem eval_of (n : ℕ) (s : S) :
    eval π n (of π S s) = Ideal.Quotient.mk _ s := by
  rw [eval_eq, coe_of, AdicCompletion.evalₐ_of]

/-- Reduction sends base scalars to their residue classes. -/
theorem eval_algebraMap (n : ℕ) (a : O) :
    eval π n (algebraMap O (weakCompletion π S) a) =
      Ideal.Quotient.mk _ (algebraMap O S a) :=
  (eval π n).commutes a

/-- Reduction from the weak completion onto each parameter-power quotient is surjective. -/
theorem eval_surjective (n : ℕ) : Function.Surjective (eval π n (S := S)) := by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  exact ⟨of π S s, eval_of π n s⟩

/-- The parameter has vanishing n-th power after reduction modulo its n-th power. -/
theorem eval_parameter_pow (n : ℕ) :
    eval π n (algebraMap O (weakCompletion π S) π) ^ n = 0 := by
  rw [eval_algebraMap, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (Ideal.subset_span rfl) n

/-- An expansion may be evaluated using extra terms, which vanish at level k. -/
private theorem eval_eq_sum_range_add (z : weakCompletion π S) (a : ℕ → S)
    (hz : ∀ k, AdicCompletion.evalₐ _ k (z : piAdicCompletion π S) =
      Ideal.Quotient.mk _ (∑ j ∈ range k, algebraMap O S π ^ j * a j)) (n k : ℕ) :
    AdicCompletion.evalₐ _ k (z : piAdicCompletion π S) =
      Ideal.Quotient.mk _ (∑ j ∈ range (n + k), algebraMap O S π ^ j * a j) := by
  have hπ : Ideal.Quotient.mk (Ideal.span {algebraMap O S π} ^ k)
      (algebraMap O S π ^ k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (Ideal.subset_span rfl) k)
  rw [hz k]
  symm
  rw [Nat.add_comm n k, sum_range_add, map_add, add_eq_left, map_sum]
  apply sum_eq_zero
  intro j hj
  simp only [pow_add, map_mul, hπ, zero_mul]

/-- Every weakly completed element has a finite head in the original algebra and a
weakly completed tail, after factoring out any prescribed power of the parameter. -/
private theorem exists_eq_of_add_pow_mul (z : weakCompletion π S) (n : ℕ) :
    ∃ (s : S) (t : weakCompletion π S),
      z = of π S s + algebraMap O (weakCompletion π S) π ^ n * t := by
  classical
  obtain ⟨g, hg⟩ := Algebra.FiniteType.out (R := O) (A := S)
  let x : g → S := (↑)
  have hx : Algebra.adjoin O (Set.range x) = ⊤ := by
    simpa only [x, Subtype.range_coe_subtype, Finset.setOfPred_mem] using hg
  obtain ⟨c, P, hP, hz⟩ := (mem_weakCompletion_iff π hx).mp z.property
  -- Shift the expansion by n, enlarging its linear degree bound for the tail.
  have htail (j : ℕ) : (P (n + j)).totalDegree ≤ (c * (n + 1)) * (j + 1) := by
    refine (hP (n + j)).trans ?_
    calc c * (n + j + 1) ≤ c * ((n + 1) * (j + 1)) := by
           gcongr
           nlinarith
         _ = c * (n + 1) * (j + 1) := (mul_assoc _ _ _).symm
  obtain ⟨t, ht, hte⟩ := exists_mem_weakCompletionSet_of_degree_le π x
    (fun j ↦ P (n + j)) htail
  have ht' : t ∈ weakCompletion π S := by
    rw [← SetLike.mem_coe, coe_weakCompletion π x hx]
    exact ht
  refine ⟨∑ j ∈ range n, algebraMap O S π ^ j * aeval x (P j), ⟨t, ht'⟩, ?_⟩
  apply Subtype.ext
  apply AdicCompletion.ext_evalₐ
  intro k
  -- Compare at each level k using n + k terms, then split off the first n terms.
  rw [← eval_eq, ← eval_eq]
  simp only [map_add, map_mul, map_pow, eval_of, eval_algebraMap,
    eval_eq π k z, eval_eq π k ⟨t, ht'⟩, hte k]
  rw [eval_eq_sum_range_add π z (fun j ↦ aeval x (P j)) hz n k]
  simp only [sum_range_add, map_add, map_sum, map_mul, map_pow, mul_sum, pow_add,
    mul_assoc]

/-- Every weakly completed element agrees with an original element modulo the
parameter power, with divisibility inside the weak completion. -/
theorem exists_sub_mem_span_pow (z : weakCompletion π S) (n : ℕ) :
    ∃ s : S, z - of π S s ∈
      Ideal.span {algebraMap O (weakCompletion π S) π} ^ n := by
  obtain ⟨s, t, h⟩ := exists_eq_of_add_pow_mul π z n
  refine ⟨s, ?_⟩
  rw [h, add_sub_cancel_left]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span rfl) n)

/-- The kernel of reduction is precisely the parameter-power ideal of the weak
completion, rather than its contraction from an unspecified larger ring. -/
theorem ker_eval (n : ℕ) :
    RingHom.ker (eval π n (S := S)) =
      Ideal.span {algebraMap O (weakCompletion π S) π} ^ n := by
  have hle : Ideal.span {algebraMap O (weakCompletion π S) π} ^ n ≤
      RingHom.ker (eval π n (S := S)) := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker,
      map_pow]
    exact eval_parameter_pow π n
  apply le_antisymm _ hle
  intro z hz
  obtain ⟨s, hs⟩ := exists_sub_mem_span_pow π z n
  have he : eval π n z = 0 := RingHom.mem_ker.mp hz
  have hs0 := RingHom.mem_ker.mp (hle hs)
  rw [map_sub, he, zero_sub, neg_eq_zero, eval_of] at hs0
  have hof : of π S s ∈ Ideal.span {algebraMap O (weakCompletion π S) π} ^ n := by
    have hm : (Ideal.span {algebraMap O S π} ^ n).map (of π S).toRingHom =
        Ideal.span {algebraMap O (weakCompletion π S) π} ^ n := by
      simp [Ideal.map_pow, Ideal.map_span]
    rw [← hm]
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp hs0)
  simpa only [sub_add_cancel] using Ideal.add_mem _ hs hof

/-- Reduction modulo a parameter power identifies the weak completion with the
same quotient of the original algebra. -/
noncomputable def quotientPowEquiv (n : ℕ) :
    (↥(weakCompletion π S) ⧸ (Ideal.span {algebraMap O (weakCompletion π S) π} ^ n)) ≃ₐ[O]
      (S ⧸ (Ideal.span {algebraMap O S π} ^ n)) :=
  (Ideal.quotientEquivAlgOfEq O (ker_eval π n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (eval_surjective π n))

/-- The quotient comparison is the reduction map on representatives. -/
@[simp]
theorem quotientPowEquiv_mk (n : ℕ) (z : weakCompletion π S) :
    quotientPowEquiv π n (Ideal.Quotient.mk _ z) = eval π n z := by
  simp [quotientPowEquiv]

/-- The inverse quotient comparison sends an original element to its weak-completion image. -/
@[simp]
theorem quotientPowEquiv_symm_mk (n : ℕ) (s : S) :
    (quotientPowEquiv π n).symm (Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ (of π S s) := by
  apply (quotientPowEquiv π (S := S) n).injective
  simp

/-- The weak completion is separated for its own parameter-adic filtration. -/
instance isHausdorff :
    IsHausdorff (Ideal.span {algebraMap O (weakCompletion π S) π}) (weakCompletion π S) where
  haus' z hz := by
    apply Subtype.ext
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [Subalgebra.coe_zero, map_zero, ← eval_eq]
    apply RingHom.mem_ker.mp
    rw [ker_eval]
    simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hz n

end weakCompletion

end TauCeti.Dagger
