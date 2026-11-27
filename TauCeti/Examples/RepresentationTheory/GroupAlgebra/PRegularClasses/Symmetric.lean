/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.PRegularClasses
import TauCeti.Algebra.MonoidAlgebra.NotReduced
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# The `p`-regular classes of `S₃` and the `p`-power commutator subspace of `k[S₃]`

Checks for the count `TauCeti.finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra` on
`S₃ = Equiv.Perm (Fin 3)`, with `ρ` a `3`-cycle and `s` a transposition:

* `p = 2`: the `2`-regular classes are those of `1` and `ρ`, so `T(k[S₃])` has codimension `2`
  over every field `k` of characteristic `2`. Every transposition `t` satisfies `(t - 1)² = 0`,
  so `t ≡ 1` modulo `T`, and the images of `1` and `ρ` form a basis of `k[S₃] / T(k[S₃])`.
  Since the coefficient sum over the class of `s` kills every commutator and takes the value `1`
  at `s - 1`, the commutator subspace `[A, A]` is strictly smaller than `T(k[S₃])`.
* `p = 3`: the `3`-regular classes are those of `1` and `s`, so `T(k[S₃])` has codimension `2`
  over every field of characteristic `3`.
-/

public section

namespace TauCeti.PRegularClassesSymmetricExamples

open _root_.MonoidAlgebra Module TauCeti.GroupAlgebraBlockExamples

/-- Every element of `S₃` other than `1` and the `3`-cycles is an involution. -/
private theorem mul_self_eq_one_of_ne (g : S₃) (h : g * g * g ≠ 1) : g * g = 1 := by
  revert g
  decide +kernel

/-- The order of an element of `S₃`: `1` for the identity, `3` for the `3`-cycles and `2` for
the transpositions. -/
theorem orderOf_eq (g : S₃) :
    orderOf g = if g = 1 then 1 else if g * g * g = 1 then 3 else 2 := by
  split_ifs with h1 h3
  · simp [h1]
  · exact orderOf_eq_prime (by rw [pow_three, ← mul_assoc, h3]) h1
  · exact orderOf_eq_prime (by rw [sq, mul_self_eq_one_of_ne g h3]) h1

/-- The class of `g` is `2`-regular exactly when `g³ = 1`. -/
theorem mk_mem_pRegularConjClasses_two_iff (g : S₃) :
    ConjClasses.mk g ∈ pRegularConjClasses 2 S₃ ↔ g * g * g = 1 := by
  rw [mk_mem_pRegularConjClasses_iff, orderOf_eq]
  split_ifs with h1 h3
  · simp [h1]
  · exact iff_of_true (by decide) h3
  · exact iff_of_false (by decide) h3

/-- The class of `g` is `3`-regular exactly when `g² = 1`. -/
theorem mk_mem_pRegularConjClasses_three_iff (g : S₃) :
    ConjClasses.mk g ∈ pRegularConjClasses 3 S₃ ↔ g * g = 1 := by
  rw [mk_mem_pRegularConjClasses_iff, orderOf_eq]
  split_ifs with h1 h3
  · simp [h1]
  · have h2 : g * g ≠ 1 := fun h2 ↦ h1 (by rwa [h2, one_mul] at h3)
    exact iff_of_false (by decide) h2
  · exact iff_of_true (by decide) (mul_self_eq_one_of_ne g h3)

/-- The class of `1` differs from the class of every `x ≠ 1`. -/
private theorem mk_one_ne_mk {x : S₃} (hx : x ≠ 1) : ConjClasses.mk 1 ≠ ConjClasses.mk x := by
  rwa [Ne, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_right]

/-- If the classes in a set `C` are those of the `g` with `P g`, and the elements conjugate to
`x` are those `g ≠ 1` with `P g`, where `P 1` holds, then `C` consists of the classes of `1` and
`x`. -/
private theorem eq_pair_of_mem_iff {C : Set (ConjClasses S₃)} {P : S₃ → Prop} {x : S₃} (h1 : P 1)
    (hC : ∀ g, ConjClasses.mk g ∈ C ↔ P g) (hx : ∀ g, IsConj g x ↔ g ≠ 1 ∧ P g) :
    C = {ConjClasses.mk 1, ConjClasses.mk x} := by
  ext c
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  rw [hC, Set.mem_insert_iff, Set.mem_singleton_iff, ConjClasses.mk_eq_mk_iff_isConj,
    ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left, hx]
  constructor
  · intro h
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ⟨hg, h⟩
  · rintro (rfl | ⟨-, h⟩)
    · exact h1
    · exact h

/-- The `2`-regular classes of `S₃` are those of `1` and of the `3`-cycle `ρ`. -/
theorem pRegularConjClasses_two :
    pRegularConjClasses 2 S₃ = {ConjClasses.mk 1, ConjClasses.mk ρ} :=
  eq_pair_of_mem_iff (by simp) mk_mem_pRegularConjClasses_two_iff isConj_ρ_iff

/-- The `3`-regular classes of `S₃` are those of `1` and of the transposition `s`. -/
theorem pRegularConjClasses_three :
    pRegularConjClasses 3 S₃ = {ConjClasses.mk 1, ConjClasses.mk s} :=
  eq_pair_of_mem_iff (by simp) mk_mem_pRegularConjClasses_three_iff isConj_s_iff

/-- `S₃` has two `2`-regular classes. -/
theorem card_pRegularConjClasses_two : Nat.card (pRegularConjClasses 2 S₃) = 2 := by
  rw [pRegularConjClasses_two, Nat.card_coe_set_eq, Set.ncard_pair (mk_one_ne_mk (by decide))]

/-- `S₃` has two `3`-regular classes. -/
theorem card_pRegularConjClasses_three : Nat.card (pRegularConjClasses 3 S₃) = 2 := by
  rw [pRegularConjClasses_three, Nat.card_coe_set_eq, Set.ncard_pair (mk_one_ne_mk (by decide))]

section CommRing

variable (k : Type*) [CommRing k]

/-- The coefficient sum over the class of `s` takes the value `1` at `s - 1`, so `s - 1` is not
a sum of commutators. -/
theorem single_s_sub_one_notMem_commutatorSubmodule [Nontrivial k] :
    single s (1 : k) - 1 ∉ commutatorSubmodule k (MonoidAlgebra k S₃) := by
  intro h
  have h0 := commutatorSubmodule_le_ker_classCoeff k (ConjClasses.mk s) h
  rw [LinearMap.mem_ker, map_sub, one_def, classCoeff_single, classCoeff_single] at h0
  simp [mk_one_ne_mk (show s ≠ 1 by decide)] at h0

/-- In characteristic `2`, an involution `t` of `S₃` satisfies `(t - 1)² = 0`, so `t ≡ 1` modulo
`T(k[S₃])`. -/
theorem single_sub_one_mem_pPowerCommutatorSubmodule_of_mul_self_eq_one [CharP k 2] {t : S₃}
    (ht : t * t = 1) :
    single t (1 : k) - 1 ∈ pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃) :=
  mem_pPowerCommutatorSubmodule_of_isNilpotent 2 k
    (isNilpotent_single_sub_one 2 (n := 1) (by rw [pow_one, sq, ht]))

/-- **`T(k[S₃])` is not `[A, A]` in characteristic `2`**: the commutator subspace is strictly
contained in the `2`-power commutator subspace, as `s - 1` lies in the latter only. -/
theorem commutatorSubmodule_lt_pPowerCommutatorSubmodule [CharP k 2] [Nontrivial k] :
    commutatorSubmodule k (MonoidAlgebra k S₃) <
      pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃) :=
  lt_of_le_of_ne (commutatorSubmodule_le_pPowerCommutatorSubmodule 2 k) fun h ↦
    single_s_sub_one_notMem_commutatorSubmodule k
      (h ▸ single_sub_one_mem_pPowerCommutatorSubmodule_of_mul_self_eq_one k (by decide))

end CommRing

variable (k : Type*) [Field k]

/-- Over a field of characteristic `3`, `T(k[S₃])` has codimension `2`, the number of `3`-regular
classes of `S₃` (the identity and the transpositions). -/
theorem finrank_quotient_pPowerCommutatorSubmodule_three [CharP k 3] :
    finrank k (MonoidAlgebra k S₃ ⧸ pPowerCommutatorSubmodule 3 k (MonoidAlgebra k S₃)) = 2 := by
  rw [finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra, card_pRegularConjClasses_three]

variable [CharP k 2]

/-- Over a field of characteristic `2`, `T(k[S₃])` has codimension `2`, the number of `2`-regular
classes of `S₃` (the identity and the `3`-cycles). -/
theorem finrank_quotient_pPowerCommutatorSubmodule_two :
    finrank k (MonoidAlgebra k S₃ ⧸ pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)) = 2 := by
  rw [finrank_quotient_pPowerCommutatorSubmodule_monoidAlgebra, card_pRegularConjClasses_two]

/-- Every element of `S₃` is congruent to `1` or to `ρ` modulo `T(k[S₃])` in characteristic `2`. -/
private theorem mkQ_single_mem_span (g : S₃) :
    (pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ (single g 1) ∈
      Submodule.span k (Set.range ![(pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ 1,
        (pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ (single ρ 1)]) := by
  by_cases h3 : g ≠ 1 ∧ g * g * g = 1
  · have hc := (isConj_ρ_iff g).2 h3
    have h : (pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ (single g 1) =
        (pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ (single ρ 1) := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact commutatorSubmodule_le_pPowerCommutatorSubmodule 2 k
        (single_sub_single_mem_commutatorSubmodule_of_isConj k hc.symm 1)
    rw [h]
    exact Submodule.subset_span ⟨1, rfl⟩
  · have h2 : g * g = 1 := by
      by_cases h1 : g = 1
      · simp [h1]
      · exact mul_self_eq_one_of_ne g fun h ↦ h3 ⟨h1, h⟩
    have h : (pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ (single g 1) =
        (pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ 1 := by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact single_sub_one_mem_pPowerCommutatorSubmodule_of_mul_self_eq_one k h2
    rw [h]
    exact Submodule.subset_span ⟨0, rfl⟩

/-- **A basis of `k[S₃] / T(k[S₃])` in characteristic `2`**: the images of `1` and of the
`3`-cycle `ρ` are linearly independent modulo `T(k[S₃])`. -/
theorem linearIndependent_mkQ_one_ρ :
    LinearIndependent k ![(pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ 1,
      (pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)).mkQ (single ρ 1)] := by
  set T := pPowerCommutatorSubmodule 2 k (MonoidAlgebra k S₃)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rintro x -
    obtain ⟨x, rfl⟩ := T.mkQ_surjective x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | single g a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul]
      exact Submodule.smul_mem _ _ (mkQ_single_mem_span k g)
  · rw [Fintype.card_fin, finrank_quotient_pPowerCommutatorSubmodule_two]

end TauCeti.PRegularClassesSymmetricExamples
