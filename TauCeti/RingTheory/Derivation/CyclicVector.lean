/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Derivation.DifferentialRing
public import TauCeti.RingTheory.Derivation.DifferentialOperator
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import TauCeti.LinearAlgebra.LinearIndependent.Perturbation

/-!
# The cyclic-vector theorem for differential modules

Let `R` be a commutative ring with a derivation `f ↦ f′` (Mathlib's `Differential R`). A
differential module over `R` is an `R`-module `V` with an additive map `D : V → V` satisfying the
Leibniz rule `D (f • v) = f′ • v + f • D v`; this is the predicate
`TauCeti.IsDifferentialModuleMap R D`. When `R` is a field `F` and `V` has dimension `n`, a cyclic
vector is a `v : V` whose iterates `v, D v, …, Dⁿ⁻¹ v` are linearly independent, hence a basis of
`V`. In that basis `D` is the companion matrix of a single monic scalar differential equation of
order `n`, which is how a differential module, or a connection on a punctured formal disc, is
turned into a scalar linear differential operator.

The main result is the **cyclic-vector theorem** `TauCeti.exists_cyclicVector`: if `F` has
characteristic zero and its derivation is not zero, every differential module over `F` has a
cyclic vector. Neither hypothesis can be dropped. If the derivation is zero, then `D = 0` is a
differential module structure on `F²`, and no vector has two independent iterates. Over
`𝔽_p(t)` with `∂ = d/dt`, the derivation `∂ᵖ` vanishes on `𝔽_p[t]` and hence on `𝔽_p(t)`, so
`D = ∂` coordinatewise on `𝔽_p(t)ᵖ⁺¹` satisfies `Dᵖ = 0` and has no cyclic vector.

As an additive map, `D` is a differential operator of order at most one on `V` in Grothendieck's
sense (`TauCeti.differentialOperators`), whose commutator with multiplication by `a` is
multiplication by `a′`. Hence the `k`-fold iterated commutator of `Dᵏ` with multiplication by `t`
is multiplication by `k! (t′)ᵏ`, and the operators `Dⁱ` with `i < k` have vanishing `k`-fold
commutators. In characteristic zero, with `t′ ≠ 0`, it follows that for every operator
`L = Dᵏ - ∑_{i < k} aᵢ Dⁱ` and every `v` outside a subspace `W`, some multiple `c • v` has
`L (c • v) ∉ W` (`TauCeti.IsDifferentialModuleMap.exists_iterate_smul_sub_sum_notMem`).

The theorem follows Deligne's argument. Let `e` have the largest number `k` of independent
iterates, and suppose `k < n`. The iterates span a `D`-stable subspace `W`, so
`Dᵏ e = ∑_{i < k} aᵢ Dⁱ e` and `L e = 0`. Choose `f ∉ W` and `c` with `y = L (c • f) ∉ W`. For a
natural number `λ`, the iterates of `e + λ c f` are `Dⁱ e + λ Dⁱ (c • f)`, and
`L (e + λ c f) = λ y`. Since the iterates of `e` together with `y` are independent, a generic
perturbation (`LinearIndependent.eventually_cofinite_add_smul`) shows that for all but finitely
many `λ` the first `k` iterates of `e + λ c f` together with `y` are independent, so
`e + λ c f` has `k + 1` independent iterates, contradicting the maximality of `k`.

## Main definitions

* `TauCeti.IsDifferentialModuleMap R D`: `D` satisfies the Leibniz rule over `(R, f ↦ f′)`.

## Main results

* `TauCeti.IsDifferentialModuleMap.toIntLinearMap_mem_differentialOperators`: `D` is a
  differential operator of order at most one.
* `TauCeti.IsDifferentialModuleMap.smulCommutator_pow_toIntLinearMap_pow_apply`: the `k`-fold
  commutator of `Dᵏ` with multiplication by `a` is multiplication by `k! (a′)ᵏ`.
* `TauCeti.IsDifferentialModuleMap.exists_iterate_smul_sub_sum_notMem`: a monic operator
  `Dᵏ - ∑_{i < k} aᵢ Dⁱ` does not map the line through a vector `v ∉ W` into `W`.
* `TauCeti.exists_cyclicVector`: the cyclic-vector theorem.

## References

* P. Deligne, *Équations différentielles à points singuliers réguliers*, Lecture Notes in
  Mathematics 163, Springer, 1970, Ch. II, Lemme 1.3.
* N. M. Katz, *A simple algorithm for cyclic vectors*, Amer. J. Math. 109 (1987), 65–70.
-/

public section

open Module
open scoped Differential Nat

namespace TauCeti

section CommRing

variable (R : Type*) {V : Type*} [CommRing R] [Differential R] [AddCommGroup V] [Module R V]

/-- An additive map `D : V → V` on a module over a differential ring `(R, f ↦ f′)` makes `V` a
differential module when it satisfies the Leibniz rule `D (f • v) = f′ • v + f • D v`. -/
structure IsDifferentialModuleMap (D : V →+ V) : Prop where
  /-- The Leibniz rule. -/
  leibniz (f : R) (v : V) : D (f • v) = f′ • v + f • D v

variable {R}

namespace IsDifferentialModuleMap

variable {D : V →+ V} (hD : IsDifferentialModuleMap R D)
include hD

/-- The commutator of `D` with multiplication by `a` is multiplication by `a′`. -/
theorem smulCommutator_toIntLinearMap_apply (a : R) (v : V) :
    smulCommutator ℤ a D.toIntLinearMap v = a′ • v := by
  simp [hD.leibniz]

/-- `D` is a differential operator of order at most one. -/
theorem toIntLinearMap_mem_differentialOperators :
    D.toIntLinearMap ∈ differentialOperators ℤ R V V 1 := by
  refine mem_differentialOperators_succ_iff.2 fun a ↦ mem_differentialOperators_zero_iff.2 ?_
  intro b v
  rw [hD.smulCommutator_toIntLinearMap_apply, hD.smulCommutator_toIntLinearMap_apply, smul_comm]

/-- The `k`-th iterate of `D` is a differential operator of order at most `k`. -/
theorem toIntLinearMap_pow_mem_differentialOperators (k : ℕ) :
    D.toIntLinearMap ^ k ∈ differentialOperators ℤ R V V k := by
  simpa using SetLike.pow_mem_graded k hD.toIntLinearMap_mem_differentialOperators

/-- The `k`-fold commutator of `Dᵏ` with multiplication by `a` is multiplication by
`k! (a′)ᵏ`. -/
theorem smulCommutator_pow_toIntLinearMap_pow_apply (a : R) (k : ℕ) (v : V) :
    (smulCommutator ℤ a ^ k) (D.toIntLinearMap ^ k) v = ((k ! : R) * a′ ^ k) • v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' D.toIntLinearMap, Module.End.mul_eq_comp, add_comm k 1,
      smulCommutator_pow_comp_of_mem hD.toIntLinearMap_mem_differentialOperators
        (hD.toIntLinearMap_pow_mem_differentialOperators k) a]
    simp only [pow_one, LinearMap.smul_apply, LinearMap.comp_apply, ih,
      hD.smulCommutator_toIntLinearMap_apply, Nat.choose_one_right, smul_smul,
      ← Nat.cast_smul_eq_nsmul R]
    rw [add_comm 1 k, Nat.factorial_succ]
    congr 1
    push_cast
    ring

end IsDifferentialModuleMap

end CommRing

section Field

variable {F V : Type*} [Field F] [Differential F] [CharZero F] [AddCommGroup V] [Module F V]
  {D : V →+ V}

/-- In characteristic zero, with a nonzero derivation, a monic operator `Dᵏ - ∑_{i < k} aᵢ Dⁱ`
does not map the line through a vector `v ∉ W` into the subspace `W`: some multiple `c • v` is
sent outside `W`. -/
theorem IsDifferentialModuleMap.exists_iterate_smul_sub_sum_notMem
    (hD : IsDifferentialModuleMap F D) (hd : (Differential.deriv : Derivation ℤ F F) ≠ 0)
    {k : ℕ} (a : Fin k → F) {W : Submodule F V} {v : V} (hv : v ∉ W) :
    ∃ c : F, (⇑D)^[k] (c • v) - ∑ i, a i • (⇑D)^[i] (c • v) ∉ W := by
  obtain ⟨t, ht⟩ : ∃ t : F, t′ ≠ 0 := by
    by_contra! h
    exact hd (Derivation.ext h)
  let L : Module.End ℤ V := D.toIntLinearMap ^ k - ∑ i, a i • D.toIntLinearMap ^ (i : ℕ)
  have hL (w : V) : L w = (⇑D)^[k] w - ∑ i, a i • (⇑D)^[i] w := by
    simp [L, pow_apply_eq_iterate]
  by_contra! h
  -- Iterated commutators with multiplication by `t` still map the line `F • v` into `W`.
  have hW (j : ℕ) (c : F) : (smulCommutator ℤ t ^ j) L (c • v) ∈ W := by
    induction j generalizing c with
    | zero => simpa [hL] using h c
    | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp, smulCommutator_apply_apply, smul_smul]
      exact W.sub_mem (ih _) (W.smul_mem t (ih c))
  -- Only the leading term `Dᵏ` survives the `k`-fold commutator.
  have htop : (smulCommutator ℤ t ^ k) L = (smulCommutator ℤ t ^ k) (D.toIntLinearMap ^ k) := by
    rw [map_sub, map_sum, sub_eq_self]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    exact smulCommutator_pow_eq_zero
      (smul_mem_differentialOperators (a i) (hD.toIntLinearMap_pow_mem_differentialOperators i))
      i.isLt t
  have hk := hW k 1
  rw [htop, one_smul, hD.smulCommutator_pow_toIntLinearMap_pow_apply] at hk
  exact hv ((W.smul_mem_iff (mul_ne_zero (Nat.cast_ne_zero.2 k.factorial_ne_zero)
    (pow_ne_zero k ht))).1 hk)

/-- The inductive step of the cyclic-vector theorem: a vector with `k < dim V` independent
iterates can be perturbed to one with `k + 1` independent iterates. -/
private theorem IsDifferentialModuleMap.exists_linearIndependent_iterate_succ
    (hD : IsDifferentialModuleMap F D) (hd : (Differential.deriv : Derivation ℤ F F) ≠ 0)
    {k : ℕ} (hk : k < finrank F V) {e : V}
    (he : LinearIndependent F fun i : Fin k ↦ (⇑D)^[i] e) :
    ∃ e' : V, LinearIndependent F fun i : Fin (k + 1) ↦ (⇑D)^[i] e' := by
  set W := Submodule.span F (Set.range fun i : Fin k ↦ (⇑D)^[i] e)
  by_cases hke : (⇑D)^[k] e ∉ W
  · refine ⟨e, ?_⟩
    rw [← Fin.snoc_init_self (fun i : Fin (k + 1) ↦ (⇑D)^[i] e)]
    exact he.finSnoc hke
  push Not at hke
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hke
  obtain ⟨f, hf⟩ : ∃ f, f ∉ W := by
    by_contra! h
    have hW : finrank F W = Fintype.card (Fin k) := finrank_span_eq_card he
    have hWtop : W = ⊤ := eq_top_iff.2 fun f _ ↦ h f
    rw [hWtop, finrank_top, Fintype.card_fin] at hW
    exact hk.ne hW.symm
  obtain ⟨c, hc⟩ := hD.exists_iterate_smul_sub_sum_notMem hd a hf
  set g := c • f
  set y := (⇑D)^[k] g - ∑ i, a i • (⇑D)^[i] g
  -- Perturb `e` by a nonzero natural multiple `n • g` that keeps the relevant family independent.
  have hev := (he.finSnoc hc).eventually_cofinite_add_smul
    (Fin.snoc (fun i : Fin k ↦ (⇑D)^[i] g) 0 : Fin (k + 1) → V)
  obtain ⟨n, hn, hn0⟩ :=
    ((Nat.cast_injective.tendsto_cofinite.eventually hev).and
      (Filter.eventually_cofinite_ne 0)).exists
  have hiter (j : ℕ) : (⇑D)^[j] (e + (n : F) • g) = (⇑D)^[j] e + (n : F) • (⇑D)^[j] g := by
    rw [iterate_map_add, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, iterate_map_nsmul]
  have heq : (Fin.snoc (fun i : Fin k ↦ (⇑D)^[i] e) y : Fin (k + 1) → V) +
      (n : F) • (Fin.snoc (fun i : Fin k ↦ (⇑D)^[i] g) 0 : Fin (k + 1) → V) =
      Fin.snoc (fun i : Fin k ↦ (⇑D)^[i] (e + (n : F) • g)) y := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [hiter]
  rw [heq] at hn
  obtain ⟨hz, hyz⟩ := linearIndependent_finSnoc.1 hn
  refine ⟨e + (n : F) • g, ?_⟩
  rw [← Fin.snoc_init_self (fun i : Fin (k + 1) ↦ (⇑D)^[i] (e + (n : F) • g))]
  refine hz.finSnoc fun hmem ↦ hyz ?_
  -- `Dᵏ` of the perturbed vector is a combination of its lower iterates plus `n • y`.
  have hDk : (⇑D)^[k] (e + (n : F) • g) =
      ∑ i, a i • (⇑D)^[i] (e + (n : F) • g) + (n : F) • y := by
    simp only [hiter, y, smul_add, Finset.sum_add_distrib, smul_sub, ← ha, Finset.smul_sum,
      smul_comm (n : F)]
    abel
  rw [Fin.val_last, hDk] at hmem
  have hsum : ∑ i, a i • (⇑D)^[i] (e + (n : F) • g) ∈
      Submodule.span F (Set.range fun i : Fin k ↦ (⇑D)^[i] (e + (n : F) • g)) :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hn0 : (n : F) ≠ 0)).1 ?_
  simpa using Submodule.sub_mem _ hmem hsum

variable (F) in
/-- **The cyclic-vector theorem.** Over a field of characteristic zero whose derivation is not
zero, every differential module `(V, D)` has a cyclic vector: a vector `v` whose iterates
`v, D v, …, Dⁿ⁻¹ v`, `n = finrank F V`, are linearly independent. When `V` is
finite-dimensional they therefore span `V` (`LinearIndependent.span_eq_top_of_card_eq_finrank'`);
when it is not, `finrank F V = 0` and the statement is empty. -/
theorem exists_cyclicVector (hd : (Differential.deriv : Derivation ℤ F F) ≠ 0) (D : V →+ V)
    (hD : IsDifferentialModuleMap F D) :
    ∃ v : V, LinearIndependent F fun i : Fin (finrank F V) ↦ (⇑D)^[i] v := by
  suffices ∀ k ≤ finrank F V, ∃ v : V, LinearIndependent F fun i : Fin k ↦ (⇑D)^[i] v from
    this _ le_rfl
  intro k hk
  induction k with
  | zero => exact ⟨0, linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨e, he⟩ := ih (by omega)
    exact hD.exists_linearIndependent_iterate_succ hd (by omega) he

end Field

end TauCeti
