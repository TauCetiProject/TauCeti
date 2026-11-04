/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.BigOperators
public import TauCeti.LinearAlgebra.Trace.Pi
public import TauCeti.RingTheory.Semisimple.Multiplicity
public import TauCeti.RingTheory.SimpleModule.Basic

/-!
# Semisimple modules are determined by their traces

Let `A` be an algebra over a field `k` of characteristic zero. A finite-dimensional semisimple
`A`-module `M` gives the trace function `a ↦ tr_k (a • · : M → M)` on `A`. This file proves that
the trace function determines `M` up to isomorphism
(`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`). No finiteness is asked of `A`,
which is the point: for the group algebra of an infinite group, such as `GL n ℂ`, it is what lets
characters determine semisimple representations.

The argument isolates one isotypic type at a time by an element of `A`. For a semisimple module
`X` finite over its endomorphism ring and a simple module `S`, the projection of `X` onto its
`S`-isotypic component along the sum of the other isotypic components commutes with every
endomorphism, because isotypic components are fully invariant. Jacobson density then writes it
as the action of some `a : A` (`IsSemisimpleModule.exists_forall_smul_eq_ite`): `a` acts
as the identity on every simple submodule of `X` isomorphic to `S`, and as zero on every other
simple submodule. Applied to `X = M × N`, the trace of `a` on `M` is the multiplicity of `S` in
`M` times the dimension of `S`, and likewise on `N`. In characteristic zero equal traces therefore
give equal multiplicities, and finite semisimple modules with equal multiplicities are isomorphic
(`IsSemisimpleModule.nonempty_linearEquiv_of_jordanHolderMultiplicity_eq`).

## Main results

* `IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`: **finite-dimensional semisimple
  modules over an algebra in characteristic zero with the same traces are isomorphic.**

## References

* S. Lang, *Algebra*, revised third edition, Chapter XVII, Corollary 3.8.
-/

public section

open Module TauCeti

universe u

namespace IsSemisimpleModule

section Trace

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]

open scoped Classical in
/-- An element acting as in `IsSemisimpleModule.exists_forall_smul_eq_ite` on the simple
submodules of `X` acts in the same way on every simple module embedded in `X`. -/
private theorem smul_eq_ite_of_injective {X : Type*} [AddCommGroup X] [Module A X]
    {S : Type*} [AddCommGroup S] [Module A S] {a : A}
    (ha : ∀ T : Submodule A X, IsSimpleModule A T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[A] S) then x else 0)
    {Y : Type*} [AddCommGroup Y] [Module A Y] [IsSimpleModule A Y]
    (f : Y →ₗ[A] X) (hf : Function.Injective f) (y : Y) :
    a • y = if Nonempty (S ≃ₗ[A] Y) then y else 0 := by
  let e := LinearEquiv.ofInjective f hf
  have hT : IsSimpleModule A (LinearMap.range f) := IsSimpleModule.congr e.symm
  have hiff : Nonempty (LinearMap.range f ≃ₗ[A] S) ↔ Nonempty (S ≃ₗ[A] Y) :=
    ⟨fun ⟨e'⟩ => ⟨e'.symm.trans e.symm⟩, fun ⟨e'⟩ => ⟨(e'.trans e).symm⟩⟩
  have hy := ha _ hT (f y) (LinearMap.mem_range_self f y)
  rw [← map_smul, hiff] at hy
  apply hf
  split_ifs at hy ⊢ <;> simpa using hy

open scoped Classical in
/-- The trace of such an element on a module embedded in `X`, computed on a decomposition into
simple submodules, adds up the dimensions of the summands isomorphic to `S`. -/
private theorem trace_lsmul_eq_sum_ite {X : Type*} [AddCommGroup X] [Module A X]
    {S : Type*} [AddCommGroup S] [Module A S] {a : A}
    (ha : ∀ T : Submodule A X, IsSimpleModule A T → ∀ x ∈ T,
      a • x = if Nonempty (T ≃ₗ[A] S) then x else 0)
    {P : Type*} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
    [FiniteDimensional k P] {n : ℕ} (Q : Fin n → Submodule A P) (e : P ≃ₗ[A] ∀ i, Q i)
    (hQ : ∀ i, IsSimpleModule A (Q i)) (j : P →ₗ[A] X) (hj : Function.Injective j) :
    LinearMap.trace k P (Algebra.lsmul k k P a) =
      ∑ i, if Nonempty (S ≃ₗ[A] Q i) then (finrank k (Q i) : k) else 0 := by
  have (i : Fin n) : Module.Finite k (Q i) :=
    .of_injective ((Q i).subtype.restrictScalars k) Subtype.val_injective
  rw [← LinearMap.trace_conj' _ (e.restrictScalars k), LinearMap.trace_pi]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hQa (y : Q i) : a • y = if Nonempty (S ≃ₗ[A] Q i) then y else 0 :=
    have := hQ i
    smul_eq_ite_of_injective ha (j ∘ₗ e.symm.toLinearMap ∘ₗ LinearMap.single A (fun i => Q i) i)
      (hj.comp (e.symm.injective.comp fun _ _ h => Pi.single_injective i h)) y
  have hblock : LinearMap.proj i ∘ₗ (e.restrictScalars k).conj (Algebra.lsmul k k P a) ∘ₗ
      LinearMap.single k (fun i => Q i) i =
        if Nonempty (S ≃ₗ[A] Q i) then LinearMap.id else 0 := by
    ext y
    simp only [LinearMap.comp_apply, LinearEquiv.conj_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, Algebra.lsmul_coe, map_smul, LinearMap.proj_apply,
      LinearMap.coe_single, Pi.smul_apply, hQa]
    split_ifs <;> simp
  rw [hblock]
  split_ifs <;> simp

/-- **Semisimple modules are determined by their traces.** Over an algebra `A` over a field of
characteristic zero, two finite-dimensional semisimple `A`-modules on which every element of `A`
acts with the same trace are isomorphic. No finiteness is asked of `A`. -/
theorem nonempty_linearEquiv_of_trace_eq [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [FiniteDimensional k M] [IsSemisimpleModule A M]
    (N : Type*) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
    [FiniteDimensional k N] [IsSemisimpleModule A N]
    (h : ∀ a : A, LinearMap.trace k M (Algebra.lsmul k k M a) =
      LinearMap.trace k N (Algebra.lsmul k k N a)) :
    Nonempty (M ≃ₗ[A] N) := by
  classical
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite k A N
  have : Module.Finite (Module.End A (M × N)) (M × N) :=
    Module.Finite.of_restrictScalars_finite k _ _
  refine nonempty_linearEquiv_of_jordanHolderMultiplicity_eq M N fun S _ _ _ => ?_
  obtain ⟨a, ha⟩ := exists_forall_smul_eq_ite (R := A) (M := M × N) S
  obtain ⟨n, P, eP, hP⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A M
  obtain ⟨m, Q, eQ, hQ⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp A N
  let _ (i : Fin n) : IsSimpleModule A (P i) := hP i
  let _ (i : Fin m) : IsSimpleModule A (Q i) := hQ i
  let eM : M ≃ₗ[A] ∀ i, P i := eP.trans DFinsupp.linearEquivFunOnFintype
  let eN : N ≃ₗ[A] ∀ i, Q i := eQ.trans DFinsupp.linearEquivFunOnFintype
  rw [jordanHolderMultiplicity_eq_of_linearEquiv eM, jordanHolderMultiplicity_pi_eq_natCard,
    jordanHolderMultiplicity_eq_of_linearEquiv eN, jordanHolderMultiplicity_pi_eq_natCard]
  have htM :=
    trace_lsmul_eq_sum_ite (k := k) ha P eM hP (LinearMap.inl A M N) LinearMap.inl_injective
  have htN :=
    trace_lsmul_eq_sum_ite (k := k) ha Q eN hQ (LinearMap.inr A M N) LinearMap.inr_injective
  by_cases hS : (∃ i, Nonempty (S ≃ₗ[A] P i)) ∨ ∃ j, Nonempty (S ≃ₗ[A] Q j)
  · -- All the summands of type `S`, in `M` and in `N`, have one common positive dimension `d`.
    obtain ⟨d, hd, hdP, hdQ⟩ : ∃ d : ℕ, 0 < d ∧
        (∀ i, Nonempty (S ≃ₗ[A] P i) → finrank k (P i) = d) ∧
        ∀ j, Nonempty (S ≃ₗ[A] Q j) → finrank k (Q j) = d := by
      rcases hS with ⟨i₀, ⟨e₀⟩⟩ | ⟨j₀, ⟨e₀⟩⟩
      · have : Module.Finite k (P i₀) :=
          .of_injective ((P i₀).subtype.restrictScalars k) Subtype.val_injective
        have : Nontrivial (P i₀) := IsSimpleModule.nontrivial A _
        exact ⟨_, finrank_pos, fun i ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq,
          fun j ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq⟩
      · have : Module.Finite k (Q j₀) :=
          .of_injective ((Q j₀).subtype.restrictScalars k) Subtype.val_injective
        have : Nontrivial (Q j₀) := IsSimpleModule.nontrivial A _
        exact ⟨_, finrank_pos, fun i ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq,
          fun j ⟨e⟩ => ((e.symm.trans e₀).restrictScalars k).finrank_eq⟩
    have heq := (htM.symm.trans (h a)).trans htN
    rw [Fintype.sum_ite_eq_card_nsmul fun i hi ↦ congrArg Nat.cast (hdP i hi),
      Fintype.sum_ite_eq_card_nsmul fun j hj ↦ congrArg Nat.cast (hdQ j hj), nsmul_eq_mul,
      nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_mul] at heq
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.cast_injective heq)
  · -- If `S` occurs in neither module, both counts vanish.
    push Not at hS
    have : IsEmpty {i // Nonempty (S ≃ₗ[A] P i)} := ⟨fun i => (hS.1 i.1).false i.2.some⟩
    have : IsEmpty {j // Nonempty (S ≃ₗ[A] Q j)} := ⟨fun j => (hS.2 j.1).false j.2.some⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

end Trace

end IsSemisimpleModule
