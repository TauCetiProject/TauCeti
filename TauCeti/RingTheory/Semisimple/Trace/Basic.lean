/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.BigOperators
public import TauCeti.LinearAlgebra.Trace.Pi
public import TauCeti.RingTheory.Semisimple.Burnside
public import TauCeti.RingTheory.Semisimple.Multiplicity
public import TauCeti.RingTheory.SimpleModule.Basic
import TauCeti.LinearAlgebra.Pi

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

Over any field, the trace of `a` on a semisimple module is `∑ i, [M : T_i] • tr(a | T_i)` for a
family `T_i` of pairwise non-isomorphic modules covering its simple submodules
(`IsSemisimpleModule.trace_lsmul_eq_sum`). Over an algebraically closed field of any
characteristic, Burnside's theorem shows that the traces on a spanning set of `A` determine the
multiplicities cast into `k` (`IsSemisimpleModule.natCast_eq_of_sum_trace_eq`).

## Main results

* `IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq`: **finite-dimensional semisimple
  modules over an algebra in characteristic zero with the same traces are isomorphic.**
* `IsSemisimpleModule.trace_lsmul_eq_sum`: the trace on a semisimple module, computed from the
  multiplicities of its simple constituents.
* `IsSemisimpleModule.natCast_jordanHolderMultiplicity_eq_of_trace_eq`: over an algebraically
  closed field, semisimple modules with the same trace on a spanning set have the same
  multiplicities of every simple module, cast into `k`.

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
  obtain ⟨n, P, hP, ⟨eM⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_submodule (R := A) M
  obtain ⟨m, Q, hQ, ⟨eN⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_submodule (R := A) N
  let _ (i : Fin n) : IsSimpleModule A (P i) := hP i
  let _ (i : Fin m) : IsSimpleModule A (Q i) := hQ i
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
    have : IsEmpty {i // Nonempty (S ≃ₗ[A] P i)} := ⟨fun i => (hS.1 i.val).false i.property.some⟩
    have : IsEmpty {j // Nonempty (S ≃ₗ[A] Q j)} := ⟨fun j => (hS.2 j.val).false j.property.some⟩
    rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]

end Trace

section Multiplicity

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

section Decomposition

variable {ι : Type*} [Fintype ι] {T : ι → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)]
  [∀ i, Module A (T i)] [∀ i, IsScalarTower k A (T i)] [∀ i, FiniteDimensional k (T i)]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [IsSemisimpleModule A M] [Module.Finite A M]

/-- **The trace on a semisimple module.** If every simple submodule of `M` is isomorphic to one
of the pairwise non-isomorphic modules `T i`, then the trace of `a` on `M` is
`∑ i, [M : T i] • tr(a | T i)`. -/
theorem trace_lsmul_eq_sum (hT : Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j))
    (hM : ∀ P : Submodule A M, IsSimpleModule A P → ∃ i, Nonempty (P ≃ₗ[A] T i)) (a : A) :
    LinearMap.trace k M (Algebra.lsmul k k M a) =
      ∑ i, jordanHolderMultiplicity A M (T i) • LinearMap.trace k (T i) (Algebra.lsmul k k (T i) a)
    := by
  classical
  obtain ⟨n, σ, ⟨e⟩, hσ⟩ := exists_linearEquiv_pi_natCard_eq hT hM
  rw [← LinearMap.trace_conj' _ (e.restrictScalars k), e.conj_lsmul_eq_piMap,
    LinearMap.trace_piMap, ← Finset.sum_fiberwise Finset.univ σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const,
    ← hσ i, Nat.card_eq_fintype_card, Fintype.card_subtype]

end Decomposition

variable [IsAlgClosed k]

section Family

variable {ι : Type*} [Finite ι] {T : ι → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)]
  [∀ i, Module A (T i)] [∀ i, IsScalarTower k A (T i)] [∀ i, IsSimpleModule A (T i)]
  [∀ i, FiniteDimensional k (T i)]

/-- **Traces separate multiplicities.** Over an algebraically closed field, if the trace
combinations `∑ i, c i • tr(a | T i)` and `∑ i, d i • tr(a | T i)` agree on a spanning set of `A`,
for pairwise non-isomorphic simple `T i`, then `c i` and `d i` agree in `k`. -/
theorem natCast_eq_of_sum_trace_eq [Fintype ι]
    (hT : Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j)) {Γ : Type*} {g : Γ → A}
    (hg : Submodule.span k (Set.range g) = ⊤) (c d : ι → ℕ)
    (h : ∀ γ, ∑ i, c i • LinearMap.trace k (T i) (Algebra.lsmul k k (T i) (g γ)) =
      ∑ i, d i • LinearMap.trace k (T i) (Algebra.lsmul k k (T i) (g γ))) (i : ι) :
    (c i : k) = d i := by
  classical
  let φ (e : ι → ℕ) : A →ₗ[k] k :=
    ∑ j, e j • (LinearMap.trace k (T j)).comp (Algebra.lsmul k k (T j)).toLinearMap
  have hφ : φ c = φ d := LinearMap.ext_on_range hg fun γ => by simpa [φ] using h γ
  -- An element acting on `T i` by a rank-one idempotent and by zero on the other `T j`.
  have : Nontrivial (T i) := IsSimpleModule.nontrivial A (T i)
  let B := Module.finBasis k (T i)
  let j₀ : Fin (finrank k (T i)) := ⟨0, finrank_pos⟩
  obtain ⟨a, ha⟩ := exists_forall_lsmul_eq hT
    (Pi.single i ((B.coord j₀).smulRight (B j₀)) : ∀ j, Module.End k (T j))
  have hφa (e : ι → ℕ) : φ e a = e i := by
    simp only [φ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, ha]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp [B, LinearMap.trace_smulRight]
  rw [← hφa c, ← hφa d, hφ]

end Family

variable {M N : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [IsSemisimpleModule A M] [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N] [FiniteDimensional k N] [IsSemisimpleModule A N]

/-- **Traces determine multiplicities modulo the characteristic.** Over an algebraically closed
field, finite-dimensional semisimple modules on which every element of `A` acts with the same
trace contain every simple module the same number of times, counted in `k`. In characteristic `p`
the multiplicities are thus congruent modulo `p`, and need not be equal: over an algebraic closure
of `𝔽₃`, three copies
of the trivial representation of `ℤ/2` and three copies of its sign representation have the same
trace everywhere, and contain the trivial representation `3` and `0` times. -/
theorem natCast_jordanHolderMultiplicity_eq_of_trace_eq [Module.Finite A M] [Module.Finite A N]
    {Γ : Type*} {g : Γ → A} (hg : Submodule.span k (Set.range g) = ⊤)
    (h : ∀ γ, LinearMap.trace k M (Algebra.lsmul k k M (g γ)) =
      LinearMap.trace k N (Algebra.lsmul k k N (g γ)))
    (S : Type*) [AddCommGroup S] [Module A S] :
    (jordanHolderMultiplicity A M S : k) = jordanHolderMultiplicity A N S := by
  obtain ⟨ι, _, T, hTs, hT, hM, hN⟩ := exists_simple_family (R := A) M N
  have (i : ι) : FiniteDimensional k (T i) :=
    .of_injective ((T i).subtype.restrictScalars k) Subtype.val_injective
  have (i : ι) : IsSimpleModule A (T i) := hTs i
  have hmult := natCast_eq_of_sum_trace_eq hT hg
    (fun i => jordanHolderMultiplicity A M (T i)) (fun i => jordanHolderMultiplicity A N (T i))
    fun γ => by
      rw [← trace_lsmul_eq_sum (k := k) hT hM, ← trace_lsmul_eq_sum (k := k) hT hN]
      exact h γ
  exact apply_jordanHolderMultiplicity_eq_of_forall_eq (Nat.cast : ℕ → k) hM hN hmult S

end Multiplicity

end IsSemisimpleModule
