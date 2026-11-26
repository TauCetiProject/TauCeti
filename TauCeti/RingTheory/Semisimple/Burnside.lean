/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.DoubleCentralizer
public import TauCeti.RingTheory.Semisimple.Schur
public import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# Burnside's theorem for several simple modules

Over an algebraically closed field `k`, Burnside's theorem says that a `k`-algebra `A` maps onto
`End_k(T)` for a finite-dimensional simple module `T`. This file extends it to finitely many
pairwise non-isomorphic finite-dimensional simple modules `T_j`: `A` maps onto `∏ j, End_k(T_j)`.
Each factor is Burnside's theorem
(`Algebra.lsmul_surjective_of_forall_end_eq_smul`), and the isotypic projections of `∏ j, T_j`,
which are actions of elements of `A` (`IsSemisimpleModule.exists_forall_smul_eq_ite`), separate
the factors.

## Main results

* `IsSemisimpleModule.exists_forall_lsmul_eq`: for a finite family of pairwise non-isomorphic
  finite-dimensional simple modules `T_j` over an algebraically closed field,
  `A → ∏ j, End_k(T_j)` is surjective.
-/

public section

open Module TauCeti

namespace IsSemisimpleModule

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [IsAlgClosed k]

section Family

variable {ι : Type*} [Finite ι] {T : ι → Type*} [∀ i, AddCommGroup (T i)] [∀ i, Module k (T i)]
  [∀ i, Module A (T i)] [∀ i, IsScalarTower k A (T i)] [∀ i, IsSimpleModule A (T i)]
  [∀ i, FiniteDimensional k (T i)]

/-- **Burnside's theorem for several simple modules.** Over an algebraically closed field, an
algebra maps onto `∏ j, End_k(T_j)` for finitely many pairwise non-isomorphic finite-dimensional
simple modules `T_j`: any family of `k`-linear endomorphisms is the action of one element. -/
theorem exists_forall_lsmul_eq (hT : Pairwise fun i j => IsEmpty (T i ≃ₗ[A] T j))
    (f : ∀ i, Module.End k (T i)) : ∃ a : A, ∀ i, Algebra.lsmul k k (T i) a = f i := by
  classical
  -- Each `T_j` alone is Burnside's theorem; the isotypic projections of `∏ j, T_j` separate the
  -- factors.
  cases nonempty_fintype ι
  have : Module.Finite (Module.End A (∀ i, T i)) (∀ i, T i) :=
    Module.Finite.of_restrictScalars_finite k _ _
  choose b hb using fun i => Algebra.lsmul_surjective_of_forall_end_eq_smul (K := k)
    (fun g : Module.End A (T i) => ⟨endAlgEquivSelfOfIsSimpleModule (k := k) g,
      fun m => (endAlgEquivSelfOfIsSimpleModule_smul g m).symm⟩) (f i)
  choose e he using fun i => exists_forall_smul_eq_ite (R := A) (M := ∀ i, T i) (T i)
  have hδ (i j : ι) (y : T j) : e i • y = if i = j then y else 0 := by
    rw [smul_eq_ite_of_injective (he i) (LinearMap.single A T j) (Pi.single_injective j)]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left ⟨LinearEquiv.refl A _⟩, ite_eq_left rfl]
    · rw [ite_eq_right fun ⟨e⟩ => (hT hij).false e, ite_eq_right hij]
  refine ⟨∑ i, e i * b i, fun j => LinearMap.ext fun x => ?_⟩
  simpa [Finset.sum_smul, mul_smul, hδ] using LinearMap.congr_fun (hb j) x

end Family

end IsSemisimpleModule
