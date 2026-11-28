/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
import TauCeti.RingTheory.Semisimple.Multiplicity

/-!
# Bounded dimension over a semisimple algebra

`TauCeti.exists_finite_module_family_of_rank_le` gives a finite family containing a representative
of every module of bounded dimension over a fixed semisimple algebra. The representatives satisfy
the same dimension bound and live in the universe of the algebra, independently of the universe
of the module being represented.

This supplies the finite list of rational module types in the Jordan–Zassenhaus argument
(I. Reiner, *Maximal Orders*, §26).
-/

public section

namespace TauCeti

universe u v

open Module

-- Formal sources: `IsSemisimpleModule.exists_simple_family` and
-- `IsSemisimpleModule.exists_linearEquiv_pi_submodule`.
/-- Over a semisimple `k`-algebra `A`, the modules of `k`-dimension at most `d` have finitely
many isomorphism classes. The representatives live in the universe of `A` even when the modules
they represent do not. -/
theorem exists_finite_module_family_of_rank_le (k : Type*) (A : Type u)
    [Field k] [Ring A] [Algebra k A] [IsSemisimpleRing A] (d : ℕ) :
    ∃ (ι : Type u) (_ : Finite ι) (S : ι → ModuleCat.{u} A),
      (∀ i, Module.rank k ((ModuleCat.restrictScalars (algebraMap k A)).obj (S i)) ≤ d) ∧
      ∀ (M : Type v) [AddCommMonoid M] [Module k M] [Module A M] [IsScalarTower k A M],
        Module.rank k M ≤ d → ∃ i, Nonempty (M ≃ₗ[A] S i) := by
  classical
  obtain ⟨ι, _, T, _, _, hT, _⟩ := IsSemisimpleModule.exists_simple_family (R := A) A A
  -- List all products of at most `d` simple representatives, then impose the rank bound.
  let S (x : Σ m : Fin (d + 1), Fin m.val → ι) : ModuleCat.{u} A :=
    ModuleCat.of A (∀ j, T (x.2 j))
  refine ⟨{x // Module.rank k ((ModuleCat.restrictScalars (algebraMap k A)).obj (S x)) ≤ d},
    inferInstance, fun x ↦ S x.val, fun x ↦ x.property, ?_⟩
  intro M _ _ _ _ hM
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup A
  have : Module.Finite k M :=
    rank_lt_aleph0_iff.mp (hM.trans_lt Cardinal.natCast_lt_aleph0)
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite k A M
  obtain ⟨m, Q, hQ, ⟨e⟩⟩ := IsSemisimpleModule.exists_linearEquiv_pi_submodule (R := A) M
  have (j : Fin m) : Module.Finite k (Q j) :=
    Module.Finite.of_injective ((Q j).subtype.restrictScalars k) (Q j).injective_subtype
  have hm : m ≤ d := by
    have hpos (j : Fin m) : 1 ≤ finrank k (Q j) := by
      have : IsSimpleModule A (Q j) := hQ j
      have := IsSimpleModule.nontrivial A (Q j)
      exact Module.finrank_pos
    calc
      m = ∑ _j : Fin m, (1 : ℕ) := by simp
      _ ≤ ∑ j, finrank k (Q j) := Finset.sum_le_sum fun j _ ↦ hpos j
      _ = finrank k M := by rw [← Module.finrank_pi_fintype, (e.restrictScalars k).finrank_eq]
      _ ≤ d := finrank_le_of_rank_le hM
  have hrep (j : Fin m) : ∃ i, Nonempty (Q j ≃ₗ[A] T i) := by
    have : IsSimpleModule A (Q j) := hQ j
    obtain ⟨I, ⟨g⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A (Q j)
    obtain ⟨i, ⟨g'⟩⟩ := hT I (IsSimpleModule.congr g.symm)
    exact ⟨i, ⟨g.trans g'⟩⟩
  choose σ eσ using hrep
  let x : Σ m : Fin (d + 1), Fin m.val → ι := ⟨⟨m, Nat.lt_succ_of_le hm⟩, σ⟩
  let eS : M ≃ₗ[A] S x := e.trans (.piCongrRight fun j ↦ (eσ j).some)
  have hx : Module.rank k ((ModuleCat.restrictScalars (algebraMap k A)).obj (S x)) ≤ d := by
    let eK : M ≃ₗ[k] (ModuleCat.restrictScalars (algebraMap k A)).obj (S x) :=
      { eS.toAddEquiv with
        map_smul' := fun c m ↦ by
          rw [ModuleCat.restrictScalars.smul_def', ← algebraMap_smul A c m]
          exact eS.map_smul (algebraMap k A c) m }
    have hlift : Cardinal.lift.{u} (Module.rank k M) ≤ d := Cardinal.lift_le_nat_iff.mpr hM
    exact Cardinal.lift_le_nat_iff.mp (eK.lift_rank_eq ▸ hlift)
  exact ⟨⟨x, hx⟩, ⟨eS⟩⟩

end TauCeti
