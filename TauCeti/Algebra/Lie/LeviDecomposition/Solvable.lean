/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import TauCeti.Algebra.Lie.LeviDecomposition.Abelian
public import TauCeti.Algebra.Lie.SemiDirect.Basic

/-!
# Levi's theorem

Let `L` be a finite-dimensional Lie algebra over a field of characteristic zero. **Levi's
theorem** says that the solvable radical `R` of `L` has a complementary Lie subalgebra `S`, a
*Levi complement*. Such an `S` is isomorphic to `L ⧸ R`, so it is semisimple, and `L` is the
semidirect sum `R ⋊ S` for the adjoint action of `S` on `R`.

The theorem is proved more generally for a solvable ideal `I` whose quotient `L ⧸ I` has
nondegenerate Killing form (`LieIdeal.exists_lieSubalgebra_isCompl_of_isSolvable`); the radical is
such an ideal by Cartan's criterion. The general form is the one that admits an induction.

## The argument

Induct on the dimension of `L`. Let `A` be the last nonzero term of the derived series of `I`: an
abelian ideal of `L` contained in `I`. If `I = 0` there is nothing to prove. Otherwise `A ≠ 0`, so
`L ⧸ A` has smaller dimension, and its solvable ideal `I ⧸ A` has quotient `L ⧸ I`; by induction it
has a complement `S₁`. The preimage `P` of `S₁` in `L` is a Lie subalgebra with `I + P = L` and
`I ∩ P = A`. The abelian ideal `A` of `P` has quotient `P ⧸ A ≃ L ⧸ I`, so the abelian case
(`LieIdeal.exists_lieSubalgebra_isCompl_of_isLieAbelian`) complements it inside `P`, and that
complement is a complement of `I` in `L` (`LieIdeal.isCompl_map_incl`).

## Main results

* `LieIdeal.exists_lieSubalgebra_isCompl_of_isSolvable`: a solvable ideal with Killing quotient has
  a complementary Lie subalgebra.
* `TauCeti.exists_leviComplement`: **Levi's theorem**, the radical has a complementary Lie
  subalgebra.
* `TauCeti.exists_leviDecomposition`: **the Levi decomposition**, `L ≃ R ⋊ S` with `S` semisimple.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129, Appendix E,
  for the proof of Levi's theorem by induction on the dimension.
* N. Jacobson, *Lie Algebras*, Chapter III, §9.
-/

public section

namespace TauCeti

open LieAlgebra Module

universe u v

variable {K : Type u} [Field K]

/-- **The inductive step.** Let `A ≤ I` be ideals of `L` with `A` abelian and `L ⧸ I` Killing. A
complement of `I ⧸ A` in `L ⧸ A` lifts to a complement of `I` in `L`: its preimage `P` satisfies
`I + P = L` and `I ∩ P = A`, and the abelian case complements `A` inside `P`. -/
private theorem exists_lieSubalgebra_isCompl_of_isCompl_map_mkQ [CharZero K] {L : Type v}
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] {I A : LieIdeal K L} [IsLieAbelian A]
    [IsKilling K (L ⧸ I)] (hAI : A ≤ I) {S₁ : LieSubalgebra K (L ⧸ A)}
    (hS₁ : IsCompl (I.map A.mkQ).toSubmodule S₁.toSubmodule) :
    ∃ S : LieSubalgebra K L, IsCompl I.toSubmodule S.toSubmodule := by
  let P := S₁.comap A.mkQ
  have hIP : Codisjoint I.toSubmodule P.toSubmodule := by
    refine codisjoint_iff.2 (Submodule.eq_top_iff'.2 fun x ↦ ?_)
    obtain ⟨k, hk, s₁, hs₁, hks⟩ :=
      Submodule.mem_sup.1 (hS₁.codisjoint.eq_top ▸ Submodule.mem_top (x := A.mkQ x))
    obtain ⟨⟨i, hi⟩, rfl⟩ := LieIdeal.mem_map_of_surjective A.mkQ_surjective hk
    obtain ⟨s, rfl⟩ := A.mkQ_surjective s₁
    have hxs : x - s - i ∈ A := by
      rw [← LieIdeal.ker_mkQ A, LieHom.mem_ker, map_sub, map_sub, ← hks]
      abel
    refine Submodule.mem_sup.2 ⟨x - s, ?_, s, hs₁, sub_add_cancel x s⟩
    rw [← sub_add_cancel (x - s) i]
    exact I.add_mem (hAI hxs) hi
  have hPI {x : L} (hxP : x ∈ P) (hxI : x ∈ I) : x ∈ A := by
    rw [← LieIdeal.ker_mkQ A, LieHom.mem_ker]
    exact Submodule.disjoint_def.1 hS₁.disjoint _ (LieIdeal.mem_map hxI) hxP
  -- The ideal `I ∩ P = A` of `P` is abelian with quotient `L ⧸ I`: apply the abelian case.
  have : IsLieAbelian (I.comap P.incl) := by
    rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot, LieSubmodule.lie_eq_bot_iff]
    intro x hx y hy
    ext
    rw [LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero]
    have h := (LieSubmodule.lie_abelian_iff_lie_self_eq_bot A).1 ‹_›
    rw [← LieSubmodule.mem_bot (R := K) (L := L), ← h]
    exact LieSubmodule.lie_mem_lie (hPI x.2 (LieIdeal.mem_comap.1 hx))
      (hPI y.2 (LieIdeal.mem_comap.1 hy))
  have := I.isKilling_quotient_comap_incl hIP
  obtain ⟨T, hT⟩ := (I.comap P.incl).exists_lieSubalgebra_isCompl_of_isLieAbelian
  exact ⟨T.map P.incl, I.isCompl_map_incl hIP hT⟩

/-- The induction behind `LieIdeal.exists_lieSubalgebra_isCompl_of_isSolvable`, on the dimension
of the ambient Lie algebra. -/
private theorem exists_lieSubalgebra_isCompl_of_isSolvable_of_finrank_eq [CharZero K] (n : ℕ) :
    ∀ (L : Type v) [LieRing L] [LieAlgebra K L] [FiniteDimensional K L], finrank K L = n →
      ∀ (I : LieIdeal K L) [IsSolvable I] [IsKilling K (L ⧸ I)],
        ∃ S : LieSubalgebra K L, IsCompl I.toSubmodule S.toSubmodule := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L _ _ _ hn I _ _
  -- `A` is the last nonzero term of the derived series of `I`, an abelian ideal inside `I`.
  set A := derivedAbelianOfIdeal I
  have : IsLieAbelian A := abelian_derivedAbelianOfIdeal I
  rcases eq_or_ne A ⊥ with hA | hA
  · rw [abelian_of_solvable_ideal_eq_bot_iff] at hA
    subst hA
    refine ⟨⊤, ?_⟩
    rw [LieSubmodule.bot_toSubmodule, LieSubalgebra.top_toSubmodule]
    exact isCompl_bot_top
  have hAI : A ≤ I := derivedAbelianOfIdeal_le I
  -- The quotient `L ⧸ A` is smaller, and its ideal `I ⧸ A` is solvable with quotient `L ⧸ I`.
  have : IsSolvable (I.map A.mkQ) := LieIdeal.isSolvable_map A.mkQ I A.mkQ_surjective
  have : IsKilling K ((L ⧸ A) ⧸ I.map A.mkQ) := by
    have hAI' : A ≤ I.mkQ.ker := by rwa [LieIdeal.ker_mkQ]
    rw [← I.ker_liftQ_mkQ hAI']
    exact isKilling_of_equiv
      ((A.liftQ I.mkQ hAI').quotKerEquivOfSurjective (A.liftQ_surjective _ _ I.mkQ_surjective)).symm
  have hlt : finrank K (L ⧸ A) < n := by
    have h := Submodule.finrank_quotient_add_finrank A.toSubmodule
    have hpos : 0 < finrank K A.toSubmodule := Nat.pos_of_ne_zero fun h0 ↦
      hA ((LieSubmodule.toSubmodule_eq_bot A).1 (Submodule.finrank_eq_zero.1 h0))
    rw [← hn]
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos) h.le
  obtain ⟨S₁, hS₁⟩ := ih _ hlt (L ⧸ A) rfl (I.map A.mkQ)
  exact exists_lieSubalgebra_isCompl_of_isCompl_map_mkQ hAI hS₁

variable {L : Type v} [LieRing L] [LieAlgebra K L]

/-- **A Levi complement of a solvable ideal.** Over a field of characteristic zero, a solvable
ideal `I` of a finite-dimensional Lie algebra `L` whose quotient `L ⧸ I` has nondegenerate Killing
form has a complementary Lie subalgebra. -/
theorem _root_.LieIdeal.exists_lieSubalgebra_isCompl_of_isSolvable [CharZero K]
    [FiniteDimensional K L] (I : LieIdeal K L) [IsSolvable I] [IsKilling K (L ⧸ I)] :
    ∃ S : LieSubalgebra K L, IsCompl I.toSubmodule S.toSubmodule :=
  exists_lieSubalgebra_isCompl_of_isSolvable_of_finrank_eq _ L rfl I

variable (K L)

/-- **Levi's theorem.** Over a field of characteristic zero, the solvable radical of a
finite-dimensional Lie algebra has a complementary Lie subalgebra, a Levi complement. -/
theorem exists_leviComplement [CharZero K] [FiniteDimensional K L] :
    ∃ S : LieSubalgebra K L, IsCompl (radical K L).toSubmodule S.toSubmodule :=
  (radical K L).exists_lieSubalgebra_isCompl_of_isSolvable

/-- **The Levi decomposition.** Over a field of characteristic zero, a finite-dimensional Lie
algebra is the semidirect sum of its solvable radical and a semisimple Lie subalgebra acting on
the radical by the adjoint action. -/
theorem exists_leviDecomposition [CharZero K] [FiniteDimensional K L] :
    ∃ (S : LieSubalgebra K L) (ψ : S →ₗ⁅K⁆ LieDerivation K (radical K L) (radical K L)),
      IsSemisimple K S ∧ Nonempty (L ≃ₗ⁅K⁆ radical K L ⋊⁅ψ⁆ S) := by
  obtain ⟨S, hS⟩ := exists_leviComplement K L
  -- `S` is isomorphic to `L ⧸ radical K L`, which is Killing by Cartan's criterion.
  have : IsKilling K S := isKilling_of_equiv ((radical K L).quotientEquivOfIsCompl S hS)
  exact ⟨S, _, inferInstance, (radical K L).nonempty_lieEquiv_semiDirectSum S hS⟩

end TauCeti
