/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The dimension of a finite product

Over a ring `R` with the strong rank condition (for instance a division ring), let
`M : J → Type*` be a finite family of free `R`-modules, each of which is either a line
(dimension `1`) or zero. Each `M j` is then finite
(`TauCeti.finite_of_finrank_eq_one_or_subsingleton`), so `Π j, M j` is finite
(`TauCeti.finite_pi_of_finrank_eq_one`) and has dimension the number of lines
(`TauCeti.finrank_pi_eq_card_of_finrank_eq_one`). This is the form in which Krull–Schmidt
multiplicities show up as dimensions over residue division rings.

Over a domain `R`, a finite product of nonzero ideals has rank the number of factors
(`Module.rank_pi_ideal`): it sits between `Rⁿ` and a copy of `Rⁿ` scaled into it. Hence so does
any module isomorphic to such a product (`Module.finrank_eq_card_of_linearEquiv_pi`); in particular
a nonzero ideal has rank one (`Ideal.finrank_eq_one_of_ne_bot`).
-/

public section

open Module (finrank)

namespace TauCeti

variable {R : Type*} [Semiring R] [StrongRankCondition R]

/-- A free line or a zero space is a finite module. -/
theorem finite_of_finrank_eq_one_or_subsingleton {N : Type*} [AddCommMonoid N] [Module R N]
    [Module.Free R N] (h : finrank R N = 1 ∨ Subsingleton N) : Module.Finite R N :=
  h.elim Module.finite_of_finrank_eq_succ fun _ => inferInstance

variable {J : Type*} [Finite J]
  (M : J → Type*) [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)] [∀ j, Module.Free R (M j)]
  (p : J → Prop)

/-- **A finite product of lines and zero spaces** is a finite module. -/
theorem finite_pi_of_finrank_eq_one (h₁ : ∀ j, p j → finrank R (M j) = 1)
    (h₀ : ∀ j, ¬p j → Subsingleton (M j)) : Module.Finite R (Π j, M j) :=
  have (j : J) := finite_of_finrank_eq_one_or_subsingleton ((em (p j)).imp (h₁ j) (h₀ j))
  inferInstance

/-- **A finite product of lines and zero spaces** has dimension the number of lines. -/
theorem finrank_pi_eq_card_of_finrank_eq_one (h₁ : ∀ j, p j → finrank R (M j) = 1)
    (h₀ : ∀ j, ¬p j → Subsingleton (M j)) :
    finrank R (Π j, M j) = Nat.card {j // p j} := by
  classical
  have := Fintype.ofFinite J
  have (j : J) := finite_of_finrank_eq_one_or_subsingleton ((em (p j)).imp (h₁ j) (h₀ j))
  have hdim (j : J) : finrank R (M j) = if p j then 1 else 0 := by
    split_ifs with h
    · exact h₁ j h
    · have := h₀ j h
      exact Module.finrank_zero_of_subsingleton
  rw [Module.finrank_pi_fintype]
  simp [hdim, Nat.card_eq_fintype_card, Fintype.card_subtype]

end TauCeti

section Rank

variable {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι]

/-- A finite product of nonzero ideals of a domain has rank equal to the number of factors. -/
theorem Module.rank_pi_ideal {J : ι → Ideal R} (hJ : ∀ i, J i ≠ ⊥) :
    Module.rank R ((i : ι) → J i) = Fintype.card ι := by
  choose a ha ha0 using fun i ↦ Submodule.exists_mem_ne_zero_of_ne_bot (hJ i)
  -- the inclusion into `Rⁿ`, and the scaling `v ↦ (vᵢ aᵢ)ᵢ` from `Rⁿ`
  let incl : ((i : ι) → J i) →ₗ[R] ι → R := LinearMap.pi fun i ↦ (J i).subtype ∘ₗ .proj i
  let scale : (ι → R) →ₗ[R] (i : ι) → J i :=
    LinearMap.pi fun i ↦ LinearMap.toSpanSingleton R (J i) ⟨a i, ha i⟩ ∘ₗ .proj i
  have hincl : Function.Injective incl := fun v w h ↦ funext fun i ↦
    Subtype.ext (congrFun h i)
  have hscale : Function.Injective scale := by
    refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ funext fun i ↦ ?_
    have := congrArg Subtype.val (congrFun hv i)
    simp [scale] at this
    exact this.resolve_right (ha0 i)
  apply le_antisymm
  · simpa [rank_fun'] using incl.lift_rank_le_of_injective hincl
  · simpa [rank_fun'] using scale.lift_rank_le_of_injective hscale

/-- A module isomorphic to a finite product of nonzero ideals of a domain has rank the number of
factors. -/
theorem Module.finrank_eq_card_of_linearEquiv_pi {M : Type*} [AddCommGroup M] [Module R M]
    {J : ι → Ideal R} (hJ : ∀ i, J i ≠ ⊥) (e : M ≃ₗ[R] (i : ι) → J i) :
    Module.finrank R M = Fintype.card ι := by
  rw [e.finrank_eq]
  exact Module.finrank_eq_of_rank_eq (Module.rank_pi_ideal hJ)

/-- A nonzero ideal of a domain has rank one. -/
theorem Ideal.finrank_eq_one_of_ne_bot {I : Ideal R} (hI : I ≠ ⊥) : Module.finrank R I = 1 :=
  Module.finrank_eq_card_of_linearEquiv_pi (J := fun _ : Unit ↦ I) (fun _ ↦ hI)
    (LinearEquiv.piUnique R fun _ : Unit ↦ I).symm

end Rank
