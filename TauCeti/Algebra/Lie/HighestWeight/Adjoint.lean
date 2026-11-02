/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.HighestWeight.Weyl.Dimension
public import TauCeti.Algebra.Lie.Weights.IsSimple
public import TauCeti.LinearAlgebra.RootSystem.HighestRoot
import TauCeti.Algebra.Lie.HighestWeight.Irreducible
import TauCeti.Algebra.Lie.Weights.Dimension

/-!
# The adjoint module as a highest weight module

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero and `H` a splitting Cartan subalgebra. The adjoint module `L` is the basic
example of the highest weight theory: this file reads off its weights and its place in the
classification of the irreducible modules.

Restricted to `H`, the module `L` is the root space decomposition, so its weights are `0`, with
multiplicity `dim H`, and the roots, each with multiplicity one. For a base `b`, adding a positive
root to the highest root `θ` of `b` raises the height, so a nonzero vector of the root space of `θ`
is a highest weight vector of weight `θ`. When `L` is simple the adjoint module is irreducible,
hence these are all of its highest weight vectors and it is the module `L(θ)`, and over an
algebraically closed field the Weyl dimension formula at `θ` computes `dim L`.

## Main results

* `TauCeti.formalCharacter_adjoint`: the formal character of `L` is
  `dim H • e^0 + ∑_α e^α`, the sum running over the roots; the coefficients are
  `TauCeti.formalCharacter_coeff_adjoint_zero`, `TauCeti.formalCharacter_coeff_adjoint_root` and
  `TauCeti.formalCharacter_coeff_adjoint_of_ne_of_notMem`.
* `TauCeti.isHighestWeightVector_of_mem_rootSpace_highestRoot`: a nonzero vector of the root space
  of `θ` is a highest weight vector of weight `θ`.
* `TauCeti.isHighestWeightVector_adjoint_iff`: for simple `L` these are all the highest weight
  vectors of the adjoint module.
* `TauCeti.nonempty_lieModuleEquiv_irreducibleQuotient_highestRoot`: for simple `L`, the adjoint
  module is `L(θ)`.
* `TauCeti.finrank_eq_prod_coweightPairing_highestRoot`: the Weyl dimension formula at `θ`,
  `dim L = ∏_{α>0} ⟨θ + ρ, α^∨⟩ / ⟨ρ, α^∨⟩`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §8, §10.4,
  §21 and §24.3.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §14.2.
-/

public section

open LieAlgebra LieModule Module

namespace TauCeti

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

section Character

/-- The weight `0` of the adjoint module has multiplicity `dim H`. -/
theorem formalCharacter_coeff_adjoint_zero :
    (formalCharacter K H L).coeff 0 = (finrank K H : ℤ) := by
  rw [formalCharacter_coeff]
  exact_mod_cast finrank_rootSpace_zero_eq_finrank_cartan H

variable [IsKilling K L] [IsTriangularizable K H L]

/-- Every root is a weight of the adjoint module of multiplicity one. -/
theorem formalCharacter_coeff_adjoint_root (i : H.root) :
    (formalCharacter K H L).coeff ((IsKilling.rootSystem H).root i) = 1 := by
  rw [formalCharacter_coeff]
  exact_mod_cast IsKilling.finrank_rootSpace_eq_one (i : Weight K H L) (H.isNonZero_coe_root i)

/-- A linear form that is neither zero nor a root is not a weight of the adjoint module. -/
theorem formalCharacter_coeff_adjoint_of_ne_of_notMem {χ : Dual K H} (h0 : χ ≠ 0)
    (hχ : χ ∉ Set.range (IsKilling.rootSystem H).root) :
    (formalCharacter K H L).coeff χ = 0 := by
  rw [formalCharacter_coeff_eq_zero_iff]
  by_contra hne
  obtain ⟨w, rfl⟩ := exists_weight_coe_eq K H L hne
  have hw : w.IsNonZero := fun hw ↦ h0 (by ext x; simpa using congrFun hw x)
  exact hχ ⟨⟨w, by simpa using hw⟩, IsKilling.rootSystem_root_apply H _⟩

/-- **The formal character of the adjoint module**: the weight `0` occurs with multiplicity
`dim H` and every root with multiplicity one. -/
theorem formalCharacter_adjoint :
    formalCharacter K H L =
      AddMonoidAlgebra.single 0 (finrank K H : ℤ) +
        ∑ i : H.root, AddMonoidAlgebra.single ((IsKilling.rootSystem H).root i) 1 := by
  classical
  refine AddMonoidAlgebra.ext (Finsupp.ext fun χ ↦ ?_)
  have hsum : (∑ i : H.root, AddMonoidAlgebra.single ((IsKilling.rootSystem H).root i)
      (1 : ℤ)).coeff χ = ∑ i : H.root, if (IsKilling.rootSystem H).root i = χ then 1 else 0 := by
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hsum, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  by_cases h0 : χ = 0
  · subst h0
    have hne : ∀ i, ¬(IsKilling.rootSystem H).root i = 0 :=
      fun i ↦ (IsKilling.rootSystem H).ne_zero i
    simp only [formalCharacter_coeff_adjoint_zero, ↓reduceIte, hne, Finset.sum_const_zero, add_zero]
  have h0' : ¬0 = χ := Ne.symm h0
  by_cases hχ : χ ∈ Set.range (IsKilling.rootSystem H).root
  · obtain ⟨i, rfl⟩ := hχ
    have hinj : ∀ j, (IsKilling.rootSystem H).root j = (IsKilling.rootSystem H).root i ↔ j = i :=
      fun _ ↦ (IsKilling.rootSystem H).root.injective.eq_iff
    simp only [formalCharacter_coeff_adjoint_root, h0', ↓reduceIte, hinj, Finset.sum_ite_eq',
      Finset.mem_univ, zero_add]
  · have hne : ∀ i, ¬(IsKilling.rootSystem H).root i = χ := fun i hi ↦ hχ ⟨i, hi⟩
    simp only [formalCharacter_coeff_adjoint_of_ne_of_notMem h0 hχ, h0', ↓reduceIte, hne,
      Finset.sum_const_zero, add_zero]

end Character

section HighestRoot

variable [IsKilling K L] [IsTriangularizable K H L]
  [Nonempty H.root] (b : (IsKilling.rootSystem H).Base)

/-- **A nonzero vector of the root space of the highest root is a highest weight vector** of the
adjoint module, of weight the highest root: adding a positive root to the highest root would raise
its height, so the positive root spaces annihilate that root space. -/
theorem isHighestWeightVector_of_mem_rootSpace_highestRoot {e : L}
    (he : e ∈ rootSpace H ((IsKilling.rootSystem H).root b.highestRoot : H → K)) (he0 : e ≠ 0) :
    IsHighestWeightVector b ((IsKilling.rootSystem H).root b.highestRoot) e := by
  refine isHighestWeightVector_of_forall_rootSpace he0
    (fun x ↦ IsKilling.lie_eq_smul_of_mem_rootSpace he x) fun i hi x hx ↦ ?_
  -- The coercion to a function of a sum of linear forms is definitionally the pointwise sum, the
  -- form in which `lie_mem_genWeightSpace_of_mem_genWeightSpace` states the weight of a bracket.
  have hsum : genWeightSpace L (((IsKilling.rootSystem H).root i +
      (IsKilling.rootSystem H).root b.highestRoot : Dual K H) : H → K) = ⊥ := by
    by_contra hne
    obtain ⟨w, hw⟩ := exists_weight_coe_eq K H L hne
    have hne0 : (IsKilling.rootSystem H).root i +
        (IsKilling.rootSystem H).root b.highestRoot ≠ 0 :=
      root_add_ne_zero_of_mem_posRoots_of_mem_posRootCone _ b hi
        (root_mem_posRootCone_of_mem_posRoots _ b ((mem_posRoots _ b _).mpr b.isPos_highestRoot))
    have hw0 : w.IsNonZero := fun hw0 ↦ hne0 (hw ▸ by ext x; simpa using congrFun hw0 x)
    have hroot : (IsKilling.rootSystem H).root ⟨w, by simpa using hw0⟩ =
        (IsKilling.rootSystem H).root i + (IsKilling.rootSystem H).root b.highestRoot :=
      (IsKilling.rootSystem_root_apply H _).trans hw
    have hle := b.height_le_height_highestRoot ⟨w, by simpa using hw0⟩
    rw [b.height_add hroot] at hle
    have hpos := b.isPos_iff.mp ((mem_posRoots _ b _).mp hi)
    omega
  have hmem : ⁅x, e⁆ ∈ genWeightSpace L (((IsKilling.rootSystem H).root i +
      (IsKilling.rootSystem H).root b.highestRoot : Dual K H) : H → K) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx he
  rw [hsum] at hmem
  simpa using hmem

/-- The adjoint module has a highest weight vector of weight the highest root. -/
theorem exists_isHighestWeightVector_highestRoot :
    ∃ e : L, IsHighestWeightVector b ((IsKilling.rootSystem H).root b.highestRoot) e := by
  obtain ⟨e, he, he0⟩ := ((b.highestRoot : H.root) : Weight K H L).exists_ne_zero
  exact ⟨e, isHighestWeightVector_of_mem_rootSpace_highestRoot b he he0⟩

end HighestRoot

section Simple

variable [IsSimple K L] [IsTriangularizable K H L] (b : (IsKilling.rootSystem H).Base)

variable {b} in
/-- **The highest weight vectors of the adjoint module of a simple Lie algebra** are exactly the
nonzero vectors of the root space of the highest root. In particular the highest weight of the
adjoint module is the highest root. -/
theorem isHighestWeightVector_adjoint_iff {lam : Dual K H} {e : L} :
    IsHighestWeightVector b lam e ↔
      lam = (IsKilling.rootSystem H).root b.highestRoot ∧
        e ∈ rootSpace H ((IsKilling.rootSystem H).root b.highestRoot : H → K) ∧ e ≠ 0 := by
  constructor
  · intro hv
    obtain ⟨e₀, he₀⟩ := exists_isHighestWeightVector_highestRoot b
    obtain rfl := hv.unique_of_isIrreducible he₀
    exact ⟨rfl, hv.mem_genWeightSpace, hv.ne_zero⟩
  · rintro ⟨rfl, he, he0⟩
    exact isHighestWeightVector_of_mem_rootSpace_highestRoot b he he0

/-- **The adjoint module of a simple Lie algebra is `L(θ)`**, the irreducible module whose highest
weight is the highest root `θ`. -/
theorem nonempty_lieModuleEquiv_irreducibleQuotient_highestRoot :
    Nonempty (L ≃ₗ⁅K,L⁆ irreducibleQuotient b ((IsKilling.rootSystem H).root b.highestRoot)) := by
  obtain ⟨e, he⟩ := exists_isHighestWeightVector_highestRoot b
  have := isIrreducible_irreducibleQuotient b ((IsKilling.rootSystem H).root b.highestRoot)
  exact nonempty_lieModuleEquiv_of_isHighestWeightVector he
    (isHighestWeightVector_irreducibleQuotientGenerator b _)

variable [IsAlgClosed K]

/-- **The Weyl dimension formula at the highest root**: for simple `L`, the dimension of `L` is
`∏_{α>0} ⟨θ + ρ, α^∨⟩ / ⟨ρ, α^∨⟩`. -/
theorem finrank_eq_prod_coweightPairing_highestRoot :
    (finrank K L : ℚ) = ∏ i ∈ posRootsFinset (IsKilling.rootSystem H) b,
      (coweightPairing ((IsKilling.rootSystem H).root b.highestRoot +
          weylVector (IsKilling.rootSystem H) b) i : ℚ) /
        (coweightPairing (weylVector (IsKilling.rootSystem H) b) i : ℚ) := by
  obtain ⟨e, he⟩ := exists_isHighestWeightVector_highestRoot b
  exact finrank_eq_prod_coweightPairing_div he (lieSpan_singleton_eq_top_of_ne_zero he.ne_zero)

end Simple

end TauCeti
