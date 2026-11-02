/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.DirectSum
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Basic
-- Non-public: these supply the inputs of the proofs, never the vocabulary of a statement.
import TauCeti.Algebra.Lie.DirectSum
import TauCeti.Algebra.Lie.Weights.Faithful

/-!
# The full-weight module of the pinned rational Lie algebra

For a valid Dynkin type `t`, the **full-weight module** `V_sc(t)` of the pinned Lie algebra
`TauCeti.DynkinType.lieAlgebra t ht` is the direct sum `⨁ᵢ L(ϖᵢ)` of its fundamental modules over
`ℚ`. It is the representation from which the simply connected Chevalley group of type `t` is
built: its weights generate the whole weight lattice, so the torus of the associated group has
the full weight lattice as character lattice.

This file proves the two properties of `V_sc(t)` that make it suitable for this:

* every fundamental weight `ϖᵢ` is a weight of `V_sc(t)`, carried by the highest weight vector
  `v⁺ᵢ` of the `i`-th summand, so the weights of `V_sc(t)` span the integral weight lattice over
  `ℤ` (Steinberg, Chapter 3, the remark after Lemma 27);
* the representation of the pinned Lie algebra on `V_sc(t)` is faithful. An element `x` of the
  Cartan subalgebra acting by zero has `ϖᵢ(x) = 0` for every `i`, so `x = 0`, and faithfulness on
  the Cartan subalgebra implies faithfulness
  (`TauCeti.isFaithful_of_isFaithful_cartanSubalgebra`).

## Main declarations

* `TauCeti.DynkinType.scModule`: the full-weight module `⨁ᵢ L(ϖᵢ)`.
* `TauCeti.DynkinType.isHighestWeightVector_lof_fundamentalModuleGenerator`: `v⁺ᵢ`, placed in the
  `i`-th summand, is a highest weight vector of weight `ϖᵢ` of `V_sc(t)`.
* `TauCeti.DynkinType.genWeightSpace_scModule_fundamentalWeight_ne_bot`: each `ϖᵢ` is a weight of
  `V_sc(t)`.
* `TauCeti.DynkinType.span_weight_scModule_eq_integralWeightLattice`: the weights of `V_sc(t)`
  span the integral weight lattice over `ℤ`.
* `TauCeti.DynkinType.instIsFaithfulScModule`: the pinned Lie algebra acts faithfully on
  `V_sc(t)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, the remark after Lemma 27.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieModule Module DirectSum

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **The full-weight module** `V_sc(t) = ⨁ᵢ L(ϖᵢ)` of the pinned Lie algebra over `ℚ`, the direct
sum of its fundamental modules. It is an abbreviation, so the Lie-module structure of a direct sum
and the finite-dimensionality of its summands apply to it directly. -/
abbrev scModule : Type :=
  ⨁ i, t.fundamentalModule ht i

/-- The highest weight vector `v⁺ᵢ` of `L(ϖᵢ)`, placed in the `i`-th summand of `V_sc(t)`, is a
highest weight vector of weight `ϖᵢ`. -/
theorem isHighestWeightVector_lof_fundamentalModuleGenerator (i : Fin t.rank) :
    IsHighestWeightVector (t.lieBasis ht).base (t.fundamentalWeight ht i)
      (lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i) :
        t.scModule ht) := by
  have hv := (t.isHighestWeightVector_fundamentalModuleGenerator ht i).map
    (lieModuleOf ℚ (Fin t.rank) (t.lieAlgebra ht) (t.fundamentalModule ht) i)
    fun h ↦ t.fundamentalModuleGenerator_ne_zero ht i (by simpa using congr($h i))
  rwa [lieModuleOf_apply, ← lof_eq_of ℚ] at hv

/-- **Each fundamental weight is a weight of `V_sc(t)`.** -/
theorem genWeightSpace_scModule_fundamentalWeight_ne_bot (i : Fin t.rank) :
    genWeightSpace (t.scModule ht) (t.fundamentalWeight ht i : t.cartanSubalgebra ht → ℚ) ≠ ⊥ :=
  (t.isHighestWeightVector_lof_fundamentalModuleGenerator ht i).genWeightSpace_ne_bot

/-- **The weights of `V_sc(t)` span the weight lattice.** Over `ℤ`, the weights of the full-weight
module span the lattice of all integral weights of the pinned Lie algebra: every weight of a
finite-dimensional module is integral, and the fundamental weights, which span the integral
weights, are weights of `V_sc(t)`. -/
theorem span_weight_scModule_eq_integralWeightLattice :
    Submodule.span ℤ
        (Set.range fun χ : Weight ℚ (t.cartanSubalgebra ht) (t.scModule ht) ↦ χ.toLinear) =
      integralWeightLattice (t.cartanSubalgebra ht) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨χ, rfl⟩
    exact mem_integralWeightLattice_iff.mpr (isIntegralWeight_of_weight (L := t.lieAlgebra ht) χ)
  refine (t.span_fundamentalWeight_eq_integralWeightLattice ht).ge.trans (Submodule.span_mono ?_)
  rintro _ ⟨i, rfl⟩
  have hv := t.isHighestWeightVector_lof_fundamentalModuleGenerator ht i
  exact ⟨hv.weight, LinearMap.coe_injective hv.coe_weight⟩

/-- **The full-weight module is faithful**: only the zero element of the pinned Lie algebra acts
by zero on `V_sc(t)`. -/
instance instIsFaithfulScModule : IsFaithful ℚ (t.lieAlgebra ht) (t.scModule ht) := by
  have : IsFaithful ℚ (t.cartanSubalgebra ht) (t.scModule ht) := by
    rw [isFaithful_iff_ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LieSubmodule.mem_bot]
    -- `x` acts on `v⁺ᵢ` by the scalar `ϖᵢ(x)`, which therefore vanishes.
    have hϖ (i : Fin t.rank) : t.fundamentalWeight ht i x = 0 := by
      have hv := t.isHighestWeightVector_lof_fundamentalModuleGenerator ht i
      have h := (LieModule.mem_ker _ _ _ x).mp hx (lof ℚ _ _ i (t.fundamentalModuleGenerator ht i))
      rw [LieSubalgebra.coe_bracket_of_module, hv.lie_eq_smul] at h
      exact (smul_eq_zero_iff_left hv.ne_zero).mp h
    refine (Module.forall_dual_apply_eq_zero_iff ℚ x).mp fun f ↦ ?_
    rw [← (t.fundamentalWeight ht).sum_repr f]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hϖ, smul_zero, Finset.sum_const_zero]
  exact isFaithful_of_isFaithful_cartanSubalgebra (H := t.cartanSubalgebra ht)

end

end TauCeti.DynkinType
