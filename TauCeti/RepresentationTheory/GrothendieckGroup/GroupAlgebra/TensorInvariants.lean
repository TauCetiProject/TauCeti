/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Invariants
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Projection
import TauCeti.RepresentationTheory.Dual

/-!
# Tensor-invariant dimensions of lines and of the regular representation

Let `G` be a finite group and `k` a field in which `#G` is nonzero. This file evaluates the
tensor-invariant dimension `TauCeti.finrankTensorInvariantsK0 A`, `[M] ↦ dimₖ (M ⊗ A)ᴳ`, on the
two kinds of classes that occur in the Grothendieck-group computation of local Galois cohomology:

* for a one-dimensional representation `M`, the line `M^∨ ⊗ M` is trivial
  (`Representation.dualTprodEquivTrivialOfFinrankEqOne`), so `[M^∨] * [M] = 1` in `G₀(k[G])`
  (`TauCeti.fdRepK0RingEquiv_dual_mul_self_eq_one`);
* the regular representation `k[G]` is induced from the trivial subgroup, so by the projection
  formula and Frobenius reciprocity `dimₖ (k[G] ⊗ V)ᴳ = dimₖ V`
  (`TauCeti.finrankInvariantsK0_permK0_self_mul`).

Together they give `TauCeti.finrankTensorInvariantsK0_dual_mul_one_add_add`: for a line `M` and
`c : ℕ`, the class `[M^∨] * (1 + [M] + c [k[G]])` has tensor-invariant dimension
`dim (M^∨ ⊗ A)ᴳ + dim Aᴳ + c dim A`. With `M = μ_ℓ`, this is the final count in the proof of
Tate's local Euler characteristic formula, where `H¹(L, 𝔽_ℓ)` has the class
`[μ_ℓ^∨] * [Lˣ/(Lˣ)^ℓ]` and `[Lˣ/(Lˣ)^ℓ] = 1 + [μ_ℓ] + [ℓ = p] [K : ℚ_p] [k[G]]`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I, proof of Theorem 2.8.
-/

public section

open CategoryTheory MonoidalCategory Module
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G]

/-- **`[M^∨] * [M] = 1` for a line.** In `G₀(k[G])`, the class of the dual of a one-dimensional
representation is inverse to the class of the representation. -/
theorem fdRepK0RingEquiv_dual_mul_self_eq_one (M : FDRep k G) (h : finrank k M = 1) :
    fdRepK0RingEquiv k G (ExactK0.of (FDRep.of (Representation.dual M.ρ))) *
      fdRepK0RingEquiv k G (ExactK0.of M) = 1 := by
  have : FiniteDimensional k M := Module.finite_of_finrank_eq_succ h
  have : Module.Finite k[G] (Representation.trivial k G k).asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  rw [← map_mul, ExactK0.of_mul_of, fdRepK0RingEquiv_of, exactK0_one_eq_of_trivial]
  have : Module.Finite k[G] (Representation.asModule
      (FDRep.of (Representation.dual M.ρ) ⊗ M).ρ) :=
    Module.Finite.of_restrictScalars_finite k k[G] _
  exact ExactK0.of_congr
    (Representation.asModuleLinearEquivOfEquiv
      (Representation.dualTprodEquivTrivialOfFinrankEqOne M.ρ h)).toFGModuleCatIso

variable [NeZero (Nat.card G : k)]

/-- **The regular representation absorbs invariants.** Tensoring with the regular representation
`k[G]` and taking invariants gives back the dimension: `dimₖ (k[G] ⊗ V)ᴳ = dimₖ V`. Indeed `k[G]`
is induced from the trivial subgroup, so by the projection formula `k[G] ⊗ V` is induced from the
restriction of `V` to the trivial subgroup, whose invariants are all of `V`. -/
theorem finrankInvariantsK0_permK0_self_mul (V : FDRep k G) :
    finrankInvariantsK0 (permK0 k G G * fdRepK0RingEquiv k G (ExactK0.of V)) = finrank k V := by
  have : NeZero (Nat.card (⊥ : Subgroup G) : k) := ⟨by simp⟩
  have hperm : permK0 k G G = indK0 k (⊥ : Subgroup G) 1 := by
    rw [exactK0_one_eq_of_trivial, indK0_of_trivial]
    exact permK0_congr k (QuotientGroup.quotientBot (G := G)).symm.toEquiv fun _ _ ↦ rfl
  rw [hperm, ← indK0_mul_resK0, one_mul, finrankInvariantsK0_indK0, resK0_fdRepK0RingEquiv_of,
    fdRepK0RingEquiv_of, finrankInvariantsK0_of]
  have htop : Representation.invariants
      (FDRep.ρ ((Action.res (FGModuleCat k) (⊥ : Subgroup G).subtype).obj V)) = ⊤ := by
    refine eq_top_iff.2 fun v _ g ↦ ?_
    rw [Subsingleton.elim g 1, map_one]
    rfl
  rw [htop, finrank_top]
  -- The carrier of the restricted representation is that of `V`.
  rfl

/-- **The tensor-invariant dimension of `[M^∨] * (1 + [M] + c [k[G]])`** for a line `M`: it is
`dimₖ (M^∨ ⊗ A)ᴳ + dimₖ Aᴳ + c dimₖ A`. The three terms come from `[M^∨] * 1 = [M^∨]`, from
`[M^∨] * [M] = 1` (`TauCeti.fdRepK0RingEquiv_dual_mul_self_eq_one`), and from the regular
representation (`TauCeti.finrankInvariantsK0_permK0_self_mul`). -/
theorem finrankTensorInvariantsK0_dual_mul_one_add_add (M A : FDRep k G) (hM : finrank k M = 1)
    (c : ℕ) :
    finrankTensorInvariantsK0 A
        (fdRepK0RingEquiv k G (ExactK0.of (FDRep.of (Representation.dual M.ρ))) *
          (1 + fdRepK0RingEquiv k G (ExactK0.of M) + c • permK0 k G G)) =
      (finrank k (Representation.invariants (V := TensorProduct k (Module.Dual k M) A)
        ((Representation.dual M.ρ).tprod A.ρ)) : ℤ) +
        finrank k (Representation.invariants A.ρ) + c * finrank k A := by
  have : FiniteDimensional k M := Module.finite_of_finrank_eq_succ hM
  have hdual : finrankTensorInvariantsK0 A
      (fdRepK0RingEquiv k G (ExactK0.of (FDRep.of (Representation.dual M.ρ)))) =
      finrank k (Representation.invariants (V := TensorProduct k (Module.Dual k M) A)
        ((Representation.dual M.ρ).tprod A.ρ)) := by
    rw [fdRepK0RingEquiv_of, finrankTensorInvariantsK0_of]
    -- The representation of a tensor product in `FDRep` is `Representation.tprod`.
    rfl
  have hone : finrankTensorInvariantsK0 A 1 = finrank k (Representation.invariants A.ρ) := by
    rw [finrankTensorInvariantsK0_apply, one_mul, fdRepK0RingEquiv_of, finrankInvariantsK0_of]
  have hreg : finrankTensorInvariantsK0 A
      (fdRepK0RingEquiv k G (ExactK0.of (FDRep.of (Representation.dual M.ρ))) * permK0 k G G) =
      finrank k A := by
    rw [finrankTensorInvariantsK0_apply, mul_comm _ (permK0 k G G), mul_assoc, ← map_mul,
      ExactK0.of_mul_of, finrankInvariantsK0_permK0_self_mul]
    congr 1
    -- The carrier of a tensor product in `FDRep` is the tensor product of the carriers.
    change finrank k (TensorProduct k (Module.Dual k M) A) = finrank k A
    rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq, hM, one_mul]
  rw [mul_add, mul_add, mul_one, fdRepK0RingEquiv_dual_mul_self_eq_one M hM, mul_smul_comm,
    map_add, map_add, map_nsmul, hdual, hone, hreg, nsmul_eq_mul]

end TauCeti
