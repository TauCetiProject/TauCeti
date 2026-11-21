/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Module
public import Mathlib.Algebra.Lie.BaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Absolute irreducibility from a full enveloping-algebra image

If the enveloping algebra of a nonzero Lie module acts as every linear operator, that module
remains irreducible after any field extension. A nonzero submodule after scalar extension is
invariant under the extended enveloping operators. Applying the extension of a suitable linear
operator to a nonzero vector yields every `1 ⊗ m`, so the submodule is the whole module.

Together with Jacobson density, this criterion proves absolute irreducibility from a scalar
commutant without requiring the original field to be algebraically closed.

## References

* N. Jacobson, *Basic Algebra II*, Chapter 4 (the density theorem).
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, §1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Module
open scoped TensorProduct

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Nontrivial M]

/-- A nonzero Lie module whose enveloping algebra realizes every linear operator remains
irreducible after every field extension. -/
theorem isIrreducible_baseChange_of_representation_surjective
    (hsurj : Function.Surjective (representation K L M))
    (A : Type*) [Field A] [Algebra K A] :
    LieModule.IsIrreducible A (A ⊗[K] L) (A ⊗[K] M) := by
  classical
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  -- Invariance under the Lie generators implies invariance under all enveloping operators.
  have hU (u : _root_.UniversalEnvelopingAlgebra K L) :
      ∀ m ∈ N, (representation K L M u).baseChange A m ∈ N := by
    let ρ := (Module.End.baseChangeHom K A M).comp (representation K L M)
    let := Module.compHom (A ⊗[K] M) ρ.toRingHom
    let : IsScalarTower K (_root_.UniversalEnvelopingAlgebra K L) (A ⊗[K] M) :=
      ⟨fun r v m => by
        -- Unfold the local restricted action to use the algebra homomorphism's linearity.
        change ρ (r • v) m = r • ρ v m
        simp only [map_smul, LinearMap.smul_apply]⟩
    exact smul_mem_of_forall_ι_smul_mem (P := N.toSubmodule.restrictScalars K)
      (fun x m hm => by
        -- Unfold the local action to identify the generator with the base-changed Lie action.
        change (representation K L M (_root_.UniversalEnvelopingAlgebra.ι K x)).baseChange A m ∈ N
        rw [representation_ι, ← LieModule.toEnd_baseChange]
        exact N.lie_mem hm) u
  -- A nonzero invariant vector `x` produces every `1 ⊗ m`: apply the extension of the operator
  -- sending a basis vector in the support of `x` to `m` and the other basis vectors to `0`.
  have hN' : N.toSubmodule ≠ ⊥ := fun h => hN ((LieSubmodule.toSubmodule_inj _ _).mp h)
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'
  let b := Module.Free.chooseBasis K M
  obtain ⟨j, hj⟩ : ∃ j, (b.baseChange A).repr x j ≠ 0 := by
    by_contra h
    exact hx0 ((b.baseChange A).repr.map_eq_zero_iff.mp
      (Finsupp.ext fun i => by_contra fun hi => h ⟨i, hi⟩))
  have hone (m : M) : (1 : A) ⊗ₜ[K] m ∈ N := by
    obtain ⟨u, hu⟩ := hsurj (b.constr K (fun i => if i = j then m else 0))
    have hux := hU u x hxN
    have hTx : (representation K L M u).baseChange A x =
        (b.baseChange A).repr x j • ((1 : A) ⊗ₜ[K] m) := by
      conv_lhs => rw [← (b.baseChange A).linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, hu]
      simp only [map_smul, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
        Module.Basis.constr_basis]
      rw [Finset.sum_eq_single j
        (fun i _ hij => by simp [hij])
        (fun h => (h (Finsupp.mem_support_iff.mpr hj)).elim)]
      simp
    rw [hTx] at hux
    simpa [smul_smul, inv_mul_cancel₀ hj] using N.smul_mem ((b.baseChange A).repr x j)⁻¹ hux
  refine eq_top_iff.2 fun y _ => ?_
  clear ‹y ∈ ⊤›
  induction y using TensorProduct.inductionOn with
  | tmul a m =>
    have := N.smul_mem a (hone m)
    rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
  | add y z hy hz => exact N.add_mem hy hz

end TauCeti.UniversalEnvelopingAlgebra
