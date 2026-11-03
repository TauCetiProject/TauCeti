/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Module
public import Mathlib.Algebra.Lie.BaseChange
import TauCeti.LinearAlgebra.End.Adjoin
import TauCeti.LinearAlgebra.TensorProduct.Hom
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Absolute irreducibility from a full enveloping-algebra image

If the enveloping algebra of a finite-dimensional nonzero Lie module acts as every linear
operator, that module remains irreducible after any field extension. A submodule after scalar
extension is invariant under the extended enveloping operators; these span all linear operators
over the larger field. Thus it is either zero or the whole module.

The operator-span comparison uses `LinearMap.isBaseChange_baseChangeHom`. Together with
Jacobson density, this criterion proves absolute irreducibility from a scalar commutant without
requiring the original field to be algebraically closed.

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
  [Module.Finite K M] [Nontrivial M]

/-- A finite-dimensional nonzero Lie module whose enveloping algebra realizes every linear
operator remains irreducible after every field extension. -/
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
  -- Extended K-linear operators span all A-linear operators, since M is finite projective.
  have hEnd (f : Module.End A (A ⊗[K] M)) : ∀ m ∈ N, f m ∈ N := by
    induction f using (LinearMap.isBaseChange_baseChangeHom K A M M).inductionOn with
    | tmul f =>
        obtain ⟨u, rfl⟩ := hsurj f
        exact hU u
    | smul a f hf =>
        intro m hm
        exact N.smul_mem a (hf m hm)
    | add f g hf hg =>
        intro m hm
        exact N.add_mem (hf m hm) (hg m hm)
  have htrivial : N.toSubmodule = ⊥ ∨ N.toSubmodule = ⊤ :=
    eq_bot_or_eq_top_of_adjoin_eq_top (s := Set.univ) (by simp)
      (fun f _ => (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem f).mpr (hEnd f))
  rcases htrivial with hbot | htop
  · exact (hN ((LieSubmodule.toSubmodule_inj _ _).mp hbot)).elim
  · exact (LieSubmodule.toSubmodule_inj _ _).mp htop

end TauCeti.UniversalEnvelopingAlgebra
