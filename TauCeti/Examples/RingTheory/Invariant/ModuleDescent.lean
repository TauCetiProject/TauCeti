/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Invariant.ModuleDescent
import TauCeti.RingTheory.Etale.Torsor

/-!
# Tests for Galois descent of modules

Over a finite étale torsor the descent isomorphisms apply with the hypotheses supplied by the
Chase–Harrison–Rosenberg characterization. For a finite Galois extension of fields this is
Speiser's lemma: an `L`-vector space with semilinear Galois action is spanned by its invariants.
The descent map is multiplication.
-/

open TensorProduct

namespace TauCeti.MulSemiringAction

/-- Over a finite étale torsor, a module with semilinear action is the base change of its
invariants, and every module is the invariants of its base change. -/
example (G A B : Type*) [Group G] [Finite G] [CommRing A] [CommRing B] [Algebra A B]
    [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsFiniteEtaleTorsor G A B]
    (N : Type*) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [DistribMulAction G N] [SMulDistribClass G B N]
    (M : Type*) [AddCommGroup M] [Module A M] :
    -- The semilinear action on `N` is `A`-linear, so its invariants form an `A`-module.
    have := smulCommClass_of_smulDistribClass A B G N
    -- `G` acts on the left factor of `B ⊗[A] M` once `A` and `G` commute in this order.
    have : SMulCommClass A G B := .symm _ _ _
    Nonempty (B ⊗[A] (Representation.ofDistribMulAction A G N).invariants ≃ₗ[B] N) ∧
      Nonempty (M ≃ₗ[A] (Representation.ofDistribMulAction A G (B ⊗[A] M)).invariants) := by
  intro _ _
  obtain ⟨_, _, hG⟩ := Algebra.isFiniteEtaleTorsor_iff.mp ‹Algebra.IsFiniteEtaleTorsor G A B›
  have := Fintype.ofFinite G
  exact ⟨⟨baseChangeInvariantsEquiv A B G N hG⟩,
    ⟨invariantsBaseChangeEquiv A B G M (exists_sum_smul_eq_one hG)⟩⟩

/-- *Speiser's lemma*: for a finite Galois extension `L / K`, an `L`-vector space `V` with
semilinear Galois action is `L ⊗[K] Vᴳ`, by `x ⊗ v ↦ x • v`. -/
example (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (V : Type*) [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
    [DistribMulAction Gal(L/K) V] [SMulDistribClass Gal(L/K) L V]
    [SMulCommClass Gal(L/K) K V] (x : L)
    (v : (Representation.ofDistribMulAction K Gal(L/K) V).invariants) :
    baseChangeInvariantsEquiv K L Gal(L/K) V
        ((Algebra.isFiniteEtaleTorsor_iff (G := Gal(L/K)) (A := K) (B := L)).mp inferInstance).2.2
        (x ⊗ₜ v) = x • (v : V) := by
  simp

end TauCeti.MulSemiringAction
