/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.Kaehler.Trace.Basic
public import TauCeti.Algebra.Module.LinearMap.Precomp.TorsionFree
public import TauCeti.LinearAlgebra.LinearMap.LocallyCyclic

/-!
# Injectivity of the differential trace pairing

Local cyclicity of the differential module, a nonzero algebraic trace, and a base-ring element
whose derivative is one make the differential trace pairing injective. The proof uses the
general injectivity criterion for maps from locally cyclic modules into torsion-free modules.
Surjectivity and the residue-field hypotheses needed for full duality are separate.

## Main results

* `Derivation.traceDerivation_algebraMap`: the base-ring computation in the precomposition module.
* `Derivation.injective_liftKaehlerDifferential_traceDerivation`: injectivity of the trace pairing.
-/

public section

open TauCeti.Algebra

namespace Derivation

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
  [Module.Free R B] [Module.Finite R B]

/-- On base-ring elements, the trace derivation is the algebraic trace multiplied by the
original derivative, for the precomposition action. -/
lemma traceDerivation_algebraMap (D : Derivation k R R) (r : R) :
    traceDerivation (B := B) D (algebraMap R B r) =
      algebraMap R B (D r) • PrecompLinearMap.ofLinearMap (Algebra.trace R B) := by
  apply PrecompLinearMap.ext
  intro c
  simp only [traceDerivation_apply, traceDeriv_algebraMap, PrecompLinearMap.smul_apply,
    PrecompLinearMap.ofLinearMap_apply, smul_eq_mul]
  rw [← Algebra.smul_def, LinearMap.map_smul]
  exact mul_comm _ _

/-- Local cyclicity of differentials makes a nonzero differential trace pairing injective.
No Dedekind, normality, or residue-field separability hypothesis is required. -/
theorem injective_liftKaehlerDifferential_traceDerivation [IsDomain R] [IsDomain B]
    (D : Derivation k R R) (t : R) (ht : D t = 1) (htrace : Algebra.trace R B ≠ 0)
    (hcyc : ∀ q : Ideal B, q.IsMaximal →
      ∃ ω : Ω[B⁄k], ∀ η : Ω[B⁄k], ∃ s ∉ q, ∃ a : B, s • η = a • ω) :
    Function.Injective (traceDerivation (B := B) D).liftKaehlerDifferential := by
  apply LinearMap.injective_of_locally_cyclic_of_ne_zero _ ?_ hcyc
  intro h
  have hval := LinearMap.congr_fun h (KaehlerDifferential.D k B (algebraMap R B t))
  rw [liftKaehlerDifferential_comp_D, traceDerivation_algebraMap, ht, map_one, one_smul] at hval
  apply htrace
  simpa only [PrecompLinearMap.toLinearMap_ofLinearMap, LinearMap.zero_apply, map_zero]
    using congrArg PrecompLinearMap.toLinearMap hval

end Derivation
