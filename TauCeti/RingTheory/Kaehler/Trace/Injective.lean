/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.Kaehler.Trace.Basic
public import TauCeti.Algebra.Module.LinearMap.Precomp.TorsionFree
public import TauCeti.LinearAlgebra.LinearMap.CyclicAtMaximal

/-!
# Injectivity of the differential trace pairing

Cyclicity of the differential module at every maximal ideal, a nonzero algebraic trace, and a
nonzero derivation into a torsion-free module make the differential trace pairing injective.
The proof uses the general injectivity criterion for modules cyclic at every maximal ideal.
Surjectivity and the residue-field hypotheses needed for full duality are separate.

## Main results

* `Derivation.injective_liftKaehlerDifferential_traceDerivation`: injectivity of the trace pairing.
-/

public section

open TauCeti.Algebra

namespace Derivation

variable {k R B : Type*} [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
  [Module.Free R B] [Module.Finite R B]

/-- If the differential module is cyclic at every maximal ideal, the algebraic trace is nonzero,
and `D` is a nonzero derivation into a torsion-free module, the differential trace pairing
is injective. -/
theorem injective_liftKaehlerDifferential_traceDerivation [IsDomain R] [IsDomain B]
    {M : Type*} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [Module.IsTorsionFree R M] (D : Derivation k R M) (hD : D ≠ 0)
    (htrace : Algebra.trace R B ≠ 0)
    (hcyc : ∀ q : Ideal B, q.IsMaximal →
      ∃ ω : Ω[B⁄k], ∀ η : Ω[B⁄k], ∃ s ∉ q, ∃ a : B, s • η = a • ω) :
    Function.Injective (traceDerivation (B := B) D).liftKaehlerDifferential := by
  apply LinearMap.injective_of_ne_zero_of_forall_isMaximal_exists_smul_eq_smul _ ?_ hcyc
  have ht : ∃ t, D t ≠ 0 := by
    by_contra h
    push Not at h
    apply hD
    ext t
    exact h t
  obtain ⟨t, ht⟩ := ht
  intro h
  have hval := LinearMap.congr_fun h (KaehlerDifferential.D k B (algebraMap R B t))
  rw [liftKaehlerDifferential_comp_D, traceDerivation_algebraMap] at hval
  apply htrace
  ext c
  have hc := congrArg (fun ψ : PrecompLinearMap R B M ↦ ψ c) hval
  simp only [PrecompLinearMap.ofLinearMap_apply, LinearMap.smulRight_apply,
    PrecompLinearMap.zero_apply, LinearMap.zero_apply] at hc ⊢
  exact (smul_eq_zero.mp hc).resolve_right ht

end Derivation
