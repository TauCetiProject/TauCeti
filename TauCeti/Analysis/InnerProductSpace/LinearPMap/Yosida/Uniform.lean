/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Yosida.Basic
import TauCeti.Analysis.Semigroups.BoundedGenerator.Perturbation
import TauCeti.Analysis.Semigroups.Group.Stone.Basic
public import TauCeti.Analysis.Normed.Operator.Dense
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Uniform convergence of Yosida exponential approximants

The exponential orbits of the symmetric Yosida approximations of a self-adjoint
partial operator form a Cauchy family uniformly for time in any bounded interval.
The proof first uses the **Duhamel estimate**

`‖exp (t • Bₘ) ψ - exp (t • Bₙ) ψ‖ ≤ |t| ‖(Bₘ - Bₙ) ψ‖`

for *commuting* skew-adjoint `Bₘ`, `Bₙ`, together with convergence of the
approximations on the domain. Density and unitarity extend the uniform bound
to every vector. No limit group is constructed in this module.

## Sources

That a bounded skew-adjoint operator exponentiates to a strongly continuous
one-parameter unitary group, and that this is the bounded case of Stone's theorem,
is standard (Reed--Simon, *Methods of Modern Mathematical Physics I*).

## Provenance

The Duhamel and density arguments adapt
`ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean` and
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean`
in the Kitware DKPS formalization at `b9a02d00c`
(Jon Crall, Claude Opus 5; Kitware 2026; Apache-2.0).

* **Original repository:** Spectra, commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
* **Original module:** `Spectra/YosidaHille/Approximation/Commutation.lean`
  (`norm_expBounded_pairwise_le` and its supporting commutation lemmas).
* **Original authors / copyright / licence:** Copyright (c) 2026 Spectra
  Formalization Project; `Authors: Adam Bornemann`; Apache 2.0.
* **Extraction class:** *adapted.*  The proof architecture — differentiate
  `s ↦ exp((t-s)Bₙ) exp(sBₘ) ψ`, recognise the derivative as
  `exp((t-s)Bₙ) exp(sBₘ) (Bₘ - Bₙ) ψ`, integrate, and bound the integrand by
  unitarity — is Spectra's, and is the classical Duhamel argument.
* **Semantic differences from the donor:**
  1. Stated over Mathlib's `NormedSpace.exp` rather than Spectra's hand-rolled
     `expBounded` power series.  Spectra proves the two agree
     (`expBounded_eq_exp`), so nothing is lost; what *is* saved is the 576 lines
     of `ExpBounded/{Helpers,Adjoint,Unitary}` establishing summability, the
     group law and unitarity, all of which Mathlib already has.
  2. Norm preservation comes directly from the native bounded Stone group.
     The Duhamel estimate specializes the native bounded-semigroup comparison
     through one shared bounded-generator uniform-Cauchy criterion. It uses time-one
     comparison for scaled generators, covering signed times directly.
-/

public section

namespace TauCeti

open Complex NormedSpace Filter Set Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- Along real shifts escaping to infinity, symmetric Yosida exponential orbits are uniformly
Cauchy on every bounded set of times. -/
theorem _root_.IsSelfAdjoint.uniformCauchySeqOn_exp_smul_I_smul_symmetricYosidaApproximation_apply
    (hA : IsSelfAdjoint A) (x : H) {S : Set ℝ} {R : ℝ}
    (hS : ∀ t ∈ S, |t| ≤ R) :
    UniformCauchySeqOn
      (fun (r t : ℝ) => exp ((t : ℂ) • (I • A.symmetricYosidaApproximation r)) x)
      (cocompact ℝ) S := by
  have hnorm (r t : ℝ) :
      ‖exp ((t : ℂ) • (I • A.symmetricYosidaApproximation r))‖ ≤ 1 := by
    have h := (Semigroups.StronglyContinuousGroup.isUnitary_ofBoundedExp _
      (hA.isSelfAdjoint_symmetricYosidaApproximation r)).opNorm_le_one t
    rwa [Semigroups.StronglyContinuousGroup.ofBoundedExp_apply,
      ContinuousLinearMap.norm_restrictScalars] at h
  refine ContinuousLinearMap.uniformCauchySeqOn_apply_of_dense
    (C := 1) hA.dense_domain (.of_forall fun r t _ => hnorm r t) ?_ x
  intro y hy
  exact Semigroups.uniformCauchySeqOn_exp_smul_apply_of_tendsto
    (G := fun r => I • A.symmetricYosidaApproximation r)
    (.of_forall fun p =>
      ((hA.commute_symmetricYosidaApproximation p.1 p.2).smul_left I).smul_right I)
    ((hA.tendsto_symmetricYosidaApproximation_apply ⟨y, hy⟩).const_smul I)
    (.of_forall fun r t _ s _ => hnorm r (s * t)) hS

end TauCeti
