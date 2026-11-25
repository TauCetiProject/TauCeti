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
# Uniform Cauchy convergence of Yosida exponential approximants

The exponential orbits of the symmetric Yosida approximations of a self-adjoint
partial operator are uniformly Cauchy on bounded sets of times as the absolute value
of the real shift tends to infinity.
The proof first uses the **Duhamel estimate**

`‖exp (t • Bₘ) ψ - exp (t • Bₙ) ψ‖ ≤ |t| ‖(Bₘ - Bₙ) ψ‖`

for *commuting* skew-adjoint `Bₘ`, `Bₙ`, together with convergence of the
approximations on the domain. Density and unitarity extend the uniform bound
to every vector.

## Sources

That a bounded skew-adjoint operator exponentiates to a strongly continuous
one-parameter unitary group, and that this is the bounded case of Stone's theorem,
is standard (Reed--Simon, *Methods of Modern Mathematical Physics I*).

## Provenance

The result and the strategy of combining Duhamel comparison on the domain with a density
argument adapt the Kitware DKPS formalization at `b9a02d00c` (Jon Crall, Claude Opus 5,
Kitware 2026, Apache 2.0), specifically
`ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean` and
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean`.

The DKPS comparison draws on the Duhamel argument in
`Spectra/YosidaHille/Approximation/Commutation.lean` at Spectra commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63` (`norm_expBounded_pairwise_le`
and its supporting commutation lemmas, Adam Bornemann, copyright 2026 Spectra
Formalization Project, Apache 2.0). Here the shared Tau Ceti bounded-generator criterion
supplies the comparison. The result strengthens the donor's pointwise Cauchy conclusion
to uniform Cauchy convergence on bounded sets of times.
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
