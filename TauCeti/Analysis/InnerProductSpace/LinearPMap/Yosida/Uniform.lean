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
public import Mathlib.Data.PNat.Basic
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

open Complex NormedSpace Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

private noncomputable def yosidaFlow (A : H →ₗ.[ℂ] H) (n : ℕ+) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (n : ℝ)))

/-- Symmetric Yosida exponential orbits are uniformly Cauchy on bounded time intervals. -/
theorem _root_.IsSelfAdjoint.yosida_exponential_uniform_cauchy
    (hA : IsSelfAdjoint A) (x : H) (R : ℝ) (ε : ℝ)
    (hε : 0 < ε) : ∃ N : ℕ+, ∀ m ≥ N, ∀ n ≥ N, ∀ t : ℝ, |t| ≤ R →
      ‖NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (m : ℝ))) x -
        NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (n : ℝ))) x‖ < ε := by
  have hnorm (n : ℕ+) (t : ℝ) :
      ‖exp (t • (I • A.symmetricYosidaApproximation (n : ℝ)))‖ ≤ 1 := by
    have h := (Semigroups.StronglyContinuousGroup.isUnitary_ofBoundedExp _
      (hA.isSelfAdjoint_symmetricYosidaApproximation (n : ℝ))).opNorm_le_one t
    rw [Semigroups.StronglyContinuousGroup.ofBoundedExp_apply,
      ContinuousLinearMap.norm_restrictScalars] at h
    simpa only [Complex.coe_smul] using h
  have hbound : ∀ᶠ n : ℕ+ in atTop, ∀ t ∈ {t : ℝ | |t| ≤ R}, ‖yosidaFlow A n t‖ ≤ 1 := by
    exact Filter.Eventually.of_forall fun n t _ => hnorm n t
  have hdomain : ∀ y ∈ (A.domain : Set H),
      UniformCauchySeqOn (fun n t => yosidaFlow A n t y) atTop {t : ℝ | |t| ≤ R} := by
    intro y hy
    have hconv := ((hA.tendsto_symmetricYosidaApproximation_apply ⟨y, hy⟩).mono_left
      atTop_le_cocompact).comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)
    have h := Semigroups.uniformCauchySeqOn_exp_smul_apply_of_tendsto
      (G := fun n : ℕ+ => I • A.symmetricYosidaApproximation (n : ℝ))
      (S := {t : ℝ | |t| ≤ R}) (M := 1) (R := R)
      (Filter.Eventually.of_forall fun p =>
        ((hA.commute_symmetricYosidaApproximation (p.1 : ℝ) (p.2 : ℝ)).smul_left I).smul_right I)
      (hconv.const_smul I)
      (Filter.Eventually.of_forall fun n t _ s _ => by
        simpa only [Complex.coe_smul] using! hnorm n (s * t))
      (fun _ ht => ht)
    simpa only [yosidaFlow, Complex.coe_smul] using! h
  have hu := ContinuousLinearMap.uniformCauchySeqOn_apply_of_dense
    (f := yosidaFlow A) (C := 1) hA.dense_domain hbound hdomain x
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hu ε hε
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  simpa only [yosidaFlow, dist_eq_norm] using hN m hm n hn t ht

end TauCeti
