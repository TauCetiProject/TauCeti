/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Yosida.Basic
public import TauCeti.Analysis.InnerProductSpace.Exponential
import TauCeti.Analysis.Semigroups.Group.Stone.Basic
public import TauCeti.Analysis.Normed.Operator.Dense
public import Mathlib.Data.PNat.Basic
import TauCeti.Topology.MetricSpace.Pseudo.Basic

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
     with bounds equal to one, using scalar restriction and time reversal.
-/

public section

namespace TauCeti

open Complex NormedSpace Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

private noncomputable def yosidaFlow (A : H →ₗ.[ℂ] H) (n : ℕ+) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (n : ℝ)))

private theorem yosidaFlow_difference (hA : IsSelfAdjoint A) (m n : ℕ+) (t : ℝ) (x : H) :
    ‖yosidaFlow A m t x - yosidaFlow A n t x‖ ≤
      |t| * ‖A.symmetricYosidaApproximation (m : ℝ) x -
        A.symmetricYosidaApproximation (n : ℝ) x‖ := by
  have h := ContinuousLinearMap.norm_exp_smul_I_sub_exp_smul_I_apply_le
    (hA.isSelfAdjoint_symmetricYosidaApproximation (m : ℝ))
    (hA.isSelfAdjoint_symmetricYosidaApproximation (n : ℝ))
    (hA.commute_symmetricYosidaApproximation (m : ℝ) (n : ℝ)) t x
  simpa only [yosidaFlow, sub_apply, smul_apply, ← smul_sub, norm_smul, norm_I, one_mul] using h

/-- Symmetric Yosida exponential orbits are uniformly Cauchy on bounded time intervals. -/
theorem _root_.IsSelfAdjoint.yosida_exponential_uniform_cauchy
    (hA : IsSelfAdjoint A) (x : H) (R : ℝ) (ε : ℝ)
    (hε : 0 < ε) : ∃ N : ℕ+, ∀ m ≥ N, ∀ n ≥ N, ∀ t : ℝ, |t| ≤ R →
      ‖NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (m : ℝ))) x -
        NormedSpace.exp (t • (I • A.symmetricYosidaApproximation (n : ℝ))) x‖ < ε := by
  let K := max R 0 + 1
  have hbound : ∀ᶠ n : ℕ+ in atTop, ∀ t ∈ {t : ℝ | |t| ≤ R}, ‖yosidaFlow A n t‖ ≤ 1 := by
    exact Filter.Eventually.of_forall fun n t _ =>
      Semigroups.StronglyContinuousGroup.norm_exp_smul_I_le _
        (hA.isSelfAdjoint_symmetricYosidaApproximation (n : ℝ)) t
  have hdomain : ∀ y ∈ (A.domain : Set H),
      UniformCauchySeqOn (fun n t => yosidaFlow A n t y) atTop {t : ℝ | |t| ≤ R} := by
    intro y hy
    have hconv := ((hA.tendsto_symmetricYosidaApproximation_apply ⟨y, hy⟩).mono_left
      atTop_le_cocompact).comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)
    have hzero : Tendsto (fun p : ℕ+ × ℕ+ => K * dist
        (A.symmetricYosidaApproximation (p.1 : ℝ) y)
        (A.symmetricYosidaApproximation (p.2 : ℝ) y)) (atTop ×ˢ atTop) (𝓝 0) := by
      simpa only [Function.comp_apply, dist_self, mul_zero] using tendsto_const_nhds.mul
        ((hconv.comp tendsto_fst).dist (hconv.comp tendsto_snd))
    apply uniformCauchySeqOn_of_dist_le hzero
    exact Filter.Eventually.of_forall fun p t ht => by
      have htK : |t| ≤ K := le_trans ht
        (le_trans (le_max_left R 0) (by dsimp [K]; linarith))
      calc
        dist (yosidaFlow A p.1 t y) (yosidaFlow A p.2 t y) ≤
            |t| * dist (A.symmetricYosidaApproximation (p.1 : ℝ) y)
              (A.symmetricYosidaApproximation (p.2 : ℝ) y) := by
          simpa only [dist_eq_norm] using yosidaFlow_difference hA p.1 p.2 t y
        _ ≤ K * dist (A.symmetricYosidaApproximation (p.1 : ℝ) y)
            (A.symmetricYosidaApproximation (p.2 : ℝ) y) :=
          mul_le_mul_of_nonneg_right htK dist_nonneg
  have hu := ContinuousLinearMap.uniformCauchySeqOn_apply_of_dense
    (f := yosidaFlow A) (C := 1) hA.dense_domain hbound hdomain x
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hu ε hε
  refine ⟨N, fun m hm n hn t ht => ?_⟩
  simpa only [yosidaFlow, dist_eq_norm] using hN m hm n hn t ht

end TauCeti
