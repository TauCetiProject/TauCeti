/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.UniformSpace.UniformApproximation
public import TauCeti.Analysis.PositiveDefinite.Limits

/-!
# Locally uniform limits of continuous positive-definite functions

This file strengthens the pointwise limit closure in
`TauCeti.Analysis.PositiveDefinite.Limits`. Pointwise convergence preserves positive-definiteness,
but it need not preserve continuity. Locally uniform convergence supplies exactly the additional
hypothesis needed to retain both properties.

The results are stated for a general topological involutive additive monoid and an arbitrary
nontrivial filter. The continuity and positive-definiteness hypotheses are both eventual, so a
finite initial segment of the approximating family may be discarded. Specializations are provided
for families satisfying the hypotheses everywhere and for sequences.

## Main declarations

* `TauCeti.continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly`: an eventually
  continuous, eventually positive-definite family has a continuous positive-definite locally
  uniform limit.
* `TauCeti.continuous_and_isPositiveDefinite_of_forall_tendstoLocallyUniformly`: the same result
  when every member of the family is continuous and positive definite.
* `TauCeti.continuous_and_isPositiveDefinite_of_seq_tendstoLocallyUniformly`: the sequential
  specialization.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C (pointwise limits preserve
  positive-definiteness, while continuity requires an additional locally uniform convergence
  hypothesis).
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [AddMonoid M] [StarAddMonoid M]
  {ι : Type*} {l : Filter ι} [NeBot l] {F : ι → M → ℂ} {G : M → ℂ}

/-- A locally uniform limit of eventually positive-definite functions is positive definite.

Unlike continuity, positive-definiteness itself only needs pointwise convergence; local uniform
convergence is converted to pointwise convergence before applying
`TauCeti.IsPositiveDefinite.of_tendsto`. -/
theorem IsPositiveDefinite.of_tendstoLocallyUniformly
    (hF : ∀ᶠ i in l, IsPositiveDefinite (F i))
    (hlim : TendstoLocallyUniformly F G l) :
    IsPositiveDefinite G :=
  IsPositiveDefinite.of_tendsto hF fun x =>
    hlim.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

/-- A locally uniform limit of eventually continuous, eventually positive-definite functions is
continuous and positive definite. The two eventual hypotheses may hold on different tails; no
common index has to be chosen explicitly. -/
theorem continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly
    (hcont : ∀ᶠ i in l, Continuous (F i))
    (hpd : ∀ᶠ i in l, IsPositiveDefinite (F i))
    (hlim : TendstoLocallyUniformly F G l) :
    Continuous G ∧ IsPositiveDefinite G :=
  ⟨hlim.continuous hcont.frequently, IsPositiveDefinite.of_tendstoLocallyUniformly hpd hlim⟩

/-- A locally uniform limit of a family of continuous positive-definite functions is continuous
and positive definite. -/
theorem continuous_and_isPositiveDefinite_of_forall_tendstoLocallyUniformly
    (hcont : ∀ i, Continuous (F i))
    (hpd : ∀ i, IsPositiveDefinite (F i))
    (hlim : TendstoLocallyUniformly F G l) :
    Continuous G ∧ IsPositiveDefinite G :=
  continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly
    (Eventually.of_forall hcont) (Eventually.of_forall hpd) hlim

/-- A sequential locally uniform limit of eventually continuous, eventually positive-definite
functions is continuous and positive definite. -/
theorem continuous_and_isPositiveDefinite_of_seq_tendstoLocallyUniformly
    {F : ℕ → M → ℂ} {G : M → ℂ}
    (hcont : ∀ᶠ n in atTop, Continuous (F n))
    (hpd : ∀ᶠ n in atTop, IsPositiveDefinite (F n))
    (hlim : TendstoLocallyUniformly F G atTop) :
    Continuous G ∧ IsPositiveDefinite G :=
  continuous_and_isPositiveDefinite_of_tendstoLocallyUniformly hcont hpd hlim

/-- A sequential locally uniform limit of continuous positive-definite functions is continuous
and positive definite. -/
theorem continuous_and_isPositiveDefinite_of_forall_seq_tendstoLocallyUniformly
    {F : ℕ → M → ℂ} {G : M → ℂ}
    (hcont : ∀ n, Continuous (F n))
    (hpd : ∀ n, IsPositiveDefinite (F n))
    (hlim : TendstoLocallyUniformly F G atTop) :
    Continuous G ∧ IsPositiveDefinite G :=
  continuous_and_isPositiveDefinite_of_forall_tendstoLocallyUniformly hcont hpd hlim

end TauCeti
