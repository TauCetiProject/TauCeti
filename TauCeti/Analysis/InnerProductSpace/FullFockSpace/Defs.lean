/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.CompletedTensorPower

/-!
# The full Fock space

Given an inner product space `H` over `𝕜` (`ℝ` or `ℂ`), its *full* (or *Boltzmann*) *Fock space* is
the `ℓ²` Hilbert direct sum
$$\mathcal{F}(H) = \mathbb{k}\,\Omega \oplus \bigoplus_{n \ge 1} H^{\widehat{\otimes} n}$$
of all completed Hilbert tensor powers `CompletedTensorPower 𝕜 H n` (defined in
`TauCeti.Analysis.InnerProductSpace.CompletedTensorPower`). Because every tensor grade is completed
individually before forming the `ℓ²` direct sum, `FullFockSpace 𝕜 H` is unconditionally a complete
inner product space (`CompleteSpace`) even when `H` itself is not complete.

Vacuum operators, creation and annihilation operators, pure tensor words, and `HilbertBasis`
expansions are developed in `TauCeti.Analysis.InnerProductSpace.FullFockSpace.Basic`; free gauge
operators are developed in `TauCeti.Analysis.InnerProductSpace.FullFockSpace.Gauge`.

## Main definitions

* `TauCeti.FullFockSpace 𝕜 H`: the full Fock space `lp (CompletedTensorPower 𝕜 H) 2`.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Series, Vol. 1,
  American Mathematical Society, 1992, §2.6.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, London Mathematical
  Society Lecture Note Series, Vol. 335, Cambridge University Press, 2006, Lecture 7.
* K. R. Parthasarathy, *An Introduction to Quantum Stochastic Calculus*, Birkhäuser, 1992, §II.19.
-/

public section

noncomputable section

namespace TauCeti

universe u v

/-- The *full* (or *Boltzmann*) *Fock space*
$\mathcal{F}(H) = \bigoplus_{n \ge 0} H^{\widehat{\otimes} n}$ over an inner product space `H`,
realized as the `ℓ²` Hilbert direct sum of `CompletedTensorPower 𝕜 H`. Because each tensor grade is
completed individually, `FullFockSpace 𝕜 H` is always a Hilbert space (`CompleteSpace`). -/
abbrev FullFockSpace (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : Type (max u v) :=
  lp (CompletedTensorPower 𝕜 H) 2

end TauCeti
