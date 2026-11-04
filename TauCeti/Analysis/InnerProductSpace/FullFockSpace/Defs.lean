/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Completed Hilbert tensor powers and the full Fock space

Given an inner product space `H` over `𝕜` (`ℝ` or `ℂ`), its *full* (or *Boltzmann*) *Fock space* is
the `ℓ²` Hilbert direct sum
$$\mathcal{F}(H) = \mathbb{k}\,\Omega \oplus \bigoplus_{n \ge 1} H^{\widehat{\otimes} n}$$
of all completed Hilbert tensor powers of `H`. Every tensor grade is completed individually before
forming the `ℓ²` direct sum, so `FullFockSpace 𝕜 H` is unconditionally a complete inner product
space (`CompleteSpace`) even when `H` itself is not complete.

This file constructs the graded summands `CompletedTensorPower 𝕜 H n`, their canonical grade-zero
and successor linear isometric equivalences `CompletedTensorPower.zeroEquiv` and
`CompletedTensorPower.succEquiv`, and the `ℓ²` direct sum `FullFockSpace 𝕜 H`. Vacuum operators,
creation and annihilation operators, pure tensor words, and `HilbertBasis` expansions are developed
in `TauCeti.Analysis.InnerProductSpace.FullFockSpace.Basic`; gauge operators are developed in
`TauCeti.Analysis.InnerProductSpace.FullFockSpace.Gauge`.

## Main definitions

* `TauCeti.CompletedTensorPower 𝕜 H n`: the `n`-th completed Hilbert tensor power
  $H^{\widehat{\otimes} n}$ of `H`.
* `TauCeti.CompletedTensorPower.zeroEquiv`: canonical linear isometric equivalence
  `CompletedTensorPower 𝕜 H 0 ≃ₗᵢ[𝕜] 𝕜`.
* `TauCeti.CompletedTensorPower.succEquiv`: canonical linear isometric equivalence
  `CompletedTensorPower 𝕜 H (n + 1) ≃ₗᵢ[𝕜] Completion (H ⊗[𝕜] CompletedTensorPower 𝕜 H n)`.
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

open scoped InnerProductSpace TensorProduct

namespace TauCeti

universe u v

/-- Internal bundled Hilbert space in `Type (max u v)` used to construct completed tensor powers
and their inner-product instances simultaneously by recursion on the tensor grade. -/
private structure BundledHilbert (𝕜 : Type u) [RCLike 𝕜] : Type (max u v + 1) where
  carrier : Type (max u v)
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [innerProductSpace : InnerProductSpace 𝕜 carrier]
  [completeSpace : CompleteSpace carrier]

attribute [local instance] BundledHilbert.normedAddCommGroup BundledHilbert.innerProductSpace
  BundledHilbert.completeSpace

private def completedTensorPowerAux (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : ℕ → BundledHilbert.{u, v} 𝕜
  | 0 => ⟨EuclideanSpace 𝕜 (ULift.{v} Unit)⟩
  | n + 1 =>
    let prev := completedTensorPowerAux 𝕜 H n
    ⟨UniformSpace.Completion (H ⊗[𝕜] prev.carrier)⟩

/-! The Hilbert-space instances of `CompletedTensorPower` are `@[no_expose]`d so their private
recursive bundle stays opaque to downstream modules; external callers interact with grade `0` and
grade `n + 1` exclusively through `CompletedTensorPower.zeroEquiv` and
`CompletedTensorPower.succEquiv`. -/

/-- The `n`-th completed Hilbert tensor power $H^{\widehat{\otimes} n}$ of an inner product space
`H` over `𝕜`. Grade `0` is canonically isometric to `𝕜` (`CompletedTensorPower.zeroEquiv`), and
grade `n + 1` is canonically isometric to `Completion (H ⊗[𝕜] CompletedTensorPower 𝕜 H n)`
(`CompletedTensorPower.succEquiv`). -/
def CompletedTensorPower (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (n : ℕ) : Type (max u v) :=
  (completedTensorPowerAux 𝕜 H n).carrier

namespace CompletedTensorPower

@[no_expose]
instance instNormedAddCommGroup {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (n : ℕ) :
    NormedAddCommGroup (CompletedTensorPower 𝕜 H n) :=
  (completedTensorPowerAux 𝕜 H n).normedAddCommGroup

@[no_expose]
instance instInnerProductSpace {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (n : ℕ) :
    InnerProductSpace 𝕜 (CompletedTensorPower 𝕜 H n) :=
  (completedTensorPowerAux 𝕜 H n).innerProductSpace

instance instCompleteSpace {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (n : ℕ) :
    CompleteSpace (CompletedTensorPower 𝕜 H n) :=
  (completedTensorPowerAux 𝕜 H n).completeSpace

/-- Grade `0` of `CompletedTensorPower 𝕜 H` is canonically linearly isometric to `𝕜`. -/
def zeroEquiv (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    CompletedTensorPower 𝕜 H 0 ≃ₗᵢ[𝕜] 𝕜 :=
  (OrthonormalBasis.singleton (ULift.{v} Unit) 𝕜).repr.symm

/-- Grade `n + 1` of `CompletedTensorPower 𝕜 H` is canonically linearly isometric to the completion
of `H ⊗[𝕜] CompletedTensorPower 𝕜 H n`. -/
def succEquiv (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (n : ℕ) :
    CompletedTensorPower 𝕜 H (n + 1) ≃ₗᵢ[𝕜]
      UniformSpace.Completion (H ⊗[𝕜] CompletedTensorPower 𝕜 H n) :=
  LinearIsometryEquiv.refl 𝕜 _

end CompletedTensorPower

/-- The *full* (or *Boltzmann*) *Fock space*
$\mathcal{F}(H) = \bigoplus_{n \ge 0} H^{\widehat{\otimes} n}$ over an inner product space `H`,
realized as the `ℓ²` Hilbert direct sum of `CompletedTensorPower 𝕜 H`. Because each tensor grade is
completed individually, `FullFockSpace 𝕜 H` is always a Hilbert space (`CompleteSpace`). -/
abbrev FullFockSpace (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : Type (max u v) :=
  lp (CompletedTensorPower 𝕜 H) 2

end TauCeti
