/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.PoissonBracket.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Gradient

/-!
# Linear Poisson evaluation of the PBW Rees zero-fibre bracket

For a Lie algebra `L` that is free as a module over a commutative ring `R`, evaluating the
zero-fibre Poisson bracket `reesZeroFiberBracket R L p q` at `ξ : Module.Dual R L` gives the
linear Kirillov–Kostant–Souriau Poisson formula `ξ ⁅p.gradient ξ, q.gradient ξ⁆`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.lift_reesZeroFiberBracket_apply`: evaluation at `ξ ∈ L*`
  equals `ξ ⁅p.gradient ξ, q.gradient ξ⁆`.
* `TauCeti.UniversalEnvelopingAlgebra.lift_reesZeroFiberBracket_eq_lie_gradient`: same evaluation
  formula for any bilinear bracket characterized by the divided-commutator equation.

## References

* S. Gutt, *Deformation Quantization and Symmetries*, Lecture 1, slide 14 (2019), solely for the
  real characteristic-zero sign convention `{ℓ_x, ℓ_y}(ξ) = ξ([x, y])`; the arbitrary-ring divided
  commutator, zero-fibre bracket, and polynomial evaluation identity are derived directly from the
  PBW Rees algebra, injective multiplication by `reesParameter`, and the Leibniz rule.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

section LinearPoissonEvaluation

/-- Evaluating `reesZeroFiberBracket R L p q` at `ξ : Module.Dual R L` gives the linear Poisson
formula `ξ ⁅p.gradient ξ, q.gradient ξ⁆`. -/
theorem lift_reesZeroFiberBracket_apply {R : Type u} [CommRing R]
    (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Free R L]
    (p q : SymmetricAlgebra R L) (ξ : Module.Dual R L) :
    SymmetricAlgebra.lift ξ (reesZeroFiberBracket R L p q) =
      ξ ⁅p.gradient ξ, q.gradient ξ⁆ := by
  have hgen : ∀ (x : L) (r : SymmetricAlgebra R L),
      SymmetricAlgebra.lift ξ (reesZeroFiberBracket R L (SymmetricAlgebra.ι R L x) r) =
        ξ ⁅x, r.gradient ξ⁆ := by
    intro x r
    induction r using SymmetricAlgebra.induction with
    | algebraMap c => simp
    | ι y => simp
    | mul r₁ r₂ h₁ h₂ =>
      simp [reesZeroFiberBracket_mul_right, h₁, h₂]
      ring
    | add r₁ r₂ h₁ h₂ => simp [h₁, h₂]
  induction p using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι x => rw [SymmetricAlgebra.gradient_ι, hgen]
  | mul p₁ p₂ h₁ h₂ =>
    simp [reesZeroFiberBracket_mul_left, h₁, h₂]
    ring
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]

/-- Every `R`-bilinear bracket on `SymmetricAlgebra R L` satisfying the divided-commutator equation
of `exists_reesZeroFiberBracket` evaluates at `ξ ∈ L*` by the linear Poisson formula
`{p, q}(ξ) = ξ ⁅p.gradient ξ, q.gradient ξ⁆` (over `R = ℝ`, matching the sign convention
`P_ξ(X, Y) = ξ([X, Y])` of Gutt, *Deformation Quantization and Symmetries*, Lecture 1, slide 14). -/
theorem lift_reesZeroFiberBracket_eq_lie_gradient {R : Type u} [CommRing R]
    (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Free R L]
    (B : SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L)
    (hB : ∀ a c d : reesAlgebra R L,
      a * c - c * a = reesParameter R L * d →
      B (reesSpecializationZero R L a) (reesSpecializationZero R L c) =
        reesSpecializationZero R L d)
    (p q : SymmetricAlgebra R L) (ξ : Module.Dual R L) :
    SymmetricAlgebra.lift ξ (B p q) = ξ ⁅p.gradient ξ, q.gradient ξ⁆ := by
  rw [eq_reesZeroFiberBracket_of_commutator_eq hB]
  exact lift_reesZeroFiberBracket_apply L p q ξ

end LinearPoissonEvaluation

end TauCeti.UniversalEnvelopingAlgebra
