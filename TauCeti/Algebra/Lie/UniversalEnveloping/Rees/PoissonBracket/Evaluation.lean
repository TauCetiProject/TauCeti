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

When a Lie algebra `L` over a commutative ring `R` admits a finite basis `b`, evaluating the
zero-fibre Poisson bracket `reesZeroFiberBracket R L p q` at `ξ : Module.Dual R L` gives the
linear Kirillov–Kostant–Souriau Poisson formula
`ξ ⁅b.symmetricGradient p ξ, b.symmetricGradient q ξ⁆`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.lift_reesZeroFiberBracket_apply`: evaluation at `ξ ∈ L*`
  equals `ξ ⁅b.symmetricGradient p ξ, b.symmetricGradient q ξ⁆`.
* `TauCeti.UniversalEnvelopingAlgebra.lift_reesZeroFiberBracket_eq_lie_symmetricGradient`: same
  evaluation formula for any bilinear bracket characterized by the divided-commutator equation.

## References

* S. Gutt, *Deformation Quantization and Symmetries*, Lecture 1, slide 14 (2019), solely for the
  real characteristic-zero sign convention `{ℓ_x, ℓ_y}(ξ) = ξ([x, y])`; the arbitrary-ring divided
  commutator, zero-fibre bracket, and polynomial evaluation identity are derived directly from the
  PBW Rees algebra, injective multiplication by `reesParameter`, and the Leibniz rule.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section LinearPoissonEvaluation

/-- Evaluating `reesZeroFiberBracket R L p q` at `ξ : Module.Dual R L` gives the linear Poisson
formula `ξ ⁅b.symmetricGradient p ξ, b.symmetricGradient q ξ⁆`, for any finite basis `b` of `L`. -/
theorem lift_reesZeroFiberBracket_apply {R : Type u} [CommRing R]
    (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Free R L] {ι : Type w} [Fintype ι]
    (b : Module.Basis ι R L) (p q : SymmetricAlgebra R L) (ξ : Module.Dual R L) :
    SymmetricAlgebra.lift ξ (reesZeroFiberBracket R L p q) =
      ξ ⁅b.symmetricGradient p ξ, b.symmetricGradient q ξ⁆ := by
  have hgen : ∀ (x : L) (r : SymmetricAlgebra R L),
      SymmetricAlgebra.lift ξ (reesZeroFiberBracket R L (SymmetricAlgebra.ι R L x) r) =
        ξ ⁅x, b.symmetricGradient r ξ⁆ := by
    intro x r
    induction r using SymmetricAlgebra.induction with
    | algebraMap c => simp
    | ι y => simp
    | mul r₁ r₂ h₁ h₂ =>
      rw [reesZeroFiberBracket_mul_right, map_add, map_mul, map_mul, h₁, h₂,
        b.symmetricGradient_mul, lie_add, lie_smul, lie_smul, map_add, LinearMap.map_smul,
        LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      ring
    | add r₁ r₂ h₁ h₂ => simp [h₁, h₂]
  induction p using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι x => rw [b.symmetricGradient_ι, hgen]
  | mul p₁ p₂ h₁ h₂ =>
    rw [reesZeroFiberBracket_mul_left, map_add, map_mul, map_mul, h₁, h₂,
      b.symmetricGradient_mul, add_lie, smul_lie, smul_lie, map_add, LinearMap.map_smul,
      LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]

/-- Every `R`-bilinear bracket on `SymmetricAlgebra R L` satisfying the divided-commutator equation
of `exists_reesZeroFiberBracket` evaluates at `ξ ∈ L*` by the linear Poisson formula
`{p, q}(ξ) = ξ ⁅b.symmetricGradient p ξ, b.symmetricGradient q ξ⁆` (over `R = ℝ`, matching the sign
convention `P_ξ(X, Y) = ξ([X, Y])` of Gutt, *Deformation Quantization and Symmetries*, Lecture 1,
slide 14). -/
theorem lift_reesZeroFiberBracket_eq_lie_symmetricGradient {R : Type u} [CommRing R]
    (L : Type v) [LieRing L] [LieAlgebra R L] [Module.Free R L] {ι : Type w} [Fintype ι]
    (b : Module.Basis ι R L)
    (B : SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L →ₗ[R] SymmetricAlgebra R L)
    (hB : ∀ a c d : reesAlgebra R L,
      a * c - c * a = reesParameter R L * d →
      B (reesSpecializationZero R L a) (reesSpecializationZero R L c) =
        reesSpecializationZero R L d)
    (p q : SymmetricAlgebra R L) (ξ : Module.Dual R L) :
    SymmetricAlgebra.lift ξ (B p q) = ξ ⁅b.symmetricGradient p ξ, b.symmetricGradient q ξ⁆ := by
  rw [eq_reesZeroFiberBracket_of_commutator_eq hB]
  exact lift_reesZeroFiberBracket_apply L b p q ξ

end LinearPoissonEvaluation

end TauCeti.UniversalEnvelopingAlgebra
