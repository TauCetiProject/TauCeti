/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The product of two integrals on a group as an iterated correlation integral

For a left-invariant s-finite measure `ν` on a measurable group and integrable `A`, `B`, the
substitution `v = u t` in `∫∫ A(u) B(v) dν(u) dν(v)` gives

`(∫ A dν) (∫ B dν) = ∫_t ∫_u A(u) B(u t) dν(u) dν(t)`.

This is the first step of Tate's proof of the local functional equation, where `A` and `B` are
the integrands of two local zeta integrals.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.4, Lemma 2.4.2.
-/

public section

open MeasureTheory Measure

namespace MeasureTheory

/-- **Correlation formula.** For a left-invariant s-finite measure `ν` on a group and integrable
`A`, `B`, `(∫ A) (∫ B) = ∫_t ∫_u A(u) B(u t)`: substitute `v = u t` in the double integral. -/
theorem integral_mul_integral_eq_integral_integral_mul {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] (ν : Measure G) [SFinite ν] [ν.IsMulLeftInvariant]
    {L : Type*} [RCLike L] {A B : G → L} (hA : Integrable A ν) (hB : Integrable B ν) :
    (∫ u, A u ∂ν) * (∫ v, B v ∂ν) = ∫ t, ∫ u, A u * B (u * t) ∂ν ∂ν := by
  have hmp := measurePreserving_prod_mul ν ν
  have he := (MeasurableEquiv.shearMulRight G).measurableEmbedding
  have hint : Integrable (fun z : G × G ↦ A z.1 * B z.2) (ν.prod ν) := hA.mul_prod hB
  rw [← integral_prod_mul, ← hmp.integral_comp he]
  exact integral_prod_symm _ ((hmp.integrable_comp_emb he).2 hint)

end MeasureTheory
