/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.LeviForm
public import TauCeti.Geometry.Manifold.Morse.ScalarComposition
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Morse indices of reciprocal plurisubharmonic exhaustions

At a nondegenerate critical point of a strictly plurisubharmonic function ρ on a complex
n-manifold, the Morse index of `(1 + ρ)⁻¹` is at least n, provided `ρ ≠ -1` at that point.
Indeed, its index is `2n` minus the index of ρ, which is at most n.

Together with `TauCeti.IsMorse.inv_one_add` and preservation of critical points under scalar
reparametrization, this supplies the local high-index condition for reversed handle attachments
near a compactifying hyperplane. Properness, extension across that hyperplane and the handle
attachments themselves are separate topological questions.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 7.
-/

public section

open scoped Manifold

namespace TauCeti

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) 2 M] {f : M → ℝ} {x : M}

/-- The reciprocal of one plus a strictly plurisubharmonic function has index at least the
complex dimension at every nondegenerate critical point of the original function where the
denominator is nonzero.
The complementary-index formula is available in
`IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_inv_one_add_add_eq_finrank`. -/
theorem IsManifoldStrictlyPlurisubharmonicAt.le_manifoldMorseIndex_inv_one_add
    (h : IsManifoldStrictlyPlurisubharmonicAt E f x)
    (hc : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x) (hf : 1 + f x ≠ 0) :
    Module.finrank ℂ E ≤ manifoldMorseIndex 𝓘(ℝ, E) (fun y ↦ (1 + f y)⁻¹) x := by
  have hbound := h.manifoldMorseIndex_le hc.contMDiffAt
    (mvfderiv_eq_zero_iff.mp hc.mvfderiv_eq_zero)
  have hsum := hc.manifoldMorseIndex_inv_one_add_add_eq_finrank hf
  have hdim : Module.finrank ℝ E = 2 * Module.finrank ℂ E :=
    finrank_real_eq_two_mul_finrank_complex
  omega

end TauCeti
