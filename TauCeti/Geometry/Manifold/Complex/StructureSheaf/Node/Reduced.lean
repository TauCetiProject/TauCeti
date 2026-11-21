/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Node.NormalForm
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Radical

/-!
# Reduced holomorphic node equations

Weierstrass division identifies a distinguished polynomial quotient with its holomorphic
germ quotient. Radicality can therefore be checked over the fraction field of the base
germ ring. The theorem `isRadical_span_nodeEquation` proves that `xy - s(b)` generates a
radical ideal for every holomorphic base germ `s`, even if `s` is zero or has a multiple zero.
The invertible change `x = u + v`, `y = u - v` gives the
quadratic normal form `u² - v² - s(b)` (`TauCeti.holomorphicStructureSheaf.nodeQuotientEquiv`).
The nonzero coefficient `v² + s(b)`, not the derivative of `s`, ensures reducedness. This is a
statement about the actual holomorphic germ quotient; no analytic-space category or
global-sections exactness is assumed.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II,
  for Weierstrass division and analytic hypersurface local rings.
-/

public noncomputable section

open Polynomial
open scoped Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The quadratic normal form of `xy = s(b)` has a radical defining ideal, including when
`s` is zero or has arbitrarily high vanishing order. Here `v` is the extra base coordinate
and `u` is the final vertical coordinate. -/
private theorem isRadical_span_nodeNormalForm [FiniteDimensional ℂ E] (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (Ideal.span {evalVertical (b, (0 : ℂ)) 0 (nodeNormalForm b s)}).IsRadical := by
  rw [nodeNormalForm_def]
  apply isRadical_span_evalVertical_X_pow_sub_C
  · apply (map_ne_zero_iff _ (evalVertical_injective b 0)).mpr
    exact (monic_X_pow_add_C s (by decide : 2 ≠ 0)).ne_zero
  · decide

/-- **All holomorphic node equations are reduced.** The ideal `(xy - s(b))` at `(b, 0, 0)`
is radical for every holomorphic base germ, including permanent nodes and singular total
spaces such as `xy = b²`. If `s(b) ≠ 0`, the equation is a unit and its ideal is the whole ring. -/
theorem isRadical_span_nodeEquation [FiniteDimensional ℂ E] (b : E)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk b) :
    (Ideal.span {nodeEquation b 0 0 s}).IsRadical := by
  have := (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_span_nodeNormalForm b s)
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr
    (isReduced_of_injective _ (nodeQuotientEquiv b s).injective)

end TauCeti.holomorphicStructureSheaf
