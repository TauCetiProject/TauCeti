/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Exact

/-!
# The short exact sequence of normal coinvariants

For a geometrically reduced affine group `G` of finite type over a field and a normal
closed subgroup `N`, the inclusion of coinvariants and restriction to `N` form the
coordinate Hopf algebra maps of a short exact sequence `1 → N → G → G/N → 1`.
The subgroup may be nonreduced, and the field need not be perfect.

This combines `faithfullyFlat_coinvariantsι`, `kernelHopfIdeal_coinvariantsι_eq`,
and `isShortExact_mkQuotient_kernelHopfIdeal`, without using fppf sheaves.
When the subgroup is finite and central, the quotient projection is a central isogeny
(`isCentralIsogeny_coinvariantsι`).

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
* J. S. Milne, *Algebraic Groups* (2017), §5.c.
-/

public section

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H]
  {I : HopfIdeal k H}

/-- The inclusion of normal coinvariants and restriction to the normal subgroup form
a short exact sequence of affine groups. The subgroup need not be reduced. -/
theorem isShortExact_coinvariantsι_mkQuotient (hI : I.IsNormal) :
    IsShortExact (coinvariantsι hI) (mkQuotient H I) := by
  have h := isShortExact_mkQuotient_kernelHopfIdeal
    (coinvariantsι hI) (faithfullyFlat_coinvariantsι hI)
  rw [kernelHopfIdeal_coinvariantsι_eq hI] at h
  exact h

/-- The projection from a geometrically reduced finite-type affine group to its quotient
by a finite central subgroup is a central isogeny. The subgroup may be nonreduced,
and the field need not be perfect. -/
theorem isCentralIsogeny_coinvariantsι (hI : I.IsCentral)
    (hfinite : Module.Finite k (H ⧸ I.toIdeal)) :
    IsCentralIsogeny (coinvariantsι hI.isNormal) := by
  have hseq := isShortExact_coinvariantsι_mkQuotient hI.isNormal
  have hisog := hseq.isIsogeny_iff_moduleFinite.mpr hfinite
  rw [isCentralIsogeny_iff]
  refine ⟨hisog.finite, hisog.faithfullyFlat, ?_⟩
  rw [kernelHopfIdeal_coinvariantsι_eq]
  exact hI

end TauCeti.CommHopfAlgCat
