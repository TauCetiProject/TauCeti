/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Retraction
public import TauCeti.Geometry.Manifold.Boundary.Collar.Topological

/-!
# The interior of a manifold with compact boundary is homotopy equivalent to the manifold

If `c : N × [0, 1) → M` is a collar of `f : N → M` with `N` compact and `M` Hausdorff, the
inclusion of the complement `M \ f(N)` into `M` is a homotopy equivalence
(`TauCeti.IsCollar.complHomotopyEquiv`, whose homotopy inverse pushes the collar inward).
Applied to the topological collar of a compact boundary of a manifold
(`TauCeti.isCollared_subtypeVal_boundary`), this shows that the inclusion of the interior of a
Hausdorff charted space over the half-space `𝓡∂ (n + 1)` with compact boundary is a homotopy
equivalence (`TauCeti.interiorHomotopyEquiv`). This is the compact-boundary case of the
homotopy-equivalence part of J. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 9.26,
there proved with a smooth collar; only a topological collar is needed.

## Main definitions

* `TauCeti.interiorHomotopyEquiv`: the inclusion of the interior of a Hausdorff charted space over
  the half-space with compact boundary, as a homotopy equivalence.

## Main results

* `TauCeti.coe_interiorHomotopyEquiv`: the homotopy equivalence is the inclusion.

## References

* J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013), Theorem 9.26.
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [T2Space M]

/-- **The interior of a manifold with compact boundary is homotopy equivalent to the manifold.**
For a Hausdorff charted space `M` over the half-space `𝓡∂ (n + 1)` whose boundary is compact, the
inclusion of the interior into `M` is a homotopy equivalence. The homotopy inverse pushes `M` off
its boundary along a topological collar (`TauCeti.isCollared_subtypeVal_boundary`). -/
def interiorHomotopyEquiv (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ContinuousMap.HomotopyEquiv ((𝓡∂ (n + 1)).interior M) M :=
  have := isCompact_iff_compactSpace.1 hK
  (Homeomorph.setCongr (by rw [Subtype.range_coe, ModelWithCorners.compl_boundary] :
      (𝓡∂ (n + 1)).interior M = (range ((↑) : (𝓡∂ (n + 1)).boundary M → M))ᶜ)).toHomotopyEquiv
    |>.trans (isCollared_iff.1 (isCollared_subtypeVal_boundary hK)).choose_spec.complHomotopyEquiv

/-- The homotopy equivalence between the interior of a manifold with compact boundary and the
manifold is the inclusion. -/
@[simp]
theorem coe_interiorHomotopyEquiv (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ⇑(interiorHomotopyEquiv hK) = Subtype.val := by
  funext x
  simp only [interiorHomotopyEquiv, ContinuousMap.HomotopyEquiv.trans_apply,
    IsCollar.coe_complHomotopyEquiv]
  -- `Homeomorph.setCongr` is the identity on underlying points, and has no `coe` simp lemma.
  rfl

end TauCeti
