/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Overlap

/-!
# Transitions between the overlap loci of analytic toric charts

The two overlap loci of a pair of cones are open subspaces of the two affine charts, and the
overlap homeomorphisms of `TauCeti.Toric.Fan.analyticOverlapHomeomorph` are homeomorphisms
between them. This file views each transition as a morphism of the overlap loci, so that the
`TopCat.GlueData` of the analytic fan can be built from the same transitions that are already
recorded on the analytic charts, and so that the inverse transitions are visibly morphisms too.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.6.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

variable (hΦ : Φ.IsRegular)

/-- The transition between the two overlap loci of two cones, as a morphism of spaces. -/
noncomputable def analyticOverlapTransition (σ τ : Φ.cones) :
    (Opens.toTopCat ((Φ.analyticAffineChartDiagram hΦ).obj σ)).obj
        (Φ.analyticOverlapOpens hΦ σ τ) ⟶
      (Opens.toTopCat ((Φ.analyticAffineChartDiagram hΦ).obj τ)).obj
        (Φ.analyticOverlapOpens hΦ τ σ) :=
  TopCat.ofHom ⟨(Φ.analyticOverlapHomeomorph hΦ σ τ).toFun,
    (Φ.analyticOverlapHomeomorph hΦ σ τ).continuous_toFun⟩

/-- The transition across the overlap of a cone with itself is the identity. -/
theorem analyticOverlapTransition_self (σ : Φ.cones) :
    ⇑(Φ.analyticOverlapTransition hΦ σ σ)
      = (id : Φ.analyticOverlapOpens hΦ σ σ → Φ.analyticOverlapOpens hΦ σ σ) := by
  funext x
  simp [analyticOverlapTransition]
  rfl

/-- A transition followed by the reverse transition is the identity on the first overlap
locus. -/
theorem analyticOverlapHomeomorph_trans_symm (σ τ : Φ.cones)
    (x : Φ.analyticOverlapOpens hΦ σ τ) :
    Φ.analyticOverlapHomeomorph hΦ τ σ (Φ.analyticOverlapHomeomorph hΦ σ τ x) = x := by
  rw [← Φ.analyticOverlapHomeomorph_symm hΦ σ τ]
  exact (Φ.analyticOverlapHomeomorph hΦ σ τ).symm_apply_apply x

end TauCeti.Toric.Fan
