/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.Topology.Sheaves.Exact

/-!
# Exactness of module sheaves on an open basis

A short complex of module sheaves is exact if it is exact on sections over every member of an
open basis. Applied to the affine basis, this detects exactness of a complex in any degree from
the global sections of its restrictions to affine opens. The converse need not hold, since
taking sections is only left exact.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Exactness on sections over an open basis implies exactness of a short complex of module
sheaves. -/
theorem _root_.CategoryTheory.ShortComplex.exact_of_isBasis_sectionsFunctor
    (S : ShortComplex X.Modules) {B : Set X.Opens}
    (hB : TopologicalSpace.Opens.IsBasis B)
    (h : ∀ U ∈ B, (S.map (Scheme.Modules.sectionsFunctor U)).Exact) : S.Exact := by
  refine (toSheaf X).reflects_exact_of_faithful _
    (TopCat.Sheaf.exact_of_isBasis hB ?_)
  intro U hU
  exact (ShortComplex.moduleCat_exact_iff _).1 (h U hU)

/-- Exactness of a complex of module sheaves in degree `j` follows from exactness in degree `j`
of the global sections of its restrictions to all affine opens. -/
theorem exactAt_of_forall_isAffineOpen (F : CochainComplex X.Modules ℤ) (j : ℤ)
    (h : ∀ U : X.Opens, IsAffineOpen U →
      (((Scheme.Modules.sectionsFunctor (⊤ : U.toScheme.Opens)).mapHomologicalComplex _).obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex _).obj F)).ExactAt j) :
    F.ExactAt j := by
  rw [HomologicalComplex.exactAt_iff]
  apply (F.sc j).exact_of_isBasis_sectionsFunctor X.isBasis_affineOpens
  intro U hU
  have h' := h U hU
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at h'
  rw [ShortComplex.moduleCat_exact_iff]
  -- Sections of the restriction over top are sections over the image of top, with the same maps.
  change ∀ s, (F.sc j).g.app U s = 0 → ∃ t, (F.sc j).f.app U t = s
  change ∀ s, (F.sc j).g.app (U.ι ''ᵁ ⊤) s = 0 →
    ∃ t, (F.sc j).f.app (U.ι ''ᵁ ⊤) t = s at h'
  rwa [Scheme.Opens.ι_image_top] at h'

end TauCeti.AlgebraicGeometry.Scheme.Modules
