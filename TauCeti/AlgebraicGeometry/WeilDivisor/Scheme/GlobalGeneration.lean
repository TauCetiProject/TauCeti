/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Interpolation

/-!
# Generation of divisor sheaves at closed points

On a proper regular integral curve with exact constant field, global sections of `𝒪_X(D)`
generate at a closed point `y` as soon as `deg D - [κ(y) : k] > 2g - 2`. This statement allows
closed points of arbitrary residue degree. It follows from the surjectivity of the restriction
map to the residue skyscraper, using the nonvanishing criterion for line-bundle sections.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Corollary 3.2.
-/

public section

open CategoryTheory AlgebraicGeometry Order TopologicalSpace
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  (hdim : ∀ x : X, coheight x ≤ 1)
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)

include hF hk

/-- Global sections of a divisor sheaf generate at a closed point when the degree minus the
residue degree of that point exceeds the canonical degree. No rationality of the point is
assumed. -/
theorem exists_section_mem_nonvanishingLocus_of_high_degree (D : SchemeWeilDivisor X)
    (y : CodimensionOnePoint X)
    (hD : 2 * (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ) - 2 <
      relativeDegree (X ↘ Spec (.of k)) D - (X ↘ Spec (.of k)).residueDegree y) :
    letI : IsLocallyNoetherian X :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
    letI : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
    letI : IsNoetherian X := {}
    ∃ s : Γ((toInvertibleSheaf hdim D).obj, ⊤),
      (y : X) ∈ (toInvertibleSheaf hdim D).obj.nonvanishingLocus s := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := compactSpace_of_universallyClosed (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  let E := D - WeilDivisor.ofPoint y
  obtain ⟨g, hg⟩ := exists_orderAt_eq y (WeilDivisor.coeff E y + 1)
  rw [orderAt_apply] at hg
  let φ := toSkyscraperResidueField (Additive.toMul g) hg
  have hE : 2 * (finrank k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) : ℤ) - 2 <
      relativeDegree (X ↘ Spec (.of k)) E := by
    simpa only [E, map_sub, relativeDegree_ofPoint] using hD
  let a := (Scheme.skyscraperResidueFieldEquiv (y : X) (Opens.mem_top (y : X))).symm 1
  obtain ⟨s, hs⟩ := surjective_toSkyscraperResidueField_app_top_of_high_degree
    k hdim hF hk hg hE a
  have hI := (toInvertibleSheaf hdim (E + WeilDivisor.ofPoint y)).property
  rw [toInvertibleSheaf_obj] at hI
  have hne : φ.app ⊤ s ≠ 0 := by
    rw [hs]
    intro h
    have := congrArg (Scheme.skyscraperResidueFieldEquiv (y : X) (Opens.mem_top (y : X))) h
    simp [a] at this
  have hmem := mem_nonvanishingLocus_of_app_ne_zero
    (Opens.mem_top (y : X)) φ s hne
  have heq : E + WeilDivisor.ofPoint y = D := sub_add_cancel _ _
  let e : sheaf (E + WeilDivisor.ofPoint y) ≅ (toInvertibleSheaf hdim D).obj :=
    eqToIso (congrArg sheaf heq) ≪≫ (eqToIso (toInvertibleSheaf_obj hdim D)).symm
  refine ⟨e.hom.app ⊤ s, ?_⟩
  rwa [Scheme.Modules.nonvanishingLocus_hom_app]

end

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor
