/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.FaithfullyFlat
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Dimension

/-!
# Surjective homomorphisms of equal-dimensional abelian varieties

A surjective homomorphism between abelian varieties of equal dimension is an isogeny.
In particular a surjective endomorphism is an isogeny over any ground field.

## References

* J. S. Milne, *Abelian Varieties* (2022), §8, Proposition 8.1.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

/-- A surjective homomorphism between abelian varieties of the same dimension is an isogeny. -/
theorem isIsogeny_of_surjective_of_dim_eq {K : Type u} [Field K] {A B : AbelianVariety K}
    (f : A ⟶ B) [Surjective (Hom.toSchemeHom f)] (hdim : A.dim = B.dim) : IsIsogeny f := by
  let : A.toScheme.Over (Spec (.of K)) := ⟨A.toOver.hom⟩
  let : B.toScheme.Over (Spec (.of K)) := ⟨B.toOver.hom⟩
  have : (Hom.toSchemeHom f).IsOver (Spec (.of K)) := ⟨Hom.toSchemeHom_comp_hom f⟩
  have : LocallyOfFiniteType (B.toScheme ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType B.toOver.hom)
  have : IsProper (Hom.toSchemeHom f ≫ B.toOver.hom) := by
    rw [Hom.toSchemeHom_comp_hom]
    infer_instance
  have : IsProper (Hom.toSchemeHom f) := IsProper.of_comp _ B.toOver.hom
  have : Flat (Hom.toSchemeHom f) := flat_of_surjective f
  exact (isIsogeny_iff f).mpr
    ⟨(Hom.toSchemeHom f).isFinite_of_generalizingMap_of_topologicalKrullDim_eq K
      (Flat.generalizingMap _) hdim, inferInstance⟩

end TauCeti.AlgebraicGeometry.AbelianVariety
