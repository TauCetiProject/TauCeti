/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.LocallyClosed
public import TauCeti.AlgebraicGeometry.Morphisms.Immersion

/-!
# Uniqueness of locally closed scheme images

A quasi-compact morphism with locally closed image has a canonical scheme image,
including its nilpotents. Any factorization as a surjective, scheme-theoretically
dominant morphism followed by an immersion identifies that intermediate scheme with
the canonical image. This characterization lets one compare locally closed scheme images
without choosing the same open and closed factorization of their immersions.

In particular, flat base change preserves these factorizations and hence gives the
field-extension comparisons for orbit schemes. Schematic dominance retains nonreduced
scheme structures.

## References

* The Stacks Project, Tag 01R5 (scheme-theoretic images and flat base change).
* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f (orbit schemes).
-/

public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)
  (h : IsLocallyClosed (Set.range f))

section Factorization

variable [QuasiCompact f]

/-- A surjective, schematically dominant factorization through an immersion identifies
its intermediate scheme with the locally closed scheme image. -/
def locallyClosedImageIsoOfFactorization (p : X ⟶ Z) (i : Z ⟶ Y)
    [Surjective p] [IsSchemeTheoreticallyDominant p] [IsImmersion i]
    (fac : p ≫ i = f) : f.locallyClosedImage h ≅ Z := by
  let ha := i.existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    (f.locallyClosedImageι h) (f.toLocallyClosedImage h) p
    (fac.trans (f.toLocallyClosedImage_locallyClosedImageι h).symm)
  let hb :=
    (f.locallyClosedImageι h).existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
      i p (f.toLocallyClosedImage h)
      ((f.toLocallyClosedImage_locallyClosedImageι h).trans fac.symm)
  exact ⟨ha.exists.choose, hb.exists.choose,
    (cancel_mono (f.locallyClosedImageι h)).mp (by
      simp [ha.exists.choose_spec, hb.exists.choose_spec]),
    (cancel_mono i).mp (by simp [ha.exists.choose_spec, hb.exists.choose_spec])⟩

/-- The comparison is over the original target. -/
@[reassoc (attr := simp)]
theorem locallyClosedImageIsoOfFactorization_hom_ι (p : X ⟶ Z) (i : Z ⟶ Y)
    [Surjective p] [IsSchemeTheoreticallyDominant p] [IsImmersion i]
    (fac : p ≫ i = f) :
    (f.locallyClosedImageIsoOfFactorization h p i fac).hom ≫ i =
      f.locallyClosedImageι h := by
  dsimp only [locallyClosedImageIsoOfFactorization]
  exact (i.existsUnique_lift_of_surjective_of_isSchemeTheoreticallyDominant
    (f.locallyClosedImageι h) (f.toLocallyClosedImage h) p
    (fac.trans (f.toLocallyClosedImage_locallyClosedImageι h).symm)).exists.choose_spec

/-- The inverse comparison also respects the immersion. -/
@[reassoc (attr := simp)]
theorem locallyClosedImageIsoOfFactorization_inv_ι (p : X ⟶ Z) (i : Z ⟶ Y)
    [Surjective p] [IsSchemeTheoreticallyDominant p] [IsImmersion i]
    (fac : p ≫ i = f) :
    (f.locallyClosedImageIsoOfFactorization h p i fac).inv ≫
      f.locallyClosedImageι h = i := by
  rw [Iso.inv_comp_eq, locallyClosedImageIsoOfFactorization_hom_ι]

/-- The comparison carries the canonical image factorization to the supplied one. -/
@[reassoc (attr := simp)]
theorem toLocallyClosedImage_isoOfFactorization_hom (p : X ⟶ Z) (i : Z ⟶ Y)
    [Surjective p] [IsSchemeTheoreticallyDominant p] [IsImmersion i]
    (fac : p ≫ i = f) :
    f.toLocallyClosedImage h ≫ (f.locallyClosedImageIsoOfFactorization h p i fac).hom = p := by
  apply (cancel_mono i).mp
  simp [fac]

end Factorization

end AlgebraicGeometry.Scheme.Hom
