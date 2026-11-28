/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianVariety.Isogeny
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Basic
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsion.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Prime-to-characteristic multiplication on abelian varieties

For an abelian variety over a field, multiplication by an integer invertible in the field is
étale and an isogeny. Properness and quasi-finiteness give finiteness, and the nonempty image
is open and closed in a connected scheme, so the map is surjective. Its torsion scheme is
the fibre at the identity and is therefore finite étale over the ground field.

## References

* J. S. Milne, *Abelian Varieties* (2008), Chapter I, Proposition 7.1 and Theorem 7.2.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

namespace TauCeti.AlgebraicGeometry.AbelianVariety

universe u

variable {K : Type u} [Field K]

/-- Multiplication by an integer invertible in the ground field is étale. -/
theorem etale_mulBy_of_intCast_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    Etale (Hom.toSchemeHom (mulBy A n)) := by
  rw [Hom.toSchemeHom, toOverHom_mulBy]
  exact GroupScheme.etale_zpow_of_intCast_ne_zero (CommGrp.mk A.toOver) hn

/-- Multiplication by an integer invertible in the ground field is an isogeny. -/
theorem isIsogeny_mulBy_of_intCast_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    IsIsogeny (mulBy A n) := by
  let f := Hom.toSchemeHom (mulBy A n)
  have : Etale f := A.etale_mulBy_of_intCast_ne_zero hn
  have : IsProper (f ≫ A.toOver.hom) := by
    dsimp only [f]
    rw [Hom.toSchemeHom_comp_hom]
    infer_instance
  have : IsProper f := IsProper.of_comp f A.toOver.hom
  refine (isIsogeny_iff _).2 ⟨IsFinite.of_isProper_of_locallyQuasiFinite (f := f), ⟨?_⟩⟩
  exact Set.range_eq_univ.mp <|
    IsClopen.eq_univ ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
      (Set.range_nonempty _)

private theorem isPullback_torsionι_mulBy (A : AbelianVariety K) (n : ℤ) :
    IsPullback (GroupScheme.torsionι (CommGrp.mk A.toOver) n).left
      (GroupScheme.torsion (CommGrp.mk A.toOver) n).X.hom (Hom.toSchemeHom (mulBy A n))
      A.zeroSection := by
  rw [Hom.toSchemeHom, toOverHom_mulBy]
  exact (GroupScheme.isPullback_torsionι (CommGrp.mk A.toOver) n).map
    (Over.forget (Spec (.of K)))

/-- The scheme-theoretic `n`-torsion is finite over the field when `n` is invertible there. -/
theorem isFinite_torsion_of_intCast_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    IsFinite (GroupScheme.torsion (CommGrp.mk A.toOver) n).X.hom :=
  MorphismProperty.of_isPullback (A.isPullback_torsionι_mulBy n)
    (A.isIsogeny_mulBy_of_intCast_ne_zero hn).isFinite

/-- The scheme-theoretic `n`-torsion is étale over the field when `n` is invertible there. -/
theorem etale_torsion_of_intCast_ne_zero (A : AbelianVariety K) {n : ℤ} (hn : (n : K) ≠ 0) :
    Etale (GroupScheme.torsion (CommGrp.mk A.toOver) n).X.hom :=
  MorphismProperty.of_isPullback (A.isPullback_torsionι_mulBy n)
    (A.etale_mulBy_of_intCast_ne_zero hn)

end TauCeti.AlgebraicGeometry.AbelianVariety
