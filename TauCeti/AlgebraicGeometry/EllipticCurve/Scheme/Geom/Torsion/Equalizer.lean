/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion.Unramified
import TauCeti.AlgebraicGeometry.EqualizerCarrier
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Torsion points of an elliptic curve agree on an open and closed subscheme

Let `E` be an elliptic curve over a scheme `S` and `n` an integer invertible in every residue
field of `S`. Two points `x y : Z ⟶ E` with values in some `Z` over `S`, both killed by
multiplication by `n`, agree on an open and closed subscheme of `Z`. The equalizer of `x` and `y`
is closed in `Z` because `E` is separated over `S` (Mathlib's
`isClosedImmersion_equalizer_ι_left`). It is open because `x` and `y` factor through the torsion
scheme `E[n]`, which is formally unramified and locally of finite type over `S`
(`EllipticCurveGeom.formallyUnramified_torsion_hom`), and the equalizer of two morphisms into
such a scheme is open (`isOpenImmersion_equalizer_ι_left`).

Applied to `[d]x` and the zero point, this makes each condition `[d]x = 0` open and closed
inside the closed locus where `[n]x = 0`. So the locus where a point is killed by `n`, and at no
point of `Z` by a proper divisor `d` of `n`, is open and closed in the locus where it is killed by
`n`. This is how the points of exact order `n` in every fibre are cut out of a family of elliptic
curves with a point, such as the universal Tate normal form, once `n` is inverted. Without the
invertibility of `n` the equalizer need not be open: over a field of characteristic `p`, the
zero section of `E[p]` is the equalizer of the inclusion `E[p] ⟶ E` and the zero point, and it
is not an open immersion, as the local ring of `E[p]` at the origin is not a field.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.range_equalizer_ι_left_one`: the equalizer of a
  point and the zero point is the set where the point meets the zero section.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOpenImmersion_equalizer_ι_left_of_mulBy_eq_one`:
  two points killed by `n` agree on an open subscheme.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isClopen_range_equalizer_ι_left_of_mulBy_eq_one`:
  the set where they agree is open and closed.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isOpenImmersion_equalizer_ι_comp_mulBy_left`: for
  any point `x`, the locus where `[d]x = 0` is open in the locus where `[n]x = 0`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S) {n : ℤ} {Z : Over S}

/-- **Where a point meets the zero section.** For a point `x` of `E` with values in `Z`, the image
of the equalizer of `x` and the zero point is the set of points of `Z` at which `x` meets the zero
section. -/
theorem range_equalizer_ι_left_one (x : Z ⟶ Over.mk E.structureMap) :
    Set.range (equalizer.ι x 1).left = {z | x.left z = E.zero (Z.hom z)} := by
  simpa using range_equalizer_ι_left_of_left_eq_hom_comp x 1 η[Over.mk E.structureMap] (by simp)

/-- **Torsion points agree on an open subscheme.** If the integer `n` is invertible in every
residue field of `S`, two points of `E` with values in `Z` which are killed by multiplication by
`n` agree on an open subscheme of `Z`: their equalizer is an open immersion into `Z`. It is also
a closed immersion, as for any two points of the separated scheme `E` over `S`. -/
theorem isOpenImmersion_equalizer_ι_left_of_mulBy_eq_one
    (hn : ∀ s : S, (n : S.residueField s) ≠ 0) {x y : Z ⟶ Over.mk E.structureMap}
    (hx : x ≫ E.mulBy n = 1) (hy : y ≫ E.mulBy n = 1) :
    IsOpenImmersion (equalizer.ι x y).left := by
  have := E.formallyUnramified_torsion_hom hn
  obtain ⟨x, rfl⟩ := (exists_comp_torsionι_iff x).mpr hx
  obtain ⟨y, rfl⟩ := (exists_comp_torsionι_iff y).mpr hy
  -- As `E[n] ⟶ E` is a monomorphism, the equalizer of the two points of `E` is the equalizer of
  -- the two points of `E[n]`, which is open since `E[n]` is unramified over `S`.
  let e := (isEqualizerCompMono (equalizerIsEqualizer x y) (E.torsionι n)).conePointUniqueUpToIso
    (equalizerIsEqualizer (x ≫ E.torsionι n) (y ≫ E.torsionι n))
  have he : e.hom ≫ equalizer.ι (x ≫ E.torsionι n) (y ≫ E.torsionι n) = equalizer.ι x y :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion e.hom.left,
    ← Over.comp_left, he]
  infer_instance

/-- **Torsion points agree on an open and closed set.** If the integer `n` is invertible in every
residue field of `S`, the set of points of `Z` over which two points of `E` with values in `Z`,
both killed by multiplication by `n`, agree is open and closed. -/
theorem isClopen_range_equalizer_ι_left_of_mulBy_eq_one
    (hn : ∀ s : S, (n : S.residueField s) ≠ 0) {x y : Z ⟶ Over.mk E.structureMap}
    (hx : x ≫ E.mulBy n = 1) (hy : y ≫ E.mulBy n = 1) :
    IsClopen (Set.range (equalizer.ι x y).left) := by
  have := E.isOpenImmersion_equalizer_ι_left_of_mulBy_eq_one hn hx hy
  -- instance search does not unfold `(Over.mk E.structureMap).hom` to `E.structureMap`
  have : IsSeparated (Over.mk E.structureMap).hom := inferInstanceAs (IsSeparated E.structureMap)
  exact ⟨(equalizer.ι x y).left.isClosedEmbedding.isClosed_range,
    (equalizer.ι x y).left.isOpenEmbedding.isOpen_range⟩

/-- **The killed-by-`d` locus is open in the killed-by-`n` locus.** Let `x` be any point of `E`
with values in `Z`, and let the integer `n` be invertible in every residue field of `S`. Inside
the closed subscheme of `Z` on which `[n]x = 0`, the closed subscheme on which moreover
`[d]x = 0` is open, for every integer `d`. -/
theorem isOpenImmersion_equalizer_ι_comp_mulBy_left
    (hn : ∀ s : S, (n : S.residueField s) ≠ 0) (x : Z ⟶ Over.mk E.structureMap) (d : ℤ) :
    IsOpenImmersion (equalizer.ι (equalizer.ι (x ≫ E.mulBy n) 1 ≫ x ≫ E.mulBy d) 1).left := by
  refine E.isOpenImmersion_equalizer_ι_left_of_mulBy_eq_one hn ?_ (by simp)
  -- `[n][d]x = [d][n]x` vanishes on the locus where `[n]x = 0`
  have h : (equalizer.ι (x ≫ E.mulBy n) 1 ≫ x) ^ n = 1 := by
    simpa [GrpObj.comp_zpow] using equalizer.condition (x ≫ E.mulBy n) 1
  simp only [comp_mulBy, Category.assoc]
  rw [← zpow_mul, mul_comm, zpow_mul, GrpObj.comp_zpow, GrpObj.comp_zpow, h, one_zpow]

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
