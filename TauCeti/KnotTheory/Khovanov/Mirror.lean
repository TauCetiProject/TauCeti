/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Cube.DualComplex
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.KnotTheory.Khovanov.Complex
public import TauCeti.KnotTheory.Khovanov.Resolution.Mirror

/-!
# The Khovanov complex of the mirror diagram is the dual complex

For a planar oriented PD-code `D`, the normalized Khovanov complex of the mirror `D.mirror` in
quantum degree `j` is isomorphic to the dual of the normalized Khovanov complex of `D` in
quantum degree `-j`, the cochain complex `Hom(C(D)_{-j}, R)` of linear maps into `R` placed in
degree `0` (`TauCeti.OrientedPDCode.khovanovComplexMirrorIso`). Its term in cochain degree `i` is
`Hom(C(D)^{-i}_{-j}, R)`, so the bidegree `(i, j)` of the mirror corresponds to `(-i, -j)`.

The isomorphism combines three identifications. The Frobenius pairing identifies the cube of
resolutions of the mirror with the dual cube of the cube of resolutions of `D`
(`TauCeti.PDCode.mirrorKhovanovBracketIso`). The totalization of a dual cube, shifted by
`b = n₊(D) = n₋(D.mirror)`, is the dual of the totalization shifted by `a = n₋(D)`, since
`a + b` is the number of crossings (`CategoryTheory.Functor.dualCubeComplexIso`). Finally the
normalized complexes are the native cochain shifts of the brackets by their negative crossing
counts (`TauCeti.OrientedPDCode.khovanovComplexShiftIso`). The resulting isomorphism respects the
differentials with all their signs; it is not merely an identification of ranks.

## Main definitions

* `TauCeti.OrientedPDCode.khovanovComplexMirrorIso D hD R j`: the isomorphism from the
  normalized Khovanov complex of `D.mirror` in quantum degree `j` to the dual of the normalized
  Khovanov complex of `D` in quantum degree `-j`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.
-/

public section

noncomputable section

open CategoryTheory CochainComplex Opposite

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]
  (j : ℤ)

/-- The quantum degree of the cube of `D` dual to the bracket degree of the mirror used in
quantum degree `j`. -/
private lemma mirror_cube_degree :
    (n : ℤ) - (j - D.mirror.positiveCrossingCount + 2 * D.mirror.negativeCrossingCount) =
      -j - D.positiveCrossingCount + 2 * D.negativeCrossingCount := by
  have := D.positiveCrossingCount_add_negativeCrossingCount
  simp only [positiveCrossingCount_mirror, negativeCrossingCount_mirror]
  omega

/-- The negative crossing counts of `D` and of its mirror add up to the number of crossings. -/
private lemma negativeCrossingCount_add_mirror :
    (D.negativeCrossingCount : ℤ) + D.mirror.negativeCrossingCount = Fintype.card (Fin n) := by
  have := D.positiveCrossingCount_add_negativeCrossingCount
  simp only [negativeCrossingCount_mirror, Fintype.card_fin]
  omega

/-- The brackets of equal codes agree. -/
private lemma khovanovBracket_congr {P Q : PDCode n} (e : P = Q) (hP : P.IsPlanar)
    (hQ : Q.IsPlanar) (k : ℤ) : P.khovanovBracket hP R k = Q.khovanovBracket hQ R k := by
  subst e
  rfl

/-- **The Khovanov complex of the mirror is the dual complex.** For a planar oriented code `D`,
the normalized Khovanov complex of `D.mirror` in quantum degree `j` is isomorphic to the dual
`Hom(C(D)_{-j}, R)` of the normalized Khovanov complex of `D` in quantum degree `-j`, the
`R`-linear Hom complex into `R` placed in degree `0`. In cochain degree `i` it pairs the states of
the mirror with `|S| - n₋(D.mirror) = i` with the complementary states of `D`, of cochain
degree `-i`, by the Frobenius pairing of their circle tensors, up to a sign depending on the state
and the degree. Any planarity proof `hD'` for the mirror may be used. -/
def khovanovComplexMirrorIso (hD' : D.mirror.toPDCode.IsPlanar) :
    D.mirror.khovanovComplex hD' R j ≅
      linearHomComplex R (D.khovanovComplex hD R (-j))
        ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
  D.mirror.khovanovComplexShiftIso hD' R j ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ)
      (D.mirror.negativeCrossingCount : ℤ)).mapIso
        (eqToIso (khovanovBracket_congr R (mirror_toPDCode D) hD'
          ((PDCode.isPlanar_mirror D.toPDCode).2 hD) _) ≪≫
          D.toPDCode.mirrorKhovanovBracketIso hD R _ ≪≫
          eqToIso (by rw [mirror_cube_degree])) ≪≫
    (D.toPDCode.resolutionCube hD R
      (-j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).dualCubeComplexIso
        (negativeCrossingCount_add_mirror D) ≪≫
    ((TauCeti.linearHomComplexFunctor R).mapIso
      (D.khovanovComplexShiftIso hD R (-j) ≪≫
        (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ)
          (D.negativeCrossingCount : ℤ)).mapIso
            (eqToIso (D.toPDCode.khovanovBracket_apply hD R _))).op).app
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

end TauCeti.OrientedPDCode
