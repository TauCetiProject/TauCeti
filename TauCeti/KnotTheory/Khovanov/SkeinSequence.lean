/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Resolution.Skein

/-!
# The skein long exact sequence of Khovanov homology

Let `D` be a planar oriented PD-code with `n + 1` crossings and `c` one of its crossings. Its two
resolutions at `c` are `D.toPDCode.resolveCrossing c true`, the `A`-smoothing (the `0`-face of the
cube), and `D.toPDCode.resolveCrossing c false`, the `B`-smoothing (the `1`-face). Unlike the
unnormalized complex, the normalized complex needs an orientation, and only one of the two
smoothings inherits the orientation of `D`. So this file takes arbitrary oriented codes `D₀` and
`D₁` whose underlying codes are these two resolutions: the unnormalized complex does not depend on
the orientations, and the sequence below is stated for every choice of them.

Writing `n₊` and `n₋` for the numbers of positive and negative crossings, set

* `a₀ = n₋(D) - n₋(D₀)` and `b₀ = n₊(D) - 2n₋(D) - n₊(D₀) + 2n₋(D₀)`,
* `a₁ = n₋(D) - n₋(D₁) - 1` and `b₁ = 1 + n₊(D) - 2n₋(D) - n₊(D₁) + 2n₋(D₁)`.

The skein triangle of the unnormalized complex (`TauCeti.PDCode.khovanovBracketSkeinTriangle`)
gives, in each quantum degree `j`, the long exact sequence

`⋯ ⟶ Khⁱ⁺ᵃ¹ʲ⁻ᵇ¹(D₁) ⟶ Khⁱʲ(D) ⟶ Khⁱ⁺ᵃ⁰ʲ⁻ᵇ⁰(D₀) ⟶ Khⁱ⁺¹⁺ᵃ¹ʲ⁻ᵇ¹(D₁) ⟶ ⋯`

of normalized Khovanov homology. The map out of `Kh(D₀)` is induced by the saddle map at `c`
(`TauCeti.OrientedPDCode.khovanovHomologySkeinδ_eq`). The other two maps come from the inclusion
of the `B`-face into the cube of `D` and the projection onto the `A`-face.

Each map takes bidegrees as explicit arguments together with hypotheses relating them, stated
through the cube heights `i + n₋` and the bracket quantum degrees `j - n₊ + 2n₋`: the maps between
`Kh(D)` and `Kh(D₀)` preserve both, the cube height of `D` exceeds that of `D₁` by one, the
connecting map preserves the cube height, and the bracket quantum degree of `D₁` is one less than
that of `D` and of `D₀`. These hypotheses are equivalent to the displayed shifts by `aᵣ` and `bᵣ`,
but leave the bidegrees free, so no index needs to be rewritten when the maps are composed.

## Main definitions

All in the namespace `TauCeti.OrientedPDCode`:

* `khovanovHomologySkeinι`: the map `Khⁱ⁺ᵃ¹ʲ⁻ᵇ¹(D₁) ⟶ Khⁱʲ(D)`.
* `khovanovHomologySkeinπ`: the map `Khⁱʲ(D) ⟶ Khⁱ⁺ᵃ⁰ʲ⁻ᵇ⁰(D₀)`.
* `khovanovHomologySkeinδ`: the map `Khⁱ⁺ᵃ⁰ʲ⁻ᵇ⁰(D₀) ⟶ Khⁱ⁺¹⁺ᵃ¹ʲ⁻ᵇ¹(D₁)` induced by the
  saddle map.

## Main results

* `khovanovHomologySkein_exact₂`: exactness at `Kh(D)`.
* `khovanovHomologySkein_exact₃`: exactness at `Kh(D₀)`.
* `khovanovHomologySkein_exact₁`: exactness at `Kh(D₁)`.
* `khovanovHomologySkeinδ_eq`: the map out of `Kh(D₀)` is the saddle map on the cohomology of
  the cube complexes.
* `khovanovHomologySkeinι_eq`, `khovanovHomologySkeinπ_eq`: the other two maps are the inclusion
  of the `B`-face and the projection onto the `A`-face of the mapping cone of the saddle map.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §3.4.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §3.1.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Pretriangulated

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode (n + 1)) (hD : D.toPDCode.IsPlanar) (c : Fin (n + 1))
  {D₀ D₁ : OrientedPDCode n} (h₀ : D₀.toPDCode = D.toPDCode.resolveCrossing c true)
  (h₁ : D₁.toPDCode = D.toPDCode.resolveCrossing c false) (R : Type u) [CommRing R]

/-- `Kh(D₀)` as the cohomology of the first object of the skein triangle, which is by definition
the cube complex of the `A`-resolution (`TauCeti.PDCode.khovanovBracketSkeinTriangle_obj₁`). -/
private def skeinIso₁ (i₀ j₀ J a : ℤ)
    (hJ : J = j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount)
    (ha : a = i₀ + D₀.negativeCrossingCount) :
    D₀.khovanovHomology (h₀ ▸ hD.resolveCrossing _ c true) R i₀ j₀ ≅
      (D.toPDCode.khovanovBracketSkeinTriangle c hD R J).obj₁.homology a :=
  D₀.khovanovHomologyIsoCubeComplexHomology _ R (hD.resolveCrossing _ c true) h₀ i₀ j₀ hJ ha

/-- `Kh(D₁)` as the cohomology of the second object of the skein triangle, which is by definition
the cube complex of the `B`-resolution (`TauCeti.PDCode.khovanovBracketSkeinTriangle_obj₂`). -/
private def skeinIso₂ (i₁ j₁ J a : ℤ)
    (hJ : J = j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1)
    (ha : a = i₁ + D₁.negativeCrossingCount) :
    D₁.khovanovHomology (h₁ ▸ hD.resolveCrossing _ c false) R i₁ j₁ ≅
      (D.toPDCode.khovanovBracketSkeinTriangle c hD R J).obj₂.homology a :=
  D₁.khovanovHomologyIsoCubeComplexHomology _ R (hD.resolveCrossing _ c false) h₁ i₁ j₁
    (k := J - 1) (by lia) ha

/-- `Khⁱʲ(D)` as the cohomology in degree `i + n₋ - 1` of the third object `⟦D⟧⟦1⟧` of the skein
triangle in bracket quantum degree `j - n₊ + 2n₋`
(`TauCeti.PDCode.khovanovBracketSkeinTriangle_obj₃`). -/
private def skeinIso₃ (i j : ℤ) :
    D.khovanovHomology hD R i j ≅
      (D.toPDCode.khovanovBracketSkeinTriangle c hD R
        (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj₃.homology
          (i + D.negativeCrossingCount - 1) :=
  D.khovanovHomologyBracketIso hD R i j ≪≫
    (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso 1
      (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia)).app _).symm

/-- The skein triangle becomes distinguished in the derived category. -/
private theorem khovanovBracketSkeinTriangle_distinguished_derived (J : ℤ)
    [HasDerivedCategory (ModuleCat.{u} R)] :
    DerivedCategory.Q.mapTriangle.obj (D.toPDCode.khovanovBracketSkeinTriangle c hD R J) ∈
      distTriang _ :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _
    (DerivedCategory.Q.mapTriangle.mapIso (D.toPDCode.khovanovBracketSkeinTriangleIso c hD R J))

/-- **The `B`-face map of the skein sequence**, `Khⁱ⁺ᵃ¹ʲ⁻ᵇ¹(D₁) ⟶ Khⁱʲ(D)`, where
`a₁ = n₋(D) - n₋(D₁) - 1` and `b₁ = 1 + n₊(D) - 2n₋(D) - n₊(D₁) + 2n₋(D₁)`. The hypotheses `hi`
and `hj` say `i₁ = i + a₁` and `j₁ = j - b₁`. It is induced by the inclusion of the cube of `D₁`
as the `B`-face of the cube of `D` at `c`, the second map of the skein triangle. -/
def khovanovHomologySkeinι (i j i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount + 1 = i + D.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    D₁.khovanovHomology (h₁ ▸ hD.resolveCrossing _ c false) R i₁ j₁ ⟶
      D.khovanovHomology hD R i j :=
  (D.skeinIso₂ hD c h₁ R i₁ j₁ _ _ hj.symm (by lia)).hom ≫
    homologyMap (D.toPDCode.khovanovBracketSkeinTriangle c hD R _).mor₂ _ ≫
    (D.skeinIso₃ hD c R i j).inv

/-- **The `A`-face map of the skein sequence**, `Khⁱʲ(D) ⟶ Khⁱ⁺ᵃ⁰ʲ⁻ᵇ⁰(D₀)`, where
`a₀ = n₋(D) - n₋(D₀)` and `b₀ = n₊(D) - 2n₋(D) - n₊(D₀) + 2n₋(D₀)`. The hypotheses `hi` and `hj`
say `i₀ = i + a₀` and `j₀ = j - b₀`. It is induced by the projection of the cube of `D` onto its
`A`-face at `c`, the third map of the skein triangle. -/
def khovanovHomologySkeinπ (i j i₀ j₀ : ℤ)
    (hi : i₀ + D₀.negativeCrossingCount = i + D.negativeCrossingCount)
    (hj : j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    D.khovanovHomology hD R i j ⟶
      D₀.khovanovHomology (h₀ ▸ hD.resolveCrossing _ c true) R i₀ j₀ :=
  (D.skeinIso₃ hD c R i j).hom ≫
    CochainComplex.homologyδOfTriangle _ _ (i + D.negativeCrossingCount) ≫
    (D.skeinIso₁ hD c h₀ R i₀ j₀ _ _ hj.symm hi.symm).inv

/-- **The connecting map of the skein sequence**, `Khⁱ⁺ᵃ⁰ʲ⁻ᵇ⁰(D₀) ⟶ Khⁱ⁺¹⁺ᵃ¹ʲ⁻ᵇ¹(D₁)`. The
hypotheses `hi` and `hj` say that the cube heights agree and that the bracket quantum degree of
`D₁` is one less than that of `D₀`. It is induced by the saddle map at `c` from the cube of `D₀`
to the cube of `D₁` (`TauCeti.OrientedPDCode.khovanovHomologySkeinδ_eq`), the first map of the
skein triangle. -/
def khovanovHomologySkeinδ (i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount = i₀ + D₀.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount) :
    D₀.khovanovHomology (h₀ ▸ hD.resolveCrossing _ c true) R i₀ j₀ ⟶
      D₁.khovanovHomology (h₁ ▸ hD.resolveCrossing _ c false) R i₁ j₁ :=
  (D.skeinIso₁ hD c h₀ R i₀ j₀ _ _ rfl rfl).hom ≫
    homologyMap (D.toPDCode.khovanovBracketSkeinTriangle c hD R _).mor₁ _ ≫
    (D.skeinIso₂ hD c h₁ R i₁ j₁ _ _ hj.symm hi.symm).inv

/-- The connecting map of the skein sequence, read through any bracket quantum degree `J` and cube
height `a` matching its source bidegree. This is `khovanovHomologySkeinδ_eq` with the cohomology
groups typed as those of the objects of the skein triangle, the form in which it composes with the
homology sequence of that triangle. -/
private theorem khovanovHomologySkeinδ_eq_skeinIso (i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount = i₀ + D₀.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount) (J a : ℤ)
    (hJ : J = j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount)
    (ha : a = i₀ + D₀.negativeCrossingCount) :
    D.khovanovHomologySkeinδ hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi hj =
      (D.skeinIso₁ hD c h₀ R i₀ j₀ J a hJ ha).hom ≫
        homologyMap (D.toPDCode.khovanovBracketSkeinTriangle c hD R J).mor₁ a ≫
        (D.skeinIso₂ hD c h₁ R i₁ j₁ J a (by lia) (by lia)).inv := by
  subst hJ ha
  rfl

/-- **The connecting map of the skein sequence is the saddle map.** Through the identifications
of Khovanov homology with the cohomology of the cube complexes of the two resolutions, at any
bracket quantum degree `J` and cube height `a` matching the source bidegree, the map
`Kh(D₀) ⟶ Kh(D₁)` is induced by the saddle map `TauCeti.PDCode.resolveCrossingSaddle` at `c`. -/
theorem khovanovHomologySkeinδ_eq (i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount = i₀ + D₀.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount) (J a : ℤ)
    (hJ : J = j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount)
    (ha : a = i₀ + D₀.negativeCrossingCount) :
    D.khovanovHomologySkeinδ hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi hj =
      (D₀.khovanovHomologyIsoCubeComplexHomology _ R (hD.resolveCrossing _ c true) h₀ i₀ j₀
          hJ ha).hom ≫
        homologyMap (NatTrans.cubeComplexMap (D.toPDCode.resolveCrossingSaddle c hD R J)) a ≫
        (D₁.khovanovHomologyIsoCubeComplexHomology _ R (hD.resolveCrossing _ c false) h₁ i₁ j₁
          (k := J - 1) (by lia) (by lia)).inv :=
  D.khovanovHomologySkeinδ_eq_skeinIso hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi hj J a hJ ha

/-- **The `B`-face map of the skein sequence is the inclusion of the `B`-face.** Through the
identifications of Khovanov homology with the cohomology of the cube complex of the `B`-resolution
and of the bracket of `D`, the map `Kh(D₁) ⟶ Kh(D)` is induced by the inclusion
`mappingCone.inr` of the cube complex of the `B`-resolution into the mapping cone of the saddle
map, identified with `⟦D⟧⟦1⟧` by `TauCeti.PDCode.khovanovBracketMappingConeIso`. -/
theorem khovanovHomologySkeinι_eq (i j i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount + 1 = i + D.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    D.khovanovHomologySkeinι hD c h₁ R i j i₁ j₁ hi hj =
      (D₁.khovanovHomologyIsoCubeComplexHomology _ R (hD.resolveCrossing _ c false) h₁ i₁ j₁
          (k := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount - 1)
          (a := i + D.negativeCrossingCount - 1) (by lia) (by lia)).hom ≫
        homologyMap (CochainComplex.mappingCone.inr (NatTrans.cubeComplexMap
            (D.toPDCode.resolveCrossingSaddle c hD R
              (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount))) ≫
          (D.toPDCode.khovanovBracketMappingConeIso c hD R
            (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).hom)
          (i + D.negativeCrossingCount - 1) ≫
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso 1
          (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia)).hom.app _ ≫
        (D.khovanovHomologyBracketIso hD R i j).inv :=
  (rfl)

/-- **The `A`-face map of the skein sequence is the projection onto the `A`-face.** Through the
identifications of Khovanov homology with the cohomology of the bracket of `D` and of the cube
complex of the `A`-resolution, the map `Kh(D) ⟶ Kh(D₀)` is induced by the third map of the
mapping cone triangle of the saddle map, which projects the mapping cone, identified with
`⟦D⟧⟦1⟧` by `TauCeti.PDCode.khovanovBracketMappingConeIso`, onto the shifted cube complex of the
`A`-resolution. -/
theorem khovanovHomologySkeinπ_eq (i j i₀ j₀ : ℤ)
    (hi : i₀ + D₀.negativeCrossingCount = i + D.negativeCrossingCount)
    (hj : j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    D.khovanovHomologySkeinπ hD c h₀ R i j i₀ j₀ hi hj =
      (D.khovanovHomologyBracketIso hD R i j).hom ≫
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso 1
          (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia)).inv.app _ ≫
        homologyMap ((D.toPDCode.khovanovBracketMappingConeIso c hD R
            (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).inv ≫
          (CochainComplex.mappingCone.triangle (NatTrans.cubeComplexMap
            (D.toPDCode.resolveCrossingSaddle c hD R
              (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)))).mor₃)
          (i + D.negativeCrossingCount - 1) ≫
        ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).shiftIso 1
          (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia)).hom.app _ ≫
        (D₀.khovanovHomologyIsoCubeComplexHomology _ R (hD.resolveCrossing _ c true) h₀ i₀ j₀
          (k := j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
          (a := i + D.negativeCrossingCount) hj.symm hi.symm).inv :=
  (rfl)

/-- The composite of the two maps of the skein sequence through `Kh(D)` vanishes. -/
@[reassoc (attr := simp)]
theorem khovanovHomologySkeinι_comp_khovanovHomologySkeinπ (i j i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount + 1 = i + D.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
    (hi' : i₀ + D₀.negativeCrossingCount = i + D.negativeCrossingCount)
    (hj' : j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    D.khovanovHomologySkeinι hD c h₁ R i j i₁ j₁ hi hj ≫
      D.khovanovHomologySkeinπ hD c h₀ R i j i₀ j₀ hi' hj' = 0 := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  simp only [khovanovHomologySkeinι, khovanovHomologySkeinπ, Category.assoc,
    Iso.inv_hom_id_assoc, CochainComplex.homologyMap_homologyδOfTriangle_assoc _
      (D.khovanovBracketSkeinTriangle_distinguished_derived hD c R _)
      (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia), zero_comp,
    comp_zero]

/-- The composite of the two maps of the skein sequence through `Kh(D₀)` vanishes. -/
@[reassoc (attr := simp)]
theorem khovanovHomologySkeinπ_comp_khovanovHomologySkeinδ (i j i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₀ + D₀.negativeCrossingCount = i + D.negativeCrossingCount)
    (hj : j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
    (hi' : i₁ + D₁.negativeCrossingCount = i₀ + D₀.negativeCrossingCount)
    (hj' : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount) :
    D.khovanovHomologySkeinπ hD c h₀ R i j i₀ j₀ hi hj ≫
      D.khovanovHomologySkeinδ hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi' hj' = 0 := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  rw [D.khovanovHomologySkeinδ_eq_skeinIso hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi' hj' _ _ hj.symm hi.symm]
  simp only [khovanovHomologySkeinπ, Category.assoc, Iso.inv_hom_id_assoc,
    CochainComplex.homologyδOfTriangle_homologyMap_assoc _
      (D.khovanovBracketSkeinTriangle_distinguished_derived hD c R _)
      (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia), zero_comp,
    comp_zero]

/-- The composite of the two maps of the skein sequence through `Kh(D₁)` vanishes. -/
@[reassoc (attr := simp)]
theorem khovanovHomologySkeinδ_comp_khovanovHomologySkeinι (i j i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount = i₀ + D₀.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount)
    (hi' : i₁ + D₁.negativeCrossingCount + 1 = i + D.negativeCrossingCount)
    (hj' : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    D.khovanovHomologySkeinδ hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi hj ≫
      D.khovanovHomologySkeinι hD c h₁ R i j i₁ j₁ hi' hj' = 0 := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  rw [D.khovanovHomologySkeinδ_eq_skeinIso hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi hj
    (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) (i + D.negativeCrossingCount - 1)
    (by lia) (by lia)]
  simp only [khovanovHomologySkeinι, Category.assoc, Iso.inv_hom_id_assoc,
    CochainComplex.homologyMap_comp_eq_zero_of_distTriang_assoc _
      (D.khovanovBracketSkeinTriangle_distinguished_derived hD c R _), zero_comp, comp_zero]

/-- **Exactness of the skein sequence at `Kh(D)`.** -/
theorem khovanovHomologySkein_exact₂ (i j i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount + 1 = i + D.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
    (hi' : i₀ + D₀.negativeCrossingCount = i + D.negativeCrossingCount)
    (hj' : j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    (ShortComplex.mk _ _ (D.khovanovHomologySkeinι_comp_khovanovHomologySkeinπ hD c h₀ h₁ R
      i j i₀ j₀ i₁ j₁ hi hj hi' hj')).Exact := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk
    (D.skeinIso₂ hD c h₁ R i₁ j₁ _ _ hj.symm (by lia)).symm (D.skeinIso₃ hD c R i j).symm
    (D.skeinIso₁ hD c h₀ R i₀ j₀ _ _ hj'.symm hi'.symm).symm
    (by simp [khovanovHomologySkeinι]) (by simp [khovanovHomologySkeinπ]))
    (CochainComplex.homologyMap_exact₃_of_distTriang _
      (D.khovanovBracketSkeinTriangle_distinguished_derived hD c R _)
      (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia))

/-- **Exactness of the skein sequence at `Kh(D₀)`.** -/
theorem khovanovHomologySkein_exact₃ (i j i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₀ + D₀.negativeCrossingCount = i + D.negativeCrossingCount)
    (hj : j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
    (hi' : i₁ + D₁.negativeCrossingCount = i₀ + D₀.negativeCrossingCount)
    (hj' : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount) :
    (ShortComplex.mk _ _ (D.khovanovHomologySkeinπ_comp_khovanovHomologySkeinδ hD c h₀ h₁ R
      i j i₀ j₀ i₁ j₁ hi hj hi' hj')).Exact := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk (D.skeinIso₃ hD c R i j).symm
    (D.skeinIso₁ hD c h₀ R i₀ j₀ _ _ hj.symm hi.symm).symm
    (D.skeinIso₂ hD c h₁ R i₁ j₁ _ _ (by lia) (by lia)).symm
    (by simp [khovanovHomologySkeinπ])
    (by simp [D.khovanovHomologySkeinδ_eq_skeinIso hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi' hj' _ _
      hj.symm hi.symm]))
    (CochainComplex.homologyMap_exact₁_of_distTriang _
      (D.khovanovBracketSkeinTriangle_distinguished_derived hD c R _)
      (i + D.negativeCrossingCount - 1) (i + D.negativeCrossingCount) (by lia))

/-- **Exactness of the skein sequence at `Kh(D₁)`.** -/
theorem khovanovHomologySkein_exact₁ (i j i₀ j₀ i₁ j₁ : ℤ)
    (hi : i₁ + D₁.negativeCrossingCount = i₀ + D₀.negativeCrossingCount)
    (hj : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j₀ - D₀.positiveCrossingCount + 2 * D₀.negativeCrossingCount)
    (hi' : i₁ + D₁.negativeCrossingCount + 1 = i + D.negativeCrossingCount)
    (hj' : j₁ - D₁.positiveCrossingCount + 2 * D₁.negativeCrossingCount + 1 =
      j - D.positiveCrossingCount + 2 * D.negativeCrossingCount) :
    (ShortComplex.mk _ _ (D.khovanovHomologySkeinδ_comp_khovanovHomologySkeinι hD c h₀ h₁ R
      i j i₀ j₀ i₁ j₁ hi hj hi' hj')).Exact := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk
    (D.skeinIso₁ hD c h₀ R i₀ j₀ _ (i + D.negativeCrossingCount - 1) (by lia) (by lia)).symm
    (D.skeinIso₂ hD c h₁ R i₁ j₁ _ _ hj'.symm (by lia)).symm (D.skeinIso₃ hD c R i j).symm
    (by simp [D.khovanovHomologySkeinδ_eq_skeinIso hD c h₀ h₁ R i₀ j₀ i₁ j₁ hi hj
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (i + D.negativeCrossingCount - 1) (by lia) (by lia)])
    (by simp [khovanovHomologySkeinι]))
    (CochainComplex.homologyMap_exact₂_of_distTriang _
      (D.khovanovBracketSkeinTriangle_distinguished_derived hD c R _) _)

end TauCeti.OrientedPDCode
