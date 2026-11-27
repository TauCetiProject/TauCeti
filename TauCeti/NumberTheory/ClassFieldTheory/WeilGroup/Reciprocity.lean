/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.GeometricArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.ArtinMap
import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.ArtinMap
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Local reciprocity for the Weil group

Let `K` be a nonarchimedean local field of characteristic zero, for instance a finite extension of
`ℚ_p`. The local Artin map into the topological abelianization `W_K^ab = W_K / closure ⁅W_K, W_K⁆`
of the local Weil group is an isomorphism of topological groups

`localWeilArtinEquiv K : Kˣ ≃ₜ* W_K^ab`.

The map is `weilArtinMap K`, the absolute local Artin map `Kˣ → G_K^ab` with its image lifted
along the injection `W_K^ab → G_K^ab`. It is a continuous open surjection for every nonarchimedean
local field, and it is injective because the absolute local Artin map is, which in characteristic
zero is a consequence of local existence (`injective_artinMap`).

The target is the topological abelianization, the quotient of `W_K` by the closure of its
commutator subgroup. It agrees with the algebraic abelianization when the commutator subgroup is
closed; taking the closure makes the quotient Hausdorff without proving that.

In characteristic `p` the map `weilArtinMap K` is still a continuous open surjection, but its
injectivity would need the existence of the `p`-primary abelian extensions, so no isomorphism is
stated there.

Composing `localWeilArtinEquiv K` with inversion in `W_K^ab` gives the **geometric** normalization
`localWeilGeometricArtinEquiv K : Kˣ ≃ₜ* W_K^ab`, compatible with `geometricArtinMap K` and
sending uniformizers to classes of geometric Frobenius lifts (inverses of arithmetic Frobenius
lifts).

## Main definitions

* `TauCeti.ClassFieldTheory.localWeilArtinEquiv`: in characteristic zero, the isomorphism of
  topological groups `Kˣ ≃ₜ* W_K^ab` under the arithmetic Frobenius normalization.
* `TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv`: in characteristic zero, the isomorphism
  `Kˣ ≃ₜ* W_K^ab` under the geometric Frobenius normalization.

## Main results

* `TauCeti.ClassFieldTheory.injective_weilArtinMap`: in characteristic zero, the local Artin map
  `Kˣ → W_K^ab` is injective.
* `TauCeti.ClassFieldTheory.localWeilArtinEquiv_compat`: the class in `G_K^ab` of a Weil element
  representing `localWeilArtinEquiv K x` is the Artin symbol of `x`.
* `TauCeti.ClassFieldTheory.localWeilGeometricArtinEquiv_compat`: the class in `G_K^ab` of a Weil
  element representing `localWeilGeometricArtinEquiv K x` is `geometricArtinMap K x`.
* `isArithFrobeniusLift_inv_of_mk_eq_localWeilGeometricArtinEquiv_uniformizer`: every Weil
  representative of `localWeilGeometricArtinEquiv K π` for a uniformizer `π` maps to a geometric
  Frobenius in `G_K`.

## References

* A. Weil, *Sur la théorie du corps de classes*, J. Math. Soc. Japan 3 (1951).
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §1.4.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [CharZero K]

/-- In characteristic zero, the local Artin map into the abelianized Weil group is injective, as
the absolute local Artin map is (`injective_artinMap`). -/
theorem injective_weilArtinMap : Function.Injective (weilArtinMap K) :=
  fun x y h ↦ injective_artinMap K <| by
    simpa using congrArg (weilToAbsoluteAbelianization K) h

/-- **Local reciprocity for the Weil group.** For a nonarchimedean local field `K` of
characteristic zero, the local Artin map is an isomorphism of topological groups from `Kˣ` onto
the topological abelianization of the local Weil group (`localWeilArtinEquiv_apply`). -/
def localWeilArtinEquiv : Kˣ ≃ₜ* TopologicalAbelianization (WeilGroup K) :=
  .mk' ((Equiv.ofBijective _ ⟨injective_weilArtinMap K, surjective_weilArtinMap K⟩)
    |>.toHomeomorphOfContinuousOpen (continuous_weilArtinMap K) (isOpenMap_weilArtinMap K))
    (map_mul (weilArtinMap K))

/-- The isomorphism `Kˣ ≃ₜ* W_K^ab` is the local Artin map into the abelianized Weil group. -/
@[simp]
theorem localWeilArtinEquiv_apply (x : Kˣ) : localWeilArtinEquiv K x = weilArtinMap K x :=
  (rfl)

/-- **Compatibility with the absolute local Artin map.** If a Weil element `w` represents
`localWeilArtinEquiv K x` in `W_K^ab`, then its class in `G_K^ab` is the Artin symbol of `x`. -/
theorem localWeilArtinEquiv_compat (x : Kˣ) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilArtinEquiv K x) :
    (QuotientGroup.mk (weilToAbsolute K w) : Field.absoluteGaloisGroupAbelianization K) =
      artinMap K x := by
  rw [← weilToAbsoluteAbelianization_mk, hw, localWeilArtinEquiv_apply,
    weilToAbsoluteAbelianization_weilArtinMap]

/-- **Geometric local reciprocity for the Weil group.** For a characteristic-zero nonarchimedean
local field `K`, this is the isomorphism `Kˣ ≃ₜ* W_K^{ab}` obtained by composing
`localWeilArtinEquiv K` with inversion in the commutative group `W_K^{ab}`. It sends a uniformizer
to the class of a geometric Frobenius (the inverse of an arithmetic Frobenius lift). -/
def localWeilGeometricArtinEquiv : Kˣ ≃ₜ* TopologicalAbelianization (WeilGroup K) :=
  (localWeilArtinEquiv K).trans (ContinuousMulEquiv.inv (TopologicalAbelianization (WeilGroup K)))

/-- The geometric Weil reciprocity isomorphism sends `x` to `(localWeilArtinEquiv K x)⁻¹`. -/
@[simp]
theorem localWeilGeometricArtinEquiv_apply (x : Kˣ) :
    localWeilGeometricArtinEquiv K x = (localWeilArtinEquiv K x)⁻¹ := by
  simp [localWeilGeometricArtinEquiv]

/-- The inverse of `localWeilGeometricArtinEquiv K` sends `y` to
`((localWeilArtinEquiv K).symm y)⁻¹`. -/
@[simp]
theorem localWeilGeometricArtinEquiv_symm_apply
    (y : TopologicalAbelianization (WeilGroup K)) :
    (localWeilGeometricArtinEquiv K).symm y = ((localWeilArtinEquiv K).symm y)⁻¹ := by
  rw [localWeilGeometricArtinEquiv, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.inv_symm, ContinuousMulEquiv.inv_apply, map_inv]

/-- Mapping `localWeilGeometricArtinEquiv K x` into `G_K^{ab}` yields the geometric Artin symbol
`geometricArtinMap K x`. -/
theorem weilToAbsoluteAbelianization_localWeilGeometricArtinEquiv (x : Kˣ) :
    weilToAbsoluteAbelianization K (localWeilGeometricArtinEquiv K x) =
      geometricArtinMap K x := by
  rw [localWeilGeometricArtinEquiv_apply, map_inv, localWeilArtinEquiv_apply,
    weilToAbsoluteAbelianization_weilArtinMap, geometricArtinMap_apply]

/-- The abelianized Weil degree of `localWeilGeometricArtinEquiv K x` is
`(normalizedValuation K x)⁻¹`. -/
theorem weilDegreeAbelianization_localWeilGeometricArtinEquiv (x : Kˣ) :
    weilDegreeAbelianization K (localWeilGeometricArtinEquiv K x) =
      (normalizedValuation K x)⁻¹ := by
  rw [localWeilGeometricArtinEquiv_apply, map_inv, localWeilArtinEquiv_apply,
    weilDegreeAbelianization_weilArtinMap]

/-- **Compatibility with the absolute geometric Artin map.** If a Weil element `w` represents
`localWeilGeometricArtinEquiv K x`, then its class in `G_K^{ab}` is `geometricArtinMap K x`. -/
theorem localWeilGeometricArtinEquiv_compat (x : Kˣ) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K x) :
    (QuotientGroup.mk (weilToAbsolute K w) : Field.absoluteGaloisGroupAbelianization K) =
      geometricArtinMap K x := by
  rw [← weilToAbsoluteAbelianization_mk, hw,
    weilToAbsoluteAbelianization_localWeilGeometricArtinEquiv]

/-- **Geometric Frobenius normalization.** Every Weil element representing
`localWeilGeometricArtinEquiv K π` for a uniformizer `π` maps to a geometric Frobenius in `G_K`:
the inverse of its image is an arithmetic Frobenius lift. -/
theorem isArithFrobeniusLift_inv_of_mk_eq_localWeilGeometricArtinEquiv_uniformizer {π : Kˣ}
    (hπ : IsUniformizer K π) (w : WeilGroup K)
    (hw : (QuotientGroup.mk w : TopologicalAbelianization (WeilGroup K)) =
      localWeilGeometricArtinEquiv K π) :
    IsArithFrobeniusLift K (weilToAbsolute K w)⁻¹ :=
  isArithFrobeniusLift_inv_of_mk_eq_geometricArtinMap_uniformizer K hπ (weilToAbsolute K w)
    (localWeilGeometricArtinEquiv_compat K π w hw)

end TauCeti.ClassFieldTheory
