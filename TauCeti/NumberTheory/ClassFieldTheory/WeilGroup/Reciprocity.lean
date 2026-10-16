/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.ArtinMap
import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.ArtinMap

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

## Main definitions

* `TauCeti.ClassFieldTheory.localWeilArtinEquiv`: in characteristic zero, the isomorphism of
  topological groups `Kˣ ≃ₜ* W_K^ab`.

## Main results

* `TauCeti.ClassFieldTheory.injective_weilArtinMap`: in characteristic zero, the local Artin map
  `Kˣ → W_K^ab` is injective.
* `TauCeti.ClassFieldTheory.localWeilArtinEquiv_compat`: the class in `G_K^ab` of a Weil element
  representing `localWeilArtinEquiv K x` is the Artin symbol of `x`.

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

end TauCeti.ClassFieldTheory
