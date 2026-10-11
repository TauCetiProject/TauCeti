/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Orientation
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Naturality of the cyclotomic character and of the cyclotomic orientation

For a field extension `L/K`, Mathlib's map `Field.absoluteGaloisGroup.mapOfAlgebra K L : G_L → G_K`
restricts automorphisms along an embedding `Kᵃˡᵍ → Lᵃˡᵍ` of algebraic closures. The embedding
identifies the `p`-power roots of unity of `Kᵃˡᵍ` with those of `Lᵃˡᵍ`, so the cyclotomic
character is natural:

```text
χ_K (mapOfAlgebra K L g) = χ_L g.
```

If `K` contains a primitive `p`th root of unity, so does `L`, and both maximal pro-`p` Galois
groups carry the cyclotomic orientation `cyclotomicOrientation`. A continuous homomorphism
`f : G_L → G_K` compatible with the two cyclotomic characters induces
`maximalProPQuotient.map f : G_L(p) → G_K(p)`, and the orientation of `G_K(p)` pulls back to that
of `G_L(p)` along it. This applies to `mapOfAlgebra K L` for an arbitrary extension, and to the
embedding `absoluteGaloisGroupExtend K L σ : G_L → G_K` of a finite extension.

For an isomorphism of fields `e : K ≃+* L`, the map of absolute Galois groups is an isomorphism
`absoluteGaloisGroupMapEquiv e : G_L ≃ₜ* G_K`, hence so is the induced map
`maximalProPQuotient.congr (absoluteGaloisGroupMapEquiv e) : G_L(p) ≃ₜ* G_K(p)`, and it carries
the cyclotomic orientation of `G_L(p)` to that of `G_K(p)`. A marked presentation of `G_K(p)`,
that is, an isomorphism `m : G_K(p) ≃ₜ* P` onto a presented group together with the values
`cyclotomicOrientation p K hmu (m.symm x)` on its generators, therefore transports to the marked
presentation `(maximalProPQuotient.congr (absoluteGaloisGroupMapEquiv e)).trans m` of `G_L(p)`
with the same values (`cyclotomicOrientation_maximalProPQuotient_congr_symm`). When `e` is an
isomorphism of finite extensions of `ℚ_p`, the degree and the number of `p`-power roots of unity,
which determine the relator, are also preserved (`LinearEquiv.finrank_eq`,
`localRootOfUnityOrder_eq_of_ringEquiv`).

## Main results

* `TauCeti.localCyclotomicCharacter_mapOfAlgebra`, `TauCeti.localCyclotomicCharacter_map`: the
  cyclotomic character of `G_L` is that of `G_K` read through the map of absolute Galois groups.
* `TauCeti.cyclotomicOrientation_maximalProPQuotient_map`: the cyclotomic orientation is natural
  along any continuous homomorphism of absolute Galois groups compatible with the cyclotomic
  characters.
* `TauCeti.cyclotomicOrientation_maximalProPQuotient_map_mapOfAlgebra`,
  `TauCeti.cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend`: its
  instances along an arbitrary extension and along a finite extension.
* `TauCeti.cyclotomicOrientation_maximalProPQuotient_congr`,
  `TauCeti.cyclotomicOrientation_maximalProPQuotient_congr_symm`: an isomorphism of fields induces
  an isomorphism of maximal pro-`p` Galois groups preserving the cyclotomic orientation.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-! ### The cyclotomic character -/

section Character

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- **The cyclotomic character along a field extension.** The cyclotomic character of
`g ∈ G_L` is that of its image `Field.absoluteGaloisGroup.mapOfAlgebra K L g` in `G_K`. -/
theorem localCyclotomicCharacter_mapOfAlgebra (g : Field.absoluteGaloisGroup L) :
    localCyclotomicCharacter p K (Field.absoluteGaloisGroup.mapOfAlgebra K L g) =
      localCyclotomicCharacter p L g := by
  rw [localCyclotomicCharacter_apply, localCyclotomicCharacter_apply]
  exact (cyclotomicCharacter_eq_of_injective p
    (algebraMap (AlgebraicClosure K) (AlgebraicClosure L)).injective
    (fun x ↦ (absoluteGaloisGroup_mapOfAlgebra_commutes K L g x).symm)
    fun H i ↦ let ⟨_, hζ⟩ := H i; hζ.exists_isPrimitiveRoot_of_isSepClosed K).symm

end Character

section Map

variable {K L : Type*} [Field K] [Field L]

/-- **The cyclotomic character along a field embedding** `f : K →+* L`: the cyclotomic character
of `g ∈ G_L` is that of its image `Field.absoluteGaloisGroup.map f g` in `G_K`. -/
theorem localCyclotomicCharacter_map (f : K →+* L) (g : Field.absoluteGaloisGroup L) :
    localCyclotomicCharacter p K (Field.absoluteGaloisGroup.map f g) =
      localCyclotomicCharacter p L g :=
  letI := f.toAlgebra
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) :=
    (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] AlgebraicClosure L).toAlgebra
  localCyclotomicCharacter_mapOfAlgebra p K L g

/-! ### The cyclotomic orientation -/

/-- **Naturality of the cyclotomic orientation.** If a continuous homomorphism
`f : G_L → G_K` intertwines the cyclotomic characters, then the cyclotomic orientation of `G_K(p)`
pulls back along the induced map `G_L(p) → G_K(p)` to the cyclotomic orientation of `G_L(p)`. -/
theorem cyclotomicOrientation_maximalProPQuotient_map (hmuK : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (hmuL : ∃ ζ : L, IsPrimitiveRoot ζ p)
    (f : Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup K) (hf : Continuous f)
    (hχ : ∀ g, localCyclotomicCharacter p K (f g) = localCyclotomicCharacter p L g)
    (x : absoluteGaloisGroupProP p L) :
    cyclotomicOrientation p K hmuK (maximalProPQuotient.map f hf x) =
      cyclotomicOrientation p L hmuL x := by
  induction x using QuotientGroup.induction_on with
  | H g => simp [hχ]

/-- **The cyclotomic orientation is preserved by an isomorphism of fields** `e : K ≃+* L`: the
induced isomorphism `G_L(p) ≃ₜ* G_K(p)` carries the cyclotomic orientation of `G_L(p)` to that of
`G_K(p)`. -/
@[simp]
theorem cyclotomicOrientation_maximalProPQuotient_congr (e : K ≃+* L)
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) (x : absoluteGaloisGroupProP p L) :
    cyclotomicOrientation p K hmu
        (maximalProPQuotient.congr (absoluteGaloisGroupMapEquiv e) x) =
      cyclotomicOrientation p L (hmu.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective e.injective⟩) x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [maximalProPQuotient.congr_mk, maximalProPQuotient.mk_apply, cyclotomicOrientation_mk,
      cyclotomicOrientation_mk, absoluteGaloisGroupMapEquiv_apply, localCyclotomicCharacter_map]

/-- **The cyclotomic orientation is preserved by an isomorphism of fields**, read through the
inverse of the induced isomorphism `G_L(p) ≃ₜ* G_K(p)`. This is the form in which the values of the
orientation on the generators of a marked presentation of `G_K(p)` transport to `G_L(p)`. -/
@[simp]
theorem cyclotomicOrientation_maximalProPQuotient_congr_symm (e : K ≃+* L)
    (hmu : ∃ ζ : L, IsPrimitiveRoot ζ p) (x : absoluteGaloisGroupProP p K) :
    cyclotomicOrientation p L hmu
        ((maximalProPQuotient.congr (absoluteGaloisGroupMapEquiv e)).symm x) =
      cyclotomicOrientation p K
        (hmu.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective e.symm.injective⟩) x := by
  rw [← cyclotomicOrientation_maximalProPQuotient_congr p e, ContinuousMulEquiv.apply_symm_apply]

end Map

section Extension

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- **The cyclotomic orientation along a field extension**: it pulls back along the map
`G_L(p) → G_K(p)` induced by `Field.absoluteGaloisGroup.mapOfAlgebra K L`. -/
@[simp]
theorem cyclotomicOrientation_maximalProPQuotient_map_mapOfAlgebra
    [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) (x : absoluteGaloisGroupProP p L) :
    cyclotomicOrientation p K hmu
        (maximalProPQuotient.map (Field.absoluteGaloisGroup.mapOfAlgebra K L)
          (Field.absoluteGaloisGroup.mapOfAlgebra K L).continuous x) =
      cyclotomicOrientation p L
        (hmu.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩) x :=
  cyclotomicOrientation_maximalProPQuotient_map p hmu _ _ _
    (localCyclotomicCharacter_mapOfAlgebra p K L) x

/-- **The cyclotomic orientation along a finite extension**: for `L/K` finite embedded in `Kˢ` by
`σ`, it pulls back along the map `G_L(p) → G_K(p)` induced by the embedding
`absoluteGaloisGroupExtend K L σ` of `G_L` into `G_K`. -/
@[simp]
theorem cyclotomicOrientation_maximalProPQuotient_map_absoluteGaloisGroupExtend
    [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
    (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) (x : absoluteGaloisGroupProP p L) :
    cyclotomicOrientation p K hmu
        (maximalProPQuotient.map (absoluteGaloisGroupExtend K L σ)
          (continuous_absoluteGaloisGroupExtend K L σ) x) =
      cyclotomicOrientation p L
        (hmu.elim fun _ hζ ↦ ⟨_, hζ.map_of_injective (algebraMap K L).injective⟩) x :=
  cyclotomicOrientation_maximalProPQuotient_map p hmu _ _ _
    (localCyclotomicCharacter_absoluteGaloisGroupExtend p K L σ) x

end Extension

end TauCeti
