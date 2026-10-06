/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.Cyclotomic.CyclotomicCharacter
import TauCeti.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The cyclotomic character along a finite extension

Let `L/K` be a finite extension embedded in a separable closure `Kˢ` by `σ`. The absolute Galois
group `G_L` is identified with the open subgroup of `G_K` fixing `σ(L)`, and
`absoluteGaloisGroupExtend K L σ : G_L →* G_K` is the resulting embedding. Since `G_L` acts on the
roots of unity of `Lˢ = Kˢ` through this embedding, the `p`-adic cyclotomic character of `G_L` is
the restriction of that of `G_K`:

```text
χ_K (absoluteGaloisGroupExtend K L σ τ) = χ_L τ.
```

This is the comparison through which a statement about the cyclotomic character of `G_K`, such as
its value on the image of a local Artin symbol, passes to finite extensions of `K` by norm
functoriality.

The characters `localCyclotomicCharacter p K` are defined on Mathlib's absolute Galois group, at the
algebraic closure, while `absoluteGaloisGroupExtend` is built from separable closures. The
comparison therefore first computes the character at the separable closure
(`cyclotomicCharacter_absoluteGaloisGroupRestrictEquiv`). Both steps are instances of the
naturality of the cyclotomic character, `TauCeti.cyclotomicCharacter_eq_of_injective`. No
hypothesis on the characteristic is needed: when `p` is the characteristic, all characters
involved are trivial.

## Main results

* `TauCeti.cyclotomicCharacter_absoluteGaloisGroupRestrictEquiv`: the cyclotomic character of
  `G_K` may be computed on the separable closure.
* `TauCeti.localCyclotomicCharacter_absoluteGaloisGroupExtend`,
  `TauCeti.localCyclotomicCharacter_comp_absoluteGaloisGroupExtend`: the cyclotomic character of
  `G_L` is that of `G_K` read through `absoluteGaloisGroupExtend K L σ`.
-/

public section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K]

/-- **The cyclotomic character at the separable closure.** The cyclotomic character of
`g ∈ Gal(AlgebraicClosure K/K)` is that of its restriction to the separable closure. -/
@[simp]
theorem cyclotomicCharacter_absoluteGaloisGroupRestrictEquiv (g : Field.absoluteGaloisGroup K) :
    cyclotomicCharacter (SeparableClosure K) p
        (absoluteGaloisGroupRestrictEquiv K g : AbsoluteGaloisGroup K).toRingEquiv =
      localCyclotomicCharacter p K g := by
  rw [localCyclotomicCharacter_apply]
  -- The algebra map of the intermediate field `SeparableClosure K` is its coercion
  -- (`IntermediateField.algebraMap_apply`), so restriction intertwines the two automorphisms.
  exact (cyclotomicCharacter_eq_of_injective p
    (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective
    (fun x ↦ (coe_absoluteGaloisGroupRestrictEquiv_apply K g x).symm)
    fun H i ↦ let ⟨_, hζ⟩ := H i; hζ.exists_isPrimitiveRoot_of_isSepClosed K).symm

variable (L : Type*) [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)
  [FiniteDimensional K L]

/-- **The cyclotomic character along a finite extension.** For `L/K` finite embedded in `Kˢ` by
`σ`, the cyclotomic character of `τ ∈ G_L` is that of its image in `G_K`. -/
theorem localCyclotomicCharacter_absoluteGaloisGroupExtend (τ : Field.absoluteGaloisGroup L) :
    localCyclotomicCharacter p K (absoluteGaloisGroupExtend K L σ τ) =
      localCyclotomicCharacter p L τ := by
  rw [← cyclotomicCharacter_absoluteGaloisGroupRestrictEquiv,
    ← cyclotomicCharacter_absoluteGaloisGroupRestrictEquiv]
  exact cyclotomicCharacter_eq_of_injective p
    (f := (separableClosureRingEquiv K L σ).toRingHom) (separableClosureRingEquiv K L σ).injective
    (absoluteGaloisGroupExtend_apply_separableClosureRingEquiv K L σ τ)
    fun H i ↦ let ⟨ζ, hζ⟩ := H i
      ⟨_, hζ.map_of_injective (separableClosureRingEquiv K L σ).symm.injective⟩

/-- **The cyclotomic character of `G_L` is that of `G_K` read through
`absoluteGaloisGroupExtend K L σ`.** -/
@[simp]
theorem localCyclotomicCharacter_comp_absoluteGaloisGroupExtend :
    (localCyclotomicCharacter p K).comp (absoluteGaloisGroupExtend K L σ) =
      localCyclotomicCharacter p L :=
  MonoidHom.ext (localCyclotomicCharacter_absoluteGaloisGroupExtend p K L σ)

end TauCeti
