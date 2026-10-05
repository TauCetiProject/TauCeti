/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Restriction with multiplicative coefficients across a finite extension

Let `L/K` be a finite extension of fields and `σ : L →ₐ[K] Kˢ` a `K`-embedding into a separable
closure. The coefficient modules `(Kˢ)ˣ` of `G_K` and `(Lˢ)ˣ` of `G_L` are identified by the
isomorphism of separable closures `TauCeti.separableClosureRingEquiv K L σ`, and this
identification is equivariant along `G_L ≃ₜ* galoisSubgroup K L σ ≤ G_K`
(`TauCeti.unitsCoeffMap_smul`). The two together form a compatible pair, and this file names the
map it induces,

```text
res : Hⁿ(G_K, (Kˢ)ˣ) → Hⁿ(G_L, (Lˢ)ˣ),
```

as `TauCeti.resHUnits`. The two coefficient modules have the same underlying group but are
coefficient objects over different groups, so this is not an instance of `TauCeti.galoisRes`,
which is restriction with trivial `𝔽₂` coefficients; in degree two it is restriction of Brauer
classes, read cohomologically.

## Main definitions

* `TauCeti.resHUnits`: restriction `Hⁿ(G_K, (Kˢ)ˣ) → Hⁿ(G_L, (Lˢ)ˣ)` along `σ`.

## Main results

* `TauCeti.unitsCoeffMap_galoisSubgroupEquiv_smul`: the identification of the coefficient modules
  is equivariant along `G_L ≃ galoisSubgroup K L σ`.
* `TauCeti.resHUnits_def`: the defining compatible pair, along the composite
  `G_L ≃ galoisSubgroup K L σ ≤ G_K` that `TauCeti.galoisRes_eq_map` uses for `𝔽₂` coefficients.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5,
  for restriction through the open subgroup associated to a finite extension.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- **The units of `Kˢ` as units of `Lˢ` form a compatible pair** along the composite
`G_L ≃ galoisSubgroup K L σ ≤ G_K`: an automorphism `g` of `Lˢ` over `L` acts on `(Kˢ)ˣ` through
its image in `G_K`. This is `TauCeti.unitsCoeffMap_smul` read along `galoisSubgroupEquiv`. -/
theorem unitsCoeffMap_galoisSubgroupEquiv_smul (g : AbsoluteGaloisGroup L) (x : UnitsCoeff K) :
    unitsCoeffMap K L σ ((galoisSubgroupEquiv K L σ g : AbsoluteGaloisGroup K) • x) =
      g • unitsCoeffMap K L σ x := by
  refine Additive.toMul.injective ?_
  rw [toMul_unitsCoeffMap, Additive.toMul_smul, Additive.toMul_smul, toMul_unitsCoeffMap]
  exact Units.ext (by simp)

/-- **Restriction with multiplicative coefficients along `L/K`**, relative to the embedding
`σ : L →ₐ[K] Kˢ`: the map `Hⁿ(G_K, (Kˢ)ˣ) → Hⁿ(G_L, (Lˢ)ˣ)` induced by the composite
`G_L ≃ galoisSubgroup K L σ ≤ G_K` together with the identification `TauCeti.unitsCoeffMap` of
the two coefficient modules. -/
def resHUnits (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) ⟶
      continuousCohomology n (ofDiscreteModule ℤ (AbsoluteGaloisGroup L) (UnitsCoeff L)) :=
  _root_.ContinuousCohomology.map
    ((ContinuousMonoidHom.subgroupSubtype (galoisSubgroup K L σ).toSubgroup).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L σ)))
    (ofDiscreteModulePair _ (unitsCoeffMap K L σ).toIntLinearMap
      (unitsCoeffMap_galoisSubgroupEquiv_smul K L σ)) n

/-- The defining compatible pair of `TauCeti.resHUnits`. -/
theorem resHUnits_def (n : ℕ) :
    resHUnits K L σ n =
      _root_.ContinuousCohomology.map
        ((ContinuousMonoidHom.subgroupSubtype (galoisSubgroup K L σ).toSubgroup).comp
          (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L σ)))
        (ofDiscreteModulePair _ (unitsCoeffMap K L σ).toIntLinearMap
          (unitsCoeffMap_galoisSubgroupEquiv_smul K L σ)) n :=
  (rfl)

end TauCeti
