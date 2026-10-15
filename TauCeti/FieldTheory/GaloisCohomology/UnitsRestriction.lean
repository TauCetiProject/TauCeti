/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Restriction with multiplicative coefficients along a field extension

Let `L/K` be an extension of fields and `σ : L →ₐ[K] Kˢ` a `K`-embedding into a separable closure.
The coefficient modules `(Kˢ)ˣ` of `G_K` and `(Lˢ)ˣ` of `G_L` are identified by the isomorphism of
separable closures `TauCeti.separableClosureRingEquiv K L σ`, and this identification is
equivariant along `G_L ≃ₜ* Gal(Kˢ/σ(L)) ≤ G_K` (`TauCeti.unitsCoeffMap_smul`). The two together
form a compatible pair, and this file names the map it induces,

```text
res : Hⁿ(G_K, (Kˢ)ˣ) → Hⁿ(G_L, (Lˢ)ˣ),
```

as `TauCeti.galoisResUnits`. `TauCeti.galoisRes` is restriction with trivial `𝔽₂` coefficients;
here the source and target coefficient modules are different and are matched by
`TauCeti.unitsCoeffMap`, so this is a separate map. In degree two it is restriction of Brauer
classes, read cohomologically. No finiteness of `L/K` is needed: the subgroup `Gal(Kˢ/σ(L))` is
used as a subgroup, not as an open subgroup.

## Main definitions

* `TauCeti.galoisResUnits`: restriction `Hⁿ(G_K, (Kˢ)ˣ) → Hⁿ(G_L, (Lˢ)ˣ)` along `σ`.

## Main results

* `TauCeti.galoisResUnits_def`: the defining compatible pair, along the composite
  `G_L ≃ Gal(Kˢ/σ(L)) ≤ G_K`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5,
  for restriction through the subgroup associated to an extension.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- **Restriction with multiplicative coefficients along `L/K`**, relative to the embedding
`σ : L →ₐ[K] Kˢ`: the map `Hⁿ(G_K, (Kˢ)ˣ) → Hⁿ(G_L, (Lˢ)ˣ)` induced by the composite
`G_L ≃ Gal(Kˢ/σ(L)) ≤ G_K` together with the identification `TauCeti.unitsCoeffMap` of the two
coefficient modules, equivariant by `TauCeti.unitsCoeffMap_smul`. -/
def galoisResUnits (n : ℕ) :
    continuousCohomology n (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) ⟶
      continuousCohomology n (ofDiscreteModule ℤ (AbsoluteGaloisGroup L) (UnitsCoeff L)) :=
  _root_.ContinuousCohomology.map
    ((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
      (absoluteGaloisGroupEquivFixingSubgroup K L σ :
        AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup))
    (ofDiscreteModulePair _ (unitsCoeffMap K L σ).toIntLinearMap (unitsCoeffMap_smul K L σ)) n

/-- The defining compatible pair of `TauCeti.galoisResUnits`. -/
theorem galoisResUnits_def (n : ℕ) :
    galoisResUnits K L σ n =
      _root_.ContinuousCohomology.map
        ((ContinuousMonoidHom.subgroupSubtype σ.fieldRange.fixingSubgroup).comp
          (absoluteGaloisGroupEquivFixingSubgroup K L σ :
            AbsoluteGaloisGroup L →ₜ* ↥σ.fieldRange.fixingSubgroup))
        (ofDiscreteModulePair _ (unitsCoeffMap K L σ).toIntLinearMap
          (unitsCoeffMap_smul K L σ)) n :=
  (rfl)

end TauCeti
