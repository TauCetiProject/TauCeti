/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.AbsoluteArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.UnitsLayer
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization

/-!
# The Artin map of a class formation on the units of a field

Let `F` be a class formation on the formation `unitsFormation K` of `(Kˢ)ˣ` over the absolute
Galois group `G_K = Gal(Kˢ/K)` of a field `K`. Its ground level is `Kˣ`, and its absolute Artin
map `ClassFormation.absoluteArtinMap` lands in `Gal(Kˢ/K)^ab`. Reading it through these
identifications gives the **Artin map of `F` on `Kˣ`**

```text
F.fieldArtinMap : Kˣ →* G_K^ab,
```

into `Field.absoluteGaloisGroupAbelianization K`, the topological abelianization of Mathlib's
absolute Galois group `Gal(AlgebraicClosure K/K)`. The comparison between the two closures is
`TauCeti.absoluteGaloisGroupRestrictEquiv`, restriction to the separable closure.

This is the common construction behind the nonarchimedean local Artin map
`TauCeti.ClassFieldTheory.artinMap` and the archimedean Artin maps
`TauCeti.ClassFieldTheory.infiniteArtinAt`; it uses no property of `K` or of `F`.

## Main definitions

* `TauCeti.ClassFieldTheory.ClassFormation.fieldArtinMap`: the Artin map `Kˣ →* G_K^ab` of a
  class formation on `unitsFormation K`.

## Main results

* `TauCeti.ClassFieldTheory.ClassFormation.fieldArtinMap_apply`: `F.fieldArtinMap` is the absolute
  Artin map of `F`, read on `Kˣ` and in `Gal(AlgebraicClosure K/K)^ab`.
* `TauCeti.ClassFieldTheory.ClassFormation.absoluteArtinMap_eq_of_mk_eq_fieldArtinMap`: a
  representative of `F.fieldArtinMap x` restricts to a representative of the absolute Artin symbol
  of `x`.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory.ClassFormation

variable {K : Type} [Field K] (F : ClassFormation (unitsFormation K))

/-- The **Artin map `Kˣ →* G_K^ab` of a class formation `F` on `unitsFormation K`**: the absolute
Artin map of `F` (`fieldArtinMap_apply`), read on `Kˣ` through the identification of the ground
level, and in the topological abelianization of Mathlib's absolute Galois group
`Gal(AlgebraicClosure K/K)`. -/
def fieldArtinMap : Kˣ →* Field.absoluteGaloisGroupAbelianization K :=
  (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr.toMonoidHom.comp
    (MonoidHom.toAdditive.symm
      (F.absoluteArtinMap.comp
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_toSubgroup_top_eq_fieldRange K)).toAddMonoidHom))

/-- **`F.fieldArtinMap` is the absolute Artin map of `F`**: the absolute Artin symbol of `x ∈ Kˣ`,
regarded as an element of the ground level `((Kˢ)ˣ)^{G_K}`, carried from `Gal(Kˢ/K)^ab` to
`Gal(AlgebraicClosure K/K)^ab`. -/
theorem fieldArtinMap_apply (x : Kˣ) :
    F.fieldArtinMap x = (absoluteGaloisGroupRestrictEquiv K).symm.topologicalAbelianizationCongr
      (F.absoluteArtinMap
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_toSubgroup_top_eq_fieldRange K)
          (Additive.ofMul x))).toMul := by
  rw [fieldArtinMap, MonoidHom.comp_apply, MonoidHom.toAdditive_symm_apply_apply]
  simp only [ContinuousMulEquiv.toMulEquiv_eq_coe, MulEquiv.toMonoidHom_eq_coe,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass,
    Function.comp_apply, MonoidHom.coe_ofClass, ContinuousMulEquiv.coe_toMulEquiv]

/-- If `σ ∈ Gal(AlgebraicClosure K/K)` represents `F.fieldArtinMap x`, then the absolute Artin
symbol of `x` for `F` is the class of the restriction of `σ` to the separable closure. -/
theorem absoluteArtinMap_eq_of_mk_eq_fieldArtinMap (x : Kˣ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = F.fieldArtinMap x) :
    F.absoluteArtinMap
        (unitsLevelEquiv (Algebra.ofId K (SeparableClosure K))
          (fixedField_toSubgroup_top_eq_fieldRange K)
          (Additive.ofMul x)) =
      Additive.ofMul ((absoluteGaloisGroupRestrictEquiv K σ : AbsoluteGaloisGroup K) :
        TopologicalAbelianization (AbsoluteGaloisGroup K)) := by
  rw [← ContinuousMulEquiv.topologicalAbelianizationCongr_mk, hσ, fieldArtinMap_apply,
    ← ContinuousMulEquiv.topologicalAbelianizationCongr_symm,
    ContinuousMulEquiv.apply_symm_apply, ofMul_toMul]

end TauCeti.ClassFieldTheory.ClassFormation
