/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Galois
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative

/-!
# The idele norm of a Galois extension

Let `L / K` be a Galois extension of number fields. Extended back to `L`, the norm
`N_{L/K}(x)` of an idele `x` of `L` is the product of its Galois conjugates `σ x`
(`ideleExtension_ideleNormMap`), and the same holds for idele classes
(`ideleClassExtension_ideleClassNormMap`). This is the adele formula
`TauCeti.GlobalNumberFields.adeleExtension_adeleNorm` read on units.

## Main results

* `TauCeti.GlobalNumberFields.ideleExtension_ideleNormMap`: the idele norm, extended back to `L`,
  is the product of the Galois conjugates.
* `TauCeti.GlobalNumberFields.ideleClassExtension_ideleClassNormMap`: the same for idele classes.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The idele norm of a Galois extension is the product of the Galois conjugates**: extended
back to `L`, the norm of an idele `x` of `L` is `∏_σ σ x`. -/
theorem ideleExtension_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    ideleExtension K L (ideleNormMap K L x) =
      ∏ σ : L ≃ₐ[K] L, Units.map (adeleGaloisAction K L σ) x := by
  apply Units.ext
  rw [coe_ideleExtension, coe_ideleNormMap, adeleExtension_adeleNorm, Units.coe_prod]
  simp only [Units.coe_map, MonoidHom.coe_ofClass]

/-- **The idele-class norm of a Galois extension is the product of the Galois conjugates**:
extended back to `L`, the norm of the class of an idele `x` of `L` is the class of `∏_σ σ x`. -/
theorem ideleClassExtension_ideleClassNormMap (x : IdeleGroup (𝓞 L) L) :
    ideleClassExtension K L (ideleClassNormMap K L x) =
      ∏ σ : L ≃ₐ[K] L, ((Units.map (adeleGaloisAction K L σ) x : IdeleGroup (𝓞 L) L) :
        IdeleClassGroup (𝓞 L) L) := by
  rw [ideleClassNormMap_mk, ideleClassExtension_mk, ideleExtension_ideleNormMap,
    QuotientGroup.mk_prod]

end TauCeti.GlobalNumberFields
