/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Galois
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative

/-!
# The idele norm as a product of conjugates

Let `L / K` be a Galois extension of number fields. Extended back to `L`, the norm
`N_{L/K}(x)` of an idele `x` of `L` is the product of its Galois conjugates `σ x`
(`ideleExtension_ideleNormMap`), and the same holds for idele classes
(`ideleClassExtension_ideleClassNormMap`). This is the adele formula
`TauCeti.GlobalNumberFields.adeleExtension_adeleNorm` read on units.

More generally, for `L / K` not necessarily normal, a product formula `N_{L/K}(y) = ∏ i, σ i y`
for the elements of `L` in an extension `M`, with ring automorphisms `σ i` of `M`, gives the same
formula for the ideles of `L` extended to `M`
(`ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod`), by the adele formula
`TauCeti.GlobalNumberFields.adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod`.

## Main results

* `TauCeti.GlobalNumberFields.ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod`: a product
  formula for the norm of field elements transfers to ideles.
* `TauCeti.GlobalNumberFields.ideleExtension_ideleNormMap`: the idele norm, extended back to `L`,
  is the product of the Galois conjugates.
* `TauCeti.GlobalNumberFields.ideleClassExtension_ideleClassNormMap`: the same for idele classes.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

/-- **A product formula for the norm transfers to ideles.** Let `L/K` be an extension of number
fields and `M` an extension of both. If for some ring automorphisms `σ i` of `M` the norm
`N_{L/K}(y)` of every `y ∈ L`, read in `M`, is `∏ i, σ i y`, then extended to `M`, the idele norm
`N_{L/K}(x)` of an idele `x` of `L` is `∏ i, σ i x`. -/
theorem ideleExtension_ideleNormMap_of_algebraMap_norm_eq_prod (K L M : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L]
    [Algebra K M] [Algebra L M] {ι : Type*} [Fintype ι] (σ : ι → M ≃+* M)
    (hσ : ∀ y : L, algebraMap K M (Algebra.norm K y) = ∏ i, σ i (algebraMap L M y))
    (x : IdeleGroup (𝓞 L) L) :
    ideleExtension K M (ideleNormMap K L x) =
      ∏ i, Units.map (adeleEquiv M M (σ i)).toMonoidHom (ideleExtension L M x) := by
  apply Units.ext
  rw [coe_ideleExtension, coe_ideleNormMap,
    adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod K L M σ hσ, Units.coe_prod]
  simp only [Units.coe_map, coe_ideleExtension]
  -- `RingEquiv.toMonoidHom` is an abbreviation, with the same underlying function.
  rfl

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
