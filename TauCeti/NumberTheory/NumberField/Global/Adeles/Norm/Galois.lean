/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Continuity

/-!
# The adele norm of a Galois extension

Let `L / K` be a Galois extension of number fields. The norm of `x ∈ L` is the product of its
Galois conjugates, `N_{L/K}(x) = ∏_σ σ x` (`Algebra.norm_eq_prod_automorphisms`). This file
proves the same formula for adeles: extended back to `L`, the adele norm `N_{L/K}(a)` of an adele
`a` of `L` is the product of the Galois conjugates `σ a` (`adeleExtension_adeleNorm`), and
likewise for finite and for infinite adeles separately.

Both sides are continuous and multiplicative in `a` and agree on the diagonal `L`, where the
formula is the one for field elements. The diagonal `L` is dense in the finite adeles of `L`
(strong approximation) and in the infinite adeles of `L` (weak approximation), so the two sides
agree on each factor. The formula for adeles follows by applying these two formulas to the
infinite and finite factors of `AdeleRing`.

This is what identifies the norm map of ideles with the norm of the Galois module of ideles, and
hence the norm of the idele-class formation with the norm map of idele classes.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleExtension_finiteAdeleNorm`: the finite adele norm,
  extended back to `L`, is the product of the Galois conjugates.
* `TauCeti.GlobalNumberFields.infiniteAdeleExtension_infiniteAdeleNorm`: the same for infinite
  adeles.
* `TauCeti.GlobalNumberFields.adeleExtension_adeleNorm`: the same for adeles.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The finite adele norm of a Galois extension is the product of the Galois conjugates**:
extended back to `L`, the norm of a finite adele `a` of `L` is `∏_σ σ a`. -/
theorem finiteAdeleExtension_finiteAdeleNorm (a : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleExtension (𝓞 K) K (𝓞 L) L (finiteAdeleNorm K L a) =
      ∏ σ : L ≃ₐ[K] L, finiteAdeleEquiv L L σ.toRingEquiv a := by
  -- Both sides are continuous in `a` and agree on the dense diagonal `L`.
  refine congrFun ((FiniteAdeleRing.denseRange_algebraMap (𝓞 L) L).equalizer
    ((continuous_finiteAdeleExtension (𝓞 K) K (𝓞 L) L).comp (continuous_finiteAdeleNorm K L))
    (continuous_finsetProd _ fun σ _ ↦ continuous_finiteAdeleEquiv L L σ.toRingEquiv)
    (funext fun x ↦ ?_)) a
  simp only [Function.comp_apply, finiteAdeleNorm_algebraMap, finiteAdeleExtension_algebraMap,
    finiteAdeleEquiv_algebraMap, Algebra.norm_eq_prod_automorphisms, map_prod,
    AlgEquiv.coe_toRingEquiv]

/-- **The infinite adele norm of a Galois extension is the product of the Galois conjugates**:
extended back to `L`, the norm of an infinite adele `a` of `L` is `∏_σ σ a`. -/
theorem infiniteAdeleExtension_infiniteAdeleNorm (a : InfiniteAdeleRing L) :
    infiniteAdeleExtension K L (infiniteAdeleNorm K L a) =
      ∏ σ : L ≃ₐ[K] L, infiniteAdeleEquiv L L σ.toRingEquiv a := by
  -- Both sides are continuous in `a` and agree on the dense diagonal `L`.
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap L).equalizer
    ((continuous_infiniteAdeleExtension K L).comp (continuous_infiniteAdeleNorm K L))
    (continuous_finsetProd _ fun σ _ ↦ continuous_infiniteAdeleEquiv L L σ.toRingEquiv)
    (funext fun x ↦ ?_)) a
  simp only [Function.comp_apply, infiniteAdeleNorm_algebraMap, infiniteAdeleExtension_algebraMap,
    infiniteAdeleEquiv_algebraMap, Algebra.norm_eq_prod_automorphisms, map_prod,
    AlgEquiv.coe_toRingEquiv]

/-- **The adele norm of a Galois extension is the product of the Galois conjugates**: extended
back to `L`, the norm of an adele `a` of `L` is `∏_σ σ a`. -/
theorem adeleExtension_adeleNorm (a : AdeleRing (𝓞 L) L) :
    adeleExtension (𝓞 K) K (𝓞 L) L (adeleNorm K L a) =
      ∏ σ : L ≃ₐ[K] L, adeleGaloisAction K L σ a := by
  -- Apply the infinite and finite formulas to the two factors. `AdeleRing` is a type synonym
  -- for the product, so its projections are `RingHom.fst` and `RingHom.snd`.
  refine Prod.ext ?_ ?_
  · rw [adeleExtension_fst, adeleNorm_fst, infiniteAdeleExtension_infiniteAdeleNorm]
    refine Eq.trans ?_ (map_prod (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
      (fun σ : L ≃ₐ[K] L ↦ adeleGaloisAction K L σ a) Finset.univ).symm
    refine Finset.prod_congr rfl fun σ _ ↦ ?_
    rw [adeleGaloisAction_apply]
    exact (adeleEquiv_fst L L σ.toRingEquiv a).symm
  · rw [adeleExtension_snd, adeleNorm_snd, finiteAdeleExtension_finiteAdeleNorm]
    refine Eq.trans ?_ (map_prod (RingHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
      (fun σ : L ≃ₐ[K] L ↦ adeleGaloisAction K L σ a) Finset.univ).symm
    refine Finset.prod_congr rfl fun σ _ ↦ ?_
    rw [adeleGaloisAction_apply]
    exact (adeleEquiv_snd L L σ.toRingEquiv a).symm

end TauCeti.GlobalNumberFields
