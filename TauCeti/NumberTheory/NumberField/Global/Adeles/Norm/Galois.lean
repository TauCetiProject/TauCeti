/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Norm.Continuity

/-!
# The adele norm as a product of conjugates

Let `L / K` be a Galois extension of number fields. The norm of `x ∈ L` is the product of its
Galois conjugates, `N_{L/K}(x) = ∏_σ σ x` (`Algebra.norm_eq_prod_automorphisms`). This file
proves the same formula for adeles: extended back to `L`, the adele norm `N_{L/K}(a)` of an adele
`a` of `L` is the product of the Galois conjugates `σ a` (`adeleExtension_adeleNorm`), and
likewise for finite and for infinite adeles separately.

The formula is an instance of a transfer principle, which does not need `L / K` to be normal. Let
`M` be an extension of both `K` and `L`, and `σ i` finitely many ring automorphisms of `M` such
that `N_{L/K}(x) = ∏ i, σ i x` in `M` for every `x ∈ L`; for instance `M` Galois over `K` and the
`σ i` representatives of the cosets of `Gal(M/L)` in `Gal(M/K)`. Then the adele norm satisfies
the same formula: extended to `M`, `N_{L/K}(a) = ∏ i, σ i a`
(`adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod`). Both sides are continuous and
multiplicative in `a` and agree on the diagonal `L`, by hypothesis. The diagonal `L` is dense in
the finite adeles of `L` (strong approximation) and in the infinite adeles of `L` (weak
approximation), so the two sides agree on each factor, and on the adeles.

This is what identifies the norm map of ideles with the norm of the Galois module of ideles, and
hence the norms between the levels of the idele-class formation with the norm maps of idele
classes.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleExtension_finiteAdeleNorm_of_algebraMap_norm_eq_prod`,
  `TauCeti.GlobalNumberFields.infiniteAdeleExtension_infiniteAdeleNorm_of_algebraMap_norm_eq_prod`,
  `TauCeti.GlobalNumberFields.adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod`: a product
  formula for the norm of field elements transfers to finite adeles, infinite adeles and adeles.
* `TauCeti.GlobalNumberFields.finiteAdeleExtension_finiteAdeleNorm`: the finite adele norm of a
  Galois extension, extended back to `L`, is the product of the Galois conjugates.
* `TauCeti.GlobalNumberFields.infiniteAdeleExtension_infiniteAdeleNorm`: the same for infinite
  adeles.
* `TauCeti.GlobalNumberFields.adeleExtension_adeleNorm`: the same for adeles.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.GlobalNumberFields

section Transfer

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]

/-- **A product formula for the norm transfers to finite adeles.** Let `L/K` be an extension of
number fields and `M` an extension of both. If for some ring automorphisms `σ i` of `M` the norm
`N_{L/K}(x)` of every `x ∈ L`, read in `M`, is `∏ i, σ i x`, then the same holds for the finite
adele norm: extended to `M`, the norm of a finite adele `a` of `L` is `∏ i, σ i a`. -/
theorem finiteAdeleExtension_finiteAdeleNorm_of_algebraMap_norm_eq_prod {ι : Type*} [Fintype ι]
    (σ : ι → M ≃+* M)
    (hσ : ∀ x : L, algebraMap K M (Algebra.norm K x) = ∏ i, σ i (algebraMap L M x))
    (a : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleExtension (𝓞 K) K (𝓞 M) M (finiteAdeleNorm K L a) =
      ∏ i, finiteAdeleEquiv M M (σ i) (finiteAdeleExtension (𝓞 L) L (𝓞 M) M a) := by
  -- Both sides are continuous in `a` and agree on the dense diagonal `L`.
  refine congrFun ((FiniteAdeleRing.denseRange_algebraMap (𝓞 L) L).equalizer
    ((continuous_finiteAdeleExtension (𝓞 K) K (𝓞 M) M).comp (continuous_finiteAdeleNorm K L))
    (continuous_finsetProd _ fun i _ ↦ (continuous_finiteAdeleEquiv M M (σ i)).comp
      (continuous_finiteAdeleExtension (𝓞 L) L (𝓞 M) M))
    (funext fun x ↦ ?_)) a
  simp only [Function.comp_apply, finiteAdeleNorm_algebraMap, finiteAdeleExtension_algebraMap,
    finiteAdeleEquiv_algebraMap, hσ, map_prod]

omit [NumberField M] in
/-- **A product formula for the norm transfers to infinite adeles.** If for some ring
automorphisms `σ i` of `M` the norm `N_{L/K}(x)` of every `x ∈ L`, read in `M`, is `∏ i, σ i x`,
then extended to `M`, the norm of an infinite adele `a` of `L` is `∏ i, σ i a`. -/
theorem infiniteAdeleExtension_infiniteAdeleNorm_of_algebraMap_norm_eq_prod {ι : Type*}
    [Fintype ι] (σ : ι → M ≃+* M)
    (hσ : ∀ x : L, algebraMap K M (Algebra.norm K x) = ∏ i, σ i (algebraMap L M x))
    (a : InfiniteAdeleRing L) :
    infiniteAdeleExtension K M (infiniteAdeleNorm K L a) =
      ∏ i, infiniteAdeleEquiv M M (σ i) (infiniteAdeleExtension L M a) := by
  -- Both sides are continuous in `a` and agree on the dense diagonal `L`.
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap L).equalizer
    ((continuous_infiniteAdeleExtension K M).comp (continuous_infiniteAdeleNorm K L))
    (continuous_finsetProd _ fun i _ ↦ (continuous_infiniteAdeleEquiv M M (σ i)).comp
      (continuous_infiniteAdeleExtension L M))
    (funext fun x ↦ ?_)) a
  simp only [Function.comp_apply, infiniteAdeleNorm_algebraMap, infiniteAdeleExtension_algebraMap,
    infiniteAdeleEquiv_algebraMap, hσ, map_prod]

/-- **A product formula for the norm transfers to adeles.** If for some ring automorphisms `σ i`
of `M` the norm `N_{L/K}(x)` of every `x ∈ L`, read in `M`, is `∏ i, σ i x`, then extended to
`M`, the adele norm `N_{L/K}(a)` of an adele `a` of `L` is `∏ i, σ i a`. The extension `L/K` need
not be normal: `M` may be a Galois extension of `K` containing `L`, and the `σ i` representatives
of the cosets of `Gal(M/L)` in `Gal(M/K)`. -/
theorem adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod {ι : Type*} [Fintype ι]
    (σ : ι → M ≃+* M)
    (hσ : ∀ x : L, algebraMap K M (Algebra.norm K x) = ∏ i, σ i (algebraMap L M x))
    (a : AdeleRing (𝓞 L) L) :
    adeleExtension (𝓞 K) K (𝓞 M) M (adeleNorm K L a) =
      ∏ i, adeleEquiv M M (σ i) (adeleExtension (𝓞 L) L (𝓞 M) M a) := by
  -- Apply the infinite and finite formulas to the two factors. `AdeleRing` is a type synonym
  -- for the product, so its projections are `RingHom.fst` and `RingHom.snd`.
  refine Prod.ext ?_ ?_
  · rw [adeleExtension_fst, adeleNorm_fst,
      infiniteAdeleExtension_infiniteAdeleNorm_of_algebraMap_norm_eq_prod K L M σ hσ]
    refine Eq.trans ?_ (map_prod (RingHom.fst (InfiniteAdeleRing M) (FiniteAdeleRing (𝓞 M) M))
      (fun i ↦ adeleEquiv M M (σ i) (adeleExtension (𝓞 L) L (𝓞 M) M a)) Finset.univ).symm
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← adeleExtension_fst (R := 𝓞 L) (B := 𝓞 M) a]
    exact (adeleEquiv_fst M M (σ i) _).symm
  · rw [adeleExtension_snd, adeleNorm_snd,
      finiteAdeleExtension_finiteAdeleNorm_of_algebraMap_norm_eq_prod K L M σ hσ]
    refine Eq.trans ?_ (map_prod (RingHom.snd (InfiniteAdeleRing M) (FiniteAdeleRing (𝓞 M) M))
      (fun i ↦ adeleEquiv M M (σ i) (adeleExtension (𝓞 L) L (𝓞 M) M a)) Finset.univ).symm
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← adeleExtension_snd (R := 𝓞 L) (B := 𝓞 M) a]
    exact (adeleEquiv_snd M M (σ i) _).symm

end Transfer

section Galois

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The finite adele norm of a Galois extension is the product of the Galois conjugates**:
extended back to `L`, the norm of a finite adele `a` of `L` is `∏_σ σ a`. -/
theorem finiteAdeleExtension_finiteAdeleNorm (a : FiniteAdeleRing (𝓞 L) L) :
    finiteAdeleExtension (𝓞 K) K (𝓞 L) L (finiteAdeleNorm K L a) =
      ∏ σ : L ≃ₐ[K] L, finiteAdeleEquiv L L σ.toRingEquiv a := by
  rw [finiteAdeleExtension_finiteAdeleNorm_of_algebraMap_norm_eq_prod K L L
    (fun σ : L ≃ₐ[K] L ↦ σ.toRingEquiv) fun x ↦ by simp [Algebra.norm_eq_prod_automorphisms]]
  -- The algebra `𝓞 L → 𝓞 L` induced by `L → L` is the identity algebra, which is the one
  -- `finiteAdeleExtension_self` is stated for, up to unfolding instances.
  exact Finset.prod_congr rfl fun σ _ ↦
    congrArg _ (RingHom.congr_fun (finiteAdeleExtension_self (𝓞 L) L) a)

/-- **The infinite adele norm of a Galois extension is the product of the Galois conjugates**:
extended back to `L`, the norm of an infinite adele `a` of `L` is `∏_σ σ a`. -/
theorem infiniteAdeleExtension_infiniteAdeleNorm (a : InfiniteAdeleRing L) :
    infiniteAdeleExtension K L (infiniteAdeleNorm K L a) =
      ∏ σ : L ≃ₐ[K] L, infiniteAdeleEquiv L L σ.toRingEquiv a := by
  rw [infiniteAdeleExtension_infiniteAdeleNorm_of_algebraMap_norm_eq_prod K L L
    (fun σ : L ≃ₐ[K] L ↦ σ.toRingEquiv) fun x ↦ by simp [Algebra.norm_eq_prod_automorphisms],
    infiniteAdeleExtension_self, RingHom.id_apply]

/-- **The adele norm of a Galois extension is the product of the Galois conjugates**: extended
back to `L`, the norm of an adele `a` of `L` is `∏_σ σ a`. -/
theorem adeleExtension_adeleNorm (a : AdeleRing (𝓞 L) L) :
    adeleExtension (𝓞 K) K (𝓞 L) L (adeleNorm K L a) =
      ∏ σ : L ≃ₐ[K] L, adeleGaloisAction K L σ a := by
  rw [adeleExtension_adeleNorm_of_algebraMap_norm_eq_prod K L L
    (fun σ : L ≃ₐ[K] L ↦ σ.toRingEquiv) fun x ↦ by simp [Algebra.norm_eq_prod_automorphisms]]
  refine Finset.prod_congr rfl fun σ _ ↦ ?_
  rw [adeleGaloisAction_apply]
  -- As above, the identity algebra of `𝓞 L` up to unfolding instances.
  exact congrArg _ (RingHom.congr_fun (adeleExtension_self (𝓞 L) L) a)

end Galois

end TauCeti.GlobalNumberFields
