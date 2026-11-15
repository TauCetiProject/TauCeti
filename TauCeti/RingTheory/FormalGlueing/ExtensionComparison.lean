/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Ext
import TauCeti.RingTheory.FormalGlueing.CyclicExt
import TauCeti.RingTheory.FormalGlueing.Koszul

/-!
# Descent of extensions with ideal-power torsion quotient

Let `R → S` be flat and induce an isomorphism `R/I ≅ S/IS`, with `I` finitely generated.
Scalar extension induces a bijection on `Ext¹_R(M, N)` whenever `M` is `I`-power torsion.
The coefficient module `N` is arbitrary, and no Noetherianity or faithful flatness is needed.
Thus extensions with quotient supported on the formal neighbourhood descend uniquely at the
level of extension classes. This is the extension comparison used to reconstruct modules by
formal gluing.

For a cyclic quotient, use the Koszul complex on a finite set of ideal generators. Its first
cohomology is unchanged by the coefficient map `N → S ⊗ N`; the Ext-to-Koszul comparison gives
the same assertion for `Ext¹`. The extension--restriction adjunction converts this coefficient
comparison into scalar extension of extensions. A presentation by cyclic quotients then handles
arbitrary ideal-power torsion sources.

## References

* The Stacks Project, Lemma 15.91.8 (05EG), the degree-one extension comparison.
* The Stacks Project, Proposition 15.91.16 (05ER), reconstruction by formal gluing.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A flat ring map preserving the quotient by a finitely generated ideal preserves first Ext
with that cyclic quotient as source, with no restriction on the coefficient module. -/
theorem mapExt_one_bijective_of_quotient (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hIfg : I.FG)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (N : ModuleCat.{u} R) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    Function.Bijective ((ModuleCat.extendScalars f).mapExtAddHom
      (ModuleCat.of R (R ⧸ I)) N 1) := by
  algebraize [f]
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hIfg
  let φ := Fintype.linearCombination R x
  have hφ : LinearMap.range φ = I := by
    simpa only [φ, Fintype.range_linearCombination] using hx
  have hcoeff := TauCeti.koszulComplex.postcomp_ext_mk_one_bijective_of_cohomologyMap_bijective
    (S := S) φ (hφ.symm ▸ hI) N
    (TauCeti.koszulComplex.homologyMap_coefficient_mk_one_bijective φ N (hφ.symm ▸ hI) 1)
  rw [hφ] at hcoeff
  apply (Adjunction.mapExt_bijective_iff_postcomp_unit_app
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)) (ModuleCat.of R (R ⧸ I)) N 1).mpr
  have hunit : (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app N =
      ModuleCat.ofHom (TensorProduct.mk R S N 1) := by
    ext m
    exact ModuleCat.extendRestrictScalarsAdj_unit_app_apply (algebraMap R S) N m
  rw [hunit]
  simp only [TauCeti.coe_postcompOfLinear] at hcoeff
  exact hcoeff

/-- **Descent of degree-one extension classes with ideal-power torsion source.** For a flat
ring map inducing `R/I ≅ S/IS` and finitely generated `I`, scalar extension preserves first Ext
bijectively when the source is `I`-power torsion. The coefficient module is unrestricted. -/
@[stacks 05EG "the degree-one extension comparison for ideal-power torsion sources"]
theorem mapExt_one_bijective_of_primaryComponent_eq_top (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hIfg : I.FG)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (M N : ModuleCat.{u} R) (hM : I.primaryComponent M = ⊤) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    Function.Bijective ((ModuleCat.extendScalars f).mapExtAddHom M N 1) := by
  algebraize [f]
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  refine ⟨f.mapExt_one_injective_of_primaryComponent_eq_top hf I hIfg hI M N hM,
    f.mapExt_one_surjective_of_quotient_pow hf I hIfg hI N (fun n ↦ ?_) M hM⟩
  exact (f.mapExt_one_bijective_of_quotient hf (I ^ n) hIfg.pow
    (Ideal.quotientMap_bijective_of_primaryComponent_eq_top I (I ^ n) hI
      (I.primaryComponent_quotient_pow_eq_top n)) N).surjective

end RingHom
