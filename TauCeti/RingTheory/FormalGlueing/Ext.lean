/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.Ext.Map.Injective
public import TauCeti.Algebra.Homology.Ext.Map.Adjunction
public import TauCeti.RingTheory.FormalGlueing.Torsion

/-!
# Ext comparison under formal base change for ideal-power torsion modules

Let `R → S` be flat and induce an isomorphism `R/I → S/IS`, with `I` finitely generated.
Scalar extension is injective on `Ext¹_R(M, N)` when `M` is `I`-power torsion.
Thus an extension with ideal-power torsion quotient splits if its scalar extension splits.
Neither faithful flatness nor a finiteness assumption on the modules is needed.

If instead the coefficient module `N` is `I`-power torsion, scalar extension is bijective
on `Extⁿ_R(M, N)` in every degree, with no restriction on `M` and no finite-generation
hypothesis on `I`. This supplies the torsion-coefficient case of the degree-one
extension comparison. The adjunction between extension and restriction of scalars
identifies this comparison with transport along `N → S ⊗[R] N`, which is an isomorphism
by `TauCeti.tensorProduct_mk_bijective_of_primaryComponent_eq_top`. In particular,
comparison in degrees one and two is available for the long exact sequence associated
to the torsion submodule of a general coefficient module.

The torsion-source result is the injectivity part of the extension comparison in formal glueing.
It follows from the Hom comparison for torsion sources: a section after base change descends, and
the section identity can be checked after base change.

## References

* [Stacks Project, Lemma 15.91.8](https://stacks.math.columbia.edu/tag/05EG),
  the injectivity part for torsion sources and the torsion-coefficient case of the
  extension comparison.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A flat ring map inducing `R/I ≅ S/IS` detects degree-one extension classes with
`I`-power torsion source, for finitely generated `I`. No faithful flatness is required. -/
@[stacks 05EG "injectivity of the degree-one extension comparison"]
theorem mapExt_one_injective_of_primaryComponent_eq_top (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hIfg : I.FG)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (M N : ModuleCat.{u} R) (hM : I.primaryComponent M = ⊤) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    Function.Injective ((ModuleCat.extendScalars f).mapExtAddHom M N 1) := by
  algebraize [f]
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  apply Functor.mapExt_one_injective_of_map_surjective
  · intro E g
    obtain ⟨t, ht⟩ := (TauCeti.baseChangeHom_bijective_of_primaryComponent_eq_top_left
      (S := S) hI hIfg (N := E) hM).2 g.hom
    refine ⟨ModuleCat.ofHom t, ?_⟩
    ext m
    exact LinearMap.congr_fun ht (1 ⊗ₜ m)
  · intro a b hab
    apply ModuleCat.hom_ext
    apply (TauCeti.baseChangeHom_bijective_of_primaryComponent_eq_top_left
      (S := S) hI hIfg (N := M) hM).1
    ext m
    exact congrArg (fun k ↦ k ((1 : S) ⊗ₜ m)) hab

/-- A flat ring map inducing `R/I ≅ S/IS` preserves all Ext groups with `I`-power
torsion coefficients. The source module is arbitrary, and `I` need not be finitely generated. -/
@[stacks 05EG "the torsion-coefficient case, in every degree"]
theorem mapExt_bijective_of_primaryComponent_eq_top_right (f : R →+* S) (hf : f.Flat)
    (I : Ideal R)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (M N : ModuleCat.{u} R) (hN : I.primaryComponent N = ⊤) (n : ℕ) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    Function.Bijective ((ModuleCat.extendScalars f).mapExtAddHom M N n) := by
  algebraize [f]
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have : IsIso ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app N) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact TauCeti.tensorProduct_mk_bijective_of_primaryComponent_eq_top (S := S) hI hN
  exact
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).mapExt_bijective_of_isIso_unit_app
      M N n

end RingHom
