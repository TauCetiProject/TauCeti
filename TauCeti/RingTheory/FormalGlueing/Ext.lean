/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.Ext.MapInjective
public import TauCeti.RingTheory.FormalGlueing.Torsion

/-!
# Detecting extensions of ideal-power torsion modules

Let `R → S` be flat and induce an isomorphism `R/I → S/IS`, with `I` finitely generated.
Scalar extension is injective on `Ext¹_R(M, N)` when `M` is `I`-power torsion.
Thus an extension with ideal-power torsion quotient splits if its scalar extension splits.
Neither faithful flatness nor a finiteness assumption on the modules is needed.

This is the injectivity part of the extension comparison in formal glueing. It follows
from the Hom comparison for torsion sources: a section after base change descends, and
the section identity can be checked after base change.

## References

* [Stacks Project, Lemma 15.91.8](https://stacks.math.columbia.edu/tag/05EG),
  the injectivity part of the degree-one extension comparison.
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

end RingHom
