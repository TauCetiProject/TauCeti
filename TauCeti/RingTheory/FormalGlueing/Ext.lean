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
public import TauCeti.Algebra.Homology.Ext.Map.Descent
public import TauCeti.Algebra.Homology.Ext.Map.Adjunction
public import TauCeti.RingTheory.FormalGlueing.Torsion
public import TauCeti.Algebra.Module.Torsion.Presentation
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Ext comparison under formal base change for ideal-power torsion modules

Let `R → S` be flat and induce an isomorphism `R/I → S/IS`, with `I` finitely generated.
Scalar extension is injective on `Ext¹_R(M, N)` when `M` is `I`-power torsion.
Thus an extension with ideal-power torsion quotient splits if its scalar extension splits.
Neither faithful flatness nor a finiteness assumption on the modules is needed.

This is the injectivity part of the extension comparison in formal glueing.
It follows from the Hom comparison for torsion sources: a section after base change descends, and
the section identity can be checked after base change.

Surjectivity on Ext¹ from arbitrary `I`-power torsion modules reduces to surjectivity from
the cyclic quotients `R/Iⁿ`. The cyclic presentation `⨁ R/I^{n_i} → M` has torsion kernel, so Hom
from that kernel descends and Ext¹ from it is detected. No finite generation of the source
module or Noetherianity of the ring is required. The presentation is supplied by
`Ideal.primaryComponent_eq_top_iff_exists_surjective_directSum_quotient_pow`; the reduction
uses `Functor.mapExt_one_surjective_of_coproduct` and
`Functor.mapExt_one_surjective_of_shortExact`.

If instead the coefficient module `N` is `I`-power torsion, scalar extension is bijective
on `Extⁿ_R(M, N)` in every degree, with no restriction on `M` and no finite-generation
hypothesis on `I`. This supplies the torsion-coefficient case of the degree-one
extension comparison. The adjunction between extension and restriction of scalars
identifies this comparison with transport along `N → S ⊗[R] N`, which is an isomorphism
by `TauCeti.tensorProduct_mk_bijective_of_primaryComponent_eq_top`. In particular,
comparison in degrees one and two is available for the long exact sequence associated
to the torsion submodule of a general coefficient module.

## References

* [Stacks Project, Lemma 15.91.8](https://stacks.math.columbia.edu/tag/05EG),
  injectivity and the reduction of surjectivity to cyclic quotients for torsion sources,
  and the torsion-coefficient case of the extension comparison.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped TensorProduct DirectSum

universe u

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- For a flat ring map inducing `R/I ≅ S/IS` with finitely generated `I`, morphisms from
an `I`-power torsion module descend along scalar extension. -/
theorem extendScalars_map_surjective_of_primaryComponent_eq_top (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hIfg : I.FG)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (M N : ModuleCat.{u} R) (hM : I.primaryComponent M = ⊤) :
    Function.Surjective ((ModuleCat.extendScalars f).map : (M ⟶ N) → _) := by
  algebraize [f]
  -- Identify the categorical map with linear base change on pure tensors.
  have hmap (t : M →ₗ[R] N) :
      (ModuleCat.extendScalars f).map (ModuleCat.ofHom t) =
        ModuleCat.ofHom (t.baseChange S) := by
    ext m
    exact (ModuleCat.ExtendScalars.map_tmul f (ModuleCat.ofHom t) 1 m).trans
      (t.baseChange_tmul 1 m).symm
  intro g
  obtain ⟨t, ht⟩ := (TauCeti.baseChangeHom_bijective_of_primaryComponent_eq_top_left
    (S := S) hI hIfg (N := N) hM).2 g.hom
  exact ⟨ModuleCat.ofHom t, (hmap t).trans (ModuleCat.hom_ext ht)⟩

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
  · intro E
    exact f.extendScalars_map_surjective_of_primaryComponent_eq_top hf I hIfg hI M E hM
  · intro a b hab
    apply ModuleCat.hom_ext
    apply (TauCeti.baseChangeHom_bijective_of_primaryComponent_eq_top_left
      (S := S) hI hIfg (N := M) hM).1
    ext m
    exact congrArg (fun k ↦ k ((1 : S) ⊗ₜ m)) hab

/-- For a flat ring map `f : R → S` inducing `R/I ≅ S/IS`, with `I` finitely generated,
to descend extensions with arbitrary `I`-power torsion source it suffices to descend extensions
with source `R/Iⁿ` for every `n`. The source and coefficient modules need not be finite. -/
@[stacks 05EG "reduction of surjectivity to cyclic quotients"]
theorem mapExt_one_surjective_of_quotient_pow (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hIfg : I.FG)
    (hI : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))
    (N : ModuleCat.{u} R)
    (hcyclic : ∀ n : ℕ, let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
      Function.Surjective ((ModuleCat.extendScalars f).mapExtAddHom
        (ModuleCat.of R (R ⧸ I ^ n)) N 1))
    (M : ModuleCat.{u} R) (hM : I.primaryComponent M = ⊤) :
    let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    Function.Surjective ((ModuleCat.extendScalars f).mapExtAddHom M N 1) := by
  classical
  algebraize [f]
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  obtain ⟨ι, n, π, hπ⟩ :=
    (I.primaryComponent_eq_top_iff_exists_surjective_directSum_quotient_pow).mp hM
  have hP : I.primaryComponent (⨁ i : ι, R ⧸ I ^ n i) = ⊤ :=
    I.primaryComponent_directSum_eq_top fun i ↦ I.primaryComponent_quotient_pow_eq_top (n i)
  have hK : I.primaryComponent (LinearMap.ker π) = ⊤ := by
    rw [← Ideal.primaryComponent_comap_subtype, hP, Submodule.comap_top]
  apply (ModuleCat.extendScalars f).mapExt_one_surjective_of_shortExact
    (π.shortExact_shortComplexKer hπ) N
  · exact f.extendScalars_map_surjective_of_primaryComponent_eq_top hf I hIfg hI
      (ModuleCat.of R (LinearMap.ker π)) N hK
  · exact mapExt_one_injective_of_primaryComponent_eq_top f hf I hIfg hI
      (ModuleCat.of R (LinearMap.ker π)) N hK
  · exact (ModuleCat.extendScalars f).mapExt_one_surjective_of_coproduct
      (ModuleCat.coproductCoconeIsColimit
        (fun i : ι ↦ ModuleCat.of R (R ⧸ I ^ n i))) N (fun i ↦ hcyclic (n i))

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
    -- The unit is 1 ⊗ₜ · by ModuleCat.extendRestrictScalarsAdj_unit_app_apply.
    -- The Module.compHom R-module structure on S used by extendScalars agrees definitionally
    -- with the one induced by the Algebra R S instance supplied by algebraize.
    exact TauCeti.tensorProduct_mk_bijective_of_primaryComponent_eq_top (S := S) hI hN
  exact
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).mapExt_bijective_of_isIso_unit_app
      M N n

end RingHom
