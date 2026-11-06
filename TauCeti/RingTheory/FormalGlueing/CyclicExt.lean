/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Torsion
public import TauCeti.RingTheory.KoszulComplex.Ext
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# From Koszul coefficient comparison to cyclic extensions

For a flat algebra `S` over `R` inducing `R/I ≅ S/IS`, comparison of first Koszul
cohomology through `N → S ⊗[R] N` implies comparison of `Ext¹_R(R/I, N)` through the
same coefficient map. Here `I` is the finitely generated image ideal of the Koszul
functional. The coefficient module is arbitrary; in particular it need not be torsion-free.

The obstruction in the Ext-to-Koszul exact sequence is Hom from first Koszul homology.
Since this homology is annihilated by `I`, the existing formal-glueing Hom comparison
detects its maps into `N`. Thus one needs only the cohomology comparison, not exactness
of the Koszul complex or a regular sequence. This is the cyclic kernel-comparison step
in the extension-descent argument of Stacks 05EG, not the cohomology comparison itself.

## References

* [Stacks Project, Lemma 15.91.8](https://stacks.math.columbia.edu/tag/05EG).
* The central formal inputs are `TauCeti.koszulComplex.exact_extToCohomology_kronecker`
  and `TauCeti.baseChangeHom_bijective_of_primaryComponent_eq_top_left`.
-/

public section

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

universe u

namespace TauCeti.koszulComplex

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M]

/-- For a flat algebra preserving the quotient by the image ideal, first Koszul cohomology
comparison implies first Ext comparison for the cyclic quotient. Both comparisons use the
actual coefficient map `n ↦ 1 ⊗ n`; no torsion-freeness of the coefficients is required. -/
theorem postcomp_ext_mk_one_bijective_of_cohomologyMap_bijective
    (φ : Module.Dual R M) (hfg : (LinearMap.range φ).FG)
    (hI : Function.Bijective (Ideal.quotientMap
      (Ideal.map (algebraMap R S) (LinearMap.range φ)) (algebraMap R S) Ideal.le_comap_map))
    (N : ModuleCat.{u} R)
    (hH : Function.Bijective (HomologicalComplex.homologyMap
      ((koszulComplex φ).linearYonedaObjMap R
        (ModuleCat.ofHom (TensorProduct.mk R S N 1))) 1)) :
    Function.Bijective ((Ext.mk₀ (ModuleCat.ofHom (TensorProduct.mk R S N 1))).postcompOfLinear
      R (ModuleCat.of R (R ⧸ LinearMap.range φ)) (add_zero 1)) := by
  apply postcomp_ext_bijective_of_cohomologyMap_bijective φ N _ hH
  intro a b hab
  apply ModuleCat.hom_ext
  apply tensorProduct_mk_comp_injective_of_primaryComponent_eq_top hI hfg
    (primaryComponent_homology_eq_top φ 1)
  exact congrArg ModuleCat.Hom.hom hab

end TauCeti.koszulComplex
