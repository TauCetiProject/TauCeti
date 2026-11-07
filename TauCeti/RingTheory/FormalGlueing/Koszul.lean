/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.HomTensor
public import TauCeti.RingTheory.KoszulComplex.Cohomology
public import TauCeti.RingTheory.FormalGlueing.Torsion
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Koszul cohomology under formal-glueing base change

Let `R → S` be flat and induce an isomorphism `R/I ≅ S/IS`. For a finite projective
module `M` and a functional `φ : M → R` with image `I`, the coefficient map
`N → S ⊗[R] N` induces an isomorphism on Koszul cohomology in every degree.
There is no regular-sequence assumption, and the coefficients need not be finite.

This is the Koszul-cohomology comparison in the proof of descent of extensions
(Stacks 05EG). Together with the Hom comparison for ideal-power torsion sources and
the Ext-to-Koszul exact sequence, it supplies the middle vertical isomorphism used
to descend extensions of `R/I`. Such extension descent is the essential-surjectivity
input in formal gluing of modules.

The proof combines `ChainComplex.tensorLinearYonedaHomologyIso`, annihilation of
Koszul cohomology by the image ideal, and invariance of ideal-power torsion modules
under this base change.

## References

* The Stacks Project, Lemma 15.91.8 (05EG), the Koszul-cohomology comparison.
* The Stacks Project, Lemmas 15.91.2 (05E9) and 15.91.7 (05EF).
-/

public section

open CategoryTheory TensorProduct

universe u

namespace TauCeti.koszulComplex

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]

/-- A flat base change preserving the quotient by the image ideal of `φ` leaves Koszul
cohomology unchanged. The isomorphism is induced by the canonical coefficient map,
not merely an abstract equivalence between the cohomology modules. -/
@[stacks 05EG "the Koszul-cohomology comparison, in all degrees"]
theorem homologyMap_coefficient_mk_one_bijective (φ : Module.Dual R M)
    (N : ModuleCat.{u} R)
    (hI : Function.Bijective (Ideal.quotientMap (Ideal.map (algebraMap R S) (LinearMap.range φ))
      (algebraMap R S) Ideal.le_comap_map)) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap
      ((koszulComplex φ).linearYonedaObjMap R
        (ModuleCat.ofHom (TensorProduct.mk R S N 1))) n) := by
  have : ∀ i, Module.Finite R ((koszulComplex φ).X i) := by
    intro i
    rw [koszulComplex_X]
    infer_instance
  have : ∀ i, Module.Projective R ((koszulComplex φ).X i) := by
    intro i
    rw [koszulComplex_X]
    infer_instance
  let H := ((koszulComplex φ).linearYonedaObj R N).homology n
  have hH : Ideal.primaryComponent H (LinearMap.range φ) = ⊤ := by
    apply top_unique
    intro z _
    refine (Ideal.primaryComponent_mem _ _ _).mpr ⟨1, ?_⟩
    rw [pow_one, Submodule.mem_torsionBySet_iff]
    intro a
    exact Module.mem_annihilator.mp (range_le_annihilator_cohomology φ N n a.2) z
  have hη := tensorProduct_mk_bijective_of_primaryComponent_eq_top (S := S) hI hH
  let e := (koszulComplex φ).tensorLinearYonedaHomologyIso (ModuleCat.of R S) N n
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  convert he.comp hη using 1
  funext z
  exact ((koszulComplex φ).tensorLinearYonedaHomologyIso_hom_tmul
    (ModuleCat.of R S) N n 1 z).symm

end TauCeti.koszulComplex
