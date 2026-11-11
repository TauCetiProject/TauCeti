/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.KoszulComplex.Basic
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.FiveLemma

/-!
# Ext and first Koszul cohomology

For a functional `φ : M → R`, there is a natural exact sequence
`0 → Ext¹(R / φ(M), N) → H¹(Hom(K(φ), N)) → Hom(H₁(K(φ)), N)`.
It is the degree-one universal coefficient sequence, using `H₀(K(φ)) = R / φ(M)`.
Neither regularity nor exactness of the Koszul complex is assumed. This comparison
is useful in descent of extensions: its obstruction term is a Hom module from a module
annihilated by the image ideal. If `N` has no elements annihilated by that ideal, the
comparison is an isomorphism. More generally,
`postcomp_ext_bijective_of_cohomologyMap_bijective` compares first Ext groups along a
coefficient morphism by comparing first Koszul cohomology and detecting the Hom obstruction.

For a finite list of generators of an ideal, this is Stacks 05EE. The kernel of the
Koszul presentation onto the image ideal in 05ED is canonically `H₁(K(φ))`, so the
obstruction is written here using Koszul homology rather than that presentation.

## References

* [Stacks Project, Lemma 15.91.6](https://stacks.math.columbia.edu/tag/05EE).
* C. A. Weibel, *An Introduction to Homological Algebra*, Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u w

namespace TauCeti.koszulComplex

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  (φ : Module.Dual R M)

-- Cache the derived instances at degree zero: searching for the split monomorphism through
-- the general projective-cycle instances otherwise exhausts the typeclass search budget.
private instance splitMono_iCycles_zero : IsSplitMono ((koszulComplex φ).iCycles 0) :=
  IsSplitMono.of_iso _

private instance projective_cycles_zero : Projective ((koszulComplex φ).cycles 0) := by
  have : Projective ((koszulComplex φ).X 0) :=
    Projective.of_iso (exteriorPower.zeroEquiv R M).symm.toModuleIso inferInstance
  exact Projective.of_iso (asIso ((koszulComplex φ).iCycles 0)).symm inferInstance

variable [HasExt.{w} (ModuleCat.{u} R)] (N : ModuleCat.{u} R)

/-- The canonical map from extensions of the quotient by the image ideal to first Koszul
cohomology. It is defined for arbitrary modules and arbitrary linear functionals. -/
def extToCohomology :
    Ext.{w} (ModuleCat.of R (R ⧸ LinearMap.range φ)) N 1 →ₗ[R]
      ((koszulComplex φ).linearYonedaObj R N).homology 1 :=
  (ChainComplex.extToHomology R (koszulComplex φ) N 1 0).comp
    (extLinearEquivOfIso R (homologyZeroEquiv φ).symm.toModuleIso (Iso.refl N) 1).toLinearMap

/-- The Ext-to-Koszul comparison is the universal-coefficient map transported along the
identification of zeroth Koszul homology with the quotient by the image ideal. -/
theorem extToCohomology_def :
    letI : Projective ((koszulComplex φ).cycles 0) := by infer_instance
    letI : IsSplitMono ((koszulComplex φ).iCycles 0) := by infer_instance
    extToCohomology φ N =
      (ChainComplex.extToHomology R (koszulComplex φ) N 1 0).comp
        (extLinearEquivOfIso R (homologyZeroEquiv φ).symm.toModuleIso (Iso.refl N) 1).toLinearMap :=
  (rfl)

/-- The Ext-to-Koszul comparison is injective; no exactness of the Koszul complex is needed. -/
@[stacks 05EE "injectivity, with the image ideal of an arbitrary functional"]
theorem extToCohomology_injective : Function.Injective (extToCohomology φ N) :=
  (ChainComplex.extToHomology_injective
    (k := R) (X := koszulComplex φ) (Y := N) (i := 1) (j := 0) rfl).comp
    (extLinearEquivOfIso R (homologyZeroEquiv φ).symm.toModuleIso (Iso.refl N) 1).injective

/-- An element of first Koszul cohomology comes from an extension of `R / φ(M)` exactly when
its evaluation on first Koszul homology vanishes. -/
@[stacks 05EE "exactness, with the obstruction written as Hom from first Koszul homology"]
theorem exact_extToCohomology_kronecker :
    Function.Exact (extToCohomology φ N)
      (ChainComplex.kronecker R (koszulComplex φ) N 1) := by
  rw [LinearMap.exact_iff, extToCohomology,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  exact (ChainComplex.exact_extToHomology_kronecker
    (k := R) (X := koszulComplex φ) (Y := N) (i := 1) (j := 0) rfl).linearMap_ker_eq

/-- The Ext-to-Koszul map commutes with a morphism of coefficient modules. -/
theorem extToCohomology_naturality {N' : ModuleCat.{u} R} (g : N ⟶ N')
    (e : Ext.{w} (ModuleCat.of R (R ⧸ LinearMap.range φ)) N 1) :
    extToCohomology φ N' (e.comp (Ext.mk₀ g) (add_zero 1)) =
      HomologicalComplex.homologyMap ((koszulComplex φ).linearYonedaObjMap R g) 1
        (extToCohomology φ N e) := by
  simp only [extToCohomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    extLinearEquivOfIso_apply, Iso.refl_hom, Ext.comp_mk₀_id]
  rw [← Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by omega)]
  exact ChainComplex.extToHomology_coefficient_naturality g 1 0 _

/-- A coefficient morphism induces a bijection on first extensions of the image-ideal
quotient if it induces a bijection on first Koszul cohomology and is injective on Hom from
first Koszul homology. No regular sequence or torsion-freeness assumption is needed. -/
theorem postcomp_ext_bijective_of_cohomologyMap_bijective
    {N' : ModuleCat.{u} R} (g : N ⟶ N')
    (hH : Function.Bijective
      (HomologicalComplex.homologyMap ((koszulComplex φ).linearYonedaObjMap R g) 1))
    (hHom : Function.Injective
      (Linear.rightComp R ((koszulComplex φ).homology 1) g)) :
    Function.Bijective
      ((Ext.mk₀ g).postcompOfLinear R (ModuleCat.of R (R ⧸ LinearMap.range φ)) (add_zero 1)) := by
  apply LinearMap.bijective_of_bijective_of_injective_of_left_exact
    (extToCohomology φ N) (ChainComplex.kronecker R (koszulComplex φ) N 1)
    (extToCohomology φ N') (ChainComplex.kronecker R (koszulComplex φ) N' 1)
    ((Ext.mk₀ g).postcompOfLinear R _ (add_zero 1))
    (HomologicalComplex.homologyMap ((koszulComplex φ).linearYonedaObjMap R g) 1).hom
    (Linear.rightComp R ((koszulComplex φ).homology 1) g)
  · exact LinearMap.ext fun e ↦ extToCohomology_naturality φ N g e
  · exact LinearMap.ext fun e ↦
      ChainComplex.kronecker_coefficient_naturality g 1 e
  · exact exact_extToCohomology_kronecker φ N
  · exact exact_extToCohomology_kronecker φ N'
  · exact hH
  · exact hHom
  · exact extToCohomology_injective φ N
  · exact extToCohomology_injective φ N'

omit [HasExt (ModuleCat R)] in
/-- If the coefficient module has no elements annihilated by the image ideal, every map from
Koszul homology to it is zero, in every degree. -/
theorem hom_homology_eq_zero_of_torsionBySet_eq_bot
    (hN : Submodule.torsionBySet R N (LinearMap.range φ) = ⊥)
    (n : ℕ) (f : (koszulComplex φ).homology n ⟶ N) : f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply (Submodule.mem_bot R).mp
  rw [← hN, Submodule.mem_torsionBySet_iff]
  rintro ⟨r, m, rfl⟩
  rw [← map_smul, smul_homology_eq_zero, map_zero]

/-- Without image-ideal torsion in the coefficients, every first Koszul cohomology class
comes from an extension of the quotient by the image ideal. -/
theorem extToCohomology_surjective_of_torsionBySet_eq_bot
    (hN : Submodule.torsionBySet R N (LinearMap.range φ) = ⊥) :
    Function.Surjective (extToCohomology φ N) := by
  intro z
  exact (exact_extToCohomology_kronecker φ N z).mp
    (hom_homology_eq_zero_of_torsionBySet_eq_bot φ N hN 1 _)

/-- The first Ext group of the quotient by the image ideal is first Koszul cohomology when
that ideal annihilates no nonzero element of the coefficients. -/
def extEquivCohomologyOfTorsionBySetEqBot
    (hN : Submodule.torsionBySet R N (LinearMap.range φ) = ⊥) :
    Ext.{w} (ModuleCat.of R (R ⧸ LinearMap.range φ)) N 1 ≃ₗ[R]
      ((koszulComplex φ).linearYonedaObj R N).homology 1 :=
  LinearEquiv.ofBijective (extToCohomology φ N)
    ⟨extToCohomology_injective φ N,
      extToCohomology_surjective_of_torsionBySet_eq_bot φ N hN⟩

/-- Under the image-ideal torsion hypothesis, the comparison equivalence has the canonical
Ext-to-cohomology map as its forward map. -/
@[simp]
theorem extEquivCohomologyOfTorsionBySetEqBot_apply
    (hN : Submodule.torsionBySet R N (LinearMap.range φ) = ⊥)
    (e : Ext.{w} (ModuleCat.of R (R ⧸ LinearMap.range φ)) N 1) :
    extEquivCohomologyOfTorsionBySetEqBot φ N hN e = extToCohomology φ N e :=
  (rfl)

end TauCeti.koszulComplex
