/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Affine
import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Effective descent of finite locally free schemes over affine bases

A finite locally free scheme over `Spec S`, equipped with descent data relative to a
faithfully flat ring map `R → S`, descends to a finite locally free scheme over `Spec R`.
Here finite local freeness means finite, flat, and locally of finite presentation; no
Noetherian hypothesis is imposed on either ring. The comparison is an isomorphism of
descent data, so it retains the cocycle, rather than just identifying the underlying schemes.

The rank function of the descended scheme pulls back to the original rank function. In
particular, prescribed ranks of finite subgroup schemes can be retained during descent.
Uniqueness and descent of morphisms are supplied by `DescentDatum.baseChangeHomEquiv`
and `DescentDatum.Hom.descendIso`, using the effective epimorphism instances in
`TauCeti.AlgebraicGeometry.Descent.Affine`.

The construction reuses `Algebra.DescentDatum.specEquiv` and `specDescendedHom`.
Mathlib's faithfully flat descent of module finiteness, flatness, and algebra finite
presentation ensures that their descended coordinate algebra has the required properties.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1 and Corollaire 2.2.
* The Stacks Project, *Descent*, Section 35.23 (properties local in the fpqc topology).
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.DescentDatum

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]

private theorem exists_finiteLocallyFree_spec_descended
    {B : Type u} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    [Module.Finite S B] [Module.Flat S B] [Algebra.FinitePresentation S B]
    (E : Algebra.DescentDatum R S B) :
    ∃ X₀ : Over (Spec (.of R)), IsFinite X₀.hom ∧ Flat X₀.hom ∧
      LocallyOfFinitePresentation X₀.hom ∧
      ∃ f : Hom (baseChange (Spec.algebraMap R S) X₀) E.spec, IsIso f.hom := by
  -- Reflect all three finiteness/flatness conditions through the effectivity isomorphism.
  have : Module.Finite S (S ⊗[R] E.descended) :=
    Module.Finite.equiv E.baseChangeEquiv.symm.toLinearEquiv
  have : Module.Finite R E.descended :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have : Module.Flat S (S ⊗[R] E.descended) :=
    Module.Flat.of_linearEquiv E.baseChangeEquiv.toLinearEquiv
  have : Module.Flat R E.descended := Module.Flat.of_flat_tensorProduct R E.descended S
  have : Algebra.FinitePresentation S (S ⊗[R] E.descended) :=
    Algebra.FinitePresentation.equiv E.baseChangeEquiv.symm
  have : Algebra.FinitePresentation R E.descended :=
    Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat S
  -- The descended coordinate algebra gives a finite locally free scheme over `Spec R`.
  have : IsFinite (Over.mk (Spec.algebraMap R E.descended)).hom := by
    simp only [Over.mk_hom]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Flat (Over.mk (Spec.algebraMap R E.descended)).hom := by
    simp only [Over.mk_hom]
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Over.mk (Spec.algebraMap R E.descended)).hom := by
    simp only [Over.mk_hom]
    exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact ⟨Over.mk (Spec.algebraMap R E.descended), inferInstance,
    inferInstance, inferInstance, E.specDescendedHom, inferInstance⟩

/-- **Effective faithfully flat descent of finite locally free schemes over affine bases.**
Every descent datum on a finite locally free `X → Spec S` is isomorphic to the canonical
datum on the base change of a finite locally free `X₀ → Spec R`. Its rank pulls back to
the rank of `X`. The source need not be presented as a spectrum in the input. -/
theorem exists_finiteLocallyFree_baseChange_hom_isIso
    {X : Over (Spec (.of S))} [IsFinite X.hom] [Flat X.hom]
    [LocallyOfFinitePresentation X.hom] (D : DescentDatum (Spec.algebraMap R S) X) :
    ∃ X₀ : Over (Spec (.of R)), IsFinite X₀.hom ∧ Flat X₀.hom ∧
      LocallyOfFinitePresentation X₀.hom ∧
      ∃ f : Hom (baseChange (Spec.algebraMap R S) X₀) D,
        IsIso f.hom ∧ X.hom.finrank = X₀.hom.finrank ∘ Spec.algebraMap R S := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  obtain ⟨B, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of S)).mpr this
  -- Spell the spectrum presentation as `Over.mk` for the affine descent dictionary.
  let e' : Over.mk (Spec.algebraMap S B.unop) ≅ X := e
  let _ : Algebra R B.unop := ((algebraMap S B.unop).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S B.unop := .of_algebraMap_eq fun _ ↦ rfl
  have he : e'.hom.left ≫ X.hom = Spec.algebraMap S B.unop := by
    simpa only [Over.mk_hom] using e'.hom.w
  have hfinite : IsFinite (Spec.algebraMap S B.unop) := by
    rw [← he]
    infer_instance
  have hflat : Flat (Spec.algebraMap S B.unop) := by
    rw [← he]
    infer_instance
  have hfp : LocallyOfFinitePresentation (Spec.algebraMap S B.unop) := by
    rw [← he]
    infer_instance
  have : Module.Finite S B.unop :=
    (RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfinite))
  have : Module.Flat S B.unop :=
    (RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflat))
  have : Algebra.FinitePresentation S B.unop :=
    (RingHom.finitePresentation_algebraMap.mp
      ((LocallyOfFinitePresentation.SpecMap_iff _).mp hfp))
  -- `algSpec.obj B` is the spectrum presentation used by `specEquiv`.
  let E := (Algebra.DescentDatum.specEquiv R S B.unop).symm (transport e' D)
  obtain ⟨X₀, hfinite₀, hflat₀, hfp₀, f₀, hf₀⟩ := exists_finiteLocallyFree_spec_descended E
  obtain ⟨g, hg⟩ : ∃ g : Hom E.spec D, IsIso g.hom := by
    dsimp only [E]
    rw [Algebra.DescentDatum.spec_specEquiv_symm]
    exact ⟨transportHom e' D, by rw [transportHom_hom]; infer_instance⟩
  let f := g.comp f₀
  have : IsIso f.hom := by
    rw [Hom.comp_hom]
    infer_instance
  refine ⟨X₀, hfinite₀, hflat₀, hfp₀, f, inferInstance, ?_⟩
  -- The comparison is over `Spec S`, and finite-flat rank is invariant under this isomorphism.
  funext s
  have h := f.hom.w
  simp only [Over.pullback_obj_hom] at h
  rw [← Scheme.Hom.finrank_comp_left_of_isIso f.hom.left X.hom, h]
  exact Scheme.Hom.finrank_pullback_snd _ _ s

end TauCeti.DescentDatum
