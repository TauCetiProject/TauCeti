/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
public import TauCeti.RingTheory.AlgebraTower

/-!
# Intermediate extensions after extending constants

For an exact constant field `k` in `F`, a separable algebraic extension `k' / k` preserves
linear independence over every intermediate field `C` of `F / k` after replacing `C` by
`k' · C`. The extension of constants may be infinite. This is the linear-algebraic input
to comparing degrees after adjoining an algebraic closure of the constants.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.6.1.
-/

public section

open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsSeparable k k']

/-- Extending separable constants preserves independence over any intermediate field, after
extending that intermediate field by the same constants. -/
theorem linearIndependent_adjoin_algebraMap_comp_of_isIntegrallyClosedIn
    (hex : IsIntegrallyClosedIn k F) (C : IntermediateField k F)
    {ι : Type*} {c : ι → F} (hc : LinearIndependent C c) :
    LinearIndependent (IntermediateField.adjoin k' (Set.range (algebraMap C F')))
      (algebraMap F F' ∘ c) := by
  let b := Module.Basis.ofVectorSpace k C
  let S := Algebra.adjoin k' (Set.range (algebraMap C F'))
  let w : _ → S := fun i ↦ ⟨algebraMap C F' (b i), Algebra.subset_adjoin ⟨b i, rfl⟩⟩
  have hprod := linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn_of_isSeparable
    (k' := k') (E := F') hex (linearIndependent_smul b.linearIndependent hc)
  have hw : Submodule.span k' (Set.range w) = ⊤ := by
    let f := IsScalarTower.toAlgHom k C F'
    let e := AlgEquiv.ofInjective f f.injective
    have hspan := f.range.adjoin_eq_span_basis k' (b.map e.toLinearEquiv)
    have hrange : (f.range : Set F') = Set.range (algebraMap C F') := by
      -- The tower homomorphism is the algebra map on elements.
      rfl
    have hfun : (fun i ↦ ((b.map e.toLinearEquiv) i : F')) =
        algebraMap C F' ∘ b := by
      ext i
      exact AlgEquiv.ofInjective_apply f f.injective (b i)
    rw [hrange, hfun] at hspan
    apply Submodule.map_injective_of_injective (f := S.val.toLinearMap) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp]
    have hval : S.val.toLinearMap = S.toSubmodule.subtype :=
      (Subalgebra.toSubmodule_subtype S).symm
    rw [hval, Submodule.range_subtype]
    exact hspan.symm
  have hli : LinearIndependent S (algebraMap F F' ∘ c) := by
    apply LinearIndependent.of_smul_of_span_eq_top (b := w) (hb := hw)
    convert (linearIndependent_equiv' (Equiv.prodComm ι _) (g := fun p : ι × _ ↦
      algebraMap F F' (b p.2 • c p.1)) rfl).mpr hprod using 1
    ext p
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply C F F', w]
  exact (LinearIndependent.iff_fractionRing S
    (IntermediateField.adjoin k' (Set.range (algebraMap C F')))).mp hli

omit [Algebra.IsSeparable k k'] [Algebra k k'] [Algebra k F']
    [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- If the original field generates the ambient field as an algebra over the enlarged
intermediate field, its basis over `C` spans the ambient field over that enlarged field. -/
theorem span_range_basis_eq_top_of_adjoin_eq_top (C : IntermediateField k F)
    {ι : Type*} (b : Module.Basis ι C F)
    (h : Algebra.adjoin (IntermediateField.adjoin k' (Set.range (algebraMap C F')))
      (Set.range (algebraMap F F')) = ⊤) :
    Submodule.span (IntermediateField.adjoin k' (Set.range (algebraMap C F')))
      (Set.range (algebraMap F F' ∘ b)) = ⊤ := by
  let C' := IntermediateField.adjoin k' (Set.range (algebraMap C F'))
  let g : C →+* C' := (algebraMap C F').codRestrict C'.toSubring fun x ↦
    IntermediateField.subset_adjoin k' _ ⟨x, rfl⟩
  let : Algebra C C' := g.toAlgebra
  have : IsScalarTower C C' F' := .of_algebraMap_eq fun _ ↦ rfl
  let f := IsScalarTower.toAlgHom C F F'
  let e := AlgEquiv.ofInjective f f.injective
  have hspan := f.range.adjoin_eq_span_basis C' (b.map e.toLinearEquiv)
  have hrange : (f.range : Set F') = Set.range (algebraMap F F') := by
    -- The tower homomorphism is the algebra map on elements.
    rfl
  have hfun : (fun i ↦ ((b.map e.toLinearEquiv) i : F')) = algebraMap F F' ∘ b := by
    ext i
    exact AlgEquiv.ofInjective_apply f f.injective (b i)
  rw [hrange, hfun] at hspan
  rw [h, Algebra.top_toSubmodule] at hspan
  exact hspan.symm

omit [Algebra.IsSeparable k k'] in
/-- A basis over an intermediate field spans the constant compositum over the enlarged
intermediate field. Algebraicity of the constants suffices; separability is unnecessary. -/
theorem span_range_basis_of_constantCompositum_eq_top
    [Algebra.IsAlgebraic k k']
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    {ι : Type*} (b : Module.Basis ι C F) :
    Submodule.span (IntermediateField.adjoin k' (Set.range (algebraMap C F')))
      (Set.range (algebraMap F F' ∘ b)) = ⊤ := by
  let C' := IntermediateField.adjoin k' (Set.range (algebraMap C F'))
  have htop : Algebra.adjoin C' (Set.range (algebraMap F F')) = ⊤ := by
    let A := Algebra.adjoin C' (Set.range (algebraMap F F'))
    apply eq_top_iff.mpr
    intro z _
    have hz : z ∈ Algebra.adjoin F (Set.range (algebraMap k' F')) := by
      rw [adjoin_range_algebraMap_of_constantCompositum_eq_top (k := k) h]
      trivial
    have hzA : z ∈ A := by
      refine Algebra.adjoin_induction (p := fun z _ ↦ z ∈ A) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨c, rfl⟩
        rw [IsScalarTower.algebraMap_apply k' C' F' c]
        exact A.algebraMap_mem (algebraMap k' C' c)
      · intro c
        exact Algebra.subset_adjoin ⟨c, rfl⟩
      · exact fun _ _ _ _ ↦ A.add_mem
      · exact fun _ _ _ _ ↦ A.mul_mem
    exact hzA
  exact span_range_basis_eq_top_of_adjoin_eq_top C b htop

/-- A basis of `F / C` remains a basis of `F · k' / C · k'` for a separable algebraic extension
of an exact constant field. Neither extension of fields needs to be finite-dimensional. -/
noncomputable def constantExtensionBasis (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (IntermediateField.adjoin k' (Set.range (algebraMap C F'))) F' :=
  Module.Basis.mk
    (linearIndependent_adjoin_algebraMap_comp_of_isIntegrallyClosedIn hex C b.linearIndependent)
    (span_range_basis_of_constantCompositum_eq_top h C b).ge

@[simp]
theorem constantExtensionBasis_apply (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    constantExtensionBasis hex h C b i = algebraMap F F' (b i) :=
  Module.Basis.mk_apply _ _ i

end TauCeti
