/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis

/-!
# Intermediate extensions after extending constants

For an exact constant field `k` in `F`, a separable algebraic extension `k' / k` preserves
linear independence over every intermediate field `C` of `F / k` after replacing `C` by
`k' · C`. The extension of constants may be infinite. This is the linear-algebraic input
to comparing degrees after adjoining an algebraic closure of the constants.

The spanning result `TauCeti.span_range_basis_of_isAlgebraic_constantCompositum` instead
allows arbitrary new constants when the original relative extension is algebraic.

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

omit [Algebra.IsSeparable k k'] [Algebra k k'] [Algebra k F']
    [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- If the original field generates the ambient field as an algebra over the enlarged
intermediate field, its basis over `C` spans the ambient field over that enlarged field. -/
theorem _root_.IntermediateField.span_range_basis_eq_top_of_adjoin_eq_top
    (C : IntermediateField k F)
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
  exact C.span_range_basis_eq_top_of_adjoin_eq_top b htop

omit [Algebra.IsSeparable k k'] [Algebra k k'] [Algebra k F']
    [IsScalarTower k k' F'] [IsScalarTower k F F'] in
/-- A basis over an intermediate field spans the constant compositum when the original
relative extension is algebraic. The extension of constants is arbitrary. -/
theorem span_range_basis_of_isAlgebraic_constantCompositum
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Submodule.span (IntermediateField.adjoin k' (Set.range (algebraMap C F')))
      (Set.range (algebraMap F F' ∘ b)) = ⊤ := by
  let C' := IntermediateField.adjoin k' (Set.range (algebraMap C F'))
  let g : C →+* C' := (algebraMap C F').codRestrict C'.toSubring fun x =>
    IntermediateField.subset_adjoin k' _ ⟨x, rfl⟩
  let : Algebra C C' := g.toAlgebra
  have : IsScalarTower C C' F' := .of_algebraMap_eq fun _ => rfl
  let f := IsScalarTower.toAlgHom C F F'
  let A := IntermediateField.adjoin C' (Set.range (algebraMap F F'))
  have hle : (constantCompositum F k' F' : Set F') ⊆ A := by
    rw [constantCompositum_def]
    refine (IntermediateField.adjoin_subset_adjoin_iff F).2 ?_
    constructor
    · rintro _ ⟨x, rfl⟩
      exact IntermediateField.subset_adjoin C' _ ⟨x, rfl⟩
    · rintro _ ⟨c, rfl⟩
      rw [IsScalarTower.algebraMap_apply k' C' F' c]
      exact A.algebraMap_mem (algebraMap k' C' c)
  have htop : A = ⊤ := eq_top_iff.mpr fun z _ => hle (by simp [h])
  have halg : ∀ z ∈ Set.range (algebraMap F F'), IsAlgebraic C' z := by
    rintro _ ⟨x, rfl⟩
    have hx : IsAlgebraic C (algebraMap F F' x) :=
      IsAlgebraic.algHom f (Algebra.IsAlgebraic.isAlgebraic (R := C) x)
    exact hx.tower_top C'
  have htop' : (IntermediateField.adjoin C' (Set.range (algebraMap F F'))).toSubalgebra =
      ⊤ := by
    simpa only [A, IntermediateField.top_toSubalgebra] using
      congrArg IntermediateField.toSubalgebra htop
  rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg] at htop'
  exact C.span_range_basis_eq_top_of_adjoin_eq_top b htop'

/-- A basis of `F / C` remains a basis of `F · k' / C · k'` for a separable algebraic extension
of an exact constant field. Neither extension of fields needs to be finite-dimensional. -/
noncomputable def constantExtensionBasis (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (IntermediateField.adjoin k' (Set.range (algebraMap C F'))) F' :=
  have H := linearDisjoint_fieldRange_of_isIntegrallyClosedIn (k' := k') (E := F') hex
  Module.Basis.mk (H.linearIndependent_adjoin_algebraMap_comp C b.linearIndependent)
    (span_range_basis_of_constantCompositum_eq_top h C b).ge

@[simp]
theorem constantExtensionBasis_apply (hex : IsIntegrallyClosedIn k F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    constantExtensionBasis hex h C b i = algebraMap F F' (b i) := by
  simp only [constantExtensionBasis, Module.Basis.mk_apply, Function.comp_apply]

end TauCeti
