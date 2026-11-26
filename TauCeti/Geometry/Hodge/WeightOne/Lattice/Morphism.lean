/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.Morphism
public import TauCeti.Geometry.Hodge.WeightOne.Lattice.Basic

/-!
# Morphisms of weight-one Hodge structures from complex-linear lattice maps

Let `V` and `V'` be integral modules with almost complex structures `J` and `J'` on their
realifications. An integral linear map `f : V → V'` whose real extension `ℝ ⊗ f` is complex
linear for `J` and `J'` complexifies to a map intertwining the transported complex structures
(`TauCeti.AlmostComplexStructure.integralMapToComplex_commutes_latticeComplexification`), so it
carries the `i`-eigenspace of `J` into that of `J'`. It is therefore a morphism of the associated
weight-one Hodge structures `latticeHodgeStructure`
(`TauCeti.AlmostComplexStructure.latticeHodgeHom`).

## Main declarations

* `TauCeti.AlmostComplexStructure.integralMapToComplex_commutes_latticeComplexification`: the
  complexification of such a map intertwines the transported complex structures.
* `TauCeti.AlmostComplexStructure.latticeHodgeHom`: the Hodge morphism
  `latticeHodgeStructure J → latticeHodgeStructure J'` of an integral map with complex-linear real
  extension.
* `TauCeti.AlmostComplexStructure.latticeHodgeHom_id` and
  `TauCeti.AlmostComplexStructure.latticeHodgeHom_comp`: compatibility with identities and
  composites.
-/

public section

namespace TauCeti.AlmostComplexStructure

open scoped TensorProduct

variable {V V' V'' Vℂ Vℂ' Vℂ'' : Type*}
variable [AddCommGroup V] [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable [AddCommGroup V'] [AddCommGroup Vℂ'] [Module ℂ Vℂ']
variable [AddCommGroup V''] [AddCommGroup Vℂ''] [Module ℂ Vℂ'']
variable {ιℂ : V →ₗ[ℤ] Vℂ} {ιℂ' : V' →ₗ[ℤ] Vℂ'} {ιℂ'' : V'' →ₗ[ℤ] Vℂ''}

/-- **Complex-linear lattice maps intertwine the transported complex structures.** If the real
extension of an integral map `f` is complex linear for `J` and `J'`, its complexification
intertwines `latticeComplexification J` and `latticeComplexification J'`. -/
theorem integralMapToComplex_commutes_latticeComplexification
    {J : AlmostComplexStructure (Hodge.Realification V)}
    {J' : AlmostComplexStructure (Hodge.Realification V')} (hℂ : IsBaseChange ℂ ιℂ)
    (hℂ' : IsBaseChange ℂ ιℂ') {f : V →ₗ[ℤ] V'}
    (hf : IsComplexLinearMap J J' (f.baseChange ℝ)) (x : Vℂ) :
    Hodge.integralMapToComplex hℂ ιℂ' f (J.latticeComplexification hℂ x) =
      J'.latticeComplexification hℂ' (Hodge.integralMapToComplex hℂ ιℂ' f x) := by
  obtain ⟨y, rfl⟩ := (Hodge.realificationComplexEquiv hℂ).surjective x
  -- Both sides are `ℂ ⊗ (ℝ ⊗ f)` composed with `ℂ ⊗ J` or `ℂ ⊗ J'`; `hf` swaps the two.
  calc Hodge.integralMapToComplex hℂ ιℂ' f
          (J.latticeComplexification hℂ (Hodge.realificationComplexEquiv hℂ y))
      _ = Hodge.realificationComplexEquiv hℂ'
          ((f.baseChange ℝ ∘ₗ J.toLinearMap).baseChange ℂ y) := by
        rw [← realificationComplexEquiv_baseChange_apply,
          Hodge.integralMapToComplex_realificationComplexEquiv, LinearMap.baseChange_comp,
          LinearMap.comp_apply]
      _ = Hodge.realificationComplexEquiv hℂ'
          ((J'.toLinearMap ∘ₗ f.baseChange ℝ).baseChange ℂ y) := by rw [hf]
      _ = J'.latticeComplexification hℂ'
          (Hodge.integralMapToComplex hℂ ιℂ' f (Hodge.realificationComplexEquiv hℂ y)) := by
        rw [Hodge.integralMapToComplex_realificationComplexEquiv hℂ hℂ',
          ← realificationComplexEquiv_baseChange_apply, LinearMap.baseChange_comp,
          LinearMap.comp_apply]

/-- **The Hodge morphism of a complex-linear lattice map.** An integral linear map `f : V → V'`
whose real extension is complex linear for `J` and `J'` is a morphism of the associated weight-one
Hodge structures. -/
noncomputable def latticeHodgeHom {J : AlmostComplexStructure (Hodge.Realification V)}
    {J' : AlmostComplexStructure (Hodge.Realification V')} (hℂ : IsBaseChange ℂ ιℂ)
    (hℂ' : IsBaseChange ℂ ιℂ') (f : V →ₗ[ℤ] V')
    (hf : IsComplexLinearMap J J' (f.baseChange ℝ)) :
    Hodge.HodgeStructure.Hom (J.latticeHodgeStructure hℂ) (J'.latticeHodgeStructure hℂ') where
  toIntLinearMap := f
  map_mem_F p x hx := by
    rw [latticeHodgeStructure_F] at hx ⊢
    split_ifs at hx ⊢ with h₀ h₁
    · trivial
    · rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [← integralMapToComplex_commutes_latticeComplexification hℂ hℂ' hf, hx, map_smul]
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]

@[simp]
theorem latticeHodgeHom_toIntLinearMap {J : AlmostComplexStructure (Hodge.Realification V)}
    {J' : AlmostComplexStructure (Hodge.Realification V')} (hℂ : IsBaseChange ℂ ιℂ)
    (hℂ' : IsBaseChange ℂ ιℂ') (f : V →ₗ[ℤ] V')
    (hf : IsComplexLinearMap J J' (f.baseChange ℝ)) :
    (latticeHodgeHom hℂ hℂ' f hf).toIntLinearMap = f := by
  rw [latticeHodgeHom]

/-- The identity of `V` has complex-linear real extension for any `J`. -/
theorem isComplexLinearMap_baseChange_id (J : AlmostComplexStructure (Hodge.Realification V)) :
    IsComplexLinearMap J J ((LinearMap.id : V →ₗ[ℤ] V).baseChange ℝ) := by
  rw [LinearMap.baseChange_id]
  exact isComplexLinearMap_id J

/-- A composite of integral maps with complex-linear real extensions has complex-linear real
extension. -/
theorem isComplexLinearMap_baseChange_comp {J : AlmostComplexStructure (Hodge.Realification V)}
    {J' : AlmostComplexStructure (Hodge.Realification V')}
    {J'' : AlmostComplexStructure (Hodge.Realification V'')} {f : V →ₗ[ℤ] V'}
    {g : V' →ₗ[ℤ] V''} (hg : IsComplexLinearMap J' J'' (g.baseChange ℝ))
    (hf : IsComplexLinearMap J J' (f.baseChange ℝ)) :
    IsComplexLinearMap J J'' ((g ∘ₗ f).baseChange ℝ) := by
  rw [LinearMap.baseChange_comp]
  exact hg.comp hf

/-- The identity of `V` is the identity Hodge morphism of `latticeHodgeStructure J`. -/
@[simp]
theorem latticeHodgeHom_id (J : AlmostComplexStructure (Hodge.Realification V))
    (hℂ : IsBaseChange ℂ ιℂ) :
    latticeHodgeHom hℂ hℂ LinearMap.id (isComplexLinearMap_baseChange_id J) =
      Hodge.HodgeStructure.Hom.id _ :=
  Hodge.HodgeStructure.Hom.ext fun _ ↦ by simp

/-- The Hodge morphism of a composite of complex-linear lattice maps is the composite of their Hodge
morphisms. -/
theorem latticeHodgeHom_comp {J : AlmostComplexStructure (Hodge.Realification V)}
    {J' : AlmostComplexStructure (Hodge.Realification V')}
    {J'' : AlmostComplexStructure (Hodge.Realification V'')} (hℂ : IsBaseChange ℂ ιℂ)
    (hℂ' : IsBaseChange ℂ ιℂ') (hℂ'' : IsBaseChange ℂ ιℂ'') {f : V →ₗ[ℤ] V'}
    {g : V' →ₗ[ℤ] V''} (hf : IsComplexLinearMap J J' (f.baseChange ℝ))
    (hg : IsComplexLinearMap J' J'' (g.baseChange ℝ)) :
    latticeHodgeHom hℂ hℂ'' (g ∘ₗ f) (isComplexLinearMap_baseChange_comp hg hf) =
      (latticeHodgeHom hℂ' hℂ'' g hg).comp (latticeHodgeHom hℂ hℂ' f hf) :=
  Hodge.HodgeStructure.Hom.ext fun _ ↦ by simp

end TauCeti.AlmostComplexStructure
