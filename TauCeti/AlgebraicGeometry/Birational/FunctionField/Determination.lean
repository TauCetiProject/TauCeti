/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.FunctionField.BaseAlgebra

/-!
# Dominant rational maps are determined by their pullback of function fields

Let `k` be a commutative ring and `X`, `Y` integral `k`-schemes with `Y` locally of finite type
over `k`. Every `k`-algebra homomorphism `φ : k(Y) → k(X)` is the pullback of rational functions
along a dominant `k`-rational map `X ⤏ Y`
(`AlgebraicGeometry.Scheme.RationalMap.exists_functionFieldAlgHom_eq`), and that map is unique
(`AlgebraicGeometry.Scheme.RationalMap.eq_of_functionFieldMap_eq`). So `f ↦ f^*` is a bijection
between dominant `k`-rational maps `X ⤏ Y` and `k`-algebra maps `k(Y) → k(X)`.

The rational map is Mathlib's `Scheme.RationalMap.ofFunctionField` of the `k`-morphism
`Spec φ ≫ (Spec k(Y) ⟶ Y)` from `Spec k(X)`, which is defined because `Y` is locally of finite
type. It is dominant because it sends the generic point of `X` into the image of
`Spec k(Y) ⟶ Y`, whose only point is the generic point of `Y`
(`AlgebraicGeometry.Scheme.RationalMap.isDominant_of_fromFunctionField_eq`).

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.isDominant_of_fromFunctionField_eq`: a rational map whose
  restriction to `Spec K(X)` factors through `Spec K(Y)` is dominant.
* `AlgebraicGeometry.Scheme.RationalMap.exists_functionFieldAlgHom_eq`: **determination**, every
  `k`-algebra map of function fields is the pullback along a dominant `k`-rational map.
* `AlgebraicGeometry.Scheme.RationalMap.existsUnique_functionFieldAlgHom_eq`: and only one.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- **A rational map whose restriction to `Spec K(X)` factors through `Spec K(Y)` is dominant.**
If `f.fromFunctionField = Spec φ ≫ (Spec K(Y) ⟶ Y)` for a ring map `φ : K(Y) ⟶ K(X)`, then `f`
sends the generic point of `X` into the image of `Spec K(Y)`, whose only point is the generic
point of `Y`. -/
theorem RationalMap.isDominant_of_fromFunctionField_eq [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⤏ Y) (φ : Y.functionField ⟶ X.functionField)
    (h : f.fromFunctionField = Spec.map φ ≫ Y.fromSpecStalk (genericPoint Y)) : f.IsDominant := by
  obtain ⟨g, rfl⟩ := f.exists_rep
  rw [PartialMap.isDominant_toRationalMap_iff]
  have : Nonempty g.domain := g.dense_domain.nonempty.to_subtype
  have : IrreducibleSpace g.domain := g.domain.ι.isOpenEmbedding.irreducibleSpace
  have hη := g.genericPoint_mem_domain
  -- The closed point of `Spec K(X)` goes to the generic point of the domain.
  have hp : g.domain.fromSpecStalkOfMem (genericPoint X) hη (IsLocalRing.closedPoint _) =
      genericPoint g.domain := g.domain.ι.isOpenEmbedding.injective <|
    (Scheme.Hom.comp_apply _ _ _).symm.trans <|
      congr($(Opens.fromSpecStalkOfMem_ι g.domain _ hη) _).trans <|
        fromSpecStalk_closedPoint.trans g.domain.ι.genericPoint_eq_of_isDominant.symm
  have hf : g.hom (genericPoint g.domain) ∈ Set.range (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨Spec.map φ (IsLocalRing.closedPoint _), (Scheme.Hom.comp_apply _ _ _).symm.trans <|
      congr($h.symm _).trans <| (Scheme.Hom.comp_apply _ _ _).trans (congrArg g.hom hp)⟩
  rw [Scheme.range_fromSpecStalk] at hf
  exact isDominant_iff_genericPoint_eq.mpr (hf.antisymm (genericPoint_specializes _)).eq

variable (k : Type u) [CommRing k] [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsIntegral X]
  [IsIntegral Y] [LocallyOfFiniteType (Y ↘ Spec (.of k))]

/-- **Determination.** For integral `k`-schemes `X` and `Y` with `Y` locally of finite type over
`k`, every `k`-algebra map `φ : k(Y) → k(X)` is the pullback of rational functions along a
dominant `k`-rational map `X ⤏ Y`. -/
theorem RationalMap.exists_functionFieldAlgHom_eq (φ : Y.functionField →ₐ[k] X.functionField) :
    ∃ (f : X ⤏ Y) (_ : f.IsDominant) (_ : f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))),
      f.functionFieldAlgHom k = φ := by
  let g₀ := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
  have hg₀ : g₀ ≫ (Y ↘ Spec (.of k)) = X.fromSpecStalk _ ≫ (X ↘ Spec (.of k)) :=
    (specMap_comp_fromSpecStalk_genericPoint_comp_over_iff k _).2 φ.commutes
  let f := RationalMap.ofFunctionField (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) g₀ hg₀
  have hf : f.fromFunctionField = g₀ := RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have : f.IsDominant := f.isDominant_of_fromFunctionField_eq _ hf
  have : f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) :=
    ((RationalMap.equivFunctionFieldOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))) ⟨g₀, hg₀⟩).property
  refine ⟨f, ‹_›, ‹_›, AlgHom.ext fun a => ?_⟩
  rw [RationalMap.functionFieldAlgHom_apply]
  have := ((RationalMap.eq_functionFieldMap_iff f _).2 hf.symm)
  exact congr($this.symm a)

/-- **Determination, with uniqueness.** For integral `k`-schemes `X` and `Y` with `Y` locally of
finite type over `k`, every `k`-algebra map `φ : k(Y) → k(X)` is the pullback of rational
functions along exactly one dominant `k`-rational map `X ⤏ Y`. -/
theorem RationalMap.existsUnique_functionFieldAlgHom_eq
    (φ : Y.functionField →ₐ[k] X.functionField) :
    ∃! f : X ⤏ Y, ∃ (_ : f.IsDominant) (_ : f.IsOver (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))),
      f.functionFieldAlgHom k = φ := by
  obtain ⟨f, hd, ho, hφ⟩ := exists_functionFieldAlgHom_eq k φ
  refine ⟨f, ⟨hd, ho, hφ⟩, fun g ⟨hd', ho', hφ'⟩ => ?_⟩
  refine RationalMap.eq_of_functionFieldMap_eq (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  have h1 := congr($hφ' a)
  have h2 := congr($hφ a)
  rw [RationalMap.functionFieldAlgHom_apply] at h1 h2
  exact h1.trans h2.symm

end AlgebraicGeometry.Scheme
