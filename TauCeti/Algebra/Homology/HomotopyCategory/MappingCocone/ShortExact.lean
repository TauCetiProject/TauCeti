/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.Basic

/-!
# The connecting map of the mapping cocone of an epimorphism

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence `S` of cochain complexes in an abelian
category. The first map lifts to the mapping cocone of the second,
`ℓ : X₁ ⟶ mappingCocone S.g`, and this lift is a quasi-isomorphism
(`CochainComplex.mappingCocone.quasiIso_lift_of_shortExact`). This file proves that `ℓ` also
carries the connecting map of the short exact sequence to the connecting map of the cocone, with
no sign.

The connecting map of the cocone `mappingCocone φ` of `φ : K ⟶ L` is the map on cohomology
`H^n(L) ⟶ H^(n+1)(mappingCocone φ)` induced by the third morphism `L ⟶ (mappingCocone φ)⟦1⟧` of
the triangle `CochainComplex.mappingCocone.triangle φ`. In components this morphism is the
inclusion `CochainComplex.mappingCocone.inr φ`, a cocycle of degree `1`, so the connecting map
sends the class of a cocycle `b` of `L` to the class of `inr b`
(`CochainComplex.mappingCocone.liftCycles_homologyπ_shiftMap_triangle_mor₃`).

For the short exact sequence, let `b` be a cocycle of `X₃`, `b'` a lift of `b` to `X₂` and `a` the
cocycle of `X₁` with `S.f a = d b'`, so that the connecting map of `S` sends `[b]` to `[a]`. In the
cocone, `d(inl b') = inl(d b') - inr(S.g b') = ℓ a - inr b`
(`CochainComplex.mappingCocone.inl_v_d`). Hence `ℓ a` and `inr b` are cohomologous, and

`ℓ_* (δ_S [b]) = [inr b]`

(`CochainComplex.mappingCocone.δ_comp_homologyMap_lift`). In the relative coordinates
`(a, b) ↦ inl a - inr b` of `CochainComplex.mappingCocone.relativeCoordinates`, the cocycle
`inr b` is `(0, -b)` (`CochainComplex.mappingCocone.relativeCoordinates_inr_v`), so its class is
`-[(0, b)]`. Hence for a surjection of complexes, such as the restriction of cochains to a
subspace, the lift identifies the connecting map of the sequence with the connecting map
`δ [b] = -[(0, b)]` of the relative complex. Equivalently, the long exact homology sequence of the
triangle `mappingCocone.triangle S.g` in the homotopy category has connecting map the connecting
map of `S` followed by `ℓ_*` (`CochainComplex.mappingCocone.homologySequenceδ_triangle`).

This is dual to Mathlib's `CochainComplex.mappingCone.homologySequenceδ_triangleh`, which compares
the mapping cone of the monomorphism `S.f` with `X₃`.

## Main results

* `CochainComplex.mappingCocone.liftCycles_homologyπ_shiftMap_triangle_mor₃`: the connecting map
  of the cocone sends `[b]` to `[inr b]`.
* `CochainComplex.mappingCocone.liftCycles_homologyπ_δ_homologyMap_lift`,
  `CochainComplex.mappingCocone.δ_comp_homologyMap_lift`: the lift `ℓ` carries the connecting map
  of `S` to the connecting map of the cocone.
* `CochainComplex.mappingCocone.homologySequenceδ_triangle`: the same statement for the homology
  sequence of the triangle in the homotopy category.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer, 1982, Chapter I, §6 (the relative de Rham complex as a mapping cocone
  and its connecting map).
-/

public section

open CategoryTheory Category Limits HomologicalComplex Preadditive

namespace CochainComplex.mappingCocone

open HomComplex

section Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- The connecting map of the mapping cocone, the map on cohomology induced by the third morphism
of `mappingCocone.triangle φ`, sends the class of a cocycle `x` of `L` to the class of
`x ≫ inr φ`. -/
@[reassoc]
lemma liftCycles_homologyπ_shiftMap_triangle_mor₃ {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    {A : C} (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (x : A ⟶ L.X n₀) (hx : x ≫ L.d n₀ n₁ = 0) :
    L.liftCycles x n₁ (by simp [h]) hx ≫ L.homologyπ n₀ ≫
        (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
          (triangle φ).mor₃ n₀ n₁ (by lia) =
      (mappingCocone φ).liftCycles (x ≫ (inr φ).val.v n₀ n₁ h) (n₁ + 1) (by simp)
          (comp_inr_v_d_eq_zero φ n₀ n₁ (n₁ + 1) h rfl x hx) ≫
        (mappingCocone φ).homologyπ n₁ := by
  dsimp [Functor.shiftMap, homologyFunctor_shift]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    (mappingCocone φ).liftCycles_shift_homologyπ_assoc _ _ _ _ n₁ (by lia) (n₁ + 1) (by simp),
    Iso.inv_hom_id_app]
  simp only [assoc, triangle_mor₃_f_shiftFunctorObjXIso_hom φ n₀ n₁ h]
  -- The identity is that of `((homologyFunctor C _ 0).shift n₁).obj _`, which is the homology
  -- of the cocone only up to unfolding `homologyFunctor_shift`.
  erw [comp_id]

variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
include hS

/-- For a short exact sequence `S`, the lift `S.X₁ ⟶ mappingCocone S.g` of `S.f` carries the
connecting map of `S` to the connecting map of the cocone: the image of `δ [x]` is the class of
`x ≫ inr S.g`. -/
@[reassoc]
lemma liftCycles_homologyπ_δ_homologyMap_lift {A : C} (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (x : A ⟶ S.X₃.X n₀) (hx : x ≫ S.X₃.d n₀ n₁ = 0) :
    S.X₃.liftCycles x n₁ (by simp [h]) hx ≫ S.X₃.homologyπ n₀ ≫ hS.δ n₀ n₁ h ≫
        HomologicalComplex.homologyMap (lift S.g S.f 0 (by simp)) n₁ =
      (mappingCocone S.g).liftCycles (x ≫ (inr S.g).val.v n₀ n₁ h) (n₁ + 1) (by simp)
          (comp_inr_v_d_eq_zero S.g n₀ n₁ (n₁ + 1) h rfl x hx) ≫
        (mappingCocone S.g).homologyπ n₁ := by
  have hS₀ := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n₀
  have hS₁ := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n₁
  have : Epi (S.g.f n₀) := hS₀.epi_g
  have : Mono (S.map (eval C (ComplexShape.up ℤ) n₁)).f := hS₁.mono_f
  -- Lift `x` to `x₂` in `S.X₂` after a refinement `π`, and write `d x₂ = S.f x₁`.
  obtain ⟨A', π, hπ, x₂, hx₂⟩ := surjective_up_to_refinements_of_epi (S.g.f n₀) x
  have hdx₂ : (x₂ ≫ S.X₂.d n₀ n₁) ≫ S.g.f n₁ = 0 := by
    rw [assoc, ← S.g.comm, ← reassoc_of% hx₂, hx, comp_zero]
  let x₁ : A' ⟶ S.X₁.X n₁ := hS₁.exact.lift (x₂ ≫ S.X₂.d n₀ n₁) hdx₂
  have hx₁ : x₁ ≫ S.f.f n₁ = x₂ ≫ S.X₂.d n₀ n₁ := hS₁.exact.lift_f _ hdx₂
  -- In the cocone, `ℓ x₁ = π ≫ x ≫ inr + d (inl x₂)`.
  have key : x₁ ≫ (lift S.g S.f 0 (by simp)).f n₁ =
      (π ≫ x) ≫ (inr S.g).val.v n₀ n₁ h +
        (x₂ ≫ (inl S.g).v n₀ n₀ (add_zero n₀)) ≫ (mappingCocone S.g).d n₀ n₁ := by
    apply ext_to S.g n₁ n₀ (by lia)
    · simp [inl_v_d S.g n₀ n₁ h, hx₁]
    · simp [inl_v_d S.g n₀ n₁ h, reassoc_of% hx₂]
  rw [← cancel_epi π, HomologicalComplex.comp_liftCycles_assoc,
    reassoc_of% (hS.δ_eq n₀ n₁ h (π ≫ x) _ x₂ hx₂.symm x₁ hx₁ (n₁ + 1) (by simp)),
    HomologicalComplex.homologyπ_naturality, HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    HomologicalComplex.comp_liftCycles_assoc]
  -- The two cycles differ by the boundary of `inl x₂`.
  have hπx : (π ≫ x) ≫ S.X₃.d n₀ n₁ = 0 := by rw [assoc, hx, comp_zero]
  have hsplit : (mappingCocone S.g).liftCycles (x₁ ≫ (lift S.g S.f 0 (by simp)).f n₁) (n₁ + 1)
        (by simp) (by rw [key, add_comp, comp_inr_v_d_eq_zero S.g n₀ n₁ (n₁ + 1) h rfl _ hπx,
          zero_add, assoc, d_comp_d, comp_zero]) =
      (mappingCocone S.g).liftCycles ((π ≫ x) ≫ (inr S.g).val.v n₀ n₁ h) (n₁ + 1) (by simp)
          (comp_inr_v_d_eq_zero S.g n₀ n₁ (n₁ + 1) h rfl _ hπx) +
        (mappingCocone S.g).liftCycles
          ((x₂ ≫ (inl S.g).v n₀ n₀ (add_zero n₀)) ≫ (mappingCocone S.g).d n₀ n₁) (n₁ + 1)
          (by simp) (by rw [assoc, d_comp_d, comp_zero]) := by
    rw [← cancel_mono ((mappingCocone S.g).iCycles n₁)]
    simp only [add_comp, HomologicalComplex.liftCycles_i, key]
  rw [hsplit, add_comp, HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _
    (x₂ ≫ (inl S.g).v n₀ n₀ (add_zero n₀)) rfl, add_zero]
  simp only [assoc]

/-- For a short exact sequence `S`, the lift `S.X₁ ⟶ mappingCocone S.g` of `S.f` carries the
connecting map of `S` to the connecting map of the cocone, the map on cohomology induced by the
third morphism of `mappingCocone.triangle S.g`. -/
theorem δ_comp_homologyMap_lift (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    hS.δ n₀ n₁ h ≫ HomologicalComplex.homologyMap (lift S.g S.f 0 (by simp)) n₁ =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (triangle S.g).mor₃ n₀ n₁ (by lia) := by
  rw [← cancel_epi (S.X₃.homologyπ n₀)]
  have hid : 𝟙 (S.X₃.cycles n₀) =
      S.X₃.liftCycles (S.X₃.iCycles n₀) n₁ (by simp [h]) (by simp) := by
    rw [← cancel_mono (S.X₃.iCycles n₀), HomologicalComplex.liftCycles_i, id_comp]
  rw [← id_comp (S.X₃.homologyπ n₀), hid, assoc, assoc,
    liftCycles_homologyπ_δ_homologyMap_lift hS n₀ n₁ h,
    liftCycles_homologyπ_shiftMap_triangle_mor₃]

/-- The connecting map of the homology sequence of the triangle `mappingCocone.triangle S.g` in
the homotopy category is the connecting map of the short exact sequence `S` followed by the lift
`S.X₁ ⟶ mappingCocone S.g`. This is dual to Mathlib's
`CochainComplex.mappingCone.homologySequenceδ_triangleh`. -/
lemma homologySequenceδ_triangle (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj (triangle S.g))
          n₀ n₁ h =
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n₀).hom.app _ ≫
        hS.δ n₀ n₁ h ≫ HomologicalComplex.homologyMap (lift S.g S.f 0 (by simp)) n₁ ≫
          (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) n₁).inv.app _ := by
  rw [homologySequenceδ_quotient_mapTriangle_obj, reassoc_of% δ_comp_homologyMap_lift hS n₀ n₁ h]
  -- The two sides differ only in writing `(triangle S.g).obj₃` and `.obj₁` for `S.X₃` and the
  -- mapping cocone, which `mappingCocone.triangle` unfolds to.
  rfl

end Abelian

end CochainComplex.mappingCocone
