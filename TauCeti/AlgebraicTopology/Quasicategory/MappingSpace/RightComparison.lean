/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.FullyFaithful
import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.Realization
import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Cylinder


/-!
# The comparison of right mapping spaces with two-sided mapping spaces

For vertices `x` and `y` of a quasicategory `X`, the comparison monomorphism
`Hom^R_X(x, y) ⟶ Hom_X(x, y)` of `TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.Basic`
(`SSet.rightMappingSpace.toMappingSpace`) is a weak homotopy equivalence. Consequently a map of
quasicategories is fully faithful, a condition stated on right mapping spaces, exactly when it
induces weak equivalences of the two-sided mapping spaces.

## Proof

The slice `X_{/y}` is modelled by the simplicial set `C` of simplices of `X` with last vertex
`y`, on which simplicial operators act on all vertices but the last one. Its projection
`p : C ⟶ X` to the face opposite to the last vertex is a right fibration, since `C` is isomorphic
over `X` to the slice, and the fibre of `p` over `x` is `Hom^R_X(x, y)`. The space `C` contracts
onto the identity of `y`: the contraction `h : C ⊗ Δ[1] ⟶ C` sends `(σ, e)` to the restriction of
`σ` along the self-map of `Δ[n + 1]` which fixes the vertices `i ≤ n` with `e i = 0` and sends the
other vertices to the last one. Through `h`, the comparison map sends `s` to the path
`σ ↦ p (h (s, σ))` from `s` to the identity of `y`.

A homotopy inverse `r : Hom_X(x, y) ⟶ Hom^R_X(x, y)` comes from a lift. The pushout-product of the
comparison map with the inclusion `{1} ⟶ Δ[1]` is right anodyne, so the uncurried inclusion
`Hom_X(x, y) ⊗ Δ[1] ⟶ X` lifts along `p` to a map `L : Hom_X(x, y) ⊗ Δ[1] ⟶ C` which is constant at
the identity of `y` on `Hom_X(x, y) ⊗ {1}` and is the contraction on `Hom^R_X(x, y) ⊗ Δ[1]`. Its
start `r = L (-, 0)` lies over `x`, and `r` is a retraction of the comparison map. A homotopy from
the identity of `Hom_X(x, y)` to the comparison map after `r` is
`(σ, γ, τ) ↦ p (h (L (γ, σ), min σ τ))`: at `τ = 1` it is `p (h (L (γ, σ), σ))`, which only depends
on `L (γ, 0)`, because `h (-, e)` forgets the vertices `i` with `e i = 1`.

## Main results

* `SSet.rightMappingSpace.isWeakHomotopyEquivalence_toMappingSpace`: for a quasicategory, the
  comparison `Hom^R_X(x, y) ⟶ Hom_X(x, y)` is a weak homotopy equivalence.
* `SSet.isFullyFaithful_iff_weakEquivalence_mappingSpace_map`: a map of quasicategories is fully
  faithful exactly when it induces weak equivalences of the two-sided mapping spaces.

## References

* J. Lurie, *Higher Topos Theory*, §4.2.1 (the comparison of the mapping spaces).
* J. Lurie, *Kerodon*, Section 4.6 (morphism spaces of `∞`-categories).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite Simplicial
  SimplexCategory

universe u

namespace SSet

variable {X : SSet.{u}}

namespace rightMappingSpace

variable {x y : X _⦋0⦌}

open prodStdSimplex in
/-- **The comparison map through the contraction**: the comparison
`Hom^R_X(x, y) ⟶ Hom_X(x, y)` sends a simplex `s` to the path from `s` to the identity of `y`
traced by the contraction, projected to `X`. -/
private lemma toMappingSpace_comp_ι :
    toMappingSpace x y ≫ (X.mappingSpace x y).ι = curry ((β_ Δ[1] _).hom ≫
      toConeSpace x y ▷ Δ[1] ≫ coneContraction y ≫ coneπ X y) := by
  ext ⟨⟨n⟩⟩ s
  -- State the goal on simplices, where `ihomObjEquiv` applies.
  change ((toMappingSpace x y).app _ s).val = (curry ((β_ Δ[1] _).hom ≫
      toConeSpace x y ▷ Δ[1] ≫ coneContraction y ≫ coneπ X y)).app _ s
  apply (ihomObjEquiv _ X).injective
  refine (ihomObjEquiv_toMappingSpace_app_coe s).trans ?_
  rw [ihomObjEquiv_apply, ← yonedaEquiv_symm_comp, ← curry_natural_left, uncurry_curry]
  ext ⟨⟨m⟩⟩ ⟨e, f⟩
  -- Expose only the product/composition wrappers; keep both cone maps behind their API.
  change _ = (coneπ X y).app _ ((coneContraction y).app _
    ((toConeSpace x y).app _ ((yonedaEquiv.symm s).app _ f), e))
  rw [coneπ_app]
  refine Eq.trans ?_ (congrArg (fun σ ↦ X.map (joinVertexInl ⦋m⦌).op σ)
    (coneContraction_app_val y (n := m)
      ((toConeSpace x y).app _ ((yonedaEquiv.symm s).app _ f), e))).symm
  have hr : ((toConeSpace x y).app _ ((yonedaEquiv.symm s).app _ f)).val =
      X.map (joinVertex.map (stdSimplex.objEquiv f)).op s.val :=
    (toConeSpace_app_val _).trans (congrArg Subtype.val (yonedaEquiv_symm_app s f))
  refine (yonedaEquiv_symm_app (S := X) (n := ⦋n + 1⦌) s.val
    ((toJoinVertex n).app (op ⦋m⦌) (e, f))).trans ?_
  refine Eq.trans ?_ (congrArg (fun σ ↦ X.map (joinVertexInl ⦋m⦌).op
    (X.map (joinVertexCollapse (stdSimplex.objEquiv e)).op σ)) hr.symm)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine congrArg (fun g : ⦋m⦌ ⟶ ⦋n + 1⦌ ↦ X.map g.op s.val) ?_
  rw [joinVertexInl_mk]
  ext i : 3
  have hi : (SimplexCategory.δ (Fin.last (m + 1))).toOrderHom i = i.castSucc :=
    Fin.succAbove_last_apply i
  refine (toJoinVertex_app_apply n (e, f) i).trans ?_
  -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
  change _ = (joinVertex.map (stdSimplex.objEquiv f)).toOrderHom
    ((joinVertexCollapse (stdSimplex.objEquiv e)).toOrderHom ((SimplexCategory.δ (Fin.last (m +
      1))).toOrderHom i))
  rw [hi, joinVertexCollapse_castSucc, toJoinVertexOrderHom_apply]
  rw [stdSimplex.objEquiv_toOrderHom_apply e i]
  by_cases h : e i = 0
  · simp only [h, ↓reduceIte]
    exact (joinVertex_map_castSucc _ i).symm
  · simp only [h, ↓reduceIte]
    exact (joinVertex_map_last _).symm

/-- **The contraction forgets the part of a family which is collapsed.** For a family `G` of
simplices of `coneSpace X y` parametrized by `Z ⊗ Δ[1]`, contracting `G (z, e)` along `e`, or the
value `G (z, 0)` at the start of the path, gives the same result. -/
@[reassoc]
private lemma lift_snd_coneContraction {Z : SSet.{u}} (G : Z ⊗ Δ[1] ⟶ (coneSpace X y : SSet.{u})) :
    lift G (snd _ _) ≫ coneContraction y =
      lift (fst _ _ ≫ ι₀ ≫ G) (snd _ _) ≫ coneContraction y := by
  ext ⟨⟨n⟩⟩ ⟨z, e⟩ : 4
  apply Subtype.ext
  -- Evaluate the products and compositions; the contraction itself is rewritten by its API.
  change ((coneContraction y).app _ (G.app _ (z, e), e)).val =
    ((coneContraction y).app _ (G.app _ (ι₀.app _ z), e)).val
  refine (coneContraction_app_val y (n := n) (G.app _ (z, e), e)).trans
    (Eq.trans ?_ (coneContraction_app_val y (n := n) (G.app _ (ι₀.app _ z), e)).symm)
  obtain ⟨k, rfl⟩ := stdSimplex.objMk₁_surjective e
  induction k using Fin.cases with
  | zero =>
    rw [stdSimplex.objEquiv_objMk₁_zero, joinVertexCollapse_const_one, op_comp,
      Functor.map_comp_apply,
      Functor.map_comp_apply]
    -- Simplices of `joinVertex.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map _ (X.map (joinVertexInr ⦋n⦌).op (G.app _ (z, _)).val) =
      X.map _ (X.map (joinVertexInr ⦋n⦌).op (G.app _ (ι₀.app _ z)).val)
    rw [show X.map (joinVertexInr ⦋n⦌).op (G.app _ (z, _)).val = y from
        (mem_coneSpace_obj_iff y _).1 (G.app _ _).property,
      show X.map (joinVertexInr ⦋n⦌).op (G.app _ (ι₀.app _ z)).val = y from
        (mem_coneSpace_obj_iff y _).1 (G.app _ _).property]
  | succ j =>
    rw [← stdSimplex.joinVertexCollapse_comp_joinVertex_map_minRetraction j, op_comp,
      Functor.map_comp_apply,
      Functor.map_comp_apply]
    congr 1
    have h₁ := congrArg Subtype.val (NatTrans.naturality_apply G (minRetraction j).op
      (show (Z ⊗ Δ[1] : SSet.{u}) _⦋n⦌ from (z, stdSimplex.objMk₁ j.succ)))
    have h₂ := congrArg Subtype.val (NatTrans.naturality_apply G (minRetraction j).op (ι₀.app _ z))
    refine h₁.symm.trans (Eq.trans ?_ h₂)
    congr 2
    refine Prod.ext rfl (stdSimplex.objEquiv.injective
      ((stdSimplex.minRetraction_comp_objMk₁.{u} j).trans ?_))
    ext i : 3
    simp only [stdSimplex.objEquiv_toOrderHom_apply, SimplexCategory.const_apply]
    -- Restriction of a constant interval simplex is still constant.
    exact ((congrArg (fun e : Δ[1] _⦋n⦌ ↦ e i)
      (SSet.prod_map_snd Z Δ[1] (minRetraction j).op (ι₀.app _ z))).trans
        (SSet.ι₀_app_snd_apply z _)).symm

section comparison

variable (x y)

variable [X.Quasicategory]

/-- The covering homotopy extension property supplies a lift of the path family, extending
its constant endpoint and the restricted cone contraction. -/
private lemma exists_pathLift :
    ∃ L : (X.mappingSpace x y : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X y : SSet.{u}),
      ι₁ ≫ L = SSet.const (coneVertex y) ∧
      toMappingSpace x y ▷ Δ[1] ≫ L = toConeSpace x y ▷ Δ[1] ≫ coneContraction y ∧
      L ≫ coneπ X y = (β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι := by
  apply exists_lift_cylinder_ι₁_of_mono
  · rw [const_coneVertex_coneπ, mappingSpace.ι₁_braiding_uncurry_ι]
  · rw [BraidedCategory.braiding_naturality_left_assoc, ← uncurry_natural_left,
      toMappingSpace_comp_ι, uncurry_curry, SymmetricCategory.symmetry_assoc, Category.assoc]
  · rw [ι₁_comp_assoc, ι₁_coneContraction, comp_const, comp_const]

/-- A lift of the path family along the cone projection, extending the contraction. -/
private noncomputable def pathLift :
    (X.mappingSpace x y : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X y : SSet.{u}) :=
  (exists_pathLift x y).choose

@[reassoc]
private lemma pathLift_coneπ :
    pathLift x y ≫ coneπ X y = (β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι :=
  (exists_pathLift x y).choose_spec.2.2

@[reassoc]
private lemma ι₁_pathLift : ι₁ ≫ pathLift x y = SSet.const (coneVertex y) :=
  (exists_pathLift x y).choose_spec.1

@[reassoc]
private lemma whiskerRight_pathLift :
    toMappingSpace x y ▷ Δ[1] ≫ pathLift x y = toConeSpace x y ▷ Δ[1] ≫ coneContraction y :=
  (exists_pathLift x y).choose_spec.2.1

/-- The homotopy inverse `Hom_X(x, y) ⟶ Hom^R_X(x, y)` of the comparison map: the start of the
lifted path. -/
private noncomputable def inverse :
    (X.mappingSpace x y : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}) :=
  fiber.lift (ι₀ ≫ pathLift x y) (coneπ X y) x
    (by rw [Category.assoc, pathLift_coneπ, mappingSpace.ι₀_braiding_uncurry_ι]) ≫
      (coneFiberIso x y).hom

@[reassoc]
private lemma inverse_toConeSpace : inverse x y ≫ toConeSpace x y = ι₀ ≫ pathLift x y := by
  rw [inverse, Category.assoc, coneFiberIso_hom_toConeSpace, fiber.lift_ι]

private lemma toMappingSpace_inverse : toMappingSpace x y ≫ inverse x y = 𝟙 _ := by
  rw [← cancel_mono (toConeSpace x y), Category.assoc, inverse_toConeSpace, ← ι₀_comp_assoc,
    whiskerRight_pathLift, ι₀_comp_assoc, ι₀_coneContraction, Category.comp_id, Category.id_comp]

/-- The uncurried homotopy from the identity of `Hom_X(x, y)` to `inverse ≫ toMappingSpace`:
`(σ, γ, τ)` goes to the contraction at time `min σ τ` of the lifted path at time `σ`. -/
private noncomputable def homotopyAux : Δ[1] ⊗ ((X.mappingSpace x y : SSet.{u}) ⊗ Δ[1]) ⟶ X :=
  lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
    (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contraction 1).h) ≫
      coneContraction y ≫ coneπ X y

private lemma range_curry_homotopyAux_le :
    Subcomplex.range (curry (homotopyAux x y)) ≤ X.mappingSpace x y := by
  rw [range_le_mappingSpace_iff, uncurry_curry]
  constructor
  · -- At `σ = 0`, the lifted path is at its start, which lies over `x`, and is not contracted.
    have e : stdSimplex.δ 1 ▷ _ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
        (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contraction 1).h) =
        (snd _ _ ≫ fst _ _ ≫ ι₀ ≫ pathLift x y) ≫ ι₀ := by
      rw [← lift_const_zero_eq_comp_ι₀]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [Category.assoc, lift_fst]
        have h : stdSimplex.δ 1 ▷ ((X.mappingSpace x y : SSet.{u}) ⊗ Δ[1]) ≫
            lift (snd _ _ ≫ fst _ _) (fst _ _) = snd _ _ ≫ fst _ _ ≫ ι₀ :=
          CartesianMonoidalCategory.hom_ext _ _ (by simp)
            (by simp [stdSimplex.δ_one_eq_const, comp_const])
        rw [reassoc_of% h]
      · simp only [Category.assoc, lift_snd]
        rw [← Category.assoc, comp_lift, whiskerRight_fst, whiskerRight_snd_assoc,
          stdSimplex.δ_one_eq_const, comp_const, stdSimplex.lift_const_zero_contraction_h]
    rw [homotopyAux, reassoc_of% e, ι₀_coneContraction_assoc]
    simp only [pathLift_coneπ, mappingSpace.ι₀_braiding_uncurry_ι, comp_const]
  · -- At `σ = 1`, the lifted path is at the identity of `y`, which the contraction fixes.
    have e : stdSimplex.δ 0 ▷ _ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
        (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contraction 1).h) =
        lift (SSet.const (coneVertex y)) (stdSimplex.δ 0 ▷ _ ≫
          lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contraction 1).h) := by
      rw [comp_lift, ← Category.assoc, comp_lift, whiskerRight_fst, whiskerRight_snd_assoc,
        stdSimplex.δ_zero_eq_const, comp_const, lift_const_one_eq_comp_ι₁, Category.assoc,
        Category.assoc, ι₁_pathLift]
      simp only [comp_const]
    rw [homotopyAux, reassoc_of% e, lift_const_coneVertex_coneContraction_assoc,
      const_coneVertex_coneπ]

/-- **The homotopy from the identity of `Hom_X(x, y)` to `inverse ≫ toMappingSpace`.** -/
private noncomputable def homotopy :
    Homotopy (𝟙 (X.mappingSpace x y : SSet.{u})) (inverse x y ≫ toMappingSpace x y) :=
  Homotopy.mk' (Subcomplex.lift _ (range_curry_homotopyAux_le x y))
    (by
      rw [← cancel_mono (X.mappingSpace x y).ι, Category.assoc, Subcomplex.lift_ι,
        Category.id_comp, ← curry_natural_left, curry_eq_iff]
      have e : (Δ[1] : SSet.{u}) ◁ ι₀ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
          (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contraction 1).h) =
          ((β_ _ _).hom ≫ pathLift x y) ≫ ι₀ := by
        rw [← lift_const_zero_eq_comp_ι₀, comp_lift, ← Category.assoc,
          whiskerLeft_comp_lift_snd_fst _ (ι₀_fst _), ← Category.assoc, comp_lift, whiskerLeft_fst,
          whiskerLeft_snd_assoc, ι₀_snd, comp_const, lift_const_zero_eq_comp_ι₀, Category.assoc,
          (stdSimplex.contraction 1).h₀, comp_const]
      rw [homotopyAux, reassoc_of% e, ι₀_coneContraction_assoc, pathLift_coneπ,
        SymmetricCategory.symmetry_assoc])
    (by
      rw [← cancel_mono (X.mappingSpace x y).ι, Category.assoc, Subcomplex.lift_ι,
        Category.assoc, toMappingSpace_comp_ι, ← curry_natural_left, ← curry_natural_left]
      congr 1
      have e : (Δ[1] : SSet.{u}) ◁ ι₁ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
          (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contraction 1).h) =
          (β_ _ _).hom ≫ lift (pathLift x y) (snd _ _) := by
        rw [comp_lift, comp_lift, ← Category.assoc, whiskerLeft_comp_lift_snd_fst _ (ι₁_fst _),
          ← Category.assoc, comp_lift, whiskerLeft_fst, whiskerLeft_snd_assoc, ι₁_snd,
          comp_const, lift_const_one_eq_comp_ι₁, Category.assoc,
          (stdSimplex.contraction 1).h₁, Category.comp_id, braiding_hom_snd]
      have e' : lift (fst _ _ ≫ ι₀ ≫ pathLift x y) (snd _ _) =
          inverse x y ▷ Δ[1] ≫ toConeSpace x y ▷ Δ[1] := by
        rw [← comp_whiskerRight, inverse_toConeSpace]
        exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
      rw [homotopyAux, reassoc_of% e, lift_snd_coneContraction_assoc, e',
        BraidedCategory.braiding_naturality_right_assoc]
      simp only [Category.assoc])

/-- **The comparison of right mapping spaces is a weak homotopy equivalence** (HTT, §4.2.1):
for a quasicategory `X`, the comparison map `Hom^R_X(x, y) ⟶ Hom_X(x, y)` is a weak homotopy
equivalence. -/
instance isWeakHomotopyEquivalence_toMappingSpace :
    IsWeakHomotopyEquivalence (toMappingSpace x y) := by
  obtain ⟨H⟩ := Homotopy.nonempty_symm (homotopy x y)
  exact IsWeakHomotopyEquivalence.of_homotopy _ (g := inverse x y)
    (RelativeMorphism.Homotopy.ofEq
      (congrArg RelativeMorphism.botEquiv.symm (toMappingSpace_inverse x y))) H

end comparison

end rightMappingSpace

section IsFullyFaithful

open HomotopicalAlgebra

open scoped modelCategoryQuillen

variable {Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]

/-- **Full faithfulness on two-sided mapping spaces**: a map of quasicategories is fully faithful
exactly when it induces weak equivalences `Hom_X(x, y) ⟶ Hom_Y(f x, f y)` of the two-sided
mapping spaces. -/
theorem isFullyFaithful_iff_weakEquivalence_mappingSpace_map (f : X ⟶ Y) :
    IsFullyFaithful f ↔ ∀ x y : X _⦋0⦌, WeakEquivalence (mappingSpace.map x y f) := by
  have key (x y : X _⦋0⦌) :
      WeakEquivalence (rightMappingSpace.map x y f) ↔ WeakEquivalence (mappingSpace.map x y f) := by
    have := modelCategoryQuillen.weakEquivalence_of_isWeakHomotopyEquivalence
      (rightMappingSpace.toMappingSpace x y)
    have := modelCategoryQuillen.weakEquivalence_of_isWeakHomotopyEquivalence
      (rightMappingSpace.toMappingSpace (f.app _ x) (f.app _ y))
    rw [← weakEquivalence_precomp_iff (rightMappingSpace.toMappingSpace x y)
      (mappingSpace.map x y f), rightMappingSpace.toMappingSpace_comp_map,
      weakEquivalence_postcomp_iff]
  exact ⟨fun _ x y ↦ (key x y).1 inferInstance, fun h ↦ ⟨fun x y ↦ (key x y).2 (h x y)⟩⟩

end IsFullyFaithful

end SSet
