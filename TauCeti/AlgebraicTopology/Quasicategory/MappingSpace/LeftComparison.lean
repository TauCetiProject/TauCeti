/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.RightComparison
import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.Realization
import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Cylinder


/-!
# The comparison of left mapping spaces with two-sided mapping spaces

For vertices `x` and `y` of a quasicategory `X`, the comparison monomorphism
`Hom^L_X(x, y) ⟶ Hom_X(x, y)` of `TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.Basic`
(`SSet.leftMappingSpace.toMappingSpace`) is a weak homotopy equivalence. Consequently a map of
quasicategories is fully faithful exactly when it induces weak equivalences of the left mapping
spaces. Together with `TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.RightComparison`,
full faithfulness can be tested on any of the three mapping spaces.

## Proof

The argument is dual to that of
`TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.RightComparison`. The coslice `X_{x/}` is
modelled by the simplicial set `C` of simplices of `X` with initial vertex `x`, on which
simplicial operators act on all vertices but the initial one. Its projection
`p : C ⟶ X` to the face opposite to the initial vertex is a left fibration, since `C` is
isomorphic over `X` to the coslice, and the fibre of `p` over `y` is `Hom^L_X(x, y)`. The
contraction `h : C ⊗ Δ[1] ⟶ C` sends `(σ, e)` to the restriction of `σ` along the self-map of
`Δ[n + 1]` which fixes the vertices `i + 1` with `e i = 1` and sends the other vertices to the
initial one; through `h`, the comparison map sends `s` to the path `σ ↦ p (h (s, σ))` from the
identity of `x` to `s`.

The pushout-product of the comparison map with the inclusion `{0} ⟶ Δ[1]` is left anodyne, so the
uncurried inclusion `Hom_X(x, y) ⊗ Δ[1] ⟶ X` lifts along `p` to a map `L` which is constant at the
identity of `x` on `Hom_X(x, y) ⊗ {0}` and is the contraction on `Hom^L_X(x, y) ⊗ Δ[1]`. Its end
`r = L (-, 1)` is a retraction of the comparison map, and `(σ, γ, τ) ↦ p (h (L (γ, σ), max σ τ))`
is a homotopy from the comparison map after `r` to the identity of `Hom_X(x, y)`.

## Main results

* `SSet.leftMappingSpace.isWeakHomotopyEquivalence_toMappingSpace`: for a quasicategory, the
  comparison `Hom^L_X(x, y) ⟶ Hom_X(x, y)` is a weak homotopy equivalence.
* `SSet.isFullyFaithful_iff_weakEquivalence_leftMappingSpace_map`: a map of quasicategories is
  fully faithful exactly when it induces weak equivalences of the left mapping spaces.

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

namespace leftMappingSpace

variable {x y : X _⦋0⦌}

open prodStdSimplex in
/-- **The comparison map through the contraction**: the comparison
`Hom^L_X(x, y) ⟶ Hom_X(x, y)` sends a simplex `s` to the path from the identity of `x` to `s`
traced by the contraction, projected to `X`. -/
lemma toMappingSpace_comp_ι :
    toMappingSpace x y ≫ (X.mappingSpace x y).ι = curry ((β_ Δ[1] _).hom ≫
      toConeSpace x y ▷ Δ[1] ≫ coneContraction x ≫ coneπ X x) := by
  ext ⟨⟨n⟩⟩ s
  -- State the goal on simplices, where `ihomObjEquiv` applies.
  change ((toMappingSpace x y).app _ s).val = (curry ((β_ Δ[1] _).hom ≫
      toConeSpace x y ▷ Δ[1] ≫ coneContraction x ≫ coneπ X x)).app _ s
  apply (ihomObjEquiv _ X).injective
  refine (ihomObjEquiv_toMappingSpace_app_coe s).trans ?_
  rw [ihomObjEquiv_apply, ← yonedaEquiv_symm_comp, ← curry_natural_left, uncurry_curry]
  ext ⟨⟨m⟩⟩ ⟨e, f⟩
  -- Expose only the product/composition wrappers; keep both cone maps behind their API.
  change _ = (coneπ X x).app _ ((coneContraction x).app _
    ((toConeSpace x y).app _ ((yonedaEquiv.symm s).app _ f), e))
  rw [coneπ_app]
  refine Eq.trans ?_ (congrArg (fun σ ↦ X.map (SimplexCategory.δ (n := m) 0).op σ)
    (coneContraction_app_val x (n := m)
      ((toConeSpace x y).app _ ((yonedaEquiv.symm s).app _ f), e))).symm
  -- Give the base face the join codomain explicitly, so composition rewrites match it.
  let face : ⦋m⦌ ⟶ vertexJoin.obj ⦋m⦌ := SimplexCategory.δ 0
  have hr : ((toConeSpace x y).app _ ((yonedaEquiv.symm s).app _ f)).val =
      X.map (vertexJoin.map (stdSimplex.objEquiv f)).op s.val :=
    (toConeSpace_app_val _).trans (congrArg Subtype.val (yonedaEquiv_symm_app s f))
  refine (yonedaEquiv_symm_app (S := X) (n := ⦋n + 1⦌) s.val
    ((toVertexJoin n).app (op ⦋m⦌) (e, f))).trans ?_
  refine Eq.trans ?_ (congrArg (fun σ ↦ X.map face.op
    (X.map (vertexJoinCollapse (stdSimplex.objEquiv e)).op σ)) hr.symm)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine congrArg (fun g : ⦋m⦌ ⟶ ⦋n + 1⦌ ↦ X.map g.op s.val) ?_
  ext i : 3
  have hi : (SimplexCategory.δ (n := m) 0).toOrderHom i = i.succ := congrFun Fin.succAbove_zero i
  refine (toVertexJoin_app_apply n (e, f) i).trans ?_
  -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
  change _ = (vertexJoin.map (stdSimplex.objEquiv f)).toOrderHom
    ((vertexJoinCollapse (stdSimplex.objEquiv e)).toOrderHom ((SimplexCategory.δ (n := m)
      0).toOrderHom i))
  rw [hi, vertexJoinCollapse_succ, toVertexJoinOrderHom_apply]
  rw [stdSimplex.objEquiv_toOrderHom_apply e i]
  by_cases h : e i = 0
  · simp only [h, ↓reduceIte]
    exact (vertexJoin_map_zero _).symm
  · have h' : e i = 1 := Fin.eq_one_of_ne_zero (e i) h
    simp only [h', ↓reduceIte]
    exact (vertexJoin_map_succ _ i).symm

section comparison

variable (x y)

variable [X.Quasicategory]

/-- The covering homotopy extension property supplies a lift of the path family, extending
its constant endpoint and the restricted cone contraction. -/
private lemma exists_pathLift :
    ∃ L : (X.mappingSpace x y : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X x : SSet.{u}),
      ι₀ ≫ L = SSet.const (coneVertex x) ∧
      toMappingSpace x y ▷ Δ[1] ≫ L = toConeSpace x y ▷ Δ[1] ≫ coneContraction x ∧
      L ≫ coneπ X x = (β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι := by
  apply exists_lift_cylinder_ι₀_of_mono
  · rw [const_coneVertex_coneπ, mappingSpace.ι₀_braiding_uncurry_ι]
  · rw [BraidedCategory.braiding_naturality_left_assoc, ← uncurry_natural_left,
      toMappingSpace_comp_ι, uncurry_curry, SymmetricCategory.symmetry_assoc, Category.assoc]
  · rw [ι₀_comp_assoc, ι₀_coneContraction, comp_const, comp_const]

/-- A lift of the path family along the cone projection, extending the contraction. -/
private noncomputable def pathLift :
    (X.mappingSpace x y : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X x : SSet.{u}) :=
  (exists_pathLift x y).choose

@[reassoc]
private lemma pathLift_coneπ :
    pathLift x y ≫ coneπ X x = (β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι :=
  (exists_pathLift x y).choose_spec.2.2

@[reassoc]
private lemma ι₀_pathLift : ι₀ ≫ pathLift x y = SSet.const (coneVertex x) :=
  (exists_pathLift x y).choose_spec.1

@[reassoc]
private lemma whiskerRight_pathLift :
    toMappingSpace x y ▷ Δ[1] ≫ pathLift x y = toConeSpace x y ▷ Δ[1] ≫ coneContraction x :=
  (exists_pathLift x y).choose_spec.2.1

/-- The homotopy inverse `Hom_X(x, y) ⟶ Hom^L_X(x, y)` of the comparison map: the end of the
lifted path. -/
private noncomputable def inverse :
    (X.mappingSpace x y : SSet.{u}) ⟶ (X.leftMappingSpace x y : SSet.{u}) :=
  fiber.lift (ι₁ ≫ pathLift x y) (coneπ X x) y
    (by rw [Category.assoc, pathLift_coneπ, mappingSpace.ι₁_braiding_uncurry_ι]) ≫
      (coneFiberIso x y).hom

@[reassoc]
private lemma inverse_toConeSpace : inverse x y ≫ toConeSpace x y = ι₁ ≫ pathLift x y := by
  rw [inverse, Category.assoc, coneFiberIso_hom_toConeSpace, fiber.lift_ι]

private lemma toMappingSpace_inverse : toMappingSpace x y ≫ inverse x y = 𝟙 _ := by
  rw [← cancel_mono (toConeSpace x y), Category.assoc, inverse_toConeSpace, ← ι₁_comp_assoc,
    whiskerRight_pathLift, ι₁_comp_assoc, ι₁_coneContraction, Category.comp_id, Category.id_comp]

/-- The uncurried homotopy from `inverse ≫ toMappingSpace` to the identity of `Hom_X(x, y)`:
`(σ, γ, τ)` goes to the contraction at time `max σ τ` of the lifted path at time `σ`. -/
private noncomputable def homotopyAux : Δ[1] ⊗ ((X.mappingSpace x y : SSet.{u}) ⊗ Δ[1]) ⟶ X :=
  lift (cylinderPathCoordinate Δ[1] _ ≫ pathLift x y)
    (cylinderTimeCoordinates _ ≫ (stdSimplex.contractionLast 1).h) ≫
      coneContraction x ≫ coneπ X x

private lemma range_curry_homotopyAux_le :
    Subcomplex.range (curry (homotopyAux x y)) ≤ X.mappingSpace x y := by
  rw [range_le_mappingSpace_iff, uncurry_curry]
  constructor
  · -- At `σ = 0`, the lifted path is at the identity of `x`, which the contraction fixes.
    have e : stdSimplex.δ 1 ▷ _ ≫ lift (cylinderPathCoordinate Δ[1] _ ≫ pathLift x y)
        (cylinderTimeCoordinates _ ≫ (stdSimplex.contractionLast 1).h) =
        lift (SSet.const (coneVertex x)) (stdSimplex.δ 1 ▷ _ ≫
          cylinderTimeCoordinates _ ≫ (stdSimplex.contractionLast 1).h) := by
      simp only [comp_lift, whiskerRight_δ_one_cylinderPathCoordinate_assoc,
        ι₀_pathLift, comp_const]
    rw [homotopyAux, reassoc_of% e, lift_const_coneVertex_coneContraction_assoc,
      const_coneVertex_coneπ]
  · -- At `σ = 1`, the lifted path is at its end, which lies over `y`, and is not contracted.
    have e : stdSimplex.δ 0 ▷ _ ≫ lift (cylinderPathCoordinate Δ[1] _ ≫ pathLift x y)
        (cylinderTimeCoordinates _ ≫ (stdSimplex.contractionLast 1).h) =
        (snd _ _ ≫ fst _ _ ≫ ι₁ ≫ pathLift x y) ≫ ι₁ := by
      rw [← lift_const_one_eq_comp_ι₁, comp_lift]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [lift_fst,
          whiskerRight_δ_zero_cylinderPathCoordinate_assoc]
      · simp only [lift_snd,
          whiskerRight_δ_zero_cylinderTimeCoordinates_assoc]
        exact stdSimplex.lift_const_last_contractionLast_h 1 _
    rw [homotopyAux, reassoc_of% e, ι₁_coneContraction_assoc]
    simp only [pathLift_coneπ, mappingSpace.ι₁_braiding_uncurry_ι, comp_const]

/-- **The homotopy from `inverse ≫ toMappingSpace` to the identity of `Hom_X(x, y)`.** -/
private noncomputable def homotopy :
    Homotopy (inverse x y ≫ toMappingSpace x y) (𝟙 (X.mappingSpace x y : SSet.{u})) :=
  Homotopy.mk' (Subcomplex.lift _ (range_curry_homotopyAux_le x y))
    (by
      rw [← cancel_mono (X.mappingSpace x y).ι, Category.assoc, Subcomplex.lift_ι,
        Category.assoc, toMappingSpace_comp_ι, ← curry_natural_left, ← curry_natural_left]
      congr 1
      have e : (Δ[1] : SSet.{u}) ◁ ι₀ ≫ lift (cylinderPathCoordinate Δ[1] _ ≫ pathLift x y)
          (cylinderTimeCoordinates _ ≫ (stdSimplex.contractionLast 1).h) =
          (β_ _ _).hom ≫ lift (pathLift x y) (snd _ _) := by
        rw [comp_lift]
        apply CartesianMonoidalCategory.hom_ext
        · simp only [lift_fst, Category.assoc]
          exact whiskerLeft_comp_cylinderPathCoordinate_assoc _ (ι₀_fst _) _
        · simp only [lift_snd, Category.assoc,
            whiskerLeft_ι₀_cylinderTimeCoordinates_assoc, (stdSimplex.contractionLast 1).h₀,
            Category.comp_id, braiding_hom_snd]
      have e' : lift (fst _ _ ≫ ι₁ ≫ pathLift x y) (snd _ _) =
          inverse x y ▷ Δ[1] ≫ toConeSpace x y ▷ Δ[1] := by
        rw [← comp_whiskerRight, inverse_toConeSpace]
        exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
      rw [homotopyAux, reassoc_of% e, lift_snd_coneContraction_assoc, e',
        BraidedCategory.braiding_naturality_right_assoc]
      simp only [Category.assoc])
    (by
      rw [← cancel_mono (X.mappingSpace x y).ι, Category.assoc, Subcomplex.lift_ι,
        Category.id_comp, ← curry_natural_left, curry_eq_iff]
      have e : (Δ[1] : SSet.{u}) ◁ ι₁ ≫ lift (cylinderPathCoordinate Δ[1] _ ≫ pathLift x y)
          (cylinderTimeCoordinates _ ≫ (stdSimplex.contractionLast 1).h) =
          ((β_ _ _).hom ≫ pathLift x y) ≫ ι₁ := by
        rw [← lift_const_one_eq_comp_ι₁, comp_lift]
        apply CartesianMonoidalCategory.hom_ext
        · simp only [lift_fst]
          exact whiskerLeft_comp_cylinderPathCoordinate_assoc _ (ι₁_fst _) _
        · simp only [lift_snd,
            whiskerLeft_ι₁_cylinderTimeCoordinates_assoc, (stdSimplex.contractionLast 1).h₁,
            comp_const]
          -- The last vertex of the interval is the numeral one.
          rfl
      rw [homotopyAux, reassoc_of% e, ι₁_coneContraction_assoc, pathLift_coneπ,
        SymmetricCategory.symmetry_assoc])

/-- **The comparison of left mapping spaces is a weak homotopy equivalence** (HTT, §4.2.1):
for a quasicategory `X`, the comparison map `Hom^L_X(x, y) ⟶ Hom_X(x, y)` is a weak homotopy
equivalence. -/
instance isWeakHomotopyEquivalence_toMappingSpace :
    IsWeakHomotopyEquivalence (toMappingSpace x y) :=
  IsWeakHomotopyEquivalence.of_homotopy _ (g := inverse x y)
    (RelativeMorphism.Homotopy.ofEq
      (congrArg RelativeMorphism.botEquiv.symm (toMappingSpace_inverse x y))) (homotopy x y)

end comparison

end leftMappingSpace

namespace modelCategoryQuillen

/-- The left comparison is a weak equivalence in the Kan–Quillen model structure. -/
scoped instance leftMappingSpace_weakEquivalence_toMappingSpace (x y : X _⦋0⦌) [X.Quasicategory] :
    HomotopicalAlgebra.WeakEquivalence (leftMappingSpace.toMappingSpace x y) :=
  weakEquivalence_of_isWeakHomotopyEquivalence _

end modelCategoryQuillen

section IsFullyFaithful

open HomotopicalAlgebra

open scoped modelCategoryQuillen

variable {Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]

/-- **Full faithfulness on left mapping spaces**: a map of quasicategories is fully faithful
exactly when it induces weak equivalences `Hom^L_X(x, y) ⟶ Hom^L_Y(f x, f y)` of the left
mapping spaces. -/
theorem isFullyFaithful_iff_weakEquivalence_leftMappingSpace_map (f : X ⟶ Y) :
    IsFullyFaithful f ↔ ∀ x y : X _⦋0⦌, WeakEquivalence (leftMappingSpace.map x y f) := by
  rw [isFullyFaithful_iff_weakEquivalence_mappingSpace_map]
  refine forall₂_congr fun x y ↦ ?_
  rw [← weakEquivalence_precomp_iff (leftMappingSpace.toMappingSpace x y),
    leftMappingSpace.toMappingSpace_comp_map, weakEquivalence_postcomp_iff]

end IsFullyFaithful

end SSet
