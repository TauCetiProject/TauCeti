/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.FullyFaithful
import TauCeti.AlgebraicTopology.Quasicategory.Slice
import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.Realization
import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne


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

/-- The monotone self-map of `Fin (n + 2)` attached to a simplex `e : ⦋n⦌ ⟶ ⦋1⦌` of `Δ[1]`: it
fixes the `i < n + 1` with `e i = 0` and sends the other elements to the last one. -/
private def collapseOrderHom {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) : Fin (n + 2) →o Fin (n + 2) where
  toFun i := if h : i = Fin.last _ then i else
    if e.toOrderHom (i.castPred h) = 0 then i else Fin.last _
  monotone' a b hab := by
    dsimp only
    by_cases hb : b = Fin.last _
    · subst hb
      split_ifs <;> exact Fin.le_last _
    · have ha : a ≠ Fin.last _ := fun ha ↦ hb (le_antisymm (Fin.le_last _) (ha ▸ hab))
      simp only [ha, hb, ↓reduceDIte]
      split_ifs with h₁ h₂ h₂
      · exact hab
      · exact Fin.le_last _
      · exact absurd (le_antisymm (h₂ ▸ e.toOrderHom.monotone
          (Fin.castPred_le_castPred_iff.2 hab)) (Fin.zero_le _)) h₁
      · exact le_rfl

private lemma collapseOrderHom_castSucc {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) (i : Fin (n + 1)) :
    collapseOrderHom e i.castSucc = if e.toOrderHom i = 0 then i.castSucc else Fin.last _ := by
  by_cases h : e.toOrderHom i = 0 <;> simp [collapseOrderHom, h]

private lemma collapseOrderHom_last {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) :
    collapseOrderHom e (Fin.last _) = Fin.last _ := by
  simp [collapseOrderHom]

/-- The self-map of `⦋n⦌ ⋆ ⦋0⦌` attached to a simplex `e : ⦋n⦌ ⟶ ⦋1⦌` of `Δ[1]`: it fixes the
vertices `i` of `⦋n⦌` with `e i = 0` and sends the other vertices to the final vertex. -/
private def collapse {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) : joinVertex.obj ⦋n⦌ ⟶ joinVertex.obj ⦋n⦌ :=
  SimplexCategory.Hom.mk (collapseOrderHom e)

private lemma collapse_comp_joinVertex_map {n n' : ℕ} (f : ⦋n'⦌ ⟶ ⦋n⦌) (e : ⦋n⦌ ⟶ ⦋1⦌) :
    collapse (f ≫ e) ≫ joinVertex.map f = joinVertex.map f ≫ collapse e := by
  refine hom_ext_castSucc_last (m := ⦋n'⦌) (fun i ↦ ?_) ?_
  · -- Normalize the join object to the finite ordinal expected by the vertex extensionality
    -- lemma; rewriting `comp_toOrderHom` alone cannot match these dependent source types.
    change (joinVertex.map f).toOrderHom (collapseOrderHom (f ≫ e) i.castSucc) =
      collapseOrderHom e ((joinVertex.map f).toOrderHom i.castSucc)
    rw [collapseOrderHom_castSucc, joinVertex_map_castSucc, collapseOrderHom_castSucc]
    -- Normalize the join object to the finite ordinal expected by the vertex extensionality
    -- lemma; rewriting `comp_toOrderHom` alone cannot match these dependent source types.
    change (joinVertex.map f).toOrderHom (if e.toOrderHom (f.toOrderHom i) = 0 then _ else _) = _
    by_cases h : e.toOrderHom (f.toOrderHom i) = 0
    · simp only [h, ↓reduceIte]
      exact joinVertex_map_castSucc f i
    · simp only [h, ↓reduceIte]
      exact joinVertex_map_last f
  · have h₁ : (joinVertex.map f).toOrderHom (Fin.last (n' + 1)) = Fin.last (n + 1) :=
      joinVertex_map_last f
    -- Normalize the join object to the finite ordinal expected by the vertex extensionality
    -- lemma; rewriting `comp_toOrderHom` alone cannot match these dependent source types.
    change (joinVertex.map f).toOrderHom (collapseOrderHom (f ≫ e) (Fin.last (n' + 1))) =
      collapseOrderHom e ((joinVertex.map f).toOrderHom (Fin.last (n' + 1)))
    rw [collapseOrderHom_last, h₁, collapseOrderHom_last]

private lemma joinVertexInr_comp_collapse {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) :
    joinVertexInr ⦋n⦌ ≫ collapse e = joinVertexInr ⦋n⦌ := by
  rw [joinVertexInr_mk]
  exact Hom.ext_zero_left _ _ (collapseOrderHom_last e)

private lemma collapse_const_zero (n : ℕ) : collapse (SimplexCategory.const ⦋n⦌ ⦋1⦌ 0) = 𝟙 _ := by
  refine hom_ext_castSucc_last (m := ⦋n⦌) (fun i ↦ ?_) (collapseOrderHom_last _)
  exact (collapseOrderHom_castSucc _ i).trans (by
    simp only [SimplexCategory.const_apply]
    -- Identity and constant simplex maps evaluate to their defining vertex functions.
    rfl)

private lemma collapse_const_one (n : ℕ) :
    collapse (SimplexCategory.const ⦋n⦌ ⦋1⦌ 1) =
      SimplexCategory.const _ ⦋0⦌ 0 ≫ joinVertexInr ⦋n⦌ := by
  rw [joinVertexInr_mk]
  refine hom_ext_castSucc_last (m := ⦋n⦌) (fun i ↦ ?_) (collapseOrderHom_last _)
  exact (collapseOrderHom_castSucc _ i).trans (by
    simp only [SimplexCategory.const_apply]
    -- Identity and constant simplex maps evaluate to their defining vertex functions.
    rfl)

variable (X) in
/-- The contraction of `joinVertex.op ⋙ X` towards the last vertices: the simplex `(σ, e)` of
`(joinVertex.op ⋙ X) ⊗ Δ[1]` goes to the restriction of `σ` along `collapse e`. -/
private noncomputable def contraction : (joinVertex.op ⋙ X) ⊗ Δ[1] ⟶ joinVertex.op ⋙ X where
  app m := TypeCat.ofHom fun z ↦
    X.map (collapse (n := m.unop.len) (stdSimplex.objEquiv z.2)).op z.1
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext z
    -- Simplices of `joinVertex.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (collapse (f.unop ≫ stdSimplex.objEquiv z.2)).op
        (X.map (joinVertex.map f.unop).op z.1) =
      X.map (joinVertex.map f.unop).op (X.map (collapse (stdSimplex.objEquiv z.2)).op z.1)
    have h := congrArg (fun g ↦ X.map g.op z.1)
      (collapse_comp_joinVertex_map f.unop (stdSimplex.objEquiv z.2))
    simp only [op_comp, Functor.map_comp_apply] at h
    exact h

@[simp]
private lemma contraction_app_apply {n : ℕ}
    (z : ((joinVertex.op ⋙ X) ⊗ Δ[1]).obj (op ⦋n⦌)) :
    dsimp% (contraction X).app _ z = X.map (collapse (stdSimplex.objEquiv z.2)).op z.1 :=
  (rfl)

@[reassoc]
private lemma ι₀_contraction : ι₀ ≫ contraction X = 𝟙 _ := by
  ext ⟨⟨n⟩⟩ σ
  have he : stdSimplex.objEquiv (ι₀.app _ σ).2 = SimplexCategory.const ⦋n⦌ ⦋1⦌ 0 := by
    ext i : 3
    exact SSet.ι₀_app_snd_apply σ i
  have h := contraction_app_apply (X := X) (n := n) (ι₀.app _ σ)
  rw [he, collapse_const_zero, op_id, CategoryTheory.Functor.map_id] at h
  exact h.trans (SSet.ι₀_app_fst σ)

variable (y : X _⦋0⦌)

/-- The contraction maps the simplices with last vertex `y` to simplices with last vertex `y`. -/
private noncomputable def coneContraction :
    (coneSpace X y : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X y : SSet.{u}) :=
  Subcomplex.lift ((coneSpace X y).ι ▷ Δ[1] ≫ contraction X) (by
    rintro ⟨⟨n⟩⟩ _ ⟨⟨⟨σ, hσ⟩, e⟩, rfl⟩
    rw [mem_coneSpace_obj_iff]
    -- Whiskering the inclusion applies it to the first coordinate; expose that pair so the
    -- contraction evaluation lemma applies without unfolding the contraction.
    change X.map (joinVertexInr ⦋n⦌).op ((contraction X).app _ (σ, e)) = y
    calc
      _ = X.map (joinVertexInr ⦋n⦌).op
          (X.map (collapse (stdSimplex.objEquiv e)).op σ) :=
        congrArg _ (contraction_app_apply (X := X) (n := n) (σ, e))
      _ = y := by
        rw [← Functor.map_comp_apply, ← op_comp, joinVertexInr_comp_collapse]
        exact (mem_coneSpace_obj_iff y σ).1 hσ)


@[simp]
private lemma coneContraction_app_val {n : ℕ}
    (z : ((coneSpace X y : SSet.{u}) ⊗ Δ[1]).obj (op ⦋n⦌)) :
    dsimp% ((coneContraction y).app _ z).val =
      X.map (collapse (stdSimplex.objEquiv z.2)).op z.1.val :=
  (rfl)

@[reassoc]
private lemma coneContraction_ι :
    coneContraction y ≫ (coneSpace X y).ι = (coneSpace X y).ι ▷ Δ[1] ≫ contraction X :=
  (rfl)

@[reassoc]
private lemma ι₀_coneContraction : ι₀ ≫ coneContraction y = 𝟙 _ := by
  rw [← cancel_mono (coneSpace X y).ι, Category.assoc, coneContraction_ι, ι₀_comp_assoc,
    ι₀_contraction, Category.comp_id, Category.id_comp]

/-- The last vertex `y`, as the vertex of `joinVertex.op ⋙ X` given by the identity edge of `y`. -/
private noncomputable def coneVertex : (coneSpace X y : SSet.{u}) _⦋0⦌ :=
  ⟨X.map (SimplexCategory.const (joinVertex.obj ⦋0⦌) ⦋0⦌ 0).op y, by
    rw [mem_coneSpace_obj_iff, map_map_const_zero, SimplexCategory.const_eq_id,
      op_id, CategoryTheory.Functor.map_id, types_id_apply]⟩

@[simp]
private lemma coneVertex_val :
    (coneVertex y).val = X.map (SimplexCategory.const (joinVertex.obj ⦋0⦌) ⦋0⦌ 0).op y :=
  (rfl)

@[reassoc]
private lemma ι₁_coneContraction : ι₁ ≫ coneContraction y = SSet.const (coneVertex y) := by
  rw [← cancel_mono (coneSpace X y).ι, Category.assoc, coneContraction_ι, ι₁_comp_assoc]
  ext ⟨⟨n⟩⟩ ⟨σ, hσ⟩
  -- Simplices of `joinVertex.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (collapse (SimplexCategory.const ⦋n⦌ ⦋1⦌ 1)).op σ =
    X.map (joinVertex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op
      (X.map (SimplexCategory.const (joinVertex.obj ⦋0⦌) ⦋0⦌ 0).op y)
  rw [collapse_const_one, op_comp, Functor.map_comp_apply, map_map_const_zero]
  -- Simplices of `joinVertex.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map _ (X.map (joinVertexInr ⦋n⦌).op σ) = _
  rw [show X.map (joinVertexInr ⦋n⦌).op σ = y from (mem_coneSpace_obj_iff y σ).1 hσ]

private instance [X.Quasicategory] : RightFibration (coneπ X y) := by
  rw [← Iso.inv_hom_id_assoc (sliceIso y) (coneπ X y), sliceIso_hom_coneπ]
  infer_instance

variable {x y : X _⦋0⦌}

@[reassoc]
private lemma const_coneVertex_coneπ {Z : SSet.{u}} : SSet.const (coneVertex y) ≫ coneπ X y =
    (SSet.const y : Z ⟶ X) := by
  rw [const_comp, coneπ_app, coneVertex_val, map_map_const_zero,
    SimplexCategory.const_eq_id, op_id, CategoryTheory.Functor.map_id, types_id_apply]

variable (x y) in
private lemma rightMappingSpace_le_coneSpace : X.rightMappingSpace x y ≤ coneSpace X y :=
  fun _ σ hσ ↦ (mem_coneSpace_obj_iff y σ).2 ((mem_rightMappingSpace_obj_iff _).1 hσ).2

variable (x y) in
/-- The inclusion of `Hom^R_X(x, y)` into `coneSpace X y`. -/
private noncomputable def toConeSpace :
    (X.rightMappingSpace x y : SSet.{u}) ⟶ (coneSpace X y : SSet.{u}) :=
  Subcomplex.homOfLE (rightMappingSpace_le_coneSpace x y)

private instance : Mono (toConeSpace x y) :=
  inferInstanceAs (Mono (Subcomplex.homOfLE (rightMappingSpace_le_coneSpace x y)))

@[reassoc]
private lemma toConeSpace_coneπ : toConeSpace x y ≫ coneπ X y = SSet.const x := by
  ext ⟨⟨n⟩⟩ s
  dsimp only [TypeCat.Fun.toFun_apply]
  rw [NatTrans.comp_app_apply, coneπ_app]
  exact ((mem_rightMappingSpace_obj_iff _).1 s.property).1

/-- A family of simplices of `coneSpace X y` lying over `x` is a family of simplices of
`Hom^R_X(x, y)`. -/
private lemma range_le_rightMappingSpace {Z : SSet.{u}} (g : Z ⟶ (coneSpace X y : SSet.{u}))
    (hg : g ≫ coneπ X y = SSet.const x) :
    Subcomplex.range (g ≫ (coneSpace X y).ι) ≤ X.rightMappingSpace x y := by
  rintro ⟨⟨n⟩⟩ _ ⟨z, rfl⟩
  exact (mem_rightMappingSpace_obj_iff _).2
    ⟨by
      have h := congrArg (fun φ ↦ φ.app _ z) hg
      exact (coneπ_app y (g.app _ z)).symm.trans h,
      (mem_coneSpace_obj_iff y _).1 (g.app _ z).property⟩

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
  -- Simplices of `joinVertex.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (stdSimplex.objEquiv ((toJoinVertex n).app _ (e, f))).op s.val =
    X.map (joinVertexInl ⦋m⦌).op (X.map (collapse (stdSimplex.objEquiv e)).op
      (X.map (joinVertex.map (stdSimplex.objEquiv f)).op s.val))
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine congrArg (fun g : ⦋m⦌ ⟶ ⦋n + 1⦌ ↦ X.map g.op s.val) ?_
  rw [joinVertexInl_mk]
  ext i : 3
  have hi : (SimplexCategory.δ (Fin.last (m + 1))).toOrderHom i = i.castSucc :=
    Fin.succAbove_last_apply i
  refine (toJoinVertex_app_apply n (e, f) i).trans ?_
  -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
  change _ = (joinVertex.map (stdSimplex.objEquiv f)).toOrderHom
    (collapseOrderHom (stdSimplex.objEquiv e) ((SimplexCategory.δ (Fin.last (m + 1))).toOrderHom i))
  rw [hi, collapseOrderHom_castSucc, toJoinVertexOrderHom_apply]
  rw [stdSimplex.objEquiv_toOrderHom_apply e i]
  by_cases h : e i = 0
  · simp only [h, ↓reduceIte]
    exact (joinVertex_map_castSucc _ i).symm
  · simp only [h, ↓reduceIte]
    exact (joinVertex_map_last _).symm

private lemma collapse_comp_joinVertex_map_minRetraction {n : ℕ} (j : Fin (n + 1)) :
    collapse (stdSimplex.objEquiv (stdSimplex.objMk₁.{u} j.succ)) ≫
        joinVertex.map (minRetraction j) =
      collapse (stdSimplex.objEquiv (stdSimplex.objMk₁.{u} j.succ)) := by
  refine hom_ext_castSucc_last (m := ⦋n⦌) (fun i ↦ ?_) ?_
  · -- Normalize the join object to the finite ordinal expected by the vertex extensionality
    -- lemma; rewriting `comp_toOrderHom` alone cannot match these dependent source types.
    change (joinVertex.map (minRetraction j)).toOrderHom (collapseOrderHom _ i.castSucc) =
      collapseOrderHom _ i.castSucc
    rw [collapseOrderHom_castSucc]
    simp only [stdSimplex.objEquiv_toOrderHom_apply (stdSimplex.objMk₁.{u} j.succ) i]
    by_cases h : stdSimplex.objMk₁.{u} j.succ i = 0
    · simp only [h, ↓reduceIte]
      refine (joinVertex_map_castSucc _ i).trans
        (congrArg Fin.castSucc ((minRetraction_apply j i).trans (min_eq_left ?_)))
      rwa [stdSimplex.objMk₁_apply_eq_zero_iff, Fin.castSucc_lt_succ_iff] at h
    · simp only [h, ↓reduceIte]
      exact joinVertex_map_last _
  · -- Normalize the join object to the finite ordinal expected by the vertex extensionality
    -- lemma; rewriting `comp_toOrderHom` alone cannot match these dependent source types.
    change (joinVertex.map (minRetraction j)).toOrderHom (collapseOrderHom _ (Fin.last (n + 1))) =
      collapseOrderHom _ (Fin.last (n + 1))
    rw [collapseOrderHom_last]
    exact joinVertex_map_last _

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
    rw [stdSimplex.objEquiv_objMk₁_zero, collapse_const_one, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply]
    -- Simplices of `joinVertex.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map _ (X.map (joinVertexInr ⦋n⦌).op (G.app _ (z, _)).val) =
      X.map _ (X.map (joinVertexInr ⦋n⦌).op (G.app _ (ι₀.app _ z)).val)
    rw [show X.map (joinVertexInr ⦋n⦌).op (G.app _ (z, _)).val = y from
        (mem_coneSpace_obj_iff y _).1 (G.app _ _).property,
      show X.map (joinVertexInr ⦋n⦌).op (G.app _ (ι₀.app _ z)).val = y from
        (mem_coneSpace_obj_iff y _).1 (G.app _ _).property]
  | succ j =>
    rw [← collapse_comp_joinVertex_map_minRetraction j, op_comp, Functor.map_comp_apply,
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

/-- Contracting the constant family at the identity of `y` gives the constant family. -/
@[reassoc]
private lemma lift_const_coneVertex_coneContraction {Z : SSet.{u}} (f : Z ⟶ Δ[1]) :
    lift (SSet.const (coneVertex y)) f ≫ coneContraction y = SSet.const (coneVertex y) := by
  ext ⟨⟨n⟩⟩ z : 4
  apply Subtype.ext
  -- Evaluate the pairing before applying the component formula for the contraction.
  change ((coneContraction y).app _ ((SSet.const (coneVertex y)).app _ z, f.app _ z)).val =
    ((SSet.const (coneVertex y)).app _ z).val
  refine (coneContraction_app_val y (n := n)
    ((SSet.const (coneVertex y)).app _ z, f.app _ z)).trans ?_
  simp only [const_app, Subfunctor.toFunctor_map, Functor.comp_map, Functor.op_map,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, coneVertex_val]
  rw [map_map_const_zero, map_map_const_zero]

section comparison

variable (x y)

/-- The pushout-product of the comparison map `Hom^R_X(x, y) ⟶ Hom_X(x, y)` with the inclusion
`{1} ⟶ Δ[1]`, a right anodyne extension. -/
private noncomputable abbrev pushoutProduct :=
  Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (toMappingSpace x y) Λ[1, 1].ι

private lemma pushoutProductTop_aux :
    ((curriedTensor SSet.{u}).map (toMappingSpace x y)).app Λ[1, 1] ≫ SSet.const (coneVertex y) =
      ((curriedTensor SSet.{u}).obj (X.rightMappingSpace x y)).map Λ[1, 1].ι ≫
        toConeSpace x y ▷ Δ[1] ≫ coneContraction y := by
  simp only [curriedTensor_map_app, curriedTensor_obj_map, comp_const,
    whiskerLeft_horn_one_one_ι, Category.assoc, ι₁_comp_assoc, ι₁_coneContraction]

/-- The map from the pushout-product to `coneSpace X y`: the constant map at the identity of `y`
on `Hom_X(x, y) ⊗ {1}`, and the contraction on `Hom^R_X(x, y) ⊗ Δ[1]`. -/
private noncomputable def pushoutProductTop :
    (pushoutProduct x y).pt ⟶ (coneSpace X y : SSet.{u}) :=
  (pushoutProduct x y).isPushout.desc (SSet.const (coneVertex y))
    (toConeSpace x y ▷ Δ[1] ≫ coneContraction y) (pushoutProductTop_aux x y)

private lemma inl_pushoutProductTop :
    (pushoutProduct x y).inl ≫ pushoutProductTop x y = SSet.const (coneVertex y) :=
  IsPushout.inl_desc _ _ _ _

private lemma inr_pushoutProductTop :
    (pushoutProduct x y).inr ≫ pushoutProductTop x y =
      toConeSpace x y ▷ Δ[1] ≫ coneContraction y :=
  IsPushout.inr_desc _ _ _ _

private lemma pushoutProductTop_comm :
    CommSq (pushoutProductTop x y) (pushoutProduct x y).ι (coneπ X y)
      ((β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι) := ⟨by
  refine (pushoutProduct x y).hom_ext ?_ ?_
  · rw [reassoc_of% inl_pushoutProductTop, const_coneVertex_coneπ,
      Functor.PushoutObjObj.inl_ι_assoc, curriedTensor_obj_map, whiskerLeft_horn_one_one_ι,
      Category.assoc, mappingSpace.ι₁_braiding_uncurry_ι, comp_const]
  · rw [reassoc_of% inr_pushoutProductTop, Functor.PushoutObjObj.inr_ι_assoc,
      curriedTensor_map_app, BraidedCategory.braiding_naturality_left_assoc,
      ← uncurry_natural_left, toMappingSpace_comp_ι, uncurry_curry,
      SymmetricCategory.symmetry_assoc]⟩

variable [X.Quasicategory]

private instance : HasLiftingProperty (pushoutProduct x y).ι (coneπ X y) :=
  (rightAnodyneExtensions_pushoutObjObjι (pushoutProduct x y)
    (rightAnodyneExtensions.horn_ι (by decide : (0 : Fin 2) < 1))).hasLiftingProperty _

/-- A lift `Hom_X(x, y) ⊗ Δ[1] ⟶ coneSpace X y` of the uncurried inclusion of `Hom_X(x, y)`
along the right fibration `coneSpace X y ⟶ X`, extending the contraction on `Hom^R_X(x, y)` and
the constant map at the identity of `y` on `Hom_X(x, y) ⊗ {1}`. -/
private noncomputable def pathLift :
    (X.mappingSpace x y : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X y : SSet.{u}) :=
  (pushoutProductTop_comm x y).lift

@[reassoc]
private lemma pathLift_coneπ :
    pathLift x y ≫ coneπ X y = (β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι :=
  (pushoutProductTop_comm x y).fac_right

@[reassoc]
private lemma ι₁_pathLift : ι₁ ≫ pathLift x y = SSet.const (coneVertex y) := by
  have h : (X.mappingSpace x y : SSet.{u}) ◁ Λ[1, 1].ι ≫ pathLift x y =
      SSet.const (coneVertex y) := by
    have h := (pushoutProduct x y).inl ≫= (pushoutProductTop_comm x y).fac_left
    rwa [Functor.PushoutObjObj.inl_ι_assoc, inl_pushoutProductTop, curriedTensor_obj_map] at h
  rw [← fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_zero, Category.assoc,
    ← (horn.ι_ι 1 0 (by decide) : horn.ι 1 0 _ ≫ Λ[1, 1].ι = stdSimplex.δ 0),
    MonoidalCategory.whiskerLeft_comp, Category.assoc, h, comp_const, comp_const]

@[reassoc]
private lemma whiskerRight_pathLift :
    toMappingSpace x y ▷ Δ[1] ≫ pathLift x y = toConeSpace x y ▷ Δ[1] ≫ coneContraction y := by
  have h := (pushoutProduct x y).inr ≫= (pushoutProductTop_comm x y).fac_left
  rwa [Functor.PushoutObjObj.inr_ι_assoc, inr_pushoutProductTop, curriedTensor_map_app] at h

/-- The homotopy inverse `Hom_X(x, y) ⟶ Hom^R_X(x, y)` of the comparison map: the start of the
lifted path. -/
private noncomputable def inverse :
    (X.mappingSpace x y : SSet.{u}) ⟶ (X.rightMappingSpace x y : SSet.{u}) :=
  Subcomplex.lift ((ι₀ ≫ pathLift x y) ≫ (coneSpace X y).ι)
    (range_le_rightMappingSpace (ι₀ ≫ pathLift x y)
      (by rw [Category.assoc, pathLift_coneπ, mappingSpace.ι₀_braiding_uncurry_ι]))

@[reassoc]
private lemma inverse_toConeSpace : inverse x y ≫ toConeSpace x y = ι₀ ≫ pathLift x y := by
  rw [← cancel_mono (coneSpace X y).ι, Category.assoc, toConeSpace, Subcomplex.homOfLE_ι]
  exact Subcomplex.lift_ι _ _

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
    (.mk' (fst _ _) (by rw [ι₀_fst, toMappingSpace_inverse]) (ι₁_fst _)) H

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
