/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.RightComparison
import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.Realization
import TauCeti.AlgebraicTopology.Quasicategory.Slice
import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne


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

variable (X) in
/-- The simplices of `vertexJoin.op ⋙ X` with initial vertex `x`. -/
private def coneSpace (x : X _⦋0⦌) : Subcomplex (vertexJoin.op ⋙ X) where
  obj m := {σ | X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj m.unop) 0).op σ = x}
  map {m m'} f σ hσ := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    have h := congrArg (fun g ↦ X.map g.op σ) (const_zero_comp_vertexJoin_map (x := ⦋0⦌) f.unop)
    exact (Functor.map_comp_apply X _ _ σ).symm.trans (h.trans hσ)

/-- The inclusion of `m` into `⦋0⦌ ⋆ m` as the face opposite to the initial vertex. -/
private def tail (m : SimplexCategory) : m ⟶ vertexJoin.obj m :=
  SimplexCategory.δ (n := m.len) 0

variable (X) in
/-- The restriction of a simplex of `vertexJoin.op ⋙ X` to the face opposite to the initial
vertex. -/
private def base : (vertexJoin.op ⋙ X) ⟶ X where
  app m := X.map (tail m.unop).op
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext σ
    have h := congrArg (fun g ↦ X.map g.op σ) (δ_zero_comp_vertexJoin_map f.unop)
    exact (Functor.map_comp_apply X _ _ σ).symm.trans (h.trans (Functor.map_comp_apply X _ _ σ))

/-- The monotone self-map of `Fin (n + 2)` attached to a simplex `e : ⦋n⦌ ⟶ ⦋1⦌` of `Δ[1]`: it
fixes `0` and the `i + 1` with `e i = 1`, and sends the other elements to `0`. -/
private def collapseOrderHom {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) : Fin (n + 2) →o Fin (n + 2) where
  toFun i := if h : i = 0 then i else if e.toOrderHom (i.pred h) = 1 then i else 0
  monotone' a b hab := by
    dsimp only
    by_cases ha : a = 0
    · subst ha
      split_ifs <;> exact Fin.zero_le _
    · have hb : b ≠ 0 := fun hb ↦ ha (le_antisymm (hb ▸ hab) (Fin.zero_le _))
      simp only [ha, hb, ↓reduceDIte]
      split_ifs with h₁ h₂ h₂
      · exact hab
      · exfalso
        have := e.toOrderHom.monotone ((Fin.pred_le_pred_iff (ha := ha) (hb := hb)).2 hab)
        rw [h₁] at this
        exact h₂ (le_antisymm (Fin.le_last _) this)
      · exact Fin.zero_le _
      · exact le_rfl

private lemma collapseOrderHom_succ {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) (i : Fin (n + 1)) :
    collapseOrderHom e i.succ = if e.toOrderHom i = 1 then i.succ else 0 := by
  by_cases h : e.toOrderHom i = 1 <;> simp [collapseOrderHom, h]

private lemma collapseOrderHom_zero {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) : collapseOrderHom e 0 = 0 := by
  simp [collapseOrderHom]

/-- The self-map of `⦋0⦌ ⋆ ⦋n⦌` attached to a simplex `e : ⦋n⦌ ⟶ ⦋1⦌` of `Δ[1]`: it fixes the
vertices `i` of `⦋n⦌` with `e i = 1` and sends the other vertices to the initial vertex. -/
private def collapse {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) : vertexJoin.obj ⦋n⦌ ⟶ vertexJoin.obj ⦋n⦌ :=
  SimplexCategory.Hom.mk (collapseOrderHom e)

private lemma collapse_comp_vertexJoin_map {n n' : ℕ} (f : ⦋n'⦌ ⟶ ⦋n⦌) (e : ⦋n⦌ ⟶ ⦋1⦌) :
    collapse (f ≫ e) ≫ vertexJoin.map f = vertexJoin.map f ≫ collapse e := by
  refine hom_ext_zero_succ (m := ⦋n'⦌) ?_ (fun i ↦ ?_)
  · have h₁ : (vertexJoin.map f).toOrderHom 0 = 0 := vertexJoin_map_zero f
    -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
    change (vertexJoin.map f).toOrderHom (collapseOrderHom (f ≫ e) 0) =
      collapseOrderHom e ((vertexJoin.map f).toOrderHom 0)
    rw [collapseOrderHom_zero]
    exact h₁.trans ((congrArg (collapseOrderHom e) h₁).trans (collapseOrderHom_zero e)).symm
  · -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
    change (vertexJoin.map f).toOrderHom (collapseOrderHom (f ≫ e) i.succ) =
      collapseOrderHom e ((vertexJoin.map f).toOrderHom i.succ)
    rw [collapseOrderHom_succ, vertexJoin_map_succ, collapseOrderHom_succ]
    -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
    change (vertexJoin.map f).toOrderHom (if e.toOrderHom (f.toOrderHom i) = 1 then _ else _) = _
    by_cases h : e.toOrderHom (f.toOrderHom i) = 1
    · simp only [h, ↓reduceIte]
      exact vertexJoin_map_succ f i
    · simp only [h, ↓reduceIte]
      exact vertexJoin_map_zero f

private lemma const_zero_comp_collapse {n : ℕ} (e : ⦋n⦌ ⟶ ⦋1⦌) :
    SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0 ≫ collapse e =
      SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0 :=
  Hom.ext_zero_left _ _ (collapseOrderHom_zero e)

private lemma collapse_const_one (n : ℕ) : collapse (SimplexCategory.const ⦋n⦌ ⦋1⦌ 1) = 𝟙 _ := by
  refine hom_ext_zero_succ (m := ⦋n⦌) (collapseOrderHom_zero _) (fun i ↦ ?_)
  exact (collapseOrderHom_succ _ i).trans (by simp; rfl)

private lemma collapse_const_zero (n : ℕ) :
    collapse (SimplexCategory.const ⦋n⦌ ⦋1⦌ 0) =
      SimplexCategory.const _ ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0 := by
  refine hom_ext_zero_succ (m := ⦋n⦌) (collapseOrderHom_zero _) (fun i ↦ ?_)
  exact (collapseOrderHom_succ _ i).trans (by simp; rfl)

variable (X) in
/-- The contraction of `vertexJoin.op ⋙ X` towards the initial vertices: the simplex `(σ, e)` of
`(vertexJoin.op ⋙ X) ⊗ Δ[1]` goes to the restriction of `σ` along `collapse e`. -/
private noncomputable def contraction : (vertexJoin.op ⋙ X) ⊗ Δ[1] ⟶ vertexJoin.op ⋙ X where
  app m := TypeCat.ofHom fun z ↦
    X.map (collapse (n := m.unop.len) (stdSimplex.objEquiv z.2)).op z.1
  naturality m m' f := by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext z
    -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (collapse (f.unop ≫ stdSimplex.objEquiv z.2)).op
        (X.map (vertexJoin.map f.unop).op z.1) =
      X.map (vertexJoin.map f.unop).op (X.map (collapse (stdSimplex.objEquiv z.2)).op z.1)
    have h := congrArg (fun g ↦ X.map g.op z.1)
      (collapse_comp_vertexJoin_map f.unop (stdSimplex.objEquiv z.2))
    simp only [op_comp, Functor.map_comp_apply] at h
    exact h

@[reassoc]
private lemma ι₁_contraction : ι₁ ≫ contraction X = 𝟙 _ := by
  ext ⟨⟨n⟩⟩ σ
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (collapse (SimplexCategory.const ⦋n⦌ ⦋1⦌ 1)).op σ = σ
  rw [collapse_const_one, op_id, CategoryTheory.Functor.map_id]
  rfl

variable (x : X _⦋0⦌)

/-- The contraction maps the simplices with initial vertex `x` to simplices with initial
vertex `x`. -/
private noncomputable def coneContraction :
    (coneSpace X x : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X x : SSet.{u}) :=
  Subcomplex.lift ((coneSpace X x).ι ▷ Δ[1] ≫ contraction X) (by
    rintro ⟨⟨n⟩⟩ _ ⟨⟨⟨σ, hσ⟩, e⟩, rfl⟩
    -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op
      (X.map (collapse (stdSimplex.objEquiv e)).op σ) = x
    have h₁ := congrArg (fun g ↦ X.map (Quiver.Hom.op g) σ)
      (const_zero_comp_collapse (stdSimplex.objEquiv e))
    exact (Functor.map_comp_apply X _ _ σ).symm.trans (h₁.trans hσ))

@[reassoc]
private lemma coneContraction_ι :
    coneContraction x ≫ (coneSpace X x).ι = (coneSpace X x).ι ▷ Δ[1] ≫ contraction X :=
  (rfl)

@[reassoc]
private lemma ι₁_coneContraction : ι₁ ≫ coneContraction x = 𝟙 _ := by
  rw [← cancel_mono (coneSpace X x).ι, Category.assoc, coneContraction_ι, ι₁_comp_assoc,
    ι₁_contraction, Category.comp_id, Category.id_comp]

/-- The initial vertex `x`, as the vertex of `vertexJoin.op ⋙ X` given by the identity edge of
`x`. -/
private noncomputable def coneVertex : (coneSpace X x : SSet.{u}) _⦋0⦌ :=
  ⟨X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x, by
    -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋0⦌) 0).op
      (X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x) = x
    rw [map_map_const_zero, Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0) (𝟙 _), op_id,
      CategoryTheory.Functor.map_id]
    rfl⟩

@[reassoc]
private lemma ι₀_coneContraction : ι₀ ≫ coneContraction x = SSet.const (coneVertex x) := by
  rw [← cancel_mono (coneSpace X x).ι, Category.assoc, coneContraction_ι, ι₀_comp_assoc]
  ext ⟨⟨n⟩⟩ ⟨σ, hσ⟩
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (collapse (SimplexCategory.const ⦋n⦌ ⦋1⦌ 0)).op σ =
    X.map (vertexJoin.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op
      (X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x)
  rw [collapse_const_zero, op_comp, Functor.map_comp_apply, map_map_const_zero]
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map _ (X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op σ) = _
  rw [show X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op σ = x from hσ]

variable (X) in
/-- The projection `(coneSpace X x) ⟶ X`: the restriction to the face opposite to the initial
vertex. -/
private noncomputable def coneπ : (coneSpace X x : SSet.{u}) ⟶ X := (coneSpace X x).ι ≫ base X

/-- The `n`-simplices of the coslice `X_{x/}` are those of `coneSpace X x`, through
`Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`. -/
private noncomputable def cosliceEquiv (n : ℕ) :
    (coslice (yonedaEquiv.symm x)) _⦋n⦌ ≃ (coneSpace X x : SSet.{u}) _⦋n⦌ where
  toFun s := ⟨(yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s).val) : X _⦋n + 1⦌), by
    -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op _ = x
    rw [yonedaEquiv_naturality, join.const_zero_comp_coneIso_inv_assoc,
      (coslice.objEquiv s).property, Equiv.apply_symm_apply]⟩
  invFun t := coslice.objEquiv.symm
      ⟨(join.coneIso n).hom ≫ yonedaEquiv.symm (t.val : X _⦋n + 1⦌),
        (join.inl_comp_coneIso_hom_assoc _).trans
          ((yonedaEquiv_symm_naturality_left (X := X) (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)
            (t.val : X _⦋n + 1⦌)).trans (congrArg yonedaEquiv.symm t.property))⟩
  left_inv s := coslice.objEquiv.injective (Subtype.ext (by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]))
  right_inv t := Subtype.ext (by
    simp only [Equiv.apply_symm_apply, Iso.inv_hom_id_assoc]
    exact yonedaEquiv.apply_symm_apply _)

/-- The coslice `X_{x/}` is isomorphic to `coneSpace X x`. -/
private noncomputable def cosliceIso : coslice (yonedaEquiv.symm x) ≅ (coneSpace X x : SSet.{u}) :=
  NatIso.ofComponents (fun m ↦ (cosliceEquiv x m.unop.len).toIso) (fun {m m'} f ↦ by
    obtain ⟨⟨a⟩⟩ := m
    obtain ⟨⟨b⟩⟩ := m'
    ext s : 3
    refine Subtype.ext ?_
    have key : (yonedaEquiv ((join.coneIso b).inv ≫
        (coslice.objEquiv ((coslice (yonedaEquiv.symm x)).map f s)).val) : X _⦋b + 1⦌) =
        X.map (vertexJoin.map f.unop).op
          (yonedaEquiv ((join.coneIso a).inv ≫ (coslice.objEquiv s).val)) := by
      rw [coslice.objEquiv_map_coe, yonedaEquiv_naturality]
      exact congrArg yonedaEquiv (join.vertexJoin_map_comp_coneIso_inv_assoc f.unop _).symm
    exact key.trans rfl)

@[reassoc]
private lemma cosliceIso_hom_coneπ : (cosliceIso x).hom ≫ coneπ X x = coslice.π _ := by
  ext ⟨⟨n⟩⟩ s
  -- State the evaluated composite in applied form.
  change (coneπ X x).app _ ((cosliceIso x).hom.app _ s) = (coslice.π _).app _ s
  rw [coslice.π_app]
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (tail ⦋n⦌).op
      (yonedaEquiv ((join.coneIso n).inv ≫ (coslice.objEquiv s).val)) = _
  rw [yonedaEquiv_naturality]
  exact congrArg yonedaEquiv (join.δ_zero_comp_coneIso_inv_assoc _)

private instance [X.Quasicategory] : LeftFibration (coneπ X x) := by
  rw [← Iso.inv_hom_id_assoc (cosliceIso x) (coneπ X x), cosliceIso_hom_coneπ]
  infer_instance


variable {x y : X _⦋0⦌}

@[reassoc]
private lemma const_coneVertex_coneπ {Z : SSet.{u}} : SSet.const (coneVertex x) ≫ coneπ X x =
    (SSet.const x : Z ⟶ X) := by
  ext ⟨⟨n⟩⟩ z
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (tail ⦋n⦌).op (X.map (vertexJoin.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op
    (X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x)) =
    X.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op x
  rw [map_map_const_zero, map_map_const_zero]

variable (x y) in
private lemma leftMappingSpace_le_coneSpace : X.leftMappingSpace x y ≤ coneSpace X x := by
  rintro ⟨⟨n⟩⟩ σ hσ
  exact ((mem_leftMappingSpace_iff σ).1 hσ).1

variable (x y) in
/-- The inclusion of `Hom^L_X(x, y)` into `coneSpace X x`. -/
private noncomputable def toConeSpace :
    (X.leftMappingSpace x y : SSet.{u}) ⟶ (coneSpace X x : SSet.{u}) :=
  Subcomplex.homOfLE (leftMappingSpace_le_coneSpace x y)

private instance : Mono (toConeSpace x y) :=
  inferInstanceAs (Mono (Subcomplex.homOfLE (leftMappingSpace_le_coneSpace x y)))

@[reassoc]
private lemma toConeSpace_coneπ : toConeSpace x y ≫ coneπ X x = SSet.const y := by
  ext ⟨⟨n⟩⟩ s
  exact ((mem_leftMappingSpace_iff (s.val : X _⦋n + 1⦌)).1 s.property).2

/-- A family of simplices of `coneSpace X x` lying over `y` is a family of simplices of
`Hom^L_X(x, y)`. -/
private lemma range_le_leftMappingSpace {Z : SSet.{u}} (g : Z ⟶ (coneSpace X x : SSet.{u}))
    (hg : g ≫ coneπ X x = SSet.const y) :
    Subcomplex.range (g ≫ (coneSpace X x).ι) ≤ X.leftMappingSpace x y := by
  rintro ⟨⟨n⟩⟩ _ ⟨z, rfl⟩
  exact (mem_leftMappingSpace_iff _).2
    ⟨(g.app _ z).property, congrArg (fun φ ↦ φ.app _ z) hg⟩

open prodStdSimplex in
/-- **The comparison map through the contraction**: the comparison
`Hom^L_X(x, y) ⟶ Hom_X(x, y)` sends a simplex `s` to the path from the identity of `x` to `s`
traced by the contraction, projected to `X`. -/
private lemma toMappingSpace_comp_ι :
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
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (stdSimplex.objEquiv ((toVertexJoin n).app _ (e, f))).op s.val =
    X.map (tail ⦋m⦌).op (X.map (collapse (stdSimplex.objEquiv e)).op
      (X.map (vertexJoin.map (stdSimplex.objEquiv f)).op s.val))
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  refine congrArg (fun g : ⦋m⦌ ⟶ ⦋n + 1⦌ ↦ X.map g.op s.val) ?_
  ext i : 3
  have hi : (tail ⦋m⦌).toOrderHom i = i.succ := congrFun Fin.succAbove_zero i
  refine (toVertexJoin_app_apply n (e, f) i).trans ?_
  -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
  change _ = (vertexJoin.map (stdSimplex.objEquiv f)).toOrderHom
    (collapseOrderHom (stdSimplex.objEquiv e) ((tail ⦋m⦌).toOrderHom i))
  rw [hi, collapseOrderHom_succ, toVertexJoinOrderHom_apply]
  -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
  change (if e i = 0 then _ else _) = (vertexJoin.map (stdSimplex.objEquiv f)).toOrderHom
    (if e i = 1 then _ else _)
  by_cases h : e i = 0
  · simp only [h, ↓reduceIte]
    exact (vertexJoin_map_zero _).symm
  · have h' : e i = 1 := (by decide : ∀ t : Fin 2, ¬ t = 0 → t = 1) _ h
    simp only [h', ↓reduceIte]
    exact (vertexJoin_map_succ _ i).symm

/-- The retraction `i ↦ max i j` of `⦋n⦌` onto its last vertices, from `j` on. -/
private def truncate {n : ℕ} (j : Fin (n + 1)) : ⦋n⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ max i j, fun _ _ h ↦ max_le_max_right j h⟩

private lemma truncate_comp_objMk₁ {n : ℕ} (j : Fin (n + 1)) :
    truncate j ≫ stdSimplex.objEquiv (stdSimplex.objMk₁.{u} j.castSucc) =
      SimplexCategory.const ⦋n⦌ ⦋1⦌ 1 := by
  ext i : 3
  -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
  change stdSimplex.objMk₁.{u} j.castSucc (max i j) = 1
  rw [stdSimplex.objMk₁_apply_eq_one_iff, Fin.castSucc_le_castSucc_iff]
  exact le_max_right i j

private lemma collapse_comp_vertexJoin_map_truncate {n : ℕ} (j : Fin (n + 1)) :
    collapse (stdSimplex.objEquiv (stdSimplex.objMk₁.{u} j.castSucc)) ≫
        vertexJoin.map (truncate j) =
      collapse (stdSimplex.objEquiv (stdSimplex.objMk₁.{u} j.castSucc)) := by
  refine hom_ext_zero_succ (m := ⦋n⦌) ?_ (fun i ↦ ?_)
  · -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
    change (vertexJoin.map (truncate j)).toOrderHom (collapseOrderHom _ 0) =
      collapseOrderHom _ 0
    rw [collapseOrderHom_zero]
    exact vertexJoin_map_zero _
  · -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
    change (vertexJoin.map (truncate j)).toOrderHom (collapseOrderHom _ i.succ) =
      collapseOrderHom _ i.succ
    rw [collapseOrderHom_succ]
    -- The vertex map of a composite in `SimplexCategory` is the composite of vertex maps.
    change (vertexJoin.map (truncate j)).toOrderHom
      (if stdSimplex.objMk₁.{u} j.castSucc i = 1 then _ else _) =
      if stdSimplex.objMk₁.{u} j.castSucc i = 1 then _ else _
    by_cases h : stdSimplex.objMk₁.{u} j.castSucc i = 1
    · simp only [h, ↓reduceIte]
      refine (vertexJoin_map_succ _ i).trans (congrArg Fin.succ (max_eq_left ?_))
      rwa [stdSimplex.objMk₁_apply_eq_one_iff, Fin.castSucc_le_castSucc_iff] at h
    · simp only [h, ↓reduceIte]
      exact vertexJoin_map_zero _

/-- **The contraction forgets the part of a family which is collapsed.** For a family `G` of
simplices of `coneSpace X x` parametrized by `Z ⊗ Δ[1]`, contracting `G (z, e)` along `e`, or the
value `G (z, 1)` at the end of the path, gives the same result. -/
@[reassoc]
private lemma lift_snd_coneContraction {Z : SSet.{u}} (G : Z ⊗ Δ[1] ⟶ (coneSpace X x : SSet.{u})) :
    lift G (snd _ _) ≫ coneContraction x =
      lift (fst _ _ ≫ ι₁ ≫ G) (snd _ _) ≫ coneContraction x := by
  rw [← cancel_mono (coneSpace X x).ι, Category.assoc, Category.assoc, coneContraction_ι]
  ext ⟨⟨n⟩⟩ ⟨z, e⟩
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (collapse (stdSimplex.objEquiv e)).op (G.app _ (z, e)).val =
    X.map (collapse (stdSimplex.objEquiv e)).op (G.app _ (ι₁.app _ z)).val
  obtain ⟨k, rfl⟩ := stdSimplex.objMk₁_surjective e
  induction k using Fin.lastCases with
  | last =>
    rw [stdSimplex.objEquiv_objMk₁_last, collapse_const_zero, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply]
    -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
    change X.map _ (X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op
        (G.app _ (z, _)).val) =
      X.map _ (X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op
        (G.app _ (ι₁.app _ z)).val)
    rw [show X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op
        (G.app _ (z, _)).val = x from (G.app _ _).property,
      show X.map (SimplexCategory.const ⦋0⦌ (vertexJoin.obj ⦋n⦌) 0).op
        (G.app _ (ι₁.app _ z)).val = x from (G.app _ _).property]
  | cast j =>
    rw [← collapse_comp_vertexJoin_map_truncate j, op_comp, Functor.map_comp_apply,
      Functor.map_comp_apply]
    congr 1
    have h₁ := congrArg Subtype.val (NatTrans.naturality_apply G (truncate j).op
      (show (Z ⊗ Δ[1] : SSet.{u}) _⦋n⦌ from (z, stdSimplex.objMk₁ j.castSucc)))
    have h₂ := congrArg Subtype.val (NatTrans.naturality_apply G (truncate j).op (ι₁.app _ z))
    refine h₁.symm.trans (Eq.trans ?_ h₂)
    congr 2
    refine Prod.ext rfl (stdSimplex.objEquiv.injective ((truncate_comp_objMk₁.{u} j).trans ?_))
    ext i : 3
    rfl

/-- Contracting the constant family at the identity of `x` gives the constant family. -/
@[reassoc]
private lemma lift_const_coneVertex_coneContraction {Z : SSet.{u}} (f : Z ⟶ Δ[1]) :
    lift (SSet.const (coneVertex x)) f ≫ coneContraction x = SSet.const (coneVertex x) := by
  rw [← cancel_mono (coneSpace X x).ι, Category.assoc, coneContraction_ι]
  ext ⟨⟨n⟩⟩ z
  -- Simplices of `vertexJoin.op ⋙ X` are simplices of `X`, on which the maps act by restriction.
  change X.map (collapse _).op (X.map (vertexJoin.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op
      (X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x)) =
    X.map (vertexJoin.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).op
      (X.map (SimplexCategory.const (vertexJoin.obj ⦋0⦌) ⦋0⦌ 0).op x)
  rw [map_map_const_zero, map_map_const_zero]

section comparison

variable (x y)

/-- The pushout-product of the comparison map `Hom^L_X(x, y) ⟶ Hom_X(x, y)` with the inclusion
`{0} ⟶ Δ[1]`, a left anodyne extension. -/
private noncomputable abbrev pushoutProduct :=
  Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (toMappingSpace x y) Λ[1, 0].ι

private lemma pushoutProductTop_aux :
    ((curriedTensor SSet.{u}).map (toMappingSpace x y)).app Λ[1, 0] ≫ SSet.const (coneVertex x) =
      ((curriedTensor SSet.{u}).obj (X.leftMappingSpace x y)).map Λ[1, 0].ι ≫
        toConeSpace x y ▷ Δ[1] ≫ coneContraction x := by
  simp only [curriedTensor_map_app, curriedTensor_obj_map, comp_const,
    whiskerLeft_horn_one_zero_ι, Category.assoc, ι₀_comp_assoc, ι₀_coneContraction]

/-- The map from the pushout-product to `coneSpace X x`: the constant map at the identity of `x`
on `Hom_X(x, y) ⊗ {0}`, and the contraction on `Hom^L_X(x, y) ⊗ Δ[1]`. -/
private noncomputable def pushoutProductTop :
    (pushoutProduct x y).pt ⟶ (coneSpace X x : SSet.{u}) :=
  (pushoutProduct x y).isPushout.desc (SSet.const (coneVertex x))
    (toConeSpace x y ▷ Δ[1] ≫ coneContraction x) (pushoutProductTop_aux x y)

private lemma inl_pushoutProductTop :
    (pushoutProduct x y).inl ≫ pushoutProductTop x y = SSet.const (coneVertex x) :=
  IsPushout.inl_desc _ _ _ _

private lemma inr_pushoutProductTop :
    (pushoutProduct x y).inr ≫ pushoutProductTop x y =
      toConeSpace x y ▷ Δ[1] ≫ coneContraction x :=
  IsPushout.inr_desc _ _ _ _

private lemma pushoutProductTop_comm :
    CommSq (pushoutProductTop x y) (pushoutProduct x y).ι (coneπ X x)
      ((β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι) := ⟨by
  refine (pushoutProduct x y).hom_ext ?_ ?_
  · rw [reassoc_of% inl_pushoutProductTop, const_coneVertex_coneπ,
      Functor.PushoutObjObj.inl_ι_assoc, curriedTensor_obj_map, whiskerLeft_horn_one_zero_ι,
      Category.assoc, mappingSpace.ι₀_braiding_uncurry_ι, comp_const]
  · rw [reassoc_of% inr_pushoutProductTop, Functor.PushoutObjObj.inr_ι_assoc,
      curriedTensor_map_app, BraidedCategory.braiding_naturality_left_assoc,
      ← uncurry_natural_left, toMappingSpace_comp_ι, uncurry_curry,
      SymmetricCategory.symmetry_assoc]⟩

variable [X.Quasicategory]

private instance : HasLiftingProperty (pushoutProduct x y).ι (coneπ X x) :=
  (leftAnodyneExtensions_pushoutObjObjι (pushoutProduct x y)
    (leftAnodyneExtensions.horn_ι (by decide : (0 : Fin 2) < Fin.last 1))).hasLiftingProperty _

/-- A lift `Hom_X(x, y) ⊗ Δ[1] ⟶ coneSpace X x` of the uncurried inclusion of `Hom_X(x, y)`
along the left fibration `coneSpace X x ⟶ X`, extending the contraction on `Hom^L_X(x, y)` and
the constant map at the identity of `x` on `Hom_X(x, y) ⊗ {0}`. -/
private noncomputable def pathLift :
    (X.mappingSpace x y : SSet.{u}) ⊗ Δ[1] ⟶ (coneSpace X x : SSet.{u}) :=
  (pushoutProductTop_comm x y).lift

@[reassoc]
private lemma pathLift_coneπ :
    pathLift x y ≫ coneπ X x = (β_ _ Δ[1]).hom ≫ uncurry (X.mappingSpace x y).ι :=
  (pushoutProductTop_comm x y).fac_right

@[reassoc]
private lemma ι₀_pathLift : ι₀ ≫ pathLift x y = SSet.const (coneVertex x) := by
  have h : (X.mappingSpace x y : SSet.{u}) ◁ Λ[1, 0].ι ≫ pathLift x y =
      SSet.const (coneVertex x) := by
    have h := (pushoutProduct x y).inl ≫= (pushoutProductTop_comm x y).fac_left
    rwa [Functor.PushoutObjObj.inl_ι_assoc, inl_pushoutProductTop, curriedTensor_obj_map] at h
  rw [← fstStdSimplexZeroIso_inv_whiskerLeft_stdSimplex_δ_one, Category.assoc,
    ← (horn.ι_ι 0 1 (by decide) : horn.ι 0 1 _ ≫ Λ[1, 0].ι = stdSimplex.δ 1),
    MonoidalCategory.whiskerLeft_comp, Category.assoc, h, comp_const, comp_const]

@[reassoc]
private lemma whiskerRight_pathLift :
    toMappingSpace x y ▷ Δ[1] ≫ pathLift x y = toConeSpace x y ▷ Δ[1] ≫ coneContraction x := by
  have h := (pushoutProduct x y).inr ≫= (pushoutProductTop_comm x y).fac_left
  rwa [Functor.PushoutObjObj.inr_ι_assoc, inr_pushoutProductTop, curriedTensor_map_app] at h

/-- The homotopy inverse `Hom_X(x, y) ⟶ Hom^L_X(x, y)` of the comparison map: the end of the
lifted path. -/
private noncomputable def inverse :
    (X.mappingSpace x y : SSet.{u}) ⟶ (X.leftMappingSpace x y : SSet.{u}) :=
  Subcomplex.lift ((ι₁ ≫ pathLift x y) ≫ (coneSpace X x).ι)
    (range_le_leftMappingSpace (ι₁ ≫ pathLift x y)
      (by rw [Category.assoc, pathLift_coneπ, mappingSpace.ι₁_braiding_uncurry_ι]))

@[reassoc]
private lemma inverse_toConeSpace : inverse x y ≫ toConeSpace x y = ι₁ ≫ pathLift x y := by
  rw [← cancel_mono (coneSpace X x).ι, Category.assoc, toConeSpace, Subcomplex.homOfLE_ι]
  exact Subcomplex.lift_ι _ _

private lemma toMappingSpace_inverse : toMappingSpace x y ≫ inverse x y = 𝟙 _ := by
  rw [← cancel_mono (toConeSpace x y), Category.assoc, inverse_toConeSpace, ← ι₁_comp_assoc,
    whiskerRight_pathLift, ι₁_comp_assoc, ι₁_coneContraction, Category.comp_id, Category.id_comp]

/-- The uncurried homotopy from `inverse ≫ toMappingSpace` to the identity of `Hom_X(x, y)`:
`(σ, γ, τ)` goes to the contraction at time `max σ τ` of the lifted path at time `σ`. -/
private noncomputable def homotopyAux : Δ[1] ⊗ ((X.mappingSpace x y : SSet.{u}) ⊗ Δ[1]) ⟶ X :=
  lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
    (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contractionLast 1).h) ≫
      coneContraction x ≫ coneπ X x

private lemma range_curry_homotopyAux_le :
    Subcomplex.range (curry (homotopyAux x y)) ≤ X.mappingSpace x y := by
  rw [range_le_mappingSpace_iff, uncurry_curry]
  constructor
  · -- At `σ = 0`, the lifted path is at the identity of `x`, which the contraction fixes.
    have e : stdSimplex.δ 1 ▷ _ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
        (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contractionLast 1).h) =
        lift (SSet.const (coneVertex x)) (stdSimplex.δ 1 ▷ _ ≫
          lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contractionLast 1).h) := by
      rw [comp_lift, ← Category.assoc, comp_lift, whiskerRight_fst, whiskerRight_snd_assoc,
        stdSimplex.δ_one_eq_const, comp_const, lift_const_zero_eq_comp_ι₀,
        Category.assoc, Category.assoc, ι₀_pathLift]
      simp only [comp_const]
    rw [homotopyAux, reassoc_of% e, lift_const_coneVertex_coneContraction_assoc,
      const_coneVertex_coneπ]
  · -- At `σ = 1`, the lifted path is at its end, which lies over `y`, and is not contracted.
    have e : stdSimplex.δ 0 ▷ _ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
        (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contractionLast 1).h) =
        (snd _ _ ≫ fst _ _ ≫ ι₁ ≫ pathLift x y) ≫ ι₁ := by
      rw [← lift_const_one_eq_comp_ι₁]
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [Category.assoc, lift_fst]
        have h : stdSimplex.δ 0 ▷ ((X.mappingSpace x y : SSet.{u}) ⊗ Δ[1]) ≫
            lift (snd _ _ ≫ fst _ _) (fst _ _) = snd _ _ ≫ fst _ _ ≫ ι₁ :=
          CartesianMonoidalCategory.hom_ext _ _ (by simp)
            (by simp [stdSimplex.δ_zero_eq_const, comp_const, ι₁])
        rw [reassoc_of% h]
      · simp only [Category.assoc, lift_snd]
        rw [← Category.assoc, comp_lift, whiskerRight_fst, whiskerRight_snd_assoc,
          stdSimplex.δ_zero_eq_const, comp_const]
        -- The vertex `1` of `Δ[1]` is its last vertex `Fin.last 1`.
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
      have e : (Δ[1] : SSet.{u}) ◁ ι₀ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
          (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contractionLast 1).h) =
          (β_ _ _).hom ≫ lift (pathLift x y) (snd _ _) := by
        rw [comp_lift, comp_lift, ← Category.assoc,
          whiskerLeft_comp_lift_snd_fst _ (ι₀_fst _), ← Category.assoc, comp_lift,
          whiskerLeft_fst, whiskerLeft_snd_assoc, ι₀_snd, comp_const, lift_const_zero_eq_comp_ι₀,
          Category.assoc, (stdSimplex.contractionLast 1).h₀, Category.comp_id, braiding_hom_snd]
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
      have e : (Δ[1] : SSet.{u}) ◁ ι₁ ≫ lift (lift (snd _ _ ≫ fst _ _) (fst _ _) ≫ pathLift x y)
          (lift (fst _ _) (snd _ _ ≫ snd _ _) ≫ (stdSimplex.contractionLast 1).h) =
          ((β_ _ _).hom ≫ pathLift x y) ≫ ι₁ := by
        rw [← lift_const_one_eq_comp_ι₁, comp_lift, ← Category.assoc,
          whiskerLeft_comp_lift_snd_fst _ (ι₁_fst _), ← Category.assoc, comp_lift,
          whiskerLeft_fst, whiskerLeft_snd_assoc, ι₁_snd, comp_const, lift_const_one_eq_comp_ι₁,
          Category.assoc, (stdSimplex.contractionLast 1).h₁, comp_const]
        -- The vertex `1` of `Δ[1]` is its last vertex `Fin.last 1`.
        rfl
      rw [homotopyAux, reassoc_of% e, ι₁_coneContraction_assoc, pathLift_coneπ,
        SymmetricCategory.symmetry_assoc])

/-- **The comparison of left mapping spaces is a weak homotopy equivalence** (HTT, §4.2.1):
for a quasicategory `X`, the comparison map `Hom^L_X(x, y) ⟶ Hom_X(x, y)` is a weak homotopy
equivalence. -/
instance isWeakHomotopyEquivalence_toMappingSpace :
    IsWeakHomotopyEquivalence (toMappingSpace x y) :=
  IsWeakHomotopyEquivalence.of_homotopy _ (g := inverse x y)
    (.mk' (fst _ _) (by rw [ι₀_fst, toMappingSpace_inverse]) (ι₁_fst _)) (homotopy x y)

end comparison

end leftMappingSpace

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
  have := modelCategoryQuillen.weakEquivalence_of_isWeakHomotopyEquivalence
    (leftMappingSpace.toMappingSpace x y)
  have := modelCategoryQuillen.weakEquivalence_of_isWeakHomotopyEquivalence
    (leftMappingSpace.toMappingSpace (f.app _ x) (f.app _ y))
  rw [← weakEquivalence_precomp_iff (leftMappingSpace.toMappingSpace x y),
    leftMappingSpace.toMappingSpace_comp_map, weakEquivalence_postcomp_iff]

end IsFullyFaithful

end SSet
