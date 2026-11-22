/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Topology.Category.TopCat.ULift
public import TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift
public import TauCeti.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import TauCeti.CategoryTheory.Functor.KanExtension.Dense

/-!
# Open cells, faithfulness, discrete spaces, and universe lift of geometric realization

Every point of the geometric realization `|X|` of `X : SSet` has the form `SSet.toTopObjMk x w`
(`SSet.exists_toTopObjMk`). Comparing `|X|` with the thin geometric realization of
`X ⋙ TopCat.discrete` (`SSet.toTopIsoGeometricRealization`) gives Milnor's open-cell bijection
onto nondegenerate simplices and interior coordinates (`SSet.ToTopCell`, `SSet.toTopCellEquiv`).
Evaluating at any interior point (`SSet.toTopObjMk_injective_of_weights_ne_zero`,
`SSet.toTopObjMk_barycenter_injective`) shows that `sSetTopAdj.unit.app X` is a monomorphism,
`SSet.toTop` is faithful, and `SSet.toTopPoint` is injective. We also identify realizations of
constant maps (`SSet.toTop_map_const`), discrete simplicial sets (`SSet.toTopConstIso`), and
universe lifts (`SSet.toTopUliftNatIso`, `SSet.toTopUliftIso`, `SSet.toTopUliftHomeomorph`).

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. (2) 65
  (1957), 357–362, Lemma 1.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section I.2.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity

universe v u

namespace SSet

section Points

variable {X : SSet.{u}}

/-- The point of `|X|` given by a vertex `x` of `X` via `(sSetTopAdj.unit.app X).app _ x`. -/
noncomputable def toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) : |X| :=
  TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app _ x)

lemma toTopPoint_def {X : SSet.{u}} (x : X _⦋0⦌) :
    toTopPoint x = TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app X).app _ x) :=
  (rfl)

/-- The realization of a map sends the point of a vertex to the point of its image. -/
@[simp] lemma toTop_map_toTopPoint {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    toTop.map f (toTopPoint x) = toTopPoint (f.app _ x) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (sSetTopAdj.unit.naturality f) _) x
  dsimp at h
  rw [toTopPoint, toTopPoint, h, TauCeti.TopCat.toSSetObj₀Equiv_toSSet_map_app]

/-- `toTopPoint` agrees with `toTopObjMk` at any point of `StdSimplex ℝ (Fin 1)`. -/
lemma toTopPoint_eq_toTopObjMk (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopPoint x = toTopObjMk x w := by
  rw [toTopPoint_def, toTopObjMk_def, TopCat.toSSetObj₀Equiv_apply, Subsingleton.elim default w]

/-- On a `0`-simplex, `toTopObjMk` is independent of the coordinates and equals `toTopPoint`. -/
@[simp] lemma toTopObjMk_zero (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopObjMk x w = toTopPoint x := (toTopPoint_eq_toTopObjMk x w).symm

/-- At `StdSimplex.single i`, `toTopObjMk x` gives the realized `i`-th vertex of `x`. -/
@[simp] lemma toTopObjMk_single {n : ℕ} (x : X _⦋n⦌) (i : Fin (n + 1)) :
    toTopObjMk x (StdSimplex.single i) =
      toTopPoint (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) := by
  have hs : (StdSimplex.single i : StdSimplex ℝ (Fin (n + 1))) =
      StdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) (StdSimplex.single 0) := by
    rw [StdSimplex.map_single]; rfl
  rw [hs, ← toTopObjMk_map, toTopObjMk_zero]

/-- `toTopObjMk x w` is the image of `w` under the realized simplex `|Δ[n]| ⟶ |X|` of `x`. -/
lemma toTopObjMk_eq_toTop_map {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk x w = toTop.map (yonedaEquiv.symm x) (⦋n⦌.toTopHomeo.symm w) := by
  rw [toTopObjMk_def, TauCeti.TopCat.toSSetObjEquiv_apply, sSetTopAdj_unit_app_app_down,
    ← ConcreteCategory.comp_apply, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Evaluating `⦋n⦌.toTopHomeo` on a realized simplex `x` of `Δ[n]` pushes forward barycentric
coordinates along `stdSimplex.objEquiv x`. -/
@[simp] lemma stdSimplex.toTopHomeo_toTopObjMk {m n : ℕ} (x : (Δ[n] : SSet.{u}) _⦋m⦌)
    (w : StdSimplex ℝ (Fin (m + 1))) :
    ⦋n⦌.toTopHomeo.{u} (toTopObjMk x w) = w.map (stdSimplex.objEquiv.{u} x) := by
  obtain ⟨θ, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [Equiv.apply_symm_apply, toTopObjMk_eq_toTop_map, ← yonedaEquiv_map θ,
    Equiv.symm_apply_apply, SimplexCategory.toTopHomeo_naturality_apply,
    Homeomorph.apply_symm_apply]

/-- `SSet.const y` realizes to `TopCat.const (toTopPoint y)` (dual to `TopCat.toSSet_map_const`). -/
@[simp] lemma toTop_map_const (X : SSet.{u}) {Y : SSet.{u}} (y : Y _⦋0⦌) :
    toTop.map (SSet.const (X := X) y) = TopCat.const (X := |X|) (toTopPoint y) :=
  toTop_hom_ext fun _ _ _ ↦ by
    rw [toTop_map_toTopObjMk, SSet.const_app, TypeCat.ofHom_apply, toTopObjMk_map, toTopObjMk_zero,
      TopCat.const_apply]

end Points

section Discrete

private noncomputable def toTopConstHom (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ⟶ TopCat.discrete.obj S :=
  (sSetTopAdj.homEquiv _ (TopCat.discrete.obj S)).symm
    ((constHomEquiv S).symm fun s ↦ TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S).symm s)

private lemma toTopConstHom_toTopPoint (S : Type u) (s : S) :
    toTopConstHom S (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s := by
  rw [toTopConstHom, toTopPoint_eq_toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s
    default, apply_toTopObjMk, Equiv.apply_symm_apply]
  have h0 := constHomEquiv_symm_app_zero S
    (fun t ↦ TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S).symm t) s
  dsimp at h0 ⊢
  rw [h0, ← TopCat.toSSetObj₀Equiv_apply]
  exact Equiv.apply_symm_apply (TopCat.toSSetObj₀Equiv (X := TopCat.discrete.obj S)) s

private noncomputable def toTopConstInv (S : Type u) :
    TopCat.discrete.obj S ⟶ |(Functor.const SimplexCategoryᵒᵖ).obj S| :=
  TopCat.ofHom (X := TopCat.discrete.obj S)
    ⟨fun s ↦ toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s, continuous_bot⟩

private lemma toTopConstInv_apply (S : Type u) (s : S) :
    toTopConstInv S s = toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s := (rfl)

/-- Every point `toTopObjMk s w` in the realization of the constant simplicial set on `S` collapses
to the vertex `toTopPoint s`. -/
@[simp] lemma toTopObjMk_const (S : Type u) {n : ℕ} (s : S) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s w =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s := by
  have hs : s = ((Functor.const SimplexCategoryᵒᵖ).obj S).map
      (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op s := by simp
  conv_lhs => rw [hs]
  rw [toTopObjMk_map, toTopObjMk_zero]

/-- The geometric realization of the constant simplicial set on `S` is isomorphic in `TopCat` to
the discrete topological space on `S`. -/
noncomputable def toTopConstIso (S : Type u) :
    |(Functor.const SimplexCategoryᵒᵖ).obj S| ≅ TopCat.discrete.obj S where
  hom := toTopConstHom S
  inv := toTopConstInv S
  hom_inv_id := toTop_hom_ext fun _ _ _ ↦ by
    simp only [ConcreteCategory.comp_apply, TopCat.id_app, toTopObjMk_const,
      toTopConstHom_toTopPoint, toTopConstInv_apply]
  inv_hom_id := by ext s; exact toTopConstHom_toTopPoint S s

@[simp] lemma toTopConstIso_inv_apply (S : Type u) (s : S) :
    (toTopConstIso S).inv s = toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s :=
  toTopConstInv_apply S s

@[simp] lemma toTopConstIso_hom_toTopPoint (S : Type u) (s : S) :
    (toTopConstIso S).hom (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj S) s) = s :=
  toTopConstHom_toTopPoint S s

end Discrete

section Cells

private noncomputable def toTopToGeometricRealizationHom (X : SSet.{u}) :
    |X| ⟶ SimplicialObject.geometricRealization (X ⋙ TopCat.discrete) :=
  (sSetTopAdj.homEquiv X (SimplicialObject.geometricRealization (X ⋙ TopCat.discrete))).symm
    { app m := ↾fun x ↦
        ((SimplicialObject.geometricRealization (X ⋙ TopCat.discrete)).toSSetObjEquiv m).symm
          (let d : (X ⋙ TopCat.discrete) _⦋m.unop.len⦌ :=
            X.map (eqToHom (by cases m using Opposite.rec; cases ‹SimplexCategory›; rfl)) x
          ⟨fun w ↦ SimplicialObject.geometricRealization.ι (X ⋙ TopCat.discrete) m.unop.len
            (d, ULift.up w),
            (SimplicialObject.geometricRealization.ι (X ⋙ TopCat.discrete)
                m.unop.len).continuous.comp
              (Continuous.prodMk
                (continuous_const (X := StdSimplex ℝ (Fin (m.unop.len + 1)))
                  (Y := ↑((X ⋙ TopCat.discrete) _⦋m.unop.len⦌)) (y := d))
                continuous_uliftUp)⟩)
      naturality m₁ m₂ f := by
        obtain ⟨⟨d₁⟩, rfl⟩ : ∃ a, m₁ = op a := ⟨m₁.unop, rfl⟩
        obtain ⟨⟨d₂⟩, rfl⟩ : ∃ a, m₂ = op a := ⟨m₂.unop, rfl⟩
        obtain ⟨g, rfl⟩ : ∃ g : ⦋d₂⦌ ⟶ ⦋d₁⦌, f = g.op := ⟨f.unop, rfl⟩
        ext x
        apply ((SimplicialObject.geometricRealization
          (X ⋙ TopCat.discrete)).toSSetObjEquiv (op ⦋d₂⦌)).injective
        apply ContinuousMap.ext
        intro w
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply, TypeCat.ofHom_apply,
          TopCat.toSSetObjEquiv_naturality_apply, Equiv.apply_symm_apply, ContinuousMap.coe_mk,
          eqToHom_refl, CategoryTheory.Functor.map_id, types_id_apply]
        exact (SimplicialObject.geometricRealization.ι_map
            (X ⋙ TopCat.discrete) g x (ULift.up.{u} w)).trans
          (congrArg (fun t ↦ SimplicialObject.geometricRealization.ι
              (X ⋙ TopCat.discrete) d₁ (x, t))
            (ULift.ext (SimplexCategory.toTop_map_down.{u} g (ULift.up.{u} w)).symm)) }

private lemma toTopToGeometricRealizationHom_toTopObjMk {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopToGeometricRealizationHom X (toTopObjMk x w) =
      SimplicialObject.geometricRealization.ι (X ⋙ TopCat.discrete) n (x, ULift.up w) := by
  rw [toTopToGeometricRealizationHom, apply_toTopObjMk, Equiv.apply_symm_apply]
  simp only [TypeCat.ofHom_apply, Equiv.apply_symm_apply, ContinuousMap.coe_mk, eqToHom_refl,
    CategoryTheory.Functor.map_id, types_id_apply]

private noncomputable def toTopFromGeometricRealizationHom (X : SSet.{u}) :
    SimplicialObject.geometricRealization (X ⋙ TopCat.discrete) ⟶ |X| :=
  TopCat.ofHom <| SimplicialObject.geometricRealization.desc (Z := |X|)
    (fun n ↦
      ⟨fun p : (X ⋙ TopCat.discrete) _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌ ↦
          toTopObjMk p.1 p.2.down,
        letI : DiscreteTopology ((X ⋙ TopCat.discrete) _⦋n⦌) := ⟨rfl⟩
        continuous_prod_of_discrete_left.mpr fun x ↦
          (continuous_toTopObjMk x).comp continuous_uliftDown⟩)
    fun m n f x t ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map, ContinuousMap.coe_mk]
      exact (toTopObjMk_map f x t.down).trans
        (congrArg (toTopObjMk x) (SimplexCategory.toTop_map_down f t).symm)

private lemma toTopFromGeometricRealizationHom_ι {X : SSet.{u}} {n : ℕ}
    (x : (X ⋙ TopCat.discrete) _⦋n⦌) (t : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    toTopFromGeometricRealizationHom X
        (SimplicialObject.geometricRealization.ι (X ⋙ TopCat.discrete) n (x, t)) =
      toTopObjMk x t.down :=
  SimplicialObject.geometricRealization.desc_ι _ _ n (x, t)

/-- The geometric realization `|X|` is isomorphic in `TopCat` to the thin geometric realization of
`X` viewed as a discrete simplicial space `X ⋙ TopCat.discrete`. -/
noncomputable def toTopIsoGeometricRealization (X : SSet.{u}) :
    |X| ≅ SimplicialObject.geometricRealization (X ⋙ TopCat.discrete) where
  hom := toTopToGeometricRealizationHom X
  inv := toTopFromGeometricRealizationHom X
  hom_inv_id := toTop_hom_ext fun n x w ↦ by
    rw [ConcreteCategory.comp_apply, TopCat.id_app, toTopToGeometricRealizationHom_toTopObjMk]
    exact toTopFromGeometricRealizationHom_ι (X := X) x (ULift.up w)
  inv_hom_id := SimplicialObject.geometricRealization.hom_ext (X ⋙ TopCat.discrete) fun n x t ↦ by
    rw [ConcreteCategory.comp_apply, TopCat.id_app, toTopFromGeometricRealizationHom_ι]
    exact toTopToGeometricRealizationHom_toTopObjMk (X := X) x t.down

@[simp] lemma toTopIsoGeometricRealization_hom_toTopObjMk {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopIsoGeometricRealization X).hom (toTopObjMk x w) =
      SimplicialObject.geometricRealization.ι (X ⋙ TopCat.discrete) n (x, ULift.up w) :=
  toTopToGeometricRealizationHom_toTopObjMk x w

lemma toTopIsoGeometricRealization_inv_ι {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (t : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    (toTopIsoGeometricRealization X).inv
        (SimplicialObject.geometricRealization.ι (X ⋙ TopCat.discrete) n (x, t)) =
      toTopObjMk x t.down :=
  toTopFromGeometricRealizationHom_ι x t

/-- Every point of `|X|` lies in the image of `toTopObjMk` for some simplex of `X`. -/
lemma exists_toTopObjMk {X : SSet.{u}} (p : |X|) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))), p = toTopObjMk x w := by
  obtain ⟨n, x, t, ht⟩ := SimplicialObject.geometricRealization.ι_jointly_surjective
    (X ⋙ TopCat.discrete) ((toTopIsoGeometricRealization X).hom p)
  refine ⟨n, x, t.down, ?_⟩
  rw [← toTopIsoGeometricRealization_inv_ι x t, ht, ← ConcreteCategory.comp_apply,
    Iso.hom_inv_id, TopCat.id_app]

/-- Every point of `|X|` can be joined by a path in `|X|` to the realization of a vertex of
`X`. -/
lemma exists_joined_toTopPoint {X : SSet.{u}} (p : |X|) :
    ∃ x : X _⦋0⦌, Joined (toTopPoint x) p := by
  obtain ⟨n, s, w, rfl⟩ := exists_toTopObjMk p
  exact ⟨X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op s, by
    rw [← toTopObjMk_single]; exact (PathConnectedSpace.joined _ w).map (continuous_toTopObjMk s)⟩

/-- The geometric realization `|X|` is nonempty if and only if `X` has a `0`-simplex. -/
@[simp] lemma nonempty_toTop_iff (X : SSet.{u}) : Nonempty |X| ↔ X.Nonempty :=
  ⟨fun ⟨p⟩ ↦ let ⟨_, x, _, _⟩ := exists_toTopObjMk p; .mk x, fun ⟨x⟩ ↦ ⟨toTopPoint x⟩⟩

/-- The geometric realization `|X|` is empty if and only if `X` has no `0`-simplices. -/
@[simp] lemma isEmpty_toTop_iff (X : SSet.{u}) : IsEmpty |X| ↔ IsEmpty (X _⦋0⦌) := by
  rw [← not_nonempty_iff, nonempty_toTop_iff, SSet.Nonempty, not_nonempty_iff]

instance isEmpty_toTop (X : SSet.{u}) [IsEmpty (X _⦋0⦌)] : IsEmpty |X| :=
  (isEmpty_toTop_iff X).2 ‹_›

instance nonempty_toTop (X : SSet.{u}) [X.Nonempty] : Nonempty |X| := (nonempty_toTop_iff X).2 ‹_›

/-- An open cell point of `|X|`: a dimension `dim`, a nondegenerate `dim`-simplex of `X`, and an
interior point of `StdSimplex ℝ (Fin (dim + 1))`. -/
@[ext] structure ToTopCell (X : SSet.{u}) : Type u where
  /-- Dimension of the open cell. -/
  dim : ℕ
  /-- Nondegenerate `dim`-simplex of `X`. -/
  simplex : X.nonDegenerate dim
  /-- Interior coordinates in `StdSimplex ℝ (Fin (dim + 1))`. -/
  point : {w : StdSimplex ℝ (Fin (dim + 1)) // ∀ j, 0 < w.weights j}

private noncomputable def normalFormEquivToTopCell (X : SSet.{u}) :
    SimplicialObject.geometricRealization.NormalForm (X ⋙ TopCat.discrete) ≃ ToTopCell X where
  toFun c :=
    ⟨c.dim, c.simplex, ⟨c.point.val.down, SimplexCategory.mem_toTopInterior_iff.1 c.point.property⟩⟩
  invFun c :=
    ⟨c.dim, c.simplex,
      ⟨ULift.up c.point.val, SimplexCategory.mem_toTopInterior_iff.2 c.point.property⟩⟩
  left_inv c := by rcases c with ⟨_, _, ⟨⟨_⟩, _⟩⟩; rfl
  right_inv c := by rcases c with ⟨_, _, ⟨_, _⟩⟩; rfl

/-- Milnor's open-cell bijection `|X| ≃ SSet.ToTopCell X` onto pairs of a nondegenerate simplex
of `X` and an interior point of the standard simplex, obtained by transporting
`SimplicialObject.geometricRealization.NormalForm.realizationEquiv` along
`toTopIsoGeometricRealization X`. -/
noncomputable def toTopCellEquiv (X : SSet.{u}) : |X| ≃ ToTopCell X :=
  (TopCat.homeoOfIso (toTopIsoGeometricRealization X)).toEquiv.trans
    ((SimplicialObject.geometricRealization.NormalForm.realizationEquiv
      (X ⋙ TopCat.discrete)).symm.trans (normalFormEquivToTopCell X))

@[simp] lemma toTopCellEquiv_symm_apply {X : SSet.{u}} (c : ToTopCell X) :
    (toTopCellEquiv X).symm c = toTopObjMk c.simplex.val c.point.val := by
  dsimp only [toTopCellEquiv, normalFormEquivToTopCell]
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
    SimplicialObject.geometricRealization.NormalForm.realizationEquiv_apply,
    SimplicialObject.geometricRealization.NormalForm.toRealization_def]
  exact (TopCat.homeoOfIso_symm_apply (toTopIsoGeometricRealization X) _).trans
    (toTopIsoGeometricRealization_inv_ι _ _)

@[simp] lemma toTopCellEquiv_toTopObjMk {X : SSet.{u}} {n : ℕ}
    {x : X _⦋n⦌} (hx : x ∈ X.nonDegenerate n) {w : StdSimplex ℝ (Fin (n + 1))}
    (hw : ∀ j, 0 < w.weights j) :
    toTopCellEquiv X (toTopObjMk x w) = ⟨n, ⟨x, hx⟩, ⟨w, hw⟩⟩ := by
  dsimp only [toTopCellEquiv, Equiv.trans_apply]
  rw [Homeomorph.coe_toEquiv, TopCat.homeoOfIso_apply,
    toTopIsoGeometricRealization_hom_toTopObjMk]
  -- `X.nonDegenerate n` and `SSet.nonDegenerate ((X ⋙ TopCat.discrete) ⋙ forget TopCat) n`
  -- agree definitionally, so `normalForm_ι_of_nonDegenerate` applies directly.
  have hnf := SimplicialObject.geometricRealization.normalForm_ι_of_nonDegenerate
    (X ⋙ TopCat.discrete) hx (SimplexCategory.mem_toTopInterior_iff.2 hw)
  rw [← SimplicialObject.geometricRealization.NormalForm.realizationEquiv_symm_apply] at hnf
  exact congrArg (normalFormEquivToTopCell X) hnf

/-- Evaluating `toTopObjMk · w` at any interior point `w` of `StdSimplex ℝ (Fin (n + 1))` is
injective on `n`-simplices. -/
theorem toTopObjMk_injective_of_weights_ne_zero (X : SSet.{u}) {n : ℕ}
    {w : StdSimplex ℝ (Fin (n + 1))} (hw : ∀ j, w.weights j ≠ 0) :
    Function.Injective fun x : X _⦋n⦌ ↦ toTopObjMk x w := fun x₁ x₂ h ↦ by
  dsimp only at h
  obtain ⟨r₁, π₁, _, z₁, rfl⟩ := X.exists_nonDegenerate x₁
  obtain ⟨r₂, π₂, _, z₂, rfl⟩ := X.exists_nonDegenerate x₂
  rw [toTopObjMk_map, toTopObjMk_map] at h
  have hc : toTopCellEquiv X (toTopObjMk z₁.val (w.map π₁)) =
      toTopCellEquiv X (toTopObjMk z₂.val (w.map π₂)) :=
    congrArg (toTopCellEquiv X) h
  rw [toTopCellEquiv_toTopObjMk z₁.property (fun j ↦ ((w.map π₁).nonneg j).lt_iff_ne'.2
        (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π₁ hw j)),
    toTopCellEquiv_toTopObjMk z₂.property (fun j ↦ ((w.map π₂).nonneg j).lt_iff_ne'.2
        (SimplexCategory.weights_stdSimplex_map_ne_zero_of_epi π₂ hw j))] at hc
  obtain rfl : r₁ = r₂ := congrArg ToTopCell.dim hc
  injection hc with _ hsimp hp
  obtain rfl : z₁ = z₂ := Subtype.ext (congrArg Subtype.val hsimp)
  have hcoords : w.map π₁ = w.map π₂ := congrArg Subtype.val hp
  rw [SimplexCategory.eq_of_stdSimplex_map_eq_of_weights_ne_zero hw hcoords]

/-- Evaluating `toTopObjMk · StdSimplex.barycenter` on `n`-simplices is injective. -/
theorem toTopObjMk_barycenter_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective fun x : X _⦋n⦌ ↦
      toTopObjMk x (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) :=
  toTopObjMk_injective_of_weights_ne_zero X fun _ ↦ by
    rw [StdSimplex.weights_barycenter_apply, Fintype.card_fin]; positivity

/-- The unit `X ⟶ Sing |X|` of `sSetTopAdj` is componentwise injective. -/
theorem sSetTopAdj_unit_app_app_injective (X : SSet.{u}) (m : SimplexCategoryᵒᵖ) :
    Function.Injective ((sSetTopAdj.unit.app X).app m) := by
  rcases m with ⟨⟨n⟩⟩
  exact fun _ _ h ↦ toTopObjMk_barycenter_injective X n (by simp only [toTopObjMk_def, h])

/-- The unit `X ⟶ Sing |X|` of `sSetTopAdj` is a monomorphism. -/
instance mono_sSetTopAdj_unit_app (X : SSet.{u}) : Mono (sSetTopAdj.unit.app X) := by
  rw [NatTrans.mono_iff_mono_app]
  exact fun m ↦ (mono_iff_injective _).2 (sSetTopAdj_unit_app_app_injective X m)

/-- The geometric realization functor `SSet.toTop` is faithful. -/
instance : toTop.{u}.Faithful := sSetTopAdj.faithful_L_of_mono_unit_app

/-- Distinct `0`-simplices of `X` map to distinct points of `|X|`. -/
theorem toTopPoint_injective (X : SSet.{u}) : Function.Injective (toTopPoint (X := X)) :=
  fun _ _ h ↦ toTopObjMk_barycenter_injective X 0 (by simpa using h)

@[simp] lemma toTopPoint_inj {X : SSet.{u}} {x₁ x₂ : X _⦋0⦌} :
    toTopPoint x₁ = toTopPoint x₂ ↔ x₁ = x₂ := (toTopPoint_injective X).eq_iff

end Cells

section ULift

/-- Evaluating `SimplexCategory.toTopUliftIso.hom.app m` on the realized standard simplex point of
`w` recovers the universe lift of the corresponding point in `SimplexCategory.toTop.{u}.obj m`. -/
private lemma simplexToTopUliftIso_hom_app_toTopSimplex (m : SimplexCategory)
    (w : StdSimplex ℝ (Fin (m.len + 1))) :
    SimplexCategory.toTopUliftIso.{u, v}.hom.app m
        (toTopSimplex.{max u v}.hom.app m (m.toTopHomeo.{max u v}.symm w)) =
      (SimplexCategory.toTop.{u}.obj m).uliftFunctorObjHomeo.{v}
        (toTopSimplex.{u}.hom.app m (m.toTopHomeo.{u}.symm w)) := by
  rw [SimplexCategory.toTopUliftIso_hom_app_apply]
  refine congrArg ((SimplexCategory.toTop.{u}.obj m).uliftFunctorObjHomeo.{v}) ?_
  apply ((SimplexCategory.toTop₀.obj m).uliftFunctorObjHomeo.{u}).symm.injective
  -- Both sides evaluate to `m.toTopHomeo (m.toTopHomeo.symm w)` (`toTop₀.obj m` is `StdSimplex`).
  exact (m.toTopHomeo.{max u v}.apply_symm_apply w).trans
    (m.toTopHomeo.{u}.apply_symm_apply w).symm

private noncomputable def toTopUliftRestrictIso :
    stdSimplex.{u} ⋙ uliftFunctor.{v, u} ⋙ toTop.{max u v} ≅
      stdSimplex.{u} ⋙ toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight stdSimplexUliftIso.{u, v} toTop.{max u v} ≪≫
    toTopSimplex.{max u v} ≪≫
    SimplexCategory.toTopUliftIso.{u, v} ≪≫
    Functor.isoWhiskerRight toTopSimplex.{u}.symm TopCat.uliftFunctor.{v, u} ≪≫
    Functor.associator _ _ _

private local instance : PreservesColimitsOfSize.{0, u} uliftFunctor.{v, u} :=
  inferInstanceAs (PreservesColimitsOfSize.{0, u}
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (Type u) (Type max u v)).obj
      CategoryTheory.uliftFunctor.{v, u}))

private local instance : stdSimplex.{u}.IsDense := inferInstanceAs uliftYoneda.{u}.IsDense

private local instance :
    Functor.IsLeftKanExtension (uliftFunctor.{v, u} ⋙ toTop.{max u v})
      (𝟙 (stdSimplex.{u} ⋙ uliftFunctor.{v, u} ⋙ toTop.{max u v})) :=
  Functor.IsDense.isLeftKanExtension_id stdSimplex.{u} (uliftFunctor.{v, u} ⋙ toTop.{max u v})

private local instance :
    Functor.IsLeftKanExtension (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})
      (𝟙 (stdSimplex.{u} ⋙ toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})) :=
  Functor.IsDense.isLeftKanExtension_id stdSimplex.{u} (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})

/-- Natural isomorphism `|uliftFunctor.obj ·| ≅ uliftFunctor.obj |·|`. -/
noncomputable def toTopUliftNatIso :
    uliftFunctor.{v, u} ⋙ toTop.{max u v} ≅ toTop.{u} ⋙ TopCat.uliftFunctor.{v, u} :=
  Functor.leftKanExtensionUniqueOfIso
    (uliftFunctor.{v, u} ⋙ toTop.{max u v}) (𝟙 _)
    toTopUliftRestrictIso.{v, u}
    (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (𝟙 _)

/-- Geometric realization of a universe-lifted simplicial set is isomorphic in `TopCat` to the
universe lift of its geometric realization (see `SSet.toTopUliftNatIso` for naturality in `X`). -/
noncomputable def toTopUliftIso (X : SSet.{u}) :
    |uliftFunctor.{v, u}.obj X| ≅ TopCat.uliftFunctor.{v, u}.obj |X| :=
  toTopUliftNatIso.{v, u}.app X

@[simp] lemma toTopUliftNatIso_hom_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.hom.app X = (toTopUliftIso.{v, u} X).hom := (rfl)

@[simp] lemma toTopUliftNatIso_inv_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.inv.app X = (toTopUliftIso.{v, u} X).inv := (rfl)

@[simp] lemma toTopUliftNatIso_app (X : SSet.{u}) :
    toTopUliftNatIso.{v, u}.app X = toTopUliftIso.{v, u} X := (rfl)

private lemma toTopUliftNatIso_hom_app_stdSimplex (m : SimplexCategory) :
    toTopUliftNatIso.{v, u}.hom.app (stdSimplex.{u}.obj m) =
      toTopUliftRestrictIso.{v, u}.hom.app m := by
  have h := Functor.descOfIsLeftKanExtension_fac_app
    (uliftFunctor.{v, u} ⋙ toTop.{max u v}) (𝟙 _)
    (toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (toTopUliftRestrictIso.{v, u}.hom ≫ 𝟙 _) m
  simpa [toTopUliftNatIso, Functor.leftKanExtensionUniqueOfIso] using h

@[simp]
lemma toTopUliftIso_hom_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).hom (toTopObjMk x w) =
      |X|.uliftFunctorObjHomeo (toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w) := by
  let x' : X _⦋n⦌ := (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x
  have hfac : yonedaEquiv.symm x =
      stdSimplexUliftIso.{u, v}.inv.app ⦋n⦌ ≫ uliftFunctor.{v, u}.map (yonedaEquiv.symm x') := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, stdSimplexUliftIso_inv_app,
      uliftFunctorHomEquiv_symm_apply, Equiv.apply_symm_apply,
      uliftFunctor_map_uliftFunctorObjEquiv, yonedaEquiv_symm_app_id, Equiv.apply_symm_apply]
  have hnat := ConcreteCategory.congr_hom
    (toTopUliftNatIso.{v, u}.hom.naturality (yonedaEquiv.symm x'))
    (toTop.{max u v}.map (stdSimplexUliftIso.{u, v}.inv.app ⦋n⦌) (⦋n⦌.toTopHomeo.symm w))
  have hstd : toTopUliftNatIso.{v, u}.hom.app (stdSimplex.{u}.obj ⦋n⦌)
        (toTop.{max u v}.map (stdSimplexUliftIso.{u, v}.inv.app ⦋n⦌) (⦋n⦌.toTopHomeo.symm w)) =
      |stdSimplex.{u}.obj ⦋n⦌|.uliftFunctorObjHomeo (⦋n⦌.toTopHomeo.symm w) := by
    rw [toTopUliftNatIso_hom_app_stdSimplex, toTopUliftRestrictIso]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.id_comp, Category.comp_id, ConcreteCategory.comp_apply,
      ← Functor.map_comp_apply, Iso.inv_hom_id_app]
    rw [CategoryTheory.Functor.map_id, TopCat.id_app,
      simplexToTopUliftIso_hom_app_toTopSimplex,
      TopCat.uliftFunctorObjHomeo_naturality_apply, ← ConcreteCategory.comp_apply,
      Iso.hom_inv_id_app, TopCat.id_app]
    -- `(stdSimplex ⋙ toTop).obj ⦋n⦌` is definitionally `toTop.obj Δ[n]`.
    rfl
  rw [toTopObjMk_eq_toTop_map, hfac, toTop.map_comp, ConcreteCategory.comp_apply,
    ← toTopUliftNatIso_hom_app]
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [← ConcreteCategory.comp_apply, hnat, ConcreteCategory.comp_apply, hstd,
    TopCat.uliftFunctorObjHomeo_naturality_apply, ← toTopObjMk_eq_toTop_map]

@[simp]
lemma toTopUliftIso_inv_uliftFunctorObjHomeo_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftIso.{v, u} X).inv (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
  have h := toTopUliftIso_hom_toTopObjMk.{v, u} (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w
  rw [Equiv.symm_apply_apply] at h
  rw [← h, ← ConcreteCategory.comp_apply, Iso.hom_inv_id, TopCat.id_app]

@[simp]
lemma toTopUliftIso_hom_toTopPoint {X : SSet.{u}} (x : (uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    (toTopUliftIso.{v, u} X).hom (toTopPoint x) =
      |X|.uliftFunctorObjHomeo (toTopPoint ((X.uliftFunctorObjEquiv.{v} (op ⦋0⦌)).symm x)) := by
  rw [toTopPoint_eq_toTopObjMk x default, toTopUliftIso_hom_toTopObjMk, toTopObjMk_zero]

@[simp]
lemma toTopUliftIso_inv_uliftFunctorObjHomeo_toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    (toTopUliftIso.{v, u} X).inv (|X|.uliftFunctorObjHomeo (toTopPoint x)) =
      toTopPoint (X.uliftFunctorObjEquiv.{v} (op ⦋0⦌) x) := by
  rw [toTopPoint_eq_toTopObjMk x default, toTopUliftIso_inv_uliftFunctorObjHomeo_toTopObjMk,
    toTopObjMk_zero]

/-- Homeomorphism `|X| ≃ₜ |uliftFunctor.obj X|` between the geometric realization of `X` and the
geometric realization of its universe lift, matching `TopCat.uliftFunctorObjHomeo`. -/
noncomputable def toTopUliftHomeomorph (X : SSet.{u}) :
    |X| ≃ₜ |uliftFunctor.{v, u}.obj X| :=
  |X|.uliftFunctorObjHomeo.trans (TopCat.homeoOfIso (toTopUliftIso.{v, u} X)).symm

@[simp] lemma toTopUliftHomeomorph_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopUliftHomeomorph.{v, u} X (toTopObjMk x w) =
      toTopObjMk (X.uliftFunctorObjEquiv.{v} (op ⦋n⦌) x) w := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_symm_toTopObjMk {X : SSet.{u}} {n : ℕ}
    (x : (uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopObjMk x w) =
      toTopObjMk ((X.uliftFunctorObjEquiv.{v} (op ⦋n⦌)).symm x) w := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_toTopPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    toTopUliftHomeomorph.{v, u} X (toTopPoint x) =
      toTopPoint (X.uliftFunctorObjEquiv.{v} (op ⦋0⦌) x) := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_symm_toTopPoint {X : SSet.{u}}
    (x : (uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopPoint x) =
      toTopPoint ((X.uliftFunctorObjEquiv.{v} (op ⦋0⦌)).symm x) := by
  simp [toTopUliftHomeomorph]

@[simp] lemma toTopUliftHomeomorph_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y) (p : |X|) :
    toTop.map (uliftFunctor.{v, u}.map f) (toTopUliftHomeomorph.{v, u} X p) =
      toTopUliftHomeomorph.{v, u} Y (toTop.map f p) := by
  obtain ⟨_, _, _, rfl⟩ := exists_toTopObjMk p; simp

@[simp] lemma toTopUliftHomeomorph_symm_naturality_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    (p : |uliftFunctor.{v, u}.obj X|) :
    (toTopUliftHomeomorph.{v, u} Y).symm (toTop.map (uliftFunctor.{v, u}.map f) p) =
      toTop.map f ((toTopUliftHomeomorph.{v, u} X).symm p) := by
  obtain ⟨_, _, _, rfl⟩ := exists_toTopObjMk p; simp

end ULift

end SSet
