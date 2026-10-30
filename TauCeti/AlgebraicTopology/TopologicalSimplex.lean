/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.LocallyPathConnectedSpaceStdSimplex
public import TauCeti.Topology.Category.TopCat.Action

/-!
# The topological simplices and the singular simplices of a space

The topological `n`-simplex is a standard simplex on a finite nonempty type, up to a universe
lift, hence contractible and in particular simply connected, and locally path connected.  This
file also names its initial vertex, and the continuous map on the topological `n`-simplex that
underlies a singular `n`-simplex of a space.

## Main declarations

* `SimplexCategory.toTopInitialVertex`: the initial vertex of the topological `n`-simplex, and
  `SimplexCategory.toTop_map_toTopInitialVertex_down`: its image under a morphism of simplices.
* `TauCeti.TopCat.simplexMap`: the continuous map underlying a singular simplex, with its
  behaviour under reindexing, pushforward and the lax monoidal structure of `TopCat.toSSet`, and
  the endpoints of the parametrization `SSet.stdSimplex.toSSetObjI` of the unit interval.
* `TauCeti.TopCat.mulActionToSSetObj`: a continuous action on a space acts on its singular
  simplices by translation, freely if it is free on the space
  (`TauCeti.TopCat.isCancelSMul_toSSetObj`).
-/

public section

open CategoryTheory Convexity

open scoped Simplicial

universe u

namespace SimplexCategory

/-- Every topological simplex is contractible, being a universe lift of a standard simplex on a
finite nonempty type. -/
instance contractibleSpace (n : SimplexCategory) : ContractibleSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).contractibleSpace

/-- Every topological simplex is locally path connected, being a universe lift of a standard
simplex on a finite type. -/
instance locallyPathConnectedSpace (n : SimplexCategory) :
    LocallyPathConnectedSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).symm.locallyPathConnectedSpace

/-- The initial vertex of the topological `n`-simplex: the universe lift of the standard-simplex
vertex `StdSimplex.single 0`. -/
noncomputable def toTopInitialVertex (n : SimplexCategory) : toTop.{u}.obj n :=
  ULift.up (StdSimplex.single 0)

/-- The initial vertex of the topological `n`-simplex lifts the standard-simplex vertex
`StdSimplex.single 0`. -/
@[simp]
lemma toTopInitialVertex_down (n : SimplexCategory) :
    (toTopInitialVertex.{u} n).down = StdSimplex.single 0 := (rfl)

/-- A map of topological simplices carries the initial vertex to the vertex indexed by
its value at zero. -/
-- Compute the vertex image before `toTop_map` unfolds the inner map.
@[simp↓]
lemma toTop_map_toTopInitialVertex_down {m n : SimplexCategory} (α : m ⟶ n) :
    (toTop.{u}.map α (toTopInitialVertex m)).down = StdSimplex.single (α.toOrderHom 0) := by
  -- The lifted affine map is read in standard-simplex coordinates.
  rw [toTop_map]
  change StdSimplex.map α.toOrderHom (toTopInitialVertex.{u} m).down = _
  rw [toTopInitialVertex_down, StdSimplex.map_single]

/-- A morphism of simplices fixing `0` fixes the initial vertex of the topological simplex. -/
lemma toTop_map_toTopInitialVertex {m n : SimplexCategory} (α : m ⟶ n)
    (hα : α.toOrderHom 0 = 0) : toTop.{u}.map α (toTopInitialVertex m) = toTopInitialVertex n :=
  ULift.ext (by rw [toTop_map_toTopInitialVertex_down, hα, toTopInitialVertex_down])

/-- A coface map other than the zeroth one fixes `0`. -/
lemma δ_toOrderHom_zero {n : ℕ} {i : Fin (n + 2)} (hi : i ≠ 0) : (δ i).toOrderHom 0 = 0 :=
  Fin.succAbove_ne_zero_zero hi

/-- Every codegeneracy map fixes `0`. -/
lemma σ_toOrderHom_zero {n : ℕ} (i : Fin (n + 1)) : (σ i).toOrderHom 0 = 0 :=
  Fin.predAbove_right_zero (i := i)

/-- The first edge of a topological simplex starts at its initial vertex. -/
lemma toTop_map_mkOfLe_toTopInitialVertex (k : ℕ) :
    toTop.{u}.map (mkOfLe (n := k + 1) 0 1 (by simp)) (toTopInitialVertex ⦋1⦌) =
      toTopInitialVertex ⦋k + 1⦌ :=
  toTop_map_toTopInitialVertex _ rfl

/-- The first edge of a topological simplex ends at vertex `1`, the initial vertex of the zeroth
face. -/
lemma toTop_map_mkOfLe_toTop_map_δ_zero (k : ℕ) :
    toTop.{u}.map (mkOfLe (n := k + 1) 0 1 (by simp))
        (toTop.map (δ 0) (toTopInitialVertex ⦋0⦌)) =
      toTop.map (δ 0) (toTopInitialVertex ⦋k⦌) := by
  refine ULift.ext ?_
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, toTop_map_toTopInitialVertex_down,
    toTop_map_toTopInitialVertex_down]
  rfl

end SimplexCategory

namespace TauCeti.TopCat

variable {X Y : TopCat.{u}} {m n : SimplexCategoryᵒᵖ}

/-- The continuous map underlying a singular simplex, defined on the topological simplex
`SimplexCategory.toTop.obj n.unop` rather than on the unlifted model used by
`TopCat.toSSetObjEquiv`, so that it composes directly with the maps `SimplexCategory.toTop.map`. -/
-- The body must stay exposed: the endpoints of a transport inside a simplex, as they appear in
-- `TauCeti.LocalCoefficientSystem.pathTransport_map` and `map_pathTransport`, agree only
-- definitionally, so without it those statements are not type-correct.
@[expose]
noncomputable def simplexMap (σ : (TopCat.toSSet.obj X).obj n) :
    C(SimplexCategory.toTop.{u}.obj n.unop, X) := σ.down.hom

/-- A singular simplex is determined by its underlying continuous map. -/
lemma simplexMap_injective :
    Function.Injective (simplexMap : (TopCat.toSSet.obj X).obj n → _) := by
  intro σ τ h
  exact ULift.ext (ConcreteCategory.hom_injective h)

/-- Every continuous map on the topological simplex underlies a singular simplex. -/
lemma simplexMap_surjective :
    Function.Surjective (simplexMap : (TopCat.toSSet.obj X).obj n → _) :=
  fun f ↦ ⟨ULift.up (TopCat.ofHom f), rfl⟩

/-- Reindexing a singular simplex precomposes the underlying continuous map with the induced map
of topological simplices. -/
@[simp]
lemma simplexMap_map (α : m ⟶ n) (σ : (TopCat.toSSet.obj X).obj m) :
    simplexMap ((TopCat.toSSet.obj X).map α σ) =
      (simplexMap σ).comp (SimplexCategory.toTop.map α.unop).hom := rfl

/-- Pushing a singular simplex forward along a continuous map postcomposes the underlying
continuous map with that map. -/
@[simp]
lemma simplexMap_app (f : X ⟶ Y) (σ : (TopCat.toSSet.obj X).obj n) :
    simplexMap ((TopCat.toSSet.map f).app n σ) = f.hom.comp (simplexMap σ) := rfl

/-- The singular simplex of a product built from two singular simplices by the lax monoidal
structure of the singular simplicial set functor has these two simplices as components. -/
lemma simplexMap_μ_apply (a : (TopCat.toSSet.obj X).obj n) (b : (TopCat.toSSet.obj Y).obj n)
    (p : SimplexCategory.toTop.{u}.obj n.unop) :
    simplexMap ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n ⟨a, b⟩) p =
      ((simplexMap a p, simplexMap b p) : X × Y) :=
  Prod.ext congr(simplexMap $(congr($(Functor.Monoidal.μ_fst TopCat.toSSet X Y).app n ⟨a, b⟩)) p)
    congr(simplexMap $(congr($(Functor.Monoidal.μ_snd TopCat.toSSet X Y).app n ⟨a, b⟩)) p)

/-- The singular `0`-simplex corresponding to a point is the constant map at that point. -/
@[simp]
lemma simplexMap_toSSetObj₀Equiv_symm_apply (x : X) (p : SimplexCategory.toTop.{u}.obj ⦋0⦌) :
    simplexMap (TopCat.toSSetObj₀Equiv.symm x) p = x := rfl

open Opposite in
/-- The parametrization of the unit interval by the topological `1`-simplex underlying the
nondegenerate `1`-simplex of `Δ[1]` sends the vertex `ε` to the point `ε` of `Δ[1]`. -/
lemma simplexMap_toSSetObjI_objMk₁_toTop_map {ε : Fin 2} (v : ⦋0⦌ ⟶ ⦋1⦌)
    (hv : v.toOrderHom 0 = ε) (p : SimplexCategory.toTop.{u}.obj ⦋0⦌) :
    simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋1⦌) (SSet.stdSimplex.objMk₁ 1))
        (SimplexCategory.toTop.map v p) =
      simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋0⦌) (SSet.stdSimplex.const 1 ε _)) p := by
  have hb : (Δ[1] : SSet.{u}).map v.op (SSet.stdSimplex.objMk₁ (1 : Fin 3)) =
      SSet.stdSimplex.const 1 ε _ := by
    ext k : 1
    fin_cases k
    refine (SSet.stdSimplex.objMk₁_apply.{u} _ _).trans ?_
    dsimp
    simp only [hv]
    fin_cases ε <;> rfl
  rw [← hb, NatTrans.naturality_apply SSet.stdSimplex.toSSetObjI.{u} v.op, simplexMap_map]
  rfl

open Opposite in
/-- The parametrization of the unit interval by the topological `1`-simplex underlying the
nondegenerate `1`-simplex of `Δ[1]` starts at `0`. -/
lemma homeomorph_simplexMap_toSSetObjI_toTopInitialVertex :
    TopCat.I.homeomorph (simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋1⦌)
      (SSet.stdSimplex.objMk₁ 1)) (SimplexCategory.toTopInitialVertex ⦋1⦌)) = 0 := by
  rw [← SimplexCategory.toTop_map_toTopInitialVertex (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) rfl,
    simplexMap_toSSetObjI_objMk₁_toTop_map _ (ε := 0) rfl,
    SSet.stdSimplex.toSSetObj_app_const_zero, simplexMap_toSSetObj₀Equiv_symm_apply,
    TopCat.I.homeomorph_zero]

open Opposite in
/-- The parametrization of the unit interval by the topological `1`-simplex underlying the
nondegenerate `1`-simplex of `Δ[1]` ends at `1`. -/
lemma homeomorph_simplexMap_toSSetObjI_toTop_map_δ_zero :
    TopCat.I.homeomorph (simplexMap (SSet.stdSimplex.toSSetObjI.{u}.app (op ⦋1⦌)
      (SSet.stdSimplex.objMk₁ 1)) (SimplexCategory.toTop.map (SimplexCategory.δ 0)
        (SimplexCategory.toTopInitialVertex ⦋0⦌))) = 1 := by
  rw [simplexMap_toSSetObjI_objMk₁_toTop_map _ (ε := 1) rfl,
    SSet.stdSimplex.toSSetObj_app_const_one, simplexMap_toSSetObj₀Equiv_symm_apply,
    TopCat.I.homeomorph_one]

section Action

variable (E : _root_.TopCat.{u}) (G : Type*) [Monoid G] [MulAction G E] [ContinuousConstSMul G E]

/-- The action of `G` on the singular simplices of a `G`-space `E` by translation, induced from
the functor `SingleObj G ⥤ Type u` they form: `g` pushes a simplex forward along `g • ·`
(`TauCeti.TopCat.toSSetObj_smul_def`). -/
noncomputable instance mulActionToSSetObj (n : SimplexCategoryᵒᵖ) :
    MulAction G ((_root_.TopCat.toSSet.obj E).obj n) :=
  inferInstanceAs (MulAction G
    (((E.actionFunctor G ⋙ _root_.TopCat.toSSet) ⋙ (evaluation _ _).obj n).obj
      (SingleObj.star G)))

variable {E G}

/-- An element `g` acts on a singular simplex by pushing it forward along `g • ·`. -/
lemma toSSetObj_smul_def {n : SimplexCategoryᵒᵖ} (g : G) (σ : (_root_.TopCat.toSSet.obj E).obj n) :
    g • σ = (_root_.TopCat.toSSet.map
      (_root_.TopCat.ofHom ⟨(g • · : E → E), continuous_const_smul g⟩)).app n σ :=
  (rfl)

end Action

section Free

variable {E : _root_.TopCat.{u}} {G : Type*} [Group G] [MulAction G E] [ContinuousConstSMul G E]

/-- **A free action on a space is free on its singular simplices**: two translates of a simplex
that agree also agree at one point of the topological simplex. -/
instance isCancelSMul_toSSetObj [IsCancelSMul G E] (n : SimplexCategoryᵒᵖ) :
    IsCancelSMul G ((_root_.TopCat.toSSet.obj E).obj n) where
  right_cancel' g h σ hσ := by
    have hx := congr(simplexMap $hσ (SimplexCategory.toTopInitialVertex n.unop))
    simp only [toSSetObj_smul_def, simplexMap_app] at hx
    exact IsCancelSMul.right_cancel g h _ hx

end Free

end TauCeti.TopCat

namespace TauCeti

/-- The topological `n`-simplex, the model of the simplicial singular chains in degree `n`. -/
noncomputable abbrev simplexModel (n : ℕ) : TopCat.{u} := SimplexCategory.toTop.{u}.obj ⦋n⦌

/-- The identity singular simplex of the topological simplex. -/
noncomputable def idSimplex (n : ℕ) : (TopCat.toSSet.obj (simplexModel.{u} n)) _⦋n⦌ :=
  ULift.up (𝟙 _)

/-- A singular simplex, as a map from the model simplex.  The type of the underlying map of a
singular simplex is only propositionally the type of maps out of `simplexModel n`; this
declaration fixes the type for use in instance and rewrite problems. -/
abbrev simplexToHom {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    simplexModel.{u} n ⟶ X := σ.down

/-- The identity simplex of the topological simplex is the identity map. -/
@[simp]
theorem simplexMap_idSimplex (n : ℕ) (x : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    TopCat.simplexMap (idSimplex.{u} n) x = x :=
  (rfl)

/-- A singular simplex is the push-forward of the identity simplex along itself. -/
theorem toSSet_map_down_idSimplex {X : TopCat.{u}} {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map σ.down).app _ (idSimplex n) = σ := by
  apply TopCat.simplexMap_injective
  rw [TopCat.simplexMap_app]
  rfl

end TauCeti
