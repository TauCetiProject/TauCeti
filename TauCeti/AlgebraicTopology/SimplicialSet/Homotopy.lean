/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom

/-!
# Homotopies of morphisms of pairs of simplicial sets

A homotopy between morphisms of a pair of simplicial sets consists of a homotopy on the
subcomplexes and a homotopy on the total complexes which agree on the subcomplexes, that is,
`SSetPair.Homotopy`.  This is the simplicial analogue of `TopPair.Homotopy` in
`Mathlib/Topology/Category/TopPair.lean` (J. Scharmberg), with the same two homotopies and the
same whiskered commuting square.

The file also records what such a commuting square gives on the combinatorial homotopies that
`SSet.Homotopy.toSimplicialObjectHomotopy` extracts: the two families of morphisms
`Xₙ ⟶ Y'ₙ₊₁` commute with the morphisms of the square.  That compatibility is what makes the
chain homotopies of the absolute case descend to relative chains.

Finally, it records where the combinatorial homotopy `h` from `f` to `g` starts: the initial vertex
of `h i x` is the image under `f` of the initial vertex of `x`, the first edge of `h (i + 1) x` is
the image under `f` of the first edge of `x`, and the first edge of `h 0 x` is the track `h 0 x₀`
of the initial vertex `x₀` of `x`.  These are what a construction transporting data along the
initial vertices of simplices, such as twisted chains, needs to lift the combinatorial homotopy.

It also provides the constructor `SSet.Homotopy.mk'` of a homotopy from a morphism on the
cylinder `X ⊗ Δ[1]` with prescribed ends, identifies these ends with the faces of
`X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` (`SSet.whiskerLeft_stdSimplex_δ_one`), records that they are disjoint
(`SSet.range_ι₀_inf_range_ι₁`), and names the edge `{v} × Δ[1]` of the cylinder over a vertex `v`
(`SSet.verticalEdge`), along which a homotopy moves the image of `v`; its endpoints are
`(v, 0)` and `(v, 1)` (`SSet.δ_one_verticalEdge` and `SSet.δ_zero_verticalEdge`). Homotopies can
be precomposed and postcomposed with maps (`SSet.Homotopy.precomp`, `SSet.Homotopy.postcomp`),
and they correspond under the tensor-hom adjunction (`SSet.Homotopy.curry`,
`SSet.Homotopy.uncurry`). Through this adjunction, the vertices of the simplicial set
`Fun(X, Z) = (ihom X).obj Z` of maps are the maps `X ⟶ Z` (`SSet.ihomObj₀Equiv`, from
`TauCeti/AlgebraicTopology/SimplicialSet/InternalHom.lean`), and its edges
between two such vertices are the homotopies between them (`SSet.ihomEdgeEquiv`).
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

open scoped Simplicial

universe w

namespace SSet

/-- The face `X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` omitting the vertex `1` is the end `X ⊗ {0}` of the cylinder,
after the projection `X ⊗ Δ[0] ⟶ X`. -/
lemma whiskerLeft_stdSimplex_δ_one (X : SSet.{w}) :
    X ◁ stdSimplex.δ (1 : Fin 2) = fst X Δ[0] ≫ ι₀ := by
  ext : 1 <;> simp [ι₀, stdSimplex.δ_one_eq_const]

/-- The face `X ⊗ Δ[0] ⟶ X ⊗ Δ[1]` omitting the vertex `0` is the end `X ⊗ {1}` of the cylinder,
after the projection `X ⊗ Δ[0] ⟶ X`. -/
lemma whiskerLeft_stdSimplex_δ_zero (X : SSet.{w}) :
    X ◁ stdSimplex.δ (0 : Fin 2) = fst X Δ[0] ≫ ι₁ := by
  ext : 1 <;> simp [ι₁, stdSimplex.δ_zero_eq_const]

/-- The associator identifies the cylinder `A ⊗ (X ⊗ Δ[1])` with `(A ⊗ X) ⊗ Δ[1]`, carrying the
inclusion of `A ⊗ (X ⊗ {0})` to that of `(A ⊗ X) ⊗ {0}`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ι₀_associator_inv (A X : SSet.{w}) :
    A ◁ ι₀ ≫ (α_ A X Δ[1]).inv = ι₀ := by
  ext : 1 <;> [ext : 1; skip] <;> simp [ι₀]

/-- The associator identifies the cylinder `A ⊗ (X ⊗ Δ[1])` with `(A ⊗ X) ⊗ Δ[1]`, carrying the
inclusion of `A ⊗ (X ⊗ {1})` to that of `(A ⊗ X) ⊗ {1}`. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ι₁_associator_inv (A X : SSet.{w}) :
    A ◁ ι₁ ≫ (α_ A X Δ[1]).inv = ι₁ := by
  ext : 1 <;> [ext : 1; skip] <;> simp [ι₁]

/-- The two ends `X ⊗ {0}` and `X ⊗ {1}` of the cylinder `X ⊗ Δ[1]` are disjoint. -/
lemma range_ι₀_inf_range_ι₁ {X : SSet.{w}} :
    Subcomplex.range (ι₀ : X ⟶ X ⊗ Δ[1]) ⊓ Subcomplex.range ι₁ = ⊥ := by
  ext ⟨n⟩ z
  induction n using SimplexCategory.rec with | _ n
  simp only [Subfunctor.min_obj, Set.mem_inter_iff, Subfunctor.range_obj, Set.mem_range,
    Subfunctor.bot_obj, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨x, rfl⟩ ⟨y, h⟩
  have := congrArg (fun z : (X ⊗ Δ[1] : SSet.{w}) _⦋n⦌ ↦ z.2 0) h
  simp at this

end SSet

namespace SSet.Homotopy

variable {X Y X' Y' : SSet.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} {u : X ⟶ X'} {v : Y ⟶ Y'}

/-- The simplicial homotopy from `f` to `g` given by a morphism `h : X ⊗ Δ[1] ⟶ Y` which is `f`
on `X ⊗ {0}` and `g` on `X ⊗ {1}`. -/
@[simps h]
def mk' (h : X ⊗ Δ[1] ⟶ Y) (h₀ : ι₀ ≫ h = f) (h₁ : ι₁ ≫ h = g) : SSet.Homotopy f g where
  h := h
  h₀ := h₀
  h₁ := h₁
  rel := by
    ext _ ⟨⟨_, hx⟩, _⟩
    simp at hx

/-- Precomposing a homotopy from `f` to `g` with `e : W ⟶ X` gives a homotopy from `e ≫ f` to
`e ≫ g`. This is the absolute case of `SSet.RelativeMorphism.Homotopy.precomp`. -/
@[no_expose]
noncomputable def precomp {W : SSet.{w}} (H : SSet.Homotopy f g) (e : W ⟶ X) :
    SSet.Homotopy (e ≫ f) (e ≫ g) :=
  RelativeMorphism.Homotopy.precomp H (RelativeMorphism.botEquiv.symm e)
    (Subcomplex.isInitialBot.hom_ext _ _)

/-- The precomposite of a homotopy `H` with `e` is `e ▷ Δ[1] ≫ H.h`. -/
@[simp]
lemma precomp_h {W : SSet.{w}} (H : SSet.Homotopy f g) (e : W ⟶ X) :
    (H.precomp e).h = e ▷ Δ[1] ≫ H.h :=
  (rfl)

/-- Postcomposing a homotopy from `f` to `g` with `e : Y ⟶ Z` gives a homotopy from `f ≫ e` to
`g ≫ e`. This is the absolute case of `SSet.RelativeMorphism.Homotopy.postcomp`. -/
@[no_expose]
noncomputable def postcomp {Z : SSet.{w}} (H : SSet.Homotopy f g) (e : Y ⟶ Z) :
    SSet.Homotopy (f ≫ e) (g ≫ e) :=
  RelativeMorphism.Homotopy.postcomp H (RelativeMorphism.botEquiv.symm e)
    (Subcomplex.isInitialBot.hom_ext _ _)

/-- The postcomposite of a homotopy `H` with `e` is `H.h ≫ e`. -/
@[simp]
lemma postcomp_h {Z : SSet.{w}} (H : SSet.Homotopy f g) (e : Y ⟶ Z) :
    (H.postcomp e).h = H.h ≫ e :=
  (rfl)

/-- A homotopy between maps `A ⊗ X ⟶ Y` curries to a homotopy between the adjoint maps
`X ⟶ Fun(A, Y)`. -/
@[no_expose]
noncomputable def curry {A : SSet.{w}} {f g : A ⊗ X ⟶ Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (MonoidalClosed.curry f) (MonoidalClosed.curry g) :=
  mk' (MonoidalClosed.curry ((α_ A X Δ[1]).inv ≫ H.h))
    (by rw [← MonoidalClosed.curry_natural_left, whiskerLeft_ι₀_associator_inv_assoc, H.h₀])
    (by rw [← MonoidalClosed.curry_natural_left, whiskerLeft_ι₁_associator_inv_assoc, H.h₁])

/-- The curried homotopy is the curried map on the reassociated cylinder. -/
@[simp]
lemma curry_h {A : SSet.{w}} {f g : A ⊗ X ⟶ Y} (H : SSet.Homotopy f g) :
    H.curry.h = MonoidalClosed.curry ((α_ A X Δ[1]).inv ≫ H.h) :=
  (rfl)

/-- A homotopy between maps `X ⟶ Fun(A, Y)` uncurries to a homotopy between the adjoint maps
`A ⊗ X ⟶ Y`. -/
@[no_expose]
noncomputable def uncurry {A : SSet.{w}} {f g : X ⟶ (ihom A).obj Y} (H : SSet.Homotopy f g) :
    SSet.Homotopy (MonoidalClosed.uncurry f) (MonoidalClosed.uncurry g) :=
  mk' ((α_ A X Δ[1]).hom ≫ MonoidalClosed.uncurry H.h)
    (by rw [← whiskerLeft_ι₀_associator_inv, Category.assoc, Iso.inv_hom_id_assoc,
      ← MonoidalClosed.uncurry_natural_left, H.h₀])
    (by rw [← whiskerLeft_ι₁_associator_inv, Category.assoc, Iso.inv_hom_id_assoc,
      ← MonoidalClosed.uncurry_natural_left, H.h₁])

/-- The uncurried homotopy is the reassociated uncurried map. -/
@[simp]
lemma uncurry_h {A : SSet.{w}} {f g : X ⟶ (ihom A).obj Y} (H : SSet.Homotopy f g) :
    H.uncurry.h = (α_ A X Δ[1]).hom ≫ MonoidalClosed.uncurry H.h :=
  (rfl)

/-- The combinatorial homotopy extracted from a simplicial homotopy sends an `n`-simplex `x` to
the value of the homotopy at the pair formed by the `i`-th degeneracy of `x` and the `n + 1`-simplex
of `Δ[1]` taking the value `0` exactly `i + 1` times. -/
lemma toSimplicialObjectHomotopy_h_apply (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    H.toSimplicialObjectHomotopy.h i x =
      H.h.app (op ⦋n + 1⦌) ⟨X.map (SimplexCategory.σ i).op x,
        stdSimplex.objMk₁ i.succ.castSucc⟩ := rfl

/-- Simplicial homotopies which fit into a commutative square induce compatible families of
morphisms `Xₙ ⟶ Y'ₙ₊₁`. -/
lemma toSimplicialObjectHomotopy_h_comm (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (hu : u ▷ Δ[1] ≫ H'.h = H.h ≫ v) (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H'.toSimplicialObjectHomotopy.h i =
      H.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) := by
  ext x
  simp only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
    toSimplicialObjectHomotopy_h_apply, ← NatTrans.naturality_apply u]
  exact congr(($hu).app _ ⟨X.map (SimplexCategory.σ i).op x, stdSimplex.objMk₁ i.succ.castSucc⟩)

/-- The value of the homotopy at a pair whose second component is constant at `0` after
reindexing is the value of `f`. -/
private lemma map_h_app_eq_app (H : SSet.Homotopy f g) {m : SimplexCategoryᵒᵖ} {n : ℕ}
    (φ : m ⟶ op ⦋n⦌) (x : X.obj m) (b : (Δ[1] : SSet.{w}).obj m) (y : X _⦋n⦌)
    (hx : X.map φ x = y) (hb : (Δ[1] : SSet.{w}).map φ b = (ι₀.app _ y).2) :
    Y.map φ (H.h.app m ⟨x, b⟩) = f.app _ y := by
  have e : ((X ⊗ Δ[1]).map φ ⟨x, b⟩ : X _⦋n⦌ × (Δ[1] : SSet.{w}) _⦋n⦌) = ι₀.app _ y :=
    Prod.ext hx hb
  exact (NatTrans.naturality_apply H.h φ _).symm.trans
    ((congrArg (H.h.app _) e).trans congr($(H.h₀).app _ y))

/-- The combinatorial homotopy starts at `f`: the initial vertex of `h i x` is the image under `f`
of the initial vertex of `x`. -/
lemma map_const_toSimplicialObjectHomotopy_h (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    Y.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (H.toSimplicialObjectHomotopy.h i x) =
      f.app _ (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply]
  refine map_h_app_eq_app H _ _ _ _ ?_ ?_
  · rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp]
    rfl
  · ext k : 1
    exact stdSimplex.objMk₁_of_castSucc_lt.{w} i.succ.castSucc (0 : Fin (n + 2)) (by simp)

/-- For `i ≥ 1`, the first edge of `h i x` is the image under `f` of the first edge of `x`. -/
lemma map_mkOfLe_toSimplicialObjectHomotopy_h_succ (H : SSet.Homotopy f g) {n : ℕ}
    (j : Fin (n + 1)) (x : X _⦋n + 1⦌) :
    Y.map (SimplexCategory.mkOfLe 0 1 (by simp)).op (H.toSimplicialObjectHomotopy.h j.succ x) =
      f.app _ (X.map (SimplexCategory.mkOfLe 0 1 (by simp)).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply]
  refine map_h_app_eq_app H _ _ _ _ ?_ ?_
  · rw [← Functor.map_comp_apply, ← op_comp]
    refine congrArg (fun φ : ⦋1⦌ ⟶ _ ↦ X.map φ.op x)
      (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k ↦ ?_)))
    fin_cases k <;> rfl
  · ext k : 1
    fin_cases k
    · exact stdSimplex.objMk₁_of_castSucc_lt.{w} j.succ.succ.castSucc 0 (by simp)
    · exact stdSimplex.objMk₁_of_castSucc_lt.{w} j.succ.succ.castSucc 1 (by
        rw [Fin.lt_def]; simp)

/-- The first edge of `h 0 x` is the track of the homotopy at the initial vertex of `x`. -/
lemma map_mkOfLe_toSimplicialObjectHomotopy_h_zero (H : SSet.Homotopy f g) {n : ℕ}
    (x : X _⦋n⦌) :
    Y.map (SimplexCategory.mkOfLe 0 1 (by simp)).op (H.toSimplicialObjectHomotopy.h 0 x) =
      H.toSimplicialObjectHomotopy.h 0 (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply, toSimplicialObjectHomotopy_h_apply]
  refine (NatTrans.naturality_apply H.h _ _).symm.trans (congrArg (H.h.app _) ?_)
  refine Prod.ext (α := X _⦋1⦌) (β := (Δ[1] : SSet.{w}) _⦋1⦌) ?_ ?_
  · -- The first components of the two pairs, both iterated reindexings of `x`.
    refine (prod_map_fst X Δ[1] _ _).trans ?_
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    refine congrArg (fun φ : ⦋1⦌ ⟶ _ ↦ X.map φ.op x)
      (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k ↦ ?_)))
    fin_cases k <;> rfl
  · ext k : 1
    fin_cases k <;> rfl

end SSet.Homotopy

namespace SSet

section MappingSpace

open MonoidalClosed

variable {X Z : SSet.{w}} (f g : X ⟶ Z)

/-- The edges of `Fun(X, Z)` between the vertices corresponding to maps `f` and `g` are the
simplicial homotopies from `f` to `g`, through the tensor-hom adjunction. -/
@[no_expose]
noncomputable def ihomEdgeEquiv :
    Edge ((ihomObj₀Equiv X Z).symm f) ((ihomObj₀Equiv X Z).symm g) ≃ Homotopy f g where
  toFun e := Homotopy.mk' (uncurry (yonedaEquiv.symm e.edge))
    (by
      have h := whiskerLeft_δ_uncurry_yonedaEquiv_symm e.edge 1
      rw [e.src_eq, Equiv.apply_symm_apply, whiskerLeft_stdSimplex_δ_one, Category.assoc] at h
      simpa using lift (𝟙 X) (stdSimplex.isTerminalObj₀.from X) ≫= h)
    (by
      have h := whiskerLeft_δ_uncurry_yonedaEquiv_symm e.edge 0
      rw [e.tgt_eq, Equiv.apply_symm_apply, whiskerLeft_stdSimplex_δ_zero, Category.assoc] at h
      simpa using lift (𝟙 X) (stdSimplex.isTerminalObj₀.from X) ≫= h)
  invFun H := Edge.mk (yonedaEquiv (curry H.h))
    (by
      apply yonedaEquiv.symm.injective
      rw [yonedaEquiv_symm_δ_yonedaEquiv_curry, whiskerLeft_stdSimplex_δ_one, Category.assoc,
        H.h₀, yonedaEquiv_symm_ihomObj₀Equiv_symm])
    (by
      apply yonedaEquiv.symm.injective
      rw [yonedaEquiv_symm_δ_yonedaEquiv_curry, whiskerLeft_stdSimplex_δ_zero, Category.assoc,
        H.h₁, yonedaEquiv_symm_ihomObj₀Equiv_symm])
  left_inv e := by
    ext
    simp
  right_inv H := by
    apply RelativeMorphism.Homotopy.ext
    simp

/-- The homotopy defined by an edge of `Fun(X, Z)` is its uncurried `1`-simplex. -/
@[simp]
lemma ihomEdgeEquiv_apply_h
    (e : Edge ((ihomObj₀Equiv X Z).symm f) ((ihomObj₀Equiv X Z).symm g)) :
    (ihomEdgeEquiv f g e).h = uncurry (yonedaEquiv.symm e.edge) :=
  (rfl)

/-- The edge defined by a homotopy is its curried form. -/
@[simp]
lemma ihomEdgeEquiv_symm_apply_edge (H : Homotopy f g) :
    ((ihomEdgeEquiv f g).symm H).edge = yonedaEquiv (curry H.h) :=
  (rfl)

end MappingSpace

end SSet

namespace SSetPair

/-- A homotopy between morphisms of pairs of simplicial sets consists of a homotopy on the
subcomplexes and a homotopy on the total complexes which agree on the subcomplexes. -/
@[ext]
structure Homotopy {P P' : SSetPair.{w}} (f g : P ⟶ P') where
  /-- The homotopy on the subcomplexes. -/
  left : SSet.Homotopy f.left g.left
  /-- The homotopy on the total complexes. -/
  right : SSet.Homotopy f.right g.right
  /-- The two homotopies agree on the subcomplexes. -/
  w : P.hom ▷ Δ[1] ≫ right.h = left.h ≫ P'.hom

end SSetPair

end

public section

open CategoryTheory MonoidalCategory

open scoped Simplicial

namespace SSet

variable {X : SSet.{w}}

/-- The edge `{v} × Δ[1]` of the cylinder `X ⊗ Δ[1]` over a vertex `v` of `X`, from `(v, 0)` to
`(v, 1)`. -/
noncomputable def verticalEdge (v : X _⦋0⦌) : (X ⊗ Δ[1] : SSet.{w}) _⦋1⦌ :=
  (X.σ 0 v, stdSimplex.edge 1 0 1 (by decide))

/-- The component of `verticalEdge v` in `X` is the degenerate edge at `v`. -/
lemma verticalEdge_fst (v : X _⦋0⦌) : (verticalEdge v).1 = X.σ 0 v := (rfl)

/-- The component of `verticalEdge v` in `Δ[1]` is the edge from `0` to `1`. -/
lemma verticalEdge_snd (v : X _⦋0⦌) :
    (verticalEdge v).2 = stdSimplex.edge 1 0 1 (by decide) := (rfl)

/-- The vertical edge over `v` starts at `(v, 0)`. -/
lemma δ_one_verticalEdge (v : X _⦋0⦌) : (X ⊗ Δ[1]).δ 1 (verticalEdge v) = ι₀.app _ v :=
  Prod.ext (δ_comp_σ_succ_apply 0 v) (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)

/-- The vertical edge over `v` ends at `(v, 1)`. -/
lemma δ_zero_verticalEdge (v : X _⦋0⦌) : (X ⊗ Δ[1]).δ 0 (verticalEdge v) = ι₁.app _ v :=
  Prod.ext (δ_comp_σ_self_apply 0 v) (stdSimplex.ext _ _ fun i ↦ by fin_cases i; rfl)

end SSet
