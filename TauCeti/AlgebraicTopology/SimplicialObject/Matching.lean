/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Matching maps of simplicial objects

For a simplicial object `X` in a category `C` and `n : ℕ`, the *matching map* in degree `n + 1` is
the component at `⦋n + 1⦌` of the unit `X ⟶ (cosk n).obj X` of the adjunction between
`n`-truncation and the `n`-coskeleton (`CategoryTheory.SimplicialObject.coskAdj`). Its target, the
*matching object*, is the limit of the `X _⦋k⦌` over all simplices `⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n`,
that is, over the boundary of the standard `(n + 1)`-simplex. The matching map sends an
`(n + 1)`-simplex to the family of its faces.

When the right Kan extensions defining the coskeleton are pointwise, this limit is realized by
the cone `CategoryTheory.SimplicialObject.matchingCone`, and the matching map is characterized by
its composites with the projections of that cone (`matchingMap_π` and `cosk_obj_hom_ext`).
Surjectivity conditions on matching maps define hypercovers.

In degree `1` the boundary of `⦋1⦌` is two points, so the matching object is
`X _⦋0⦌ ⨯ X _⦋0⦌` (`CategoryTheory.SimplicialObject.matchingObjectZeroIso`). The matching map
becomes the pair of vertex maps `(δ 1, δ 0)` (`matchingMap_zero_comp_matchingObjectZeroIso_hom`).

## Main declarations

* `CategoryTheory.SimplicialObject.matchingMap`: the matching map
  `X _⦋n + 1⦌ ⟶ ((cosk n).obj X) _⦋n + 1⦌`.
* `CategoryTheory.SimplicialObject.matchingCone`: the cone over the faces of dimension at most `n`
  of `⦋n + 1⦌` with vertex the matching object.
* `CategoryTheory.SimplicialObject.isLimitMatchingCone`: it is a limit cone.
* `CategoryTheory.SimplicialObject.matchingObjectZeroIso`: the matching object in degree `1` is
  `X _⦋0⦌ ⨯ X _⦋0⦌`.
* `CategoryTheory.SimplicialObject.epi_matchingMap_zero_iff`: the matching map in degree `1` is an
  epimorphism if and only if `(δ 1, δ 0) : X _⦋1⦌ ⟶ X _⦋0⦌ ⨯ X _⦋0⦌` is.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section VII.1, for matching objects and coskeleta.
-/

public section

open CategoryTheory Limits Opposite Functor SimplexCategory.Truncated

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] (n : ℕ)

section

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/-- The `n`-coskeleton of a truncated simplicial object, with the counit of the adjunction
`truncation n ⊣ Truncated.cosk n`, is a right Kan extension. This only uses the existence of the
right Kan extensions, and not of left Kan extensions. -/
instance Truncated.cosk_obj_isRightKanExtension (T : Truncated C n) :
    ((Truncated.cosk n).obj T).IsRightKanExtension ((coskAdj n).counit.app T) := by
  dsimp [coskAdj]
  rw [ranAdjunction_counit]
  infer_instance

variable (X : SimplicialObject C)

/-- The matching map of `X` in degree `n + 1`, from `X _⦋n + 1⦌` to the matching object
`((cosk n).obj X) _⦋n + 1⦌`. It sends a simplex to the family of its faces of dimension at
most `n`. -/
noncomputable def matchingMap : X _⦋n + 1⦌ ⟶ ((cosk n).obj X) _⦋n + 1⦌ :=
  ((coskAdj n).unit.app X).app (op ⦋n + 1⦌)

/-- The cone over the simplices `⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n` whose vertex is the matching object
`((cosk n).obj X) _⦋n + 1⦌`. It is a limit cone when the right Kan extensions defining the
coskeleton are pointwise (`isLimitMatchingCone`). -/
noncomputable abbrev matchingCone :
    Cone (StructuredArrow.proj (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op ⋙
      (truncation n).obj X) :=
  (RightExtension.mk _ ((coskAdj n).counit.app ((truncation n).obj X))).coneAt (op ⦋n + 1⦌)

/-- The projection of the matching map to the face `f` of `⦋n + 1⦌` is the action of `f`. -/
@[reassoc]
theorem matchingMap_π
    (f : StructuredArrow (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op) :
    X.matchingMap n ≫ (X.matchingCone n).π.app f = X.map f.hom := by
  have h := congr_app ((coskAdj (C := C) n).left_triangle_components X) f.right
  have h' := ((coskAdj (C := C) n).unit.app X).naturality f.hom
  dsimp [matchingMap] at h h' ⊢
  rw [← Category.assoc, ← h', Category.assoc]
  -- `h` is the triangle identity, stated with the component of the unit at the truncated object.
  exact (congrArg (X.map f.hom ≫ ·) h).trans (Category.comp_id _)

end

section

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
  (X : SimplicialObject C)

/-- When the right Kan extensions defining the `n`-coskeleton are pointwise, the matching object
is the limit of the `X _⦋k⦌` over the simplices `⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n`. -/
noncomputable def isLimitMatchingCone : IsLimit (X.matchingCone n) :=
  isPointwiseRightKanExtensionOfIsRightKanExtension _ _ (op ⦋n + 1⦌)

variable {X n} in
/-- Two morphisms into the matching object agree if their projections to every simplex
`⦋k⦌ ⟶ ⦋n + 1⦌` with `k ≤ n` agree. -/
theorem cosk_obj_hom_ext {Z : C} {g h : Z ⟶ ((cosk n).obj X) _⦋n + 1⦌}
    (w : ∀ f, g ≫ (X.matchingCone n).π.app f = h ≫ (X.matchingCone n).π.app f) : g = h :=
  (X.isLimitMatchingCone n).hom_ext w

end

section

variable (X : SimplicialObject C) [HasBinaryProduct (X _⦋0⦌) (X _⦋0⦌)]

/-- The vertex `i` of `⦋1⦌`, as an object of the indexing category of the matching cone in
degree `1`. -/
private abbrev vertex (i : Fin 2) :
    StructuredArrow (op ⦋1⦌) (SimplexCategory.Truncated.inclusion 0).op :=
  .mk (Y := op ⦋0⦌₀) (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op

/-- A face `⦋k⦌ ⟶ ⦋1⦌` with `k ≤ 0` takes the same value on every vertex of `⦋k⦌`. -/
private theorem toOrderHom_hom_unop_eq
    (f : StructuredArrow (op ⦋1⦌) (SimplexCategory.Truncated.inclusion 0).op)
    (x : Fin (f.right.unop.obj.len + 1)) :
    f.hom.unop.toOrderHom x = f.hom.unop.toOrderHom 0 := by
  have hf := f.right.unop.property
  obtain rfl : x = 0 := by
    ext
    have hx := x.isLt
    simp at hf hx ⊢
    omega
  rfl

/-- The cone over the faces of dimension `0` of `⦋1⦌` with vertex `X _⦋0⦌ ⨯ X _⦋0⦌`: the face at
the vertex `0` is the first projection and the face at the vertex `1` the second. -/
private noncomputable abbrev prodCone :
    Cone (StructuredArrow.proj (op ⦋1⦌) (SimplexCategory.Truncated.inclusion 0).op ⋙
      (truncation 0).obj X) where
  pt := X _⦋0⦌ ⨯ X _⦋0⦌
  π :=
    { app f := (if f.hom.unop.toOrderHom 0 = 0 then prod.fst else prod.snd) ≫
        X.map (SimplexCategory.const _ ⦋0⦌ 0).op
      naturality f f' φ := by
        have h : f'.hom.unop.toOrderHom 0 = f.hom.unop.toOrderHom 0 := by
          rw [← StructuredArrow.w φ]
          simp only [unop_comp, SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
            Function.comp_apply]
          exact toOrderHom_hom_unop_eq f _
        dsimp [truncation]
        rw [h, Category.id_comp, Category.assoc, ← X.map_comp]
        -- Both sides act by morphisms `(unop f'.right).obj ⟶ ⦋0⦌`, which are unique.
        congr 2 }

private theorem prodCone_π_app_vertex_zero :
    (prodCone X).π.app (vertex 0) = prod.fst := by
  simp [prodCone, (SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm]

private theorem prodCone_π_app_vertex_one :
    (prodCone X).π.app (vertex 1) = prod.snd := by
  simp [prodCone, (SimplexCategory.eq_const_to_zero (𝟙 ⦋0⦌)).symm]

/-- The morphism from the vertex `f.hom.unop.toOrderHom 0` to a face `f` of dimension `0`. -/
private def toFace (f : StructuredArrow (op ⦋1⦌) (SimplexCategory.Truncated.inclusion 0).op) :
    vertex (f.hom.unop.toOrderHom 0) ⟶ f :=
  StructuredArrow.homMk (.op (SimplexCategory.Truncated.Hom.tr
    (SimplexCategory.const _ ⦋0⦌ 0) f.right.unop.property (by simp))) (by
      apply Quiver.Hom.unop_inj
      ext x : 3
      exact (toOrderHom_hom_unop_eq f x).symm)

/-- The cone `prodCone X` is a limit cone. -/
private noncomputable def isLimitProdCone : IsLimit (prodCone X) where
  lift s := prod.lift (s.π.app (vertex 0)) (s.π.app (vertex 1))
  fac s f := by
    rw [← s.w (toFace f), ← (prodCone X).w (toFace f), ← Category.assoc]
    congr 1
    generalize f.hom.unop.toOrderHom 0 = i
    fin_cases i <;> simp
  uniq s m hm := by
    apply prod.hom_ext
    · rw [prod.lift_fst, ← hm (vertex 0), prodCone_π_app_vertex_zero]
    · rw [prod.lift_snd, ← hm (vertex 1), prodCone_π_app_vertex_one]

variable [∀ (F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion 0).op.HasPointwiseRightKanExtension F]

/-- The matching object of `X` in degree `1` is `X _⦋0⦌ ⨯ X _⦋0⦌`: the boundary of `⦋1⦌` consists
of its two vertices. -/
noncomputable def matchingObjectZeroIso : ((cosk 0).obj X) _⦋1⦌ ≅ X _⦋0⦌ ⨯ X _⦋0⦌ :=
  (X.isLimitMatchingCone 0).conePointUniqueUpToIso (isLimitProdCone X)

/-- The first projection of `matchingObjectZeroIso` is the face at the vertex `0` of `⦋1⦌`. -/
@[reassoc (attr := simp)]
theorem matchingObjectZeroIso_hom_fst :
    X.matchingObjectZeroIso.hom ≫ prod.fst = (X.matchingCone 0).π.app
      (.mk (Y := op ⦋0⦌₀) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op) := by
  rw [← prodCone_π_app_vertex_zero]
  exact (X.isLimitMatchingCone 0).conePointUniqueUpToIso_hom_comp (isLimitProdCone X) _

/-- The second projection of `matchingObjectZeroIso` is the face at the vertex `1` of `⦋1⦌`. -/
@[reassoc (attr := simp)]
theorem matchingObjectZeroIso_hom_snd :
    X.matchingObjectZeroIso.hom ≫ prod.snd = (X.matchingCone 0).π.app
      (.mk (Y := op ⦋0⦌₀) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op) := by
  rw [← prodCone_π_app_vertex_one]
  exact (X.isLimitMatchingCone 0).conePointUniqueUpToIso_hom_comp (isLimitProdCone X) _

/-- Under `matchingObjectZeroIso`, the matching map in degree `1` sends an edge to its pair of
vertices `(δ 1, δ 0)`. -/
@[reassoc (attr := simp)]
theorem matchingMap_zero_comp_matchingObjectZeroIso_hom :
    X.matchingMap 0 ≫ X.matchingObjectZeroIso.hom = prod.lift (X.δ (n := 0) 1) (X.δ 0) := by
  apply prod.hom_ext
  · rw [Category.assoc, matchingObjectZeroIso_hom_fst, matchingMap_π]
    simp [δ, SimplexCategory.δ_one_eq_const]
  · rw [Category.assoc, matchingObjectZeroIso_hom_snd, matchingMap_π]
    simp [δ, SimplexCategory.δ_zero_eq_const]

/-- The matching map of `X` in degree `1` is an epimorphism if and only if the pair of vertex maps
`(δ 1, δ 0) : X _⦋1⦌ ⟶ X _⦋0⦌ ⨯ X _⦋0⦌` is. -/
theorem epi_matchingMap_zero_iff :
    Epi (X.matchingMap 0) ↔ Epi (prod.lift (X.δ (n := 0) 1) (X.δ 0)) := by
  rw [← matchingMap_zero_comp_matchingObjectZeroIso_hom]
  exact (epi_comp_iff_of_isIso _ _).symm

end

end CategoryTheory.SimplicialObject
