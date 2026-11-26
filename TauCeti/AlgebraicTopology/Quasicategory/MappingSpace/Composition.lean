/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration
public import TauCeti.CategoryTheory.Monoidal.Closed.Swap
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# Composition of mapping spaces

For vertices `x`, `y` and `z` of a simplicial set `X`, the *triangle space*
`SSet.triangleSpace X x y z` is the simplicial set of `2`-simplices of `X` with vertices `x`, `y`
and `z`: the subcomplex of `Fun(Δ[2], X)` of the families of `2`-simplices whose edge `0 ⟶ 1`
lies in the mapping space `Hom_X(x, y)` and whose edge `1 ⟶ 2` lies in `Hom_X(y, z)`. Restricting
to the three edges gives maps to `Hom_X(x, y)`, `Hom_X(y, z)` and `Hom_X(x, z)`, and the first two
together form the restriction to the spine,
`SSet.triangleSpace.spine x y z : Hom_X(x, y, z) ⟶ Hom_X(x, y) ⊗ Hom_X(y, z)`.

When `X` is a quasicategory, the restriction to the spine is a trivial fibration
(`SSet.triangleSpace.rlp_monomorphisms_spine`). A family of spines parametrized by `B`, with a
filling given over a simplicial subset of `B`, is a horn `Λ[2, 1]` of the functor quasicategory
`Fun(B, X)` over a triangle of `Fun(A, X)`, through the exchange of exponent and source
`CategoryTheory.MonoidalClosed.ihomSwapEquiv`; it is filled because restriction
`Fun(B, X) ⟶ Fun(A, X)` along a monomorphism is an inner fibration. A section of the spine
followed by the long edge is the **composition of mapping spaces**
`SSet.mappingSpace.comp x y z : Hom_X(x, y) ⊗ Hom_X(y, z) ⟶ Hom_X(x, z)`. It is unique up to
homotopy, it sends two edges to a composite of them, and it is unital and associative up to
homotopy. Associativity comes from filling horns `Λ[3, 2]` in `Fun(Z, X)`, which is again a
parametrized statement about `X` (`SSet.triangleSpace.exists_triangle_of_horn₃₂`).

## Main definitions

* `SSet.triangleSpace X x y z`: the triangles of `X` with vertices `x`, `y` and `z`.
* `SSet.triangleSpace.edge₀₁`, `SSet.triangleSpace.edge₁₂`, `SSet.triangleSpace.edge₀₂`: the
  restrictions to the three edges, and `SSet.triangleSpace.spine` the restriction to the spine.
* `SSet.mappingSpace.comp x y z`: for a quasicategory, the composition of mapping spaces.

## Main results

* `SSet.triangleSpace.rlp_monomorphisms_spine`: for a quasicategory, the restriction to the spine
  is a trivial fibration.
* `SSet.triangleSpace.exists_homotopy_edge₀₂`: two families of triangles with the same spines have
  homotopic long edges.
* `SSet.mappingSpace.exists_homotopy_comp`: every section of the spine followed by the long edge
  is homotopic to the composition.
* `SSet.mappingSpace.comp_compStruct`: the composition sends two edges to a composite of them.
* `SSet.mappingSpace.exists_homotopy_id_comp`, `SSet.mappingSpace.exists_homotopy_comp_id`: the
  composition is unital up to homotopy.
* `SSet.mappingSpace.exists_homotopy_comp_assoc`: the composition is associative up to homotopy.

## References

* J. Lurie, *Higher Topos Theory*, Corollary 2.3.2.5 (restriction to the spine of `Δ[2]` is a
  trivial fibration exactly for quasicategories).
* J. Lurie, *Kerodon*, §4.6.9 (composition of morphisms).

The construction follows the existing postcomposition of right mapping spaces in
`TauCeti.AlgebraicTopology.Quasicategory.Postcomposition`: `SSet.mappingSpace.comp` is built
like `SSet.rightMappingSpace.postcomp`, as a chosen section of a trivial fibration followed by
an edge restriction, and its independence of the section (`SSet.mappingSpace.exists_homotopy_comp`)
is proved like `SSet.rightMappingSpace.exists_homotopy_postcomp`, by applying
`SSet.exists_homotopy_of_rlp_monomorphisms` to the trivial fibration
(`SSet.triangleSpace.exists_homotopy_edge₀₂`).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory Limits Opposite
  Simplicial

universe u

namespace SSet

variable (X : SSet.{u})

/-- The *triangle space* `Hom_X(x, y, z)` of vertices `x`, `y` and `z` of a simplicial set `X`:
the subcomplex of `Fun(Δ[2], X)` of the `2`-simplices whose edge `0 ⟶ 1` lies in the mapping space
`Hom_X(x, y)` and whose edge `1 ⟶ 2` lies in `Hom_X(y, z)`. Its `n`-simplices are the maps
`Δ[2] ⊗ Δ[n] ⟶ X` which are constant at `x`, `y` and `z` on the three vertices of `Δ[2]`, and its
long edge `0 ⟶ 2` lies in `Hom_X(x, z)` (`SSet.range_comp_pre_δ_one_le_mappingSpace`). -/
noncomputable def triangleSpace (x y z : X _⦋0⦌) : ((ihom Δ[2]).obj X).Subcomplex :=
  (X.mappingSpace x y).preimage ((pre (stdSimplex.δ 2)).app X) ⊓
    (X.mappingSpace y z).preimage ((pre (stdSimplex.δ 0)).app X)

variable {X} {x y z : X _⦋0⦌}

/-- **The universal property of `Hom_X(x, y, z)`**: a family `g` of `2`-simplices of `X` lies in
the triangle space exactly when its edges `0 ⟶ 1` lie in `Hom_X(x, y)` and its edges `1 ⟶ 2` lie in
`Hom_X(y, z)`. -/
lemma range_le_triangleSpace_iff {Z : SSet.{u}} (g : Z ⟶ (ihom Δ[2]).obj X) :
    Subcomplex.range g ≤ X.triangleSpace x y z ↔
      Subcomplex.range (g ≫ (pre (stdSimplex.δ 2)).app X) ≤ X.mappingSpace x y ∧
        Subcomplex.range (g ≫ (pre (stdSimplex.δ 0)).app X) ≤ X.mappingSpace y z := by
  rw [triangleSpace, le_inf_iff, Subcomplex.range_comp, Subcomplex.range_comp,
    Subcomplex.image_le_iff, Subcomplex.image_le_iff]

/-- An `n`-simplex of `Fun(Δ[2], X)` lies in `Hom_X(x, y, z)` exactly when its edge `0 ⟶ 1` lies
in `Hom_X(x, y)` and its edge `1 ⟶ 2` lies in `Hom_X(y, z)`. -/
lemma mem_triangleSpace_iff {n : ℕ} (σ : ((ihom Δ[2]).obj X) _⦋n⦌) :
    σ ∈ (X.triangleSpace x y z).obj _ ↔
      ((pre (stdSimplex.δ 2)).app X).app _ σ ∈ (X.mappingSpace x y).obj _ ∧
        ((pre (stdSimplex.δ 0)).app X).app _ σ ∈ (X.mappingSpace y z).obj _ :=
  Iff.rfl

/-- The long edges `0 ⟶ 2` of a family of triangles with vertices `x`, `y` and `z` lie in
`Hom_X(x, z)`. -/
lemma range_comp_pre_δ_one_le_mappingSpace {Z : SSet.{u}} {g : Z ⟶ (ihom Δ[2]).obj X}
    (hg : Subcomplex.range g ≤ X.triangleSpace x y z) :
    Subcomplex.range (g ≫ (pre (stdSimplex.δ 1)).app X) ≤ X.mappingSpace x z := by
  obtain ⟨h₂, h₀⟩ := (range_le_triangleSpace_iff g).1 hg
  rw [range_le_mappingSpace_iff, uncurry_pre_app] at h₂ h₀ ⊢
  -- The vertex `0` of `Δ[2]` lies on the edge `δ 2`, and the vertex `2` on the edge `δ 0`.
  have e₀ : stdSimplex.δ.{u} (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ 1 ≫ stdSimplex.δ 2 :=
    stdSimplex.δ_comp_δ_self
  have e₂ : stdSimplex.δ.{u} (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ 0 ≫ stdSimplex.δ 0 :=
    stdSimplex.δ_comp_δ_self.symm
  refine ⟨?_, ?_⟩
  · rw [← comp_whiskerRight_assoc, e₀, comp_whiskerRight_assoc, h₂.1]
  · rw [← comp_whiskerRight_assoc, e₂, comp_whiskerRight_assoc, h₀.2]

namespace triangleSpace

variable (x y z)

/-- The restriction `Hom_X(x, y, z) ⟶ Hom_X(x, y)` of a triangle to its edge `0 ⟶ 1`. -/
noncomputable def edge₀₁ : (X.triangleSpace x y z : SSet.{u}) ⟶ (X.mappingSpace x y : SSet.{u}) :=
  Subcomplex.lift ((X.triangleSpace x y z).ι ≫ (pre (stdSimplex.δ 2)).app X)
    ((range_le_triangleSpace_iff _).1 (Subfunctor.range_ι _).le).1

/-- The restriction `Hom_X(x, y, z) ⟶ Hom_X(y, z)` of a triangle to its edge `1 ⟶ 2`. -/
noncomputable def edge₁₂ : (X.triangleSpace x y z : SSet.{u}) ⟶ (X.mappingSpace y z : SSet.{u}) :=
  Subcomplex.lift ((X.triangleSpace x y z).ι ≫ (pre (stdSimplex.δ 0)).app X)
    ((range_le_triangleSpace_iff _).1 (Subfunctor.range_ι _).le).2

/-- The restriction `Hom_X(x, y, z) ⟶ Hom_X(x, z)` of a triangle to its long edge `0 ⟶ 2`. -/
noncomputable def edge₀₂ : (X.triangleSpace x y z : SSet.{u}) ⟶ (X.mappingSpace x z : SSet.{u}) :=
  Subcomplex.lift ((X.triangleSpace x y z).ι ≫ (pre (stdSimplex.δ 1)).app X)
    (range_comp_pre_δ_one_le_mappingSpace (Subfunctor.range_ι _).le)

/-- The restriction to the edge `0 ⟶ 1` is restriction along `stdSimplex.δ 2`. -/
@[reassoc (attr := simp)]
lemma edge₀₁_ι : edge₀₁ x y z ≫ (X.mappingSpace x y).ι =
    (X.triangleSpace x y z).ι ≫ (pre (stdSimplex.δ 2)).app X :=
  (rfl)

/-- The restriction to the edge `1 ⟶ 2` is restriction along `stdSimplex.δ 0`. -/
@[reassoc (attr := simp)]
lemma edge₁₂_ι : edge₁₂ x y z ≫ (X.mappingSpace y z).ι =
    (X.triangleSpace x y z).ι ≫ (pre (stdSimplex.δ 0)).app X :=
  (rfl)

/-- The restriction to the long edge `0 ⟶ 2` is restriction along `stdSimplex.δ 1`. -/
@[reassoc (attr := simp)]
lemma edge₀₂_ι : edge₀₂ x y z ≫ (X.mappingSpace x z).ι =
    (X.triangleSpace x y z).ι ≫ (pre (stdSimplex.δ 1)).app X :=
  (rfl)

variable {x y z} in
/-- The edge `0 ⟶ 1` of a simplex of `Hom_X(x, y, z)` is its restriction along `stdSimplex.δ 2`. -/
@[simp]
lemma edge₀₁_app_coe {n : SimplexCategoryᵒᵖ} (σ : (X.triangleSpace x y z : SSet.{u}).obj n) :
    dsimp% ((edge₀₁ x y z).app n σ).val = ((pre (stdSimplex.δ 2)).app X).app n σ.val :=
  (rfl)

variable {x y z} in
/-- The edge `1 ⟶ 2` of a simplex of `Hom_X(x, y, z)` is its restriction along `stdSimplex.δ 0`. -/
@[simp]
lemma edge₁₂_app_coe {n : SimplexCategoryᵒᵖ} (σ : (X.triangleSpace x y z : SSet.{u}).obj n) :
    dsimp% ((edge₁₂ x y z).app n σ).val = ((pre (stdSimplex.δ 0)).app X).app n σ.val :=
  (rfl)

variable {x y z} in
/-- The long edge of a simplex of `Hom_X(x, y, z)` is its restriction along `stdSimplex.δ 1`. -/
@[simp]
lemma edge₀₂_app_coe {n : SimplexCategoryᵒᵖ} (σ : (X.triangleSpace x y z : SSet.{u}).obj n) :
    dsimp% ((edge₀₂ x y z).app n σ).val = ((pre (stdSimplex.δ 1)).app X).app n σ.val :=
  (rfl)

/-- The restriction `Hom_X(x, y, z) ⟶ Hom_X(x, y) ⊗ Hom_X(y, z)` of a triangle to its spine,
the pair of its edges `0 ⟶ 1` and `1 ⟶ 2`. -/
noncomputable def spine : (X.triangleSpace x y z : SSet.{u}) ⟶
    (X.mappingSpace x y : SSet.{u}) ⊗ (X.mappingSpace y z : SSet.{u}) :=
  lift (edge₀₁ x y z) (edge₁₂ x y z)

/-- The first component of the spine is the edge `0 ⟶ 1`. -/
@[reassoc (attr := simp)]
lemma spine_fst : spine x y z ≫ fst _ _ = edge₀₁ x y z := lift_fst _ _

/-- The second component of the spine is the edge `1 ⟶ 2`. -/
@[reassoc (attr := simp)]
lemma spine_snd : spine x y z ≫ snd _ _ = edge₁₂ x y z := lift_snd _ _

variable {x y z} in
/-- A family `g` of `2`-simplices of `X` whose edges are families of edges `e₀₁ : x ⟶ y`,
`e₁₂ : y ⟶ z` and `e₀₂ : x ⟶ z` lifts to the triangle space. -/
lemma exists_lift {Z : SSet.{u}} (g : Z ⟶ (ihom Δ[2]).obj X)
    (e₀₁ : Z ⟶ (X.mappingSpace x y : SSet.{u})) (e₁₂ : Z ⟶ (X.mappingSpace y z : SSet.{u}))
    (e₀₂ : Z ⟶ (X.mappingSpace x z : SSet.{u}))
    (h₂ : g ≫ (pre (stdSimplex.δ 2)).app X = e₀₁ ≫ (X.mappingSpace x y).ι)
    (h₀ : g ≫ (pre (stdSimplex.δ 0)).app X = e₁₂ ≫ (X.mappingSpace y z).ι)
    (h₁ : g ≫ (pre (stdSimplex.δ 1)).app X = e₀₂ ≫ (X.mappingSpace x z).ι) :
    ∃ τ : Z ⟶ (X.triangleSpace x y z : SSet.{u}), τ ≫ (X.triangleSpace x y z).ι = g ∧
      τ ≫ edge₀₁ x y z = e₀₁ ∧ τ ≫ edge₁₂ x y z = e₁₂ ∧ τ ≫ edge₀₂ x y z = e₀₂ := by
  have hg : Subcomplex.range g ≤ X.triangleSpace x y z := by
    rw [range_le_triangleSpace_iff, h₂, h₀]
    exact ⟨(Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le,
      (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le⟩
  refine ⟨Subcomplex.lift g hg, Subcomplex.lift_ι _ _, ?_, ?_, ?_⟩
  · rw [← cancel_mono (X.mappingSpace x y).ι, Category.assoc, edge₀₁_ι, Subcomplex.lift_ι_assoc,
      h₂]
  · rw [← cancel_mono (X.mappingSpace y z).ι, Category.assoc, edge₁₂_ι, Subcomplex.lift_ι_assoc,
      h₀]
  · rw [← cancel_mono (X.mappingSpace x z).ι, Category.assoc, edge₀₂_ι, Subcomplex.lift_ι_assoc,
      h₁]

/-- **The restriction of triangles to their spine is a trivial fibration** (HTT Corollary 2.3.2.5):
for a quasicategory `X`, `Hom_X(x, y, z) ⟶ Hom_X(x, y) ⊗ Hom_X(y, z)` has the right lifting property
with respect to all monomorphisms. -/
theorem rlp_monomorphisms_spine [X.Quasicategory] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (spine x y z) := by
  intro A B i (_ : Mono i)
  -- A lifting problem against `i : A ⟶ B` is a horn `Λ[2, 1]` of `Fun(B, X)`, given by the two
  -- families of edges of `b`, over the triangle of `Fun(A, X)` given by `t`. It has a filler since
  -- restriction `Fun(B, X) ⟶ Fun(A, X)` along `i` is an inner fibration.
  refine ⟨fun {t b} sq ↦ ?_⟩
  let F : B ⟶ (ihom Δ[1]).obj X := (b ≫ fst _ _) ≫ (X.mappingSpace x y).ι
  let G : B ⟶ (ihom Δ[1]).obj X := (b ≫ snd _ _) ≫ (X.mappingSpace y z).ι
  have hFG : stdSimplex.δ 0 ≫ ihomSwapEquiv _ _ _ F = stdSimplex.δ 1 ≫ ihomSwapEquiv _ _ _ G := by
    rw [← ihomSwapEquiv_comp_pre_app, ← ihomSwapEquiv_comp_pre_app]
    congr 1
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_pre_app, mappingSpace.whiskerRight_δ_zero_uncurry_comp_ι,
      mappingSpace.whiskerRight_δ_one_uncurry_comp_ι]
  let ψ := horn₂₁.isPushout.desc _ _ hFG
  have hψ : CommSq ψ Λ[2, 1].ι ((pre i).app X)
      (ihomSwapEquiv _ _ _ (t ≫ (X.triangleSpace x y z).ι)) := ⟨by
    apply horn₂₁.isPushout.hom_ext
    · rw [IsPushout.inl_desc_assoc, horn.ι_ι_assoc, ← ihomSwapEquiv_comp,
        ← ihomSwapEquiv_comp_pre_app, Category.assoc, ← edge₀₁_ι, ← spine_fst_assoc,
        reassoc_of% sq.w]
      simp only [F, Category.assoc]
    · rw [IsPushout.inr_desc_assoc, horn.ι_ι_assoc, ← ihomSwapEquiv_comp,
        ← ihomSwapEquiv_comp_pre_app, Category.assoc, ← edge₁₂_ι, ← spine_snd_assoc,
        reassoc_of% sq.w]
      simp only [G, Category.assoc]⟩
  have := mem_innerFibrations ((pre i).app X) _
    (horn_ι_mem_innerHornInclusions (n := 2) (i := 1) (by decide) (by decide))
  let l : B ⟶ (ihom Δ[2]).obj X := (ihomSwapEquiv _ _ _).symm hψ.lift
  have hl : ihomSwapEquiv _ _ _ l = hψ.lift := (ihomSwapEquiv _ _ _).apply_symm_apply _
  have hl₂ : l ≫ (pre (stdSimplex.δ 2)).app X = F := (ihomSwapEquiv _ _ _).injective (by
    rw [ihomSwapEquiv_comp_pre_app, hl, ← horn.ι_ι 1 2 (by decide), Category.assoc,
      hψ.fac_left, IsPushout.inl_desc])
  have hl₀ : l ≫ (pre (stdSimplex.δ 0)).app X = G := (ihomSwapEquiv _ _ _).injective (by
    rw [ihomSwapEquiv_comp_pre_app, hl, ← horn.ι_ι 1 0 (by decide), Category.assoc,
      hψ.fac_left, IsPushout.inr_desc])
  have hl' : Subcomplex.range l ≤ X.triangleSpace x y z := by
    rw [range_le_triangleSpace_iff, hl₂, hl₀]
    exact ⟨(Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le,
      (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le⟩
  refine ⟨⟨{ l := Subcomplex.lift l hl', fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [← cancel_mono (X.triangleSpace x y z).ι, Category.assoc, Subcomplex.lift_ι]
    refine (ihomSwapEquiv _ _ _).injective ?_
    rw [ihomSwapEquiv_comp, hl, hψ.fac_right]
  · refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, spine_fst, ← cancel_mono (X.mappingSpace x y).ι, Category.assoc,
        edge₀₁_ι, Subcomplex.lift_ι_assoc, hl₂]
    · rw [Category.assoc, spine_snd, ← cancel_mono (X.mappingSpace y z).ι, Category.assoc,
        edge₁₂_ι, Subcomplex.lift_ι_assoc, hl₀]

section

variable [X.Quasicategory]

/-- For a quasicategory, the restriction to the spine has a section. -/
instance isSplitEpi_spine : IsSplitEpi (spine x y z) :=
  isSplitEpi_of_rlp_monomorphisms (rlp_monomorphisms_spine x y z)

/-- The chosen section of the spine has the given edge `0 ⟶ 1`. -/
@[reassoc (attr := simp)]
lemma section_spine_comp_edge₀₁ : section_ (spine x y z) ≫ edge₀₁ x y z = fst _ _ := by
  rw [← spine_fst, IsSplitEpi.id_assoc]

/-- The chosen section of the spine has the given edge `1 ⟶ 2`. -/
@[reassoc (attr := simp)]
lemma section_spine_comp_edge₁₂ : section_ (spine x y z) ≫ edge₁₂ x y z = snd _ _ := by
  rw [← spine_snd, IsSplitEpi.id_assoc]

variable {x y z} in
/-- **Long edges are unique up to homotopy**: for a quasicategory, two families of triangles with
the same spines have homotopic long edges. -/
theorem exists_homotopy_edge₀₂ {Z : SSet.{u}} (τ τ' : Z ⟶ (X.triangleSpace x y z : SSet.{u}))
    (h : τ ≫ spine x y z = τ' ≫ spine x y z) :
    Nonempty (Homotopy (τ ≫ edge₀₂ x y z) (τ' ≫ edge₀₂ x y z)) :=
  let H := (exists_homotopy_of_rlp_monomorphisms (rlp_monomorphisms_spine x y z) τ τ' h).choose
  ⟨H.postcomp _⟩

end

variable {x y z} in
/-- **Parametrized filling of the inner horn `Λ[3, 2]`**: in a quasicategory, three families of
triangles `τ₀ : (x, y, z)`, `τ₁ : (w, y, z)` and `τ₃ : (w, x, y)` with matching edges, the faces of
a horn `Λ[3, 2]` with vertices `w`, `x`, `y`, `z`, admit a family of triangles `(w, x, z)` with
edges the edge `w ⟶ x` of `τ₃`, the long edge of `τ₀` and the long edge of `τ₁`. It is the face
opposite to `y` of a filler of the horn. -/
theorem exists_triangle_of_horn₃₂ [X.Quasicategory] {w : X _⦋0⦌} {Z : SSet.{u}}
    (τ₀ : Z ⟶ (X.triangleSpace x y z : SSet.{u})) (τ₁ : Z ⟶ (X.triangleSpace w y z : SSet.{u}))
    (τ₃ : Z ⟶ (X.triangleSpace w x y : SSet.{u}))
    (h₀₂ : τ₁ ≫ edge₀₁ w y z = τ₃ ≫ edge₀₂ w x y) (h₁₂ : τ₀ ≫ edge₀₁ x y z = τ₃ ≫ edge₁₂ w x y)
    (h₂₃ : τ₀ ≫ edge₁₂ x y z = τ₁ ≫ edge₁₂ w y z) :
    ∃ ρ : Z ⟶ (X.triangleSpace w x z : SSet.{u}), ρ ≫ edge₀₁ w x z = τ₃ ≫ edge₀₁ w x y ∧
      ρ ≫ edge₁₂ w x z = τ₀ ≫ edge₀₂ x y z ∧ ρ ≫ edge₀₂ w x z = τ₁ ≫ edge₀₂ w y z := by
  -- The three families of triangles, as triangles of the quasicategory `Fun(Z, X)`.
  have face {a b c : X _⦋0⦌} (τ : Z ⟶ (X.triangleSpace a b c : SSet.{u})) (k : Fin 3) :
      stdSimplex.δ k ≫ ihomSwapEquiv _ _ _ (τ ≫ (X.triangleSpace a b c).ι) =
        ihomSwapEquiv _ _ _ (τ ≫ (X.triangleSpace a b c).ι ≫ (pre (stdSimplex.δ k)).app X) := by
    rw [← Category.assoc, ihomSwapEquiv_comp_pre_app]
  let ψ := horn₃₂.desc (ihomSwapEquiv _ _ _ (τ₀ ≫ (X.triangleSpace x y z).ι))
    (ihomSwapEquiv _ _ _ (τ₁ ≫ (X.triangleSpace w y z).ι))
    (ihomSwapEquiv _ _ _ (τ₃ ≫ (X.triangleSpace w x y).ι))
    (by rw [face, face, ← edge₀₁_ι, ← edge₀₂_ι, reassoc_of% h₀₂])
    (by rw [face, face, ← edge₀₁_ι, ← edge₁₂_ι, reassoc_of% h₁₂])
    (by rw [face, face, ← edge₁₂_ι, ← edge₁₂_ι, reassoc_of% h₂₃])
  obtain ⟨σ, hσ⟩ := Quasicategory.hornFilling (n := 3) (i := 2) (by decide) (by decide) ψ
  have hσ₀ : stdSimplex.δ 0 ≫ σ = ihomSwapEquiv _ _ _ (τ₀ ≫ (X.triangleSpace x y z).ι) := by
    rw [← horn.ι_ι 2 0 (by decide), Category.assoc, ← hσ, horn₃₂.ι₀_desc]
  have hσ₁ : stdSimplex.δ 1 ≫ σ = ihomSwapEquiv _ _ _ (τ₁ ≫ (X.triangleSpace w y z).ι) := by
    rw [← horn.ι_ι 2 1 (by decide), Category.assoc, ← hσ, horn₃₂.ι₁_desc]
  have hσ₃ : stdSimplex.δ 3 ≫ σ = ihomSwapEquiv _ _ _ (τ₃ ≫ (X.triangleSpace w x y).ι) := by
    rw [← horn.ι_ι 2 3 (by decide), Category.assoc, ← hσ, horn₃₂.ι₃_desc]
  -- The face of the filler opposite to the vertex `2` is the family of triangles we look for.
  let ρ : Z ⟶ (ihom Δ[2]).obj X := (ihomSwapEquiv _ _ _).symm (stdSimplex.δ 2 ≫ σ)
  have hρ (k : Fin 3) : ihomSwapEquiv _ _ _ (ρ ≫ (pre (stdSimplex.δ k)).app X) =
      stdSimplex.δ k ≫ stdSimplex.δ 2 ≫ σ := by
    rw [ihomSwapEquiv_comp_pre_app, Equiv.apply_symm_apply]
  have e₀₁ : stdSimplex.δ.{u} (2 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ 2 ≫ stdSimplex.δ 3 :=
    stdSimplex.δ_comp_δ_self
  have e₁₃ : stdSimplex.δ.{u} (0 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ 1 ≫ stdSimplex.δ 0 :=
    stdSimplex.δ_comp_δ (i := 0) (j := 1) (by decide)
  have e₀₃ : stdSimplex.δ.{u} (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) =
      stdSimplex.δ 1 ≫ stdSimplex.δ 1 :=
    stdSimplex.δ_comp_δ_self.symm
  have hρ₂ : ρ ≫ (pre (stdSimplex.δ 2)).app X = (τ₃ ≫ edge₀₁ w x y) ≫ (X.mappingSpace w x).ι :=
    (ihomSwapEquiv _ _ _).injective (by
      rw [hρ, reassoc_of% e₀₁, hσ₃, face, Category.assoc, edge₀₁_ι])
  have hρ₀ : ρ ≫ (pre (stdSimplex.δ 0)).app X = (τ₀ ≫ edge₀₂ x y z) ≫ (X.mappingSpace x z).ι :=
    (ihomSwapEquiv _ _ _).injective (by
      rw [hρ, reassoc_of% e₁₃, hσ₀, face, Category.assoc, edge₀₂_ι])
  have hρ₁ : ρ ≫ (pre (stdSimplex.δ 1)).app X = (τ₁ ≫ edge₀₂ w y z) ≫ (X.mappingSpace w z).ι :=
    (ihomSwapEquiv _ _ _).injective (by
      rw [hρ, reassoc_of% e₀₃, hσ₁, face, Category.assoc, edge₀₂_ι])
  obtain ⟨τ, -, h₀₁, h₁₂, h₀₂⟩ := exists_lift ρ _ _ _ hρ₂ hρ₀ hρ₁
  exact ⟨τ, h₀₁, h₁₂, h₀₂⟩

end triangleSpace

namespace mappingSpace

open triangleSpace

variable [X.Quasicategory]

variable (x y z) in
/-- For a quasicategory `X`, **the composition of mapping spaces**
`Hom_X(x, y) ⊗ Hom_X(y, z) ⟶ Hom_X(x, z)`: a chosen section of the trivial fibration
`SSet.triangleSpace.spine x y z`, followed by the long edge. It sends two edges to a composite of
them (`SSet.mappingSpace.comp_compStruct`), any other choice of section gives a homotopic map
(`SSet.mappingSpace.exists_homotopy_comp`), and it is unital and associative up to homotopy. -/
noncomputable def comp :
    (X.mappingSpace x y : SSet.{u}) ⊗ (X.mappingSpace y z : SSet.{u}) ⟶
      (X.mappingSpace x z : SSet.{u}) :=
  section_ (triangleSpace.spine x y z) ≫ edge₀₂ x y z

variable (x y z) in
/-- The long edge of the chosen section of the spine is the composition. -/
@[reassoc (attr := simp)]
lemma section_spine_comp_edge₀₂ :
    section_ (triangleSpace.spine x y z) ≫ edge₀₂ x y z = comp x y z :=
  (rfl)

/-- For a quasicategory, the long edges of a family of triangles are homotopic to the composites of
their spines. -/
theorem exists_homotopy_comp_edge₀₂ {Z : SSet.{u}} (τ : Z ⟶ (X.triangleSpace x y z : SSet.{u})) :
    Nonempty (Homotopy ((τ ≫ triangleSpace.spine x y z) ≫ comp x y z) (τ ≫ edge₀₂ x y z)) := by
  rw [← section_spine_comp_edge₀₂, ← Category.assoc]
  exact exists_homotopy_edge₀₂ _ _ (by rw [Category.assoc, IsSplitEpi.id, Category.comp_id])

/-- **The composition is well-defined up to homotopy**: for every section `s` of the trivial
fibration `SSet.triangleSpace.spine x y z`, the map `s ≫ SSet.triangleSpace.edge₀₂ x y z` is
homotopic to `SSet.mappingSpace.comp x y z`. -/
theorem exists_homotopy_comp (s : (X.mappingSpace x y : SSet.{u}) ⊗
      (X.mappingSpace y z : SSet.{u}) ⟶ (X.triangleSpace x y z : SSet.{u}))
    (hs : s ≫ triangleSpace.spine x y z = 𝟙 _) :
    Nonempty (Homotopy (s ≫ edge₀₂ x y z) (comp x y z)) :=
  exists_homotopy_edge₀₂ s (section_ _) (by rw [hs, IsSplitEpi.id])

end mappingSpace

/-! ### Composites of edges -/

section compStruct

variable {x y z : X _⦋0⦌}

namespace triangleSpace

/-- A vertex of the triangle space is a `2`-simplex of `X` exhibiting its long edge as a composite
of its two short edges. -/
noncomputable def compStruct (v : (X.triangleSpace x y z : SSet.{u}) _⦋0⦌) :
    Edge.CompStruct (mappingSpace.obj₀Equiv ((edge₀₁ x y z).app _ v))
      (mappingSpace.obj₀Equiv ((edge₁₂ x y z).app _ v))
      (mappingSpace.obj₀Equiv ((edge₀₂ x y z).app _ v)) :=
  -- The vertex of `Fun(Δ[1], X)` obtained by restricting `v` along `f` is `f ≫ v`.
  have key (f : Δ[1] ⟶ Δ[2]) : ihomObj₀Equiv _ X (((pre f).app X).app _ v.val) =
      f ≫ ihomObj₀Equiv _ X v.val := by
    conv_lhs => rw [← (ihomObj₀Equiv _ X).symm_apply_apply v.val]
    rw [pre_app_app_ihomObj₀Equiv_symm, Equiv.apply_symm_apply]
  Edge.CompStruct.mk (yonedaEquiv (ihomObj₀Equiv _ X v.val))
    (by rw [mappingSpace.obj₀Equiv_apply_edge, edge₀₁_app_coe, key, stdSimplex.yonedaEquiv_δ_comp])
    (by rw [mappingSpace.obj₀Equiv_apply_edge, edge₁₂_app_coe, key, stdSimplex.yonedaEquiv_δ_comp])
    (by rw [mappingSpace.obj₀Equiv_apply_edge, edge₀₂_app_coe, key, stdSimplex.yonedaEquiv_δ_comp])

end triangleSpace

namespace mappingSpace

variable [X.Quasicategory]

/-- **Composition composes edges**: on vertices, the composition of mapping spaces sends two
edges `f : x ⟶ y` and `g : y ⟶ z` to a composite of `f` and `g`. -/
theorem comp_compStruct (f : Edge x y) (g : Edge y z) :
    Nonempty (Edge.CompStruct f g
      (obj₀Equiv ((comp x y z).app _ (obj₀Equiv.symm f, obj₀Equiv.symm g)))) := by
  let v := (section_ (triangleSpace.spine x y z)).app _ (obj₀Equiv.symm f, obj₀Equiv.symm g)
  have h₁ : (triangleSpace.edge₀₁ x y z).app _ v = obj₀Equiv.symm f :=
    congrArg (fun φ ↦ φ.app (op ⦋0⦌) (obj₀Equiv.symm f, obj₀Equiv.symm g))
      (triangleSpace.section_spine_comp_edge₀₁ x y z)
  have h₂ : (triangleSpace.edge₁₂ x y z).app _ v = obj₀Equiv.symm g :=
    congrArg (fun φ ↦ φ.app (op ⦋0⦌) (obj₀Equiv.symm f, obj₀Equiv.symm g))
      (triangleSpace.section_spine_comp_edge₁₂ x y z)
  have := triangleSpace.compStruct v
  rw [h₁, h₂, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact ⟨this⟩

end mappingSpace

end compStruct

/-! ### Unitality and associativity -/

namespace mappingSpace

variable {w x y z : X _⦋0⦌}

variable [X.Quasicategory]

/-- **Left unitality up to homotopy**: composing with the identity of `x` on the left is
homotopic to the identity of `Hom_X(x, y)`. -/
theorem exists_homotopy_id_comp :
    Nonempty (Homotopy (lift (const (obj₀Equiv.symm (Edge.id x))) (𝟙 _) ≫ comp x x y)
      (𝟙 (X.mappingSpace x y : SSet.{u}))) := by
  -- The degenerate triangles `σ 0` on the edges from `x` to `y`.
  let g := (X.mappingSpace x y).ι ≫ (pre (stdSimplex.σ 0)).app X
  have hg (f : Δ[1] ⟶ Δ[2]) :
      g ≫ (pre f).app X = (X.mappingSpace x y).ι ≫ (pre (f ≫ stdSimplex.σ 0)).app X := by
    rw [pre_map, NatTrans.comp_app, Category.assoc]
  have e₀ : stdSimplex.δ.{u} (0 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) = 𝟙 _ :=
    stdSimplex.δ_comp_σ_self (i := 0)
  have e₁ : stdSimplex.δ.{u} (1 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) = 𝟙 _ :=
    stdSimplex.δ_comp_σ_succ (i := 0)
  have e₂ : stdSimplex.δ.{u} (2 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) =
      stdSimplex.σ 0 ≫ stdSimplex.δ 1 :=
    stdSimplex.δ_comp_σ_of_gt (i := 1) (j := 0) (by decide)
  obtain ⟨τ, -, h₀₁, h₁₂, h₀₂⟩ := triangleSpace.exists_lift g
    (const (obj₀Equiv.symm (Edge.id x))) (𝟙 _) (𝟙 _)
    (by
      rw [hg, e₂]
      apply uncurry_injective
      rw [uncurry_pre_app, comp_whiskerRight_assoc, whiskerRight_δ_one_uncurry_ι, comp_const,
        uncurry_const_obj₀Equiv_symm_id_comp_ι])
    (by rw [hg, e₀, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp])
    (by rw [hg, e₁, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp])
  have hs : τ ≫ triangleSpace.spine x x y = lift (const (obj₀Equiv.symm (Edge.id x))) (𝟙 _) :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp [h₀₁]) (by simp [h₁₂])
  have := exists_homotopy_comp_edge₀₂ τ
  rwa [hs, h₀₂] at this

/-- **Right unitality up to homotopy**: composing with the identity of `y` on the right is
homotopic to the identity of `Hom_X(x, y)`. -/
theorem exists_homotopy_comp_id :
    Nonempty (Homotopy (lift (𝟙 _) (const (obj₀Equiv.symm (Edge.id y))) ≫ comp x y y)
      (𝟙 (X.mappingSpace x y : SSet.{u}))) := by
  -- The degenerate triangles `σ 1` on the edges from `x` to `y`.
  let g := (X.mappingSpace x y).ι ≫ (pre (stdSimplex.σ 1)).app X
  have hg (f : Δ[1] ⟶ Δ[2]) :
      g ≫ (pre f).app X = (X.mappingSpace x y).ι ≫ (pre (f ≫ stdSimplex.σ 1)).app X := by
    rw [pre_map, NatTrans.comp_app, Category.assoc]
  have e₀ : stdSimplex.δ.{u} (0 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) =
      stdSimplex.σ 0 ≫ stdSimplex.δ 0 :=
    stdSimplex.δ_comp_σ_of_le (i := 0) (j := 0) (by decide)
  have e₁ : stdSimplex.δ.{u} (1 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 _ :=
    stdSimplex.δ_comp_σ_self (i := 1)
  have e₂ : stdSimplex.δ.{u} (2 : Fin 3) ≫ stdSimplex.σ (1 : Fin 2) = 𝟙 _ :=
    stdSimplex.δ_comp_σ_succ (i := 1)
  obtain ⟨τ, -, h₀₁, h₁₂, h₀₂⟩ := triangleSpace.exists_lift g
    (𝟙 _) (const (obj₀Equiv.symm (Edge.id y))) (𝟙 _)
    (by rw [hg, e₂, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp])
    (by
      rw [hg, e₀]
      apply uncurry_injective
      rw [uncurry_pre_app, comp_whiskerRight_assoc, whiskerRight_δ_zero_uncurry_ι, comp_const,
        uncurry_const_obj₀Equiv_symm_id_comp_ι])
    (by rw [hg, e₁, pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp])
  have hs : τ ≫ triangleSpace.spine x y y = lift (𝟙 _) (const (obj₀Equiv.symm (Edge.id y))) :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp [h₀₁]) (by simp [h₁₂])
  have := exists_homotopy_comp_edge₀₂ τ
  rwa [hs, h₀₂] at this

/-- **Associativity up to homotopy**: for a quasicategory, the two composites
`Hom_X(w, x) ⊗ Hom_X(x, y) ⊗ Hom_X(y, z) ⟶ Hom_X(w, z)` are homotopic. -/
theorem exists_homotopy_comp_assoc :
    Nonempty (Homotopy ((α_ _ _ _).hom ≫ _ ◁ comp x y z ≫ comp w x z)
      (comp w x y ▷ _ ≫ comp w y z)) := by
  -- For edges `f : w ⟶ x`, `g : x ⟶ y` and `h : y ⟶ z`, the triangles with spines `(f, g)`,
  -- `(g, h)` and `(f ≫ g, h)` form a horn `Λ[3, 2]`.
  let p : ((X.mappingSpace w x : SSet.{u}) ⊗ (X.mappingSpace x y : SSet.{u})) ⊗
      (X.mappingSpace y z : SSet.{u}) ⟶ _ := fst _ _
  let τ₃ := p ≫ section_ (triangleSpace.spine w x y)
  let τ₀ := lift (p ≫ snd _ _) (snd _ _) ≫ section_ (triangleSpace.spine x y z)
  let τ₁ := lift (p ≫ comp w x y) (snd _ _) ≫ section_ (triangleSpace.spine w y z)
  obtain ⟨ρ, h₀₁, h₁₂, h₀₂⟩ := triangleSpace.exists_triangle_of_horn₃₂ τ₀ τ₁ τ₃
    (by simp [τ₁, τ₃, p]) (by simp [τ₀, τ₃, p]) (by simp [τ₀, τ₁, p])
  have hs : ρ ≫ triangleSpace.spine w x z = (α_ _ _ _).hom ≫ _ ◁ comp x y z := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp [h₀₁, τ₃, p]
    · rw [Category.assoc, triangleSpace.spine_snd, h₁₂, Category.assoc, Category.assoc,
        whiskerLeft_snd]
      have hα : (α_ _ _ _).hom ≫ snd _ _ = lift (p ≫ snd _ _) (snd _ _) :=
        CartesianMonoidalCategory.hom_ext _ _ (by simp [p]) (by simp)
      rw [← Category.assoc (α_ _ _ _).hom, hα, section_spine_comp_edge₀₂]
  have ht : ρ ≫ triangleSpace.edge₀₂ w x z = comp w x y ▷ _ ≫ comp w y z := by
    rw [h₀₂]
    simp only [τ₁, Category.assoc, section_spine_comp_edge₀₂]
    congr 1
  have := exists_homotopy_comp_edge₀₂ ρ
  rwa [hs, ht, Category.assoc] at this

end mappingSpace

end SSet
