/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.GroupTheory.Coprod.Basic

import TauCeti.AlgebraicTopology.FundamentalGroup.CoverGeneration
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue
import TauCeti.CategoryTheory.Groupoid.SingleObj

/-!
# The based Seifert--van Kampen theorem

Suppose that the interiors of two sets `A` and `B` cover a space `X`, that `A`, `B` and `A ∩ B`
are path connected, and that all three contain a basepoint `x`. This file proves that the square
of fundamental groups induced by the inclusions

```
π₁(A ∩ B, x) ⟶ π₁(A, x)
     ↓             ↓
π₁(B, x)    ⟶  π₁(X, x)
```

is a pushout of groups: `π₁(X, x)` is the amalgamated free product of `π₁(A, x)` and `π₁(B, x)`
over `π₁(A ∩ B, x)`. When `A ∩ B` is moreover simply connected, the amalgamation is trivial and the
canonical map `π₁(A, x) ∗ π₁(B, x) →* π₁(X, x)` from the free product is an isomorphism.

The homomorphism out of `π₁(X, x)` induced by compatible homomorphisms `fA` and `fB` out of
`π₁(A, x)` and `π₁(B, x)` is built from the fundamental-groupoid gluing theorem
`TauCeti.FundamentalGroupoid.glue`. Choose for every point `z` of `A` a morphism from `x` to `z` in
the fundamental groupoid of `A`, taken inside `A ∩ B` whenever `z ∈ A ∩ B`, and similarly for `B`.
Conjugating by these morphisms turns `fA` and `fB` into functors out of the fundamental groupoids of
`A` and `B`; on `A ∩ B` both functors are induced by the common restriction of `fA` and `fB` to
`π₁(A ∩ B, x)`, so they glue. Uniqueness is the generation half of van Kampen,
`TauCeti.FundamentalGroup.range_map_subtypeVal_sup_eq_top`.

## Main declarations

* `TauCeti.vanKampenDesc`: the homomorphism `π₁(X, x) →* K` induced by homomorphisms out of
  `π₁(A, x)` and `π₁(B, x)` which agree on `π₁(A ∩ B, x)`.
* `TauCeti.vanKampenDesc_map_left`, `TauCeti.vanKampenDesc_map_right`: it restricts to the given
  homomorphisms.
* `TauCeti.vanKampen_hom_ext`: homomorphisms out of `π₁(X, x)` are determined by their
  restrictions to `π₁(A, x)` and `π₁(B, x)`.
* `TauCeti.isPushout_fundamentalGroup`: **the based Seifert--van Kampen theorem**, as a pushout
  square in the category of groups.
* `TauCeti.vanKampenLift`, `TauCeti.vanKampenLift_bijective`, `TauCeti.vanKampenEquiv`: the
  canonical homomorphism from the free product, and the theorem that it is bijective when `A ∩ B`
  is simply connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20.
* R. Brown, *Topology and Groupoids*, Section 6.7.
-/

public section

open CategoryTheory Limits Set Topology
open scoped FundamentalGroupoid Monoid.Coprod

namespace TauCeti

/-- A choice of morphisms out of `x₀` to every object, which is the identity at `x₀`. -/
private noncomputable def connectingHom {C : Type*} [CategoryTheory.Groupoid C] (x₀ : C)
    (h : ∀ y : C, Nonempty (x₀ ⟶ y)) (y : C) : x₀ ⟶ y :=
  by
    classical
    exact if hy : y = x₀ then eqToHom hy.symm else (h y).some

@[simp]
private theorem connectingHom_self {C : Type*} [CategoryTheory.Groupoid C] (x₀ : C)
    (h : ∀ y : C, Nonempty (x₀ ⟶ y)) : connectingHom x₀ h x₀ = 𝟙 x₀ := by
  simp [connectingHom]

variable {X : Type*} [TopologicalSpace X]

section Connect

variable {S T : Set X}

/-- Morphisms in the fundamental groupoid of a path-connected set `S` from a basepoint `s₀` to
every point, the identity at `s₀`. -/
private noncomputable def baseHom (hS : IsPathConnected S) (s₀ : S) (z : FundamentalGroupoid S) :
    FundamentalGroupoid.mk s₀ ⟶ z := by
  letI : PathConnectedSpace S := isPathConnected_iff_pathConnectedSpace.mp hS
  exact connectingHom _ (FundamentalGroupoid.nonempty_hom _) z

@[simp]
private theorem baseHom_self (hS : IsPathConnected S) (s₀ : S) :
    baseHom hS s₀ (FundamentalGroupoid.mk s₀) = 𝟙 _ := by
  simp [baseHom]

/-- For path-connected sets `S ⊆ T` and a basepoint `s₀ ∈ S`, morphisms in the fundamental
groupoid of `T` from `s₀` to every point, chosen inside `S` for the points of `S`. -/
private noncomputable def connect (hST : S ⊆ T) (hS : IsPathConnected S) (hT : IsPathConnected T)
    (s₀ : S) (z : FundamentalGroupoid T) :
    FundamentalGroupoid.mk (ContinuousMap.inclusion hST s₀) ⟶ z := by
  classical
  exact if hz : z.as.1 ∈ S then
    (FundamentalGroupoid.map (ContinuousMap.inclusion hST)).map
      (baseHom hS s₀ (FundamentalGroupoid.mk ⟨z.as.1, hz⟩))
  else baseHom hT _ z

private theorem connect_map_obj (hST : S ⊆ T) (hS : IsPathConnected S) (hT : IsPathConnected T)
    (s₀ : S) (w : FundamentalGroupoid S) :
    connect hST hS hT s₀ ((FundamentalGroupoid.map (ContinuousMap.inclusion hST)).obj w) =
      (FundamentalGroupoid.map (ContinuousMap.inclusion hST)).map (baseHom hS s₀ w) := by
  classical
  exact dite_eq_left w.as.2

@[simp]
private theorem connect_base (hST : S ⊆ T) (hS : IsPathConnected S) (hT : IsPathConnected T)
    (s₀ : S) :
    connect hST hS hT s₀ (FundamentalGroupoid.mk (ContinuousMap.inclusion hST s₀)) = 𝟙 _ := by
  refine (connect_map_obj hST hS hT s₀ (FundamentalGroupoid.mk s₀)).trans ?_
  rw [baseHom_self]
  exact (FundamentalGroupoid.map _).map_id _

variable {K : Type*} [Monoid K]

/-- The functor out of the fundamental groupoid of `T` induced by a homomorphism out of the
fundamental group, conjugating by the morphisms `connect`. -/
private noncomputable def localFunctor (hST : S ⊆ T) (hS : IsPathConnected S)
    (hT : IsPathConnected T) (s₀ : S)
    (f : FundamentalGroup T (ContinuousMap.inclusion hST s₀) →* K) :
    FundamentalGroupoid T ⥤ SingleObj K :=
  Groupoid.functorOfEndHom _ (connect hST hS hT s₀) f

/-- On the fundamental groupoid of `S`, the local functor of `T` is the one induced by the
restriction of the homomorphism to the fundamental group of `S`. -/
private theorem map_inclusion_comp_localFunctor (hST : S ⊆ T) (hS : IsPathConnected S)
    (hT : IsPathConnected T) (s₀ : S)
    (f : FundamentalGroup T (ContinuousMap.inclusion hST s₀) →* K) :
    FundamentalGroupoid.map (ContinuousMap.inclusion hST) ⋙ localFunctor hST hS hT s₀ f =
      Groupoid.functorOfEndHom _ (baseHom hS s₀)
        (f.comp (FundamentalGroup.map (ContinuousMap.inclusion hST) s₀)) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) fun y z g ↦ ?_
  simp only [localFunctor, Functor.comp_map, Groupoid.functorOfEndHom_map, connect_map_obj,
    eqToHom_refl, Category.id_comp, Category.comp_id, MonoidHom.coe_comp, Function.comp_apply]
  -- `FundamentalGroup.map` applies the functor `FundamentalGroupoid.map` to a loop.
  exact congrArg f (by simp only [CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_inv]; rfl :
      (FundamentalGroupoid.map (ContinuousMap.inclusion hST)).map
        (baseHom hS s₀ y ≫ g ≫ inv (baseHom hS s₀ z)) = _).symm

/-- On loops at the basepoint, the local functor is the given homomorphism. -/
private theorem localFunctor_map_base (hST : S ⊆ T) (hS : IsPathConnected S)
    (hT : IsPathConnected T) (s₀ : S)
    (f : FundamentalGroup T (ContinuousMap.inclusion hST s₀) →* K)
    (g : FundamentalGroup T (ContinuousMap.inclusion hST s₀)) :
    (localFunctor hST hS hT s₀ f).map g = f g := by
  simp [localFunctor]

end Connect

section Pushout

variable {A B : Set X} {x : X}

/-- The basepoint of `A ∩ B`. -/
private abbrev interBase (hxA : x ∈ A) (hxB : x ∈ B) : ↥(A ∩ B) := ⟨x, hxA, hxB⟩

private def swapInter : C(↥(B ∩ A), ↥(A ∩ B)) where
  toFun z := ⟨z.1, z.2.2, z.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk fun z ↦ ⟨z.2.2, z.2.1⟩

/-- The cover of `X` by `A` and `B`, indexed by `Bool`. -/
private abbrev twoCover (A B : Set X) : Bool → Set X := fun b ↦ Bool.rec B A b

private theorem exists_twoCover_mem_nhds (hCover : interior A ∪ interior B = univ) (y : X) :
    ∃ b, twoCover A B b ∈ 𝓝 y := by
  rcases (hCover ▸ mem_univ y : y ∈ interior A ∪ interior B) with hy | hy
  · exact ⟨true, mem_interior_iff_mem_nhds.1 hy⟩
  · exact ⟨false, mem_interior_iff_mem_nhds.1 hy⟩

variable {D : Type*} [Category D]

/-- Functors out of the fundamental groupoids of `A` and `B` which agree on `A ∩ B`, as a family
indexed by `twoCover A B`, satisfy the compatibility hypothesis of the gluing theorem. -/
private theorem twoCover_compatibility (FA : FundamentalGroupoid A ⥤ D)
    (FB : FundamentalGroupoid B ⥤ D)
    (h : FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_left) ⋙ FA =
      FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_right) ⋙ FB) (i j : Bool) :
    FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_left : twoCover A B i ∩ twoCover A B j ⊆ twoCover A B i)) ⋙
        (Bool.rec FB FA i : FundamentalGroupoid (twoCover A B i) ⥤ D) =
      FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_right : twoCover A B i ∩ twoCover A B j ⊆ twoCover A B j)) ⋙
        (Bool.rec FB FA j : FundamentalGroupoid (twoCover A B j) ⥤ D) := by
  cases i <;> cases j
  · rfl
  · -- The inclusions of `B ∩ A` factor through the swap `B ∩ A ≃ A ∩ B`.
    have hr : FundamentalGroupoid.map (ContinuousMap.inclusion (inter_subset_left : B ∩ A ⊆ B)) =
        FundamentalGroupoid.map (swapInter (A := A) (B := B)) ⋙
          FundamentalGroupoid.map (ContinuousMap.inclusion (inter_subset_right : A ∩ B ⊆ B)) := by
      rw [← FundamentalGroupoid.map_comp]
      congr 1
    have hl : FundamentalGroupoid.map (ContinuousMap.inclusion (inter_subset_right : B ∩ A ⊆ A)) =
        FundamentalGroupoid.map (swapInter (A := A) (B := B)) ⋙
          FundamentalGroupoid.map (ContinuousMap.inclusion (inter_subset_left : A ∩ B ⊆ A)) := by
      rw [← FundamentalGroupoid.map_comp]
      congr 1
    rw [hr, hl]
    exact congrArg (FundamentalGroupoid.map (swapInter (A := A) (B := B)) ⋙ ·) h.symm
  · exact h
  · rfl

variable {K : Type*} [Monoid K]

/-- The local functors of `A` and `B`, as a family indexed by `twoCover A B`. -/
private noncomputable def coverFunctor (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsPathConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (fA : FundamentalGroup A ⟨x, hxA⟩ →* K) (fB : FundamentalGroup B ⟨x, hxB⟩ →* K) (b : Bool) :
    FundamentalGroupoid (twoCover A B b) ⥤ SingleObj K :=
  Bool.rec (localFunctor inter_subset_right hAB hB (interBase hxA hxB) fB)
    (localFunctor inter_subset_left hAB hA (interBase hxA hxB) fA) b

/-- The local functors of `A` and `B` agree on the fundamental groupoid of `A ∩ B`. -/
private theorem coverFunctor_compatibility (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsPathConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (fA : FundamentalGroup A ⟨x, hxA⟩ →* K) (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (interBase hxA hxB)) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (interBase hxA hxB))) (i j : Bool) :
    FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_left : twoCover A B i ∩ twoCover A B j ⊆ twoCover A B i)) ⋙
        coverFunctor hA hB hAB hxA hxB fA fB i =
      FundamentalGroupoid.map (ContinuousMap.inclusion
        (inter_subset_right : twoCover A B i ∩ twoCover A B j ⊆ twoCover A B j)) ⋙
        coverFunctor hA hB hAB hxA hxB fA fB j :=
  twoCover_compatibility _ _ ((map_inclusion_comp_localFunctor _ _ _ _ _).trans <|
    (congrArg (Groupoid.functorOfEndHom _ (baseHom hAB _)) h).trans
      (map_inclusion_comp_localFunctor _ _ _ _ _).symm) i j

/-- **The homomorphism out of `π₁(X, x)` given by the based Seifert--van Kampen theorem.**

If the interiors of `A` and `B` cover `X` and `A`, `B` and `A ∩ B` are path connected, then two
homomorphisms out of `π₁(A, x)` and `π₁(B, x)` which agree on `π₁(A ∩ B, x)` are the restrictions
of this homomorphism out of `π₁(X, x)` (`TauCeti.vanKampenDesc_map_left`,
`TauCeti.vanKampenDesc_map_right`); it is the unique such homomorphism
(`TauCeti.vanKampen_hom_ext`). -/
noncomputable def vanKampenDesc (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (fA : FundamentalGroup A ⟨x, hxA⟩ →* K)
    (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        ⟨x, hxA, hxB⟩) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        ⟨x, hxA, hxB⟩)) :
    FundamentalGroup X x →* K :=
  (SingleObj.mapHom _ _).symm (Groupoid.singleObjFunctor (FundamentalGroupoid.mk x) ⋙
    FundamentalGroupoid.glue (exists_twoCover_mem_nhds hCover)
      (coverFunctor hA hB hAB hxA hxB fA fB)
      (coverFunctor_compatibility hA hB hAB hxA hxB fA fB h))

/-- `vanKampenDesc` restricts on a fundamental group of a member of the cover to the
corresponding local functor. -/
private theorem vanKampenDesc_map_subtypeVal (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (fA : FundamentalGroup A ⟨x, hxA⟩ →* K)
    (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        ⟨x, hxA, hxB⟩) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        ⟨x, hxA, hxB⟩))
    (b : Bool) (hx : x ∈ twoCover A B b) (g : FundamentalGroup (twoCover A B b) ⟨x, hx⟩) :
    vanKampenDesc hCover hA hB hAB hxA hxB fA fB h
        (FundamentalGroup.map (ContinuousMap.subtypeVal _) ⟨x, hx⟩ g) =
      (coverFunctor hA hB hAB hxA hxB fA fB b).map g := by
  have hg := CategoryTheory.Functor.congr_hom (FundamentalGroupoid.map_subtypeVal_comp_glue
    (exists_twoCover_mem_nhds hCover) (coverFunctor hA hB hAB hxA hxB fA fB)
    (coverFunctor_compatibility hA hB hAB hxA hxB fA fB h) b) g
  simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp] at hg
  -- `SingleObj.mapHom` has no evaluation lemma: its inverse evaluates a functor on a loop, and
  -- `FundamentalGroup.map` applies `FundamentalGroupoid.map` to it, so `hg` is the claim.
  exact hg

/-- `vanKampenDesc` restricts to `fA` on `π₁(A, x)`. -/
theorem vanKampenDesc_map_left (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (fA : FundamentalGroup A ⟨x, hxA⟩ →* K)
    (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        ⟨x, hxA, hxB⟩) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        ⟨x, hxA, hxB⟩))
    (g : FundamentalGroup A ⟨x, hxA⟩) :
    vanKampenDesc hCover hA hB hAB hxA hxB fA fB h
        (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩ g) = fA g :=
  (vanKampenDesc_map_subtypeVal hCover hA hB hAB hxA hxB fA fB h true hxA g).trans
    (localFunctor_map_base inter_subset_left hAB hA (interBase hxA hxB) fA g)

/-- `vanKampenDesc` restricts to `fB` on `π₁(B, x)`. -/
theorem vanKampenDesc_map_right (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (fA : FundamentalGroup A ⟨x, hxA⟩ →* K)
    (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        ⟨x, hxA, hxB⟩) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        ⟨x, hxA, hxB⟩))
    (g : FundamentalGroup B ⟨x, hxB⟩) :
    vanKampenDesc hCover hA hB hAB hxA hxB fA fB h
        (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩ g) = fB g :=
  (vanKampenDesc_map_subtypeVal hCover hA hB hAB hxA hxB fA fB h false hxB g).trans
    (localFunctor_map_base inter_subset_right hAB hB (interBase hxA hxB) fB g)

/-- `vanKampenDesc` restricts to `fA` on `π₁(A, x)`. -/
@[simp]
theorem vanKampenDesc_comp_map_left (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (fA : FundamentalGroup A ⟨x, hxA⟩ →* K)
    (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        ⟨x, hxA, hxB⟩) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        ⟨x, hxA, hxB⟩)) :
    (vanKampenDesc hCover hA hB hAB hxA hxB fA fB h).comp
        (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩) = fA :=
  MonoidHom.ext (vanKampenDesc_map_left hCover hA hB hAB hxA hxB fA fB h)

/-- `vanKampenDesc` restricts to `fB` on `π₁(B, x)`. -/
@[simp]
theorem vanKampenDesc_comp_map_right (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (fA : FundamentalGroup A ⟨x, hxA⟩ →* K)
    (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        ⟨x, hxA, hxB⟩) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        ⟨x, hxA, hxB⟩)) :
    (vanKampenDesc hCover hA hB hAB hxA hxB fA fB h).comp
        (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩) = fB :=
  MonoidHom.ext (vanKampenDesc_map_right hCover hA hB hAB hxA hxB fA fB h)

/-- **Uniqueness in the based Seifert--van Kampen theorem.** If the interiors of `A` and `B`
cover `X` and `A`, `B` and `A ∩ B` are path connected, then two homomorphisms out of `π₁(X, x)`
which agree on the images of `π₁(A, x)` and `π₁(B, x)` are equal. -/
theorem vanKampen_hom_ext (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) {f g : FundamentalGroup X x →* K}
    (hfgA : f.comp (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩) =
      g.comp (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩))
    (hfgB : f.comp (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩) =
      g.comp (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩)) :
    f = g := by
  have hle : (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩).range ⊔
      (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩).range ≤ f.eqLocus g := by
    refine sup_le ?_ ?_ <;> rintro _ ⟨y, rfl⟩
    exacts [DFunLike.congr_fun hfgA y, DFunLike.congr_fun hfgB y]
  have htop := FundamentalGroup.range_map_subtypeVal_sup_eq_top hCover hA hB hAB hxA hxB
  exact MonoidHom.eq_of_eqOn_top fun y _ ↦ (htop.ge.trans hle) (Subgroup.mem_top y)

/-- **The based Seifert--van Kampen theorem.** If the interiors of `A` and `B` cover `X`, the sets
`A`, `B` and `A ∩ B` are path connected, and all three contain the basepoint `x`, then the square
of fundamental groups induced by the inclusions of `A ∩ B` into `A` and `B` and of `A` and `B`
into `X` is a pushout of groups. That is, `π₁(X, x)` is the free product of `π₁(A, x)` and
`π₁(B, x)` amalgamated over `π₁(A ∩ B, x)`. -/
theorem isPushout_fundamentalGroup (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    IsPushout
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (⟨x, hxA, hxB⟩ : ↥(A ∩ B))))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩))
      (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩)) := by
  have comm : (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩).comp
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) ⟨x, hxA, hxB⟩) =
      (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩).comp
        (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) ⟨x, hxA, hxB⟩) := by
    -- Both composites send the class of a loop in `A ∩ B` to the class of the same loop in `X`.
    ext g
    induction g using Path.Homotopic.Quotient.ind
    rfl
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (congrArg GrpCat.ofHom comm)
    (fun s ↦ GrpCat.ofHom (vanKampenDesc hCover hA hB hAB hxA hxB s.inl.hom s.inr.hom
      (congrArg GrpCat.Hom.hom s.condition))) (fun s ↦ ?_) (fun s ↦ ?_) fun s m h₁ h₂ ↦ ?_)
  · exact GrpCat.hom_ext (vanKampenDesc_comp_map_left hCover hA hB hAB hxA hxB _ _
      (congrArg GrpCat.Hom.hom s.condition))
  · exact GrpCat.hom_ext (vanKampenDesc_comp_map_right hCover hA hB hAB hxA hxB _ _
      (congrArg GrpCat.Hom.hom s.condition))
  · refine GrpCat.hom_ext (vanKampen_hom_ext hCover hA hB hAB hxA hxB ?_ ?_)
    · exact (congrArg GrpCat.Hom.hom h₁).trans (vanKampenDesc_comp_map_left hCover hA hB hAB
        hxA hxB _ _ (congrArg GrpCat.Hom.hom s.condition)).symm
    · exact (congrArg GrpCat.Hom.hom h₂).trans (vanKampenDesc_comp_map_right hCover hA hB hAB
        hxA hxB _ _ (congrArg GrpCat.Hom.hom s.condition)).symm

/-- The canonical homomorphism from the free product of the fundamental groups of two
subspaces to the fundamental group of the ambient space. -/
noncomputable def vanKampenLift (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B) :
    (FundamentalGroup A ⟨x, hxA⟩ ∗ FundamentalGroup B ⟨x, hxB⟩) →* FundamentalGroup X x :=
  Monoid.Coprod.lift
    (FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩)
    (FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩)

/-- `vanKampenLift` restricts on the left factor to the map induced by inclusion. -/
@[simp]
theorem vanKampenLift_apply_inl (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B)
    {g : FundamentalGroup A ⟨x, hxA⟩} :
    vanKampenLift A B x hxA hxB (Monoid.Coprod.inl g) =
      FundamentalGroup.map (ContinuousMap.subtypeVal A) ⟨x, hxA⟩ g :=
  (rfl)

/-- `vanKampenLift` restricts on the right factor to the map induced by inclusion. -/
@[simp]
theorem vanKampenLift_apply_inr (A B : Set X) (x : X) (hxA : x ∈ A) (hxB : x ∈ B)
    {g : FundamentalGroup B ⟨x, hxB⟩} :
    vanKampenLift A B x hxA hxB (Monoid.Coprod.inr g) =
      FundamentalGroup.map (ContinuousMap.subtypeVal B) ⟨x, hxB⟩ g :=
  (rfl)

/-- **The based Seifert--van Kampen theorem for a simply connected overlap.**

If the interiors of two path-connected sets cover `X`, their intersection is simply connected,
and both contain the basepoint, then the canonical homomorphism from the free product of their
fundamental groups to the fundamental group of `X` is bijective. -/
theorem vanKampenLift_bijective (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    Function.Bijective (vanKampenLift A B x hxA hxB) := by
  have : SimplyConnectedSpace ↥(A ∩ B) := hAB.simplyConnectedSpace
  -- The fundamental group of `A ∩ B` is trivial, so the two inclusions agree on it.
  have h : (Monoid.Coprod.inl : FundamentalGroup A ⟨x, hxA⟩ →* _).comp
      (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) ⟨x, hxA, hxB⟩) =
      (Monoid.Coprod.inr : FundamentalGroup B ⟨x, hxB⟩ →* _).comp
        (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right) ⟨x, hxA, hxB⟩) :=
    MonoidHom.ext fun g ↦ by rw [Subsingleton.elim g 1, map_one, map_one]
  have hleft : (vanKampenDesc hCover hA hB hAB.isPathConnected hxA hxB _ _ h).comp
      (vanKampenLift A B x hxA hxB) = MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · exact vanKampenDesc_comp_map_left hCover hA hB hAB.isPathConnected hxA hxB _ _ h
    · exact vanKampenDesc_comp_map_right hCover hA hB hAB.isPathConnected hxA hxB _ _ h
  constructor
  · exact Function.LeftInverse.injective fun g ↦ DFunLike.congr_fun hleft g
  · rw [← MonoidHom.range_eq_top]
    exact (Monoid.Coprod.range_lift _ _).trans <|
      FundamentalGroup.range_map_subtypeVal_sup_eq_top hCover hA hB hAB.isPathConnected hxA hxB

/-- The equivalence in the based Seifert--van Kampen theorem for two path-connected sets with
simply connected intersection. Its underlying homomorphism is `vanKampenLift`. -/
noncomputable def vanKampenEquiv (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    (FundamentalGroup A ⟨x, hxA⟩ ∗ FundamentalGroup B ⟨x, hxB⟩) ≃* FundamentalGroup X x :=
  MulEquiv.ofBijective (vanKampenLift A B x hxA hxB)
    (vanKampenLift_bijective hCover hA hB hAB hxA hxB)

/-- The homomorphism underlying `vanKampenEquiv` is `vanKampenLift`. -/
@[simp]
theorem vanKampenEquiv_toMonoidHom (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsSimplyConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) :
    (↑(vanKampenEquiv hCover hA hB hAB hxA hxB) :
      (FundamentalGroup A ⟨x, hxA⟩ ∗ FundamentalGroup B ⟨x, hxB⟩) →* FundamentalGroup X x) =
      vanKampenLift A B x hxA hxB :=
  (rfl)

end Pushout

end TauCeti
