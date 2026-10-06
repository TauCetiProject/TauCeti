/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI

import TauCeti.AlgebraicTopology.FundamentalGroup.CoverGeneration
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Pushout
import TauCeti.CategoryTheory.Groupoid.SingleObj
import TauCeti.Topology.Connected.PathConnected

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

The same holds for a family of sets `U i`, with interiors covering `X`, whose pairwise
intersections are all one path-connected set `C ∋ x`: `π₁(X, x)` is the wide pushout of the groups
`π₁(U i, x)` over `π₁(C, x)`, and their free product when `C` is simply connected. This is the
form of the theorem that computes the fundamental group of a wedge sum, where `U i` is the `i`-th
summand together with a contractible neighbourhood `C` of the wedge point.

The homomorphism out of `π₁(X, x)` induced by compatible homomorphisms `fA` and `fB` out of
`π₁(A, x)` and `π₁(B, x)` is built from the fundamental-groupoid gluing theorem for two sets,
`TauCeti.FundamentalGroupoid.glueTwo`. Choose for every point `z` of `A` a morphism from `x` to
`z` in the fundamental groupoid of `A`, taken inside `A ∩ B` whenever `z ∈ A ∩ B`, and similarly
for `B`. Conjugating by these morphisms turns `fA` and `fB` into functors out of the fundamental
groupoids of `A` and `B`; on `A ∩ B` both functors are induced by the common restriction of `fA`
and `fB` to `π₁(A ∩ B, x)`, so they glue. Uniqueness is the generation half of van Kampen,
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
* `TauCeti.vanKampenWideDesc`, `TauCeti.vanKampenWideDesc_map`: the universal property of
  `π₁(X, x)` for a family whose pairwise intersections are all `C`.
* `TauCeti.vanKampenWide_hom_ext`: homomorphisms out of `π₁(X, x)` are determined by their
  restrictions to the groups `π₁(U i, x)`, for any family of sets containing `x` whose interiors
  cover `X` and whose pairwise intersections are path connected.
* `TauCeti.isColimitFundamentalGroupWideCocone`: **the Seifert--van Kampen theorem for such a
  family**, as a wide pushout in the category of groups.
* `TauCeti.vanKampenWideLift`, `TauCeti.vanKampenWideEquiv`: the canonical homomorphism from the
  free product of the groups `π₁(U i, x)`, and the resulting isomorphism when `C` is simply
  connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20 and
  Example 1.21.
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

variable {K : Type*} [Monoid K]

/-- The local functors of `A` and `B` agree on the fundamental groupoid of `A ∩ B`. -/
private theorem localFunctor_compatibility (hA : IsPathConnected A) (hB : IsPathConnected B)
    (hAB : IsPathConnected (A ∩ B)) (hxA : x ∈ A) (hxB : x ∈ B)
    (fA : FundamentalGroup A ⟨x, hxA⟩ →* K) (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        (interBase hxA hxB)) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        (interBase hxA hxB))) :
    FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_left) ⋙
        localFunctor inter_subset_left hAB hA (interBase hxA hxB) fA =
      FundamentalGroupoid.map (ContinuousMap.inclusion inter_subset_right) ⋙
        localFunctor inter_subset_right hAB hB (interBase hxA hxB) fB :=
  (map_inclusion_comp_localFunctor _ _ _ _ _).trans <|
    (congrArg (Groupoid.functorOfEndHom _ (baseHom hAB _)) h).trans
      (map_inclusion_comp_localFunctor _ _ _ _ _).symm

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
    FundamentalGroupoid.glueTwo hCover
      (localFunctor inter_subset_left hAB hA (interBase hxA hxB) fA)
      (localFunctor inter_subset_right hAB hB (interBase hxA hxB) fB)
      (localFunctor_compatibility hA hB hAB hxA hxB fA fB h))

/-- `vanKampenDesc` restricts on the fundamental group of a set `U` to a functor `F` out of the
fundamental groupoid of `U` through which the glued functor restricts. -/
private theorem vanKampenDesc_map_subtypeVal (hCover : interior A ∪ interior B = univ)
    (hA : IsPathConnected A) (hB : IsPathConnected B) (hAB : IsPathConnected (A ∩ B))
    (hxA : x ∈ A) (hxB : x ∈ B) (fA : FundamentalGroup A ⟨x, hxA⟩ →* K)
    (fB : FundamentalGroup B ⟨x, hxB⟩ →* K)
    (h : fA.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
        ⟨x, hxA, hxB⟩) =
      fB.comp (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_right)
        ⟨x, hxA, hxB⟩))
    {U : Set X} (hx : x ∈ U) (F : FundamentalGroupoid U ⥤ SingleObj K)
    (hF : FundamentalGroupoid.map (ContinuousMap.subtypeVal U) ⋙
      FundamentalGroupoid.glueTwo hCover
        (localFunctor inter_subset_left hAB hA (interBase hxA hxB) fA)
        (localFunctor inter_subset_right hAB hB (interBase hxA hxB) fB)
        (localFunctor_compatibility hA hB hAB hxA hxB fA fB h) = F)
    (g : FundamentalGroup U ⟨x, hx⟩) :
    vanKampenDesc hCover hA hB hAB hxA hxB fA fB h
        (FundamentalGroup.map (ContinuousMap.subtypeVal _) ⟨x, hx⟩ g) = F.map g := by
  have hg := CategoryTheory.Functor.congr_hom hF g
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
  (vanKampenDesc_map_subtypeVal hCover hA hB hAB hxA hxB fA fB h hxA _
    (FundamentalGroupoid.map_subtypeVal_comp_glueTwo_left hCover _ _ _) g).trans
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
  (vanKampenDesc_map_subtypeVal hCover hA hB hAB hxA hxB fA fB h hxB _
    (FundamentalGroupoid.map_subtypeVal_comp_glueTwo_right hCover _ _ _) g).trans
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

section Wide

/-! ### Families of sets with a common pairwise intersection

Let `U : ι → Set X` be a family whose interiors cover `X`, all of whose members contain a
path-connected set `C ∋ x`, and any two distinct members of which meet exactly in `C`. Then
`π₁(X, x)` is the wide pushout of the groups `π₁(U i, x)` over `π₁(C, x)`; when `C` is simply
connected, it is their free product. For two sets, `C` is `A ∩ B`. The homomorphism out of
`π₁(X, x)` is built as in the two-set case, gluing with `TauCeti.FundamentalGroupoid.glue` in place
of `TauCeti.FundamentalGroupoid.glueTwo`. -/

variable {ι : Type*} {U : ι → Set X} {C : Set X} {x : X}

variable {K : Type*} [Monoid K]

/-- The local functors of the members of the family agree on the fundamental groupoids of their
pairwise intersections. -/
private theorem localFunctor_compatibility_of_pairwise (hUp : ∀ i, IsPathConnected (U i))
    (hC : IsPathConnected C) (hCU : ∀ i, C ⊆ U i) (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C)
    (hx : x ∈ C) (f : ∀ i, FundamentalGroup (U i) ⟨x, hCU i hx⟩ →* K)
    (h : ∀ i j, (f i).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩) =
      (f j).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU j)) ⟨x, hx⟩))
    (i j : ι) :
    FundamentalGroupoid.map (ContinuousMap.inclusion (inter_subset_left : U i ∩ U j ⊆ U i)) ⋙
        localFunctor (hCU i) hC (hUp i) ⟨x, hx⟩ (f i) =
      FundamentalGroupoid.map (ContinuousMap.inclusion (inter_subset_right : U i ∩ U j ⊆ U j)) ⋙
        localFunctor (hCU j) hC (hUp j) ⟨x, hx⟩ (f j) := by
  rcases eq_or_ne i j with rfl | hij
  · -- The two inclusions of `U i ∩ U i` into `U i` are the same map.
    rfl
  -- Both inclusions of `U i ∩ U j` factor through `C`.
  rw [← ContinuousMap.inclusion_comp_inclusion (hCU i) (hUC hij),
    ← ContinuousMap.inclusion_comp_inclusion (hCU j) (hUC hij), FundamentalGroupoid.map_comp,
    FundamentalGroupoid.map_comp, Functor.assoc, Functor.assoc]
  exact congrArg (FundamentalGroupoid.map (ContinuousMap.inclusion (hUC hij)) ⋙ ·) <|
    (map_inclusion_comp_localFunctor _ _ _ _ _).trans <|
      (congrArg (Groupoid.functorOfEndHom _ (baseHom hC _)) (h i j)).trans
        (map_inclusion_comp_localFunctor _ _ _ _ _).symm

/-- **The homomorphism out of `π₁(X, x)` given by the Seifert--van Kampen theorem for a family
with a common pairwise intersection.**

Let the sets `U i` have interiors covering `X`, be path connected, and contain the path-connected
set `C ∋ x`, and let two distinct members meet inside `C`. Then homomorphisms out of the groups
`π₁(U i, x)` which agree on `π₁(C, x)` are the restrictions of this homomorphism out of
`π₁(X, x)` (`TauCeti.vanKampenWideDesc_map`); it is the unique such homomorphism
(`TauCeti.vanKampenWide_hom_ext`). -/
noncomputable def vanKampenWideDesc (hU : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hUp : ∀ i, IsPathConnected (U i)) (hC : IsPathConnected C) (hCU : ∀ i, C ⊆ U i)
    (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C) (hx : x ∈ C)
    (f : ∀ i, FundamentalGroup (U i) ⟨x, hCU i hx⟩ →* K)
    (h : ∀ i j, (f i).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩) =
      (f j).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU j)) ⟨x, hx⟩)) :
    FundamentalGroup X x →* K :=
  (SingleObj.mapHom _ _).symm (Groupoid.singleObjFunctor (FundamentalGroupoid.mk x) ⋙
    FundamentalGroupoid.glue hU (fun i ↦ localFunctor (hCU i) hC (hUp i) ⟨x, hx⟩ (f i))
      (localFunctor_compatibility_of_pairwise hUp hC hCU hUC hx f h))

/-- `vanKampenWideDesc` restricts to `f i` on `π₁(U i, x)`. -/
theorem vanKampenWideDesc_map (hU : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hUp : ∀ i, IsPathConnected (U i)) (hC : IsPathConnected C) (hCU : ∀ i, C ⊆ U i)
    (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C) (hx : x ∈ C)
    (f : ∀ i, FundamentalGroup (U i) ⟨x, hCU i hx⟩ →* K)
    (h : ∀ i j, (f i).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩) =
      (f j).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU j)) ⟨x, hx⟩))
    (i : ι) (g : FundamentalGroup (U i) ⟨x, hCU i hx⟩) :
    vanKampenWideDesc hU hUp hC hCU hUC hx f h
        (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hCU i hx⟩ g) = f i g := by
  have hg := CategoryTheory.Functor.congr_hom (FundamentalGroupoid.map_subtypeVal_comp_glue hU _
    (localFunctor_compatibility_of_pairwise hUp hC hCU hUC hx f h) i) g
  simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp] at hg
  -- `SingleObj.mapHom` has no evaluation lemma: its inverse evaluates a functor on a loop, and
  -- `FundamentalGroup.map` applies `FundamentalGroupoid.map` to it, so `hg` is the claim up to
  -- the value of the local functor on loops at the basepoint.
  exact hg.trans (localFunctor_map_base (hCU i) hC (hUp i) ⟨x, hx⟩ (f i) g)

/-- `vanKampenWideDesc` restricts to `f i` on `π₁(U i, x)`. -/
@[simp]
theorem vanKampenWideDesc_comp_map (hU : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hUp : ∀ i, IsPathConnected (U i)) (hC : IsPathConnected C) (hCU : ∀ i, C ⊆ U i)
    (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C) (hx : x ∈ C)
    (f : ∀ i, FundamentalGroup (U i) ⟨x, hCU i hx⟩ →* K)
    (h : ∀ i j, (f i).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩) =
      (f j).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU j)) ⟨x, hx⟩))
    (i : ι) :
    (vanKampenWideDesc hU hUp hC hCU hUC hx f h).comp
        (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hCU i hx⟩) = f i :=
  MonoidHom.ext (vanKampenWideDesc_map hU hUp hC hCU hUC hx f h i)

/-- **Uniqueness in the Seifert--van Kampen theorem for a family.** If the interiors of the sets
`U i ∋ x` cover `X` and their pairwise intersections are path connected, then two homomorphisms out
of `π₁(X, x)` which agree on the image of every `π₁(U i, x)` are equal. -/
theorem vanKampenWide_hom_ext (hU : ∀ y, ∃ i, U i ∈ 𝓝 y) (hx : ∀ i, x ∈ U i)
    (hpc : ∀ i j, IsPathConnected (U i ∩ U j)) {f g : FundamentalGroup X x →* K}
    (hfg : ∀ i, f.comp (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩) =
      g.comp (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩)) :
    f = g := by
  have hle : (⨆ i, (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩).range :
      Subgroup (FundamentalGroup X x)) ≤ f.eqLocus g :=
    iSup_le fun i ↦ by
      rintro _ ⟨y, rfl⟩
      exact DFunLike.congr_fun (hfg i) y
  have htop := FundamentalGroup.iSup_range_map_subtypeVal_eq_top hU hx hpc
  exact MonoidHom.eq_of_eqOn_top fun y _ ↦ (htop.ge.trans hle) (Subgroup.mem_top y)

/-- The wide span of fundamental groups of the inclusions of `C` into the sets `U i`. -/
noncomputable abbrev fundamentalGroupWideSpan (hCU : ∀ i, C ⊆ U i) (hx : x ∈ C) :
    WidePushoutShape ι ⥤ GrpCat :=
  WidePushoutShape.wideSpan (GrpCat.of (FundamentalGroup C ⟨x, hx⟩))
    (fun i ↦ GrpCat.of (FundamentalGroup (U i) ⟨x, hCU i hx⟩))
    fun i ↦ GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩)

/-- The cocone over `fundamentalGroupWideSpan` with vertex `π₁(X, x)`, whose legs are induced by
the inclusions of `C` and of the sets `U i` into `X`. -/
noncomputable def fundamentalGroupWideCocone (hCU : ∀ i, C ⊆ U i) (hx : x ∈ C) :
    Cocone (fundamentalGroupWideSpan hCU hx) :=
  WidePushoutShape.mkCocone
    (GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.subtypeVal C) ⟨x, hx⟩))
    (fun i ↦ GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hCU i hx⟩))
    fun i ↦ by
      -- Both composites send the class of a loop in `C` to the class of the same loop in `X`.
      ext g
      induction g using Path.Homotopic.Quotient.ind
      rfl

/-- The vertex of `fundamentalGroupWideCocone` is `π₁(X, x)`. -/
@[simp]
theorem fundamentalGroupWideCocone_pt (hCU : ∀ i, C ⊆ U i) (hx : x ∈ C) :
    (fundamentalGroupWideCocone hCU hx).pt = GrpCat.of (FundamentalGroup X x) :=
  by unfold fundamentalGroupWideCocone; rfl

/-- The leg of `fundamentalGroupWideCocone` at `C` is induced by the inclusion of `C`. -/
@[simp]
theorem fundamentalGroupWideCocone_ι_app_none (hCU : ∀ i, C ⊆ U i) (hx : x ∈ C) :
    (fundamentalGroupWideCocone hCU hx).ι.app none ≫
        eqToHom (fundamentalGroupWideCocone_pt hCU hx) =
      GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.subtypeVal C) ⟨x, hx⟩) :=
  by unfold fundamentalGroupWideCocone; rfl

/-- The leg of `fundamentalGroupWideCocone` at `U i` is induced by the inclusion of `U i`. -/
@[simp]
theorem fundamentalGroupWideCocone_ι_app_some (hCU : ∀ i, C ⊆ U i) (hx : x ∈ C) (i : ι) :
    (fundamentalGroupWideCocone hCU hx).ι.app (some i) ≫
        eqToHom (fundamentalGroupWideCocone_pt hCU hx) =
      GrpCat.ofHom (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hCU i hx⟩) :=
  by unfold fundamentalGroupWideCocone; rfl

/-- **The Seifert--van Kampen theorem for a family with a common pairwise intersection.** If the
interiors of the path-connected sets `U i` cover `X`, all of them contain the path-connected set
`C ∋ x`, and two distinct members meet inside `C`, then `π₁(X, x)` is the wide pushout in the
category of groups of the groups `π₁(U i, x)` over `π₁(C, x)`, along the maps induced by the
inclusions. -/
noncomputable def isColimitFundamentalGroupWideCocone (hU : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hUp : ∀ i, IsPathConnected (U i)) (hC : IsPathConnected C) (hCU : ∀ i, C ⊆ U i)
    (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C) (hx : x ∈ C) :
    IsColimit (fundamentalGroupWideCocone hCU hx) :=
  -- The legs of a cocone at the sets `U i`, and their compatibility on `π₁(C, x)`.
  let f (s : Cocone (fundamentalGroupWideSpan hCU hx)) (i : ι) :
      FundamentalGroup (U i) ⟨x, hCU i hx⟩ →* s.pt :=
    (s.ι.app (some i)).hom
  have hs (s : Cocone (fundamentalGroupWideSpan hCU hx)) (i : ι) :
      (f s i).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩) =
        (s.ι.app none).hom :=
    congrArg GrpCat.Hom.hom (s.w (WidePushoutShape.Hom.init i))
  have hf (s : Cocone (fundamentalGroupWideSpan hCU hx)) (i j : ι) :
      (f s i).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩) =
        (f s j).comp (FundamentalGroup.map (ContinuousMap.inclusion (hCU j)) ⟨x, hx⟩) :=
    (hs s i).trans (hs s j).symm
  { desc s := GrpCat.ofHom (vanKampenWideDesc hU hUp hC hCU hUC hx (f s) (hf s))
    fac s j := by
      refine GrpCat.hom_ext ?_
      cases j with
      | none =>
        obtain ⟨i, -⟩ := hU x
        refine Eq.trans ?_ (hs s i)
        ext g
        induction g using Path.Homotopic.Quotient.ind with | mk γ =>
        -- The leg at `C` sends the class of `γ` to the class of the same loop in `X`, which is
        -- also the image under the leg at `U i` of the class of `γ` in `U i`.
        exact vanKampenWideDesc_map hU hUp hC hCU hUC hx (f s) (hf s) i
          (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩ ⟦γ⟧)
      | some i => exact vanKampenWideDesc_comp_map hU hUp hC hCU hUC hx (f s) (hf s) i
    uniq s m hm := GrpCat.hom_ext <| vanKampenWide_hom_ext hU (fun i ↦ hCU i hx)
      (isPathConnected_inter_of_pairwise hUp hC hCU hUC) fun i ↦
        (congrArg GrpCat.Hom.hom (hm (some i))).trans
          (vanKampenWideDesc_comp_map hU hUp hC hCU hUC hx (f s) (hf s) i).symm }

/-- The canonical homomorphism from the free product of the fundamental groups of a family of
subspaces containing `x` to the fundamental group of the ambient space. -/
noncomputable def vanKampenWideLift (U : ι → Set X) (x : X) (hx : ∀ i, x ∈ U i) :
    Monoid.CoprodI (fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) →* FundamentalGroup X x :=
  Monoid.CoprodI.lift fun i ↦ FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩

/-- `vanKampenWideLift` restricts on the `i`-th factor to the map induced by inclusion. -/
@[simp]
theorem vanKampenWideLift_of (U : ι → Set X) (x : X) (hx : ∀ i, x ∈ U i) {i : ι}
    (g : FundamentalGroup (U i) ⟨x, hx i⟩) :
    vanKampenWideLift U x hx
        (Monoid.CoprodI.of (M := fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) g) =
      FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hx i⟩ g :=
  Monoid.CoprodI.lift_of (M := fun i ↦ FundamentalGroup (U i) ⟨x, hx i⟩) _ g

/-- **The Seifert--van Kampen theorem for a family with a simply connected common pairwise
intersection.** If the interiors of the path-connected sets `U i` cover `X`, all of them contain
the simply connected set `C ∋ x`, and two distinct members meet inside `C`, then the canonical
homomorphism from the free product of the groups `π₁(U i, x)` to `π₁(X, x)` is an isomorphism.
Its underlying homomorphism is `vanKampenWideLift`. -/
noncomputable def vanKampenWideEquiv (hU : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hUp : ∀ i, IsPathConnected (U i)) (hC : IsSimplyConnected C) (hCU : ∀ i, C ⊆ U i)
    (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C) (hx : x ∈ C) :
    Monoid.CoprodI (fun i ↦ FundamentalGroup (U i) ⟨x, hCU i hx⟩) ≃* FundamentalGroup X x :=
  have : SimplyConnectedSpace C := hC.simplyConnectedSpace
  let M (i : ι) := FundamentalGroup (U i) ⟨x, hCU i hx⟩
  -- The fundamental group of `C` is trivial, so the inclusions into the free product agree on it.
  have h : ∀ i j, (Monoid.CoprodI.of (M := M) (i := i)).comp
      (FundamentalGroup.map (ContinuousMap.inclusion (hCU i)) ⟨x, hx⟩) =
      (Monoid.CoprodI.of (M := M) (i := j)).comp
        (FundamentalGroup.map (ContinuousMap.inclusion (hCU j)) ⟨x, hx⟩) := fun _ _ ↦
    MonoidHom.ext fun g ↦ by rw [Subsingleton.elim g 1, map_one, map_one]
  let D : FundamentalGroup X x →* Monoid.CoprodI M :=
    vanKampenWideDesc hU hUp hC.isPathConnected hCU hUC hx
      (fun i ↦ Monoid.CoprodI.of (M := M) (i := i)) h
  have hD (i : ι) (g : M i) :
      D (FundamentalGroup.map (ContinuousMap.subtypeVal (U i)) ⟨x, hCU i hx⟩ g) =
        Monoid.CoprodI.of g :=
    vanKampenWideDesc_map hU hUp hC.isPathConnected hCU hUC hx _ h i g
  MonoidHom.toMulEquiv (vanKampenWideLift U x fun i ↦ hCU i hx) D
    (Monoid.CoprodI.ext_hom _ _ fun i ↦ MonoidHom.ext fun g ↦
      (congrArg D (vanKampenWideLift_of U x (fun i ↦ hCU i hx) (i := i) g)).trans (hD i g))
    (vanKampenWide_hom_ext hU (fun i ↦ hCU i hx)
      (isPathConnected_inter_of_pairwise hUp hC.isPathConnected hCU hUC) fun i ↦
        MonoidHom.ext fun g ↦ (congrArg (vanKampenWideLift U x _) (hD i g)).trans
          (vanKampenWideLift_of U x (fun i ↦ hCU i hx) (i := i) g))

/-- `vanKampenWideEquiv` is `vanKampenWideLift`. -/
@[simp]
theorem vanKampenWideEquiv_apply (hU : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hUp : ∀ i, IsPathConnected (U i)) (hC : IsSimplyConnected C) (hCU : ∀ i, C ⊆ U i)
    (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C) (hx : x ∈ C)
    (g : Monoid.CoprodI fun i ↦ FundamentalGroup (U i) ⟨x, hCU i hx⟩) :
    vanKampenWideEquiv hU hUp hC hCU hUC hx g = vanKampenWideLift U x (fun i ↦ hCU i hx) g :=
  (rfl)

/-- The homomorphism underlying `vanKampenWideEquiv` is `vanKampenWideLift`. -/
@[simp]
theorem vanKampenWideEquiv_toMonoidHom (hU : ∀ y, ∃ i, U i ∈ 𝓝 y)
    (hUp : ∀ i, IsPathConnected (U i)) (hC : IsSimplyConnected C) (hCU : ∀ i, C ⊆ U i)
    (hUC : Pairwise fun i j ↦ U i ∩ U j ⊆ C) (hx : x ∈ C) :
    (↑(vanKampenWideEquiv hU hUp hC hCU hUC hx) :
      Monoid.CoprodI (fun i ↦ FundamentalGroup (U i) ⟨x, hCU i hx⟩) →* FundamentalGroup X x) =
      vanKampenWideLift U x fun i ↦ hCU i hx :=
  (rfl)

end Wide

end TauCeti
