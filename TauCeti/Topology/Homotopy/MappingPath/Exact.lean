/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic
public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.Homotopy.MappingPath.Functoriality
public import TauCeti.Topology.Homotopy.MappingPath.PathFibration
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

/-!
# The exact homotopy sequence of a map

Let `f : X ⟶ Y` be a continuous map and `x` a point of `X`. The **homotopy fibre** of `f` over
`f x` is the mapping-path fibre `MappingPathFiber f (f x)`, of the pairs `(z, γ)` of a point `z`
of `X` and a path `γ` in `Y` from `f z` to `f x`. Its source projection
`TauCeti.TopCat.homotopyFiberProj f x`, `(z, γ) ↦ z`, is a Hurewicz fibration, with base point
the point `x` with the constant path (`TauCeti.TopCat.homotopyFiberBasepoint f x`). This file
shows that the homotopy sequence

`⋯ → π_{n+1}(Y) → π_n(Fib f) → π_n(X) → π_n(Y) → ⋯`

of this projection followed by `f` is exact at the groups of `X`, and that the composite
`π_{n+1}(X) → π_{n+1}(Y) → π_n(Fib f)` controls the kernel of the projection:

* a class of `X` comes from the homotopy fibre exactly when `f` kills it
  (`TauCeti.TopCat.mem_range_map_homotopyFiberProj_iff`);
* if `f` is surjective on `π_{n+1}`, the projection has trivial kernel on `π_n`
  (`TauCeti.TopCat.eq_const_of_map_homotopyFiberProj_eq_const`).

The proof compares the projection with the fixed-end path fibration of `Y`, the source
projection of `MappingPathFiber (ContinuousMap.id Y) (f x)`. The map `(z, γ) ↦ (f z, γ)` is a map
of fibrations over `f`, and it identifies the two fibres over `x` and over `f x`, both being the
space of loops at `f x`. The total space of the path fibration is contractible, so its boundary
map is surjective with trivial kernel
(`TauCeti.TopCat.fibrationBoundary_eq_const_iff_of_subsingleton`,
`TauCeti.TopCat.surjective_fibrationBoundary_of_subsingleton`), and naturality of the boundary
map (`TauCeti.TopCat.fibrationBoundary_map`) shows that the boundary map of the homotopy fibre is
the composite of `f` with that bijection.

Homotopy groups are indexed as in `TauCeti.Topology.Homotopy.SerreFibration.Exact`: `π_{n+1}`
is modelled on the cube `I^(Option N)` and `π_n` on `I^N`, for a finite index type `N` with `n`
elements, which may be empty.

## Main declarations

* `TauCeti.TopCat.homotopyFiberProj`: the projection of the homotopy fibre of `f` to `X`, a
  Hurewicz fibration (`TauCeti.TopCat.isHurewiczFibration_homotopyFiberProj`).
* `TauCeti.TopCat.mem_range_map_homotopyFiberProj_iff`: exactness at the homotopy groups of `X`.
* `TauCeti.TopCat.eq_const_of_map_homotopyFiberProj_eq_const`: the projection has trivial
  kernel on `π_n` when `f` is surjective on `π_{n+1}`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.3, the long exact sequence of homotopy fibres.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

open CategoryTheory Set unitInterval
open scoped Topology Topology.Homotopy

universe w u

namespace TauCeti.TopCat

variable {N : Type*} [Finite N]

/-! ### The homotopy fibre of a map -/

/-- The source projection of a mapping-path fibre, written as a function, is a Hurewicz
fibration. -/
private theorem isHurewiczFibration_val_fst {B K : Type u} [TopologicalSpace B]
    [TopologicalSpace K] (g : C(B, K)) (k : K) :
    IsHurewiczFibration.{w} fun z : MappingPathFiber g k ↦ z.val.1 := by
  have h : (fun z : MappingPathFiber g k ↦ z.val.1) = MappingPathFiber.proj g k :=
    funext fun z ↦ (MappingPathFiber.proj_apply g k z).symm
  rw [h]
  exact MappingPathFiber.isHurewiczFibration_proj g k

variable {X Y : _root_.TopCat.{u}} (f : X ⟶ Y) (x : X)

/-- The projection `(z, γ) ↦ z` of the homotopy fibre `MappingPathFiber f (f x)` of `f` over
`f x`, of the points `z` of `X` with a path from `f z` to `f x`, to `X`. -/
def homotopyFiberProj : _root_.TopCat.of (MappingPathFiber f.hom (f x)) ⟶ X :=
  _root_.TopCat.ofHom ⟨fun z ↦ z.val.1, by fun_prop⟩

@[simp]
theorem homotopyFiberProj_apply (z : MappingPathFiber f.hom (f x)) :
    homotopyFiberProj f x z = z.val.1 :=
  (rfl)

/-- The projection of the homotopy fibre is a Hurewicz fibration. -/
theorem isHurewiczFibration_homotopyFiberProj :
    IsHurewiczFibration.{w} (homotopyFiberProj f x) :=
  isHurewiczFibration_val_fst f.hom (f x)

/-- The projection of the homotopy fibre is a Serre fibration. -/
theorem serreFibrations_homotopyFiberProj : serreFibrations (homotopyFiberProj f x) :=
  (isHurewiczFibration_homotopyFiberProj.{0, u} f x).mem_serreFibrations

/-- The base point of the homotopy fibre, in the fibre of its projection over `x`: the point `x`
with the constant path at `f x`. -/
def homotopyFiberBasepoint : (homotopyFiberProj f x).fiber x :=
  ⟨⟨(x, ContinuousMap.const I (f x)), rfl, rfl⟩, rfl⟩

@[simp]
theorem homotopyFiberBasepoint_val :
    (homotopyFiberBasepoint f x).1.val = (x, ContinuousMap.const I (f x)) :=
  (rfl)

/-- The fixed-end path fibration of `Y` over `f x`, the source projection of
`MappingPathFiber (ContinuousMap.id Y) (f x)`. -/
private abbrev pathProj : _root_.TopCat.of (MappingPathFiber (ContinuousMap.id Y) (f x)) ⟶ Y :=
  _root_.TopCat.ofHom ⟨fun z ↦ z.val.1, by fun_prop⟩

private theorem serreFibrations_pathProj : serreFibrations (pathProj f x) :=
  IsHurewiczFibration.mem_serreFibrations (isHurewiczFibration_val_fst.{0, u} _ _)

/-- The map `(z, γ) ↦ (f z, γ)` from the homotopy fibre of `f` to the paths ending at `f x`. -/
private abbrev toPath :
    _root_.TopCat.of (MappingPathFiber f.hom (f x)) ⟶
      _root_.TopCat.of (MappingPathFiber (ContinuousMap.id Y) (f x)) :=
  _root_.TopCat.ofHom ⟨fun z ↦ ⟨(f z.val.1, z.val.2), z.property.1, z.property.2⟩, by fun_prop⟩

/-- The homotopy fibre maps to the path fibration over `f`. -/
private theorem commSq : CommSq (toPath f x) (homotopyFiberProj f x) (pathProj f x) f :=
  ⟨rfl⟩

omit [Finite N] in
/-- The map of fibrations is a homeomorphism of the fibres over `x` and over `f x`, both the
space of loops at `f x`; so it is bijective on homotopy groups. -/
private theorem bijective_map_fiberMap {e : (homotopyFiberProj f x).fiber x} :
    Function.Bijective (HomotopyGroup.map (N := N) ((commSq f x).fiberMap x).hom
      (rfl : ((commSq f x).fiberMap x) e = _)) := by
  -- The inverse forgets the source point, which is `f x`, and puts back `x`.
  let g : C((pathProj f x).fiber (f x), (homotopyFiberProj f x).fiber x) :=
    ⟨fun q ↦ ⟨⟨(x, q.1.val.2), q.1.property.1.trans (Set.mem_singleton_iff.1 q.2),
      q.1.property.2⟩, rfl⟩, by fun_prop⟩
  have hF (q : (homotopyFiberProj f x).fiber x) :
      (((commSq f x).fiberMap x).hom q).1.val = (f q.1.val.1, q.1.val.2) :=
    congrArg Subtype.val (CommSq.fiberMap_apply_coe (commSq f x) x q)
  have hg : g ((commSq f x).fiberMap x e) = e := by
    have h := congrArg Prod.snd (hF e)
    exact Subtype.ext (Subtype.ext (Prod.ext (Set.mem_singleton_iff.1 e.2).symm h))
  refine Function.bijective_iff_has_inverse.2 ⟨HomotopyGroup.map g hg, fun a ↦ ?_, fun a ↦ ?_⟩
  · refine HomotopyGroup.map_map_of_comp_eq_id g _ _ hg
      (ContinuousMap.ext fun q ↦ Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))) a
    · exact (Set.mem_singleton_iff.1 q.2).symm
    · have h := congrArg Prod.snd (hF q)
      exact h
  · refine HomotopyGroup.map_map_of_comp_eq_id _ g hg _
      (ContinuousMap.ext fun q ↦ Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))) a
    · have h := congrArg Prod.fst (hF (g q))
      exact h.trans (Set.mem_singleton_iff.1 q.2).symm
    · have h := congrArg Prod.snd (hF (g q))
      exact h

/-- The boundary map of the homotopy fibre of `f` is `f` followed by the boundary map of the path
fibration of `Y`, up to the identification of their fibres. -/
private theorem fibrationBoundary_toPath (a : HomotopyGroup (Option N) X x) :
    fibrationBoundary (serreFibrations_pathProj f x)
        ((commSq f x).fiberMap x (homotopyFiberBasepoint f x)) (HomotopyGroup.map f.hom rfl a) =
      HomotopyGroup.map ((commSq f x).fiberMap x).hom rfl
        (fibrationBoundary (serreFibrations_homotopyFiberProj f x) (homotopyFiberBasepoint f x)
          a) :=
  fibrationBoundary_map (commSq f x) _ _ a

/-- **Exactness of the homotopy sequence of a map at the source.** A class of `π_{n+1}(X, x)`
comes from the homotopy fibre of `f` exactly when `f` sends it to the trivial class. -/
theorem mem_range_map_homotopyFiberProj_iff {a : HomotopyGroup (Option N) X x} :
    a ∈ range (HomotopyGroup.map (homotopyFiberProj f x).hom
      (Set.mem_singleton_iff.1 (homotopyFiberBasepoint f x).2)) ↔
      HomotopyGroup.map f.hom rfl a = ⟦GenLoop.const⟧ := by
  have hP := serreFibrations_pathProj f x
  rw [mem_range_homotopyGroupMap_iff_fibrationBoundary_eq (serreFibrations_homotopyFiberProj f x),
    ← (fibrationBoundary_eq_const_iff_of_subsingleton hP
      (e := (commSq f x).fiberMap x (homotopyFiberBasepoint f x))),
    fibrationBoundary_toPath, ← GenLoop.map_const ((commSq f x).fiberMap x).hom rfl,
    ← HomotopyGroup.map_mk _ rfl]
  exact (bijective_map_fiberMap (N := N) f x).injective.eq_iff.symm

/-- **The kernel of the projection of the homotopy fibre.** If `f` is surjective on `π_{n+1}`,
then a class of `π_n` of the homotopy fibre of `f` which projects to the trivial class of `X` is
trivial. -/
theorem eq_const_of_map_homotopyFiberProj_eq_const
    (hf : Function.Surjective (HomotopyGroup.map (N := Option N) f.hom (rfl : f x = f x)))
    {c : HomotopyGroup N (_root_.TopCat.of (MappingPathFiber f.hom (f x)))
      (homotopyFiberBasepoint f x).1}
    (hc : HomotopyGroup.map (homotopyFiberProj f x).hom
      (Set.mem_singleton_iff.1 (homotopyFiberBasepoint f x).2) c = ⟦GenLoop.const⟧) :
    c = ⟦GenLoop.const⟧ := by
  have hq := serreFibrations_homotopyFiberProj f x
  have hP := serreFibrations_pathProj f x
  -- The class `c` comes from the fibre, and every class of the fibre is a boundary.
  obtain ⟨d, rfl⟩ := (mem_range_homotopyGroupMap_fiberι_iff hq).2 hc
  obtain ⟨a', ha'⟩ := surjective_fibrationBoundary_of_subsingleton hP
    (e := (commSq f x).fiberMap x (homotopyFiberBasepoint f x))
    (HomotopyGroup.map ((commSq f x).fiberMap x).hom rfl d)
  obtain ⟨a, rfl⟩ := hf a'
  rw [fibrationBoundary_toPath] at ha'
  have hd := (bijective_map_fiberMap (N := N) f x).injective ha'
  exact (mem_range_fibrationBoundary_iff hq).1 ⟨a, hd⟩

end TauCeti.TopCat
