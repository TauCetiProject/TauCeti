/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
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
`TopCat.Hom.homotopyFiberProj f x`, `(z, γ) ↦ z`, is a Hurewicz fibration, with base point
the point `x` with the constant path (`TopCat.Hom.homotopyFiberBasepoint f x`). This file
shows that the homotopy sequence

`⋯ → π_{n+1}(Y) → π_n(Fib f) → π_n(X) → π_n(Y) → ⋯`

of this projection followed by `f` is exact at the groups of `X`, and that the composite
`π_{n+1}(X) → π_{n+1}(Y) → π_n(Fib f)` controls the kernel of the projection:

* a class of `X` comes from the homotopy fibre exactly when `f` kills it
  (`TopCat.Hom.mem_range_homotopyGroupMap_homotopyFiberProj_iff`);
* if `f` is surjective on `π_{n+1}`, the projection has trivial kernel on `π_n`
  (`TopCat.Hom.eq_const_of_homotopyGroupMap_homotopyFiberProj_eq_const`).

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

* `TopCat.Hom.homotopyFiberProj`: the projection of the homotopy fibre of `f` to `X`, a
  Hurewicz fibration (`TopCat.Hom.isHurewiczFibration_homotopyFiberProj`).
* `TopCat.Hom.homotopyFiberFiberHomeomorph`: the fibre of that projection over `x` is the
  loop space of `Y` at `f x`.
* `TopCat.Hom.mem_range_homotopyGroupMap_homotopyFiberProj_iff`: exactness at the homotopy
  groups of `X`.
* `TopCat.Hom.eq_const_of_homotopyGroupMap_homotopyFiberProj_eq_const`: the projection has
  trivial kernel on `π_n` when `f` is surjective on `π_{n+1}`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.3, the long exact sequence of homotopy fibres.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

open CategoryTheory Set unitInterval TauCeti TauCeti.TopCat
open scoped Topology Topology.Homotopy

universe w u

namespace TopCat.Hom

variable {N : Type*} [Finite N]

/-! ### The homotopy fibre of a map -/

variable {X Y : _root_.TopCat.{u}} (f : X ⟶ Y) (x : X)

/-- The projection `(z, γ) ↦ z` of the homotopy fibre `MappingPathFiber f (f x)` of `f` over
`f x`, of the points `z` of `X` with a path from `f z` to `f x`, to `X`. -/
def homotopyFiberProj : _root_.TopCat.of (MappingPathFiber f.hom (f x)) ⟶ X :=
  _root_.TopCat.ofHom (MappingPathFiber.proj f.hom (f x))

@[simp]
theorem homotopyFiberProj_apply (z : MappingPathFiber f.hom (f x)) :
    homotopyFiberProj f x z = z.val.1 :=
  MappingPathFiber.proj_apply _ _ z

/-- The projection of the homotopy fibre is a Hurewicz fibration. -/
theorem isHurewiczFibration_homotopyFiberProj :
    IsHurewiczFibration.{w} (homotopyFiberProj f x) :=
  MappingPathFiber.isHurewiczFibration_proj f.hom (f x)

/-- The projection of the homotopy fibre is a Serre fibration. -/
theorem serreFibrations_homotopyFiberProj : serreFibrations (homotopyFiberProj f x) :=
  (isHurewiczFibration_homotopyFiberProj.{0, u} f x).mem_serreFibrations

/-- The base point of the homotopy fibre, in the fibre of its projection over `x`: the point `x`
with the constant path at `f x`. -/
def homotopyFiberBasepoint : (homotopyFiberProj f x).fiber x :=
  ⟨⟨(x, ContinuousMap.const I (f x)), rfl, rfl⟩, homotopyFiberProj_apply f x _⟩

@[simp]
theorem homotopyFiberBasepoint_val :
    (homotopyFiberBasepoint f x).1.val = (x, ContinuousMap.const I (f x)) :=
  (rfl)

/-- The fibre over `x` of the projection of the homotopy fibre of `f` is the loop space of `Y` at
`f x`. -/
def homotopyFiberFiberHomeomorph : (homotopyFiberProj f x).fiber x ≃ₜ Ω Y (f x) :=
  MappingPathFiber.projFiberHomeomorphPath f.hom (f x) x

@[simp]
theorem homotopyFiberFiberHomeomorph_apply (p : (homotopyFiberProj f x).fiber x) (t : I) :
    homotopyFiberFiberHomeomorph f x p t = p.1.val.2 t :=
  MappingPathFiber.projFiberHomeomorphPath_apply _ _ x p t

/-- The fixed-end path fibration of `Y` over `f x`, the source projection of
`MappingPathFiber (ContinuousMap.id Y) (f x)`. -/
private abbrev pathProj : _root_.TopCat.of (MappingPathFiber (ContinuousMap.id Y) (f x)) ⟶ Y :=
  _root_.TopCat.ofHom (MappingPathFiber.proj (ContinuousMap.id Y) (f x))

private theorem serreFibrations_pathProj : serreFibrations (pathProj f x) :=
  (MappingPathFiber.isHurewiczFibration_proj.{0} (ContinuousMap.id Y) (f x)).mem_serreFibrations

/-- The map `(z, γ) ↦ (f z, γ)` from the homotopy fibre of `f` to the paths ending at `f x`. -/
private abbrev toPath :
    _root_.TopCat.of (MappingPathFiber f.hom (f x)) ⟶
      _root_.TopCat.of (MappingPathFiber (ContinuousMap.id Y) (f x)) :=
  _root_.TopCat.ofHom (MappingPathFiber.map f.hom (ContinuousMap.id Y) rfl rfl)

/-- The homotopy fibre maps to the path fibration over `f`. -/
private theorem commSq : CommSq (toPath f x) (homotopyFiberProj f x) (pathProj f x) f :=
  ⟨ConcreteCategory.hom_ext _ _ <| ContinuousMap.congr_fun <|
    MappingPathFiber.proj_comp_map f.hom (ContinuousMap.id Y) rfl rfl⟩

omit [Finite N] in
/-- The map of fibrations is a homeomorphism of the fibres over `x` and over `f x`, both the
space of loops at `f x`; so it is bijective on homotopy groups. -/
private theorem bijective_map_fiberMap {e : (homotopyFiberProj f x).fiber x} :
    Function.Bijective (HomotopyGroup.map (N := N) ((commSq f x).fiberMap x).hom
      (rfl : ((commSq f x).fiberMap x) e = _)) := by
  -- Both fibres are the loop space at `f x`, and the map of fibres keeps the loop.
  let φ : (homotopyFiberProj f x).fiber x ≃ₜ (pathProj f x).fiber (f x) :=
    (homotopyFiberFiberHomeomorph f x).trans
      (MappingPathFiber.projFiberHomeomorphPath (ContinuousMap.id Y) (f x) (f x)).symm
  have hφ : ((commSq f x).fiberMap x).hom = ⟨φ, φ.continuous⟩ := by
    refine ContinuousMap.ext fun q ↦ Subtype.ext (Subtype.ext ?_)
    have hφq : (φ q).1.val = (f x, (homotopyFiberFiberHomeomorph f x q).toContinuousMap) :=
      MappingPathFiber.projFiberHomeomorphPath_symm_val_val _ _ _ _
    refine ((congrArg Subtype.val (CommSq.fiberMap_apply_coe (commSq f x) x q)).trans
      (MappingPathFiber.map_val _ _ _ _ _)).trans (hφq ▸ Prod.ext ?_ ?_)
    · exact congrArg f ((homotopyFiberProj_apply f x q.1).symm.trans q.2)
    · exact ContinuousMap.ext fun t ↦ (homotopyFiberFiberHomeomorph_apply f x q t).symm
  have h := (HomotopyGroup.homeomorphEquivOfEq (N := N) φ (DFunLike.congr_fun hφ e).symm).bijective
  rw [funext (HomotopyGroup.homeomorphEquivOfEq_apply φ _)] at h
  convert h

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
theorem mem_range_homotopyGroupMap_homotopyFiberProj_iff {a : HomotopyGroup (Option N) X x} :
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
theorem eq_const_of_homotopyGroupMap_homotopyFiberProj_eq_const
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

end TopCat.Hom
