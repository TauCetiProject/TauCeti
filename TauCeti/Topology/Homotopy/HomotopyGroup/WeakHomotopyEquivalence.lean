/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Weak homotopy equivalences

A continuous map `f : X → Y` is a *weak homotopy equivalence* if it induces a bijection on path
components and a bijection `π_n(X, x) → π_n(Y, f x)` for every `n ≥ 1` and every point `x : X`
(Hatcher, *Algebraic Topology*, Section 4.1). This file defines the predicate
`ContinuousMap.IsWeakHomotopyEquivalence` on Mathlib's cubical homotopy groups and proves its
closure properties: homotopy equivalences are weak homotopy equivalences, the predicate depends
only on the homotopy class of the map, and it is closed under composition and under left and
right cancellation.

Whitehead's theorem, that a weak homotopy equivalence between spaces of CW type is a homotopy
equivalence, is `ContinuousMap.IsWeakHomotopyEquivalence.homotopyEquiv` in
`TauCeti.AlgebraicTopology.Homotopy.Whitehead`.

## Main declarations

* `ContinuousMap.IsWeakHomotopyEquivalence`: the predicate.
* `ContinuousMap.IsWeakHomotopyEquivalence.map_bijective`: the induced map on the homotopy group
  indexed by any finite type of cube directions is bijective.
* `ContinuousMap.IsWeakHomotopyEquivalence.joined_iff`: a weak homotopy equivalence is injective
  on path components.
* `ContinuousMap.IsWeakHomotopyEquivalence.mapOfEq_bijective`: a weak homotopy
  equivalence induces bijections of fundamental groups.
* `ContinuousMap.isWeakHomotopyEquivalence_iff_forall_bijective`: on a path-connected space it
  suffices to check bijectivity on homotopy groups at a single base point.
* `ContinuousMap.HomotopyEquiv.isWeakHomotopyEquivalence`: a homotopy equivalence is a weak
  homotopy equivalence.
* `ContinuousMap.IsWeakHomotopyEquivalence.of_homotopic`,
  `ContinuousMap.IsWeakHomotopyEquivalence.comp`,
  `ContinuousMap.IsWeakHomotopyEquivalence.of_postcomp`,
  `ContinuousMap.IsWeakHomotopyEquivalence.of_precomp`: invariance under homotopy, composition, and
  left and right cancellation (two out of three).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the definition of weak homotopy equivalence preceding Theorem 4.5.
-/

public section

open scoped Topology Topology.Homotopy ContinuousMap
open Topology.Homotopy

namespace ContinuousMap

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f : C(X, Y)} {g : C(Y, Z)}

/-- A continuous map `f : X → Y` is a **weak homotopy equivalence** if every point of `Y` is
joined by a path to a point of the image of `f`, and `f` induces a bijection
`π_n(X, x) → π_n(Y, f x)` for every `n` and every `x : X`.

Since `π_0(X, x)` is the set of path components of `X`, the condition in degree `0` says that `f`
is injective on path components, and also surjective on them as soon as `X` is nonempty. The
field `exists_joined`, surjectivity on path components, adds to this only when `X` is empty: it
then forces `Y` to be empty as well. -/
structure IsWeakHomotopyEquivalence (f : C(X, Y)) : Prop where
  /-- Every point of the target is joined by a path to a point of the image. -/
  exists_joined (y : Y) : ∃ x, Joined (f x) y
  /-- The induced map `π_n(X, x) → π_n(Y, f x)` is bijective for every `n` and every `x`. -/
  bijective (n : ℕ) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) f (rfl : f x = f x))

namespace IsWeakHomotopyEquivalence

/-- A weak homotopy equivalence induces a bijection on the homotopy groups indexed by any finite
type of cube directions, not only on the groups `π_n` indexed by `Fin n`. -/
theorem map_bijective (hf : f.IsWeakHomotopyEquivalence) (N : Type*) [Finite N] (x : X) :
    Function.Bijective (HomotopyGroup.map (N := N) f (rfl : f x = f x)) := by
  let e := Finite.equivFin N
  have h : HomotopyGroup.map (N := N) f (rfl : f x = f x) =
      (HomotopyGroup.congrEquiv e).symm ∘ HomotopyGroup.map f rfl ∘ HomotopyGroup.congrEquiv e := by
    funext a
    simp
  rw [h]
  exact (Equiv.bijective _).comp ((hf.bijective _ x).comp (Equiv.bijective _))

/-- A weak homotopy equivalence is injective on path components: two points of `X` are joined by
a path exactly when their images are. -/
@[simp]
theorem joined_iff (hf : f.IsWeakHomotopyEquivalence) {a b : X} :
    Joined (f a) (f b) ↔ Joined a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map f.continuous⟩
  -- `π_0(X, a)` is the set of path components of `X`: Mathlib's bijection
  -- `homotopyGroupEquivZerothHomotopyOfIsEmpty` sends the class of the zero-dimensional
  -- generalized loop at `c` (the constant map `I^0 → X` with value `c`) to the path component of
  -- `c`. Postcomposing that loop with `f` gives the loop at `f c`.
  let φX := homotopyGroupEquivZerothHomotopyOfIsEmpty (X := X) (Fin 0) a
  let φY := homotopyGroupEquivZerothHomotopyOfIsEmpty (X := Y) (Fin 0) (f a)
  let pt (c : X) : π_ 0 X a := ⟦(genLoopHomeoOfIsEmpty (Fin 0) a).symm c⟧
  have hpt (c : X) : ((genLoopHomeoOfIsEmpty (Fin 0) a).symm c) 0 = c := by
    rw [← genLoopHomeoOfIsEmpty_apply, Homeomorph.apply_symm_apply]
  have hφX (c : X) : φX (pt c) = ZerothHomotopy.mk c := by
    rw [homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, hpt]
  have hmap (c : X) : φY (HomotopyGroup.map f rfl (pt c)) = ZerothHomotopy.mk (f c) := by
    rw [HomotopyGroup.map_mk, homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, GenLoop.map_apply,
      hpt]
  have hab : HomotopyGroup.map f rfl (pt a) = HomotopyGroup.map f rfl (pt b) :=
    φY.injective <| by rw [hmap, hmap]; exact ZerothHomotopy.sound h.somePath
  have := congrArg φX ((hf.bijective 0 a).injective hab)
  rw [hφX, hφX] at this
  exact Quotient.exact this

/-- A map homotopic to a weak homotopy equivalence is a weak homotopy equivalence. -/
theorem of_homotopic {f₀ f₁ : C(X, Y)} (hf : f₀.IsWeakHomotopyEquivalence) (h : f₀.Homotopic f₁) :
    f₁.IsWeakHomotopyEquivalence where
  exists_joined y := by
    obtain ⟨x, hx⟩ := hf.exists_joined y
    exact ⟨x, (Joined.symm ⟨h.some.evalAt x⟩).trans hx⟩
  bijective n x := by
    -- The two induced maps differ by transport along the trace of the homotopy at `x`.
    have hfun : HomotopyGroup.map (N := Fin n) f₁ (rfl : f₁ x = f₁ x) =
        TauCeti.homotopyGroupEquivOfPath ((h.some.evalAt x).cast rfl rfl) ∘
          HomotopyGroup.map f₀ rfl := by
      funext a
      rw [Function.comp_apply, TauCeti.homotopyGroupEquivOfPath_apply]
      exact (TauCeti.homotopyGroupTransport_map h.some rfl rfl a).symm
    rw [hfun]
    exact (Equiv.bijective _).comp (hf.bijective n x)

/-- The identity map is a weak homotopy equivalence. -/
protected theorem id : (ContinuousMap.id X).IsWeakHomotopyEquivalence where
  exists_joined y := ⟨y, Joined.refl y⟩
  bijective _ _ := Function.bijective_iff_has_inverse.2
    ⟨id, HomotopyGroup.map_id_apply, HomotopyGroup.map_id_apply⟩

/-- A composite of weak homotopy equivalences is a weak homotopy equivalence. -/
theorem comp (hg : g.IsWeakHomotopyEquivalence) (hf : f.IsWeakHomotopyEquivalence) :
    (g.comp f).IsWeakHomotopyEquivalence where
  exists_joined z := by
    obtain ⟨y, hy⟩ := hg.exists_joined z
    obtain ⟨x, hx⟩ := hf.exists_joined y
    exact ⟨x, (hx.map g.continuous).trans hy⟩
  bijective n x :=
    HomotopyGroup.map_comp_map g rfl f rfl ▸ (hg.bijective n (f x)).comp (hf.bijective n x)

/-- **Two out of three, left cancellation.** If `g` and `g ∘ f` are weak homotopy equivalences,
then so is `f`. -/
theorem of_postcomp (hg : g.IsWeakHomotopyEquivalence)
    (hgf : (g.comp f).IsWeakHomotopyEquivalence) : f.IsWeakHomotopyEquivalence where
  exists_joined y := by
    obtain ⟨x, hx⟩ := hgf.exists_joined (g y)
    exact ⟨x, hg.joined_iff.1 hx⟩
  bijective n x := (Function.Bijective.of_comp_iff' (hg.bijective n (f x)) _).1
    (HomotopyGroup.map_comp_map g rfl f rfl ▸ hgf.bijective n x)

/-- **Two out of three, right cancellation.** If `f` and `g ∘ f` are weak homotopy equivalences,
then so is `g`. At a point `y` of `Y`, the induced map on homotopy groups is compared, by
base-point change along a path from a point `f x` to `y` and along its image under `g`, with the
induced map at `f x`, which is bijective by cancellation on the right. -/
theorem of_precomp (hf : f.IsWeakHomotopyEquivalence)
    (hgf : (g.comp f).IsWeakHomotopyEquivalence) : g.IsWeakHomotopyEquivalence where
  exists_joined z := by
    obtain ⟨x, hx⟩ := hgf.exists_joined z
    exact ⟨f x, hx⟩
  bijective n y := by
    obtain ⟨x, ⟨γ⟩⟩ := hf.exists_joined y
    exact (TauCeti.bijective_map_iff_of_path g γ).1
      ((Function.Bijective.of_comp_iff _ (hf.bijective n x)).1
        (HomotopyGroup.map_comp_map g rfl f rfl ▸ hgf.bijective n x))

/-- A weak homotopy equivalence induces a bijection of fundamental groups at every base point. -/
theorem mapOfEq_bijective (hf : f.IsWeakHomotopyEquivalence) {x : X} {y : Y}
    (hxy : f x = y) : Function.Bijective (FundamentalGroup.mapOfEq f hxy) := by
  subst hxy
  exact (HomotopyGroup.bijective_map_iff_bijective_mapOfEq f rfl).1 (hf.bijective 1 x)

end IsWeakHomotopyEquivalence

/-- **On a path-connected space, weak homotopy equivalences can be detected at one point.** A
map out of a path-connected space is a weak homotopy equivalence exactly when it induces a
bijection `π_n(X, x) → π_n(Y, f x)` for every `n` at a single base point `x`. In degree `0` this
says that `Y` is path-connected as well. -/
theorem isWeakHomotopyEquivalence_iff_forall_bijective [PathConnectedSpace X] (x : X) :
    f.IsWeakHomotopyEquivalence ↔
      ∀ n, Function.Bijective (HomotopyGroup.map (N := Fin n) f (rfl : f x = f x)) := by
  refine ⟨fun hf n ↦ hf.bijective n x, fun h ↦ ⟨fun y ↦ ?_, fun n x' ↦ ?_⟩⟩
  · -- Surjectivity on `π_0(Y, f x)`, the set of path components of `Y`, finds a point of `X`
    -- whose image is joined to `y`.
    let φY := homotopyGroupEquivZerothHomotopyOfIsEmpty (X := Y) (Fin 0) (f x)
    obtain ⟨a, ha⟩ := (h 0).2 (φY.symm (ZerothHomotopy.mk y))
    induction a using Quotient.inductionOn with
    | h p =>
    refine ⟨p 0, Quotient.exact (?_ : ZerothHomotopy.mk (f (p 0)) = ZerothHomotopy.mk y)⟩
    rw [← φY.apply_symm_apply (ZerothHomotopy.mk y), ← ha, HomotopyGroup.map_mk,
      homotopyGroupEquivZerothHomotopyOfIsEmpty_mk, GenLoop.map_apply]
  · exact (TauCeti.bijective_map_iff_of_path f (PathConnectedSpace.somePath x x')).1 (h n)

/-- **A homotopy equivalence is a weak homotopy equivalence.** -/
theorem HomotopyEquiv.isWeakHomotopyEquivalence (e : X ≃ₕ Y) :
    e.toFun.IsWeakHomotopyEquivalence where
  exists_joined y := ⟨e.invFun y, ⟨e.right_inv.some.evalAt y⟩⟩
  bijective _ x := HomotopyGroup.map_bijective_of_homotopyEquiv e x

end ContinuousMap
