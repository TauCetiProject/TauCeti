/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.GenLoop.Homotopic
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.Homotopy.HomotopyGroup.ConnectedMap.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.PathSpace.Loop
public import TauCeti.Topology.PathSpace.Prepend

/-!
# Loop maps of `n`-connected maps

A based map `f : X → Y`, `f x = y`, induces the map of fixed-interval loop spaces
`Ω f : Ω X x → Ω Y y`, `γ ↦ f ∘ γ` (`ContinuousMap.loopMap`, defined in
`TauCeti.Topology.PathSpace.Loop`). Under the loop-space shift
`π_k(Ω X, refl x) ≅ π_(k+1)(X, x)` the map induced by `Ω f` on homotopy groups is the map induced
by `f` one degree higher, so connectivity drops by one when passing to loop spaces: if `f`
induces injections on `π_(k+1)` at `x` for `k < n` and surjections for `k ≤ n`, then `Ω f` is
`n`-connected (`ContinuousMap.isNConnected_loopMap`). In particular the loop map of an
`(n + 1)`-connected map is `n`-connected (`ContinuousMap.IsNConnected.loopMap`), and the double
loop map of an `(n + 2)`-connected map is `n`-connected
(`ContinuousMap.IsNConnected.loopMap_loopMap`).

The connectivity of `Ω f` concerns every base point of `Ω X x`, not only the constant loop. In
degree zero the loop-space shift reads `π_0(Ω X x) = π_1(X, x)`, which is independent of the
base point. In positive degrees, prepending a loop `γ` is a homotopy equivalence of `Ω X x`
(`Path.prependHomotopyEquiv`) which commutes with `Ω f` and moves the constant loop into the path
component of `γ`; so the maps induced by `Ω f` at `γ` and at the constant loop are injective, or
surjective, together.

Only the base point `x` matters: no condition on `f` at other points of `X` is needed, because
`Ω X x` only sees the path component of `x`.

These are the homotopy-theoretic inputs of the homology comparisons between double loop spaces
of the fibre and of the total space of a fibration over a highly connected base: there the fibre
inclusion is highly connected, and so is its double loop map, which therefore induces
isomorphisms on homology in a range.

## Main results

* `ContinuousMap.isNConnected_loopMap`: the loop map is `n`-connected when `f` induces injections
  on `π_(k+1)` at `x` for `k < n` and surjections for `k ≤ n`.
* `ContinuousMap.IsNConnected.loopMap`: the loop map of an `(n + 1)`-connected map is
  `n`-connected.
* `ContinuousMap.IsNConnected.loopMap_loopMap`: the double loop map of an `(n + 2)`-connected map
  is `n`-connected.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1 (the loop-space shift and `n`-connected maps).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy HomotopyGroup

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-! ### Degree zero -/

section DegreeZero

variable (f : C(X, Y)) (hf : f x = y)

/-- A loop seen as a one-dimensional generalized loop. -/
private abbrev toGenLoop (γ : Ω X x) : Ω^ (Fin 1) X x :=
  (GenLoop.homeomorphOfUnique (Fin 1)).symm γ

/-- Read through `toGenLoop`, the loop map is postcomposition with `f`. -/
private theorem map_mk_toGenLoop (γ : Ω X x) :
    map (N := Fin 1) f hf ⟦toGenLoop γ⟧ = ⟦toGenLoop (f.loopMap hf γ)⟧ := by
  rw [map_mk]
  exact congrArg _ (_root_.GenLoop.ext _ _ fun t ↦ by simp)

/-- Two loops are joined in the loop space exactly when they have the same class in `π_1`. -/
private theorem joined_iff_mk_toGenLoop_eq {γ δ : Ω X x} :
    Joined γ δ ↔ (⟦toGenLoop γ⟧ : π_ 1 X x) = ⟦toGenLoop δ⟧ :=
  ⟨fun h ↦ Quotient.sound (GenLoop.homotopic_iff_joined.2
      (h.map (GenLoop.homeomorphOfUnique (Fin 1)).symm.continuous)),
    fun h ↦ by
      simpa using (GenLoop.homotopic_iff_joined.1 (Quotient.exact h)).map
        (GenLoop.homeomorphOfUnique (Fin 1)).continuous⟩

/-- If `f` is surjective on `π_1` at `x`, every loop at `y` is joined to the image of a loop at
`x` under the loop map. -/
private theorem exists_joined_loopMap (h : Function.Surjective (map (N := Fin 1) f hf))
    (δ : Ω Y y) : ∃ γ, Joined (f.loopMap hf γ) δ := by
  obtain ⟨a, ha⟩ := h ⟦toGenLoop δ⟧
  induction a using Quotient.inductionOn with
  | h p =>
    refine ⟨GenLoop.homeomorphOfUnique (Fin 1) p, joined_iff_mk_toGenLoop_eq.2 ?_⟩
    rw [← map_mk_toGenLoop, ← ha]
    simp

/-- If `f` is injective on `π_1` at `x`, two loops at `x` whose images under the loop map are
joined are joined. -/
private theorem joined_of_joined_loopMap (h : Function.Injective (map (N := Fin 1) f hf))
    {γ δ : Ω X x} (hγδ : Joined (f.loopMap hf γ) (f.loopMap hf δ)) : Joined γ δ := by
  rw [joined_iff_mk_toGenLoop_eq, ← map_mk_toGenLoop, ← map_mk_toGenLoop] at hγδ
  exact joined_iff_mk_toGenLoop_eq.2 (h hγδ)

end DegreeZero

/-! ### Positive degrees -/

section PositiveDegree

variable (f : C(X, Y)) (hf : f x = y)

/-- At the constant loop, the map induced by the loop map on `π_(m+1)` is the map induced by `f`
on `π_(m+2)`, up to the loop-space shifts. -/
private theorem pathLoopSpaceMulEquiv_map_loopMap (m : ℕ) (a : π_ (m + 1) (Ω X x) (Path.refl x)) :
    pathLoopSpaceMulEquiv m (map (f.loopMap hf) (f.loopMap_refl hf) a) =
      map f hf (pathLoopSpaceMulEquiv m a) :=
  f.pathLoopSpaceMulEquiv_map hf (f.loopMap hf) (f.loopMap_apply hf) m a

/-- Prepending a loop commutes with the loop map. -/
private theorem prepend_comp_loopMap (γ : Ω X x) :
    (Path.prependHomotopyEquiv (f.loopMap hf γ) y).toFun.comp (f.loopMap hf) =
      (f.loopMap hf).comp (Path.prependHomotopyEquiv γ x).toFun :=
  ContinuousMap.ext fun δ ↦ by
    simp [Path.prependHomotopyEquiv_apply, loopMap_trans]

/-- The map induced by the loop map on `π_k` is injective at a loop `γ` exactly when it is
injective at the constant loop. -/
private theorem injective_map_loopMap_iff (k : ℕ) (γ : Ω X x) :
    Function.Injective (map (N := Fin k) (f.loopMap hf) (rfl : f.loopMap hf γ = _)) ↔
      Function.Injective
        (map (N := Fin k) (f.loopMap hf) (rfl : f.loopMap hf (Path.refl x) = _)) := by
  rw [← (f.loopMap hf).injective_map_iff_of_path
    (Path.joined_prependHomotopyEquiv_refl γ).somePath]
  exact (Path.prependHomotopyEquiv γ x).isWeakHomotopyEquivalence.injective_map_iff_of_comp_eq
    (Path.prependHomotopyEquiv (f.loopMap hf γ) y).isWeakHomotopyEquivalence
    (prepend_comp_loopMap f hf γ) (Fin k) (Path.refl x)

/-- The map induced by the loop map on `π_k` is surjective at a loop `γ` exactly when it is
surjective at the constant loop. -/
private theorem surjective_map_loopMap_iff (k : ℕ) (γ : Ω X x) :
    Function.Surjective (map (N := Fin k) (f.loopMap hf) (rfl : f.loopMap hf γ = _)) ↔
      Function.Surjective
        (map (N := Fin k) (f.loopMap hf) (rfl : f.loopMap hf (Path.refl x) = _)) := by
  rw [← (f.loopMap hf).surjective_map_iff_of_path
    (Path.joined_prependHomotopyEquiv_refl γ).somePath]
  exact (Path.prependHomotopyEquiv γ x).isWeakHomotopyEquivalence.surjective_map_iff_of_comp_eq
    (Path.prependHomotopyEquiv (f.loopMap hf γ) y).isWeakHomotopyEquivalence
    (prepend_comp_loopMap f hf γ) (Fin k) (Path.refl x)

/-- At the constant loop, the map induced by the loop map on `π_(m+1)` is injective when `f` is
injective on `π_(m+2)` at `x`. -/
private theorem injective_map_loopMap_refl (m : ℕ)
    (h : Function.Injective (map (N := Fin (m + 2)) f hf)) :
    Function.Injective
      (map (N := Fin (m + 1)) (f.loopMap hf) (rfl : f.loopMap hf (Path.refl x) = _)) := by
  -- Replace the base point `f.loopMap hf (refl x)` of the target by `refl y`.
  suffices Function.Injective (map (N := Fin (m + 1)) (f.loopMap hf) (f.loopMap_refl hf)) by
    convert this using 2; simp
  intro a b hab
  apply (pathLoopSpaceMulEquiv m).injective
  apply h
  rw [← pathLoopSpaceMulEquiv_map_loopMap, ← pathLoopSpaceMulEquiv_map_loopMap, hab]

/-- At the constant loop, the map induced by the loop map on `π_(m+1)` is surjective when `f` is
surjective on `π_(m+2)` at `x`. -/
private theorem surjective_map_loopMap_refl (m : ℕ)
    (h : Function.Surjective (map (N := Fin (m + 2)) f hf)) :
    Function.Surjective
      (map (N := Fin (m + 1)) (f.loopMap hf) (rfl : f.loopMap hf (Path.refl x) = _)) := by
  suffices Function.Surjective (map (N := Fin (m + 1)) (f.loopMap hf) (f.loopMap_refl hf)) by
    convert this using 2; simp
  intro b
  obtain ⟨a, ha⟩ := h (pathLoopSpaceMulEquiv m b)
  refine ⟨(pathLoopSpaceMulEquiv m).symm a, (pathLoopSpaceMulEquiv m).injective ?_⟩
  rw [pathLoopSpaceMulEquiv_map_loopMap, MulEquiv.apply_symm_apply, ha]

end PositiveDegree

/-- **Loop maps lower connectivity by one.** If a based map `f : X → Y`, `f x = y`, induces
injections `π_(k+1)(X, x) → π_(k+1)(Y, y)` for `k < n` and surjections for `k ≤ n`, then the
loop map `Ω f : Ω X x → Ω Y y` is `n`-connected. -/
theorem isNConnected_loopMap (f : C(X, Y)) (hf : f x = y) {n : ℕ}
    (hinj : ∀ k < n, Function.Injective (map (N := Fin (k + 1)) f hf))
    (hsurj : ∀ k ≤ n, Function.Surjective (map (N := Fin (k + 1)) f hf)) :
    (f.loopMap hf).IsNConnected n where
  exists_joined := exists_joined_loopMap f hf (hsurj 0 (Nat.zero_le n))
  injective k hk γ := by
    cases k with
    | zero =>
      exact map_injective_of_isEmpty_of_joined _ rfl fun _ _ h ↦
        joined_of_joined_loopMap f hf (hinj 0 hk) h
    | succ m =>
      exact (injective_map_loopMap_iff f hf (m + 1) γ).2
        (injective_map_loopMap_refl f hf m (hinj (m + 1) hk))
  surjective k hk γ := by
    cases k with
    | zero =>
      exact map_surjective_of_isEmpty_of_exists_joined _ rfl
        (exists_joined_loopMap f hf (hsurj 0 (Nat.zero_le n)))
    | succ m =>
      exact (surjective_map_loopMap_iff f hf (m + 1) γ).2
        (surjective_map_loopMap_refl f hf m (hsurj (m + 1) hk))

namespace IsNConnected

variable {f : C(X, Y)} {n : ℕ}

/-- **The loop map of an `(n + 1)`-connected map is `n`-connected.** -/
theorem loopMap (hf : f.IsNConnected (n + 1)) (hx : f x = y) : (f.loopMap hx).IsNConnected n := by
  subst hx
  exact isNConnected_loopMap f rfl (fun k hk ↦ hf.injective (k + 1) (by omega) x)
    (fun k hk ↦ hf.surjective (k + 1) (by omega) x)

/-- **The double loop map of an `(n + 2)`-connected map is `n`-connected.** -/
theorem loopMap_loopMap (hf : f.IsNConnected (n + 2)) (hx : f x = y) :
    ((f.loopMap hx).loopMap (f.loopMap_refl hx)).IsNConnected n :=
  (hf.loopMap hx).loopMap (f.loopMap_refl hx)

end IsNConnected

end ContinuousMap
