/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Logic.Function.Iterate

/-!
# The forward orbit of a point under a self-map

For a self-map `f : α → α` of an arbitrary type and a point `x : α`, the *forward orbit* of `x`
is the set `{f^[n] x | n : ℕ}` of all its iterates, including `x = f^[0] x` itself. In arithmetic
dynamics a point is preperiodic exactly when its forward orbit is finite, and a point of canonical
height zero is preperiodic because its forward orbit has bounded height; this file supplies the
set-theoretic API for these arguments.

## Main definitions

* `Function.forwardOrbit f x`: the forward orbit of `x` under `f`, the range of `n ↦ f^[n] x`.

## Main results

* `Function.mem_forwardOrbit`: `y` lies in the forward orbit of `x` iff `f^[n] x = y` for
  some `n`.
* `Function.forwardOrbit_eq_insert`: the forward orbit of `x` is `x` together with the forward
  orbit of `f x`.
* `Function.forwardOrbit_subset_iff_mapsTo`: the forward orbit of `x` is the smallest set
  containing `x` and mapped into itself by `f`.
* `Function.Semiconj.image_forwardOrbit`: a semiconjugacy `g` from `fa` to `fb` maps the forward
  orbit of `x` under `fa` onto the forward orbit of `g x` under `fb`.

The forward orbit is the orbit of `x` under the `ℕ`-action `IterateMulAct f`
(`MulAction.orbit_iterateMulAct`); as a range it is indexed directly by the number of iterations.
Unlike the orbit of a group action, it only moves forwards: under `n ↦ n + 1` on `ℤ`, the point
`1` is not in the forward orbit of `2`.

## References

* J. H. Silverman, *Lecture notes on arithmetic dynamics*, Arizona Winter School 2010, §1.
* G. S. Call and J. H. Silverman, *Canonical heights on varieties with morphisms*,
  Compositio Math. 89 (1993), §1.
-/

public section

open Set

namespace Function

variable {α β : Type*} {f : α → α} {x y : α}

/-- The forward orbit `{f^[n] x | n : ℕ}` of a point `x` under a self-map `f`. It contains `x`
itself, as `f^[0] x`. -/
def forwardOrbit (f : α → α) (x : α) : Set α :=
  range fun n : ℕ ↦ f^[n] x

theorem forwardOrbit_def (f : α → α) (x : α) :
    forwardOrbit f x = range fun n : ℕ ↦ f^[n] x :=
  (rfl)

theorem mem_forwardOrbit : y ∈ forwardOrbit f x ↔ ∃ n : ℕ, f^[n] x = y :=
  Iff.rfl

@[simp]
theorem iterate_mem_forwardOrbit (f : α → α) (x : α) (n : ℕ) : f^[n] x ∈ forwardOrbit f x :=
  ⟨n, rfl⟩

@[simp]
theorem self_mem_forwardOrbit (f : α → α) (x : α) : x ∈ forwardOrbit f x :=
  iterate_mem_forwardOrbit f x 0

@[simp]
theorem apply_mem_forwardOrbit (f : α → α) (x : α) : f x ∈ forwardOrbit f x :=
  iterate_mem_forwardOrbit f x 1

/-- The forward orbit of `x` is the smallest set containing `x` and mapped into itself by `f`. -/
theorem forwardOrbit_subset_iff_mapsTo {s : Set α} (hs : MapsTo f s s) :
    forwardOrbit f x ⊆ s ↔ x ∈ s :=
  ⟨fun h ↦ h (self_mem_forwardOrbit f x), fun hx _ ⟨n, hn⟩ ↦ hn ▸ hs.iterate n hx⟩

/-- `f` maps the forward orbit of any point into itself. -/
theorem mapsTo_forwardOrbit (f : α → α) (x : α) : MapsTo f (forwardOrbit f x) (forwardOrbit f x) :=
  by rintro _ ⟨n, rfl⟩; exact ⟨n + 1, iterate_succ_apply' f n x⟩

theorem forwardOrbit_subset_of_mem (hy : y ∈ forwardOrbit f x) :
    forwardOrbit f y ⊆ forwardOrbit f x :=
  (forwardOrbit_subset_iff_mapsTo (mapsTo_forwardOrbit f x)).2 hy

theorem forwardOrbit_apply_iterate_subset (f : α → α) (x : α) (n : ℕ) :
    forwardOrbit f (f^[n] x) ⊆ forwardOrbit f x :=
  forwardOrbit_subset_of_mem (iterate_mem_forwardOrbit f x n)

theorem forwardOrbit_apply_subset (f : α → α) (x : α) : forwardOrbit f (f x) ⊆ forwardOrbit f x :=
  forwardOrbit_apply_iterate_subset f x 1

/-- The forward orbit of `x` is `x` together with the forward orbit of `f x`. -/
theorem forwardOrbit_eq_insert (f : α → α) (x : α) :
    forwardOrbit f x = insert x (forwardOrbit f (f x)) := by
  refine (insert_subset (self_mem_forwardOrbit f x) (forwardOrbit_apply_subset f x)).antisymm' ?_
  rintro _ ⟨_ | n, rfl⟩
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ ⟨n, (iterate_succ_apply f n x).symm⟩

/-- The forward orbit of `f x` is the image of the forward orbit of `x` under `f`. -/
theorem forwardOrbit_apply (f : α → α) (x : α) : forwardOrbit f (f x) = f '' forwardOrbit f x := by
  simp only [forwardOrbit, ← range_comp, comp_def, ← iterate_succ_apply' f, iterate_succ_apply]

/-- The forward orbit of `x` under an iterate `f^[k]` is contained in its forward orbit under
`f`. -/
theorem forwardOrbit_iterate_subset (f : α → α) (x : α) (k : ℕ) :
    forwardOrbit f^[k] x ⊆ forwardOrbit f x := by
  rintro _ ⟨n, rfl⟩
  exact ⟨k * n, congrFun (iterate_mul f k n) x⟩

@[simp]
theorem forwardOrbit_id (x : α) : forwardOrbit id x = {x} := by
  simp [forwardOrbit]

/-- The forward orbit of a fixed point is the singleton of that point. -/
theorem IsFixedPt.forwardOrbit_eq (hx : IsFixedPt f x) : forwardOrbit f x = {x} := by
  simp [forwardOrbit, iterate_fixed hx]

/-- A semiconjugacy `g` from `fa` to `fb` maps the forward orbit of `x` under `fa` onto the forward
orbit of `g x` under `fb`. -/
theorem Semiconj.image_forwardOrbit {fa : α → α} {fb : β → β} {g : α → β}
    (h : Semiconj g fa fb) (x : α) : g '' forwardOrbit fa x = forwardOrbit fb (g x) := by
  simp only [forwardOrbit, ← range_comp, comp_def, (h.iterate_right _).eq]

end Function
