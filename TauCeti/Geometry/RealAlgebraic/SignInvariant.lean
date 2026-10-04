/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Sign

/-!
# Sign-invariant functions

A function `f` is *sign-invariant* on a set `s` when it has the same sign at any two points of
`s`, where the sign `SignType.sign` takes the values `-1`, `0` and `1`. In particular a function
that vanishes somewhere on `s` is sign-invariant on `s` only if it vanishes on all of `s`. This is
the invariance asked of the cells of a cylindrical algebraic decomposition adapted to a family of
polynomials: each polynomial of the family is sign-invariant on each cell.

The basic source of sign-invariance is connectedness: a function that is continuous and nowhere
zero on a preconnected set is sign-invariant there, since its sign is a continuous map to the
discrete space `SignType`.

## Main declarations

* `TauCeti.SignInvariant`: sign-invariance of a function on a set.
* `TauCeti.signInvariant_iff_exists`: a sign-invariant function has a single sign on the set.
* `TauCeti.signInvariant_image`: sign-invariance on an image is sign-invariance of the
  composite.
* `IsPreconnected.signInvariant`: a continuous, nowhere-zero function on a preconnected set is
  sign-invariant.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1.
-/

public section

open Set

namespace TauCeti

variable {α β R : Type*}

section Preorder

variable [Zero R] [Preorder R] [DecidableLT R]

/-- A function `f` is sign-invariant on `s` if it has the same sign, possibly zero, at any two
points of `s`. -/
def SignInvariant (f : α → R) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, SignType.sign (f x) = SignType.sign (f y)

variable {f g : α → R} {s t : Set α}

theorem signInvariant_def :
    SignInvariant f s ↔ ∀ x ∈ s, ∀ y ∈ s, SignType.sign (f x) = SignType.sign (f y) :=
  Iff.rfl

/-- A function is sign-invariant on `s` exactly when a single sign is taken at every point of
`s`. -/
theorem signInvariant_iff_exists :
    SignInvariant f s ↔ ∃ σ : SignType, ∀ x ∈ s, SignType.sign (f x) = σ := by
  refine ⟨fun h ↦ ?_, fun ⟨σ, hσ⟩ x hx y hy ↦ (hσ x hx).trans (hσ y hy).symm⟩
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨0, by simp⟩
  · exact ⟨SignType.sign (f x), fun y hy ↦ h y hy x hx⟩

theorem SignInvariant.mono (h : SignInvariant f t) (hst : s ⊆ t) : SignInvariant f s :=
  fun x hx y hy ↦ h x (hst hx) y (hst hy)

theorem SignInvariant.congr (h : SignInvariant f s) (hfg : EqOn f g s) : SignInvariant g s :=
  fun x hx y hy ↦ by rw [← hfg hx, ← hfg hy]; exact h x hx y hy

/-- Sign-invariance on an image is sign-invariance of the composite on the source set. -/
theorem signInvariant_image {u : β → α} {s : Set β} :
    SignInvariant f (u '' s) ↔ SignInvariant (f ∘ u) s := by
  simp [SignInvariant]

/-- A function is sign-invariant on a set containing at most one point. -/
theorem _root_.Set.Subsingleton.signInvariant (hs : s.Subsingleton) : SignInvariant f s :=
  fun x hx y hy ↦ by rw [hs hx hy]

@[simp]
theorem signInvariant_empty : SignInvariant f ∅ :=
  subsingleton_empty.signInvariant

@[simp]
theorem signInvariant_singleton (a : α) : SignInvariant f {a} :=
  subsingleton_singleton.signInvariant

/-- A constant function is sign-invariant on every set. -/
@[simp]
theorem signInvariant_const (c : R) : SignInvariant (fun _ : α ↦ c) s :=
  fun _ _ _ _ ↦ rfl

end Preorder

/-- A function that is continuous and nowhere zero on a preconnected set is sign-invariant
there. -/
theorem _root_.IsPreconnected.signInvariant [Zero R] [LinearOrder R] [TopologicalSpace R]
    [OrderTopology R] [TopologicalSpace α] {f : α → R} {s : Set α} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) : SignInvariant f s :=
  fun _ hx _ hy ↦ hs.constant (f := fun x ↦ SignType.sign (f x))
    (fun z hz ↦ (continuousAt_sign_of_ne_zero (h0 z hz)).comp_continuousWithinAt (hf z hz)) hx hy

end TauCeti
