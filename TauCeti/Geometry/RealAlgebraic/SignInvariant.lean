/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Sign
import TauCeti.Topology.LocallyConstant.Preconnected

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

A set on which each function of a family is sign-invariant lies inside or outside each set
described by a condition on their signs. If the sets of a cover each have this property, one sample
point from each of them realizes every sign vector that the functions take.

## Main declarations

* `TauCeti.SignInvariant`: sign-invariance of a function on a set.
* `TauCeti.signInvariant_iff_exists`: a sign-invariant function has a single sign on the set.
* `TauCeti.signInvariant_image`: sign-invariance on an image is sign-invariance of the
  composite.
* `TauCeti.subset_or_disjoint_setOf_sign`: a set on which the functions are sign-invariant lies
  inside or outside each sign-condition set.
* `TauCeti.range_sign_sample_eq`: sample points of a cover by sets on which the functions are
  sign-invariant realize all their sign vectors.
* `IsPreconnected.signInvariant`: a continuous, nowhere-zero function on a preconnected set is
  sign-invariant.
* `IsPreconnected.signInvariant_of_eq_zero_iff`: a continuous function on a preconnected set that
  vanishes everywhere or nowhere there is sign-invariant.

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

/-! ### Sign conditions -/

section SignCondition

variable {ι : Type*} {f : ι → α → R}

/-- If each function `f i` is sign-invariant on `t`, then `t` lies inside or outside every set
described by a condition on the signs of the `f i`. -/
theorem subset_or_disjoint_setOf_sign (hf : ∀ i, SignInvariant (f i) t)
    (Φ : (ι → SignType) → Prop) :
    t ⊆ {x | Φ fun i ↦ SignType.sign (f i x)} ∨
      Disjoint t {x | Φ fun i ↦ SignType.sign (f i x)} := by
  by_cases h : ∃ x ∈ t, Φ fun i ↦ SignType.sign (f i x)
  · obtain ⟨x, hx, hΦ⟩ := h
    refine .inl fun y hy ↦ ?_
    rwa [mem_ofPred_eq, funext fun i ↦ hf i y hy x hx]
  · exact .inr <| disjoint_left.2 fun x hx hΦ ↦ h ⟨x, hx, hΦ⟩

/-- **Sample points realize all sign conditions.** Let the functions `f i` be sign-invariant on
each set of a family `𝒞` covering `α`, and pick a sample point `x E` in each `E ∈ 𝒞`. Then the
sign vectors of the `f i` at the sample points are exactly the sign vectors they take on `α`. -/
theorem range_sign_sample_eq {𝒞 : Set (Set α)} (h𝒞 : ⋃₀ 𝒞 = univ)
    (hf : ∀ i, ∀ E ∈ 𝒞, SignInvariant (f i) E) (x : 𝒞 → α) (hx : ∀ E : 𝒞, x E ∈ (E : Set α)) :
    (range fun E i ↦ SignType.sign (f i (x E))) = range fun y i ↦ SignType.sign (f i y) := by
  refine (range_comp_subset_range x fun y i ↦ SignType.sign (f i y)).antisymm ?_
  rintro _ ⟨y, rfl⟩
  obtain ⟨E, hE, hy⟩ := mem_sUnion.1 (h𝒞 ▸ mem_univ y)
  exact ⟨⟨E, hE⟩, funext fun i ↦ hf i E hE _ (hx ⟨E, hE⟩) y hy⟩

end SignCondition

end Preorder

/-- A function that is continuous and nowhere zero on a preconnected set is sign-invariant
there. -/
theorem _root_.IsPreconnected.signInvariant [Zero R] [LinearOrder R] [TopologicalSpace R]
    [OrderTopology R] [TopologicalSpace α] {f : α → R} {s : Set α} (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) : SignInvariant f s :=
  fun _ hx _ hy ↦ hs.constant (f := fun x ↦ SignType.sign (f x))
    (fun z hz ↦ (continuousAt_sign_of_ne_zero (h0 z hz)).comp_continuousWithinAt (hf z hz)) hx hy

/-- A function that is continuous on a preconnected set, and vanishes either at every point of
the set or at none, is sign-invariant there. -/
theorem _root_.IsPreconnected.signInvariant_of_eq_zero_iff [Zero R] [LinearOrder R]
    [TopologicalSpace R] [OrderTopology R] [TopologicalSpace α] {f : α → R} {s : Set α}
    (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (h0 : ∀ x ∈ s, ∀ y ∈ s, f x = 0 ↔ f y = 0) : SignInvariant f s := by
  intro x hx y hy
  by_cases hfx : f x = 0
  · rw [hfx, (h0 x hx y hy).1 hfx]
  · exact hs.signInvariant hf (fun z hz hfz ↦ hfx ((h0 x hx z hz).2 hfz)) x hx y hy

/-- Local sign-invariance on relative neighborhoods implies sign-invariance on a preconnected
set. No continuity of the function itself is required. -/
theorem _root_.IsPreconnected.signInvariant_of_locally [Zero R] [Preorder R] [DecidableLT R]
    [TopologicalSpace α] {f : α → R} {s : Set α} (hs : IsPreconnected s)
    (hlocal : ∀ x ∈ s, ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ SignInvariant f (s ∩ U)) :
    SignInvariant f s := by
  rw [signInvariant_def]
  refine fun x hx y hy ↦ hs.apply_eq_of_eventually_eq
    (f := fun a ↦ SignType.sign (f a)) (fun a ha ↦ ?_) hx hy
  obtain ⟨U, hU, haU, h⟩ := hlocal a ha
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds haU)] with b hb hbU
  exact h b ⟨hb, hbU⟩ a ⟨ha, haU⟩

end TauCeti
