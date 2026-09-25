/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# The homotopy extension property

A subset `A` of a topological space `X` has the *homotopy extension property* when a homotopy of
maps out of `A` can be extended over `X` as soon as its initial map extends: given `f : C(X, Y)`
and `H : C(I × A, Y)` with `H (0, a) = f a` for every `a ∈ A`, there is a homotopy
`G : C(I × X, Y)` with `G (0, x) = f x` and `G (t, a) = H (t, a)`.  In this situation the
inclusion of `A` into `X` is a cofibration, and it is a *closed* cofibration as soon as `X` is
Hausdorff, because the property then forces `A` to be closed.

For closed `A` the property is equivalent to a purely geometric statement: the subspace
`X × {0} ∪ A × I` of the cylinder `I × X` is a retract of the whole cylinder.  This is how the
property is verified in practice, and it is also what frees it from the universe the target
space `Y` is taken in: the definition below quantifies over targets in the universe of `X`, and
`TauCeti.HasHomotopyExtensionProperty.exists_homotopy` upgrades a closed subset with that
property to one that extends homotopies with values in a space in any universe.

## Main declarations

* `TauCeti.cylinderBase`: the subspace `X × {0} ∪ A × I` of the cylinder `I × X`.
* `TauCeti.HasHomotopyExtensionProperty`: the homotopy extension property of a subset.
* `TauCeti.hasHomotopyExtensionProperty_iff_exists_retraction`: **a closed subset has the
  homotopy extension property exactly when `X × {0} ∪ A × I` is a retract of `I × X`.**
* `TauCeti.HasHomotopyExtensionProperty.exists_homotopy` and
  `TauCeti.HasHomotopyExtensionProperty.exists_homotopy_of_restrict`: extension of homotopies
  with values in a space in an arbitrary universe, in terms of raw maps and of Mathlib's bundled
  homotopies.
* `TauCeti.HasHomotopyExtensionProperty.isClosed`: in a Hausdorff space the property forces the
  subset to be closed, so the inclusion is a closed cofibration.
* `TauCeti.HasHomotopyExtensionProperty.image`: transport of the property along a homeomorphism.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Proposition 0.16.
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.
-/

public section

namespace TauCeti

open Set unitInterval

universe u u' v

variable {X : Type u} [TopologicalSpace X] {A : Set X}

/-- The subspace `X × {0} ∪ A × I` of the cylinder `I × X`: the bottom of the cylinder together
with the part of the cylinder lying over `A`.  A homotopy extension problem for `A ⊆ X` is
exactly the problem of extending a map defined on this subspace over the whole cylinder. -/
def cylinderBase (A : Set X) : Set (I × X) := {p | p.1 = 0 ∨ p.2 ∈ A}

omit [TopologicalSpace X] in
@[simp]
lemma mem_cylinderBase_iff {p : I × X} : p ∈ cylinderBase A ↔ p.1 = 0 ∨ p.2 ∈ A := Iff.rfl

omit [TopologicalSpace X] in
lemma zero_mem_cylinderBase (x : X) : ((0 : I), x) ∈ cylinderBase A := Or.inl rfl

omit [TopologicalSpace X] in
lemma mem_cylinderBase_of_mem {t : I} {x : X} (hx : x ∈ A) : (t, x) ∈ cylinderBase A := Or.inr hx

lemma isClosed_cylinderBase (hA : IsClosed A) : IsClosed (cylinderBase A) :=
  ((isClosed_singleton (x := (0 : I))).preimage continuous_fst).union (hA.preimage continuous_snd)

/-- A subset `A` of `X` has the *homotopy extension property* when every homotopy of maps out of
`A` whose initial map extends to `X` is itself the restriction of a homotopy of maps out of `X`.

Only targets `Y` in the universe of `X` are quantified over here.  For a closed subset this is
no restriction: `TauCeti.HasHomotopyExtensionProperty.exists_homotopy` then extends homotopies
with values in a space in an arbitrary universe. -/
def HasHomotopyExtensionProperty (A : Set X) : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (H : C(I × A, Y)),
    (∀ a : A, H (0, a) = f a) →
      ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a)

/-- A retraction of the cylinder `I × X` onto `X × {0} ∪ A × I` solves every homotopy extension
problem for a closed subset `A ⊆ X`, with values in a space in any universe. -/
theorem exists_homotopy_of_retraction {Y : Type v} [TopologicalSpace Y] (hA : IsClosed A)
    {r : C(I × X, I × X)} (hr : ∀ p, r p ∈ cylinderBase A) (hr' : ∀ p ∈ cylinderBase A, r p = p)
    (f : C(X, Y)) (H : C(I × A, Y)) (hH : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) := by
  classical
  refine ⟨⟨fun p => if h : (r p).2 ∈ A then H ((r p).1, ⟨(r p).2, h⟩) else f (r p).2, ?_⟩,
    fun x => ?_, fun t a => ?_⟩
  · -- The two closed sets where the two branches are used cover the cylinder, so it suffices to
    -- see that each branch is continuous on its own set.
    have hcover : {p : I × X | (r p).2 ∈ A} ∪ {p : I × X | (r p).1 = 0} = univ := by
      ext p
      simpa [or_comm] using hr p
    rw [← continuousOn_univ, ← hcover]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (hA.preimage r.continuous.snd)
      ((isClosed_singleton (x := (0 : I))).preimage r.continuous.fst)
    · rw [continuousOn_iff_continuous_domRestrict]
      have key : Set.domRestrict {p : I × X | (r p).2 ∈ A}
          (fun p : I × X => if h : (r p).2 ∈ A then H ((r p).1, ⟨(r p).2, h⟩) else f (r p).2) =
            fun p : {p : I × X | (r p).2 ∈ A} =>
              H ((r p.1).1, ⟨(r p.1).2, p.2⟩) :=
        funext fun p => dite_eq_left p.2
      rw [key]
      exact H.continuous.comp (((r.continuous.comp continuous_subtype_val).fst).prodMk
        (((r.continuous.comp continuous_subtype_val).snd).subtype_mk _))
    · rw [continuousOn_iff_continuous_domRestrict]
      have key : Set.domRestrict {p : I × X | (r p).1 = 0}
          (fun p : I × X => if h : (r p).2 ∈ A then H ((r p).1, ⟨(r p).2, h⟩) else f (r p).2) =
            fun p : {p : I × X | (r p).1 = 0} => f (r p.1).2 := by
        refine funext fun p => ?_
        have hp : (r p.1).1 = 0 := p.2
        by_cases h : (r p.1).2 ∈ A
        · have hbranch : Set.domRestrict {p : I × X | (r p).1 = 0}
              (fun p : I × X =>
                if h : (r p).2 ∈ A then H ((r p).1, ⟨(r p).2, h⟩) else f (r p).2) p =
              H ((r p.1).1, ⟨(r p.1).2, h⟩) := dite_eq_left h
          rw [hbranch, hp]
          exact hH ⟨_, h⟩
        · exact dite_eq_right h
      rw [key]
      exact f.continuous.comp ((r.continuous.comp continuous_subtype_val).snd)
  · simp only [ContinuousMap.coe_mk, hr' _ (zero_mem_cylinderBase x)]
    split_ifs with h
    · exact hH ⟨x, h⟩
    · rfl
  · simp only [ContinuousMap.coe_mk, hr' _ (mem_cylinderBase_of_mem a.2)]
    rw [dite_eq_left a.2]

/-- A closed subset onto whose cylinder base the cylinder retracts has the homotopy extension
property. -/
theorem hasHomotopyExtensionProperty_of_retraction (hA : IsClosed A) {r : C(I × X, I × X)}
    (hr : ∀ p, r p ∈ cylinderBase A) (hr' : ∀ p ∈ cylinderBase A, r p = p) :
    HasHomotopyExtensionProperty A :=
  fun f H hH => exists_homotopy_of_retraction hA hr hr' f H hH

/-- Solving the universal homotopy extension problem, the one whose target is the subspace
`X × {0} ∪ A × I` itself, produces a retraction of the cylinder onto that subspace. -/
theorem HasHomotopyExtensionProperty.exists_retraction (h : HasHomotopyExtensionProperty A) :
    ∃ r : C(I × X, I × X), (∀ p, r p ∈ cylinderBase A) ∧ ∀ p ∈ cylinderBase A, r p = p := by
  obtain ⟨G, hG₀, hG₁⟩ :=
    h (Y := cylinderBase A)
      ⟨fun x => ⟨((0 : I), x), zero_mem_cylinderBase x⟩, by fun_prop⟩
      ⟨fun q => ⟨(q.1, (q.2 : X)), mem_cylinderBase_of_mem q.2.2⟩, by fun_prop⟩
      (fun _ => rfl)
  refine ⟨⟨fun p => (G p : I × X), continuous_subtype_val.comp G.continuous⟩,
    fun p => (G p).2, ?_⟩
  rintro ⟨t, x⟩ (h0 | hx)
  · rw [show t = 0 from h0]
    exact congrArg Subtype.val (hG₀ x)
  · exact congrArg Subtype.val (hG₁ t ⟨x, hx⟩)

/-- **A closed subset has the homotopy extension property exactly when the subspace
`X × {0} ∪ A × I` is a retract of the cylinder `I × X`.** -/
theorem hasHomotopyExtensionProperty_iff_exists_retraction (hA : IsClosed A) :
    HasHomotopyExtensionProperty A ↔
      ∃ r : C(I × X, I × X), (∀ p, r p ∈ cylinderBase A) ∧ ∀ p ∈ cylinderBase A, r p = p :=
  ⟨fun h => h.exists_retraction,
    fun ⟨_, hr, hr'⟩ => hasHomotopyExtensionProperty_of_retraction hA hr hr'⟩

/-- The homotopy extension property extends homotopies with values in a space in an arbitrary
universe, not only in the universe of `X`. -/
theorem HasHomotopyExtensionProperty.exists_homotopy (hA : IsClosed A)
    (h : HasHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (H : C(I × A, Y)) (hH : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  let ⟨_, hr, hr'⟩ := h.exists_retraction
  exists_homotopy_of_retraction hA hr hr' f H hH

/-- The homotopy extension property in terms of bundled homotopies: a homotopy starting at the
restriction of `f : C(X, Y)` to `A` is the restriction of a homotopy starting at `f`. -/
theorem HasHomotopyExtensionProperty.exists_homotopy_of_restrict (hA : IsClosed A)
    (h : HasHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    {g : C(A, Y)} (H : (f.restrict A).Homotopy g) :
    ∃ (f' : C(X, Y)) (G : f.Homotopy f'), ∀ (t : I) (a : A), G (t, (a : X)) = H (t, a) := by
  obtain ⟨G, hG₀, hG₁⟩ := h.exists_homotopy hA f H.toContinuousMap fun a => H.apply_zero a
  exact ⟨⟨fun x => G (1, x), by fun_prop⟩,
    { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ => rfl }, hG₁⟩

/-- In a Hausdorff space, a subset with the homotopy extension property is closed, so the
inclusion of such a subset is a closed cofibration. -/
theorem HasHomotopyExtensionProperty.isClosed [T2Space X] (h : HasHomotopyExtensionProperty A) :
    IsClosed A := by
  obtain ⟨r, hr, hr'⟩ := h.exists_retraction
  have hfix : cylinderBase A = {p : I × X | r p = p} := by
    ext p
    exact ⟨hr' p, fun hp => hp ▸ hr p⟩
  have hcl : IsClosed (cylinderBase A) := hfix ▸ isClosed_eq r.continuous continuous_id
  have hpre : A = (fun x : X => ((1 : I), x)) ⁻¹' cylinderBase A := by
    ext x
    simp [show (1 : I) ≠ 0 from fun h => one_ne_zero (congrArg Subtype.val h)]
  exact hpre ▸ hcl.preimage (by fun_prop)

/-- The homotopy extension property transports along a homeomorphism; the two spaces need not
live in the same universe. -/
theorem HasHomotopyExtensionProperty.image {X' : Type u'} [TopologicalSpace X']
    (h : HasHomotopyExtensionProperty A) (e : X ≃ₜ X') (hA : IsClosed A) :
    HasHomotopyExtensionProperty (e '' A) := by
  obtain ⟨r, hr, hr'⟩ := h.exists_retraction
  refine hasHomotopyExtensionProperty_of_retraction (e.isClosedMap A hA)
    (r := ⟨fun q => ((r (q.1, e.symm q.2)).1, e (r (q.1, e.symm q.2)).2), by fun_prop⟩)
    (fun q => ?_) (fun q hq => ?_)
  · obtain h0 | hmem := hr (q.1, e.symm q.2)
    · exact Or.inl h0
    · exact Or.inr (mem_image_of_mem e hmem)
  · have hq' : (q.1, e.symm q.2) ∈ cylinderBase A := by
      obtain h0 | ⟨a, ha, hae⟩ := hq
      · exact Or.inl h0
      · exact Or.inr (by rw [← hae, e.symm_apply_apply]; exact ha)
    simp [hr' _ hq']

end TauCeti
