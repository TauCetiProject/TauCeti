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
`{0} × X ∪ I × A` of the cylinder `I × X` is a retract of the whole cylinder.  This is how the
property is verified in practice, and it is also what frees it from the universe the target
space `Y` is taken in: the definition below quantifies over targets in the universe of `X`, and
`TauCeti.HasHomotopyExtensionProperty.exists_extension_of_isClosed` upgrades a closed subset
with that property to one that extends homotopies with values in a space in any universe.

## Main declarations

* `TauCeti.cylinderExtensionDomain`: the subspace `{0} × X ∪ I × A` of the cylinder `I × X`, the
  domain of the initial data of a homotopy extension problem.
* `TauCeti.HasHomotopyExtensionProperty`: the homotopy extension property of a subset, together
  with `TauCeti.hasHomotopyExtensionProperty_iff` and
  `TauCeti.HasHomotopyExtensionProperty.exists_extension` restating it.
* `TauCeti.hasHomotopyExtensionProperty_iff_exists_retraction`: **a closed subset has the
  homotopy extension property exactly when `{0} × X ∪ I × A` is a retract of `I × X`.**
* `TauCeti.HasHomotopyExtensionProperty.exists_extension_of_isClosed` and
  `TauCeti.HasHomotopyExtensionProperty.exists_homotopy_of_restrict`: for a closed subset,
  extension of homotopies with values in a space in an arbitrary universe, in terms of raw maps
  and of Mathlib's bundled homotopies.
* `TauCeti.HasHomotopyExtensionProperty.isClosed`: in a Hausdorff space the property forces the
  subset to be closed, so the inclusion is a closed cofibration.
* `TauCeti.HasHomotopyExtensionProperty.image`: transport of the property for a closed subset
  along a homeomorphism.

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

/-- The subspace `{0} × X ∪ I × A` of the cylinder `I × X`: the bottom of the cylinder together
with the part of the cylinder lying over `A`.  For closed `A`, a homotopy extension problem for
`A ⊆ X` is exactly the problem of extending a map defined on this subspace over the whole
cylinder; the closedness is what lets the two pieces of initial data be glued into a single
continuous map on the union. -/
def cylinderExtensionDomain (A : Set X) : Set (I × X) := {p | p.1 = 0 ∨ p.2 ∈ A}

omit [TopologicalSpace X] in
@[simp]
lemma mem_cylinderExtensionDomain_iff {p : I × X} :
    p ∈ cylinderExtensionDomain A ↔ p.1 = 0 ∨ p.2 ∈ A := Iff.rfl

omit [TopologicalSpace X] in
lemma zero_mem_cylinderExtensionDomain (x : X) : ((0 : I), x) ∈ cylinderExtensionDomain A :=
  Or.inl rfl

omit [TopologicalSpace X] in
lemma mem_cylinderExtensionDomain_of_mem {t : I} {x : X} (hx : x ∈ A) :
    (t, x) ∈ cylinderExtensionDomain A := Or.inr hx

lemma isClosed_cylinderExtensionDomain (hA : IsClosed A) :
    IsClosed (cylinderExtensionDomain A) :=
  ((isClosed_singleton (x := (0 : I))).preimage continuous_fst).union (hA.preimage continuous_snd)

/-- A subset `A` of `X` has the *homotopy extension property* when every homotopy of maps out of
`A` whose initial map extends to `X` is itself the restriction of a homotopy of maps out of `X`.

Only targets `Y` in the universe of `X` are quantified over here.  For a closed subset this is
no restriction: `TauCeti.HasHomotopyExtensionProperty.exists_extension_of_isClosed` then
extends homotopies with values in a space in an arbitrary universe. -/
def HasHomotopyExtensionProperty (A : Set X) : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (H : C(I × A, Y)),
    (∀ a : A, H (0, a) = f a) →
      ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a)

/-- Unfolding of `TauCeti.HasHomotopyExtensionProperty`, so that the property can be proved and
used in modules that only import this one. -/
theorem hasHomotopyExtensionProperty_iff :
    HasHomotopyExtensionProperty A ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (H : C(I × A, Y)),
        (∀ a : A, H (0, a) = f a) →
          ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  Iff.rfl

/-- The defining consequence of the homotopy extension property: a homotopy out of `A` whose
initial map extends to `X` extends to a homotopy out of `X`. -/
theorem HasHomotopyExtensionProperty.exists_extension (h : HasHomotopyExtensionProperty A)
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (H : C(I × A, Y))
    (hH : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  h f H hH

section Glue

variable {Y : Type v} [TopologicalSpace Y] [DecidablePred (· ∈ A)] {r : C(I × X, I × X)}
  {f : C(X, Y)} {H : C(I × A, Y)}

/-- The candidate solution of the homotopy extension problem `(f, H)` built from a retraction `r`
of the cylinder onto `cylinderExtensionDomain A`: where `r` lands over `A` read off the homotopy
`H`, and elsewhere read off `f`, which is what the value at time `0` is forced to be. -/
private def glueAlongRetraction (r : C(I × X, I × X)) (f : C(X, Y)) (H : C(I × A, Y))
    (p : I × X) : Y :=
  if h : (r p).2 ∈ A then H ((r p).1, ⟨(r p).2, h⟩) else f (r p).2

private lemma glueAlongRetraction_of_mem {p : I × X} (h : (r p).2 ∈ A) :
    glueAlongRetraction r f H p = H ((r p).1, ⟨(r p).2, h⟩) := dite_eq_left h

private lemma glueAlongRetraction_of_notMem {p : I × X} (h : (r p).2 ∉ A) :
    glueAlongRetraction r f H p = f (r p).2 := dite_eq_right h

private lemma domRestrict_glueAlongRetraction_mem :
    Set.domRestrict {p : I × X | (r p).2 ∈ A} (glueAlongRetraction r f H) =
      fun p : {p : I × X | (r p).2 ∈ A} => H ((r p.1).1, ⟨(r p.1).2, p.2⟩) := by
  refine funext fun p => ?_
  have hp : (r p.1).2 ∈ A := p.2
  rw [Set.domRestrict_apply, glueAlongRetraction_of_mem hp]

private lemma domRestrict_glueAlongRetraction_zero (hH : ∀ a : A, H (0, a) = f a) :
    Set.domRestrict {p : I × X | (r p).1 = 0} (glueAlongRetraction r f H) =
      fun p : {p : I × X | (r p).1 = 0} => f (r p.1).2 := by
  refine funext fun p => ?_
  have hp : (r p.1).1 = 0 := p.2
  rw [Set.domRestrict_apply]
  by_cases h : (r p.1).2 ∈ A
  · rw [glueAlongRetraction_of_mem h, hp]
    exact hH ⟨_, h⟩
  · rw [glueAlongRetraction_of_notMem h]

private lemma continuous_glueAlongRetraction (hA : IsClosed A)
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A) (hH : ∀ a : A, H (0, a) = f a) :
    Continuous (glueAlongRetraction r f H) := by
  -- The two closed sets where the two branches are used cover the cylinder, so it suffices to
  -- see that each branch is continuous on its own set.
  have hcover : {p : I × X | (r p).2 ∈ A} ∪ {p : I × X | (r p).1 = 0} = univ := by
    ext p
    simpa [or_comm] using hr p
  rw [← continuousOn_univ, ← hcover]
  refine ContinuousOn.union_of_isClosed ?_ ?_ (hA.preimage r.continuous.snd)
    ((isClosed_singleton (x := (0 : I))).preimage r.continuous.fst)
  · rw [continuousOn_iff_continuous_domRestrict, domRestrict_glueAlongRetraction_mem]
    exact H.continuous.comp (((r.continuous.comp continuous_subtype_val).fst).prodMk
      (((r.continuous.comp continuous_subtype_val).snd).subtype_mk _))
  · rw [continuousOn_iff_continuous_domRestrict, domRestrict_glueAlongRetraction_zero hH]
    exact f.continuous.comp ((r.continuous.comp continuous_subtype_val).snd)

end Glue

/-- A retraction of the cylinder `I × X` onto `{0} × X ∪ I × A` solves every homotopy extension
problem for a closed subset `A ⊆ X`, with values in a space in any universe. -/
theorem exists_homotopy_extension_of_retraction {Y : Type v} [TopologicalSpace Y]
    (hA : IsClosed A) {r : C(I × X, I × X)} (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p)
    (f : C(X, Y)) (H : C(I × A, Y)) (hH : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) := by
  classical
  refine ⟨⟨glueAlongRetraction r f H, continuous_glueAlongRetraction hA hr hH⟩,
    fun x => ?_, fun t a => ?_⟩
  · simp only [ContinuousMap.coe_mk, glueAlongRetraction,
      hr' _ (zero_mem_cylinderExtensionDomain x)]
    split_ifs with h
    · exact hH ⟨x, h⟩
    · rfl
  · simp only [ContinuousMap.coe_mk, glueAlongRetraction,
      hr' _ (mem_cylinderExtensionDomain_of_mem a.2)]
    rw [dite_eq_left a.2]

/-- A closed subset onto whose cylinder extension domain the cylinder retracts has the homotopy
extension property. -/
theorem hasHomotopyExtensionProperty_of_retraction (hA : IsClosed A) {r : C(I × X, I × X)}
    (hr : ∀ p, r p ∈ cylinderExtensionDomain A)
    (hr' : ∀ p ∈ cylinderExtensionDomain A, r p = p) :
    HasHomotopyExtensionProperty A :=
  fun f H hH => exists_homotopy_extension_of_retraction hA hr hr' f H hH

/-- Solving the universal homotopy extension problem, the one whose target is the subspace
`{0} × X ∪ I × A` itself, produces a retraction of the cylinder onto that subspace. -/
theorem HasHomotopyExtensionProperty.exists_retraction (h : HasHomotopyExtensionProperty A) :
    ∃ r : C(I × X, I × X), (∀ p, r p ∈ cylinderExtensionDomain A) ∧
      ∀ p ∈ cylinderExtensionDomain A, r p = p := by
  obtain ⟨G, hG₀, hG₁⟩ :=
    h (Y := cylinderExtensionDomain A)
      ⟨fun x => ⟨((0 : I), x), zero_mem_cylinderExtensionDomain x⟩, by fun_prop⟩
      ⟨fun q => ⟨(q.1, (q.2 : X)), mem_cylinderExtensionDomain_of_mem q.2.2⟩, by fun_prop⟩
      (fun _ => rfl)
  refine ⟨⟨fun p => (G p : I × X), continuous_subtype_val.comp G.continuous⟩,
    fun p => (G p).2, ?_⟩
  rintro ⟨t, x⟩ (h0 | hx)
  · rw [show t = 0 from h0]
    exact congrArg Subtype.val (hG₀ x)
  · exact congrArg Subtype.val (hG₁ t ⟨x, hx⟩)

/-- **A closed subset has the homotopy extension property exactly when the subspace
`{0} × X ∪ I × A` is a retract of the cylinder `I × X`.** -/
theorem hasHomotopyExtensionProperty_iff_exists_retraction (hA : IsClosed A) :
    HasHomotopyExtensionProperty A ↔
      ∃ r : C(I × X, I × X), (∀ p, r p ∈ cylinderExtensionDomain A) ∧
        ∀ p ∈ cylinderExtensionDomain A, r p = p :=
  ⟨fun h => h.exists_retraction,
    fun ⟨_, hr, hr'⟩ => hasHomotopyExtensionProperty_of_retraction hA hr hr'⟩

/-- For a closed subset, the homotopy extension property extends homotopies with values in a
space in an arbitrary universe, not only in the universe of `X`.  The closedness hypothesis is
what routes the argument through the retraction characterisation, which is universe-free. -/
theorem HasHomotopyExtensionProperty.exists_extension_of_isClosed (hA : IsClosed A)
    (h : HasHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    (H : C(I × A, Y)) (hH : ∀ a : A, H (0, a) = f a) :
    ∃ G : C(I × X, Y), (∀ x, G (0, x) = f x) ∧ ∀ (t : I) (a : A), G (t, a) = H (t, a) :=
  let ⟨_, hr, hr'⟩ := h.exists_retraction
  exists_homotopy_extension_of_retraction hA hr hr' f H hH

/-- For a closed subset, the homotopy extension property in terms of bundled homotopies: a
homotopy starting at the restriction of `f : C(X, Y)` to `A` is the restriction of a homotopy
starting at `f`.  As in `TauCeti.HasHomotopyExtensionProperty.exists_extension_of_isClosed`,
closedness lets `Y` live in any universe. -/
theorem HasHomotopyExtensionProperty.exists_homotopy_of_restrict (hA : IsClosed A)
    (h : HasHomotopyExtensionProperty A) {Y : Type v} [TopologicalSpace Y] (f : C(X, Y))
    {g : C(A, Y)} (H : (f.restrict A).Homotopy g) :
    ∃ (f' : C(X, Y)) (G : f.Homotopy f'), ∀ (t : I) (a : A), G (t, (a : X)) = H (t, a) := by
  obtain ⟨G, hG₀, hG₁⟩ :=
    h.exists_extension_of_isClosed hA f H.toContinuousMap fun a => H.apply_zero a
  exact ⟨⟨fun x => G (1, x), by fun_prop⟩,
    { toContinuousMap := G, map_zero_left := hG₀, map_one_left := fun _ => rfl }, hG₁⟩

/-- In a Hausdorff space, a subset with the homotopy extension property is closed, so the
inclusion of such a subset is a closed cofibration. -/
theorem HasHomotopyExtensionProperty.isClosed [T2Space X] (h : HasHomotopyExtensionProperty A) :
    IsClosed A := by
  obtain ⟨r, hr, hr'⟩ := h.exists_retraction
  have hleft : Function.LeftInverse
      (fun p : I × X => (⟨r p, hr p⟩ : cylinderExtensionDomain A)) Subtype.val :=
    fun q => Subtype.ext (hr' q q.2)
  have hcl : IsClosed (cylinderExtensionDomain A) := by
    rw [← Subtype.range_coe (s := cylinderExtensionDomain A)]
    exact hleft.isClosed_range (r.continuous.subtype_mk _) continuous_subtype_val
  have hpre : A = (fun x : X => ((1 : I), x)) ⁻¹' cylinderExtensionDomain A := by
    ext x
    simp [show (1 : I) ≠ 0 from fun h => one_ne_zero (congrArg Subtype.val h)]
  exact hpre ▸ hcl.preimage (by fun_prop)

/-- For a closed subset, the homotopy extension property transports along a homeomorphism; the
two spaces need not live in the same universe.  Closedness enters because the transport goes
through the retraction characterisation. -/
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
  · have hq' : (q.1, e.symm q.2) ∈ cylinderExtensionDomain A := by
      obtain h0 | ⟨a, ha, hae⟩ := hq
      · exact Or.inl h0
      · exact Or.inr (by rw [← hae, e.symm_apply_apply]; exact ha)
    simp [hr' _ hq']

end TauCeti
