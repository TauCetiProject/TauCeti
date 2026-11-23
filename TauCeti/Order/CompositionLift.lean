/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Exact lifts of monotone compositions

Let `D : Set X` be a domain, `g : X → Y` an inner map into a preorder, `h : Y → β` an outer
function into a preorder and `b : β` a budget. The constraint `h (g x) ≤ b` on `D` cuts out the
original set

    S = {x ∈ D | h (g x) ≤ b}.

Introducing an auxiliary upper height `y` for `g x`, ranging over an outer domain `E : Set Y`,
gives the lifted set

    L = {(x, y) | x ∈ D, y ∈ E, g x ≤ y, h y ≤ b}.

If `g` maps `D` into `E` and `h` is monotone on `E`, then `L` projects exactly onto `S`: the graph
point `(x, g x)` lifts a point of `S`, and monotonicity of `h` pushes a point of `L` back down to
`S`. Convexity, differentiability and compactness play no role in this identity; it is the order
form of the monotone-outer epigraph reformulation used in convex mixed-integer programming, where
`L` replaces the nonlinear constraint `h (g x) ≤ b` by the simpler constraints `g x ≤ y` and
`h y ≤ b`.

Objectives that only see the original variables are then optimised equally well on `S` and on
`L`: they take the same set of values, a point of `L` is a minimiser there exactly when its
projection is a minimiser on `S`, and a minimiser exists on one set exactly when it exists on the
other. Membership is stated separately from Mathlib's `IsMinOn`, which does not assert it.

## Main declarations

* `TauCeti.CompositionLift.originalSet`, `TauCeti.CompositionLift.liftedSet`: the sets `S`
  and `L` above.
* `TauCeti.CompositionLift.fst_image_liftedSet`: the projection of `L` is `S`.
* `TauCeti.CompositionLift.epigraph_comp_eq`: the epigraph of `h ∘ g` on `D` consists of the
  pairs `(x, t)` admitting a height `y` with `(x, y)` in the lift at budget `t`.
* `TauCeti.CompositionLift.isMinOn_comp_fst_liftedSet_iff`: a point of `L` minimises
  `f ∘ Prod.fst` on `L` if and only if its projection minimises `f` on `S`.
* `TauCeti.CompositionLift.exists_isMinOn_liftedSet_iff`: attainment of the minimum transfers in
  both directions.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Math. Program. 103 (2005), 225–249, §2, Proposition 1.
* M. Lubin, E. Yamangil, R. Bent and J. P. Vielma, *Extended formulations in mixed-integer
  convex programming*, IPCO 2016, arXiv:1511.06710v3, §4.
-/

public section

open Set

namespace TauCeti.CompositionLift

variable {X Y β γ : Type*} [Preorder β]

/-- The points of the domain `D` satisfying the composed constraint `h (g x) ≤ b`. -/
def originalSet (D : Set X) (g : X → Y) (h : Y → β) (b : β) : Set X :=
  {x | x ∈ D ∧ h (g x) ≤ b}

@[simp]
theorem mem_originalSet {D : Set X} {g : X → Y} {h : Y → β} {b : β} {x : X} :
    x ∈ originalSet D g h b ↔ x ∈ D ∧ h (g x) ≤ b :=
  Iff.rfl

/-- The original set retains the domain constraint. -/
theorem originalSet_subset (D : Set X) (g : X → Y) (h : Y → β) (b : β) :
    originalSet D g h b ⊆ D :=
  fun _ hx => hx.1

variable [Preorder Y]

/-- The pairs `(x, y)` with `x` in the domain `D`, `y` an upper height for `g x` in the outer
domain `E`, and `y` satisfying the outer constraint `h y ≤ b`. -/
def liftedSet (D : Set X) (E : Set Y) (g : X → Y) (h : Y → β) (b : β) : Set (X × Y) :=
  {p | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b}

variable {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}

@[simp]
theorem mem_liftedSet {p : X × Y} :
    p ∈ liftedSet D E g h b ↔ p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b :=
  Iff.rfl

/-- Graph insertion: a point of the original set lifts to the lifted set with height `g x`.
Monotonicity of `h` is not needed for this direction. -/
theorem mk_mem_liftedSet_of_mem_originalSet (hg : MapsTo g D E) {x : X}
    (hx : x ∈ originalSet D g h b) : (x, g x) ∈ liftedSet D E g h b :=
  ⟨hx.1, hg hx.1, le_rfl, hx.2⟩

/-- Projection: the first coordinate of a point of the lifted set lies in the original set. -/
theorem fst_mem_originalSet_of_mem_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E)
    {p : X × Y} (hp : p ∈ liftedSet D E g h b) : p.1 ∈ originalSet D g h b :=
  ⟨hp.1, (hm (hg hp.1) hp.2.1 hp.2.2.1).trans hp.2.2.2⟩

/-- Pointwise form of the exact projection: `x` admits a height in the lifted set if and only if
it lies in the original set. -/
theorem exists_mem_liftedSet_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) {x : X} :
    (∃ y, (x, y) ∈ liftedSet D E g h b) ↔ x ∈ originalSet D g h b :=
  ⟨fun ⟨_, hy⟩ => fst_mem_originalSet_of_mem_liftedSet hg hm hy,
    fun hx => ⟨g x, mk_mem_liftedSet_of_mem_originalSet hg hx⟩⟩

/-- **Exact projection.** If `g` maps `D` into `E` and `h` is monotone on `E`, the lifted set
projects onto the original set. -/
theorem fst_image_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    Prod.fst '' liftedSet D E g h b = originalSet D g h b := by
  ext x
  simpa only [mem_image, Prod.exists, exists_and_right, exists_eq_right] using
    exists_mem_liftedSet_iff hg hm

/-- The lifted set is nonempty exactly when the original set is. -/
theorem liftedSet_nonempty_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    (liftedSet D E g h b).Nonempty ↔ (originalSet D g h b).Nonempty := by
  rw [← fst_image_liftedSet hg hm, image_nonempty]

/-- The lifted set is empty exactly when the original set is. -/
theorem liftedSet_eq_empty_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    liftedSet D E g h b = ∅ ↔ originalSet D g h b = ∅ := by
  rw [← fst_image_liftedSet hg hm, image_eq_empty]

/-- **Epigraph criterion.** The epigraph `{(x, t) | x ∈ D, h (g x) ≤ t}` of `h ∘ g` on `D`, in the
form used by `convexOn_iff_convex_epigraph`, consists of the pairs `(x, t)` for which some height
`y ∈ E` satisfies `g x ≤ y` and `h y ≤ t`. -/
theorem epigraph_comp_eq (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    {p : X × β | p.1 ∈ D ∧ h (g p.1) ≤ p.2} = {p | ∃ y, (p.1, y) ∈ liftedSet D E g h p.2} := by
  ext p
  exact (exists_mem_liftedSet_iff hg hm).symm

/-- An objective pulled back from the original variables takes the same values on the lifted set
as on the original set. In particular both problems have the same lower bounds and the same
infimum. -/
theorem image_comp_fst_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) (f : X → γ) :
    (f ∘ Prod.fst) '' liftedSet D E g h b = f '' originalSet D g h b := by
  rw [image_comp, fst_image_liftedSet hg hm]

/-- **Feasible minima.** A pair `p` minimises an objective pulled back from the original variables
on the lifted set if and only if its projection minimises the objective on the original set.
Since `IsMinOn` does not assert membership, this holds for every pair; together with
`fst_mem_originalSet_of_mem_liftedSet` it transports feasible minima from `L` to `S`. -/
theorem isMinOn_comp_fst_liftedSet_iff [Preorder γ] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → γ) (p : X × Y) :
    IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p ↔ IsMinOn f (originalSet D g h b) p.1 :=
  ⟨fun hmin => isMinOn_iff.2 fun _ hx =>
      isMinOn_iff.1 hmin _ (mk_mem_liftedSet_of_mem_originalSet hg hx),
    fun hmin => hmin.comp_of_mapsTo (fun _ hq => fst_mem_originalSet_of_mem_liftedSet hg hm hq)
      rfl⟩

/-- **Attainment.** An objective pulled back from the original variables attains its minimum on
the lifted set if and only if it attains its minimum on the original set. -/
theorem exists_isMinOn_liftedSet_iff [Preorder γ] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → γ) :
    (∃ p ∈ liftedSet D E g h b, IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) ↔
      ∃ x ∈ originalSet D g h b, IsMinOn f (originalSet D g h b) x := by
  constructor
  · rintro ⟨p, hp, hmin⟩
    exact ⟨p.1, fst_mem_originalSet_of_mem_liftedSet hg hm hp,
      (isMinOn_comp_fst_liftedSet_iff hg hm f p).1 hmin⟩
  · rintro ⟨x, hx, hmin⟩
    have hgx := mk_mem_liftedSet_of_mem_originalSet hg hx
    exact ⟨(x, g x), hgx, (isMinOn_comp_fst_liftedSet_iff hg hm f (x, g x)).2 hmin⟩

end TauCeti.CompositionLift
