/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Order.Filter.Extr
import TauCeti.Order.Filter.Extr

/-!
# Exact lifts of monotone compositions

For a domain `D : Set X`, an outer domain `E : Set Y` in a preordered type `Y`, an inner map
`g : X → Y`, an outer map `h : Y → β` into a preordered type `β`, and a budget `b : β`,
replacing the composed constraint `h (g x) ≤ b` on `D` by an auxiliary height variable `y ∈ E`
satisfying `g x ≤ y` and `h y ≤ b` defines the lifted set

    {(x, y) ∈ X × Y | x ∈ D ∧ y ∈ E ∧ g x ≤ y ∧ h y ≤ b}.

Whenever `g` maps `D` into `E` and `h` is monotone on `E`, projecting onto the original variable
recovers `{x ∈ D | h (g x) ≤ b}` exactly (`TauCeti.ConvexLifting.projection_eq`), with the
corresponding pointwise existential characterization
(`TauCeti.ConvexLifting.mem_originalSet_iff_exists_mem_liftedSet`), without requiring convexity,
differentiability, or compactness.
When `g` is convex on `D` and `h` is quasiconvex on `E` (in particular, when `h` is convex on `E`),
the lifted set is convex with no `MapsTo g D E` or monotonicity requirement
(`TauCeti.ConvexLifting.convex_liftedSet`). When additionally `h` is monotone on `E` and
`MapsTo g D E` holds, the original feasible set is also convex without requiring `g '' D` to be
convex (`TauCeti.ConvexLifting.convex_originalSet`).

Because any objective `f : X → α` lifted by pullback `f ∘ Prod.fst` is independent of the height
variable, feasible lower bounds, objective-value witnesses, feasible minimizers, and existence of
attained minima transfer identically between the lifted and original sets
(`TauCeti.ConvexLifting.feasible_minimum_iff`, `TauCeti.ConvexLifting.attainment_iff`).

## Main definitions

* `TauCeti.ConvexLifting.originalSet` — `{x ∈ D | h (g x) ≤ b}`.
* `TauCeti.ConvexLifting.liftedSet` — `{p : X × Y | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b}`.

## Main statements

* `TauCeti.ConvexLifting.projection_eq` — `Prod.fst '' liftedSet D E g h b = originalSet D g h b`
  under `MapsTo g D E` and `MonotoneOn h E`.
* `TauCeti.ConvexLifting.mem_originalSet_iff_exists_mem_liftedSet` — pointwise existential
  characterization of `originalSet` via `liftedSet`.
* `TauCeti.ConvexLifting.convex_liftedSet` — convexity of `liftedSet` assuming only
  `ConvexOn 𝕜 D g` and `QuasiconvexOn 𝕜 E h` (no `MapsTo` or monotonicity needed).
* `TauCeti.ConvexLifting.convex_originalSet` — convexity of `originalSet` under `ConvexOn 𝕜 D g`,
  `QuasiconvexOn 𝕜 E h`, `MapsTo g D E`, and `MonotoneOn h E`.
* `TauCeti.ConvexLifting.feasible_minimum_iff` and `TauCeti.ConvexLifting.attainment_iff` — exact
  transfer of feasible minima and attainment for any pullback objective `f ∘ Prod.fst`.

## References

* M. Tawarmalani and N. V. Sahinidis, *A polyhedral branch-and-cut approach to global
  optimization*, Mathematical Programming 103 (2005), 225–249, §2, Proposition 1, pp. 226–227.
* M. Lubin, E. Yamangil, R. Bent and J. P. Vielma, *Extended Formulations in Mixed-integer Convex
  Programming*, IPCO 2016, arXiv:1511.06710v3 §4, p. 9.
* M. Lubin, E. Yamangil, R. Bent and J. P. Vielma, *Polyhedral approximation in mixed-integer
  convex optimization*, Mathematical Programming 172 (2018), arXiv:1607.03566v2 §4, p. 12,
  Eqs. (8)–(10).
-/

public section

open Set

namespace TauCeti.ConvexLifting

section Defs

variable {X Y β : Type*}

/-- Points in the original domain `D` satisfying the composed inequality `h (g x) ≤ b`. -/
def originalSet [LE β] (D : Set X) (g : X → Y) (h : Y → β) (b : β) : Set X :=
  {x | x ∈ D ∧ h (g x) ≤ b}

/-- Pairs `(x, y)` with `x ∈ D`, admissible upper height `y ∈ E` satisfying `g x ≤ y`, and outer
constraint `h y ≤ b`. -/
def liftedSet [LE Y] [LE β] (D : Set X) (E : Set Y) (g : X → Y) (h : Y → β) (b : β) :
    Set (X × Y) :=
  {p | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b}

/-- Membership in `originalSet`. -/
@[simp]
theorem mem_originalSet_iff [LE β] {D : Set X} {g : X → Y} {h : Y → β} {b : β} {x : X} :
    x ∈ originalSet D g h b ↔ x ∈ D ∧ h (g x) ≤ b :=
  (Iff.rfl)

/-- Membership in `liftedSet`. -/
@[simp]
theorem mem_liftedSet_iff [LE Y] [LE β] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β}
    {b : β} {p : X × Y} :
    p ∈ liftedSet D E g h b ↔ p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b :=
  (Iff.rfl)

/-- Every point of `originalSet` lies in the original domain `D`. -/
theorem originalSet_subset_domain [LE β] (D : Set X) (g : X → Y) (h : Y → β) (b : β) :
    originalSet D g h b ⊆ D :=
  fun _ hx => hx.1

/-- Every point of `liftedSet` lies in the product domain `D ×ˢ E`. -/
theorem liftedSet_subset_prod [LE Y] [LE β] (D : Set X) (E : Set Y) (g : X → Y) (h : Y → β)
    (b : β) : liftedSet D E g h b ⊆ D ×ˢ E :=
  fun _ hp => ⟨hp.1, hp.2.1⟩

/-- The original set over an empty domain is empty. -/
@[simp]
theorem originalSet_empty [LE β] (g : X → Y) (h : Y → β) (b : β) :
    originalSet (∅ : Set X) g h b = ∅ := by
  ext x
  simp

/-- The lifted set over an empty original domain is empty. -/
@[simp]
theorem liftedSet_empty_left [LE Y] [LE β] (E : Set Y) (g : X → Y) (h : Y → β) (b : β) :
    liftedSet (∅ : Set X) E g h b = ∅ := by
  ext p
  simp

/-- The lifted set over an empty height domain is empty. -/
@[simp]
theorem liftedSet_empty_right [LE Y] [LE β] (D : Set X) (g : X → Y) (h : Y → β) (b : β) :
    liftedSet D (∅ : Set Y) g h b = ∅ := by
  ext p
  simp

end Defs

section GraphInsertion

variable {X Y β : Type*} [Preorder Y] [LE β]
variable {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}

/-- Inserting the canonical graph point `(x, g x)` lifts any point of `originalSet` into
`liftedSet`, provided `g` maps `D` into `E`. No monotonicity of `h` is needed. -/
theorem graph_mem_liftedSet (hg : MapsTo g D E) {x : X} (hx : x ∈ originalSet D g h b) :
    (x, g x) ∈ liftedSet D E g h b :=
  ⟨hx.1, hg hx.1, le_rfl, hx.2⟩

/-- The graph map `x ↦ (x, g x)` maps `originalSet` into `liftedSet`. -/
theorem mapsTo_graph_originalSet (hg : MapsTo g D E) :
    MapsTo (fun x => (x, g x)) (originalSet D g h b) (liftedSet D E g h b) :=
  fun _ hx => graph_mem_liftedSet hg hx

/-- Every originally feasible point lies in the projection of `liftedSet`, provided `g` maps `D`
into `E`. -/
theorem originalSet_subset_fst_image_liftedSet (hg : MapsTo g D E) :
    originalSet D g h b ⊆ Prod.fst '' liftedSet D E g h b :=
  fun x hx => ⟨(x, g x), graph_mem_liftedSet hg hx, rfl⟩

end GraphInsertion

section Projection

variable {X Y β : Type*} [Preorder Y] [Preorder β]
variable {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}

/-- Projecting a point of `liftedSet` lands in `originalSet`, using `MapsTo g D E` and
monotonicity of `h` on `E`. -/
theorem fst_mem_originalSet_of_mem_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E)
    {p : X × Y} (hp : p ∈ liftedSet D E g h b) : p.1 ∈ originalSet D g h b :=
  ⟨hp.1, (hm (hg hp.1) hp.2.1 hp.2.2.1).trans hp.2.2.2⟩

/-- First projection maps `liftedSet` into `originalSet`. -/
theorem mapsTo_fst_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    MapsTo Prod.fst (liftedSet D E g h b) (originalSet D g h b) :=
  fun _ hp => fst_mem_originalSet_of_mem_liftedSet hg hm hp

/-- The projection of `liftedSet` is contained in `originalSet`. -/
theorem fst_image_liftedSet_subset (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    Prod.fst '' liftedSet D E g h b ⊆ originalSet D g h b :=
  (mapsTo_fst_liftedSet hg hm).image_subset

/-- **Exact projection of a monotone-composition lift.** Under `MapsTo g D E` and `MonotoneOn h E`,
the first projection of `liftedSet D E g h b` equals `originalSet D g h b`. -/
theorem projection_eq (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    Prod.fst '' liftedSet D E g h b = originalSet D g h b :=
  Subset.antisymm (fst_image_liftedSet_subset hg hm) (originalSet_subset_fst_image_liftedSet hg)

/-- Pointwise existential characterization of `originalSet` via `liftedSet`. -/
theorem mem_originalSet_iff_exists_mem_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (x : X) : x ∈ originalSet D g h b ↔ ∃ y, (x, y) ∈ liftedSet D E g h b := by
  rw [← projection_eq (b := b) hg hm]
  constructor
  · rintro ⟨⟨x', y⟩, hp, rfl⟩
    exact ⟨y, hp⟩
  · rintro ⟨y, hp⟩
    exact ⟨(x, y), hp, rfl⟩

/-- `liftedSet` is nonempty if and only if `originalSet` is nonempty. -/
theorem liftedSet_nonempty_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    (liftedSet D E g h b).Nonempty ↔ (originalSet D g h b).Nonempty := by
  rw [← projection_eq (b := b) hg hm, image_nonempty]

/-- `liftedSet` is empty if and only if `originalSet` is empty. -/
theorem liftedSet_eq_empty_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) :
    liftedSet D E g h b = ∅ ↔ originalSet D g h b = ∅ := by
  rw [← projection_eq (b := b) hg hm, image_eq_empty]

end Projection

section Convex

variable {𝕜 X Y β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid Y] [PartialOrder Y]

/-- When `g` is convex on `D` and `h` is quasiconvex on `E` (in particular, when `h` is convex on
`E`, via `ConvexOn.quasiconvexOn`), the lifted set `liftedSet D E g h b` is convex. Neither
`MapsTo g D E` nor monotonicity of `h` is required here. -/
theorem convex_liftedSet [LE β] [IsOrderedAddMonoid Y] [Module 𝕜 Y] [PosSMulMono 𝕜 Y]
    {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}
    (hg : ConvexOn 𝕜 D g) (hh : QuasiconvexOn 𝕜 E h) : Convex 𝕜 (liftedSet D E g h b) := by
  have hEq :
      liftedSet D E g h b =
        {p : X × Y | p.1 ∈ D ∧ g p.1 ≤ p.2} ∩ ((univ : Set X) ×ˢ {y ∈ E | h y ≤ b}) := by
    ext p
    simp only [mem_liftedSet_iff, mem_inter_iff, mem_ofPred_eq, mem_prod, mem_univ, true_and]
    tauto
  rw [hEq]
  exact hg.convex_epigraph.inter (convex_univ.prod (hh b))

/-- When `g` is convex on `D`, `h` is quasiconvex and monotone on `E` (in particular, when `h` is
convex and monotone on `E`, via `ConvexOn.quasiconvexOn`), and `g` maps `D` into `E`, the original
feasible set `originalSet D g h b` is convex (even when `g '' D` itself is not convex). -/
theorem convex_originalSet [SMul 𝕜 Y] [Preorder β] {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β}
    {b : β} (hg : ConvexOn 𝕜 D g) (hh : QuasiconvexOn 𝕜 E h) (hDE : MapsTo g D E)
    (hm : MonotoneOn h E) : Convex 𝕜 (originalSet D g h b) := by
  intro x hx x' hx' a c ha hc hac
  have hcomb := hh b ⟨hDE hx.1, hx.2⟩ ⟨hDE hx'.1, hx'.2⟩ ha hc hac
  exact ⟨hg.1 hx.1 hx'.1 ha hc hac,
    (hm (hDE (hg.1 hx.1 hx'.1 ha hc hac)) hcomb.1 (hg.2 hx.1 hx'.1 ha hc hac)).trans hcomb.2⟩

end Convex

section Minima

variable {X Y β α : Type*} [Preorder Y]
variable {D : Set X} {E : Set Y} {g : X → Y} {h : Y → β} {b : β}

/-- A minimizer of `f ∘ Prod.fst` on `liftedSet` projects to a minimizer of `f` on `originalSet`.
Only `MapsTo g D E` is needed for this direction. -/
theorem isMinOn_originalSet_of_isMinOn_comp_fst [LE β] [Preorder α] (hg : MapsTo g D E)
    {f : X → α} {p : X × Y} (hmin : IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) :
    IsMinOn f (originalSet D g h b) p.1 := by
  rw [isMinOn_iff] at hmin ⊢
  intro x hx
  exact hmin (x, g x) (graph_mem_liftedSet hg hx)

variable [Preorder β]

/-- The set of feasible objective values of `f ∘ Prod.fst` on `liftedSet` coincides with the set
of feasible objective values of `f` on `originalSet`. -/
theorem image_comp_fst_liftedSet (hg : MapsTo g D E) (hm : MonotoneOn h E) (f : X → α) :
    (f ∘ Prod.fst) '' liftedSet D E g h b = f '' originalSet D g h b := by
  rw [image_comp, projection_eq hg hm]

/-- Lower bounds on `f` transfer identically between `liftedSet` and `originalSet`. -/
theorem forall_mem_liftedSet_le_apply_iff [LE α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) (c : α) :
    (∀ p ∈ liftedSet D E g h b, c ≤ f p.1) ↔ ∀ x ∈ originalSet D g h b, c ≤ f x := by
  rw [← projection_eq (b := b) hg hm, forall_mem_image]

/-- Existence of a feasible point with objective value at most `c` transfers identically between
`liftedSet` and `originalSet`. -/
theorem exists_mem_liftedSet_apply_le_iff [LE α] (hg : MapsTo g D E) (hm : MonotoneOn h E)
    (f : X → α) (c : α) :
    (∃ p ∈ liftedSet D E g h b, f p.1 ≤ c) ↔ ∃ x ∈ originalSet D g h b, f x ≤ c := by
  rw [← projection_eq (b := b) hg hm, exists_mem_image]

variable [Preorder α]

/-- A minimizer of `f` on `originalSet` lifts to a minimizer of `f ∘ Prod.fst` on `liftedSet`. -/
theorem isMinOn_comp_fst_liftedSet_of_isMinOn (hg : MapsTo g D E) (hm : MonotoneOn h E)
    {f : X → α} {p : X × Y} (hmin : IsMinOn f (originalSet D g h b) p.1) :
    IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p :=
  hmin.comp_of_mapsTo (mapsTo_fst_liftedSet hg hm) rfl

/-- **Feasible minimum equivalence.** A pair `p` is a feasible minimizer of `f ∘ Prod.fst` on
`liftedSet` if and only if `p ∈ liftedSet` and `p.1` is a feasible minimizer of `f` on
`originalSet`. Membership is kept explicit because `IsMinOn` alone does not assert feasibility. -/
theorem feasible_minimum_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) (f : X → α) (p : X × Y) :
    (p ∈ liftedSet D E g h b ∧ IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) ↔
      p ∈ liftedSet D E g h b ∧ p.1 ∈ originalSet D g h b ∧
        IsMinOn f (originalSet D g h b) p.1 := by
  rw [← projection_eq (b := b) hg hm, mem_and_isMinOn_comp_iff]

/-- **Attainment equivalence.** An attained feasible minimum exists on `liftedSet` for
`f ∘ Prod.fst` if and only if one exists on `originalSet` for `f`. Neither direction assumes that
an arbitrary nonempty feasible set attains its infimum. -/
theorem attainment_iff (hg : MapsTo g D E) (hm : MonotoneOn h E) (f : X → α) :
    (∃ p ∈ liftedSet D E g h b, IsMinOn (f ∘ Prod.fst) (liftedSet D E g h b) p) ↔
      ∃ x ∈ originalSet D g h b, IsMinOn f (originalSet D g h b) x := by
  rw [← projection_eq (b := b) hg hm, exists_mem_image_isMinOn_iff]

end Minima

end TauCeti.ConvexLifting
