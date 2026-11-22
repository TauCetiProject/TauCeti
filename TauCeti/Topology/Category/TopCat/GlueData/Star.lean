/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Open gluing in a star

A space `X` can be glued to a family of spaces `Y i` along open partial homeomorphisms
`e i : OpenPartialHomeomorph X (Y i)` with pairwise disjoint sources. The hub is indexed by
`none` and the leaves by `some i`. Distinct leaves have empty overlap. This is gluing data for
Mathlib's existing glued carrier, not a new quotient construction.

The disjointness assumption ensures that there are no additional identifications between leaves
through the hub. In particular, the pairwise overlaps specified here already satisfy the cocycle
condition. No finiteness or nonemptiness assumption is needed; finite stars are a special case.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 1
  (the smooth manifold chart lemma).
-/

public section

open CategoryTheory TopologicalSpace Set Function

namespace TauCeti

universe u

variable {ι X : Type u} [TopologicalSpace X] {Y : ι → Type u}
  [∀ i, TopologicalSpace (Y i)]

/-- The hub at `none` and the leaf `Y i` at `some i`, as bundled spaces. -/
abbrev starPiece : Option ι → TopCat.{u}
  | none => TopCat.of X
  | some i => TopCat.of (Y i)

/-- The open overlap in a star piece: the prescribed source or target along an edge,
the whole piece on the diagonal, and the empty set between distinct leaves. -/
abbrev starOverlap (e : ∀ i, OpenPartialHomeomorph X (Y i)) :
    ∀ i : Option ι, Option ι → Opens (starPiece (X := X) (Y := Y) i)
  | none, none => ⊤
  | none, some j => ⟨(e j).source, (e j).open_source⟩
  | some i, none => ⟨(e i).target, (e i).open_target⟩
  | some i, some j => ⟨{_x | i = j}, by classical by_cases h : i = j <;> simp [h]⟩

/-- The transition between star overlaps: the given homeomorphism along an edge, its inverse
in the reverse direction, and identity on a self-overlap. -/
noncomputable def starTransition (e : ∀ i, OpenPartialHomeomorph X (Y i)) :
    ∀ i j : Option ι, TopCat.of (starOverlap e i j) ⟶ TopCat.of (starOverlap e j i)
  | none, none => 𝟙 _
  | none, some j => TopCat.ofHom ⟨(e j).toHomeomorphSourceTarget,
      (e j).toHomeomorphSourceTarget.continuous⟩
  | some i, none => TopCat.ofHom ⟨(e i).toHomeomorphSourceTarget.symm,
      (e i).toHomeomorphSourceTarget.symm.continuous⟩
  | some i, some j => by
    classical
    by_cases h : i = j
    · subst j
      exact 𝟙 _
    · haveI : IsEmpty (starOverlap e (some i) (some j)) := ⟨fun x ↦ h x.2⟩
      exact TopCat.ofHom ⟨fun x ↦ False.elim (h x.2), continuous_of_discreteTopology⟩

private theorem starTransition_self (e : ∀ i, OpenPartialHomeomorph X (Y i))
    (i : Option ι) : starTransition e i i = 𝟙 _ := by
  cases i <;> simp [starTransition]

private theorem starTransition_inter (e : ∀ i, OpenPartialHomeomorph X (Y i))
    (he : Pairwise (Disjoint on fun i ↦ (e i).source))
    {i j : Option ι} (k : Option ι) (x : starOverlap e i j)
    (hx : (x : starPiece (X := X) (Y := Y) i) ∈ starOverlap e i k) :
    ((starTransition e i j x).val : starPiece (X := X) (Y := Y) j) ∈ starOverlap e j k := by
  classical
  cases i with
  | none =>
    cases j with
    | none => exact hx
    | some j =>
      cases k with
      | none => exact (e j).map_source x.2
      | some k =>
        have hjk : j = k := by
          by_contra h
          exact Set.disjoint_left.1 (he h) x.2 hx
        exact hjk
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => trivial
      | some k =>
        have hik : i = k := hx
        subst k
        exact (e i).map_target x.2
    | some j =>
      have hij : i = j := x.2
      subst j
      simpa only [starTransition_self, CategoryTheory.id_apply] using hx

private theorem starTransition_cocycle (e : ∀ i, OpenPartialHomeomorph X (Y i))
    (he : Pairwise (Disjoint on fun i ↦ (e i).source))
    (i j k : Option ι) (x : starOverlap e i j)
    (hx : (x : starPiece (X := X) (Y := Y) i) ∈ starOverlap e i k) :
    (starTransition e j k ⟨_, starTransition_inter e he k x hx⟩).val =
      (starTransition e i k ⟨x, hx⟩).val := by
  classical
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      cases k with
      | none => exact (e j).left_inv x.2
      | some k =>
        have hjk : j = k := by
          by_contra h
          exact Set.disjoint_left.1 (he h) x.2 hx
        subst k
        simp only [starTransition_self, CategoryTheory.id_apply]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some k =>
        have hik : i = k := hx
        subst k
        simp only [starTransition_self, CategoryTheory.id_apply]
        exact (e i).right_inv x.2
    | some j =>
      have hij : i = j := x.2
      subst j
      apply congrArg (fun z : starOverlap e (some i) k ↦
        (starTransition e (some i) k z).val)
      apply Subtype.ext
      simp only [starTransition_self, CategoryTheory.id_apply]

/-- Glue a hub `X` to leaves `Y i` along open partial homeomorphisms with pairwise disjoint
sources. The index `none` denotes the hub, and `some i` denotes the leaf `Y i`.
The body is exposed so that the dependent piece and overlap carriers can be computed. -/
@[expose] noncomputable def starGlueData (e : ∀ i, OpenPartialHomeomorph X (Y i))
    (he : Pairwise (Disjoint on fun i ↦ (e i).source)) : TopCat.GlueData.{u} :=
  TopCat.GlueData.mk'
    { U := starPiece
      V := starOverlap e
      t := starTransition e
      V_id := by intro i; cases i <;> ext x <;> simp [starOverlap]
      t_id := fun i ↦ by rw [starTransition_self]; rfl
      t_inter := by exact fun {_ _} ↦ starTransition_inter e he
      cocycle := by exact starTransition_cocycle e he }

variable (e : ∀ i, OpenPartialHomeomorph X (Y i))
  (he : Pairwise (Disjoint on fun i ↦ (e i).source))

/-- The hub of the star is `X`. -/
theorem starGlueData_U_none : (starGlueData e he).U none = TopCat.of X := rfl

/-- The leaf at `i` is `Y i`. -/
theorem starGlueData_U_some (i : ι) :
    (starGlueData e he).U (some i) = TopCat.of (Y i) := rfl

/-- The self-overlap of the hub is its whole open subspace. -/
@[simp] theorem starGlueData_V_none_none :
    (starGlueData e he).V (none, none) = TopCat.of (⊤ : Opens X) := rfl

/-- The overlap in the hub with leaf `i` is the source of `e i`. -/
@[simp] theorem starGlueData_V_none_some (i : ι) :
    (starGlueData e he).V (none, some i) = TopCat.of (e i).source := rfl

/-- The overlap in leaf `i` with the hub is the target of `e i`. -/
@[simp] theorem starGlueData_V_some_none (i : ι) :
    (starGlueData e he).V (some i, none) = TopCat.of (e i).target := rfl

/-- A leaf overlaps itself everywhere and any other leaf nowhere. -/
@[simp] theorem starGlueData_V_some_some (i j : ι) :
    (starGlueData e he).V (some i, some j) = TopCat.of {_x : Y i // i = j} := rfl

/-- Each overlap map is inclusion of its underlying open subspace. -/
@[simp] theorem starGlueData_f_apply (i j : Option ι) (x : (starGlueData e he).V (i, j)) :
    (starGlueData e he).f i j x = x.val := rfl

/-- The transition from the hub to a leaf is the given homeomorphism on its source. -/
@[simp] theorem starGlueData_t_none_some (i : ι) :
    (starGlueData e he).t none (some i) =
      TopCat.ofHom ⟨(e i).toHomeomorphSourceTarget,
        (e i).toHomeomorphSourceTarget.continuous⟩ := (rfl)

/-- The transition from a leaf to the hub is the inverse homeomorphism on its target. -/
@[simp] theorem starGlueData_t_some_none (i : ι) :
    (starGlueData e he).t (some i) none =
      TopCat.ofHom ⟨(e i).toHomeomorphSourceTarget.symm,
        (e i).toHomeomorphSourceTarget.symm.continuous⟩ := (rfl)

/-- A hub point is identified with a leaf point exactly by the prescribed transition. -/
@[simp, grind =] theorem starGlueData_ι_none_eq_some_iff (i : ι) (x : X) (y : Y i) :
    (starGlueData e he).toGlueData.ι none x = (starGlueData e he).toGlueData.ι (some i) y ↔
      x ∈ (e i).source ∧ e i x = y := by
  refine ((starGlueData e he).ι_eq_iff_rel none (some i) x y).trans ⟨?_, ?_⟩
  · rintro ⟨z, hx, hy⟩
    simp only [starGlueData_f_apply, starGlueData_t_none_some] at hx hy
    exact hx ▸ ⟨z.2, hy⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl, rfl⟩

/-- A leaf point is identified with a hub point exactly by the prescribed transition. -/
@[simp, grind =] theorem starGlueData_ι_some_eq_none_iff (i : ι) (x : X) (y : Y i) :
    (starGlueData e he).toGlueData.ι (some i) y = (starGlueData e he).toGlueData.ι none x ↔
      x ∈ (e i).source ∧ e i x = y :=
  eq_comm.trans (starGlueData_ι_none_eq_some_iff e he i x y)

/-- Two hub points are identified only if they are equal. -/
@[simp] theorem starGlueData_ι_none_eq_none_iff (x y : X) :
    (starGlueData e he).toGlueData.ι none x = (starGlueData e he).toGlueData.ι none y ↔ x = y :=
  ((starGlueData e he).ι_injective none).eq_iff

/-- Two points of the same leaf are identified only if they are equal. -/
@[simp] theorem starGlueData_ι_some_eq_same_iff (i : ι) (x y : Y i) :
    (starGlueData e he).toGlueData.ι (some i) x = (starGlueData e he).toGlueData.ι (some i) y ↔
      x = y :=
  ((starGlueData e he).ι_injective (some i)).eq_iff

/-- Distinct leaves have disjoint images, even after taking all generated identifications. -/
@[simp] theorem starGlueData_ι_some_ne_some {i j : ι} (hij : i ≠ j) (x : Y i) (y : Y j) :
    (starGlueData e he).toGlueData.ι (some i) x ≠
      (starGlueData e he).toGlueData.ι (some j) y := by
  intro h
  obtain ⟨z, -, -⟩ := ((starGlueData e he).ι_eq_iff_rel (some i) (some j) x y).1 h
  exact hij z.2

end TauCeti
